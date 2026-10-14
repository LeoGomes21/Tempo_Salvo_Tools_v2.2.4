from qgis.core import QgsProject, QgsMapLayer, QgsWkbTypes, Qgis, QgsCoordinateReferenceSystem, QgsCoordinateTransform, QgsLayerTreeLayer, QgsPointXY, QgsGeometry, QgsLayerTree, QgsVectorLayer, QgsField, QgsPoint, QgsFeature, QgsMeshLayer, edit, QgsProcessingException, QgsTask, QgsApplication, QgsProcessingContext, QgsProcessingFeedback, QgsProcessingAlgRunnerTask
from qgis.core import (
    QgsMeshDatasetIndex,
    QgsMeshRendererScalarSettings,
    QgsColorRampShader)
from qgis.PyQt.QtWidgets import QTreeView, QStyledItemDelegate, QColorDialog, QMenu, QDialog, QVBoxLayout, QLabel, QPushButton, QHBoxLayout, QFileDialog, QComboBox, QFrame, QCheckBox, QProgressBar, QListWidget, QScrollBar, QStyle, QGraphicsDropShadowEffect, QDoubleSpinBox, QSpinBox, QRadioButton, QSlider, QGridLayout, QSpacerItem, QSizePolicy, QWidget, QToolTip, QInputDialog, QProgressDialog, QApplication, QDialogButtonBox, QMessageBox
from qgis.PyQt.QtGui import QStandardItemModel, QStandardItem, QIcon, QPixmap, QPainter, QColor, QPen, QFont, QPalette, QCursor, QDesktopServices, QLinearGradient, QVector3D, QVector4D
from qgis.PyQt.QtCore import Qt, QPoint, QRect, QEvent, QCoreApplication, QSettings, QItemSelectionModel, QSize, QVariant, QModelIndex, QObject, pyqtSignal, QThread, QEventLoop, QUrl, QTimer, pyqtSlot, QRectF, QMetaType, QPointF
from pyqtgraph.opengl import GLViewWidget, GLLinePlotItem
from pyqtgraph.opengl.shaders import ShaderProgram
from qgis.gui import QgsProjectionSelectionDialog
from OpenGL.error import GLError
from lxml import etree as XmlET
try:
    from defusedxml import ElementTree as DefusedET
    from defusedxml.common import DefusedXmlException
    DEFUSEDXML_OK = True
except ImportError:
    DefusedET = None
    DefusedXmlException = Exception
    DEFUSEDXML_OK = False
import pyqtgraph.opengl as gl
from qgis.utils import iface

from lxml import etree
import pyqtgraph as pg
from OpenGL import GL
import numpy as np
import processing
import traceback
import simplekml
import tempfile
import pathlib
import shutil
import ezdxf
import time
import math
import os
import re

class UiManagerM:
    """
    Gerencia a interface do usuário, interagindo com um QTreeView para listar e gerenciar camadas de malhas no QGIS.
    """
    def __init__(self, iface, dialog):
        """
        Inicializa a instância da classe UiManagerM, responsável por gerenciar a interface do usuário
        que interage com um QTreeView para listar e gerenciar camadas de malhas no QGIS.

        :param iface: Interface do QGIS para interagir com o ambiente.
        :param dialog: Diálogo ou janela que esta classe gerenciará.

        Funções e Ações Desenvolvidas:
        - Configuração inicial das variáveis de instância.
        - Associação do modelo de dados com o QTreeView.
        - Inicialização da configuração do QTreeView.
        - Seleção automática da última camada no QTreeView.
        - Conexão dos sinais do QGIS e da interface do usuário com os métodos correspondentes.
        """
        # Salva as referências para a interface do QGIS e o diálogo fornecidos
        self.iface = iface
        self.dlg = dialog

        # Guards anti-recursão / anti-loop
        self._tree_sync_depth = 0
        self._selection_sync_depth = 0

        # Cria e configura o modelo de dados para o QTreeView
        self.treeViewModel = QStandardItemModel()

        # Aplica estilos CSS para aprimorar a interação visual com os itens do QTreeView
        self.dlg.treeViewListaMalha.setStyleSheet("""
            QTreeView::item:hover:!selected {
                background-color: #def2fc;
            }
            QTreeView::item:selected {
            }""")

        # Atualiza a visualização da lista de camadas no QTreeView
        self.atualizar_treeView_lista_malha()

        self.dlg.treeViewListaMalha.setModel(self.treeViewModel)

        # Inicia a conexão de sinais para tratar a mudança de nome das camadas no projeto
        self.connect_name_changed_signals()

        # Conecta os sinais do QGIS e da interface do usuário para sincronizar ações e eventos
        self.connect_signals()

        # Chama atualização dos botões após toda modificação
        self.atualizar_estado_botoes()

        # Adiciona o filtro de eventos ao treeView
        self.tree_view_event_filter = TreeViewEventFilter(self)
        self.dlg.treeViewListaMalha.viewport().installEventFilter(self.tree_view_event_filter)

    def connect_signals(self):
        """
        Conecta os sinais do QGIS e do QTreeView para sincronizar a interface
        com o estado atual do projeto.
        """
        self._tree_sync_depth = getattr(self, "_tree_sync_depth", 0)

        QgsProject.instance().layersAdded.connect(self.layers_added)

        try:
            self.treeViewModel.itemChanged.disconnect(self.on_item_changed)
        except TypeError:
            pass  # nosec B110
        self.treeViewModel.itemChanged.connect(self.on_item_changed)

        root = QgsProject.instance().layerTreeRoot()
        try:
            root.visibilityChanged.connect(
                self._on_any_layer_tree_visibility_changed,
                type=Qt.ConnectionType.UniqueConnection)
        except TypeError:
            try:
                root.visibilityChanged.connect(self._on_any_layer_tree_visibility_changed)
            except Exception:
                pass  # nosec B110

        # Uma única conexão basta
        self.iface.mapCanvas().layersChanged.connect(self.sync_from_qgis_to_treeview)

        # Seleção via mouse somente no TreeView de Malhas
        self.dlg.treeViewListaMalha.clicked.connect(lambda _: self.on_treeview_selection_changed(None, None))

        self.dlg.treeViewListaMalha.clicked.connect(self.on_treeview_item_clicked)

        # Define e aplica um delegado personalizado para customização da exibição de itens no QTreeView
        self.dlg.treeViewListaMalha.setItemDelegate(CustomDelegate(self.dlg.treeViewListaMalha))

        # Sincroniza a seleção no QGIS com a seleção no QTreeView quando a camada ativa no QGIS muda
        self.iface.currentLayerChanged.connect(self.on_current_layer_changed)

        # Configura a política de menu de contexto para permitir menus personalizados em cliques com o botão direito
        self.dlg.treeViewListaMalha.setContextMenuPolicy(Qt.ContextMenuPolicy.CustomContextMenu)
        self.dlg.treeViewListaMalha.customContextMenuRequested.connect(self.open_context_menu)

        # Conectar o botão à função 3D
        self.dlg.pushButtonMalha3D.clicked.connect(self.mostrar_dialogo_exporta_malha_3d)

        # Conectar o botão à função KML
        self.dlg.pushButtonMalhaKML.clicked.connect(self.exportar_malha_kml)

        # Conectando o botão pushButton3DMalha
        self.dlg.pushButton3DMalha.clicked.connect(self.abrir_visualizador_malha_3d)

        # Conectando o botão pushButtonFecharM à função que fecha o diálogo
        self.dlg.pushButtonFecharM.clicked.connect(self.close_dialog)

        # seleção via mouse (funciona mesmo com 1 Malha)
        self.dlg.treeViewListaMalha.clicked.connect(lambda _: self.on_treeview_selection_changed(None, None))

        # Ação de controle ao remover Camadas de Rasters
        QgsProject.instance().layersRemoved.connect(self.on_layers_removed)

        # Conecta o botão para Zoom
        self.dlg.pushButtonVisualizarM.clicked.connect(self.visualizar_raster_selecionada)

        # Conectar o botão de renomear à função de renomear a camada
        self.dlg.pushButtonRenomeM.clicked.connect(self.renomear_camada_selecionada)

        # Conectar o botão de deletar à função de remover a camada
        self.dlg.pushButtonDelM.clicked.connect(self.remover_camada_selecionada)

        # Conectar o botão de salvar à função de salvar a camada
        self.dlg.pushButtonSalvarMalha.clicked.connect(self.salvar_malha_selecionada)

        # Conectar o botão de clocar à função de Clonar a camada
        self.dlg.pushButtonClonaMalha.clicked.connect(self.clonar_malha_selecionada)

        # Conectar o botão de Reprojetar à função de Reprojetar a camada
        self.dlg.pushButtonReprojetarM.clicked.connect(self.reprojetar_malha_selecionada)

        # Abre para adicionar camada de Malhas
        self.dlg.pushButtonAbrirM.clicked.connect(self.abrir_malha_arquivo)

        # Salvar múltiplos rasters
        self.dlg.pushButtonSalvaMultiplosM.clicked.connect(self.abrir_salvar_multiplas_malhas)

    def tr(self, message):
        """
        Traduz textos deste diálogo.
        O contexto precisa ser estável para o Qt Linguist encontrar as traduções.
        """
        return QCoreApplication.translate("UiManagerM", message)

    def _salvar_malha_em_arquivo(self, layer: QgsMeshLayer, path_saida: str) -> bool:
        """
        Salva uma camada de malha em arquivo.

        Estratégia:
        1. tenta saveMesh();
        2. se falhar, tenta copiar o arquivo-fonte real da malha.
        """
        if not layer or layer.type() != QgsMapLayer.LayerType.MeshLayer or not layer.isValid():
            return False

        try:
            # 1) tenta exportação nativa
            if hasattr(layer, "saveMesh"):
                try:
                    ok = layer.saveMesh(path_saida, "MDAL Mesh")
                    if ok:
                        return True
                except Exception:
                    pass  # nosec B110

            # 2) fallback: copia o arquivo-fonte real
            src_path = self._resolver_caminho_fonte_malha(layer)
            if src_path and os.path.isfile(src_path):
                shutil.copyfile(src_path, path_saida)
                return True

            return False

        except Exception:
            print(traceback.format_exc())
            return False

    def abrir_salvar_multiplas_malhas(self):
        """
        Abre um diálogo para salvar múltiplas malhas:
        - todas as camadas, ou
        - apenas as camadas visíveis.
        """
        dlg, rb_todas, rb_visiveis = self._criar_dialogo_salvar_multiplas_malhas()
        if dlg.exec() != QDialog.DialogCode.Accepted:
            return

        apenas_visiveis = rb_visiveis.isChecked()

        layers = self._coletar_camadas_malhas_treeview(apenas_visiveis=apenas_visiveis)
        if not layers:
            self.mostrar_mensagem(self.tr("Nenhuma camada de malha para salvar."), "Aviso")
            return

        pasta = self._selecionar_pasta_saida_batch()
        if not pasta:
            return

        progressBar, progressMsg = self.iniciar_progress_bar(len(layers), self.tr("Salvando malhas..."))

        ok_count = 0
        falhas = []

        for i, layer in enumerate(layers, start=1):
            try:
                path_saida = self._gerar_caminho_saida_unico(pasta, layer.name(), ext=".mesh")
                ok = self._salvar_malha_em_arquivo(layer, path_saida)

                if ok:
                    ok_count += 1
                else:
                    falhas.append(layer.name())

            except Exception as e:
                falhas.append(f"{layer.name()} ({e})")

            progressBar.setValue(i)
            QCoreApplication.processEvents()

        try:
            self.iface.messageBar().popWidget(progressMsg)
        except Exception:
            pass  # nosec B110

        if falhas:
            self.mostrar_mensagem(self.tr("Salvamento concluído com falhas: {ok_count}/{total}.\nFalharam: {falhas}{sufixo}").format(ok_count=ok_count, total=len(layers), falhas=", ".join(falhas[:8]), sufixo="..." if len(falhas) > 8 else ""), "Erro", duracao=3, caminho_pasta=pasta)
        else:
            self.mostrar_mensagem(self.tr("Salvamento concluído: {ok_count}/{total} arquivos.").format(ok_count=ok_count, total=len(layers)), "Sucesso", duracao=3, caminho_pasta=pasta)

    def _criar_dialogo_salvar_multiplas_malhas(self):
        """
        Cria o diálogo para salvar múltiplas malhas.
        """
        dlg = QDialog(self.dlg)
        dlg.setWindowTitle(self.tr("Salvar Múltiplas Malhas"))

        layout = QVBoxLayout(dlg)

        frame = QFrame(dlg)
        frame.setFrameShape(QFrame.Shape.Box)
        frame.setFrameShadow(QFrame.Shadow.Raised)

        frame_layout = QVBoxLayout(frame)

        rb_todas = QRadioButton(self.tr("Salvar todas as Camadas"), frame)
        rb_visiveis = QRadioButton(self.tr("Salvar apenas as Camadas Visíveis"), frame)
        rb_todas.setChecked(True)

        frame_layout.addWidget(rb_todas)
        frame_layout.addWidget(rb_visiveis)

        layout.addWidget(frame)

        buttonBox = QDialogButtonBox(
            QDialogButtonBox.StandardButton.Ok | QDialogButtonBox.StandardButton.Cancel, dlg)
        buttonBox.setCenterButtons(True)
        buttonBox.setSizePolicy(QSizePolicy.Policy.Expanding, QSizePolicy.Policy.Fixed)

        buttonBox.accepted.connect(dlg.accept)
        buttonBox.rejected.connect(dlg.reject)

        layout.addWidget(buttonBox)

        return dlg, rb_todas, rb_visiveis

    def _selecionar_pasta_saida_batch(self) -> str | None:
        """
        Abre um diálogo para escolher a pasta de saída
        e guarda a última pasta em QSettings.
        """
        settings = QSettings()
        lastDir = settings.value("lastDir", "")

        pasta = QFileDialog.getExistingDirectory(self.dlg, self.tr("Selecione a pasta de destino"), lastDir)
        if not pasta:
            return None

        settings.setValue("lastDir", pasta)
        return pasta

    def _coletar_camadas_malhas_treeview(self, *, apenas_visiveis: bool) -> list:
        """
        Coleta as camadas de malha listadas no treeViewModel.
        Se 'apenas_visiveis' for True, filtra pelo checkState.
        """
        layers = []

        for row in range(self.treeViewModel.rowCount()):
            item = self.treeViewModel.item(row)
            if not item:
                continue

            if apenas_visiveis and item.checkState() != Qt.CheckState.Checked:
                continue

            layer_id = item.data(Qt.ItemDataRole.UserRole)
            layer = QgsProject.instance().mapLayer(layer_id)

            if isinstance(layer, QgsMeshLayer) and layer.isValid():
                layers.append(layer)

        return layers

    def _gerar_caminho_saida_unico(self, pasta: str, base_name: str, *, ext: str = ".mesh") -> str:
        """
        Gera um caminho único na pasta (evita sobrescrever):
        Nome.tif, Nome_1.tif, Nome_2.tif...
        """
        safe = self._sanitizar_nome_arquivo(base_name)
        path = os.path.join(pasta, safe + ext)

        i = 1
        while os.path.exists(path):
            path = os.path.join(pasta, f"{safe}_{i}{ext}")
            i += 1

        return path

    def _sanitizar_nome_arquivo(self, name: str) -> str:
        """
        Remove caracteres inadequados para nome de arquivo.
        """
        if not name:
            return "malha"

        permitido = " _-()[]{}."
        out = []

        for ch in name:
            if ch.isalnum() or ch in permitido:
                out.append(ch)
            else:
                out.append("_")

        safe = "".join(out).strip()
        return safe or "malha"

    def abrir_malha_arquivo(self):
        """
        Abre um arquivo de malha compatível com MDAL.

        Se o arquivo não possuir SRC, solicita ao usuário que defina
        o sistema de referência antes de adicionar a camada ao projeto.
        """
        filtros = self.tr("Arquivos de Malha (*.2dm *.mesh *.nc *.slf);;"
            "Todos os Arquivos (*)")

        file_path, _ = QFileDialog.getOpenFileName(self.dlg, self.tr("Abrir Arquivo de Malha"), "", filtros)

        if not file_path:
            return

        nome_camada = os.path.splitext(
            os.path.basename(file_path))[0]

        layer = QgsMeshLayer(file_path, nome_camada, "mdal")

        if not layer.isValid():
            self.mostrar_mensagem(self.tr("Falha ao carregar a malha.\nVerifique se o arquivo é compatível com o MDAL."), "Erro")
            return

        # Muitos arquivos .2dm e .mesh não armazenam o SRC.
        if not layer.crs().isValid():
            crs_projeto = QgsProject.instance().crs()

            dlg_crs = QgsProjectionSelectionDialog(self.dlg)
            dlg_crs.setWindowTitle(
                self.tr("Definir SRC da Malha"))

            # Inicia o diálogo com o SRC atual do projeto.
            if crs_projeto.isValid():
                dlg_crs.setCrs(crs_projeto)

            if dlg_crs.exec() != QDialog.DialogCode.Accepted:
                self.mostrar_mensagem(self.tr("A malha não foi adicionada porque o SRC não foi definido."), "Aviso")
                return

            crs_selecionado = dlg_crs.crs()

            if not crs_selecionado.isValid():
                self.mostrar_mensagem(self.tr("O SRC selecionado não é válido."), "Erro")
                return

            # Apenas atribui o SRC às coordenadas existentes.
            # Não altera nem reprojeta os vértices.
            layer.setCrs(crs_selecionado)

        QgsProject.instance().addMapLayer(layer)

        self.iface.setActiveLayer(layer)
        self.iface.zoomToActiveLayer()
        self.iface.mapCanvas().refresh()

        self.mostrar_mensagem(self.tr("Camada de malha '{nome_camada}' adicionada com sucesso!").format(nome_camada=nome_camada), "Sucesso")

        self.atualizar_treeView_lista_malha()

    def salvar_malha_selecionada(self):
        """
        Salva a malha selecionada em .mesh e substitui
        a camada atual pela camada permanente salva em disco.
        """
        # Obtém a seleção no TreeView
        indexes = self.dlg.treeViewListaMalha.selectedIndexes()

        if not indexes:
            self.mostrar_mensagem(self.tr("Nenhuma camada de malha selecionada."), "Erro")
            return

        selected_index = indexes[0]

        layer_id = self.treeViewModel.itemFromIndex(selected_index).data(Qt.ItemDataRole.UserRole)

        layer = QgsProject.instance().mapLayer(layer_id)

        if (not layer
            or layer.type() != QgsMapLayer.LayerType.MeshLayer):
            self.mostrar_mensagem(self.tr("Camada selecionada não é uma malha válida."), "Erro")
            return

        project = QgsProject.instance()
        root = project.layerTreeRoot()

        # Guarda informações da camada original
        nome_original = layer.name()
        crs_original = layer.crs()

        # Guarda posição e visibilidade na árvore do QGIS
        node_original = root.findLayer(layer_id)

        parent_node = root
        posicao_original = 0
        visivel = True

        if node_original is not None:
            try:
                visivel = bool(node_original.itemVisibilityChecked())
            except Exception:
                pass  # nosec B110

            try:
                parent_node = (node_original.parent()
                    or root)

                filhos = parent_node.children()
                posicao_original = filhos.index(node_original)

            except Exception:
                parent_node = root
                posicao_original = 0

        # Guarda a configuração visual da malha
        renderer_settings = None

        try:
            renderer_settings = (layer.rendererSettings())
        except Exception:
            pass  # nosec B110

        # Sugere nome baseado na camada
        nome_sugerido = (nome_original + ".mesh")

        path_saida = self.escolher_local_para_salvar(nome_sugerido, self.tr("Arquivo de Malha (*.mesh)"))

        if not path_saida:
            return

        # Garante extensão
        if not path_saida.lower().endswith(".mesh"):
            path_saida += ".mesh"

        try:
            # Salva efetivamente no disco
            ok = self._salvar_malha_em_arquivo(layer, path_saida)

            if not ok:
                self.mostrar_mensagem(self.tr("Erro ao salvar malha. Verifique se o provedor suporta exportação."), "Erro")
                return

            # Verifica se o arquivo realmente existe
            if (not os.path.isfile(path_saida)
                or os.path.getsize(path_saida) == 0):
                self.mostrar_mensagem(self.tr("O arquivo da malha foi criado, mas está vazio ou não foi localizado."), "Erro")
                return

            # Nome da nova camada = nome do arquivo salvo
            nome_salvo = os.path.splitext(os.path.basename(path_saida))[0]

            # Carrega agora a malha PERMANENTE
            nova_camada = QgsMeshLayer(path_saida, nome_salvo, "mdal")

            if (not nova_camada
                or not nova_camada.isValid()):
                self.mostrar_mensagem(self.tr("A malha foi salva, mas não pôde ser recarregada no projeto. A camada original foi mantida."), "Erro", caminho_arquivo=path_saida, caminho_pasta=os.path.dirname(path_saida))
                return

            # Mantém o SRC original.
            #
            # Arquivos .mesh podem não armazenar o SRC.
            if (crs_original
                and crs_original.isValid()):
                try:
                    nova_camada.setCrs(crs_original)
                except Exception:
                    pass  # nosec B110

            # Tenta preservar a simbologia/configuração
            # de renderização da malha original
            if renderer_settings is not None:
                try:
                    nova_camada.setRendererSettings(renderer_settings)
                except Exception:
                    pass  # nosec B110

            # Adiciona ao registro do projeto,
            # mas ainda sem criar nó automaticamente
            project.addMapLayer(nova_camada, False)

            # Coloca exatamente na posição da camada original
            try:
                parent_node.insertLayer(posicao_original, nova_camada)

            except Exception:
                root.addLayer(nova_camada)

            # Mantém a visibilidade
            novo_node = root.findLayer(nova_camada.id())

            if novo_node is not None:
                try:
                    novo_node.setItemVisibilityChecked(visivel)
                except Exception:
                    pass  # nosec B110

            # SOMENTE agora remove a camada temporária original.
            #
            # Assim, se algo falhar anteriormente,
            # o usuário não perde a camada.
            project.removeMapLayer(layer_id)

            # Atualiza o TreeView do plugin
            self.atualizar_treeView_lista_malha()

            def selecionar_camada_salva():
                try:
                    self.iface.setActiveLayer(nova_camada)
                    self.iface.layerTreeView().setCurrentLayer(nova_camada)
                    self.on_current_layer_changed(nova_camada)
                    self.iface.mapCanvas().refresh()

                except Exception:
                    pass  # nosec B110

            QTimer.singleShot(0, selecionar_camada_salva)

            self.mostrar_mensagem(self.tr("Malha salva e substituída pela camada permanente com sucesso!"), "Sucesso", caminho_arquivo=path_saida, caminho_pasta=os.path.dirname(path_saida))

        except Exception as e:
            self.mostrar_mensagem(self.tr("Erro ao salvar malha: {error}").format(error=e), "Erro")

    def _resolver_caminho_fonte_malha(self, layer: QgsMeshLayer) -> str:
        """
        Resolve o caminho físico do arquivo-fonte de uma malha MDAL.
        Aceita URIs como:
          2DM:"C:/caminho/arquivo.mesh"
          C:/caminho/arquivo.mesh
          C:/caminho/arquivo.mesh|alguma_opcao
        """
        raw_src = ""
        try:
            prov = layer.dataProvider()
            raw_src = prov.dataSourceUri() if prov else ""
        except Exception:
            raw_src = ""

        if not raw_src:
            raw_src = layer.source() or ""

        src_path = raw_src.strip()

        if "|" in src_path:
            src_path = src_path.split("|", 1)[0].strip()

        m = re.match(r'^[A-Za-z0-9_]+:\s*"(.+)"\s*$', src_path)
        if m:
            src_path = m.group(1)

        src_path = src_path.strip().strip('"').strip("'")
        return src_path

    def remover_camada_selecionada(self):
        """
        Remove a camada de malha (mesh) selecionada no treeViewListaMalha sem perguntar nada ao usuário.
        """
        # Obtém os índices selecionados no treeView de malha
        selected_indexes = self.dlg.treeViewListaMalha.selectedIndexes()
        if selected_indexes:
            selected_index = selected_indexes[0]
            # Usa o papel UserRole para pegar o ID real da camada
            layer_id = selected_index.model().itemFromIndex(selected_index).data(Qt.ItemDataRole.UserRole)
            layer_to_remove = QgsProject.instance().mapLayer(layer_id)
            if layer_to_remove:
                # Remove a camada de malha diretamente do projeto QGIS
                QgsProject.instance().removeMapLayer(layer_id)
                self.atualizar_treeView_lista_malha()
                self.iface.mapCanvas().refresh()

    def renomear_camada_selecionada(self):
        """
        Permite ao usuário renomear uma camada de Malha selecionado no treeViewListaMalha,
        garantindo unicidade do nome no projeto.

        Fluxo:
        - Obtém o índice selecionado.
        - Recupera a camada associada ao item (usando Qt.UserRole).
        - Exibe um diálogo para o usuário digitar o novo nome.
        - Garante que o nome será único (ajusta se necessário).
        - Atualiza o nome da camada no QGIS e o texto do item no treeView.
        """
        # Obtém os índices atualmente selecionados no treeView de malha
        selected_indexes = self.dlg.treeViewListaMalha.selectedIndexes()
        if selected_indexes:
            # Pega o primeiro índice selecionado
            selected_index = selected_indexes[0]
            # Recupera o ID da camada usando o papel UserRole (garante que é o ID real da camada QGIS)
            layer_id = selected_index.model().itemFromIndex(selected_index).data(Qt.ItemDataRole.UserRole)
            # Busca a camada correspondente no projeto QGIS
            selected_layer = QgsProject.instance().mapLayer(layer_id)
            if selected_layer:
                # Exibe um diálogo para o usuário digitar o novo nome (pré-preenchido com o nome atual)
                novo_nome, ok = QInputDialog.getText(self.dlg, self.tr("Renomear Camada"), self.tr("Digite o novo nome da camada:"), text=selected_layer.name())
                # Se o usuário confirmou e digitou algo
                if ok and novo_nome:
                    # Gera um nome único para evitar duplicidade no projeto
                    novo_nome = self.gerar_nome_unico(novo_nome, selected_layer.id())
                    # Renomeia a camada no QGIS (isso pode disparar sinais que atualizam a interface automaticamente)
                    selected_layer.setName(novo_nome)
                    # Em vez de tentar alterar diretamente o item do modelo (risco de crash), reconstrói o treeView do zero
                    self.atualizar_treeView_lista_malha()

    def gerar_nome_unico(self, base_nome, current_layer_id):
        """
        Gera um nome único para uma camada de malha (mesh) dentro do projeto QGIS,
        garantindo que não haja conflitos de nome entre as camadas de malha.

        Parâmetros:
        - base_nome (str): Nome base proposto para a camada.
        - current_layer_id (str): ID da camada que está sendo renomeada, usado para ignorar ela mesma.

        Funcionalidades:
        - Cria um dicionário dos nomes de todas as camadas mesh existentes no projeto QGIS, exceto a camada renomeada.
        - Se o nome base não existir, retorna ele mesmo.
        - Se já existir, incrementa um sufixo numérico (_1, _2, ...) até encontrar um nome único.
        - Retorna o novo nome gerado.
        """
        # Só considera camadas de malha (mesh)
        existing_names = {layer.name(): layer.id()
            for layer in QgsProject.instance().mapLayers().values()
            if (layer.id() != current_layer_id and layer.type() == QgsMapLayer.LayerType.MeshLayer)}
        if base_nome not in existing_names:
            return base_nome
        else:
            i = 1
            novo_nome = f"{base_nome}_{i}"
            while novo_nome in existing_names:
                i += 1
                novo_nome = f"{base_nome}_{i}"
            return novo_nome

    def visualizar_raster_selecionada(self):
        """
        Aproxima a visualização do mapa para a camada de malha selecionada no treeView.

        - Obtém a camada de malha atualmente selecionada.
        - Centraliza e ajusta a extensão do mapa para mostrar toda a camada.
        - Se não houver feições ou seleção, não faz nada.
        """
        index = self.dlg.treeViewListaMalha.currentIndex()  # Obtém o índice selecionado
        if not index.isValid():
            return  # Não há seleção

        # Obtém o ID da camada do UserRole (melhor do que usar .data() sem argumentos)
        layer_id = index.model().itemFromIndex(index).data(Qt.ItemDataRole.UserRole)
        layer = QgsProject.instance().mapLayer(layer_id)
        if not layer or layer.extent().isEmpty():
            return  # Camada não encontrada ou sem feições

        # Garante que a camada esteja ativa (opcional, mas recomendado)
        self.iface.setActiveLayer(layer)
        # Ajusta o zoom para a extensão da camada ativa
        self.iface.zoomToActiveLayer()

    def atualizar_estado_botoes(self):
        """
        Atualiza o estado (habilitado/desabilitado) dos botões da interface gráfica conforme a presença de camadas no treeView de Rasters.

        Detalhamento do Processo:
        1. Verifica se o modelo associado ao treeViewListaMalha está vazio, ou seja, sem nenhuma camada listada.
        2. Se o modelo estiver vazio, todos os botões que dependem de camada devem ser desabilitados para evitar operações inválidas.
        3. Caso contrário, os botões são habilitados, permitindo ao usuário interagir normalmente com as funções associadas a uma camada de Malha.
        4. Os botões afetados incluem:
            - Deletar camada (`pushButtonDelM`)
            - Renomear camada (`pushButtonRenomeM`)
            - Tornar camada permanente (`pushButtonSalvarMalha`)
            - Salvar em múltiplos formatos (`pushButtonSalvaMultiplosM`)
            - Exportar para DXF/DAE/STL/OBJ (`pushButtonMalha3D`)
            - Exportar para KML (`pushButtonRasterKML`)
            - Visualizar pontos associados (`pushButtonVisualizarM`)
            - Vizzualizar 3D (`pushButton3DMalha`)
            - Reprojetar camada (`pushButtonReprojetarR`)
        5. Garante uma experiência segura e intuitiva, evitando erros por ações em contexto inválido.
        """
        # Verifica se o modelo do treeView está vazio
        modelo_vazio = self.dlg.treeViewListaMalha.model().rowCount() == 0

        # Atualiza o estado dos botões baseado na presença ou ausência de itens no modelo
        self.dlg.pushButtonDelM.setEnabled(not modelo_vazio)
        self.dlg.pushButtonRenomeM.setEnabled(not modelo_vazio)
        self.dlg.pushButtonSalvarMalha.setEnabled(not modelo_vazio)
        self.dlg.pushButtonSalvaMultiplosM.setEnabled(not modelo_vazio)
        self.dlg.pushButtonMalha3D.setEnabled(not modelo_vazio)
        self.dlg.pushButtonMalhaKML.setEnabled(not modelo_vazio)
        self.dlg.pushButtonVisualizarM.setEnabled(not modelo_vazio)
        self.dlg.pushButtonClonaMalha.setEnabled(not modelo_vazio)
        self.dlg.pushButtonReprojetarM.setEnabled(not modelo_vazio)
        self.dlg.pushButton3DMalha.setEnabled(not modelo_vazio)

    def clonar_malha_selecionada(self):
        """
        Clona a camada de malha selecionada no treeViewListaMalha, criando uma camada idêntica
        como camada temporária no QGIS. Não funciona para malhas de provedores online.
        """
        idxs = self.dlg.treeViewListaMalha.selectedIndexes()
        if not idxs:
            self.mostrar_mensagem(self.tr("Nenhuma camada selecionada."), "Aviso")
            return

        layer_id = self.treeViewModel.itemFromIndex(idxs[0]).data(Qt.ItemDataRole.UserRole)
        layer = QgsProject.instance().mapLayer(layer_id)
        if not layer or layer.type() != QgsMapLayer.LayerType.MeshLayer:
            self.mostrar_mensagem(self.tr("Selecione uma camada de malha válida."), "Erro")
            return

        # Verifica se é camada de provedor local suportado
        if layer.providerType().lower() not in ("mdal",):
            self.mostrar_mensagem(self.tr("Não é possível clonar malhas de provedores online.\nSomente malhas locais (arquivos no disco) podem ser clonadas."), "Aviso")
            return

        import tempfile, shutil, os, re

        # clone_name = f"{layer.name()}_Clone"
        clone_name = self.gerar_nome_unico(f"{layer.name()}_Clone", None)
        # URI do provider pode vir como:
        #   2DM:"C:/caminho/arquivo.mesh"
        #   C:/caminho/arquivo.mesh
        #   C:/caminho/arquivo.mesh|alguma_opcao
        raw_src = ""
        try:
            prov = layer.dataProvider()
            raw_src = prov.dataSourceUri() if prov else ""
        except Exception:
            raw_src = ""

        if not raw_src:
            raw_src = layer.source() or ""

        src_path = raw_src.strip()

        # Remove opções anexadas via "|..."
        if "|" in src_path:
            src_path = src_path.split("|", 1)[0].strip()

        # Remove prefixos do tipo 2DM:"..."/MESH:"..."/NETCDF:"..."
        m = re.match(r'^[A-Za-z0-9_]+:\s*"(.+)"\s*$', src_path)
        if m:
            src_path = m.group(1)

        # Remove aspas simples/duplas sobrando
        src_path = src_path.strip().strip('"').strip("'")

        if not src_path or not os.path.isfile(src_path):
            self.mostrar_mensagem(self.tr("Não foi possível localizar o arquivo-fonte da malha.\nOrigem: {raw_src}").format(raw_src=raw_src), "Erro")
            return

        ext = os.path.splitext(src_path)[-1] or ".mesh"
        tmp_dir = tempfile.mkdtemp()
        clone_path = os.path.join(tmp_dir, f"{clone_name}{ext}")

        try:
            shutil.copyfile(src_path, clone_path)
        except Exception as e:
            self.mostrar_mensagem(self.tr("Erro ao clonar arquivo da malha: {error}").format(error=e), "Erro")
            shutil.rmtree(tmp_dir, ignore_errors=True)
            return

        clone_layer = QgsMeshLayer(clone_path, clone_name, "mdal")

        if clone_layer.isValid():
            try:
                clone_layer.setCrs(layer.crs())
            except Exception:
                pass  # nosec B110

            # tenta copiar estilo/simbologia
            try:
                clone_layer.importNamedStyle(layer.styleManager().style(layer.styleManager().currentStyle()))
            except Exception:
                pass  # nosec B110

            QgsProject.instance().addMapLayer(clone_layer)
            self.mostrar_mensagem(self.tr("Clone de malha criado com sucesso!"), "Sucesso")
        else:
            self.mostrar_mensagem(self.tr("Erro ao criar o clone de malha!"), "Erro")
            shutil.rmtree(tmp_dir, ignore_errors=True)

    def selecionar_crs_dialogo(self, titulo=None):
        """
        Abre o diálogo padrão do QGIS para seleção de SRC e retorna um QgsCoordinateReferenceSystem.
        """
        if titulo is None:
            titulo = self.tr("Selecionar SRC")

        dlg = QgsProjectionSelectionDialog()
        dlg.setWindowTitle(titulo)

        if dlg.exec():
            epsg = dlg.crs().authid()
            return QgsCoordinateReferenceSystem(epsg)

        return None

    def reprojetar_malha_selecionada(self):
        """
        Permite ao usuário atribuir SRC se a malha não tiver,
        ou reprojetar a malha selecionada usando o algoritmo 'native:reprojectmesh'.
        """
        idxs = self.dlg.treeViewListaMalha.selectedIndexes()
        if not idxs:
            self.mostrar_mensagem(self.tr("Nenhuma camada de malha selecionada."), "Aviso")
            return

        layer_id = self.treeViewModel.itemFromIndex(idxs[0]).data(Qt.ItemDataRole.UserRole)
        layer = QgsProject.instance().mapLayer(layer_id)
        if not layer or layer.type() != QgsMapLayer.LayerType.MeshLayer:
            self.mostrar_mensagem(self.tr("Selecione uma camada de malha válida."), "Erro")
            return

        if not layer.crs().isValid():
            # Se não tem SRC, abre diálogo para atribuir (não reprojeta, só define SRC)
            crs = self.selecionar_crs_dialogo(self.tr("Definir SRC para a malha"))
            if not crs:
                self.mostrar_mensagem(self.tr("SRC não definido!"), "Erro")
                return
            layer.setCrs(crs)
            self.mostrar_mensagem(self.tr("SRC definido na malha."), "Informação")
            return

        # Tem SRC, pede SRC de destino
        crs_destino = self.selecionar_crs_dialogo(self.tr("Selecionar SRC de destino"))
        if not crs_destino or crs_destino == layer.crs():
            self.mostrar_mensagem(self.tr("SRC de destino não selecionado ou igual ao atual."), "Aviso")
            return

        # Executa a reprojeção real (gera nova camada de malha)
        params = {
            'INPUT': layer,
            'TARGET_CRS': crs_destino,
            'OUTPUT': 'TEMPORARY_OUTPUT'}
        try:
            result = processing.run("native:reprojectmesh", params)
            output_mesh = result['OUTPUT']
            clone_name = f"{layer.name()}_reprojetada"
            clone_layer = QgsMeshLayer(output_mesh, clone_name, "mdal")
            if clone_layer.isValid():
                clone_layer.setCrs(crs_destino)
                QgsProject.instance().addMapLayer(clone_layer)
                self.mostrar_mensagem(self.tr("Malha reprojetada com sucesso!"), "Sucesso")
            else:
                self.mostrar_mensagem(self.tr("Erro ao carregar malha reprojetada!"), "Erro")
        except Exception as e:
            self.mostrar_mensagem(self.tr("Erro ao reprojetar a malha: {error}").format(error=e), "Erro")

    def configurar_tooltip(self, index):
        """
        Exibe um tooltip com informações detalhadas sobre a camada de malha (mesh) selecionada no treeView.

        Detalhamento do Processo:
        1. Obtém o item do modelo de dados correspondente ao índice informado.
        2. Recupera o ID da camada mesh associada ao item e acessa a camada no projeto QGIS.
        3. Valida se a camada encontrada é realmente uma MeshLayer.
        4. Extrai informações relevantes da malha, incluindo:
            - Tipo de camada ("Mesh")
            - SRC (sistema de referência de coordenadas)
            - Número de nós (vertices)
            - Número de faces (elementos)
        5. Formata todas essas informações em um texto amigável.
        6. Exibe o tooltip na posição atual do cursor do mouse.
        """
        item = index.model().itemFromIndex(index)
        layer_id = item.data(Qt.ItemDataRole.UserRole)
        layer = QgsProject.instance().mapLayer(layer_id)

        if layer and layer.type() == QgsMapLayer.LayerType.MeshLayer:
            # Tipo de camada (Mesh)
            tipo_malha = self.obter_tipo_de_malha(layer)

            # SRC
            crs = layer.crs().description() if layer.crs().isValid() else self.tr("Sem Georreferenciamento")

            # Fonte do dado (arquivo/path)
            source = layer.source()

            # Obtém o provider para informações de geometria
            prov = layer.dataProvider()

            # Número de nós (vértices)
            num_vertices = prov.vertexCount() if hasattr(prov, "vertexCount") else "N/D"

            # Número de faces (elementos)
            num_faces = prov.faceCount() if hasattr(prov, "faceCount") else "N/D"

            # Monta o texto do tooltip
            tooltip_text = self.tr("SRC: {crs}\nArquivo: {source}\nVértices: {num_vertices}\nFaces: {num_faces}").format(
                crs=crs,
                source=source,
                num_vertices=num_vertices,
                num_faces=num_faces)

            # Exibe o tooltip
            QToolTip.showText(QCursor.pos(), tooltip_text)

    def obter_tipo_de_malha(self, layer):
        """
        Retorna uma string descritiva do tipo de camada mesh.

        Para camadas mesh padrão do QGIS, retorna 'Mesh'.
        """
        if layer.type() == QgsMapLayer.LayerType.MeshLayer:
            return "Mesh"
        return self.tr("Desconhecido")

    def close_dialog(self):
        """
        Fecha o diálogo associado a este UiManagerM:
        """
        self.dlg.close()

    def atualizar_treeView_lista_malha(self):
        """
        Atualiza o TreeView que lista as camadas de malhas no QGIS.
        """

        tv = self.dlg.treeViewListaMalha

        # 0) GARANTE que o TreeView tem model (evita model() == None)
        if tv.model() is not self.treeViewModel:
            tv.setModel(self.treeViewModel)

        # 1) Guarda o layer_id selecionado ANTES de recriar o modelo
        current_layer_id = None
        current_index = tv.currentIndex()
        if current_index.isValid():
            current_layer_id = current_index.data(Qt.ItemDataRole.UserRole)

        # 2) Reconstrói o modelo
        self.treeViewModel.clear()

        headerItem = QStandardItem(self.tr("Lista de Camadas de Malhas"))
        headerItem.setTextAlignment(Qt.AlignmentFlag.AlignCenter)
        self.treeViewModel.setHorizontalHeaderItem(0, headerItem)

        root = QgsProject.instance().layerTreeRoot()

        for layer in QgsProject.instance().mapLayers().values():
            if layer.type() == QgsMapLayer.LayerType.MeshLayer:
                item = QStandardItem(layer.name())
                item.setCheckable(True)
                item.setEditable(False)
                item.setData(layer.id(), Qt.ItemDataRole.UserRole)

                item.setCheckState(
                    Qt.CheckState.Checked
                    if self.camada_esta_visivel(layer)
                    else Qt.CheckState.Unchecked)

                self.adjust_item_font(item, layer)
                self.treeViewModel.appendRow(item)

        # 3) Seleção/scroll (AGORA fora do loop)
        row_count = self.treeViewModel.rowCount()
        if row_count == 0:
            return

        target_row = 0
        if current_layer_id:
            for r in range(row_count):
                it = self.treeViewModel.item(r, 0)
                if it and it.data(Qt.ItemDataRole.UserRole) == current_layer_id:
                    target_row = r
                    break

        target_index = self.treeViewModel.index(target_row, 0)
        tv.setCurrentIndex(target_index)
        tv.scrollTo(target_index)
        self.sync_from_qgis_to_treeview()

    def _node_checkbox_checked(self, node):
        """
        Retorna o estado do checkbox do nó na árvore de camadas,
        sem confundir com a visibilidade herdada de grupos.
        """
        if node is None:
            return False

        try:
            return bool(node.itemVisibilityChecked())
        except Exception:
            try:
                return bool(node.isVisible())
            except Exception:
                return False

    def _on_any_layer_tree_visibility_changed(self, node):
        """
        Mantém o treeView sincronizado quando o checkbox muda no painel do QGIS.
        """
        if isinstance(node, QgsLayerTreeLayer):
            self.atualizar_item_visibilidade(node)
        else:
            self.sync_from_qgis_to_treeview()

    def camada_esta_visivel(self, layer):
        """
        Retorna o estado do checkbox da camada na árvore do QGIS.
        """
        layer_tree_layer = QgsProject.instance().layerTreeRoot().findLayer(layer.id())
        return self._node_checkbox_checked(layer_tree_layer)

    def atualizar_item_visibilidade(self, layer_tree_layer):
        """
        Atualiza o checkbox do item correspondente no treeView.
        """
        if not isinstance(layer_tree_layer, QgsLayerTreeLayer):
            self.sync_from_qgis_to_treeview()
            return

        model = self.dlg.treeViewListaMalha.model()
        if model is None:
            return

        target_id = layer_tree_layer.layerId()
        desired = (Qt.CheckState.Checked
            if self._node_checkbox_checked(layer_tree_layer)
            else Qt.CheckState.Unchecked)

        self._tree_sync_depth = getattr(self, "_tree_sync_depth", 0) + 1
        try:
            for row in range(model.rowCount()):
                item = model.item(row)
                if not item:
                    continue
                if item.data(Qt.ItemDataRole.UserRole) != target_id:
                    continue

                if item.checkState() != desired:
                    item.setCheckState(desired)
                break
        finally:
            self._tree_sync_depth = max(0, getattr(self, "_tree_sync_depth", 1) - 1)

    def on_treeview_item_clicked(self, index):
        """
        Fallback para garantir a aplicação da visibilidade no QGIS
        quando o clique no checkbox não disparar itemChanged como esperado.
        """
        if not index.isValid():
            return

        item = self.treeViewModel.itemFromIndex(index)
        if item is None:
            return

        self.on_item_changed(item)

    def on_current_layer_changed(self, layer):
        """
        Sincroniza a seleção do treeView com a camada ativa no QGIS.
        """
        if getattr(self, "_selection_sync_depth", 0) > 0:
            return

        model = self.dlg.treeViewListaMalha.model()
        if model is None or model.rowCount() == 0:
            return

        if not layer or layer.type() != QgsMapLayer.LayerType.MeshLayer:
            return

        layer_id = layer.id()

        for row in range(model.rowCount()):
            item = model.item(row, 0)
            if item and item.data(Qt.ItemDataRole.UserRole) == layer_id:
                index = model.indexFromItem(item)
                current = self.dlg.treeViewListaMalha.currentIndex()

                if current != index:
                    self._selection_sync_depth += 1
                    try:
                        self.dlg.treeViewListaMalha.setCurrentIndex(index)
                        self.dlg.treeViewListaMalha.scrollTo(index)
                    finally:
                        self._selection_sync_depth = max(0, self._selection_sync_depth - 1)
                break

    def on_item_changed(self, item):
        """
        Atualiza a visibilidade da camada no QGIS quando o checkbox do treeView muda.
        """
        if item is None:
            return

        if getattr(self, "_tree_sync_depth", 0) > 0:
            return

        layer_id = item.data(Qt.ItemDataRole.UserRole)
        if not layer_id:
            return

        root = QgsProject.instance().layerTreeRoot()
        node = root.findLayer(layer_id)
        if node is None:
            return

        desired = (item.checkState() == Qt.CheckState.Checked)

        try:
            current = bool(node.itemVisibilityChecked())
        except Exception:
            try:
                current = bool(node.isVisible())
            except Exception:
                current = None

        if current != desired:
            node.setItemVisibilityChecked(desired)

    def on_layers_removed(self, removed_ids):
        """
        Remove do treeView apenas as linhas correspondentes às malhas removidas do projeto.
        """
        if self.treeViewModel.rowCount() == 0:
            return

        self._tree_sync_depth += 1
        self._selection_sync_depth += 1
        try:
            last_removed_row = 0

            for rid in removed_ids:
                for row in range(self.treeViewModel.rowCount()):
                    item = self.treeViewModel.item(row)
                    if item and item.data(Qt.ItemDataRole.UserRole) == rid:
                        last_removed_row = row
                        self.treeViewModel.removeRow(row)
                        break

            model = self.dlg.treeViewListaMalha.model()
            if model is not None and model.rowCount() > 0:
                current_index = self.dlg.treeViewListaMalha.currentIndex()
                if not current_index.isValid():
                    target_row = min(last_removed_row, model.rowCount() - 1)
                    idx = model.index(target_row, 0)
                    self.dlg.treeViewListaMalha.setCurrentIndex(idx)
                    self.dlg.treeViewListaMalha.scrollTo(idx)
        finally:
            self._selection_sync_depth = max(0, self._selection_sync_depth - 1)
            self._tree_sync_depth = max(0, self._tree_sync_depth - 1)

        self.atualizar_estado_botoes()

    def on_treeview_selection_changed(self, selected, deselected):
        """
        Descrição:
        Função chamada sempre que a seleção no QTreeView de malhas é alterada.
        Ela obtém o item selecionado e, caso corresponda a uma camada de malha,
        torna essa camada ativa no QGIS.

        Parâmetros:
        - selected (QItemSelection): Itens que passaram a ser selecionados.
        - deselected (QItemSelection): Itens que deixaram de ser selecionados.

        Passos:
        1. Obtém os índices dos itens atualmente selecionados no treeView.
        2. Se não houver seleção, encerra sem fazer nada.
        3. Recupera o ID da camada armazenado no primeiro item selecionado.
        4. Busca o objeto QgsMapLayer a partir desse ID no projeto.
        5. Se a camada existir e for válida, define-a como camada ativa na interface.
        """
        # 1. Obtém os índices dos itens selecionados no QTreeView de malhas
        indexes = self.dlg.treeViewListaMalha.selectionModel().selectedIndexes()
        # 2. Verifica se não há nenhum índice selecionado; se não houver, sai da função
        if not indexes:
            return

        # 3. Recupera a ID da camada armazenada em Qt.UserRole do primeiro índice
        layer_id = self.treeViewModel.itemFromIndex(indexes[0]).data(Qt.ItemDataRole.UserRole)
        # 4. Busca a camada no projeto QGIS usando a ID recuperada
        layer = QgsProject.instance().mapLayer(layer_id)

        if (layer
            and layer.type() == QgsMapLayer.LayerType.MeshLayer):
            self.iface.setActiveLayer(layer)

    def on_layer_was_renamed(self, layerId, newName):
        """
        Descrição:
        Função chamada sempre que uma camada é renomeada no projeto QGIS.
        Atualiza o item correspondente no treeView de malhas para exibir o novo nome.

        Parâmetros:
        - layerId (str): ID única da camada que foi renomeada.
        - newName (str): Novo nome atribuído à camada.

        Passos:
        1. Percorrer todas as linhas do modelo do treeView.
        2. Para cada item, verificar se o dado em Qt.UserRole é igual a layerId.
        3. Se encontrar correspondência, atualizar o texto do item com newName.
        4. Interromper o loop após atualizar o nome.
        """
        # 1. Percorre todas as linhas do modelo do treeView de malhas
        for i in range(self.treeViewModel.rowCount()):
            # 1.1. Obtém o item da linha i, coluna 0
            item = self.treeViewModel.item(i)
            # 2. Verifica se o UserRole (ID da camada) coincide com o layerId passado
            if item.data(Qt.ItemDataRole.UserRole) == layerId:
                # 3. Atualiza o texto do item para refletir o novo nome da camada
                item.setText(newName)
                # 4. Sai do loop, pois já atualizamos o item correto
                break

    def sync_from_qgis_to_treeview(self):
        """
        Sincroniza o checkbox do treeView com o checkbox real da árvore do QGIS.
        """
        root = QgsProject.instance().layerTreeRoot()

        self._tree_sync_depth = getattr(self, "_tree_sync_depth", 0) + 1
        try:
            for i in range(self.treeViewModel.rowCount()):
                item = self.treeViewModel.item(i)
                if not item:
                    continue

                layer_id = item.data(Qt.ItemDataRole.UserRole)
                node = root.findLayer(layer_id) if layer_id else None
                if not node:
                    continue

                desired = (
                    Qt.CheckState.Checked
                    if self._node_checkbox_checked(node)
                    else Qt.CheckState.Unchecked)

                if item.checkState() != desired:
                    item.setCheckState(desired)
        finally:
            self._tree_sync_depth = max(0, getattr(self, "_tree_sync_depth", 1) - 1)

    def adjust_item_font(self, item, layer):
        """
        Esta função ajusta a fonte do item no QTreeView com base no tipo de camada.
        Se a camada for temporária (dados em memória), ajusta a fonte para itálico.
        Se a camada for permanente, ajusta a fonte para negrito.

        Detalhes:
        - Cria um objeto QFont para ajustar a fonte do item.
        - Verifica se a camada é temporária usando o método isTemporary().
        - Se a camada for temporária, ajusta a fonte para itálico.
        - Se a camada for permanente, ajusta a fonte para negrito.
        - Aplica a fonte ajustada ao item no QTreeView.
        - Retorna o item com a fonte ajustada para uso posterior, se necessário.
        """
        # Cria um objeto QFont para ajustar a fonte do item
        fonte_item = QFont()

        # Verifica se a camada é temporária (dados em memória) e ajusta a fonte para itálico
        if layer.isTemporary():
            fonte_item.setItalic(True)
        # Se não for temporária, ajusta a fonte para negrito, indicando uma camada permanente
        else:
            fonte_item.setBold(True)

        # Aplica a fonte ajustada ao item no QTreeView
        item.setFont(fonte_item)

        # Retorna o item com a fonte ajustada para uso posterior se necessário
        return item

    def connect_name_changed_signals(self):
        """
        Conecta o sinal nameChanged de todas as camadas reais do projeto.
        Ignora grupos e nós sem camada associada.
        Evita conexões duplicadas.
        """
        root = QgsProject.instance().layerTreeRoot()

        for layerNode in root.findLayers():
            if isinstance(layerNode, QgsLayerTreeLayer):
                layer = layerNode.layer()
                if layer is not None:
                    try:
                        # desconecta primeiro para evitar duplicidade
                        layer.nameChanged.disconnect(self.on_layer_name_changed)
                    except TypeError:
                        # se não estava conectado, ignora o erro
                        pass  # nosec B110

                    # conecta de forma segura
                    layer.nameChanged.connect(self.on_layer_name_changed)

    def layers_added(self, layers):
        """
        Atualiza o treeView quando novas camadas de malha são adicionadas ao projeto,
        aguardando um ciclo da UI para o nó da árvore do QGIS estabilizar.
        """
        mesh_layers = [
            layer for layer in layers
            if layer.type() == QgsMapLayer.LayerType.MeshLayer]

        if not mesh_layers:
            return

        for layer in mesh_layers:
            try:
                layer.nameChanged.disconnect(self.on_layer_name_changed)
            except TypeError:
                pass  # nosec B110
            layer.nameChanged.connect(self.on_layer_name_changed)

        def _refresh_after_qgis_tree_settles():
            self.atualizar_treeView_lista_malha()
            self.sync_from_qgis_to_treeview()
            self.atualizar_estado_botoes()

        QTimer.singleShot(0, _refresh_after_qgis_tree_settles)

    def on_layer_name_changed(self):
        """
        Responde ao evento de mudança de nome de qualquer camada no projeto QGIS. 
        Este método é chamado automaticamente quando o nome de uma camada é alterado,
        e sua função é garantir que a lista de camadas no QTreeView seja atualizada para refletir
        essa mudança.

        Funções e Ações Desenvolvidas:
        - Atualização da lista de camadas no QTreeView para assegurar que os nomes das camadas estejam corretos.
        """
        # Atualiza a lista de camadas no QTreeView para refletir a mudança de nome
        self.atualizar_treeView_lista_malha()

    def open_context_menu(self, position):
        """
        Esta função abre um menu de contexto ao clicar com o botão direito na árvore de visualização (QTreeView).
        Se um item for selecionado, cria e exibe um menu de contexto com a opção de abrir as propriedades da camada.
        
        Detalhes:
        - Obtém os índices dos itens selecionados no QTreeView.
        - Verifica se há algum item selecionado.
        - Se houver um item selecionado:
            - Cria um novo menu de contexto.
            - Adiciona a opção "Abrir Propriedades da Camada" ao menu de contexto.
            - Exibe o menu de contexto na posição do cursor.
            - Executa a ação correspondente se a opção "Abrir Propriedades da Camada" for selecionada.
        """
        # Obtém os índices dos itens selecionados na árvore de visualização
        indexes = self.dlg.treeViewListaMalha.selectedIndexes()
        
        # Verifica se algum item foi selecionado
        if indexes:
            # Cria um novo menu de contexto
            menu = QMenu()
            
            # Adiciona uma ação ao menu de contexto
            layer_properties_action = menu.addAction(self.tr("Abrir Propriedades da Camada"))
            
            # Exibe o menu de contexto na posição do cursor e obtém a ação selecionada pelo usuário
            action = menu.exec(self.dlg.treeViewListaMalha.viewport().mapToGlobal(position))
            
            # Verifica se a ação selecionada foi "Abrir Propriedades da Camada"
            if action == layer_properties_action:
                # Abre as propriedades da camada para o item selecionado
                self.abrir_layer_properties(indexes[0])

    def abrir_layer_properties(self, index):
        """
        Abre a janela de propriedades da camada selecionada no QTreeView. Este método é chamado quando o usuário deseja
        ver ou editar as propriedades de uma camada específica, como símbolos, campos e outras configurações.

        Funções e Ações Desenvolvidas:
        - Obtenção do ID da camada a partir do item selecionado no QTreeView.
        - Recuperação da camada correspondente no projeto QGIS.
        - Exibição da janela de propriedades da camada se ela for encontrada.

        :param index: O índice do modelo que representa o item selecionado no QTreeView.
        """
        # Obtém o ID da camada do item selecionado no treeView
        layer_id = index.model().itemFromIndex(index).data(Qt.ItemDataRole.UserRole)
        
        # Busca a camada correspondente no projeto QGIS usando o ID
        layer = QgsProject.instance().mapLayer(layer_id)
        
        # Se a camada for encontrada, exibe a janela de propriedades da camada
        if layer:
            self.iface.showLayerProperties(layer)

    def escolher_local_para_salvar(self, nome_padrao, tipo_arquivo):
        """
        Permite ao usuário escolher um local e um nome de arquivo para salvar uma camada, usando uma caixa de diálogo.
        O método também gerencia nomes de arquivos para evitar sobreposição e lembra o último diretório utilizado.

        Funções e Ações Desenvolvidas:
        - Recuperação do último diretório utilizado através das configurações do QGIS.
        - Geração de um nome de arquivo único para evitar sobreposição.
        - Exibição de uma caixa de diálogo para escolha do local de salvamento.
        - Atualização do último diretório utilizado nas configurações do QGIS.

        :param nome_padrao: Nome padrão proposto para o arquivo a ser salvo.
        :param tipo_arquivo: Descrição do tipo de arquivo para a caixa de diálogo (ex. "Arquivos DXF (*.dxf)").

        :return: O caminho completo do arquivo escolhido para salvar ou None se nenhum arquivo foi escolhido.
        """
        # Acessa as configurações do QGIS para recuperar o último diretório utilizado
        settings = QSettings()
        lastDir = settings.value("lastDir", "")  # Usa uma string vazia como padrão se não houver último diretório
        
        # Gera um nome de arquivo com um sufixo numérico caso o arquivo já exista
        base_nome_padrao, extensao = os.path.splitext(nome_padrao)
        numero = 1
        nome_proposto = base_nome_padrao
        
        # Incrementa o número no nome até encontrar um nome que não exista
        while os.path.exists(os.path.join(lastDir, nome_proposto + extensao)):
            nome_proposto = f"{base_nome_padrao}_{numero}"
            numero += 1

        # Propõe o nome completo no último diretório utilizado
        nome_completo_proposto = os.path.join(lastDir, nome_proposto + extensao)

        # Exibe a caixa de diálogo para salvar arquivos com o nome proposto
        fileName, _ = QFileDialog.getSaveFileName(self.dlg, self.tr("Salvar Camada"), nome_completo_proposto, tipo_arquivo)

        # Verifica se um nome de arquivo foi escolhido
        if fileName:
            # Atualiza o último diretório usado nas configurações do QGIS
            settings.setValue("lastDir", os.path.dirname(fileName))

            # Assegura que o arquivo tenha a extensão correta
            if not fileName.endswith(extensao):
                fileName += extensao

        return fileName  # Retorna o caminho completo do arquivo escolhido ou None se cancelado

    def mostrar_mensagem(self, texto, tipo, duracao=3, caminho_pasta=None, caminho_arquivo=None):
        """
        Exibe mensagens na barra do QGIS.

        Tipos aceitos:
        - Erro
        - Informação / Info
        - Aviso / Alerta / Warning
        - Sucesso
        """
        bar = self.iface.messageBar()

        if tipo == "Erro":
            bar.pushMessage(self.tr("Erro"), texto, level=Qgis.MessageLevel.Critical, duration=duracao)
            return

        if tipo in ("Informação", "Info"):
            bar.pushMessage(self.tr("Informação"), texto, level=Qgis.MessageLevel.Info, duration=duracao)
            return

        if tipo in ("Aviso", "Alerta", "Warning"):
            bar.pushMessage(self.tr("Aviso"), texto, level=Qgis.MessageLevel.Warning, duration=duracao)
            return

        if tipo == "Sucesso":
            msg = bar.createMessage(self.tr("Sucesso"), texto)

            if caminho_pasta:
                botao_abrir_pasta = QPushButton(self.tr("Abrir Pasta"))

                def abrir_pasta():
                    url = QUrl.fromLocalFile(
                        str(pathlib.Path(caminho_pasta).resolve()))
                    QDesktopServices.openUrl(url)

                botao_abrir_pasta.clicked.connect(abrir_pasta)
                msg.layout().insertWidget(1, botao_abrir_pasta)

            if caminho_arquivo:
                botao_executar = QPushButton(
                    self.tr("Executar"))

                def abrir_arquivo():
                    url = QUrl.fromLocalFile(
                        str(pathlib.Path(caminho_arquivo).resolve()))
                    QDesktopServices.openUrl(url)

                botao_executar.clicked.connect(abrir_arquivo)
                msg.layout().insertWidget(2, botao_executar)

            bar.pushWidget(msg, level=Qgis.MessageLevel.Info, duration=duracao)
            return

        bar.pushMessage(self.tr("Informação"), texto, level=Qgis.MessageLevel.Info, duration=duracao)

    def iniciar_progress_bar(self, total_steps, titulo=None):
        if titulo is None:
            titulo = self.tr("Exportando malha...")
        """
        Cria e exibe uma barra de progresso na barra de mensagens do QGIS.

        Parâmetros
        total_steps : int
            Número total de etapas (valor máximo da barra de progresso).
        titulo : str, opcional
            Texto exibido na mensagem junto à barra (padrão: "Exportando malha...").

        Retorna
        (QProgressBar, QWidget)
            A barra de progresso criada e o widget de mensagem associado.
        """
        # Cria a mensagem na barra do QGIS com o título fornecido
        progressMessageBar = self.iface.messageBar().createMessage(titulo)

        # Cria a barra de progresso Qt
        progressBar = QProgressBar()
        progressBar.setAlignment(Qt.AlignmentFlag.AlignLeft | Qt.AlignmentFlag.AlignVCenter)  # alinha texto à esquerda/verticalmente
        progressBar.setFormat(self.tr("%p% - %v de %m etapas concluídas"))  # formato do texto exibido
        progressBar.setMinimumWidth(300)  # largura mínima em px

        # Define o estilo visual da barra
        progressBar.setStyleSheet("""
            QProgressBar {
                border: 1px solid grey;
                border-radius: 2px;
                background-color: #cddbde;
                text-align: center;
            }
            QProgressBar::chunk {
                background-color: #55aaff;
                width: 5px;
                margin: 1px;
            }
            QProgressBar { min-height: 5px; }""")

        # Adiciona a barra ao layout da mensagem
        progressMessageBar.layout().addWidget(progressBar)

        # Publica a mensagem com a barra na barra do QGIS
        self.iface.messageBar().pushWidget(progressMessageBar, Qgis.MessageLevel.Info)

        # Define o número máximo de etapas para a barra
        progressBar.setMaximum(total_steps)

        # Retorna a barra e o widget de mensagem (para poder atualizar/fechar depois)
        return progressBar, progressMessageBar

    def mostrar_dialogo_exporta_malha_3d(self):
        """
        Exibe o diálogo para exportação da malha 3D e conecta os botões para exportação em diferentes formatos.

        Funções e Ações Desenvolvidas:
        - Cria e exibe o diálogo ExportaMalha3D.
        - Conecta os botões do diálogo às funções de exportação correspondentes (DXF, DAE, OBJ, STL).
        - Executa o diálogo de exportação de malha 3D.

        """
        # Cria uma instância do diálogo ExportaMalha3D passando o diálogo principal como pai
        self.dlg_exporta_malha = ExportaMalha3D(self.dlg)
        
        # Conecta o botão DXF à função de exportação de malha para DXF
        self.dlg_exporta_malha.button_dxf.clicked.connect(lambda: self.exportar_malha("DXF"))
        
        # Conecta o botão DAE à função de exportação de malha para DAE
        self.dlg_exporta_malha.button_dae.clicked.connect(lambda: self.exportar_malha("DAE"))
        
        # Conecta o botão OBJ à função de exportação de malha para OBJ
        self.dlg_exporta_malha.button_obj.clicked.connect(lambda: self.exportar_malha("OBJ"))
        
        # Conecta o botão STL à função de exportação de malha para STL
        self.dlg_exporta_malha.button_stl.clicked.connect(lambda: self.exportar_malha("STL"))
        
        # Executa o diálogo de exportação de malha 3D
        self.dlg_exporta_malha.exec()

    def convert_mesh_to_polygons_and_points(self, mesh_layer):
        """
        Converte uma camada de malha para polígonos e extrai os pontos com coordenadas Z.

        A função usa algoritmos de processamento nativos do QGIS para exportar faces da malha como polígonos e vértices da malha como pontos.
        Em seguida, adiciona campos ID e Altitude às feições resultantes.

        Funções e Ações Desenvolvidas:
        - Exporta as faces da malha como polígonos.
        - Adiciona um campo ID à camada de polígonos.
        - Converte a camada de polígonos para MultiSurface (MultiPolygonZ).
        - Exporta os vértices da malha como pontos.
        - Adiciona campos ID e Altitude à camada de pontos.
        - Cria um dicionário para mapear as coordenadas dos pontos às suas altitudes.

        :param mesh_layer: Camada de malha a ser convertida (QgsMeshLayer).
        :return: Uma tupla contendo a camada de polígonos MultiSurface (MultiPolygonZ) e um dicionário de valores de altitude dos pontos.
        """
        # Obter o CRS da camada de malha
        crs = mesh_layer.crs()
        
        # Configurar parâmetros para o algoritmo de processamento de polígonos
        params_polygons = {
            'INPUT': mesh_layer,
            'DATASET_GROUPS': [],  # Ajuste conforme necessário
            'DATASET_TIME': {'type': 'static'},  # Configurar o tipo de tempo como estático
            'CRS_OUTPUT': crs.toWkt(),  # Definir o CRS de saída como o mesmo da camada de malha
            'VECTOR_OPTION': 0,  # 0 para Polygons
            'OUTPUT': 'memory:Polygons from TIN Mesh'}
        
        # Executar o algoritmo de processamento para polígonos
        result_polygons = processing.run("native:exportmeshfaces", params_polygons)
        
        # Obter a camada de polígonos resultante
        poly_layer = result_polygons['OUTPUT']
        
        # Adicionar campo ID à camada de polígonos
        provider_poly = poly_layer.dataProvider()
        provider_poly.addAttributes([QgsField("ID", QMetaType.Type.Int)])
        poly_layer.updateFields()
        
        # Atribuir valores de ID para cada feição
        with edit(poly_layer):
            for i, feature in enumerate(poly_layer.getFeatures()):
                feature.setAttribute("ID", i + 1)  # ID começa em 1
                poly_layer.updateFeature(feature)
        
        # Converter a camada de polígonos para MultiSurface (MultiPolygonZ)
        multi_poly_layer = self.convert_to_multisurface(poly_layer)
        
        # Configurar parâmetros para o algoritmo de processamento de pontos
        params_points = {
            'INPUT': mesh_layer,
            'DATASET_GROUPS': [],  # Ajuste conforme necessário
            'DATASET_TIME': {'type': 'static'},  # Configurar o tipo de tempo como estático
            'CRS_OUTPUT': crs.toWkt(),  # Definir o CRS de saída como o mesmo da camada de malha
            'VECTOR_OPTION': 1,  # 1 para pontos
            'OUTPUT': 'memory:Mesh Vertices'}
        
        # Executar o algoritmo de processamento para pontos
        result_points = processing.run("native:exportmeshvertices", params_points)
        
        # Obter a camada de pontos resultante
        point_layer = result_points['OUTPUT']
        
        # Adicionar campo ID e Altimetria à camada de pontos
        provider_point = point_layer.dataProvider()
        provider_point.addAttributes([QgsField("ID", QMetaType.Type.Int), QgsField("Altitude", QMetaType.Type.Double)])
        point_layer.updateFields()
        
        # Atribuir valores de ID e Altimetria para cada feição
        point_z_values = {}
        with edit(point_layer):
            for i, feature in enumerate(point_layer.getFeatures()):
                geom = feature.geometry()
                if QgsWkbTypes.hasZ(geom.wkbType()):  # Verificar se a geometria tem coordenada Z
                    point = geom.constGet()  # Obter a geometria como QgsPoint
                    feature.setAttribute("ID", i + 1)  # ID começa em 1
                    feature.setAttribute("Altitude", point.z())  # Define a altimetria (z-coordinate)
                    point_z_values[(point.x(), point.y())] = point.z() # Adicionar ao dicionário de valores de Z
                    point_layer.updateFeature(feature) # Atualizar feição
        # Retornar a camada de polígonos e o dicionário de valores de Z
        return multi_poly_layer, point_z_values 

    def convert_to_multisurface(self, poly_layer):
        """
        Converte uma camada de polígonos simples em uma camada de MultiSurface (MultiPolygonZ).

        A função cria uma nova camada de memória que armazena polígonos como MultiPolygonZ, preservando os atributos e IDs das feições originais.

        Funções e Ações Desenvolvidas:
        - Cria uma nova camada de MultiSurface (MultiPolygonZ) com o mesmo CRS da camada de entrada.
        - Adiciona um campo ID à nova camada.
        - Converte cada feição da camada de polígonos simples para MultiPolygon e adiciona à nova camada.
        
        :param poly_layer: Camada de polígonos simples a ser convertida (QgsVectorLayer).
        :return: A nova camada de MultiSurface (MultiPolygonZ) (QgsVectorLayer).
        """
        # Criar uma nova camada de MultiSurface (MultiPolygonZ)
        multi_poly_layer = QgsVectorLayer(f"MultiPolygonZ?crs={poly_layer.crs().authid()}", "MultiSurface Polygons", "memory")
        provider_multi_poly = multi_poly_layer.dataProvider()
        
        # Adicionar campo ID à nova camada
        provider_multi_poly.addAttributes([QgsField("ID", QMetaType.Type.Int)])
        multi_poly_layer.updateFields()
        
        # Converter cada feição para MultiPolygon e adicionar à nova camada
        with edit(multi_poly_layer):
            for feature in poly_layer.getFeatures():
                geom = feature.geometry() # Obter a geometria da feição
                if geom.isMultipart():
                    multi_geom = geom # Se a geometria já for multipart, mantê-la como está
                else:
                    multi_geom = QgsGeometry.fromMultiPolygonXY([geom.asPolygon()])  # Converter para MultiPolygon
                new_feature = QgsFeature()  # Criar uma nova feição
                new_feature.setGeometry(multi_geom)  # Definir a geometria da nova feição
                new_feature.setAttributes(feature.attributes())  # Copiar atributos da feição original
                multi_poly_layer.addFeature(new_feature)  # Adicionar a nova feição à camada
        
        return multi_poly_layer  # Retornar a nova camada de MultiSurface (MultiPolygonZ)

    def criar_simbologia_gradiente(self, valores):
        """
        Cria uma simbologia gradiente de vermelho, laranja, amarelo e verde baseada nos valores fornecidos.

        Funções e Ações Desenvolvidas:
        - Calcula os valores mínimo e máximo da lista fornecida.
        - Interpola cores entre vermelho, laranja, amarelo e verde com base nos valores fornecidos.
        - Cria um dicionário onde as chaves são os valores fornecidos e os valores são listas RGBA.

        :param valores: Lista de valores para os quais a simbologia será aplicada.
        :return: Um dicionário com valores como chave e a cor RGBA correspondente como valor.
        """
        cores = {}  # Dicionário para armazenar as cores
        min_valor = min(valores)  # Calcula o valor mínimo da lista
        max_valor = max(valores)  # Calcula o valor máximo da lista

        # Itera sobre cada valor na lista de valores
        for valor in valores:
            ratio = (valor - min_valor) / (max_valor - min_valor)  # Calcula a razão normalizada do valor

            # Interpola a cor com base na razão
            if ratio < 0.33:
                # Interpolação de vermelho para laranja
                r = 1.0  # Vermelho constante
                g = ratio * 3.0  # Verde cresce de 0 a 1
                b = 0.0  # Azul constante
            elif ratio < 0.66:
                # Interpolação de laranja para amarelo
                r = 1.0 - (ratio - 0.33) * 3.0  # Vermelho decresce de 1 a 0
                g = 1.0  # Verde constante
                b = 0.0  # Azul constante
            else:
                # Interpolação de amarelo para verde
                r = 0.0  # Vermelho constante
                g = 1.0  # Verde constante
                b = (ratio - 0.66) * 3.0  # Azul cresce de 0 a 1
            a = 1.0  # Alfa constante
            cores[valor] = [r, g, b, a]  # Adiciona a cor interpolada ao dicionário

        return cores  # Retorna o dicionário de cores

    def abrir_visualizador_malha_3d(self):
        """
        Visualização 3D sem travar a UI:
          1) Mostra barra INDETERMINADA de imediato;
          2) Roda PrepTask (mesh -> polygons + dict Z) em background;
          3) Ao terminar, inicia BuffersWorker (triangulação) em QThread;
          4) Quando BuffersWorker informar o total, troca a barra para DETERMINADA;
          5) Abre VisualizadorDAE3D direto dos buffers; fallback: DAE em disco.
        """
        # 0) Resolve camada selecionada
        indexes = self.dlg.treeViewListaMalha.selectedIndexes()
        if not indexes:
            self.mostrar_mensagem(self.tr("Nenhuma camada selecionada"), "Erro"); return
        selected_layer_name = self.treeViewModel.itemFromIndex(indexes[0]).text()
        layers = QgsProject.instance().mapLayersByName(selected_layer_name)
        if not layers:
            self.mostrar_mensagem(self.tr("Camada não encontrada"), "Erro"); return
        layer = layers[0]
        if not isinstance(layer, QgsMeshLayer):
            self.mostrar_mensagem(self.tr("A camada selecionada não é uma malha"), "Erro"); return

        msg_bar = self.iface.messageBar()

        # 1) Mensagem + barra INDETERMINADA imediata
        prep_item = msg_bar.createMessage(self.tr("Aguarde"), self.tr("Preparando malha para visualização…"))
        prep_bar = QProgressBar(); prep_bar.setRange(0, 0)  # indeterminada
        prep_item.layout().addWidget(prep_bar)
        msg_bar.pushWidget(prep_item, Qgis.MessageLevel.Info)

        # manter refs vivas
        self._viewer_msg_item = prep_item
        self._viewer_msg_bar  = prep_bar

        def dismiss_bar():
            try:
                msg_bar.popWidget(prep_item)
            except Exception:
                try: prep_item.close()
                except Exception: pass  # nosec B110
            self._viewer_msg_item = None
            self._viewer_msg_bar  = None

        # 2) Deferir 1 tick para a barra aparecer antes de começar a preparar
        def _start_prep_task():
            try:
                # Task de preparação (background)
                task = PrepTask(self, layer.id())
                self._viewer_prep_task = task  # guardar para GC/cancel

                # Quando a preparação terminar com sucesso → inicia triangulação
                def on_prep_ok(polygons, point_z_values):
                    # 3) Worker de buffers (triangulação) em QThread
                    thread = QThread(self.iface.mainWindow())
                    worker = BuffersWorker(polygons, point_z_values)
                    worker.moveToThread(thread)

                    # manter vivos
                    self._viewer_thread = thread
                    self._viewer_worker = worker

                    # ao receber total de faces → barra DETERMINADA
                    def on_max(m):
                        m = max(1, int(m))
                        try:
                            prep_bar.setRange(0, m)
                            prep_bar.setValue(0)
                        except Exception:
                            pass  # nosec B110

                    def on_progress(v):
                        try:
                            if prep_bar.maximum() > 0:
                                prep_bar.setValue(int(v))
                        except Exception:
                            pass  # nosec B110

                    def on_finished(positions, tri_indices, _dur):
                        dismiss_bar()
                        try:
                            visualizador = VisualizadorDAE3D(
                                None, self.dlg, self,
                                positions=positions,
                                tri_indices=tri_indices, camada_origem_id=layer.id())
                            visualizador.show()
                        except Exception as e:
                            self.mostrar_mensagem(self.tr("Erro ao instanciar visualizador: {error}").format(error=e), "Erro")
                        finally:
                            try: thread.quit()
                            except Exception: pass  # nosec B110

                    def on_error(msg):
                        # fallback: caminha via DAE em disco
                        dismiss_bar()
                        try:
                            dae_file_path = self.exportar_malha_para_dae(layer)
                            if not dae_file_path:
                                raise RuntimeError(msg or self.tr("Falha no pipeline de buffers e no fallback DAE."))
                            visualizador = VisualizadorDAE3D(dae_file_path, self.dlg, self,
                            camada_origem_id=layer.id())
                            visualizador.show()
                        except Exception as e:
                            self.mostrar_mensagem(self.tr("Erro ao abrir visualização 3D: {error}").format(error=e), "Erro")
                        finally:
                            try: thread.quit()
                            except Exception: pass  # nosec B110

                    worker.max_value.connect(on_max)
                    worker.progress.connect(on_progress)
                    worker.finished.connect(on_finished)
                    worker.error.connect(on_error)

                    thread.started.connect(worker.run)
                    worker.finished.connect(worker.deleteLater)
                    thread.finished.connect(thread.deleteLater)
                    thread.start()

                def on_prep_failed(msg):
                    dismiss_bar()
                    self.mostrar_mensagem(self.tr("Erro na preparação da malha: {msg}").format(msg=msg), "Erro")

                task.finished_ok.connect(on_prep_ok)
                task.failed.connect(on_prep_failed)

                # dispara a task
                QgsApplication.taskManager().addTask(task)

            except Exception as e:
                dismiss_bar()
                self.mostrar_mensagem(self.tr("Erro ao iniciar preparação: {error}").format(error=e), "Erro")

        QTimer.singleShot(0, _start_prep_task)

    def _to_python_mesh_data(self, faces_layer: QgsVectorLayer, verts_layer: QgsVectorLayer):
        """
        Converte:
          - faces_layer (polígonos) → List[List[List[Tuple[float,float]]]]
            (lista de polígonos; cada polígono = lista de anéis; cada anel = lista de (x,y))
          - verts_layer (pontos Z)   → dict[(x,y)] = z
        Não altera camadas; sem edição.
        """
        # Polígonos (apenas XY; Z virá dos pontos)
        polygons = []  # tipo: List[List[List[Tuple[float,float]]]]
        for feat in faces_layer.getFeatures():
            geom = feat.geometry()
            if geom.isMultipart():
                multi = geom.asMultiPolygon()  # [[[QgsPointXY]]]
                poly_list = []
                for poly in multi:
                    ring_list = []
                    for ring in poly:
                        ring_list.append([(p.x(), p.y()) for p in ring])
                    poly_list.extend([ring_list])
                polygons.extend(poly_list)
            else:
                poly = geom.asPolygon()
                ring_list = []
                for ring in poly:
                    ring_list.append([(p.x(), p.y()) for p in ring])
                polygons.append(ring_list)

        # Pontos com Z
        point_z_values = {}  # {(x,y): z}
        for feat in verts_layer.getFeatures():
            g = feat.geometry()
            if QgsWkbTypes.hasZ(g.wkbType()):
                pt = g.constGet()  # QgsPoint
                # opcional: quantizar para reduzir problemas de igualdade de float
                x = round(pt.x(), 9)
                y = round(pt.y(), 9)
                point_z_values[(x, y)] = pt.z()

        if not polygons or not point_z_values:
            raise ValueError(self.tr("Sem polígonos ou sem pontos Z para exportar."))

        return polygons, point_z_values

    def _set_progressbar_max(self, maxv: int):
        # Se vier 0 (sem triângulos), evita indeterminado eterno
        maxv = maxv if maxv > 0 else 1
        # garante modo determinado
        self.iface.messageBar().currentItem().progressBar().setRange(0, maxv)

    def _set_progressbar_value(self, v: int):
        self.iface.messageBar().currentItem().progressBar().setValue(v)

    def _on_export_finished(self, fmt: str, path: str, duration: float, progressMsgBar=None, close_dialog: bool = True):
        """
        Handler genérico para término de exportação.

        :param fmt: Rótulo do formato (ex.: "STL", "OBJ", "DXF", "DAE").
        :param path: Caminho do arquivo exportado.
        :param duration: Duração em segundos.
        :param progressMsgBar: Item da barra de mensagem (se quiser manipular/fechar algo específico).
        :param close_dialog: Se True, fecha o diálogo de exportação se existir.
        """
        # Limpa a barra de mensagens/progresso
        try:
            if progressMsgBar is not None:
                self.iface.messageBar().popWidget(progressMsgBar)
        except Exception:
            try:
                if progressMsgBar is not None:
                    progressMsgBar.close()
            except Exception:
                pass  # nosec B110

        # Mensagem de sucesso
        self.mostrar_mensagem(self.tr("Camada exportada para {fmt} em {duration:.2f} segundos").format(fmt=fmt, duration=duration), "Sucesso", caminho_pasta=os.path.dirname(path), caminho_arquivo=path)

        # Fecha o diálogo se existir
        if close_dialog and getattr(self, "dlg_exporta_malha", None):
            self.dlg_exporta_malha.close()

    def _on_export_error(self, fmt: str, message: str, progressMsgBar=None):
        """
        Handler genérico para erro de exportação.
        """
        try:
            if progressMsgBar is not None:
                self.iface.messageBar().popWidget(progressMsgBar)
        except Exception:
            try:
                if progressMsgBar is not None:
                    progressMsgBar.close()
            except Exception:
                pass  # nosec B110

        self.mostrar_mensagem(self.tr("Erro ao exportar {fmt}: {message}").format(fmt=fmt, message=message), "Erro")

    def _start_export_worker(self, fmt: str, worker_cls, polygons, point_z_values, save_path: str, progressBar, progressMsgBar, **worker_kwargs):
        """
        Inicia um worker de exportação (DAE/DXF/OBJ/STL) em QThread, conectando sinais
        de progresso e finalização de forma genérica.

        :param fmt: Rótulo do formato ("DAE" | "DXF" | "OBJ" | "STL").
        :param worker_cls: Classe do worker (ex.: DaeExportWorker).
        :param polygons: Dados puros de polígonos (lista de anéis).
        :param point_z_values: Dict[(x,y)] = z.
        :param save_path: Caminho do arquivo de saída.
        :param progressBar: QProgressBar mostrado na QgsMessageBar.
        :param progressMsgBar: QgsMessageBarItem (para opcional cancel/fechamento).
        :param worker_kwargs: kwargs extras para o worker (ex.: binary=True no STL).
        """
        # Criamos contêiner para manter as referências vivas (evita GC)
        if not hasattr(self, "_live_exports"):
            self._live_exports = []

        thread = QThread(self.iface.mainWindow())
        worker = worker_cls(polygons, point_z_values, save_path, **worker_kwargs)
        worker.moveToThread(thread)

        # Ligações de execução e progresso
        thread.started.connect(worker.run)
        worker.max_value.connect(lambda m: progressBar.setRange(0, max(1, m)))
        worker.progress.connect(progressBar.setValue)

        # Finalização/erro genéricos (use seus handlers unificados)
        # ATENÇÃO: garanta que sua assinatura seja _on_export_finished(fmt, path, duration, progressMsgBar=None, ...)
        worker.finished.connect(lambda p, d: self._on_export_finished(fmt, p, d, progressMsgBar))
        worker.error.connect(lambda msg: self._on_export_error(fmt, msg, progressMsgBar))

        # Limpeza Qt
        worker.finished.connect(thread.quit)
        worker.finished.connect(worker.deleteLater)
        thread.finished.connect(thread.deleteLater)

        # Cancelamento pelo X da barra (se existir)
        if hasattr(progressMsgBar, "accepted"):
            progressMsgBar.accepted.connect(worker.cancel)

        # Registrar bundle vivo e removê‑lo ao terminar (mantém refs)
        bundle = {"fmt": fmt, "thread": thread, "worker": worker, "bar": progressBar, "item": progressMsgBar}
        self._live_exports.append(bundle)

        def _remove_bundle():
            try:
                self._live_exports.remove(bundle)
            except Exception:
                pass  # nosec B110
        thread.finished.connect(_remove_bundle)

        # start
        thread.start()

    def exportar_malha_kml(self):
        """
        Exporta a camada de malha selecionada para o formato KML.

        Fluxo:
        1. Abre diálogo para configurar estilo (cores, transparência etc.).
        2. Obtém a camada de malha selecionada na interface.
        3. Pede ao usuário o caminho/arquivo de saída (.kml).
        4. Exibe mensagem inicial e cria barra de progresso.
        5. Inicia o processo de conversão e exportação assíncrona.
        """
        # 1) Diálogo de estilo
        style_dialog = KMLStyleDialog()
        if not style_dialog.exec():
            return
        style_options = style_dialog.get_style_options()

        # 2) Seleção da camada
        indexes = self.dlg.treeViewListaMalha.selectedIndexes()
        if not indexes:
            self.mostrar_mensagem(self.tr("Nenhuma camada selecionada"), "Erro"); 
            return

        selected_layer_name = self.treeViewModel.itemFromIndex(indexes[0]).text()
        layers = QgsProject.instance().mapLayersByName(selected_layer_name)
        if not layers:
            self.mostrar_mensagem(self.tr("Camada não encontrada"), "Erro")
            return

        layer = layers[0]
        if not isinstance(layer, QgsMeshLayer):
            self.mostrar_mensagem(self.tr("A camada selecionada não é uma malha"), "Erro"); 
            return

        # 3) Caminho de saída
        save_path = self.escolher_local_para_salvar(layer.name() + ".kml", "KML Files (*.kml)")
        if not save_path:
            return

        # 4) Mensagem inicial + Barra com título correto
        self.mostrar_mensagem(self.tr("Aguarde, iniciando exportação da camada para KML"), "Informação", duracao=2)

        progressBar, progressMsgBar = self.iniciar_progress_bar(0, titulo = self.tr("Exportando malha para KML"))
        progressBar.setRange(0, 0)  # indeterminado durante a conversão

        # 5) Conversão + start worker
        self._kml_convert_and_export_with_tasks(layer, save_path, progressBar, progressMsgBar, style_options)

    def _kml_convert_and_export_with_tasks(self, mesh_layer, save_path, progressBar, progressMsgBar, style_options):
        """
        KML:
        - Cria APENAS a task das FACES (assíncrona, com descrição controlada)
        - Ao concluir faces, exporta VÉRTICES de forma síncrona (processing.run)
          → não aparece a notificação automática do QGIS para os vértices
        - Converte para Python, reprojeta p/ WGS84 e inicia KmlExportWorker
        """
        # Diretório temporário
        self._kml_tmpdir = tempfile.mkdtemp(prefix="kmlconv_")
        faces_path = os.path.join(self._kml_tmpdir, "faces.gpkg")
        verts_path = os.path.join(self._kml_tmpdir, "verts.gpkg")

        def _cleanup():
            if getattr(self, "_kml_tmpdir", None):
                try:
                    shutil.rmtree(self._kml_tmpdir)
                except Exception:
                    pass  # nosec B110
                self._kml_tmpdir = None
            for attr in ("_kml_context", "_kml_feedback", "_task_faces_kml"):
                if hasattr(self, attr):
                    setattr(self, attr, None)

        def _on_error(msg):
            try:
                self.iface.messageBar().popWidget(progressMsgBar)
            except Exception:
                try:
                    progressMsgBar.close()
                except Exception:
                    pass  # nosec B110

            self.mostrar_mensagem(msg, "Erro")
            _cleanup()

        # Parâmetros
        crs_wkt = mesh_layer.crs().toWkt()
        params_faces = {
            'INPUT': mesh_layer, 'DATASET_GROUPS': [], 'DATASET_TIME': {'type': 'static'},
            'CRS_OUTPUT': crs_wkt, 'VECTOR_OPTION': 0, 'OUTPUT': faces_path}
        params_verts = {
            'INPUT': mesh_layer, 'DATASET_GROUPS': [], 'DATASET_TIME': {'type': 'static'},
            'CRS_OUTPUT': crs_wkt, 'VECTOR_OPTION': 1, 'OUTPUT': verts_path}

        # Algoritmo (apenas faces como task)
        reg = QgsApplication.processingRegistry()
        alg_faces = reg.createAlgorithmById("native:exportmeshfaces")
        if not alg_faces:
            _on_error(self.tr("Algoritmo 'native:exportmeshfaces' não encontrado."))
            return

        # Contexto/feedback fortes
        self._kml_context  = QgsProcessingContext()
        self._kml_feedback = QgsProcessingFeedback()

        # Task SOMENTE das FACES (com descrição desejada)
        self._task_faces_kml = QgsProcessingAlgRunnerTask(alg_faces, params_faces, self._kml_context, self._kml_feedback)
        self._task_faces_kml.setDescription(self.tr("Exporta malha de faces"))

        # Callback das faces
        def _on_faces_executed(success, results):
            if not success:
                _on_error(self.tr("Falha ao exportar faces da malha (native:exportmeshfaces)."))
                return

            # Exportar VÉRTICES sincronamente (sem task → sem notificação automática)
            try:
                processing.run(
                    "native:exportmeshvertices",
                    params_verts,
                    context=self._kml_context,
                    feedback=self._kml_feedback)
            except Exception as e:
                _on_error(self.tr("Falha ao exportar vértices da malha (native:exportmeshvertices): {error}").format(error=e))
                return

            # Carregar GPKGs
            faces_vl = QgsVectorLayer(faces_path, "faces_tmp", "ogr")
            verts_vl = QgsVectorLayer(verts_path, "verts_tmp", "ogr")
            if not faces_vl.isValid() or not verts_vl.isValid():
                _on_error(self.tr("Falha ao carregar arquivos temporários (GPKG)."))
                return

            # Converter p/ Python + reprojetar p/ WGS84 + estilo
            try:
                polygons_xy, point_z_values = self._to_python_mesh_data(faces_vl, verts_vl)  # XY + Z por ponto
                polygons_wgs84_3d = self._polygons_to_wgs84_3d(polygons_xy, point_z_values, mesh_layer.crs())  # (lon,lat,z)
                style_payload = self._kml_style_payload(style_options)
            except Exception as e:
                _on_error(self.tr("Falha na preparação para KML: {error}").format(error=e))
                return

            # Barra determinada; worker definirá max/valor
            progressBar.setRange(0, 1)

            # Dispara worker KML (usa polígonos já em (lon,lat,z) e estilo ABGR)
            self._start_export_worker(
                fmt="KML",
                worker_cls=KmlExportWorker,
                polygons=polygons_wgs84_3d,
                point_z_values={},      # não usado pelo KML
                save_path=save_path,
                progressBar=progressBar,
                progressMsgBar=progressMsgBar,
                style=style_payload)

            _cleanup()

        # Conecta e dispara task de FACES
        self._task_faces_kml.executed.connect(_on_faces_executed)
        QgsApplication.taskManager().addTask(self._task_faces_kml)

    def _polygons_to_wgs84_3d(self, polygons_xy, point_z_values, src_crs):
        """
        Converte 'polygons_xy' (ring de (x,y) no CRS de origem) em
        'polygons_wgs84_3d' (ring de (lon,lat,z)), usando Z do dict.
        Mantém anéis na mesma ordem; fecha anel depois no worker.
        """
        crs_dest = QgsCoordinateReferenceSystem(4326)
        xform = QgsCoordinateTransform(src_crs, crs_dest, QgsProject.instance())

        out = []  # List[List[List[Tuple[lon,lat,z]]]]
        for poly in polygons_xy:
            rings3d = []
            for ring in poly:
                ring3d = []
                for (x, y) in ring:
                    p_ll = xform.transform(QgsPointXY(x, y))
                    z = point_z_values.get((round(x,9), round(y,9)), 0.0)
                    ring3d.append((p_ll.x(), p_ll.y(), z))
                rings3d.append(ring3d)
            out.append(rings3d)
        return out

    def _parse_xml_file_seguro(self, caminho_xml):
        if not DEFUSEDXML_OK:
            self.mostrar_mensagem(self.tr("A biblioteca 'defusedxml' não está instalada no Python do QGIS. Instale com: python -m pip install defusedxml"), "Erro", duracao=3)
            return None, None

        try:
            tree = DefusedET.parse(caminho_xml)
            return tree, tree.getroot()
        except (DefusedET.ParseError, DefusedXmlException) as e:
            self.mostrar_mensagem(self.tr("XML/DAE inválido ou inseguro: {error}").format(error=str(e)), "Erro")
            return None, None
        except Exception as e:
            self.mostrar_mensagem(self.tr("Erro ao ler DAE: {error}").format(error=str(e)), "Erro")
            return None, None

    def _kml_style_payload(self, style_options):
        """
        Converte QColor/opacidade em strings KML (ABGR) e demais opções.
        Espera opacidades inteiras 0–255 (como seu diálogo fornece).
        """
        def _abgr(qcolor, opacity255: int):
            # KML espera ABGR em hex: AA,BB,GG,RR
            return f"{opacity255:02x}{qcolor.blue():02x}{qcolor.green():02x}{qcolor.red():02x}"

        line_abgr = _abgr(style_options["line_color"], style_options["line_opacity"])
        poly_abgr  = _abgr(style_options["face_color"], style_options["face_opacity"])
        return {
            "line_color_abgr": line_abgr,
            "line_width": int(style_options["line_width"]),
            "poly_color_abgr": poly_abgr,
            "fill": 1,      # manter como no seu código
            "outline": 1,
            "style_id": "customStyle"}

    def _build_color_map_from_pointz(self, point_z_values: dict) -> dict:
        """
        Gera {z: (r,g,b,a)} a partir dos Zs únicos em point_z_values,
        usando UiManagerM.criar_simbologia_gradiente.
        """
        # Zs únicos e ordenados
        zs = sorted({float(z) for z in point_z_values.values()})
        if not zs:
            return {}
        # criar_simbologia_gradiente espera lista de valores
        cores_dict = self.criar_simbologia_gradiente(zs)  # retorna {valor: [r,g,b,a]}
        # normaliza: chaves float e tuplas RGBA
        color_map = {float(z): tuple(cores_dict.get(z, [1,1,1,1])) for z in zs}
        return color_map

    def _polygons_from_vector_layer(self, faces_layer: QgsVectorLayer):
        """
        Converte uma QgsVectorLayer de polígonos em
        List[List[List[Tuple[x,y]]]] (polígono → anéis → (x,y)).
        """
        polygons = []
        for feat in faces_layer.getFeatures():
            geom = feat.geometry()
            if geom.isMultipart():
                multi = geom.asMultiPolygon()
                for poly in multi:
                    rings = []
                    for ring in poly:
                        rings.append([(p.x(), p.y()) for p in ring])
                    polygons.append(rings)
            else:
                poly = geom.asPolygon()
                rings = []
                for ring in poly:
                    rings.append([(p.x(), p.y()) for p in ring])
                polygons.append(rings)
        return polygons

    def exportar_malha_para_dae(self, layer):
        """
        Exporta a malha para DAE (COLLADA) usando worker em QThread.

        Fluxo sucinto:
        - Valida a camada (bloqueia vetor em edição).
        - Mostra barra “Preparando...” e converte malha → polígonos e pontos Z.
        - Gera estruturas Python e cores via criar_simbologia_gradiente.
        - Executa DaeExportWorker (assíncrono) com barra de progresso.
        - Exibe mensagem de sucesso/erro e retorna o caminho gerado.

        Parâmetros:
        - layer (QgsMeshLayer | QgsVectorLayer): Camada selecionada.

        Retorno:
        - str | None: Caminho do .dae criado ou None em caso de falha.
        """
        try:
            # 1) bloqueio de edição em vetor
            if isinstance(layer, QgsVectorLayer) and layer.isEditable():
                self.mostrar_mensagem(self.tr("A camada '{layer_name}' está no modo de edição. Por favor, salve ou cancele as edições antes de exportar.").format(layer_name=layer.name()), "Erro")
                return None

            # 2) caminho temp
            temp_dir = os.path.join(os.path.expanduser("~"), "Temp")
            os.makedirs(temp_dir, exist_ok=True)
            dae_file_path = os.path.join(temp_dir, layer.name() + ".dae")

            # 3) MOSTRAR barra de “Preparando...” ANTES da conversão pesada
            msg_bar = self.iface.messageBar()
            wait_item = msg_bar.createMessage(self.tr("Aguarde"), self.tr("Preparando malha para exportação..."))
            progress_bar = QProgressBar()
            progress_bar.setRange(0, 0)  # indeterminado
            wait_item.layout().addWidget(progress_bar)
            msg_bar.pushWidget(wait_item, Qgis.MessageLevel.Info)

            try:
                # 4) conversão pesada (síncrona) — aqui era a “travada”
                polygon_layer, point_z_values = self.convert_mesh_to_polygons_and_points(layer)
            finally:
                # remove só este item, sem apagar outras barras em uso
                try:
                    msg_bar.popWidget(wait_item)
                except Exception:
                    # fallback se popWidget não estiver disponível
                    try:
                        self.iface.messageBar().popWidget(wait_item)
                    except Exception:
                        try: wait_item.close()
                        except Exception: pass  # nosec B110

            if not polygon_layer or not point_z_values:
                self.mostrar_mensagem(self.tr("Falha na conversão da malha para polígonos e pontos"), "Erro")
                return None

            # 5) montar estruturas Python e color_map a partir da sua simbologia
            polygons = self._polygons_from_vector_layer(polygon_layer)
            color_map = self._build_color_map_from_pointz(point_z_values)  # usa criar_simbologia_gradiente internamente

            # 6) rodar DaeExportWorker (com color_map) usando QThread + QEventLoop
            thread = QThread(self.iface.mainWindow())
            worker = DaeExportWorker(polygons, point_z_values, dae_file_path, color_map=color_map)
            worker.moveToThread(thread)

            done = {"ok": False, "duration": 0.0, "err": None}
            loop = QEventLoop()

            def _on_finished(path, dur):
                done["ok"] = True
                done["duration"] = dur
                loop.quit()

            def _on_error(msg):
                done["err"] = msg
                loop.quit()

            thread.started.connect(worker.run)
            worker.finished.connect(_on_finished)
            worker.error.connect(_on_error)
            worker.finished.connect(thread.quit)
            worker.finished.connect(worker.deleteLater)
            thread.finished.connect(thread.deleteLater)

            # barra de progresso da escrita (opcional)
            progressBar, progressMsgBar = self.iniciar_progress_bar(0)
            worker.max_value.connect(lambda m: progressBar.setRange(0, max(1, m)))
            worker.progress.connect(progressBar.setValue)

            thread.start()
            loop.exec()  # mantém UI responsiva e espera terminar

            # limpa a barra de progresso da escrita
            try:
                self.iface.messageBar().popWidget(wait_item)
            except Exception:
                try: wait_item.close()
                except Exception: pass  # nosec B110

            if done["err"]:
                self.mostrar_mensagem(self.tr("Erro ao exportar a malha para DAE: {error}").format(error=done["err"]), "Erro")
                return None

            self.mostrar_mensagem(self.tr("Camada exportada para DAE em {duration:.2f} segundos").format(duration=done["duration"]), "Sucesso", caminho_pasta=os.path.dirname(dae_file_path), caminho_arquivo=dae_file_path)
            return dae_file_path

        except QgsProcessingException as pe:
            self.mostrar_mensagem(self.tr("Erro ao exportar a malha para DAE: {error}. Verifique o modo de edição ou as restrições da camada.").format(error=str(pe)), "Erro")
            return None
        except Exception as e:
            self.mostrar_mensagem(self.tr("Erro inesperado: {error}").format(error=str(e)), "Erro")
            return None

    def exportar_malha(self, formato):
        """
        Exporta a camada de malha selecionada para o formato informado.

        Resumo do fluxo:
        - Valida a seleção no QTreeView e o tipo da camada (QgsMeshLayer).
        - Abre o diálogo para escolher o caminho de saída com a extensão do formato.
        - Para formatos suportados (DAE/DXF/OBJ/STL), prepara os dados e inicia a exportação assíncrona
          (conversão via Processing → estruturas Python → gravação em QThread), exibindo barra de progresso.
        - Mostra mensagens de sucesso/erro e fecha o diálogo, quando aplicável.

        Parâmetros:
        - formato (str): "DAE", "DXF", "OBJ" ou "STL".

        Retorno:
        - None (opera por efeitos na UI e criação do arquivo no caminho escolhido).
        """
        start_time = time.time()
        indexes = self.dlg.treeViewListaMalha.selectedIndexes()
        if not indexes:
            self.mostrar_mensagem(self.tr("Nenhuma camada selecionada"), "Erro")
            return

        selected_layer_name = self.treeViewModel.itemFromIndex(indexes[0]).text()
        layers = QgsProject.instance().mapLayersByName(selected_layer_name)
        if not layers:
            self.mostrar_mensagem(self.tr("Camada não encontrada"), "Erro")
            return

        layer = layers[0]
        if not isinstance(layer, QgsMeshLayer):
            self.mostrar_mensagem(self.tr("A camada selecionada não é uma malha"), "Erro")
            return

        if formato == "DAE":
            save_path = self.escolher_local_para_salvar(layer.name() + ".dae", "DAE Files (*.dae)")
            if not save_path:
                return

            # Mensagem inicial
            self.mostrar_mensagem(self.tr("Aguarde, iniciando exportação da camada para DAE"), "Informação", duracao=2)

            # Barra com título correto
            progressBar, progressMsgBar = self.iniciar_progress_bar(0, titulo = self.tr("Exportando malha para DAE"))
            progressBar.setRange(0, 0)  # indeterminado

            self._dae_convert_and_export_with_tasks(layer, save_path, progressBar, progressMsgBar)

        elif formato == "DXF":
            save_path = self.escolher_local_para_salvar(layer.name() + ".dxf", "DXF Files (*.dxf)")
            if not save_path:
                return

            # 1) Mensagem inicial
            self.mostrar_mensagem(self.tr("Aguarde, iniciando exportação da camada para DXF"), "Informação", duracao=2)

            # 2) Barra de progresso com o título correto
            progressBar, progressMsgBar = self.iniciar_progress_bar(0, titulo = self.tr("Exportando malha para DXF"))
            progressBar.setRange(0, 0)  # indeterminado durante a conversão

            # 3) Dispara o pipeline DXF
            self._dxf_convert_and_export_with_tasks(layer, save_path, progressBar, progressMsgBar)

        elif formato == "OBJ":
            save_path = self.escolher_local_para_salvar(layer.name() + ".obj", "OBJ Files (*.obj)")
            if not save_path:
                return

            self.mostrar_mensagem(self.tr("Aguarde, iniciando exportação da camada para OBJ"), "Informação", duracao=2)

            progressBar, progressMsgBar = self.iniciar_progress_bar(0, titulo = self.tr("Exportando malha para OBJ"))
            progressBar.setRange(0, 0)  # indeterminado

            self._obj_convert_and_export_with_tasks(layer, save_path, progressBar, progressMsgBar)

        elif formato == "STL":
            save_path = self.escolher_local_para_salvar(layer.name() + ".stl", "STL Files (*.stl)")
            if not save_path:
                return

            self.mostrar_mensagem(self.tr("Aguarde, iniciando exportação da camada para STL"), "Informação", duracao=2)

            progressBar, progressMsgBar = self.iniciar_progress_bar(0, titulo = self.tr("Exportando malha para STL"))
            progressBar.setRange(0, 0)

            self._stl_convert_and_export_with_tasks(layer, save_path, progressBar, progressMsgBar)

        else:
            super().exportar_malha(formato)

    def _dxf_convert_and_export_with_tasks(self, mesh_layer, save_path, progressBar, progressMsgBar):
        """
        DXF:
        - Cria APENAS a task das FACES (assíncrona)
        - Ao concluir faces, exporta VÉRTICES de forma síncrona (processing.run)
          → não aparece a notificação automática do QGIS para os vértices
        - Converte GPKG → Python e inicia DxfExportWorker
        """
        # 1) Barra indeterminada durante a conversão inicial
        progressBar.setRange(0, 0)

        # 2) Tempdir guardado em self
        self._dxf_tmpdir = tempfile.mkdtemp(prefix="dxfconv_")
        faces_path = os.path.join(self._dxf_tmpdir, "faces.gpkg")
        verts_path = os.path.join(self._dxf_tmpdir, "verts.gpkg")

        def _cleanup():
            if getattr(self, "_dxf_tmpdir", None):
                try:
                    shutil.rmtree(self._dxf_tmpdir)
                except Exception:
                    pass  # nosec B110
                self._dxf_tmpdir = None
            for attr in ("_dxf_context", "_dxf_feedback", "_task_faces_dxf"):
                if hasattr(self, attr):
                    setattr(self, attr, None)

        def _on_error(msg):
            try:
                self.iface.messageBar().popWidget(progressMsgBar)
            except Exception:
                try:
                    progressMsgBar.close()
                except Exception:
                    pass  # nosec B110

            self.mostrar_mensagem(msg, "Erro")
            _cleanup()

        # 3) Parâmetros de exportação
        crs_wkt = mesh_layer.crs().toWkt()
        params_faces = {
            'INPUT': mesh_layer,
            'DATASET_GROUPS': [],
            'DATASET_TIME': {'type': 'static'},
            'CRS_OUTPUT': crs_wkt,
            'VECTOR_OPTION': 0,   # polygons
            'OUTPUT': faces_path}
        params_verts = {
            'INPUT': mesh_layer,
            'DATASET_GROUPS': [],
            'DATASET_TIME': {'type': 'static'},
            'CRS_OUTPUT': crs_wkt,
            'VECTOR_OPTION': 1,   # points
            'OUTPUT': verts_path}

        # 4) Algoritmos
        reg = QgsApplication.processingRegistry()
        alg_faces = reg.createAlgorithmById("native:exportmeshfaces")
        if not alg_faces:
            _on_error(self.tr("Algoritmo 'native:exportmeshfaces' não encontrado."))
            return

        # 5) Contexto/feedback fortes em self
        self._dxf_context  = QgsProcessingContext()
        self._dxf_feedback = QgsProcessingFeedback()

        # 6) Task SOMENTE para FACES
        self._task_faces_dxf = QgsProcessingAlgRunnerTask(alg_faces, params_faces, self._dxf_context, self._dxf_feedback)
        # Define a descrição para controlar o texto da notificação de conclusão
        self._task_faces_dxf.setDescription(self.tr("Exporta malha de faces"))

        # 7) Callback das faces
        def _on_faces_executed(success, results):
            if not success:
                _on_error(self.tr("Falha ao exportar faces da malha (native:exportmeshfaces)."))
                return

            # 7.1) Exporta VÉRTICES sincronamente (sem criar task → sem notificação automática)
            try:
                processing.run(
                    "native:exportmeshvertices",
                    params_verts,
                    context=self._dxf_context,
                    feedback=self._dxf_feedback)
            except Exception as e:
                _on_error(self.tr("Falha ao exportar vértices da malha (native:exportmeshvertices): {error}").format(error=e))
                return

            # 7.2) Carrega GPKGs e converte para dados Python
            faces_vl = QgsVectorLayer(faces_path, "faces_tmp", "ogr")
            verts_vl = QgsVectorLayer(verts_path, "verts_tmp", "ogr")
            if not faces_vl.isValid() or not verts_vl.isValid():
                _on_error(self.tr("Falha ao carregar arquivos temporários gerados (GPKG)."))
                return

            try:
                polygons, point_z_values = self._to_python_mesh_data(faces_vl, verts_vl)
            except Exception as e:
                _on_error(self.tr("Falha ao converter dados para Python: {error}").format(error=e))
                return

            # 7.3) Barra volta para modo determinado; o worker ajustará o máximo real
            progressBar.setRange(0, 1)

            # 7.4) Inicia o worker de DXF
            self._start_export_worker(fmt="DXF", worker_cls=DxfExportWorker, polygons=polygons, point_z_values=point_z_values, save_path=save_path, progressBar=progressBar, progressMsgBar=progressMsgBar)

            # 7.5) Limpeza final
            _cleanup()

        # 8) Conecta e dispara a task de FACES
        self._task_faces_dxf.executed.connect(_on_faces_executed)
        QgsApplication.taskManager().addTask(self._task_faces_dxf)

    def _dae_convert_and_export_with_tasks(self, mesh_layer, save_path, progressBar, progressMsgBar):
        """
        DAE:
        - Cria APENAS a task das FACES (assíncrona, com descrição controlada)
        - Ao concluir faces, exporta VÉRTICES de forma síncrona (processing.run)
          → não aparece a notificação automática do QGIS para os vértices
        - Converte GPKG → Python e inicia DaeExportWorker
        """
        # 1) Barra indeterminada enquanto converte
        progressBar.setRange(0, 0)

        # 2) Tempdir guardado em self (limpar no final)
        self._dae_tmpdir = tempfile.mkdtemp(prefix="daeconv_")
        faces_path = os.path.join(self._dae_tmpdir, "faces.gpkg")
        verts_path = os.path.join(self._dae_tmpdir, "verts.gpkg")

        def _cleanup():
            if getattr(self, "_dae_tmpdir", None):
                try:
                    shutil.rmtree(self._dae_tmpdir)
                except Exception:
                    pass  # nosec B110
                self._dae_tmpdir = None
            for attr in ("_proc_context", "_proc_feedback", "_task_faces"):
                if hasattr(self, attr):
                    setattr(self, attr, None)

        def _on_error(msg):
            try:
                self.iface.messageBar().popWidget(progressMsgBar)
            except Exception:
                try:
                    progressMsgBar.close()
                except Exception:
                    pass  # nosec B110

            self.mostrar_mensagem(msg, "Erro")
            _cleanup()

        # 3) Parâmetros
        crs_wkt = mesh_layer.crs().toWkt()
        params_faces = {
            'INPUT': mesh_layer,
            'DATASET_GROUPS': [],
            'DATASET_TIME': {'type': 'static'},
            'CRS_OUTPUT': crs_wkt,
            'VECTOR_OPTION': 0,   # polygons
            'OUTPUT': faces_path}
        params_verts = {
            'INPUT': mesh_layer,
            'DATASET_GROUPS': [],
            'DATASET_TIME': {'type': 'static'},
            'CRS_OUTPUT': crs_wkt,
            'VECTOR_OPTION': 1,   # points
            'OUTPUT': verts_path}

        # 4) Algoritmo (apenas faces como task)
        reg = QgsApplication.processingRegistry()
        alg_faces = reg.createAlgorithmById("native:exportmeshfaces")
        if not alg_faces:
            _on_error(self.tr("Algoritmo 'native:exportmeshfaces' não encontrado."))
            return

        # 5) Contexto/feedback fortes (lifetime)
        self._proc_context  = QgsProcessingContext()
        self._proc_feedback = QgsProcessingFeedback()

        # 6) Task das FACES (com descrição para controlar a mensagem “Tarefa concluída: ...”)
        self._task_faces = QgsProcessingAlgRunnerTask(alg_faces, params_faces, self._proc_context, self._proc_feedback)
        self._task_faces.setDescription(self.tr("Exporta malha de faces"))

        # 7) Callback das faces
        def _on_faces_executed(success, results):
            if not success:
                _on_error(self.tr("Falha ao exportar faces da malha (native:exportmeshfaces)."))
                return

            # 7.1) Exporta VÉRTICES sincronamente (sem task → sem notificação automática)
            try:
                processing.run(
                    "native:exportmeshvertices",
                    params_verts,
                    context=self._proc_context,
                    feedback=self._proc_feedback)
            except Exception as e:
                _on_error(self.tr("Falha ao exportar vértices da malha (native:exportmeshvertices): {error}").format(error=e))
                return

            # 7.2) Carrega GPKGs e converte para dados Python
            faces_vl = QgsVectorLayer(faces_path, "faces_tmp", "ogr")
            verts_vl = QgsVectorLayer(verts_path, "verts_tmp", "ogr")
            if not faces_vl.isValid() or not verts_vl.isValid():
                _on_error(self.tr("Falha ao carregar arquivos temporários gerados (GPKG)."))
                return

            try:
                polygons, point_z_values = self._to_python_mesh_data(faces_vl, verts_vl)
            except Exception as e:
                _on_error(self.tr("Falha ao converter dados para Python: {error}").format(error=e))
                return

            # 7.3) Barra determinada; o worker definirá o máximo real
            progressBar.setRange(0, 1)

            # 7.4) Dispara o worker DAE
            self._start_export_worker(fmt="DAE", worker_cls=DaeExportWorker, polygons=polygons, point_z_values=point_z_values, save_path=save_path, progressBar=progressBar, progressMsgBar=progressMsgBar)

            # 7.5) Limpeza final
            _cleanup()

        # 8) Conecta e dispara a task de FACES
        self._task_faces.executed.connect(_on_faces_executed)
        QgsApplication.taskManager().addTask(self._task_faces)

    def _obj_convert_and_export_with_tasks(self, mesh_layer, save_path, progressBar, progressMsgBar):
        """
        OBJ:
        - Cria APENAS a task das FACES (assíncrona, com descrição controlada)
        - Ao concluir faces, exporta VÉRTICES de forma síncrona (processing.run)
          → não aparece a notificação automática do QGIS para os vértices
        - Converte GPKG → Python e inicia ObjExportWorker
        """
        # 1) Barra indeterminada no início
        progressBar.setRange(0, 0)

        # 2) Tempdir guardado em self
        self._obj_tmpdir = tempfile.mkdtemp(prefix="objconv_")
        faces_path = os.path.join(self._obj_tmpdir, "faces.gpkg")
        verts_path = os.path.join(self._obj_tmpdir, "verts.gpkg")

        def _cleanup():
            if getattr(self, "_obj_tmpdir", None):
                try:
                    shutil.rmtree(self._obj_tmpdir)
                except Exception:
                    pass  # nosec B110
                self._obj_tmpdir = None
            for attr in ("_obj_context", "_obj_feedback", "_task_faces_obj"):
                if hasattr(self, attr):
                    setattr(self, attr, None)

        def _on_error(msg):
            try:
                self.iface.messageBar().popWidget(progressMsgBar)
            except Exception:
                try:
                    progressMsgBar.close()
                except Exception:
                    pass  # nosec B110

            self.mostrar_mensagem(msg, "Erro")
            _cleanup()

        # 3) Parâmetros de exportação
        crs_wkt = mesh_layer.crs().toWkt()
        params_faces = {
            'INPUT': mesh_layer,
            'DATASET_GROUPS': [],
            'DATASET_TIME': {'type': 'static'},
            'CRS_OUTPUT': crs_wkt,
            'VECTOR_OPTION': 0,   # polygons
            'OUTPUT': faces_path}
        params_verts = {
            'INPUT': mesh_layer,
            'DATASET_GROUPS': [],
            'DATASET_TIME': {'type': 'static'},
            'CRS_OUTPUT': crs_wkt,
            'VECTOR_OPTION': 1,   # points
            'OUTPUT': verts_path}

        # 4) Algoritmo para FACES
        reg = QgsApplication.processingRegistry()
        alg_faces = reg.createAlgorithmById("native:exportmeshfaces")
        if not alg_faces:
            _on_error(self.tr("Algoritmo 'native:exportmeshfaces' não encontrado."))
            return

        # 5) Contexto/feedback fortes
        self._obj_context  = QgsProcessingContext()
        self._obj_feedback = QgsProcessingFeedback()

        # 6) Task SOMENTE das FACES (com descrição desejada)
        self._task_faces_obj = QgsProcessingAlgRunnerTask(alg_faces, params_faces, self._obj_context, self._obj_feedback)
        self._task_faces_obj.setDescription(self.tr("Exporta malha de faces"))

        # 7) Callback das FACES
        def _on_faces_executed(success, results):
            if not success:
                _on_error(self.tr("Falha ao exportar faces da malha (native:exportmeshfaces)."))
                return

            # 7.1) Exportar VÉRTICES sincronamente (sem task → sem notificação automática)
            try:
                processing.run(
                    "native:exportmeshvertices",
                    params_verts,
                    context=self._obj_context,
                    feedback=self._obj_feedback)
            except Exception as e:
                _on_error(self.tr("Falha ao exportar vértices da malha (native:exportmeshvertices): {error}").format(error=e))
                return

            # 7.2) Carrega GPKGs e converte em dados Python
            faces_vl = QgsVectorLayer(faces_path, "faces_tmp", "ogr")
            verts_vl = QgsVectorLayer(verts_path, "verts_tmp", "ogr")
            if not faces_vl.isValid() or not verts_vl.isValid():
                _on_error(self.tr("Falha ao carregar arquivos temporários gerados (GPKG)."))
                return

            try:
                polygons, point_z_values = self._to_python_mesh_data(faces_vl, verts_vl)
            except Exception as e:
                _on_error(self.tr("Falha ao converter dados para Python: {error}").format(error=e))
                return

            # 7.3) Barra determinada; o worker ajustará o máximo real
            progressBar.setRange(0, 1)

            # 7.4) Inicia worker OBJ
            self._start_export_worker(fmt="OBJ", worker_cls=ObjExportWorker, polygons=polygons, point_z_values=point_z_values, save_path=save_path, progressBar=progressBar, progressMsgBar=progressMsgBar)

            # 7.5) Limpeza final
            _cleanup()

        # 8) Conecta e dispara a task de FACES
        self._task_faces_obj.executed.connect(_on_faces_executed)
        QgsApplication.taskManager().addTask(self._task_faces_obj)

    def _stl_convert_and_export_with_tasks(self, mesh_layer, save_path, progressBar, progressMsgBar):
        """
        STL:
        - Cria APENAS a task das FACES (assíncrona, com descrição controlada)
        - Ao concluir faces, exporta VÉRTICES de forma síncrona (processing.run)
          → não aparece a notificação automática do QGIS para os vértices
        - Converte GPKG → Python e inicia StlExportWorker
        """
        # 1) Barra indeterminada
        progressBar.setRange(0, 0)

        # 2) Tempdir guardado em self
        self._stl_tmpdir = tempfile.mkdtemp(prefix="stlconv_")
        faces_path = os.path.join(self._stl_tmpdir, "faces.gpkg")
        verts_path = os.path.join(self._stl_tmpdir, "verts.gpkg")

        def _cleanup():
            if getattr(self, "_stl_tmpdir", None):
                try:
                    shutil.rmtree(self._stl_tmpdir)
                except Exception:
                    pass  # nosec B110
                self._stl_tmpdir = None
            for attr in ("_stl_context", "_stl_feedback", "_task_faces_stl"):
                if hasattr(self, attr):
                    setattr(self, attr, None)

        def _on_error(msg):
            try:
                self.iface.messageBar().popWidget(progressMsgBar)
            except Exception:
                try:
                    progressMsgBar.close()
                except Exception:
                    pass  # nosec B110

            self.mostrar_mensagem(msg, "Erro")
            _cleanup()

        # 3) Parâmetros
        crs_wkt = mesh_layer.crs().toWkt()
        params_faces = {
            'INPUT': mesh_layer,
            'DATASET_GROUPS': [],
            'DATASET_TIME': {'type': 'static'},
            'CRS_OUTPUT': crs_wkt,
            'VECTOR_OPTION': 0,   # polygons
            'OUTPUT': faces_path}
        params_verts = {
            'INPUT': mesh_layer,
            'DATASET_GROUPS': [],
            'DATASET_TIME': {'type': 'static'},
            'CRS_OUTPUT': crs_wkt,
            'VECTOR_OPTION': 1,   # points
            'OUTPUT': verts_path }

        # 4) Algoritmo (apenas faces como task)
        reg = QgsApplication.processingRegistry()
        alg_faces = reg.createAlgorithmById("native:exportmeshfaces")
        if not alg_faces:
            _on_error(self.tr("Algoritmo 'native:exportmeshfaces' não encontrado."))
            return

        # 5) Contexto/feedback fortes
        self._stl_context  = QgsProcessingContext()
        self._stl_feedback = QgsProcessingFeedback()

        # 6) Task SOMENTE das FACES (com descrição desejada)
        self._task_faces_stl = QgsProcessingAlgRunnerTask(alg_faces, params_faces, self._stl_context, self._stl_feedback)
        self._task_faces_stl.setDescription(self.tr("Exporta malha de faces"))

        # 7) Callback das faces
        def _on_faces_executed(success, results):
            if not success:
                _on_error(self.tr("Falha ao exportar faces da malha (native:exportmeshfaces)."))
                return

            # 7.1) Exporta VÉRTICES sincronamente (sem task → sem notificação automática)
            try:
                processing.run(
                    "native:exportmeshvertices",
                    params_verts,
                    context=self._stl_context,
                    feedback=self._stl_feedback)
            except Exception as e:
                _on_error(self.tr("Falha ao exportar vértices da malha (native:exportmeshvertices): {error}").format(error=e))
                return

            # 7.2) Carrega GPKGs e converte para dados Python
            faces_vl = QgsVectorLayer(faces_path, "faces_tmp", "ogr")
            verts_vl = QgsVectorLayer(verts_path, "verts_tmp", "ogr")
            if not faces_vl.isValid() or not verts_vl.isValid():
                _on_error(self.tr("Falha ao carregar arquivos temporários gerados (GPKG)."))
                return

            try:
                polygons, point_z_values = self._to_python_mesh_data(faces_vl, verts_vl)
            except Exception as e:
                _on_error(self.tr("Falha ao converter dados para Python: {error}").format(error=e))
                return

            # 7.3) Barra determinada; o worker ajustará o máximo real
            progressBar.setRange(0, 1)

            # 7.4) Inicia worker STL (mantendo binary=True)
            self._start_export_worker(fmt="STL", worker_cls=StlExportWorker, polygons=polygons, point_z_values=point_z_values, save_path=save_path, progressBar=progressBar, progressMsgBar=progressMsgBar, binary=True)

            # 7.5) Limpeza final
            _cleanup()

        # 8) Conecta e dispara a task de FACES
        self._task_faces_stl.executed.connect(_on_faces_executed)
        QgsApplication.taskManager().addTask(self._task_faces_stl)

class PrepTask(QgsTask):
    """
    Prepara dados para visualização SEM travar a UI:
      - Converte a QgsMeshLayer em (polygons, point_z_values) prontos para triangulação.
    Requisitos:
      - convert_mesh_to_polygons_and_points(layer) NÃO deve mexer em UI.
    """
    finished_ok = pyqtSignal(list, dict)  # polygons, point_z_values
    failed = pyqtSignal(str)

    def __init__(self, ui_manager, layer_id: str):
        super().__init__(ui_manager.tr("Preparando malha para visualização"), QgsTask.Flag.CanCancel)
        self._ui = ui_manager
        self._layer_id = layer_id
        self._err = None
        self._polygons = None
        self._point_z = None

    def run(self):
        try:
            layer = QgsProject.instance().mapLayer(self._layer_id)
            if layer is None or not isinstance(layer, QgsMeshLayer):
                raise RuntimeError(self._ui.tr("Camada inválida durante a preparação."))

            # Passo 1: converter malha (não tocar UI aqui!)
            # Esperado: (QgsVectorLayer de faces, dict {(x,y): z})
            poly_layer, point_z_values = self._ui.convert_mesh_to_polygons_and_points(layer)

            # Passo 2: extrair polígonos (coordenadas) para Python puro
            polygons = self._ui._polygons_from_vector_layer(poly_layer)

            # Resultado para o callback
            self._polygons = polygons
            self._point_z = point_z_values
            return True

        except Exception as e:
            self._err = str(e)
            return False

    def finished(self, result):
        # roda no main thread
        if result and self._err is None:
            try:
                self.finished_ok.emit(self._polygons or [], self._point_z or {})
            except Exception as e:
                self.failed.emit(str(e))
        else:
            self.failed.emit(self._err or self._ui.tr("Falha desconhecida na preparação."))

    def cancel(self):
        super().cancel()

class BuffersWorker(QObject):
    max_value  = pyqtSignal(int)
    progress   = pyqtSignal(int)
    finished   = pyqtSignal(list, list, float)  # positions(float flat list), tri_indices(int flat list), duration
    error      = pyqtSignal(str)

    def __init__(self, polygons, point_z_values, eps: float = 1e-9):
        super().__init__()
        # normaliza chaves para (x,y) com 9 casas p/ consistência com export workers
        self.polygons = polygons
        self.point_z_values = {(round(x,9), round(y,9)): float(z) for (x,y), z in point_z_values.items()}
        self.eps = float(eps)
        self._cancel = False

    def cancel(self):
        self._cancel = True

    @staticmethod
    def _area2(a, b, c):
        return (b[0] - a[0])*(c[1] - a[1]) - (b[1] - a[1])*(c[0] - a[0])

    def run(self):
        try:
            t0 = time.time()
            positions = []  # [x0,y0,z0, x1,y1,z1, ...]
            tri_indices = []  # [i0,i1,i2, i3,i4,i5, ...]
            indices = {}   # (x,y) -> idx
            progress = 0

            # estima máximo de faces (fan por anel)
            total_faces_est = 0
            prepared_polys = []
            for poly in self.polygons:  # poly = [ring0, ring1, ...]
                new_poly = []
                for ring in poly:
                    if not ring:
                        continue
                    # remove último=primeiro, se vier fechado
                    if len(ring) >= 2 and ring[0] == ring[-1]:
                        ring = ring[:-1]
                    new_poly.append(ring)
                    n = len(ring)
                    if n >= 3:
                        total_faces_est += (n - 2)
                prepared_polys.append(new_poly)

            self.max_value.emit(max(1, total_faces_est))

            def ensure_index(xy):
                if xy not in indices:
                    z = self.point_z_values.get((round(xy[0],9), round(xy[1],9)), 0.0)
                    idx = len(positions)//3
                    positions.extend([xy[0], xy[1], z])
                    indices[xy] = idx
                return indices[xy]

            for poly in prepared_polys:
                for ring in poly:
                    n = len(ring)
                    if n < 3:
                        continue
                    p0 = ring[0]
                    for i in range(1, n - 1):
                        if self._cancel:
                            raise RuntimeError(QCoreApplication.translate("BuffersWorker", "Operação cancelada pelo usuário."))
                        p1 = ring[i]
                        p2 = ring[i+1]
                        if abs(self._area2(p0, p1, p2)) < self.eps:
                            continue
                        i0 = ensure_index((round(p0[0],9), round(p0[1],9)))
                        i1 = ensure_index((round(p1[0],9), round(p1[1],9)))
                        i2 = ensure_index((round(p2[0],9), round(p2[1],9)))
                        tri_indices.extend([i0, i1, i2])

                        progress += 1
                        if progress % 100 == 0:
                            self.progress.emit(progress)

            self.max_value.emit(max(1, progress))
            self.progress.emit(progress)
            self.finished.emit(positions, tri_indices, time.time() - t0)

        except Exception as e:
            self.error.emit(str(e))

class DaeExportWorker(QObject):
    max_value  = pyqtSignal(int)
    progress   = pyqtSignal(int)
    finished   = pyqtSignal(str, float)  # path, duration
    error      = pyqtSignal(str)

    def __init__(self, polygons, point_z_values, output_path: str, color_map: dict | None = None):
        super().__init__()
        self.polygons = polygons
        self.point_z_values = {(round(x,9), round(y,9)): z for (x,y), z in point_z_values.items()}
        self.output_path = output_path
        self.color_map = {float(k): tuple(v) for k, v in (color_map or {}).items()}
        self._cancel = False

    def cancel(self):
        self._cancel = True

    @staticmethod
    def _area2(p1, p2, p3):
        return (p2[0]-p1[0])*(p3[1]-p1[1]) - (p3[0]-p1[0])*(p2[1]-p1[1])

    @staticmethod
    def _open_ring(ring):
        """Remove o último ponto se o anel estiver fechado (repete o primeiro)."""
        if not ring:
            return ring
        x0, y0 = ring[0]
        x1, y1 = ring[-1]
        if abs(x0 - x1) < 1e-12 and abs(y0 - y1) < 1e-12:
            return ring[:-1]
        return ring

    def run(self):
        try:
            t0 = time.time()

            positions, colors, indices = [], [], {}
            zs = sorted(set(self.point_z_values.values()))
            z_min, z_max = (zs[0], zs[-1]) if zs else (0.0, 1.0)

            def lerp(a, b, t): return a + (b - a) * t

            def color_for_z(z):
                if self.color_map:
                    # exato ou aproximação pelo Z mais próximo
                    if z in self.color_map:
                        return self.color_map[z]
                    if zs:
                        nearest = min(zs, key=lambda v: abs(v - z))
                        return self.color_map.get(nearest, (1.0, 1.0, 1.0, 1.0))
                    return (1.0, 1.0, 1.0, 1.0)
                # fallback: azul→vermelho
                t = 0.0 if z_max == z_min else (z - z_min)/(z_max - z_min)
                return (lerp(0.0, 1.0, t), 0.0, lerp(1.0, 0.0, t), 1.0)

            def ensure_index(xy):
                if xy not in indices:
                    z = self.point_z_values.get((round(xy[0],9), round(xy[1],9)), 0.0)
                    idx = len(positions)//3
                    positions.extend([xy[0], xy[1], z])
                    colors.extend(color_for_z(z))
                    indices[xy] = idx
                return indices[xy]

            # Preparar anéis abertos e estimar faces
            prepared_polys = []
            total_faces_est = 0
            for poly in self.polygons:
                new_poly = []
                for ring in poly:
                    ring2 = self._open_ring(ring)  # <<< usar método da classe
                    n = len(ring2)
                    if n >= 3:
                        total_faces_est += (n - 2)
                    new_poly.append(ring2)
                prepared_polys.append(new_poly)

            self.max_value.emit(total_faces_est if total_faces_est > 0 else 1)

            # Triangulação tipo "fan" + progresso 100/100
            tri_indices = []
            progress = 0
            eps = 1e-12
            for poly in prepared_polys:
                for ring in poly:
                    n = len(ring)
                    if n < 3:
                        continue
                    p0 = ring[0]
                    for i in range(1, n - 1):
                        if self._cancel:
                            raise RuntimeError(QCoreApplication.translate("DaeExportWorker", "Operação cancelada pelo usuário."))
                        p1 = ring[i]
                        p2 = ring[i+1]
                        if abs(self._area2(p0, p1, p2)) < eps:
                            continue
                        i0 = ensure_index((round(p0[0],9), round(p0[1],9)))
                        i1 = ensure_index((round(p1[0],9), round(p1[1],9)))
                        i2 = ensure_index((round(p2[0],9), round(p2[1],9)))
                        tri_indices.extend([i0, i1, i2])
                        progress += 1
                        if progress % 100 == 0:
                            self.progress.emit(progress)

            self.max_value.emit(max(1, progress))
            self.progress.emit(progress)

            # Escrever COLLADA (igual ao que você já tinha)
            collada = XmlET.Element("COLLADA", xmlns="http://www.collada.org/2005/11/COLLADASchema", version="1.4.1")
            asset = XmlET.SubElement(collada, "asset")
            XmlET.SubElement(asset, "created").text  = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
            XmlET.SubElement(asset, "modified").text = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
            XmlET.SubElement(asset, "unit", name="meter", meter="1")
            XmlET.SubElement(asset, "up_axis").text  = "Z_UP"

            lib_geo  = XmlET.SubElement(collada, "library_geometries")
            geometry = XmlET.SubElement(lib_geo, "geometry", id="mesh", name="mesh")
            mesh     = XmlET.SubElement(geometry, "mesh")

            def _append_source(mesh_elem, name, stride, array):
                src = XmlET.SubElement(mesh_elem, "source", id=f"mesh-{name}")
                fa  = XmlET.SubElement(src, "float_array", id=f"mesh-{name}-array", count=str(len(array)))
                fa.text = " ".join(map(str, array))
                tech = XmlET.SubElement(src, "technique_common")
                acc  = XmlET.SubElement(tech, "accessor", source=f"#mesh-{name}-array",
                                     count=str(len(array)//stride), stride=str(stride))
                if name == "positions":
                    XmlET.SubElement(acc, "param", name="X", type="float")
                    XmlET.SubElement(acc, "param", name="Y", type="float")
                    XmlET.SubElement(acc, "param", name="Z", type="float")
                elif name == "colors":
                    for n in ("R","G","B","A"):
                        XmlET.SubElement(acc, "param", name=n, type="float")
                return src

            _append_source(mesh, "positions", 3, positions)
            _append_source(mesh, "colors",    4, colors)

            verts = XmlET.SubElement(mesh, "vertices", id="mesh-vertices")
            XmlET.SubElement(verts, "input", semantic="POSITION", source="#mesh-positions")
            XmlET.SubElement(verts, "input", semantic="COLOR",    source="#mesh-colors")

            real_count = len(tri_indices) // 3
            tris = XmlET.SubElement(mesh, "triangles", count=str(real_count))
            XmlET.SubElement(tris, "input", semantic="VERTEX", source="#mesh-vertices", offset="0")
            p_elem = XmlET.SubElement(tris, "p")
            p_elem.text = " ".join(map(str, tri_indices))

            lib_scenes = XmlET.SubElement(collada, "library_visual_scenes")
            v_scene = XmlET.SubElement(lib_scenes, "visual_scene", id="Scene", name="Scene")
            node = XmlET.SubElement(v_scene, "node", id="mesh", name="mesh", type="NODE")
            XmlET.SubElement(node, "matrix", sid="transform").text = "1 0 0 0 0 1 0 0 0 0 1 0 0 0 0 1"
            XmlET.SubElement(node, "instance_geometry", url="#mesh")
            scene = XmlET.SubElement(collada, "scene")
            XmlET.SubElement(scene, "instance_visual_scene", url="#Scene")

            XmlET.ElementTree(collada).write(self.output_path, encoding="UTF-8", xml_declaration=True)
            self.finished.emit(self.output_path, time.time() - t0)

        except Exception as e:
            self.error.emit(str(e))

class KmlExportWorker(QObject):
    max_value  = pyqtSignal(int)
    progress   = pyqtSignal(int)
    finished   = pyqtSignal(str, float)  # path, duration
    error      = pyqtSignal(str)

    def __init__(self, polygons, point_z_values_unused, output_path: str, style: dict):
        super().__init__()
        # polygons: List[List[List[Tuple[lon,lat,z]]]]
        self.polygons = polygons
        self.output_path = output_path
        self.style = style
        self._cancel = False

    def cancel(self): self._cancel = True

    @staticmethod
    def _ensure_closed(ring3d):
        if not ring3d: return ring3d
        a = ring3d[0]; b = ring3d[-1]
        if abs(a[0]-b[0])<1e-12 and abs(a[1]-b[1])<1e-12 and abs(a[2]-b[2])<1e-12:
            return ring3d
        return ring3d + [ring3d[0]]

    def run(self):
        try:
            import time
            t0 = time.time()

            total = len(self.polygons)
            self.max_value.emit(total if total>0 else 1)

            kml = XmlET.Element("kml", xmlns="http://www.opengis.net/kml/2.2")
            doc = XmlET.SubElement(kml, "Document")

            # Estilo único
            style = XmlET.SubElement(doc, "Style", id=self.style.get("style_id","customStyle"))
            ls = XmlET.SubElement(style, "LineStyle")
            XmlET.SubElement(ls, "color").text = self.style["line_color_abgr"]
            XmlET.SubElement(ls, "width").text = str(self.style["line_width"])
            ps = XmlET.SubElement(style, "PolyStyle")
            XmlET.SubElement(ps, "color").text = self.style["poly_color_abgr"]
            XmlET.SubElement(ps, "fill").text = "1" if self.style.get("fill",1) else "0"
            XmlET.SubElement(ps, "outline").text = "1" if self.style.get("outline",1) else "0"

            progress = 0

            for poly in self.polygons:
                if self._cancel:
                    raise RuntimeError(QCoreApplication.translate("KmlExportWorker", "Operação cancelada pelo usuário."))

                placemark = XmlET.SubElement(doc, "Placemark")
                XmlET.SubElement(placemark, "styleUrl").text = f"#{self.style.get('style_id','customStyle')}"
                polygon_elem = XmlET.SubElement(placemark, "Polygon")
                XmlET.SubElement(polygon_elem, "altitudeMode").text = "absolute"

                if len(poly) >= 1:
                    # outer
                    outer = XmlET.SubElement(polygon_elem, "outerBoundaryIs")
                    lr = XmlET.SubElement(outer, "LinearRing")
                    ring = self._ensure_closed(poly[0])
                    coords = " ".join([f"{x},{y},{z}" for (x,y,z) in ring])
                    XmlET.SubElement(lr, "coordinates").text = coords

                # holes (inners)
                if len(poly) > 1:
                    for ring3d in poly[1:]:
                        inner = XmlET.SubElement(polygon_elem, "innerBoundaryIs")
                        lr = XmlET.SubElement(inner, "LinearRing")
                        ring = self._ensure_closed(ring3d)
                        coords = " ".join([f"{x},{y},{z}" for (x,y,z) in ring])
                        XmlET.SubElement(lr, "coordinates").text = coords

                progress += 1
                if progress % 100 == 0:
                    self.progress.emit(progress)

            # Finaliza progresso e grava
            self.max_value.emit(max(1, progress))
            self.progress.emit(progress)

            XmlET.ElementTree(kml).write(self.output_path, xml_declaration=True, encoding="utf-8")
            self.finished.emit(self.output_path, time.time() - t0)

        except Exception as e:
            self.error.emit(str(e))

class StlExportWorker(QObject):
    max_value  = pyqtSignal(int)
    progress   = pyqtSignal(int)
    finished   = pyqtSignal(str, float)  # path, duration
    error      = pyqtSignal(str)

    def __init__(self, polygons, point_z_values, output_path: str, binary: bool = True):
        super().__init__()
        # polygons: List[List[List[Tuple[float,float]]]] (polígono→anéis→(x,y))
        self.polygons = polygons
        # normaliza para reduzir problemas de flutuante
        self.point_z_values = {(round(x,9), round(y,9)): z for (x,y), z in point_z_values.items()}
        self.output_path = output_path
        self.binary = binary
        self._cancel = False

    def cancel(self):
        self._cancel = True

    @staticmethod
    def _open_ring(ring):
        if not ring:
            return ring
        x0, y0 = ring[0]
        x1, y1 = ring[-1]
        if abs(x0 - x1) < 1e-12 and abs(y0 - y1) < 1e-12:
            return ring[:-1]
        return ring

    @staticmethod
    def _area2(p1, p2, p3):
        return (p2[0]-p1[0])*(p3[1]-p1[1]) - (p3[0]-p1[0])*(p2[1]-p1[1])

    @staticmethod
    def _normal(a, b, c):
        # normal de (a,b,c) com produto vetorial, normalizada
        ux, uy, uz = b[0]-a[0], b[1]-a[1], b[2]-a[2]
        vx, vy, vz = c[0]-a[0], c[1]-a[1], c[2]-a[2]
        nx = uy*vz - uz*vy
        ny = uz*vx - ux*vz
        nz = ux*vy - uy*vx
        norm = (nx*nx + ny*ny + nz*nz) ** 0.5
        if norm == 0.0:
            return (0.0, 0.0, 0.0)
        return (nx/norm, ny/norm, nz/norm)

    def run(self):
        try:
            import time, struct
            t0 = time.time()

            # 1) Abrir anéis e estimar faces (para setar um "max" inicial)
            prepared_polys = []
            total_faces_est = 0
            for poly in self.polygons:
                new_poly = []
                for ring in poly:
                    ring2 = self._open_ring(ring)
                    n = len(ring2)
                    if n >= 3:
                        total_faces_est += (n - 2)
                    new_poly.append(ring2)
                prepared_polys.append(new_poly)

            self.max_value.emit(total_faces_est if total_faces_est > 0 else 1)

            def z_of(xy):
                return self.point_z_values.get((round(xy[0],9), round(xy[1],9)), 0.0)

            progress = 0
            real_count = 0
            eps = 1e-12

            if self.binary:
                # STL BINÁRIO
                # Formato:
                # 80 bytes header
                # 4 bytes (uint32) count
                # N * (normal[3]*float32 + v1[3] + v2[3] + v3[3] + uint16 attribute)
                with open(self.output_path, "wb") as f:
                    header = b"STL binary generated by plugin".ljust(80, b" ")
                    f.write(header)
                    f.write(struct.pack("<I", 0))  # placeholder para count (corrigiremos após escrever)

                    pack_tri = struct.Struct("<12fH").pack  # normal(3) + 3*vertex(3) + attr(0)
                    for poly in prepared_polys:
                        for ring in poly:
                            n = len(ring)
                            if n < 3:
                                continue
                            p0 = ring[0]
                            for i in range(1, n - 1):
                                if self._cancel:
                                    raise RuntimeError(QCoreApplication.translate("StlExportWorker", "Operação cancelada pelo usuário."))
                                p1 = ring[i]
                                p2 = ring[i+1]
                                if abs(self._area2(p0, p1, p2)) < eps:
                                    continue

                                a = (p0[0], p0[1], z_of(p0))
                                b = (p1[0], p1[1], z_of(p1))
                                c = (p2[0], p2[1], z_of(p2))
                                nx, ny, nz = self._normal(a, b, c)

                                # empacota e escreve triângulo
                                f.write(pack_tri(
                                    float(nx), float(ny), float(nz),
                                    float(a[0]), float(a[1]), float(a[2]),
                                    float(b[0]), float(b[1]), float(b[2]),
                                    float(c[0]), float(c[1]), float(c[2]),
                                    0  # attribute byte count
                                ))

                                real_count += 1
                                progress += 1
                                if progress % 100 == 0:
                                    self.progress.emit(progress)

                    # Corrige a contagem real no cabeçalho
                    f.seek(80)
                    f.write(struct.pack("<I", real_count))

                # Ajuste final da barra
                self.max_value.emit(max(1, progress))
                self.progress.emit(progress)

            else:
                # STL ASCII
                with open(self.output_path, "w", encoding="utf-8") as f:
                    f.write("solid mesh\n")
                    for poly in prepared_polys:
                        for ring in poly:
                            n = len(ring)
                            if n < 3:
                                continue
                            p0 = ring[0]
                            for i in range(1, n - 1):
                                if self._cancel:
                                    raise RuntimeError(QCoreApplication.translate("StlExportWorker", "Operação cancelada pelo usuário."))
                                p1 = ring[i]
                                p2 = ring[i+1]
                                if abs(self._area2(p0, p1, p2)) < eps:
                                    continue

                                a = (p0[0], p0[1], z_of(p0))
                                b = (p1[0], p1[1], z_of(p1))
                                c = (p2[0], p2[1], z_of(p2))
                                nx, ny, nz = self._normal(a, b, c)

                                f.write(f"facet normal {nx} {ny} {nz}\n")
                                f.write("  outer loop\n")
                                f.write(f"    vertex {a[0]} {a[1]} {a[2]}\n")
                                f.write(f"    vertex {b[0]} {b[1]} {b[2]}\n")
                                f.write(f"    vertex {c[0]} {c[1]} {c[2]}\n")
                                f.write("  endloop\n")
                                f.write("endfacet\n")

                                real_count += 1
                                progress += 1
                                if progress % 100 == 0:
                                    self.progress.emit(progress)

                    self.max_value.emit(max(1, progress))
                    self.progress.emit(progress)
                    f.write("endsolid mesh\n")

            self.finished.emit(self.output_path, time.time() - t0)

        except Exception as e:
            self.error.emit(str(e))

class ObjExportWorker(QObject):
    max_value  = pyqtSignal(int)
    progress   = pyqtSignal(int)
    finished   = pyqtSignal(str, float)  # path, duration
    error      = pyqtSignal(str)

    def __init__(self, polygons, point_z_values, output_path: str, dedup_vertices: bool = True):
        super().__init__()
        self.polygons = polygons
        self.point_z_values = {(round(x,9), round(y,9)): z for (x,y), z in point_z_values.items()}
        self.output_path = output_path
        self.dedup_vertices = dedup_vertices
        self._cancel = False

    def cancel(self):
        self._cancel = True

    @staticmethod
    def _area2(p1, p2, p3):
        return (p2[0]-p1[0])*(p3[1]-p1[1]) - (p3[0]-p1[0])*(p2[1]-p1[1])

    @staticmethod
    def _open_ring(ring):
        if not ring:
            return ring
        x0, y0 = ring[0]
        x1, y1 = ring[-1]
        if abs(x0 - x1) < 1e-12 and abs(y0 - y1) < 1e-12:
            return ring[:-1]
        return ring

    def run(self):
        try:
            import time
            t0 = time.time()

            # 1) Preparar anéis abertos e estimar faces
            prepared_polys = []
            total_faces_est = 0
            for poly in self.polygons:
                new_poly = []
                for ring in poly:
                    ring2 = self._open_ring(ring)
                    n = len(ring2)
                    if n >= 3:
                        total_faces_est += (n - 2)
                    new_poly.append(ring2)
                prepared_polys.append(new_poly)

            self.max_value.emit(total_faces_est if total_faces_est > 0 else 1)

            # 2) Tabelas para OBJ (v e f)
            positions = []               # [x0,y0,z0, x1,y1,z1, ...]
            vertex_index = {}            # (x,y,z) -> idx (1-based para OBJ)
            faces_idx = []               # [ (i0,i1,i2), ... ]
            progress = 0
            eps = 1e-12

            def z_of(xy):
                return self.point_z_values.get((round(xy[0],9), round(xy[1],9)), 0.0)

            def ensure_vertex(xy):
                z = z_of(xy)
                key = (round(xy[0],9), round(xy[1],9), z if self.dedup_vertices else time.time())
                idx = vertex_index.get(key)
                if idx is None:
                    idx = len(positions)//3 + 1  # OBJ é 1-based
                    positions.extend([xy[0], xy[1], z])
                    vertex_index[key] = idx
                return idx

            # 3) Triangulação fan (igual aos outros workers)
            for poly in prepared_polys:
                for ring in poly:
                    n = len(ring)
                    if n < 3:
                        continue
                    p0 = ring[0]
                    for i in range(1, n - 1):
                        if self._cancel:
                            raise RuntimeError(QCoreApplication.translate("ObjExportWorker", "Operação cancelada pelo usuário."))
                        p1 = ring[i]
                        p2 = ring[i+1]
                        if abs(self._area2(p0, p1, p2)) < eps:
                            continue

                        i0 = ensure_vertex((p0[0], p0[1]))
                        i1 = ensure_vertex((p1[0], p1[1]))
                        i2 = ensure_vertex((p2[0], p2[1]))
                        faces_idx.append((i0, i1, i2))

                        progress += 1
                        if progress % 100 == 0:
                            self.progress.emit(progress)

            # 4) Ajuste final da barra e gravação do arquivo
            self.max_value.emit(max(1, progress))
            self.progress.emit(progress)

            # Escrever OBJ
            lines = []
            lines.append(QCoreApplication.translate("ObjExportWorker", "# OBJ exportado por plugin (triangulado)"))
            # v x y z
            for i in range(0, len(positions), 3):
                lines.append(f"v {positions[i]} {positions[i+1]} {positions[i+2]}")
            # faces triangulares
            # (sem normais/texcoords; pode-se adicionar 'vn' depois)
            for (a,b,c) in faces_idx:
                lines.append(f"f {a} {b} {c}")

            with open(self.output_path, "w", encoding="utf-8") as f:
                f.write("\n".join(lines) + "\n")

            self.finished.emit(self.output_path, time.time() - t0)

        except Exception as e:
            self.error.emit(str(e))

class DxfExportWorker(QObject):
    max_value  = pyqtSignal(int)
    progress   = pyqtSignal(int)
    finished   = pyqtSignal(str, float)  # path, duration
    error      = pyqtSignal(str)

    def __init__(self, polygons, point_z_values, output_path: str, dedup_faces: bool = True):
        super().__init__()
        # polygons: List[List[List[Tuple[float,float]]]]  (polígonos→anéis→(x,y))
        self.polygons = polygons
        # normaliza as chaves (x,y) para bater com floats
        self.point_z_values = {(round(x,9), round(y,9)): z for (x,y), z in point_z_values.items()}
        self.output_path = output_path
        self.dedup_faces = dedup_faces
        self._cancel = False

    def cancel(self):
        self._cancel = True

    @staticmethod
    def _area2(p1, p2, p3):
        return (p2[0]-p1[0])*(p3[1]-p1[1]) - (p3[0]-p1[0])*(p2[1]-p1[1])

    @staticmethod
    def _open_ring(ring):
        if not ring:
            return ring
        x0, y0 = ring[0]
        x1, y1 = ring[-1]
        if abs(x0 - x1) < 1e-12 and abs(y0 - y1) < 1e-12:
            return ring[:-1]
        return ring

    def run(self):
        try:
            t0 = time.time()

            # 1) Preparar anéis abertos e estimar faces
            prepared_polys = []
            total_faces_est = 0
            for poly in self.polygons:
                new_poly = []
                for ring in poly:
                    ring2 = self._open_ring(ring)
                    n = len(ring2)
                    if n >= 3:
                        total_faces_est += (n - 2)
                    new_poly.append(ring2)
                prepared_polys.append(new_poly)

            self.max_value.emit(total_faces_est if total_faces_est > 0 else 1)

            # 2) Criar DXF
            doc = ezdxf.new(dxfversion='R2013')
            msp = doc.modelspace()

            faces_seen = set() if self.dedup_faces else None

            def z_of(xy):
                return self.point_z_values.get((round(xy[0],9), round(xy[1],9)), 0.0)

            progress = 0
            eps = 1e-12

            # 3) Triangulação fan simples (igual ao DAE atual)
            for poly in prepared_polys:
                for ring in poly:
                    n = len(ring)
                    if n < 3:
                        continue
                    p0 = ring[0]
                    for i in range(1, n - 1):
                        if self._cancel:
                            raise RuntimeError(QCoreApplication.translate("DxfExportWorker", "Operação cancelada pelo usuário."))
                        p1 = ring[i]
                        p2 = ring[i+1]
                        if abs(self._area2(p0, p1, p2)) < eps:
                            continue

                        # Deduplicação opcional (por XY)
                        if faces_seen is not None:
                            key = frozenset([
                                (round(p0[0],9), round(p0[1],9)),
                                (round(p1[0],9), round(p1[1],9)),
                                (round(p2[0],9), round(p2[1],9)),
                            ])
                            if key in faces_seen:
                                continue
                            faces_seen.add(key)

                        v0 = (p0[0], p0[1], z_of(p0))
                        v1 = (p1[0], p1[1], z_of(p1))
                        v2 = (p2[0], p2[1], z_of(p2))
                        msp.add_3dface([v0, v1, v2, v2])  # 3DFACE triangular

                        progress += 1
                        if progress % 100 == 0:
                            self.progress.emit(progress)

            # 4) Ajuste final da barra e salvar
            self.max_value.emit(max(1, progress))
            self.progress.emit(progress)

            doc.saveas(self.output_path)

            self.finished.emit(self.output_path, time.time() - t0)

        except Exception as e:
            self.error.emit(str(e))

class TreeViewEventFilter(QObject):
    """
    Filtro de eventos personalizado para detectar movimentos do mouse sobre itens em um treeView.

    Esta classe herda de QObject e implementa um filtro de eventos que detecta quando o mouse se move
    sobre itens específicos em um treeView. Quando o mouse se move sobre um item, a classe chama um 
    método no UiManagerM para exibir um tooltip com informações sobre o item.

    Parâmetros:
    - ui_manager: Referência à instância do objeto UiManagerM, que gerencia a interface do usuário.
    """

    def __init__(self, ui_manager):
        """
        Inicializa o filtro de eventos com uma referência ao UiManagerM.

        Parâmetros:
        - ui_manager: Instância do UiManager que será usada para acessar e manipular a interface do usuário.
        """
        super().__init__()  # Inicializa a classe base QObject
        self.ui_manager = ui_manager  # Armazena a referência ao UiManagerM para uso posterior

    def eventFilter(self, obj, event):
        """
        Filtra os eventos de movimentação do mouse sobre o treeView e exibe tooltips quando aplicável.

        Esta função intercepta eventos que ocorrem no treeView especificado. Se o evento for de movimento
        do mouse (QEvent.MouseMove) e o mouse estiver sobre um item válido no treeView, a função chama
        o método 'configurar_tooltip' do UiManager para exibir um tooltip com informações sobre o item.

        Parâmetros:
        - obj: O objeto que está sendo monitorado (neste caso, o viewport do treeView).
        - event: O evento que está sendo filtrado (como QEvent.MouseMove).

        Retorno:
        - bool: O resultado da chamada à função 'eventFilter' da classe base, indicando se o evento foi processado.
        """
        # Verifica se o objeto é o viewport do treeView e se o evento é de movimento do mouse
        if obj == self.ui_manager.dlg.treeViewListaMalha.viewport() and event.type() == QEvent.Type.MouseMove:
            # Obtém o índice do item no treeView sob o cursor do mouse
            index = self.ui_manager.dlg.treeViewListaMalha.indexAt(event.position().toPoint())
            if index.isValid():  # Verifica se o índice é válido (se o mouse está sobre um item)
                self.ui_manager.configurar_tooltip(index)  # Chama o método para configurar e exibir o tooltip
        # Retorna o resultado padrão do filtro de eventos
        return super().eventFilter(obj, event)  # Chama a implementação da classe base para continuar o processamento normal

class ExportarMalha2DMTask(QgsTask):
    """
    Gera um arquivo .2dm em segundo plano a partir dos vértices
    reais e das faces editadas mantidas em memória.

    Esta task apenas escreve o arquivo. A criação da QgsMeshLayer
    deve ocorrer na thread principal após o término da tarefa.
    """
    def __init__(self, vertices, faces, caminho_saida, nome_tarefa="Gerando malha 2DM"):
        super().__init__(nome_tarefa, QgsTask.Flag.CanCancel)

        # Cópias independentes. A task não deve depender de arrays
        # que ainda possam ser alterados pelo visualizador.
        self.vertices = np.asarray(vertices, dtype=np.float64).copy()

        self.faces = np.asarray(faces, dtype=np.int64).copy()

        self.caminho_saida = str(caminho_saida)

        self.erro = None
        self.cancelado = False

    def run(self):
        """
        Executado em uma thread de trabalho do gerenciador de tarefas.
        """
        try:
            if self.vertices.ndim != 2:
                raise ValueError("A matriz de vértices não possui duas dimensões.")

            if self.vertices.shape[1] < 3:
                raise ValueError("Os vértices precisam possuir coordenadas X, Y e Z.")

            if self.faces.ndim != 2:
                raise ValueError("A matriz de faces não possui duas dimensões.")

            if self.faces.shape[1] != 3:
                raise ValueError("O formato 2DM desta operação aceita apenas faces triangulares.")

            quantidade_vertices = int(self.vertices.shape[0])

            quantidade_faces = int(self.faces.shape[0])

            if quantidade_vertices == 0:
                raise ValueError("A malha não possui vértices.")

            if quantidade_faces == 0:
                raise ValueError("A malha não possui faces.")

            menor_indice = int(self.faces.min())
            maior_indice = int(self.faces.max())

            if menor_indice < 0:
                raise ValueError("A malha possui índice de vértice negativo.")

            if maior_indice >= quantidade_vertices:
                raise ValueError("Uma ou mais faces fazem referência a vértices inexistentes.")

            pasta_saida = os.path.dirname(self.caminho_saida)

            if pasta_saida:
                os.makedirs(pasta_saida, exist_ok=True)

            caminho_temporario = (self.caminho_saida + ".tmp")

            total_registros = max(1, quantidade_vertices + quantidade_faces)

            registros_processados = 0
            ultimo_progresso = -1

            with open(caminho_temporario, "w", encoding="utf-8",
                newline="\n") as arquivo:

                arquivo.write("MESH2D\n")

                # Nós do arquivo 2DM.
                # Os identificadores começam em 1.
                for indice, vertice in enumerate(self.vertices, start=1):
                    if self.isCanceled():
                        self.cancelado = True
                        return False

                    x = float(vertice[0])
                    y = float(vertice[1])
                    z = float(vertice[2])

                    if not (math.isfinite(x)
                        and math.isfinite(y)
                        and math.isfinite(z)):
                        raise ValueError("A malha contém coordenadas inválidas ou não finitas.")

                    arquivo.write(
                        "ND {id_no} {x:.15g} {y:.15g} {z:.15g}\n".format(
                            id_no=indice,
                            x=x,
                            y=y,
                            z=z))

                    registros_processados += 1

                    progresso = int(registros_processados * 100 / total_registros)

                    if progresso != ultimo_progresso:
                        self.setProgress(progresso)
                        ultimo_progresso = progresso

                # Faces triangulares.
                # O último valor representa o material.
                for indice, face in enumerate(self.faces, start=1):
                    if self.isCanceled():
                        self.cancelado = True
                        return False

                    # Arrays Python usam índices iniciados em zero.
                    # O 2DM usa identificadores iniciados em um.
                    no_1 = int(face[2]) + 1
                    no_2 = int(face[1]) + 1
                    no_3 = int(face[0]) + 1

                    arquivo.write(
                        "E3T {id_face} {no_1} {no_2} {no_3} 1\n".format(
                            id_face=indice,
                            no_1=no_1,
                            no_2=no_2,
                            no_3=no_3))

                    registros_processados += 1

                    progresso = int(registros_processados * 100 / total_registros)

                    if progresso != ultimo_progresso:
                        self.setProgress(progresso)
                        ultimo_progresso = progresso

            if self.isCanceled():
                self.cancelado = True

                try:
                    if os.path.exists(caminho_temporario):
                        os.remove(caminho_temporario)
                except Exception:
                    pass  # nosec B110

                return False

            # Somente apresenta o arquivo final quando a escrita
            # tiver sido concluída integralmente.
            os.replace(caminho_temporario, self.caminho_saida)

            self.setProgress(100)
            return True

        except Exception as e:
            self.erro = str(e)

            try:
                caminho_temporario = (self.caminho_saida + ".tmp")

                if os.path.exists(caminho_temporario):
                    os.remove(caminho_temporario)
            except Exception:
                pass  # nosec B110

            return False

class GLMeshItemComEspessura(gl.GLMeshItem):
    """
    GLMeshItem com controle visual da espessura
    das arestas da malha.
    """
    def __init__(self, *args, edgeWidth=1.0, **kwargs):
        self._edge_width = float(edgeWidth)

        super().__init__(*args, **kwargs)

    def setEdgeWidth(self, width):
        self._edge_width = max(1.0, float(width))
        self.update()

    def edgeWidth(self):
        return self._edge_width

    def paint(self):
        try:
            GL.glLineWidth(self._edge_width)

            super().paint()

        finally:
            # Não deixa a largura afetar outros
            # elementos OpenGL da cena.
            GL.glLineWidth(1.0)

class VisualizadorDAE3D(QDialog):

    def __init__(self, dae_file_path=None, parent=None, ui_manager=None, positions=None, tri_indices=None, camada_origem_id=None):
        """
        Inicializa o visualizador 3D de malhas em formato DAE (COLLADA).

        Esta função configura a janela de visualização 3D, incluindo a interface lateral com
        várias opções de configuração, como inverter o gradiente, salvar a visualização em PNG, e alternar a exibição dos eixos XYZ e das linhas dos vértices.

        Parâmetros:
        - dae_file_path (str): O caminho do arquivo DAE que será visualizado.
        - parent (QWidget): O widget pai da janela de visualização (opcional).
        - ui_manager (UiManagerM): Instância da classe UiManagerM para acessar métodos auxiliares, como salvar arquivos e exibir mensagens.

        Atributos:
        - view (GLViewWidget): O widget principal que renderiza a malha 3D.
        - mesh_data (GLMeshItem): Os dados da malha carregados a partir do arquivo DAE.
        - mesh_item (GLMeshItem): O item da malha renderizada.
        - checkbox_xyz (QCheckBox): Checkbox para exibir ou ocultar os eixos XYZ.
        """
        super().__init__(parent)
        self.ui_manager = ui_manager  # Instância de UiManagerM
        self.setWindowTitle(self.tr("Visualização 3D da Malha"))
        self.dae_file_path = dae_file_path # Caminho do arquivo DAE a ser carregado
        # novos buffers em memória (opcionais)
        self._positions = positions
        self._tri_indices = tri_indices

        # ID da QgsMeshLayer usada para abrir este visualizador.
        # A referência pelo ID evita manter um objeto QGIS dentro de tasks.
        self._camada_origem_id = camada_origem_id

        # Mantém viva a task atual de exportação.
        self._task_exportar_2dm = None

        # Diretório temporário da nova malha.
        # Ele não será apagado enquanto a camada estiver sendo usada.
        self._diretorio_malha_editada = None

        self._export_vertices_raw = None
        self._export_faces_raw = None
        self._vertex_colors = None

        # Estrutura da edição temporária da malha
        # Vértices nas coordenadas originais do arquivo
        self._vertices_reais = None

        # Vértices centralizados usados apenas pelo OpenGL
        self._vertices_visualizacao = None

        # Faces exatamente como foram carregadas e orientadas
        self._faces_originais = None

        # Cópia das faces que poderá ser alterada em memória
        self._faces_editadas = None

        # Histórico das alterações topológicas
        self._pilha_desfazer_arestas = []
        self._pilha_refazer_arestas = []

        # Índice:
        # (vertice_1, vertice_2) -> lista de faces que usam a aresta
        self._indice_arestas = {}

        # Aresta que futuramente estará sob o cursor
        self._aresta_hover = None

        # Item gráfico usado para destacar uma única aresta
        self._item_aresta_hover = None

        # Evita executar picking em frequência excessiva
        self._ultimo_hover_ms = 0.0

        # Distância máxima entre cursor e aresta em pixels
        self._tolerancia_aresta_px = 10.0

        # Escala aplicada ao GLMeshItem
        self._escala_visual_malha = 10.0

        # Controle das alterações temporárias
        self.malha_modificada = False

        # Estado do modo de edição temporária das arestas
        self.modo_edicao_arestas = False

        # Evita aplicar o enquadramento inicial mais de uma vez.
        self._enquadramento_inicial_aplicado = False

        # Definir a geometria da janela (largura=1400, altura=900)
        self.setGeometry(100, 100, 1400, 900)

        # Ativar botões de minimizar e maximizar
        self.setWindowFlags(self.windowFlags() | Qt.WindowType.WindowMinimizeButtonHint | Qt.WindowType.WindowMaximizeButtonHint)

        # Definir a janela como não modal
        self.setWindowModality(Qt.WindowModality.NonModal)

        # Layout principal
        main_layout = QHBoxLayout()
        self.setLayout(main_layout)

        # Visualizador 3D
        self.view = PannableGLViewWidget()

        self.view.falhaOpenGL.connect(self._tratar_falha_opengl)

        # Eventos usados para detectar a aresta sob o cursor
        self.view.mouseMoved3D.connect(self._processar_hover_aresta)
        self.view.mouseLeft3D.connect(self._limpar_hover_aresta)
        self.view.ctrlCliqueEsquerdo3D.connect(self._inverter_aresta_hover)
        self.view.desfazerEdicao3D.connect(self._desfazer_edicao_aresta)
        self.view.refazerEdicao3D.connect(self._refazer_edicao_aresta)

        self.view.opts['antialias'] = True  # Ativar suavização para melhor renderização
        main_layout.addWidget(self.view)  # Adicionar o visualizador 3D ao layout principal

        # Linha usada para destacar a aresta sob o cursor
        self._item_aresta_hover = GLLinePlotItem(
            pos=np.zeros((2, 3), dtype=np.float32),

            # Amarelo quente, mais limpo e menos fluorescente
            color=(1.0, 0.55, 0.05, 1.0),

            # Linhas muito largas podem ficar serrilhadas
            # dependendo do driver OpenGL.
            width=3.0,

            antialias=True, mode="lines")

        # Mantém profundidade e transparência, mas a linha será ligeiramente deslocada da superfície.
        self._item_aresta_hover.setGLOptions("translucent")
        self._item_aresta_hover.setVisible(False)

        self.view.addItem(self._item_aresta_hover)

        # Frame lateral para botões
        frame = QFrame()
        frame.setFrameShape(QFrame.Shape.Box)
        frame.setFrameShadow(QFrame.Shadow.Raised)
        frame.setFixedWidth(200)
        
        # Layout para os widgets dentro do frame
        side_layout = QVBoxLayout()
        frame.setLayout(side_layout)

        # Fixar o texto "Configurações:" no topo
        label = QLabel(self.tr("Configurações:"))
        label.setAlignment(Qt.AlignmentFlag.AlignLeft | Qt.AlignmentFlag.AlignTop)
        side_layout.addWidget(label, alignment=Qt.AlignmentFlag.AlignTop)

        # Adicionar um espaçador vertical para garantir que o texto e o slider fiquem juntos
        vertical_spacer = QSpacerItem(20, 40, QSizePolicy.Policy.Minimum, QSizePolicy.Policy.Expanding)
        side_layout.addItem(vertical_spacer)

        # Grupo: Escala de Cores (acima do "Salvar como PNG")
        color_frame = QFrame()
        color_frame.setFrameShape(QFrame.Shape.Box)
        color_frame.setFrameShadow(QFrame.Shadow.Raised)
        color_frame.setLineWidth(1)

        color_layout = QVBoxLayout(color_frame)
        color_layout.setContentsMargins(8, 8, 8, 8)
        color_layout.setSpacing(6)

        lbl_color = QLabel(self.tr("Escala de Cores:"))
        lbl_color.setAlignment(Qt.AlignmentFlag.AlignLeft | Qt.AlignmentFlag.AlignVCenter)
        # opcional: destaque leve do título
        lbl_color.setStyleSheet("font-weight: 600;")

        self.colorbar = ColorBarWidget()
        self.colorbar.setSizePolicy(QSizePolicy.Policy.Expanding, QSizePolicy.Policy.Preferred)

        color_layout.addWidget(lbl_color)
        color_layout.addWidget(self.colorbar)

        side_layout.addWidget(color_frame)

        # Linha horizontal acima da seleção da rampa
        self.linha_rampa_superior = QFrame()
        self.linha_rampa_superior.setFrameShape(QFrame.Shape.HLine)
        self.linha_rampa_superior.setFrameShadow(QFrame.Shadow.Sunken)
        side_layout.addWidget(self.linha_rampa_superior)

        # Texto da seleção da rampa de cores
        self.labelRampaCores = QLabel(self.tr("Selecione a Rampa de Cores"))
        self.labelRampaCores.setAlignment(Qt.AlignmentFlag.AlignLeft | Qt.AlignmentFlag.AlignVCenter)
        side_layout.addWidget(self.labelRampaCores)

        # ComboBox das rampas de cores
        self.Comboboxrampa = QComboBox()
        self.Comboboxrampa.setObjectName("Comboboxrampa")

        self.Comboboxrampa.setToolTip(self.tr("Selecione a rampa utilizada para colorir a malha de acordo com a elevação."))

        # Preenche o ComboBox com nome e pré-visualização
        # gráfica de cada rampa de cores.
        self._configurar_combobox_rampas()

        # Rampa inicialmente selecionada.
        self.Comboboxrampa.setCurrentText("Classic")

        # Atualiza a malha e a legenda sempre que a rampa mudar.
        self.Comboboxrampa.currentIndexChanged.connect(self._on_rampa_cores_alterada)

        side_layout.addWidget(self.Comboboxrampa)

        # Linha horizontal abaixo da seleção da rampa
        self.linha_rampa_inferior = QFrame()
        self.linha_rampa_inferior.setFrameShape(QFrame.Shape.HLine)
        self.linha_rampa_inferior.setFrameShadow(QFrame.Shadow.Sunken)
        side_layout.addWidget(self.linha_rampa_inferior)

        # Botão para salvar a visualização como PNG
        self.botao_salvar_png = QPushButton(self.tr("Salvar Visualização PNG"))
        self.botao_salvar_png.clicked.connect(self.salvar_visualizacao_como_png)
        side_layout.addWidget(self.botao_salvar_png)

        # Botão para salvar a malha visualizada como DAE
        self.botao_salvar_dae = QPushButton(self.tr("Salvar Arquivo DAE"))
        self.botao_salvar_dae.clicked.connect(self.salvar_visualizacao_como_dae)
        side_layout.addWidget(self.botao_salvar_dae)

        # Área de edição temporária da malha
        # Linha horizontal acima dos controles de edição
        self.linha_edicao_superior = QFrame()
        self.linha_edicao_superior.setFrameShape(QFrame.Shape.HLine)
        self.linha_edicao_superior.setFrameShadow(QFrame.Shadow.Sunken)
        side_layout.addWidget(self.linha_edicao_superior)

        # Checkbox que habilitará o modo de edição das arestas
        self.checkBoxEditarArestas = QCheckBox(self.tr("Editar Arestas (Ctrl + Clique)"))
        self.checkBoxEditarArestas.setChecked(False)
        self.checkBoxEditarArestas.setToolTip(self.tr("Ativa a edição temporária das diagonais da malha. As alterações não modificam a camada original."))
        self.checkBoxEditarArestas.toggled.connect(self._alternar_modo_edicao_arestas)
        side_layout.addWidget(self.checkBoxEditarArestas)

        # Botão para futuramente gerar uma malha 2DM
        # e adicioná-la ao projeto do QGIS
        self.pushButtonAdicionarMapa = QPushButton(self.tr("Adicionar ao Mapa"))
        self.pushButtonAdicionarMapa.setToolTip(self.tr("Cria uma nova malha 2DM com as alterações realizadas e a adiciona ao projeto do QGIS."))

        self.pushButtonAdicionarMapa.clicked.connect(self._adicionar_malha_editada_ao_qgis)

        # Inicialmente desabilitado.
        # Será habilitado quando houver alguma alteração na malha.
        self.pushButtonAdicionarMapa.setEnabled(False)

        # Nesta primeira etapa ainda não conectamos o botão
        # à conversão ou criação do arquivo 2DM.
        side_layout.addWidget(self.pushButtonAdicionarMapa)

        # Linha horizontal abaixo dos controles de edição
        self.linha_edicao_inferior = QFrame()
        self.linha_edicao_inferior.setFrameShape(QFrame.Shape.HLine)
        self.linha_edicao_inferior.setFrameShadow(QFrame.Shadow.Sunken)
        side_layout.addWidget(self.linha_edicao_inferior)

        # Criar o layout em grade (grid layout)
        grid_layout = QGridLayout()

        # Adicionar o texto "Número de faixas de cores" na primeira linha, coluna 0
        label_faixas = QLabel(self.tr("Número de faixas de cores:"))
        grid_layout.addWidget(label_faixas, 0, 0)

         # Adicionar um QSpinBox para selecionar o número de faixas de cores
        self.spinbox_faixas = QSpinBox()
        self.spinbox_faixas.setMinimum(1)
        self.spinbox_faixas.setMaximum(10)
        self.spinbox_faixas.setValue(10)  # Valor padrão
        self.spinbox_faixas.valueChanged.connect(self.atualizar_malha_com_faixas)
        grid_layout.addWidget(self.spinbox_faixas, 1, 0)

        # Crie um novo layout horizontal para os botões e o slider
        h_layout = QHBoxLayout()

        # Botão para diminuir o valor
        self.button_decrease = QPushButton()
        self.button_decrease.setIcon(self.style().standardIcon(QStyle.StandardPixmap.SP_ArrowLeft))
        self.button_decrease.setFixedSize(QSize(20, 20))
        self.button_decrease.clicked.connect(self.decrease_slider_value)
        h_layout.addWidget(self.button_decrease)

        # Adicione o slider ao layout horizontal
        self.slider_faixas = QSlider(Qt.Orientation.Horizontal)
        self.slider_faixas.setMinimum(1)
        self.slider_faixas.setMaximum(10)
        self.slider_faixas.setValue(10)
        self.slider_faixas.setTickPosition(QSlider.TickPosition.TicksAbove)
        self.slider_faixas.setTickInterval(1)
        self.slider_faixas.valueChanged.connect(self.atualizar_malha_com_faixas)
        h_layout.addWidget(self.slider_faixas)

        # Mantém sempre sincronizados
        self.slider_faixas.valueChanged.connect(self.spinbox_faixas.setValue)
        self.spinbox_faixas.valueChanged.connect(self.slider_faixas.setValue)

        # Botão para aumentar o valor
        self.button_increase = QPushButton()
        self.button_increase.setIcon(self.style().standardIcon(QStyle.StandardPixmap.SP_ArrowRight))
        self.button_increase.setFixedSize(QSize(20, 20))
        self.button_increase.clicked.connect(self.increase_slider_value)
        h_layout.addWidget(self.button_increase)

        # Adicione o layout horizontal ao grid_layout
        grid_layout.addLayout(h_layout, 1, 0)

        # Adicionar o layout em grid ao layout principal (side_layout)
        side_layout.addLayout(grid_layout)

        # CheckBox para inverter as cores do gradiente
        self.checkbox_inverter_cores = QCheckBox(self.tr("Inverter Cores do Gradiente"))
        self.checkbox_inverter_cores.setChecked(False)  # Desativado por padrão
        self.checkbox_inverter_cores.stateChanged.connect(self.atualizar_malha_com_faixas)
        side_layout.addWidget(self.checkbox_inverter_cores)

        # Linha Horizontal (abaixo do slider)
        hline_below_slider = QFrame()
        hline_below_slider.setFrameShape(QFrame.Shape.HLine)
        hline_below_slider.setFrameShadow(QFrame.Shadow.Sunken)
        side_layout.addWidget(hline_below_slider)

        # RadioButton para mudar a cor do fundo
        self.radio_white = QRadioButton(self.tr("Fundo Branco"))
        self.radio_black = QRadioButton(self.tr("Fundo Preto"))

        # Definir o fundo branco como padrão
        self.radio_white.setChecked(True)
        self.view.setBackgroundColor('w')

        # Conectar os RadioButtons às funções para alterar a cor do fundo
        self.radio_white.toggled.connect(self.mudar_fundo)
        self.radio_black.toggled.connect(self.mudar_fundo)

        # Adicionar RadioButtons ao layout do frame
        side_layout.addWidget(self.radio_white)
        side_layout.addWidget(self.radio_black)

        # **Adicionar o CheckBox para exibir/ocultar as linhas dos vértices**
        self.checkbox_edges = QCheckBox(self.tr("Exibir Linhas dos Vértices"))
        self.checkbox_edges.setChecked(True)  # Exibir as linhas por padrão
        self.checkbox_edges.stateChanged.connect(self.alternar_linhas_vertices)
        side_layout.addWidget(self.checkbox_edges)

        # Adicionando o checkbox para exibir ou ocultar eixos XYZ
        self.checkbox_xyz = QCheckBox(self.tr("Exibir Eixos XYZ"))
        self.checkbox_xyz.setChecked(True)  # Exibir os eixos por padrão
        self.checkbox_xyz.stateChanged.connect(self.alternar_eixos_xyz)
        side_layout.addWidget(self.checkbox_xyz)

        # Separador abaixo do checkbox XYZ
        hline_after_xyz = QFrame()
        hline_after_xyz.setFrameShape(QFrame.Shape.HLine)
        hline_after_xyz.setFrameShadow(QFrame.Shadow.Sunken)
        side_layout.addWidget(hline_after_xyz)

        # "Ver Tudo: botão" (texto + botão em uma linha)
        ver_tudo_row = QHBoxLayout()
        ver_tudo_label = QLabel(self.tr("Centralizar Malha:"))
        self.btn_ver_tudo = QPushButton(self.tr("Aperte"))
        self.btn_ver_tudo.clicked.connect(self.ver_tudo)  # chama o slot para enquadrar a malha
        ver_tudo_row.addWidget(ver_tudo_label)
        ver_tudo_row.addWidget(self.btn_ver_tudo, 1)
        side_layout.addLayout(ver_tudo_row)

        # Adiciona o frame ao layout principal
        main_layout.addWidget(frame)

        # Variável para armazenar os dados da malha
        self.mesh_data = None  # Inicializa a variável mesh_data como None
        self.mesh_item = None  # Inicializa a variável mesh_item como None

        # Carregar via buffers (se vieram), senão via DAE
        try:
            if self._positions is not None and self._tri_indices is not None:
                verts_np = np.asarray(self._positions, dtype=float).reshape(-1, 3)
                faces_np = np.asarray(self._tri_indices, dtype=int).reshape(-1, 3)
                self.load_and_draw_buffers(verts_np, faces_np)
            else:
                self.load_and_draw_dae()
        except Exception as e:
            if self.ui_manager:
                self.ui_manager.mostrar_mensagem(self.ui_manager.tr("Erro ao carregar malha no visualizador: {error}").format(error=e), "Erro")

        self.eixos_xyz = None  # evita AttributeError e facilita checagens

        self.alternar_eixos_xyz(self.checkbox_xyz.checkState())

    def _tratar_falha_opengl(self, diagnostico):
        """
        Informa ao usuário que o visualizador 3D não pôde
        iniciar e apresenta informações da GPU/OpenGL.
        """
        if getattr(self, "_aviso_opengl_exibido", False):

            return

        self._aviso_opengl_exibido = True

        mensagem = QMessageBox(self)
        mensagem.setIcon(QMessageBox.Icon.Critical)
        mensagem.setWindowTitle(self.tr("Falha na Visualização 3D"))
        mensagem.setText(self.tr("Não foi possível iniciar a visualização 3D neste computador."))

        mensagem.setInformativeText(self.tr(
                "Foi detectado um problema no contexto "
                "OpenGL utilizado pela placa de vídeo.\n\n"
                "Isso pode estar relacionado ao driver "
                "gráfico ou à compatibilidade da GPU.\n\n"
                "A camada de malha não foi alterada."))

        mensagem.setDetailedText(diagnostico)
        mensagem.setStandardButtons(QMessageBox.StandardButton.Ok)
        mensagem.exec()

        # Fecha somente o visualizador 3D.
        self.close()

    def showEvent(self, event):
        """
        Quando a janela estiver realmente visível, aplica o mesmo
        enquadramento usado pelo botão 'Aperte'.

        O pequeno atraso permite que:
        - o OpenGL termine de criar o viewport;
        - a malha seja adicionada à cena;
        - a largura e a altura da view estejam corretas.
        """
        super().showEvent(event)

        if self._enquadramento_inicial_aplicado:
            return

        self._enquadramento_inicial_aplicado = True

        QTimer.singleShot(100, self._aplicar_enquadramento_inicial)

    def _definicoes_rampas_cores(self):
        """
        Retorna as rampas disponíveis no visualizador.

        As cores muito escuras foram suavizadas para melhorar
        a visualização da malha sobre fundos preto e branco.
        """
        return {
            # Paleta original do visualizador.
            "Classic": (
                "#ff0000",  # Vermelho
                "#ff4d00",  # Vermelho-laranja
                "#ff8000",  # Laranja
                "#ffbf00",  # Amarelo-alaranjado
                "#ffff00",  # Amarelo
                "#80ff00",  # Verde-amarelado
                "#00ff00",  # Verde
                "#00ff80",  # Verde-ciano
                "#0080ff",  # Azul-claro
                "#0000cc"),   # Azul
            "Blues": (
                "#f7fbff",
                "#deebf7",
                "#9ecae1",
                "#4292c6",
                "#2f6f9f"),
            "Cividis": (
                "#25476f",
                "#455d78",
                "#666970",
                "#948e77",
                "#c8b866",
                "#fee838"),
            "Greens": (
                "#f7fcf5",
                "#c7e9c0",
                "#74c476",
                "#31a354",
                "#2c8c4a"),
            "Greys": (
                "#ffffff",
                "#d9d9d9",
                "#969696",
                "#696969",
                "#4a4a4a"),
            "Magma": (
                "#2a0f3f",
                "#4c1d69",
                "#721f81",
                "#b73779",
                "#f1605d",
                "#feb078",
                "#fcfdbf"),
            "Mako": (
                "#24343f",
                "#334a5b",
                "#3d616f",
                "#357386",
                "#38a1a6",
                "#92d7c4",
                "#def5e5"),
            "RdGy": (
                "#8f2745",
                "#b83a42",
                "#ef8a62",
                "#fddbc7",
                "#ffffff",
                "#e0e0e0",
                "#aaaaaa",
                "#737373",
                "#4a4a4a"),
            "Reds": (
                "#fff5f0",
                "#fcbba1",
                "#fb6a4a",
                "#de2d26",
                "#b52a2f"),
            "Rocket": (
                "#291c3b",
                "#47284f",
                "#682f5d",
                "#8e2d5f",
                "#bd4e63",
                "#df7f65",
                "#f6b48f",
                "#faebdd"),
            "Spectral": (
                "#b11a52",
                "#d53e4f",
                "#f46d43",
                "#fdae61",
                "#fee08b",
                "#ffffbf",
                "#e6f598",
                "#abdda4",
                "#66c2a5",
                "#3288bd",
                "#6875b8"),
            "Turbo": (
                "#53346d",
                "#4145ab",
                "#4675ed",
                "#39a2fc",
                "#1bcfd4",
                "#24eca6",
                "#61fc6c",
                "#a4fc3b",
                "#d6e935",
                "#f9ba38",
                "#f67a24",
                "#e23b1c",
                "#b83a1c"),
            "Viridis": (
                "#5b3478",
                "#5c4a82",
                "#48608c",
                "#31688e",
                "#26828e",
                "#1f9e89",
                "#35b779",
                "#6ece58",
                "#b5de2b",
                "#fde725")}

    def _criar_icone_rampa(self, cores, largura=88, altura=16):
        """
        Cria um ícone horizontal contendo o gradiente da rampa.
        """
        pixmap = QPixmap(largura, altura)
        pixmap.fill(Qt.GlobalColor.transparent)

        painter = QPainter(pixmap)

        try:
            painter.setRenderHint(QPainter.RenderHint.Antialiasing, True)

            margem = 1

            retangulo = QRectF(margem, margem, largura - (2 * margem), altura - (2 * margem))

            gradiente = QLinearGradient(retangulo.left(), 0.0, retangulo.right(), 0.0)

            total_cores = len(cores)

            if total_cores == 1:
                cor = QColor(cores[0])

                gradiente.setColorAt(0.0, cor)
                gradiente.setColorAt(1.0, cor)

            else:
                for indice, codigo_cor in enumerate(cores):
                    posicao = indice / (total_cores - 1)

                    gradiente.setColorAt(posicao, QColor(codigo_cor))

            painter.setPen(QPen(QColor(90, 90, 90, 180), 1.0))

            painter.setBrush(gradiente)

            painter.drawRoundedRect(retangulo, 2.0, 2.0)

        finally:
            painter.end()

        return QIcon(pixmap)

    def _configurar_combobox_rampas(self):
        """
        Preenche o ComboBox com o nome e a pré-visualização
        gráfica de cada rampa de cores.
        """
        self.Comboboxrampa.clear()

        # Tamanho da faixa exibida ao lado do nome.
        self.Comboboxrampa.setIconSize(QSize(88, 16))

        # Evita que o ComboBox fique muito baixo.
        self.Comboboxrampa.setMinimumHeight(26)

        # Mantém as rampas disponíveis na instância do diálogo.
        self._rampas_cores = self._definicoes_rampas_cores()

        for nome_rampa, cores in self._rampas_cores.items():
            icone = self._criar_icone_rampa(cores)

            # O terceiro argumento guarda as cores no Qt.UserRole
            # do item, permitindo reutilizá-las posteriormente.
            self.Comboboxrampa.addItem(icone, nome_rampa, tuple(cores))

        # Dá espaço suficiente para o gradiente e o nome.
        self.Comboboxrampa.view().setMinimumWidth(176)

    def _area_orientada_xy(self, p1, p2, p3):
        """
        Retorna o dobro da área orientada do triângulo em XY.

        Positivo:
            orientação anti-horária.

        Negativo:
            orientação horária.

        Próximo de zero:
            triângulo degenerado.
        """
        return float(
            (p2[0] - p1[0]) * (p3[1] - p1[1])
            - (p2[1] - p1[1]) * (p3[0] - p1[0]))

    def _validar_inversao_aresta(self, aresta, vertice_oposto_1, vertice_oposto_2):
        """
        Verifica se a nova diagonal produz dois triângulos válidos.

        A validação principal é feita no plano XY, pois a malha
        representa uma superfície de terreno.
        """
        if self._vertices_reais is None:
            return False, self.tr("Os vértices da malha não estão disponíveis.")

        a, b = map(int, aresta)
        c = int(vertice_oposto_1)
        d = int(vertice_oposto_2)

        if len({a, b, c, d}) != 4:
            return False, self.tr("As faces não formam um quadrilátero com quatro vértices distintos.")

        vertices = np.asarray(self._vertices_reais, dtype=float)

        pa = vertices[a]
        pb = vertices[b]
        pc = vertices[c]
        pd = vertices[d]

        # Tolerância adaptada às dimensões do quadrilátero.
        pontos_xy = np.array(
            [pa[:2],
                pb[:2],
                pc[:2],
                pd[:2]],
            dtype=float)

        dimensoes = np.ptp(pontos_xy, axis=0)

        escala_xy = max(float(np.linalg.norm(dimensoes)), 1.0)

        tolerancia_area = max(escala_xy * escala_xy * 1e-12, 1e-12)

        # C e D precisam estar em lados opostos da aresta AB.
        lado_c_ab = self._area_orientada_xy(pa, pb, pc)

        lado_d_ab = self._area_orientada_xy(pa, pb, pd)

        if (abs(lado_c_ab) <= tolerancia_area
            or abs(lado_d_ab) <= tolerancia_area
            or lado_c_ab * lado_d_ab >= 0.0):
            return False, self.tr("As faces não formam um quadrilátero convexo.")

        # A e B também precisam ficar em lados opostos da nova diagonal CD.
        lado_a_cd = self._area_orientada_xy(pc, pd, pa)

        lado_b_cd = self._area_orientada_xy(pc, pd, pb)

        if (abs(lado_a_cd) <= tolerancia_area
            or abs(lado_b_cd) <= tolerancia_area
            or lado_a_cd * lado_b_cd >= 0.0):
            return False, self.tr("A nova diagonal ficaria fora do quadrilátero.")

        nova_aresta = tuple(sorted((c, d)))

        faces_nova_aresta = self._indice_arestas.get(nova_aresta, [])

        if faces_nova_aresta:
            return False, self.tr("A nova diagonal já existe na malha.")

        return True, ""

    def _orientar_face_com_normal(self, face, normal_referencia):
        """
        Ajusta a ordem dos vértices para que a nova face
        mantenha uma normal compatível com as faces anteriores.
        """
        face = np.asarray(face, dtype=np.int32).copy()

        vertices = np.asarray(
            self._vertices_visualizacao,
            dtype=float)

        p0 = vertices[int(face[0])]
        p1 = vertices[int(face[1])]
        p2 = vertices[int(face[2])]

        normal = np.cross(p1 - p0, p2 - p0)

        comprimento = float(np.linalg.norm(normal))

        if comprimento <= 1e-12:
            return None

        if (normal_referencia is not None
            and np.dot(normal, normal_referencia) < 0.0):
            face[1], face[2] = (face[2], face[1])

        return face

    def _atualizar_mesh_apos_edicao(self):
        """
        Recria somente o objeto visual da malha após uma edição.

        A posição da câmera não é alterada.
        """
        if (self._vertices_visualizacao is None
            or self._faces_editadas is None):
            return False

        try:
            cores = self._vertex_colors

            if cores is None:
                num_vertices = len(self._vertices_visualizacao)

                cores = np.ones((num_vertices, 4), dtype=float)

            self.mesh_data = gl.MeshData(
                vertexes=np.asarray(
                    self._vertices_visualizacao,
                    dtype=float),
                faces=np.asarray(
                    self._faces_editadas,
                    dtype=np.int32),
                vertexColors=np.asarray(
                    cores,
                    dtype=float))

            try:
                _ = self.mesh_data.vertexNormals()
            except Exception:
                pass  # nosec B110

            if self.mesh_item is not None:
                try:
                    self.view.removeItem(self.mesh_item)
                except Exception:
                    pass  # nosec B110

            edge_color = (
                (0.12, 0.12, 0.12, 1.0)
                if self.radio_white.isChecked()
                else (0.9, 0.9, 0.9, 1.0))

            self.mesh_item = GLMeshItemComEspessura(
                meshdata=self.mesh_data,
                smooth=False,
                drawEdges=self.checkbox_edges.isChecked(),
                edgeColor=edge_color,
                edgeWidth=self._espessura_arestas(),
                shader=self._get_phong_rim_shader(),
                glOptions="opaque")

            self.mesh_item.scale(
                self._escala_visual_malha,
                self._escala_visual_malha,
                self._escala_visual_malha)

            self.view.addItem(self.mesh_item)

            # Mantém as estruturas antigas de exportação sincronizadas.
            self._export_vertices_raw = (
                self._vertices_visualizacao.copy())

            self._export_faces_raw = (self._faces_editadas.copy())

            self.view.update()

            return True

        except Exception as e:
            self.ui_manager.mostrar_mensagem(
                self.tr( "Erro ao atualizar a malha editada: {error}").format(error=e), "Erro")

            return False

    def _desfazer_edicao_aresta(self):
        """
        Desfaz a última inversão de aresta realizada na malha.
        """
        if not self._pilha_desfazer_arestas:
            self.ui_manager.mostrar_mensagem(self.tr("Não há alterações de arestas para desfazer."), "Info", duracao=2)
            return

        # Guarda o estado atual para permitir refazer.
        self._pilha_refazer_arestas.append(np.array(self._faces_editadas, copy=True))

        # Recupera o estado anterior.
        estado_anterior = (self._pilha_desfazer_arestas.pop())

        # Guarda o estado atual para rollback, caso a
        # atualização visual falhe.
        estado_atual = np.array(self._faces_editadas, copy=True)

        self._faces_editadas = np.array(estado_anterior, copy=True)

        # Reconstrói a topologia.
        self._construir_indice_arestas()

        # Atualiza a malha exibida.
        if not self._atualizar_mesh_apos_edicao():
            # Rollback caso a atualização falhe.
            self._faces_editadas = estado_atual

            self._construir_indice_arestas()
            self._atualizar_mesh_apos_edicao()

            # Remove o estado que acabamos de colocar
            # indevidamente na pilha de refazer.
            if self._pilha_refazer_arestas:
                self._pilha_refazer_arestas.pop()

            # Devolve o estado anterior para a pilha.
            self._pilha_desfazer_arestas.append(estado_anterior )

            self.ui_manager.mostrar_mensagem(self.tr("Não foi possível desfazer a alteração da aresta."), "Erro", duracao=2)
            return

        self.malha_modificada = True

        if hasattr(self, "pushButtonAdicionarMapa"):
            self.pushButtonAdicionarMapa.setEnabled(True)

        # O hover antigo pode apontar para uma aresta
        # que não existe mais no estado restaurado.
        self._limpar_hover_aresta()

        self.ui_manager.mostrar_mensagem(self.tr("Última alteração de aresta desfeita."), "Info", duracao=2)

    def _refazer_edicao_aresta(self):
        """
        Refaz a última inversão de aresta desfeita.
        """
        if not self._pilha_refazer_arestas:
            self.ui_manager.mostrar_mensagem(self.tr("Não há alterações de arestas para refazer."), "Info", duracao=2)
            return

        # Guarda o estado atual para permitir desfazer novamente.
        estado_atual = np.array(self._faces_editadas, copy=True)

        # Recupera o próximo estado da pilha de refazer.
        estado_refeito = (self._pilha_refazer_arestas.pop())

        self._faces_editadas = np.array(estado_refeito, copy=True)

        # Reconstrói a topologia.
        self._construir_indice_arestas()

        # Atualiza a malha exibida.
        if not self._atualizar_mesh_apos_edicao():
            # Rollback caso a atualização visual falhe.
            self._faces_editadas = estado_atual

            self._construir_indice_arestas()
            self._atualizar_mesh_apos_edicao()

            # Devolve o estado à pilha de refazer.
            self._pilha_refazer_arestas.append(estado_refeito)

            self.ui_manager.mostrar_mensagem(self.tr("Não foi possível refazer a alteração da aresta."), "Erro", duracao=2)
            return

        # A operação refeita pode ser desfeita novamente.
        self._pilha_desfazer_arestas.append(estado_atual)

        if len(self._pilha_desfazer_arestas) > 50:
            self._pilha_desfazer_arestas.pop(0)

        self.malha_modificada = True

        if hasattr(self, "pushButtonAdicionarMapa"):
            self.pushButtonAdicionarMapa.setEnabled(True)

        # Evita manter uma aresta destacada de uma topologia anterior.
        self._limpar_hover_aresta()

        self.ui_manager.mostrar_mensagem(self.tr("Última alteração de aresta refeita."), "Info", duracao=2)

    def _inverter_aresta_hover(self):
        """
        Inverte a diagonal atualmente destacada.

        A alteração ocorre somente em memória.
        """
        if not self.modo_edicao_arestas:
            return

        if self._aresta_hover is None:
            return

        aresta_antiga = tuple(sorted(map(int, self._aresta_hover)))

        faces_vizinhas = list(self._indice_arestas.get( aresta_antiga, []))

        if len(faces_vizinhas) != 2:
            self.ui_manager.mostrar_mensagem(self.tr("Esta aresta não pode ser invertida porque não pertence a duas faces."), "Aviso", duracao=2)
            return

        face_id_1, face_id_2 = map(int, faces_vizinhas)

        face_1 = np.asarray(
            self._faces_editadas[face_id_1],
            dtype=np.int32).copy()

        face_2 = np.asarray(
            self._faces_editadas[face_id_2],
            dtype=np.int32).copy()

        a, b = aresta_antiga

        opostos_1 = [int(v)
            for v in face_1
            if int(v) not in aresta_antiga]

        opostos_2 = [int(v)
            for v in face_2
            if int(v) not in aresta_antiga]

        if (len(opostos_1) != 1
            or len(opostos_2) != 1):
            self.ui_manager.mostrar_mensagem(
                self.tr("Não foi possível identificar os vértices "
                    "opostos da aresta."), "Erro")
            return

        c = opostos_1[0]
        d = opostos_2[0]

        valido, motivo = self._validar_inversao_aresta(aresta_antiga, c, d)

        if not valido:
            self.ui_manager.mostrar_mensagem(motivo, "Aviso", duracao=2)
            return

        vertices = np.asarray(self._vertices_visualizacao, dtype=float)

        def normal_face(face):
            """
            Calcula a normal de uma face triangular.
            """
            p0 = vertices[int(face[0])]
            p1 = vertices[int(face[1])]
            p2 = vertices[int(face[2])]

            return np.cross(p1 - p0, p2 - p0)

        normal_referencia = (normal_face(face_1) + normal_face(face_2))

        if np.linalg.norm(normal_referencia) <= 1e-12:
            normal_referencia = normal_face(face_1)

        # Nova diagonal C-D.
        nova_face_1 = self._orientar_face_com_normal([c, d, a], normal_referencia)

        nova_face_2 = self._orientar_face_com_normal([d, c, b], normal_referencia)

        if (nova_face_1 is None
            or nova_face_2 is None):
            self.ui_manager.mostrar_mensagem(
                self.tr("A inversão produziria um triângulo "
                    "com área nula."), "Aviso", duracao=2)
            return

        # Guarda todo o estado anterior, mas ainda não o
        # adiciona ao histórico.
        estado_anterior = np.array(self._faces_editadas, copy=True )

        self._faces_editadas[face_id_1] = (nova_face_1)

        self._faces_editadas[face_id_2] = (nova_face_2)

        # Reconstrói o índice com a nova topologia.
        self._construir_indice_arestas()

        if not self._atualizar_mesh_apos_edicao():
            # Restaura toda a topologia anterior caso a
            # atualização visual falhe.
            self._faces_editadas = estado_anterior

            self._construir_indice_arestas()

            # Tenta restaurar também a exibição.
            self._atualizar_mesh_apos_edicao()
            return

        # A alteração foi concluída com sucesso.
        # Agora registra o estado anterior no histórico.
        self._pilha_desfazer_arestas.append(estado_anterior)

        # Limita o histórico às últimas 50 operações.
        if len(self._pilha_desfazer_arestas) > 50:
            self._pilha_desfazer_arestas.pop(0)

        # Uma nova edição invalida o histórico de refazer.
        self._pilha_refazer_arestas.clear()

        self.malha_modificada = True

        if hasattr(self, "pushButtonAdicionarMapa"):
            self.pushButtonAdicionarMapa.setEnabled(True)

        # A nova diagonal passa a ser a aresta destacada.
        nova_aresta = tuple(sorted((c, d)))
        self._aresta_hover = nova_aresta
        self._mostrar_aresta_hover(nova_aresta)

    def _espessura_arestas(self):
        """
        Retorna a espessura visual das arestas.

        Normal:
            1.0

        Modo Editar Arestas:
            1.8
        """
        return (3.0
            if self.modo_edicao_arestas
            else 1.0)

    def _alternar_modo_edicao_arestas(self, habilitado):
        """
        Ativa ou desativa o modo temporário de edição de arestas.
        """
        self.modo_edicao_arestas = bool(habilitado)

        # Altera imediatamente a espessura
        if isinstance(self.mesh_item, GLMeshItemComEspessura):
            self.mesh_item.setEdgeWidth(self._espessura_arestas())

        self.view.definir_modo_edicao_arestas(self.modo_edicao_arestas)

        if self.modo_edicao_arestas:
            self.checkBoxEditarArestas.setToolTip(self.tr("Modo de edição ativo. Passe o mouse sobre uma aresta para destacá-la."))

            self.view.definir_cursor_reposo(Qt.CursorShape.CrossCursor)

        else:
            self._limpar_hover_aresta()

            self.checkBoxEditarArestas.setToolTip(self.tr("Ativa a edição temporária das diagonais da malha. As alterações não modificam a camada original."))

            self.view.definir_cursor_reposo(Qt.CursorShape.OpenHandCursor)

    def _criar_raio_mouse(self, pos_mouse):
        """
        Converte uma posição 2D do mouse em um raio no espaço 3D.

        Retorna:
            origem: ndarray shape (3,)
            direcao: ndarray shape (3,)
        """
        largura = max(1, self.view.width())
        altura = max(1, self.view.height())

        x_ndc = (2.0 * float(pos_mouse.x()) / largura) - 1.0
        y_ndc = 1.0 - (2.0 * float(pos_mouse.y()) / altura)

        try:
            matriz_projecao = self.view.projectionMatrix()

        except TypeError:
            viewport = self.view.getViewport()
            matriz_projecao = self.view.projectionMatrix(viewport, viewport)

        matriz_visao = self.view.viewMatrix()

        matriz_completa = (matriz_projecao * matriz_visao)
        matriz_inversa, sucesso = (matriz_completa.inverted())

        if not sucesso:
            return None, None

        ponto_perto = matriz_inversa.map(QVector4D(x_ndc, y_ndc, -1.0, 1.0))
        ponto_longe = matriz_inversa.map(QVector4D(x_ndc, y_ndc, 1.0, 1.0))

        if (abs(ponto_perto.w()) < 1e-12
            or abs(ponto_longe.w()) < 1e-12):
            return None, None

        origem = np.array(
            [ponto_perto.x() / ponto_perto.w(),
                ponto_perto.y() / ponto_perto.w(),
                ponto_perto.z() / ponto_perto.w()],
            dtype=float)

        destino = np.array(
            [ponto_longe.x() / ponto_longe.w(),
                ponto_longe.y() / ponto_longe.w(),
                ponto_longe.z() / ponto_longe.w()],
            dtype=float)

        direcao = destino - origem
        comprimento = np.linalg.norm(direcao)

        if comprimento <= 1e-12:
            return None, None

        direcao /= comprimento

        return origem, direcao

    def _encontrar_face_sob_raio(self, origem, direcao):
        """
        Encontra a face visível mais próxima atingida pelo raio.

        Usa uma versão vetorizada do algoritmo
        Möller-Trumbore.
        """
        if (self._vertices_visualizacao is None
            or self._faces_editadas is None):
            return None

        if len(self._faces_editadas) == 0:
            return None

        escala = float(self._escala_visual_malha)

        vertices = (np.asarray(self._vertices_visualizacao, dtype=float) * escala)

        faces = np.asarray(self._faces_editadas, dtype=np.int32)

        v0 = vertices[faces[:, 0]]
        v1 = vertices[faces[:, 1]]
        v2 = vertices[faces[:, 2]]

        aresta_1 = v1 - v0
        aresta_2 = v2 - v0

        direcoes = np.broadcast_to(direcao, aresta_2.shape)

        h = np.cross(direcoes, aresta_2)

        determinante = np.einsum("ij,ij->i", aresta_1, h)

        tolerancia = 1e-10

        mascara = (np.abs(determinante) > tolerancia)

        if not np.any(mascara):
            return None

        inverso_det = np.zeros_like(determinante, dtype=float)

        inverso_det[mascara] = (1.0 / determinante[mascara])

        s = origem - v0

        u = (np.einsum("ij,ij->i", s, h) * inverso_det)

        mascara &= ((u >= 0.0) & (u <= 1.0))

        q = np.cross(s, aresta_1)

        v = (np.einsum("ij,ij->i", direcoes, q) * inverso_det)

        mascara &= ((v >= 0.0) & ((u + v) <= 1.0))

        t = (np.einsum("ij,ij->i", aresta_2, q) * inverso_det)

        mascara &= t > tolerancia

        indices_validos = np.flatnonzero(mascara)

        if indices_validos.size == 0:
            return None

        indice_mais_proximo = indices_validos[np.argmin(t[indices_validos])]

        return int(indice_mais_proximo)

    def _projetar_ponto_na_tela(self, ponto_3d):
        """
        Projeta um ponto do espaço 3D para coordenadas
        de pixel do GLViewWidget.
        """
        try:
            matriz_projecao = self.view.projectionMatrix()

        except TypeError:
            viewport = self.view.getViewport()

            matriz_projecao = self.view.projectionMatrix(viewport, viewport)

        matriz = (matriz_projecao * self.view.viewMatrix())

        clip = matriz.map(QVector4D(
                float(ponto_3d[0]),
                float(ponto_3d[1]),
                float(ponto_3d[2]),
                1.0))

        if abs(clip.w()) < 1e-12:
            return None

        x_ndc = (clip.x() / clip.w())
        y_ndc = (clip.y() / clip.w())

        x_tela = ((x_ndc + 1.0) * 0.5 * self.view.width())
        y_tela = ((1.0 - y_ndc) * 0.5 * self.view.height())

        return np.array([x_tela, y_tela], dtype=float)

    def _distancia_ponto_segmento_2d(self, ponto, inicio, fim):
        """
        Retorna a distância, em pixels, entre um ponto
        e um segmento de reta 2D.
        """
        segmento = fim - inicio
        comprimento_2 = float(np.dot(segmento, segmento))

        if comprimento_2 <= 1e-12:
            return float(
                np.linalg.norm(ponto - inicio))

        parametro = float(
            np.dot(ponto - inicio, segmento) / comprimento_2)

        parametro = max(0.0, min(1.0, parametro))

        projecao = (inicio + parametro * segmento)

        return float(np.linalg.norm( ponto - projecao))

    def _encontrar_aresta_da_face(self, face_id, pos_mouse):
        """
        Retorna a aresta da face que está mais próxima
        do cursor na tela.
        """
        if face_id is None:
            return None

        face = self._faces_editadas[int(face_id)]

        vertices = (self._vertices_visualizacao * float(self._escala_visual_malha))

        ponto_mouse = np.array(
            [float(pos_mouse.x()),
                float(pos_mouse.y())],
            dtype=float)

        arestas = (
            (int(face[0]), int(face[1])),
            (int(face[1]), int(face[2])),
            (int(face[2]), int(face[0])))

        melhor_aresta = None
        menor_distancia = float("inf")

        for vertice_1, vertice_2 in arestas:
            ponto_1 = self._projetar_ponto_na_tela(
                vertices[vertice_1])
            ponto_2 = self._projetar_ponto_na_tela(
                vertices[vertice_2])

            if ponto_1 is None or ponto_2 is None:
                continue

            distancia = (
                self._distancia_ponto_segmento_2d(
                    ponto_mouse,
                    ponto_1,
                    ponto_2))

            if distancia < menor_distancia:
                menor_distancia = distancia
                melhor_aresta = tuple(
                    sorted((vertice_1, vertice_2)))

        if (menor_distancia
            > self._tolerancia_aresta_px):
            return None

        return melhor_aresta

    def _processar_hover_aresta(self, pos_mouse):
        """
        Detecta e destaca uma única aresta sob o cursor.

        Só funciona quando o checkbox de edição está marcado.
        """
        if not self.modo_edicao_arestas:
            return

        # Durante Shift, o hover é suspenso para deixar
        # a navegação visual mais limpa.
        modificadores = (QApplication.keyboardModifiers())

        if (modificadores
            & Qt.KeyboardModifier.ShiftModifier):
            self._limpar_hover_aresta()
            return

        # Limita a aproximadamente 40 verificações por segundo.
        agora_ms = time.monotonic() * 1000.0

        if (agora_ms - self._ultimo_hover_ms < 25.0):
            return

        self._ultimo_hover_ms = agora_ms

        origem, direcao = (self._criar_raio_mouse(pos_mouse))

        if origem is None or direcao is None:
            self._limpar_hover_aresta()
            return

        face_id = self._encontrar_face_sob_raio(origem, direcao)

        if face_id is None:
            self._limpar_hover_aresta()
            return

        aresta = self._encontrar_aresta_da_face(face_id, pos_mouse)

        if aresta is None:
            self._limpar_hover_aresta()
            return

        if aresta == self._aresta_hover:
            return

        self._aresta_hover = aresta
        self._mostrar_aresta_hover(aresta)

    def _mostrar_aresta_hover(self, aresta):
        """
        Exibe a aresta ativa sobre a malha.

        A linha é ligeiramente deslocada na direção da câmera
        para evitar z-fighting com a superfície da malha.

        Laranja:
            aresta interna que pode ser invertida.

        Vermelho:
            aresta de contorno ou topologia inválida.
        """
        if (aresta is None
            or self._vertices_visualizacao is None
            or self._item_aresta_hover is None):
            self._limpar_hover_aresta()
            return

        vertice_1, vertice_2 = map(int, aresta)

        escala = float(self._escala_visual_malha)

        pontos = np.array(
            [self._vertices_visualizacao[vertice_1],
                self._vertices_visualizacao[vertice_2]],
            dtype=np.float64) * escala

        # Afasta ligeiramente a linha em direção à câmera.
        # Isso evita a disputa de profundidade com a malha.
        try:
            camera_qt = self.view.cameraPosition()

            camera = np.array(
                [float(camera_qt.x()),
                    float(camera_qt.y()),
                    float(camera_qt.z())],
                dtype=np.float64)

            meio_aresta = pontos.mean(axis=0)
            direcao_camera = camera - meio_aresta

            comprimento = np.linalg.norm(direcao_camera)

            if comprimento > 1e-12:
                direcao_camera /= comprimento

                vertices_render = (np.asarray(
                        self._vertices_visualizacao,
                        dtype=np.float64) * escala)

                dimensoes = np.ptp(vertices_render, axis=0)

                tamanho_malha = float( np.linalg.norm(dimensoes))

                # Deslocamento pequeno o bastante para parecer
                # sobre a malha, mas suficiente para eliminar falhas.
                deslocamento = max( tamanho_malha * 0.00015, 0.004)

                pontos += (direcao_camera * deslocamento)

        except Exception:
            # O destaque ainda funciona mesmo caso
            # a posição da câmera não esteja disponível.
            pass  # nosec B110

        # Cor conforme a validade da aresta
        if self._aresta_pode_ser_invertida(aresta):
            cor = (1.0, 0.82, 0.02, 1.0)
        else:
            cor = (1.0, 0.08, 0.08, 1.0)

        self._item_aresta_hover.setData(
            pos=np.asarray(
                pontos,
                dtype=np.float32),
            color=cor,
            width=3.0,
            antialias=False,
            mode="lines")

        self._item_aresta_hover.setVisible(True)

        self.view.update()

    def _limpar_hover_aresta(self):
        """
        Remove o destaque da aresta atual.
        """
        self._aresta_hover = None

        if self._item_aresta_hover is not None:
            self._item_aresta_hover.setVisible(False)

        try:
            self.view.update()
        except Exception:
            pass  # nosec B110

    def _obter_camada_origem(self):
        """
        Recupera a camada original que abriu o visualizador.
        """
        if not self._camada_origem_id:
            return None

        camada = QgsProject.instance().mapLayer(self._camada_origem_id)

        if not isinstance(camada, QgsMeshLayer):
            return None

        return camada

    def _adicionar_malha_editada_ao_qgis(self):
        """
        Gera uma nova malha .2dm a partir dos dados editados em memória.

        A escrita é executada por QgsTask para não bloquear a interface.
        A camada original não é alterada.
        """
        if self._vertices_reais is None:
            self.ui_manager.mostrar_mensagem(
                self.tr("Os vértices reais da malha não estão disponíveis."), "Erro")
            return

        if self._faces_editadas is None:
            self.ui_manager.mostrar_mensagem(self.tr("As faces editadas da malha não estão disponíveis."), "Erro")
            return

        vertices = np.asarray(self._vertices_reais, dtype=np.float64)

        faces = np.asarray(self._faces_editadas, dtype=np.int64)

        if vertices.ndim != 2 or vertices.shape[1] < 3:
            self.ui_manager.mostrar_mensagem(self.tr("A estrutura dos vértices da malha não é válida."), "Erro")
            return

        if faces.ndim != 2 or faces.shape[1] != 3:
            self.ui_manager.mostrar_mensagem(self.tr("A estrutura das faces triangulares não é válida."), "Erro")
            return

        camada_origem = self._obter_camada_origem()

        if camada_origem is not None:
            crs_origem = QgsCoordinateReferenceSystem(camada_origem.crs())

            nome_base = camada_origem.name()
        else:
            crs_origem = QgsCoordinateReferenceSystem(QgsProject.instance().crs())

            nome_base = self.tr("Malha")

        if not crs_origem.isValid():
            self.ui_manager.mostrar_mensagem(self.tr("Não foi possível identificar um SRC válido para a nova malha."), "Erro")
            return

        # Impede duas exportações simultâneas no mesmo visualizador.
        if (self._task_exportar_2dm is not None
            and self._task_exportar_2dm.status()
            in (QgsTask.TaskStatus.Queued, QgsTask.TaskStatus.Running)):
            self.ui_manager.mostrar_mensagem(self.tr("A geração da malha já está em andamento."), "Aviso", duracao=2)
            return

        nome_camada = self._gerar_nome_unico_malha_editada(nome_base)

        # Cria um diretório temporário exclusivo.
        # A referência fica guardada no visualizador para impedir
        # uma limpeza prematura.
        self._diretorio_malha_editada = tempfile.mkdtemp(prefix="tempo_salvo_malha_editada_")

        caminho_2dm = os.path.join(self._diretorio_malha_editada, nome_camada + ".2dm")

        # Cópias são feitas antes de iniciar a task.
        # Assim, o usuário pode continuar navegando sem alterar
        # os dados que estão sendo gravados.
        vertices_task = np.array(vertices, dtype=np.float64, copy=True)

        faces_task = np.array(faces, dtype=np.int64, copy=True)

        task = ExportarMalha2DMTask(
            vertices=vertices_task,
            faces=faces_task,
            caminho_saida=caminho_2dm,
            nome_tarefa=self.tr("Gerando malha editada em 2DM" ))

        self._task_exportar_2dm = task

        # Captura valores simples para os callbacks.
        crs_wkt = crs_origem.toWkt()

        self.pushButtonAdicionarMapa.setEnabled(False)

        self.ui_manager.mostrar_mensagem(self.tr("A geração da nova malha foi iniciada em segundo plano."), "Info", duracao=3)

        def tarefa_concluida():
            self._task_exportar_2dm = None

            self._finalizar_adicao_malha_2dm(
                caminho_2dm=caminho_2dm,
                nome_camada=nome_camada,
                crs_wkt=crs_wkt)

        def tarefa_interrompida():
            erro = task.erro
            cancelado = task.cancelado or task.isCanceled()

            self._task_exportar_2dm = None

            if self.malha_modificada:
                self.pushButtonAdicionarMapa.setEnabled(True)

            if cancelado:
                self.ui_manager.mostrar_mensagem(self.tr("A geração da malha foi cancelada."), "Aviso", duracao=3)
                return

            self.ui_manager.mostrar_mensagem(self.tr("Não foi possível gerar a malha 2DM: {erro}").format(erro=erro or self.tr("erro desconhecido")), "Erro")

        task.taskCompleted.connect(tarefa_concluida)

        task.taskTerminated.connect(tarefa_interrompida)

        QgsApplication.taskManager().addTask(task)

    def _gerar_nome_unico_malha_editada(self, nome_base):
        """
        Gera um nome que ainda não exista entre as camadas do projeto.
        """
        base = self.tr("{nome}_Editada").format(nome=nome_base)

        nomes_existentes = {camada.name()
            for camada in QgsProject.instance().mapLayers().values()}

        if base not in nomes_existentes:
            return base

        contador = 1

        while True:
            candidato = "{base}_{contador}".format(base=base, contador=contador)

            if candidato not in nomes_existentes:
                return candidato

            contador += 1

    def _finalizar_adicao_malha_2dm(self, caminho_2dm, nome_camada, crs_wkt):
        """
        Executado após a conclusão da QgsTask.

        Cria a QgsMeshLayer, adiciona a camada ao projeto
        e aplica a simbologia selecionada no visualizador.
        """
        if not os.path.isfile(caminho_2dm):
            if self.malha_modificada:
                self.pushButtonAdicionarMapa.setEnabled(True)

            self.ui_manager.mostrar_mensagem(self.tr("O arquivo 2DM não foi criado."), "Erro")

            return

        nova_camada = QgsMeshLayer(caminho_2dm, nome_camada, "mdal")

        if not nova_camada.isValid():
            if self.malha_modificada:
                self.pushButtonAdicionarMapa.setEnabled(True)

            self.ui_manager.mostrar_mensagem(self.tr("O arquivo 2DM foi criado, mas não pôde ser carregado como uma camada de malha."), "Erro")
            return

        crs = QgsCoordinateReferenceSystem()

        if crs_wkt:
            crs.createFromWkt(crs_wkt)

        if crs.isValid():
            # O 2DM normalmente não registra o SRC.
            # Portanto, atribui o SRC da camada original.
            nova_camada.setCrs(crs)

        # Primeiro adiciona a camada para que o MDAL
        # termine de registrar os grupos de dados.
        QgsProject.instance().addMapLayer(nova_camada)
        
        def finalizar_configuracao_camada():
            """
            Executada no próximo ciclo da interface.
            Nesse momento, o MDAL já registrou os grupos
            de dados da nova camada.
            """
            (simbologia_aplicada, detalhe_simbologia) = self._aplicar_simbologia_visualizador_na_malha(nova_camada)

            try:
                iface.setActiveLayer(nova_camada)

                iface.mapCanvas().setExtent(nova_camada.extent())

                iface.mapCanvas().refresh()

            except Exception:
                print(traceback.format_exc())

            self.malha_modificada = False

            self.pushButtonAdicionarMapa.setEnabled(False)

            if simbologia_aplicada:
                mensagem = self.tr(
                    "A malha editada foi adicionada ao projeto.\n"
                    "Rampa: {rampa}.\n"
                    "Faixas: {faixas}.\n"
                    "Grupo escalar: {grupo}.").format(
                    rampa=self.Comboboxrampa.currentText(),
                    faixas=self.spinbox_faixas.value(),
                    grupo=detalhe_simbologia)

                tipo_mensagem = "Sucesso"

            else:
                mensagem = self.tr(
                    "A malha foi adicionada, mas a simbologia "
                    "não pôde ser aplicada.\n"
                    "Detalhes: {detalhe}").format(
                    detalhe=detalhe_simbologia)

                tipo_mensagem = "Aviso"

            self.ui_manager.mostrar_mensagem(mensagem, tipo_mensagem, duracao=5, caminho_pasta=os.path.dirname(caminho_2dm))

        # Aguarda o QGIS concluir a inicialização da camada MDAL.
        QTimer.singleShot(0, finalizar_configuracao_camada)

    def _localizar_grupo_escalar_elevacao(self, mesh_layer):
        """
        Localiza o grupo escalar associado às cotas Z da malha.

        Retorna:
            group_index, metadata, nomes_grupos
        """
        candidatos = []
        nomes_grupos = []

        try:
            indices_grupos = list(mesh_layer.datasetGroupsIndexes())
        except Exception:
            indices_grupos = []

        for group_index in indices_grupos:
            try:
                group_index = int(group_index)

                # IMPORTANTE:
                # utiliza o dataset real 0, não -1.
                dataset_index = QgsMeshDatasetIndex(group_index, 0)

                quantidade_datasets = mesh_layer.datasetCount(dataset_index)

                if quantidade_datasets <= 0:
                    continue

                metadata = mesh_layer.datasetGroupMetadata(dataset_index)

                nome = (metadata.name() or "").strip()

                nomes_grupos.append("{indice}: {nome}".format(indice=group_index, nome=nome or self.tr("Sem nome")))

                if not metadata.isScalar():
                    continue

                texto = nome.casefold()

                prioridade = 0

                if "bed elevation" in texto:
                    prioridade = 100

                elif "elevação" in texto:
                    prioridade = 95

                elif "elevacao" in texto:
                    prioridade = 95

                elif "elevation" in texto:
                    prioridade = 90

                elif "altitude" in texto:
                    prioridade = 80

                elif texto in ("z", "z value", "z-value"):
                    prioridade = 70

                # Material ID não representa elevação.
                if "material" in texto:
                    prioridade = -100

                minimo = float(metadata.minimum())
                maximo = float(metadata.maximum())

                if (np.isfinite(minimo)
                    and np.isfinite(maximo)):
                    prioridade += 5

                candidatos.append((prioridade, group_index, metadata))

            except Exception:
                print(traceback.format_exc())
                continue

        # Primeiro procura um grupo explicitamente relacionado à elevação.
        candidatos_validos = [candidato
            for candidato in candidatos
            if candidato[0] > 0]

        if candidatos_validos:
            candidatos_validos.sort(key=lambda item: item[0], reverse=True )

            _, group_index, metadata = candidatos_validos[0]

            return (group_index, metadata, nomes_grupos)

        # Segurança: usa o único grupo escalar existente,
        # desde que não seja Material ID.
        candidatos_escalares = [candidato
            for candidato in candidatos
            if candidato[0] > -100]

        if len(candidatos_escalares) == 1:
            _, group_index, metadata = candidatos_escalares[0]

            return (group_index, metadata, nomes_grupos)

        return (None, None, nomes_grupos)

    def _aplicar_simbologia_visualizador_na_malha(self, mesh_layer):
        """
        Aplica à camada de malha do QGIS a rampa utilizada
        no visualizador 3D.
        """
        if not mesh_layer or not mesh_layer.isValid():
            return (False, self.tr("Camada de malha inválida."))

        try:
            # Força o QGIS a carregar a estrutura interna da malha.
            mesh_layer.updateTriangularMesh()

            (group_index, metadata, nomes_grupos) = self._localizar_grupo_escalar_elevacao(mesh_layer)

            if group_index is None or metadata is None:
                grupos_texto = (", ".join(nomes_grupos)
                    if nomes_grupos
                    else self.tr("nenhum grupo detectado"))

                return (False, self.tr(
                        "O grupo de elevação não foi localizado. "
                        "Grupos encontrados: {grupos}.").format(grupos=grupos_texto))

            dataset_index = QgsMeshDatasetIndex(group_index, 0)

            if mesh_layer.datasetCount(dataset_index) <= 0:
                return (False, self.tr("O grupo '{grupo}' não possui datasets.").format(grupo=metadata.name()))

            zmin = float(metadata.minimum())
            zmax = float(metadata.maximum())

            # Usa as cotas do visualizador como segurança.
            if (not np.isfinite(zmin)
                or not np.isfinite(zmax)
                or zmax < zmin):
                z_values = np.asarray(getattr(self, "_z_raw", []), dtype=float)

                z_values = z_values[np.isfinite(z_values)]

                if z_values.size == 0:
                    return (False, self.tr(
                            "Não foi possível determinar "
                            "o intervalo de elevação."))

                zmin = float(z_values.min())
                zmax = float(z_values.max())

            num_faixas = max(1, int(self.spinbox_faixas.value()))

            inverter = bool(self.checkbox_inverter_cores.isChecked())

            bandas = self._band_colors_from_settings(num_faixas, inverter)

            if not bandas:
                return (False, self.tr("A rampa selecionada não possui cores."))

            shader_min = float(zmin)
            shader_max = float(zmax)

            if math.isclose(
                    shader_min,
                    shader_max,
                    rel_tol=1e-12,
                    abs_tol=1e-12):

                shader_max = shader_min + 1e-9
                num_faixas = 1
                bandas = [bandas[0]]
            #
            # Distribui as cores por todo o intervalo de elevação.
            posicoes = np.linspace(shader_min, shader_max, len(bandas))

            itens_shader = []

            for indice, rgba in enumerate(bandas):
                vermelho, verde, azul, alfa = rgba

                cor = QColor()
                cor.setRgbF(
                float(np.clip(vermelho, 0.0, 1.0)),
                float(np.clip(verde, 0.0, 1.0)),
                float(np.clip(azul, 0.0, 1.0)),
                float(np.clip(alfa, 0.0, 1.0)))

                valor = float(posicoes[indice])
                rotulo = self._fmt_br(valor, 2)

                itens_shader.append(QgsColorRampShader.ColorRampItem(valor, cor, rotulo))

            shader = QgsColorRampShader(shader_min, shader_max, None, Qgis.ShaderInterpolationMethod.Linear, Qgis.ShaderClassificationMethod.Continuous)

            shader.setClip(False)

            shader.setColorRampItemList(itens_shader)

            scalar_settings = QgsMeshRendererScalarSettings()

            scalar_settings.setClassificationMinimumMaximum(shader_min, shader_max)

            scalar_settings.setColorRampShader(shader)

            scalar_settings.setOpacity(1.0)

            renderer_settings = (mesh_layer.rendererSettings())

            renderer_settings.setScalarSettings(group_index, scalar_settings)

            renderer_settings.setActiveScalarDatasetGroup(group_index)

            # Somente depois entrega o renderizador completo à camada.
            mesh_layer.setRendererSettings(renderer_settings, True)

            mesh_layer.setCustomProperty("tempo_salvo_tools/rampa_malha", self.Comboboxrampa.currentText())

            mesh_layer.setCustomProperty("tempo_salvo_tools/faixas_malha", num_faixas)

            mesh_layer.setCustomProperty("tempo_salvo_tools/inverter_rampa_malha", inverter)

            mesh_layer.triggerRepaint()

            try:
                iface.layerTreeView().refreshLayerSymbology(mesh_layer.id())

                iface.mapCanvas().clearCache()
                iface.mapCanvas().refresh()

            except Exception:
                print(traceback.format_exc())

            # Verificação interna.
            grupo_ativo = (mesh_layer
                .rendererSettings()
                .activeScalarDatasetGroup() )

            if grupo_ativo != group_index:
                return (False, self.tr(
                        "O QGIS não manteve o grupo escalar ativo. "
                        "Esperado: {esperado}; ativo: {ativo}.").format(esperado=group_index, ativo=grupo_ativo))

            return ( True, self.tr("{grupo}, intervalo {minimo} a {maximo}").format(grupo=metadata.name(), minimo=self._fmt_br(zmin, 2), maximo=self._fmt_br(zmax, 2)))

        except Exception as e:
            print(traceback.format_exc())

            return (False, str(e))

    def _aplicar_enquadramento_inicial(self):
        """
        Aplica na abertura exatamente o mesmo zoom total
        utilizado pelo botão de centralização.
        """
        try:
            if self.mesh_item is None or self.mesh_data is None:
                # A malha ainda não terminou de entrar na cena.
                # Tenta novamente após um pequeno intervalo.
                self._enquadramento_inicial_aplicado = False

                QTimer.singleShot(100, lambda: self.showEvent_deferred())
                return

            self.ver_tudo()

        except Exception as e:
            if self.ui_manager:
                self.ui_manager.mostrar_mensagem(
                    self.ui_manager.tr("Não foi possível aplicar o enquadramento inicial: "
                        "{error}").format(error=e), "Erro")

    def _find_colorbar_widget(self):
        """
        Tenta localizar o widget de colorbar por nomes comuns.
        Deve expor o método update_discrete(labels, band_colors).
        """
        for name in ("colorBar", "colorbarWidget", "widgetColorBar", "colorbar", "cbWidget"):
            cb = getattr(self, name, None)
            if cb is not None and hasattr(cb, "update_discrete"):
                return cb
        return None

    def _update_colorbar_from_arrays(self, z_values: "np.ndarray", colors: "np.ndarray", num_faixas: int):
        """
        Gera faixas [low, high] e uma cor representativa por faixa (média das
        cores dos vértices dentro daquela faixa) e envia para o ColorBarWidget.
        Robusto para z constante, faixas vazias, etc.
        """
        cb = self._find_colorbar_widget()
        if cb is None:
            return

        z_values = np.asarray(z_values).astype(float)
        colors   = np.asarray(colors).astype(float)

        # Sem dados: placeholder único
        if z_values.size == 0 or not np.isfinite(z_values).any():
            cb.update_discrete([""], [(0.85, 0.85, 0.85, 1.0)])
            return

        zmin = float(np.nanmin(z_values))
        zmax = float(np.nanmax(z_values))

        # z constante → uma faixa só
        if not math.isfinite(zmin) or not math.isfinite(zmax) or abs(zmax - zmin) < 1e-12:
            label = f"{zmin:.2f}"
            # usa média global das cores como representativa
            if colors.size:
                c = colors.reshape(-1, colors.shape[-1]).mean(axis=0)
                c = tuple(float(x) for x in c.tolist())
            else:
                c = (0.85, 0.85, 0.85, 1.0)
            cb.update_discrete([label], [c])
            return

        # Constrói edges e agrega cor por banda
        num_faixas = max(1, int(num_faixas))
        edges = np.linspace(zmin, zmax, num_faixas + 1)
        labels = []
        band_colors = []

        flat_colors = colors.reshape(-1, colors.shape[-1]) if colors.ndim > 1 else colors
        for i in range(num_faixas):
            low, high = edges[i], edges[i + 1]
            # último intervalo inclui o high
            if i < num_faixas - 1:
                mask = (z_values >= low) & (z_values < high)
            else:
                mask = (z_values >= low) & (z_values <= high)

            labels.append(f"{low:.2f} – {high:.2f}")

            if mask.any() and flat_colors.size:
                c = flat_colors[mask].mean(axis=0)
            elif flat_colors.size:
                # faixa vazia → usa média global para não “quebrar” a sequência
                c = flat_colors.mean(axis=0)
            else:
                c = (0.85, 0.85, 0.85, 1.0)

            # garante tupla de floats (RGBA) no range [0,1]
            c = tuple(float(x) for x in np.asarray(c).tolist())
            if max(c) > 1.0:
                c = tuple(x / 255.0 for x in c)
            if len(c) == 3:
                c = (*c, 1.0)

            band_colors.append(c)

        cb.update_discrete(labels, band_colors)

    def load_and_draw_buffers(self, vertices_np, faces_np):
        """
        Desenha a malha diretamente de arrays (vértices/faces), sem ler DAE.
        Robustez: não depende da existência de controles específicos da UI; usa defaults.
        """
        # helpers para ler UI com segurança
        def _ui_bool(names, default=False):
            for n in names:
                w = getattr(self, n, None)
                if hasattr(w, "isChecked"):
                    try:
                        return bool(w.isChecked())
                    except Exception:
                        pass  # nosec B110
            return default

        def _ui_int(names, default):
            for n in names:
                w = getattr(self, n, None)
                if hasattr(w, "value"):
                    try:
                        return int(w.value())
                    except Exception:
                        pass  # nosec B110
            return default

        # Remove item anterior, se houver
        try:
            if getattr(self, "mesh_item", None) is not None:
                self.view.removeItem(self.mesh_item)
                self.mesh_item = None
        except Exception:
            pass  # nosec B110

        # Preserva os vértices nas coordenadas reais
        vertices_reais = np.asarray(vertices_np, dtype=float).copy()

        self._vertices_reais = vertices_reais.copy()

        # Guarda Z original para cores e legenda
        self._z_raw = vertices_reais[:, 2].copy()
        self._zmin_raw = (
            float(self._z_raw.min())
            if self._z_raw.size
            else 0.0)
        self._zmax_raw = (
            float(self._z_raw.max())
            if self._z_raw.size
            else 0.0)

        # Centraliza somente a cópia usada pelo OpenGL
        if vertices_reais.size:
            cx = (vertices_reais[:, 0].min() + vertices_reais[:, 0].max()) / 2.0

            cy = (vertices_reais[:, 1].min() + vertices_reais[:, 1].max()) / 2.0

            cz = (vertices_reais[:, 2].min() + vertices_reais[:, 2].max()) / 2.0

            self._centro_visualizacao = np.array([cx, cy, cz], dtype=float)

            vertices_np = (vertices_reais - self._centro_visualizacao)
        else:
            self._centro_visualizacao = np.zeros(3, dtype=float)

            vertices_np = vertices_reais.copy()

        self._vertices_visualizacao = vertices_np.copy()

        # Lê configurações da UI com defaults seguros
        draw_edges = _ui_bool(["checkbox_linhas", "checkBoxLinhas", "cbLinhas", "chkLinhas"], True)
        bg_white   = _ui_bool(["radio_white", "rbWhite", "radioButtonWhite", "rbBranco"], True)
        num_faixas = _ui_int (["slider_faixas", "sldFaixas", "horizontalSliderFaixas", "sliderFaixas"], 7)
        inverter   = _ui_bool(["checkbox_inverter_cores", "checkBoxInverterCores", "cbInvert", "chkInvert"], False)

        # Cores por faixas (usa método da classe se existir; senão cai no fallback)
        z_values = self._z_raw
        try:
            if hasattr(self, "criar_simbologia_gradiente_discreta"):
                colors = self.criar_simbologia_gradiente_discreta(z_values, num_faixas, inverter)
                colors = np.asarray(colors, dtype=float)
                if colors.size and colors.max() > 1.0:
                    colors = colors / 255.0
            else:
                # Fallback: escala de cinza simples
                if z_values.size:
                    zmin, zmax = float(z_values.min()), float(z_values.max())
                    den = max(zmax - zmin, 1e-9)
                    t = (z_values - zmin) / den
                    colors = np.c_[t, t, t, np.ones_like(t)]
                else:
                    colors = np.zeros((0, 4), dtype=float)
        except Exception:
            # Fallback de segurança, mesmo se algo der errado na geração de cores
            if z_values.size:
                zmin, zmax = float(z_values.min()), float(z_values.max())
                den = max(zmax - zmin, 1e-9)
                t = (z_values - zmin) / den
                colors = np.c_[t, t, t, np.ones_like(t)]
            else:
                colors = np.zeros((0, 4), dtype=float)

        # Corrige orientação e garante o tipo adequado
        faces_np = np.asarray(faces_np, dtype=np.int32)

        if faces_np.size:
            faces_np = faces_np[:, ::-1]

        # Guarda a topologia original e a cópia editável
        self._faces_originais = faces_np.copy()
        self._faces_editadas = faces_np.copy()

        # Nova malha: reinicia o histórico de edição
        self._pilha_desfazer_arestas.clear()
        self._pilha_refazer_arestas.clear()

        # Constrói o índice de arestas
        self._construir_indice_arestas()

        # MeshData usando a topologia editável
        self.mesh_data = gl.MeshData(
            vertexes=self._vertices_visualizacao,
            faces=self._faces_editadas,
            vertexColors=colors)

        try:
            _ = self.mesh_data.vertexNormals()
        except Exception:
            pass  # nosec B110

        # Mantém compatibilidade com a exportação DAE
        self._export_vertices_raw = (self._vertices_visualizacao.copy())

        self._export_faces_raw = (self._faces_editadas.copy())

        # Shader (usa método se existir; senão 'shaded')
        shader_obj = "shaded"
        try:
            if hasattr(self, "_get_phong_rim_shader"):
                shader_obj = self._get_phong_rim_shader()
        except Exception:
            shader_obj = "shaded"

        edge = (0.12, 0.12, 0.12, 1.0) if bg_white else (0.9, 0.9, 0.9, 1.0)

        self.mesh_item = GLMeshItemComEspessura(
            meshdata=self.mesh_data,
            smooth=True,
            drawFaces=True,
            drawEdges=draw_edges,
            edgeColor=edge,
            edgeWidth=self._espessura_arestas(),
            shader=shader_obj,
            glOptions="opaque")

        self.mesh_item.scale(10, 10, 10)

        self.view.addItem(self.mesh_item)

        try:
            self.view.setBackgroundColor("w" if bg_white else "k")
        except Exception:
            pass  # nosec B110

        # Atualiza colorbar/eixos se os métodos existirem
        try:
            if hasattr(self, "_update_colorbar"):
                self._update_colorbar()
        except Exception:
            pass  # nosec B110

        # guarda para futuros refreshes a partir de sinais da UI (se existirem)
        self._vertex_colors = colors

        # atualiza a colorbar imediatamente com as mesmas faixas/cores usadas no mesh
        self._update_colorbar_from_arrays(self._z_raw, self._vertex_colors, num_faixas)

        # (se você ainda chama algo como _ensure_axes_after_mesh_change(), mantenha)
        try:
            if hasattr(self, "_ensure_axes_after_mesh_change"):
                self._ensure_axes_after_mesh_change()
        except Exception:
            pass  # nosec B110

        # A nova malha começa sem alterações temporárias
        self.malha_modificada = False
        self._aresta_hover = None

        if hasattr(self, "pushButtonAdicionarMapa"):
            self.pushButtonAdicionarMapa.setEnabled(False)

    def salvar_visualizacao_como_png(self):
        """
        Salva a visualização 3D atual como uma imagem PNG.

        Esta função usa o método escolher_local_para_salvar de UiManagerM para permitir que o
        usuário escolha o local e o nome do arquivo PNG. Depois de capturar a imagem da área 3D
        (GLViewWidget), ela é salva no local escolhido. Se o processo for concluído com sucesso, uma
        mensagem de sucesso é exibida; caso contrário, uma mensagem de erro é exibida.

        Parâmetros:
        - Nenhum parâmetro explícito. A função usa o estado interno do objeto para capturar e salvar a visualização.

        Retorno:
        - Nenhum retorno explícito. Salva um arquivo PNG no local escolhido ou exibe mensagens de erro em caso de falha.
        """
        # Usar a função escolher_local_para_salvar da classe UiManagerM para obter o caminho do arquivo
        file_path = self.ui_manager.escolher_local_para_salvar("visualizacao_malha", self.ui_manager.tr("PNG Files (*.png)"))
        
        if not file_path:
            # Se o usuário cancelar a operação, mostrar uma mensagem de erro e sair
            self.ui_manager.mostrar_mensagem(self.ui_manager.tr("Operação cancelada pelo usuário."), "Erro")
            return  # Se não houver caminho, interrompe a função

        # Capturar a visualização da área 3D e salvar como PNG
        try:
            # Capturar a imagem da visualização 3D (tamanho atual da janela)
            img = self.view.grabFramebuffer()  # Captura o conteúdo da área 3D como uma imagem
            
            # Salvar a imagem no caminho escolhido com formato PNG
            img.save(file_path, 'PNG')

            # Mostrar uma mensagem de sucesso usando a função mostrar_mensagem de UiManagerM
            self.ui_manager.mostrar_mensagem(self.ui_manager.tr("Visualização salva com sucesso em {file_path}").format(file_path=file_path), "Sucesso", caminho_pasta=os.path.dirname(file_path), caminho_arquivo=file_path)

        except Exception as e:
            # Se houver um erro, mostrar a mensagem de erro
            self.ui_manager.mostrar_mensagem(self.ui_manager.tr("Erro ao salvar a visualização: {error}").format(error=str(e)), "Erro")

    def salvar_visualizacao_como_dae(self):
        """
        Salva a malha atualmente visualizada em DAE (COLLADA),
        respeitando a geometria original e as cores atuais da escala.
        """
        file_path = self.ui_manager.escolher_local_para_salvar("visualizacao_malha", self.ui_manager.tr("DAE Files (*.dae)"))

        if not file_path:
            self.ui_manager.mostrar_mensagem(self.ui_manager.tr("Operação cancelada pelo usuário."), "Erro")
            return

        try:
            if self._export_vertices_raw is None or self._export_faces_raw is None:
                raise RuntimeError(self.ui_manager.tr("Não há geometria carregada para exportar."))

            vertices_np = np.asarray(self._export_vertices_raw, dtype=float)
            faces_np = np.asarray(self._export_faces_raw, dtype=int)

            # Usa as cores atuais do visualizador, se existirem
            if self._vertex_colors is not None and len(self._vertex_colors) == len(vertices_np):
                colors = np.asarray(self._vertex_colors, dtype=float)
            elif hasattr(self, "_z_raw") and self._z_raw is not None:
                colors = np.asarray(
                    self.criar_simbologia_gradiente_discreta(
                        self._z_raw,
                        self.slider_faixas.value(),
                        self.checkbox_inverter_cores.isChecked()),
                    dtype=float)
            else:
                colors = np.ones((len(vertices_np), 4), dtype=float)

            # Garante faixa [0, 1]
            if colors.size and colors.max() > 1.0:
                colors = colors / 255.0

            positions = vertices_np.reshape(-1).tolist()
            colors_flat = colors.reshape(-1).tolist()
            tri_indices = faces_np.reshape(-1).tolist()

            collada = XmlET.Element(
                "COLLADA",
                xmlns="http://www.collada.org/2005/11/COLLADASchema",
                version="1.4.1")

            asset = XmlET.SubElement(collada, "asset")
            XmlET.SubElement(asset, "created").text = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
            XmlET.SubElement(asset, "modified").text = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
            XmlET.SubElement(asset, "unit", name="meter", meter="1")
            XmlET.SubElement(asset, "up_axis").text = "Z_UP"

            lib_geo = XmlET.SubElement(collada, "library_geometries")
            geometry = XmlET.SubElement(lib_geo, "geometry", id="mesh", name="mesh")
            mesh = XmlET.SubElement(geometry, "mesh")

            def _append_source(mesh_elem, name, stride, array):
                src = XmlET.SubElement(mesh_elem, "source", id=f"mesh-{name}")
                fa = XmlET.SubElement(src, "float_array", id=f"mesh-{name}-array", count=str(len(array)))
                fa.text = " ".join(map(str, array))

                tech = XmlET.SubElement(src, "technique_common")
                acc = XmlET.SubElement(
                    tech,
                    "accessor",
                    source=f"#mesh-{name}-array",
                    count=str(len(array) // stride),
                    stride=str(stride))

                if name == "positions":
                    XmlET.SubElement(acc, "param", name="X", type="float")
                    XmlET.SubElement(acc, "param", name="Y", type="float")
                    XmlET.SubElement(acc, "param", name="Z", type="float")
                elif name == "colors":
                    XmlET.SubElement(acc, "param", name="R", type="float")
                    XmlET.SubElement(acc, "param", name="G", type="float")
                    XmlET.SubElement(acc, "param", name="B", type="float")
                    XmlET.SubElement(acc, "param", name="A", type="float")

            _append_source(mesh, "positions", 3, positions)
            _append_source(mesh, "colors", 4, colors_flat)

            verts = XmlET.SubElement(mesh, "vertices", id="mesh-vertices")
            XmlET.SubElement(verts, "input", semantic="POSITION", source="#mesh-positions")
            XmlET.SubElement(verts, "input", semantic="COLOR", source="#mesh-colors")

            tris = XmlET.SubElement(mesh, "triangles", count=str(len(tri_indices) // 3))
            XmlET.SubElement(tris, "input", semantic="VERTEX", source="#mesh-vertices", offset="0")
            p_elem = XmlET.SubElement(tris, "p")
            p_elem.text = " ".join(map(str, tri_indices))

            lib_scenes = XmlET.SubElement(collada, "library_visual_scenes")
            v_scene = XmlET.SubElement(lib_scenes, "visual_scene", id="Scene", name="Scene")
            node = XmlET.SubElement(v_scene, "node", id="mesh", name="mesh", type="NODE")
            XmlET.SubElement(node, "matrix", sid="transform").text = "1 0 0 0 0 1 0 0 0 0 1 0 0 0 0 1"
            XmlET.SubElement(node, "instance_geometry", url="#mesh")

            scene = XmlET.SubElement(collada, "scene")
            XmlET.SubElement(scene, "instance_visual_scene", url="#Scene")

            XmlET.ElementTree(collada).write(file_path, encoding="UTF-8", xml_declaration=True)

            self.ui_manager.mostrar_mensagem(self.ui_manager.tr("DAE salvo com sucesso em {file_path}").format(file_path=file_path), "Sucesso", caminho_pasta=os.path.dirname(file_path), caminho_arquivo=file_path)

        except Exception as e:
            self.ui_manager.mostrar_mensagem(self.ui_manager.tr("Erro ao salvar DAE: {error}").format(error=str(e)), "Erro")

    def alternar_eixos_xyz(self, state):
        """
        Exibe ou oculta somente o eixo de orientação
        fixo no canto inferior esquerdo.
        """
        visivel = state == Qt.CheckState.Checked

        self.view.set_corner_axis_visible(visivel)

    def decrease_slider_value(self):
        """
        Diminui o valor atual do slider de faixas de cores em 1 unidade.

        Esta função verifica o valor atual do slider (`self.slider_faixas`). Se o valor atual for maior
        que o valor mínimo permitido pelo slider, ele é diminuído em 1 unidade.

        Ações realizadas:
        - Verifica o valor atual do slider.
        - Compara o valor atual com o valor mínimo permitido.
        - Se o valor atual for maior que o mínimo, diminui o valor do slider em 1 unidade.

        Parâmetros:
        - Nenhum parâmetro explícito. A função opera sobre o estado atual do slider de faixas de cores.

        Retorno:
        - Nenhum retorno explícito. Atualiza o valor do slider diretamente.
        """
        # Obtém o valor atual do slider de faixas de cores
        current_value = self.slider_faixas.value()
        
        # Verifica se o valor atual é maior que o valor mínimo permitido pelo slider
        if current_value > self.slider_faixas.minimum():
            # Se for maior, diminui o valor do slider em 1 unidade
            self.slider_faixas.setValue(current_value - 1)

    def increase_slider_value(self):
        """
        Aumenta o valor atual do slider de faixas de cores em 1 unidade.

        Esta função verifica o valor atual do slider (`self.slider_faixas`). Se o valor atual for menor
        que o valor máximo permitido pelo slider, ele é aumentado em 1 unidade.

        Ações realizadas:
        - Verifica o valor atual do slider.
        - Compara o valor atual com o valor máximo permitido.
        - Se o valor atual for menor que o máximo, aumenta o valor do slider em 1 unidade.

        Parâmetros:
        - Nenhum parâmetro explícito. A função opera sobre o estado atual do slider de faixas de cores.

        Retorno:
        - Nenhum retorno explícito. Atualiza o valor do slider diretamente.
        """
        # Obtém o valor atual do slider de faixas de cores
        current_value = self.slider_faixas.value()

        # Verifica se o valor atual é menor que o valor máximo permitido pelo slider
        if current_value < self.slider_faixas.maximum():
            # Se for menor, aumenta o valor do slider em 1 unidade
            self.slider_faixas.setValue(current_value + 1)

    def mudar_fundo(self):
        """
        Altera a cor de fundo da visualização 3D com base no RadioButton selecionado.

        Esta função verifica qual dos RadioButtons está selecionado: se o fundo branco ou o fundo preto.
        Dependendo da seleção, a função altera a cor de fundo da visualização 3D para branco ou preto.
        Além disso, para manter a legibilidade da malha, ela recria o objeto GLMeshItem ajustando
        automaticamente a cor das arestas (edges) de acordo com o fundo escolhido.

        Ações realizadas:
        - Verifica qual RadioButton está marcado:
          - Se "Fundo Branco": define fundo branco e usa arestas escuras.
          - Se "Fundo Preto": define fundo preto e usa arestas claras.
        - Remove o GLMeshItem atual (se existir) e recria-o com a cor de aresta adequada.
        - Mantém todas as demais características da malha (dados, escala, shader e checkbox de arestas).

        Parâmetros:
        - Nenhum. Opera sobre o estado dos RadioButtons e do GLMeshItem atual.

        Retorno:
        - Nenhum. Atualiza diretamente a visualização 3D.
        """
        # Parte 1: definir cor do fundo
        # Se o RadioButton de fundo branco estiver selecionado
        if self.radio_white.isChecked():
            # Define a cor de fundo como branca
            self.view.setBackgroundColor('w')
        # Se o RadioButton de fundo preto estiver selecionado
        elif self.radio_black.isChecked():
            # Define a cor de fundo como preta
            self.view.setBackgroundColor('k')

        # Parte 2: recriar o GLMeshItem para ajustar arestas
        # Só faz a operação se já houver malha carregada (mesh_data)
        if self.mesh_item is not None and self.mesh_data is not None:
            # Remove o item antigo da cena para evitar sobreposição
            self.view.removeItem(self.mesh_item)

            # Define cor das arestas de forma adaptativa:
            # - Fundo branco → arestas escuras (preto suave)
            # - Fundo preto  → arestas claras (branco suave)
            edge = (0.1, 0.1, 0.1, 1.0) if self.radio_white.isChecked() else (0.9, 0.9, 0.9, 1.0)

            # # Recria o objeto da malha 3D com as mesmas configurações
            self.mesh_item = GLMeshItemComEspessura(
                meshdata=self.mesh_data,
                smooth=False,
                drawEdges=self.checkbox_edges.isChecked(),
                edgeColor=edge,
                edgeWidth=self._espessura_arestas(),
                shader=self._get_phong_rim_shader(),
                glOptions="opaque"
            )

            # Escala da malha (mantém a mesma do carregamento inicial)
            self.mesh_item.scale(10, 10, 10)

            # Adiciona novamente a malha à visualização 3D
            self.view.addItem(self.mesh_item)

    def enquadrar_malha(self, vertices_np):
        """
        Centraliza e enquadra toda a malha no visualizador.

        Também define essa distância como a posição central
        do slider de zoom.
        """
        try:
            vertices_np = np.asarray(
                vertices_np,
                dtype=float)

            if (vertices_np.ndim != 2
                or vertices_np.shape[0] == 0
                or vertices_np.shape[1] < 3):
                return

            min_bounds = np.nanmin(vertices_np[:, :3], axis=0)
            max_bounds = np.nanmax(vertices_np[:, :3], axis=0)

            centro = (min_bounds + max_bounds) / 2.0
            tamanho = (max_bounds - min_bounds)

            # A malha é exibida com escala 10.
            escala_visual = 10.0

            self.view.definir_limite_zoom_malha(vertices_np[:, :3] * escala_visual)

            diagonal = float(np.linalg.norm(tamanho * escala_visual))

            if (not math.isfinite(diagonal)
                or diagonal <= 0):
                diagonal = 1.0

            # Margem suficiente para a malha inteira aparecer,
            # sem iniciar aproximada demais.
            distancia = max(1.0, diagonal * 1.20)

            # Como os vértices já são centralizados durante
            # o carregamento, o centro visual deve ser a origem.
            self.view.opts["center"] = pg.Vector(0.0, 0.0, 0.0)
            self.view.opts["fov"] = 60.0

            self.view.setCameraPosition(azimuth=45, elevation=30)
            self.view.definir_zoom_central(distancia)

            self.view.update()

        except Exception as e:
            if self.ui_manager:
                self.ui_manager.mostrar_mensagem(self.ui_manager.tr("Não foi possível enquadrar a malha: {error}").format(error=e), "Erro")

    def alternar_linhas_vertices(self):
        """
        Atualiza a exibição das linhas dos vértices (arestas) da malha 3D.

        Esta função verifica se os dados da malha (mesh_data) estão disponíveis. Se estiverem, a função remove
        a malha atual da visualização e a recria com a opção de exibir ou ocultar as linhas das arestas com base no estado do checkbox.
        A exibição das arestas é controlada pelo checkbox `self.checkbox_edges`.

        Ações realizadas:
        - Verifica se a malha (mesh_data) está carregada.
        - Remove o item da malha atual da visualização.
        - Recria o item da malha com a opção de desenhar ou não as arestas, dependendo do estado do checkbox.
        - Adiciona novamente o item da malha à visualização.
        - Atualiza a visualização para refletir as mudanças.

        Parâmetros:
        - Nenhum parâmetro explícito. A função opera sobre o estado atual da visualização 3D e o checkbox.

        Retorno:
        - Nenhum retorno explícito. Atualiza a visualização 3D diretamente.
        """
        # Verifica se os dados da malha estão carregados
        if self.mesh_data is not None:
            # Remove o item da malha atual da visualização
            self.view.removeItem(self.mesh_item)  # Remove o item da malha atual

            # Recria o item da malha com a opção de desenhar as arestas (drawEdges) controlada pelo checkbox
            edge = (0.1, 0.1, 0.1, 0.9) if self.radio_white.isChecked() else (0.9, 0.9, 0.9, 1.0)

            self.mesh_item = GLMeshItemComEspessura(
                meshdata=self.mesh_data,
                smooth=False,
                drawEdges=self.checkbox_edges.isChecked(),
                edgeColor=edge,
                edgeWidth=self._espessura_arestas(),
                shader=self._get_phong_rim_shader(),
                glOptions="opaque")

            # Ajusta o tamanho da malha
            self.mesh_item.scale(10, 10, 10)

            # Adiciona o item da malha de volta à visualização
            self.view.addItem(self.mesh_item)

            # Atualiza a visualização para aplicar as mudanças
            self.view.update()

    def _get_phong_rim_shader(self):
        """
        Shader Phong + rim (silhueta) com iluminação two-sided.
        - Usa faceforward para orientar a normal para a câmera.
        - Mantém a cor por vértice (vColor) que você já aplica pelo gradiente de Z.
        - Se ShaderProgram não estiver disponível, faz fallback para 'shaded'.
        """
        if hasattr(self, "_phong_rim_cached"):
            return self._phong_rim_cached

        try:
            vshader = """
            varying vec3 vNormal;
            varying vec3 vPos;
            varying vec4 vColor;
            void main() {
                gl_Position = gl_ModelViewProjectionMatrix * gl_Vertex;
                vPos    = (gl_ModelViewMatrix * gl_Vertex).xyz;
                vNormal = normalize(gl_NormalMatrix * gl_Normal);
                vColor  = gl_Color;
            }
            """;

            # // Iluminação two-sided: usa normal virada para o observador.
            fshader = """
            varying vec3 vNormal;
            varying vec3 vPos;
            varying vec4 vColor;
            uniform vec3  light_dir;   // em espaço de view
            uniform float ambient;
            uniform float diffuse;
            uniform float specular;
            uniform float shininess;
            uniform float rim;

            void main() {
                vec3 N = normalize(vNormal);
                vec3 V = normalize(-vPos);                 // direção p/ câmera
                vec3 Nf = faceforward(N, -V, N);           // vira normal p/ a câmera (two-sided)
                vec3 L = normalize(light_dir);             // luz desde a câmera
                vec3 H = normalize(L + V);

                float lambert = max(dot(Nf, L), 0.0);      // difuso em ambas as faces
                float specHL  = pow(max(dot(Nf, H), 0.0), shininess);

                // Rim realça silhueta dos dois lados (usa Nf)
                float rimTerm = pow(1.0 - max(dot(Nf, V), 0.0), 2.0) * rim;

                vec3 base = vColor.rgb;                    // cor já vinda do seu gradiente por Z
                vec3 col  = base * (ambient + diffuse * lambert)
                            + specular * specHL * vec3(1.0)
                            + rimTerm * vec3(0.25);

                gl_FragColor = vec4(col, vColor.a);
            }
            """;

            sp = ShaderProgram('phong_rim_twosided', [vshader, fshader])
            # parâmetros próximos do 3dviewer
            sp.setUniform('light_dir', (0.0, 0.0, 1.0))
            sp.setUniform('ambient',   0.35)
            sp.setUniform('diffuse',   0.85)
            sp.setUniform('specular',  0.20)
            sp.setUniform('shininess', 48.0)
            sp.setUniform('rim',       0.65)

            self._phong_rim_cached = sp
            return sp

        except Exception:
            self._phong_rim_cached = 'shaded'  # fallback (sem two-sided custom)
            return 'shaded'

    def criar_simbologia_gradiente_discreta(self,valores,num_faixas=5, inverter_gradiente=False):
        """
        Cria as cores discretas dos vértices utilizando a rampa
        atualmente selecionada no ComboBox.

        As cores são distribuídas conforme os valores de elevação
        e o número de faixas definido na interface.
        """
        valores = np.asarray(valores, dtype=float).reshape(-1)

        if valores.size == 0:
            return np.zeros((0, 4), dtype=float)

        num_faixas = max(1, int(num_faixas))

        # Obtém as cores discretas da rampa selecionada.
        cores_faixas = np.asarray(self._band_colors_from_settings(num_faixas, inverter_gradiente), dtype=float)

        min_valor = float(np.min(valores))

        max_valor = float(np.max(valores))

        # Caso todos os vértices possuam a mesma elevação,
        # utiliza a primeira cor da rampa.
        if math.isclose(min_valor, max_valor, rel_tol=1e-12, abs_tol=1e-12):

            return np.tile(cores_faixas[0], (valores.size, 1))

        # Limites internos entre as faixas.
        limites = np.linspace(min_valor, max_valor, num_faixas + 1)

        # Apenas os limites internos são necessários.
        # O resultado sempre ficará entre 0 e num_faixas - 1.
        indices = np.searchsorted(limites[1:-1], valores, side="right")

        indices = np.clip(indices, 0, num_faixas - 1)

        return cores_faixas[indices]

    def ver_tudo(self):
        """
        Mostra toda a malha no visualizador e redefine o slider
        para sua posição central.
        """
        try:
            mins, maxs = self._scene_bounds()

            center = (mins + maxs) * 0.5

            size = (maxs - mins)

            # Margem para evitar que a malha encoste nas bordas.
            size *= 1.15

            diagonal = float(np.linalg.norm(size))

            distancia = max(1.0, diagonal * 0.9)

            # Centraliza a câmera no centro real da cena.
            self.view.opts["center"] = pg.Vector(
                float(center[0]),
                float(center[1]),
                float(center[2]))

            self.view.opts["fov"] = 60.0

            self.view.setCameraPosition(distance=distancia, azimuth=45, elevation=30)

            # Essa distância passa a representar o centro do slider.
            self.view._zoom_center_distance = distancia

            if hasattr(self.view, "zoom_slider"):
                self.view.zoom_slider.blockSignals(True)

                try:
                    self.view.zoom_slider.setValue(50)
                finally:
                    self.view.zoom_slider.blockSignals(False)

            self.view.update()

        except Exception as e:
            if self.ui_manager:
                self.ui_manager.mostrar_mensagem(self.ui_manager.tr("Não foi possível mostrar toda a visualização: {error}").format(error=e), "Erro")

    def _scene_bounds(self):
        """
        Retorna (min_xyz, max_xyz) do que existe na cena:
        - Malha (mesh_data) já considerando a escala aplicada ao GLMeshItem (10x).
        - Eixos XYZ (se estiverem presentes).
        """
        have_any = False
        mins = np.array([ np.inf,  np.inf,  np.inf], dtype=float)
        maxs = np.array([-np.inf, -np.inf, -np.inf], dtype=float)

        # Malha (considera escala do GLMeshItem)
        if self.mesh_data is not None and self.mesh_item is not None:
            try:
                V = self.mesh_data.vertexes()  # (N,3) centrados no load
                # sua malha é escalada em 10x após adicionar:
                V = V * 10.0
                vmin = V.min(axis=0)
                vmax = V.max(axis=0)
                mins = np.minimum(mins, vmin); maxs = np.maximum(maxs, vmax)
                have_any = True
            except Exception:
                pass  # nosec B110

        # Eixos (se existirem)
        if getattr(self, "eixos_xyz", None):
            try:
                # eixos foram criados como linhas entre [0,0,0] e [tamanho,0,0] etc.
                # então basta considerar o tamanho que você usou:
                tamanho_eixo = 120.0
                axis_pts = np.array([
                    [0, 0, 0], [tamanho_eixo, 0, 0],
                    [0, 0, 0], [0, tamanho_eixo, 0],
                    [0, 0, 0], [0, 0, tamanho_eixo]
                ], dtype=float)
                vmin = axis_pts.min(axis=0)
                vmax = axis_pts.max(axis=0)
                mins = np.minimum(mins, vmin); maxs = np.maximum(maxs, vmax)
                have_any = True
            except Exception:
                pass  # nosec B110

        if not have_any:
            # fallback: volume pequeno ao redor da origem
            return np.array([-1.0, -1.0, -1.0]), np.array([1.0, 1.0, 1.0])
        return mins, maxs

    def _ensure_axes_after_mesh_change(self):
        """
        Atualiza o eixo fixo de orientação após alterações na malha.
        """
        self.view.set_corner_axis_visible(self.checkbox_xyz.isChecked())

    def load_and_draw_dae(self):
        """
        Carrega um DAE, aplica cores por Z (faixas), e desenha a malha com
        sombreamento semelhante ao 3dviewer: Phong + rim (quando disponível),
        mantendo o controle de arestas pelo checkbox.
        """
        # Remover item anterior (se houver) para evitar sobreposição/leak
        try:
            if getattr(self, "mesh_item", None) is not None:
                self.view.removeItem(self.mesh_item)
                self.mesh_item = None
        except Exception:
            pass  # nosec B110

        vertices = []
        faces = []

        try:
            # 1) Ler DAE de forma segura
            tree, root = self.ui_manager._parse_xml_file_seguro(self.dae_file_path)
            if tree is None or root is None:
                return

            ns = "{http://www.collada.org/2005/11/COLLADASchema}"

            # 2) Vértices
            for source in root.findall(f".//{ns}float_array"):
                if "positions" in source.attrib.get("id", ""):
                    raw = list(map(float, source.text.split()))
                    for i in range(0, len(raw), 3):
                        vertices.append([raw[i], raw[i+1], raw[i+2]])
                    break

            # 3) Faces (assumindo triângulos indexados simples)
            for p in root.findall(f".//{ns}p"):
                raw = list(map(int, p.text.split()))
                for i in range(0, len(raw), 3):
                    faces.append([raw[i], raw[i+1], raw[i+2]])

            if not vertices or not faces:
                self.ui_manager.mostrar_mensagem(self.ui_manager.tr("Nenhuma geometria encontrada no DAE."), "Erro")
                return

            # 4) NumPy + centralizar
            vertices_np = np.array(vertices, dtype=float)

            faces_np    = np.array(faces, dtype=int)

            # Preserva os vértices nas coordenadas originais
            vertices_reais = np.asarray(vertices_np, dtype=float).copy()

            self._vertices_reais = vertices_reais.copy()

            # Z original para cores e legenda
            self._z_raw = vertices_reais[:, 2].copy()
            self._zmin_raw = float(self._z_raw.min())
            self._zmax_raw = float(self._z_raw.max())

            # Centraliza somente a cópia usada na visualização OpenGL
            self._centro_visualizacao = vertices_reais.mean(axis=0)

            vertices_np = (vertices_reais - self._centro_visualizacao)

            self._vertices_visualizacao = vertices_np.copy()

            # 5) Cores por Z (faixas)  -> usa Z ORIGINAL
            z_values = self._z_raw
            num_faixas = self.slider_faixas.value()
            inverter = self.checkbox_inverter_cores.isChecked()
            colors = self.criar_simbologia_gradiente_discreta(z_values, num_faixas, inverter)

            # Garantir formato/intervalo das cores: (N,4) float [0..1]
            colors = np.asarray(colors, dtype=float)
            if colors.max() > 1.0:
                colors = colors / 255.0

            # Corrige a orientação das faces
            faces_np = np.asarray(faces_np[:, ::-1], dtype=np.int32)

            # Guarda uma cópia imutável de referência
            self._faces_originais = faces_np.copy()

            # Esta será a cópia efetivamente modificada durante a edição
            self._faces_editadas = faces_np.copy()

            # Nova malha: reinicia o histórico de edição
            self._pilha_desfazer_arestas.clear()
            self._pilha_refazer_arestas.clear()

            # Cria o índice de vizinhança das arestas
            self._construir_indice_arestas()

            # Cria a malha usando a cópia editável
            self.mesh_data = gl.MeshData(vertexes=self._vertices_visualizacao, faces=self._faces_editadas, vertexColors=colors)

            try: # força o cálculo (ignora se já existir)
                _ = self.mesh_data.vertexNormals()
            except Exception:
                pass  # nosec B110

            self._vertex_colors = colors.copy()

            # Mantém compatibilidade com as funções de exportação existentes
            # O DAE visual atual usa os vértices centralizados.
            self._export_vertices_raw = (self._vertices_visualizacao.copy())

            # A exportação deverá sempre considerar as faces editáveis
            self._export_faces_raw = (self._faces_editadas.copy())

            # 7) GLMeshItem com shader (Phong+rim se disponível, senão 'shaded')
            shader_obj = self._get_phong_rim_shader()  # pode devolver ShaderProgram ou 'shaded'
            edge = (0.12, 0.12, 0.12, 1.0) if self.radio_white.isChecked() else (0.9, 0.9, 0.9, 1.0)

            self.mesh_item = GLMeshItemComEspessura(
                meshdata=self.mesh_data,
                smooth=False,
                drawEdges=self.checkbox_edges.isChecked(),
                edgeColor=edge,
                edgeWidth=self._espessura_arestas(),
                shader=self._get_phong_rim_shader(),
                glOptions="opaque")

            # 8) Escala, adicionar e fundo
            self.mesh_item.scale(10, 10, 10)
            self.view.addItem(self.mesh_item)

            # Toda nova malha começa sem alterações temporárias
            self.malha_modificada = False
            self._aresta_hover = None

            if hasattr(self, "pushButtonAdicionarMapa"):
                self.pushButtonAdicionarMapa.setEnabled(False)

            self.view.setBackgroundColor('w')

            # Atualize a legenda discreta
            self._update_colorbar_discrete()

            self.ui_manager.mostrar_mensagem(self.ui_manager.tr("Renderização da malha DAE concluída com sucesso."), "Sucesso")

        except Exception as e:
            self.ui_manager.mostrar_mensagem(self.ui_manager.tr("Erro ao carregar/processar o DAE: {error}").format(error=e), "Erro")

    def _construir_indice_arestas(self):
        """
        Constrói a relação entre cada aresta e as faces que a utilizam.

        A chave da aresta sempre é armazenada na ordem crescente:

            (menor_indice, maior_indice)

        Exemplos:
            [face]     -> aresta de contorno
            [face1, face2] -> aresta interna válida para análise
        """
        self._indice_arestas = {}

        if self._faces_editadas is None:
            return

        faces = np.asarray(self._faces_editadas, dtype=np.int32)

        for face_id, face in enumerate(faces):
            if len(face) != 3:
                continue

            v0, v1, v2 = map(int, face)

            arestas_face = ((v0, v1), (v1, v2), (v2, v0))

            for vertice_a, vertice_b in arestas_face:
                chave = tuple(sorted((vertice_a, vertice_b)))

                self._indice_arestas.setdefault(chave, []).append(face_id)

    def _aresta_pode_ser_invertida(self, aresta):
        """
        Informa se a aresta pode ser realmente invertida,
        utilizando as mesmas validações geométricas usadas
        durante a edição.
        """
        if aresta is None:
            return False

        if self._faces_editadas is None:
            return False

        chave = tuple(sorted(map(int, aresta)))

        faces_vizinhas = list(self._indice_arestas.get(chave, []))

        # Uma diagonal editável precisa pertencer
        # exatamente a duas faces.
        if len(faces_vizinhas) != 2:
            return False

        face_id_1, face_id_2 = map(int, faces_vizinhas)
        face_1 = np.asarray(self._faces_editadas[face_id_1], dtype=np.int32)
        face_2 = np.asarray(self._faces_editadas[face_id_2], dtype=np.int32)

        opostos_1 = [int(v)
            for v in face_1
            if int(v) not in chave]

        opostos_2 = [int(v)
            for v in face_2
            if int(v) not in chave]

        if (len(opostos_1) != 1
            or len(opostos_2) != 1):

            return False

        valido, _ = (self._validar_inversao_aresta(chave, opostos_1[0], opostos_2[0]))

        return bool(valido)

    def _on_rampa_cores_alterada(self, index):
        """
        Atualiza as cores da visualização e habilita a aplicação
        da nova simbologia em uma camada adicionada ao mapa.
        """
        self.atualizar_malha_com_faixas()
        self.malha_modificada = True

        if hasattr(self, "pushButtonAdicionarMapa"):
            self.pushButtonAdicionarMapa.setEnabled(True)

    def atualizar_malha_com_faixas(self):
        """
        Atualiza a malha 3D com novas cores baseadas no número de faixas (slider) e
        na opção de inverter gradiente (checkbox).

        Fluxo principal:
        1. Verifica se existe `mesh_data` carregada.
        2. Lê valores de Z dos vértices da malha.
        3. Gera um conjunto de cores discretas (gradiente com faixas).
        4. Aplica essas cores diretamente na `mesh_data` (ou recria um `MeshData`).
        5. Remove o item antigo da cena e adiciona um novo com as cores atualizadas.
        6. Recoloca eixos XYZ, se estiverem habilitados.
        """
        if self.mesh_data is None:
            return  # não há malha carregada

        # 1) Captura parâmetros da interface
        inverter_cores = self.checkbox_inverter_cores.isChecked()
        num_faixas     = self.slider_faixas.value()

        try:
            # 2) Lê Z para colorir -> Z ORIGINAL, se disponível
            if hasattr(self, "_z_raw") and self._z_raw is not None:
                z_values = self._z_raw
            else:
                z_values = self.mesh_data.vertexes()[:, 2]  # fallback

            # 3) Gera as cores
            new_colors = self.criar_simbologia_gradiente_discreta(z_values, num_faixas, inverter_cores).astype(float)

            # Normaliza se vier em escala 0–255
            if new_colors.max() > 1.0:
                new_colors = new_colors / 255.0

            self._vertex_colors = new_colors.copy()

        except Exception as e:
            self.ui_manager.mostrar_mensagem(self.ui_manager.tr("Erro ao recalcular cores: {error}").format(error=e), "Erro")
            return

        # 4) Aplica cores na malha (se não suportar, recria MeshData)
        try:
            self.mesh_data.setVertexColors(new_colors)
            recreate_meshdata = False
        except Exception:
            recreate_meshdata = True

        if recreate_meshdata:
            try:
                vertices_np = self.mesh_data.vertexes().copy()

                # Usa sempre as faces editadas, quando já estiverem disponíveis.
                # Isso evita perder futuras alterações de diagonais ao mudar as cores.
                if (hasattr(self, "_faces_editadas")
                    and self._faces_editadas is not None):
                    faces_render = self._faces_editadas.copy()
                else:
                    faces_render = self.mesh_data.faces().copy()

                new_md = gl.MeshData(
                    vertexes=vertices_np,
                    faces=faces_render,
                    vertexColors=new_colors)
                try:
                    _ = new_md.vertexNormals()
                except Exception:
                    pass  # nosec B110
                self.mesh_data = new_md
            except Exception as e:
                self.ui_manager.mostrar_mensagem(self.ui_manager.tr("Erro ao recriar MeshData: {error}").format(error=e), "Erro")
                return

        # 5) Recria o GLMeshItem com as novas cores
        try:
            if self.mesh_item is not None:
                self.view.removeItem(self.mesh_item)

            edge = (0.1, 0.1, 0.1, 1.0) if self.radio_white.isChecked() else (0.9, 0.9, 0.9, 1.0)

            self.mesh_item = GLMeshItemComEspessura(
                meshdata=self.mesh_data,
                smooth=False,
                drawEdges=self.checkbox_edges.isChecked(),
                edgeColor=edge,
                edgeWidth=self._espessura_arestas(),
                shader=self._get_phong_rim_shader(),
                glOptions="opaque")

            self.mesh_item.scale(10, 10, 10)
            self.view.addItem(self.mesh_item)

            # depois de redesenhar:
            self.view.update()
            self._update_colorbar_discrete()

        except Exception as e:
            self.ui_manager.mostrar_mensagem(self.ui_manager.tr("Erro ao atualizar a malha: {error}").format(error=e), "Erro")

    def _update_colorbar(self):
        """Sincroniza a barra de cores com Zmin/Zmax atuais e as faixas/ordem."""
        if self.mesh_data is None:
            return
        V = self.mesh_data.vertexes()
        zmin = float(np.min(V[:,2]))
        zmax = float(np.max(V[:,2]))
        num = self.slider_faixas.value()
        inv = self.checkbox_inverter_cores.isChecked()
        bands = self._band_colors_from_settings(num, inv)
        self.colorbar.update_scale(zmin, zmax, bands)

    def _fmt_br(self, v, dec=2):
        # formata 12.3456 -> "12,35"
        return f"{v:.{dec}f}".replace('.', ',')

    def _legend_edges_labels(self, zmin, zmax, n, inverter=False, dec=2):
        """
        Gera N rótulos SEM inverter a ordem:
          n=1   →  ["zmin - zmax"]
          n=2   →  ["<= e1", "> e1"]
          n>=3  →  ["<= e1", "e1 - e2-ε", ..., "> e(N-1)-ε"]
        """
        if n < 1:
            return [], []

        edges = np.linspace(zmin, zmax, n + 1)   # e0..eN
        eps   = 10 ** (-dec)

        if n == 1:
            labels = [f"{self._fmt_br(zmin, dec)} - {self._fmt_br(zmax, dec)}"]
            return edges, labels

        labels = []
        labels.append(f"<= {self._fmt_br(edges[1], dec)}")  # primeira faixa (baixa)

        if n == 2:
            labels.append(f"> {self._fmt_br(edges[1], dec)}")  # segunda (alta)
        else:
            for k in range(1, n - 1):
                lo = self._fmt_br(edges[k], dec)
                hi = self._fmt_br(edges[k + 1] - eps, dec)
                labels.append(f"{lo} - {hi}")
            labels.append(f"> {self._fmt_br(edges[-2] - eps, dec)}")  # última (alta)

        return edges, labels

    def _update_colorbar_discrete(self):
        """Atualiza a barra com rótulos por faixa usando Z ORIGINAL."""
        if not hasattr(self, "_z_raw") or self._z_raw is None:
            return

        zmin = float(self._z_raw.min())
        zmax = float(self._z_raw.max())
        inv  = self.checkbox_inverter_cores.isChecked()

        bands = self._band_colors_from_settings(self.slider_faixas.value(), inv)  # cores já invertidas quando preciso
        n     = len(bands)

        # rótulos SEM inversão (ordem baixa → alta)
        _, labels = self._legend_edges_labels(zmin, zmax, n, inverter=False, dec=2)

        if hasattr(self, "colorbar") and self.colorbar is not None:
            self.colorbar.update_discrete(labels, bands)

    def _band_colors_from_settings(self, num_faixas: int, inverter: bool):
        """
        Retorna as cores discretas da rampa selecionada.

        A rampa é interpolada para produzir exatamente o número
        de faixas definido no slider ou no spinbox.
        """
        num_faixas = max(1, int(num_faixas))

        # Recupera as rampas configuradas anteriormente.
        rampas = getattr(self, "_rampas_cores", None)

        if not rampas:
            rampas = self._definicoes_rampas_cores()
            self._rampas_cores = rampas

        # Nome selecionado no ComboBox.
        nome_rampa = "Classic"

        if hasattr(self, "Comboboxrampa"):
            nome_selecionado = (self.Comboboxrampa.currentText().strip())

            if nome_selecionado:
                nome_rampa = nome_selecionado

        # Usa Classic como segurança caso o nome não exista.
        cores_origem = rampas.get(nome_rampa, rampas.get("Classic", ()))

        if not cores_origem:
            cores_origem = (
                "#ff0000",
                "#ff4d00",
                "#ff8000",
                "#ffbf00",
                "#ffff00",
                "#80ff00",
                "#00ff00",
                "#00ff80",
                "#0080ff",
                "#0000cc")

        # Converte hexadecimal para RGBA normalizado entre 0 e 1.
        cores_rgba = []

        for codigo_cor in cores_origem:
            cor = QColor(codigo_cor)

            if not cor.isValid():
                continue

            vermelho, verde, azul, alfa = cor.getRgbF()

            cores_rgba.append((
                float(vermelho),
                float(verde),
                float(azul),
                float(alfa)))

        # Segurança para uma eventual rampa inválida.
        if not cores_rgba:
            cores_rgba = [(0.5, 0.5, 0.5, 1.0)]

        # A inversão ocorre antes da interpolação.
        # Assim, uma única faixa também troca de extremidade.
        if inverter:
            cores_rgba.reverse()

        # Uma rampa contendo somente uma cor.
        if len(cores_rgba) == 1:
            return [cores_rgba[0]
                for _ in range(num_faixas)]

        matriz_cores = np.asarray(cores_rgba, dtype=float)

        posicoes_origem = np.linspace(0.0, 1.0, len(cores_rgba))

        posicoes_saida = np.linspace(0.0, 1.0, num_faixas)

        bandas = []

        for posicao in posicoes_saida:
            rgba = tuple(
                float(np.interp(
                        posicao,
                        posicoes_origem,
                        matriz_cores[:, canal] ))
                for canal in range(4))

            bandas.append(rgba)

        return bandas

    def closeEvent(self, e):
        try:
            if getattr(self, "mesh_item", None) is not None:
                self.view.removeItem(self.mesh_item)
                self.mesh_item = None
            if getattr(self, "_axes", None) is not None:
                self.view.removeItem(self._axes)
                self._axes = None
        except Exception:
            pass  # nosec B110
        super().closeEvent(e)

class PannableGLViewWidget(gl.GLViewWidget):
    """
    Viewer 3D com:
      - Pan no botão direito (RMB), colado ao cursor, mesmo sentido do arrasto.
      - Rotação no botão esquerdo (LMB) mais SUAVE (sensibilidade menor + leve amortecimento).
    Ajustes finos:
      - self._sens       → sensibilidade do PAN (menor = mais lento)
      - self._rot_sens   → sensibilidade da ROTAÇÃO (deg por device-pixel; menor = mais lento)
      - self._rot_alpha  → suavização da rotação (0.1–0.3 = suave; 1.0 = sem suavização)
    """
    mouseMoved3D = pyqtSignal(QPointF)
    mouseLeft3D = pyqtSignal()
    ctrlCliqueEsquerdo3D = pyqtSignal()
    desfazerEdicao3D = pyqtSignal()
    refazerEdicao3D = pyqtSignal()

    falhaOpenGL = pyqtSignal(str)

    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)

        # Evita repetir a mesma falha OpenGL a cada tentativa
        # de repintura do widget.
        self._falha_opengl_reportada = False

        self.setFocusPolicy(Qt.FocusPolicy.StrongFocus)
        self.setMouseTracking(True)
        self.setContextMenuPolicy(Qt.ContextMenuPolicy.NoContextMenu)

        # Eixo de orientação fixo no canto inferior esquerdo.
        self._corner_axis_visible = True
        self._corner_axis_size = 55.0
        self._corner_axis_margin = 28.0
        self._corner_axis_line_width = 3.0

        # PAN (RMB)
        self._panning = False
        self._lastPosPan = None

        # Sensibilidade básica do arraste.
        self._sens = 0.15

        # Compensação aplicada quando a câmera está muito próxima.
        # Evita que o deslocamento fique excessivamente lento com zoom alto.
        self._pan_zoom_boost = 2.5

        # Limita a compensação para não deixar o movimento brusco.
        self._pan_zoom_boost_max = 5.0

        # ROT (LMB)
        self._rotating    = False
        self._lastPosRot  = None
        self._rot_sx      = 0.0    # acumuladores p/ filtro (rotação)
        self._rot_sy      = 0.0
        self._rot_alpha   = 0.25   # suavização da rotação (0.1–0.3 deixa "mais suave")
        self._rot_sens    = 0.35   # deg por device-pixel (padrão do pyqtgraph ~0.5)

        # Cursor usado quando nenhum botão do mouse está pressionado.
        # No modo normal será uma mão; no modo de edição será uma cruz.
        self._cursor_reposo = Qt.CursorShape.OpenHandCursor

        try:
            self.setCursor(self._cursor_reposo)
        except Exception:
            pass  # nosec B110

        # Indica se o widget está no modo de edição de arestas
        self._modo_edicao_arestas = False


        # Permite receber diretamente os eventos de teclado
        self.setFocusPolicy(Qt.FocusPolicy.StrongFocus)

        # Cursores usados durante a edição de arestas
        self._cursor_edicao_normal = QCursor(Qt.CursorShape.CrossCursor)

        self._cursor_edicao_ctrl = (self._criar_cursor_circulo_cruz())

        # Slider vertical sobreposto para controle do zoom.
        self.zoom_slider = HoverZoomSlider(self)

        # Altura visual do controle.
        self.zoom_slider.resize(24, 150)

        self.zoom_slider.setToolTip(QCoreApplication.translate("PannableGLViewWidget", "Aproxime ou afaste a visualização"))

        self.zoom_slider.valueChanged.connect(
            self._aplicar_zoom_slider)

        # Evita que o slider receba foco permanente pelo teclado.
        self.zoom_slider.setFocusPolicy(Qt.FocusPolicy.NoFocus)

        self.zoom_slider.show()

        # Distância correspondente ao centro do slider.
        # Será atualizada quando a malha for enquadrada.
        self._zoom_center_distance = 1000.0

        # Limites relativos ao enquadramento padrão.
        # Permite inspeção muito próxima sem usar distâncias fixas.
        self._zoom_min_ratio = 0.002
        self._zoom_max_ratio = 8.0

        # Distância mínima absoluta de segurança.
        self._zoom_min_absoluto = 0.0001

        # Vértices da malha usados exclusivamente para impedir
        # que a câmera atravesse a superfície durante o zoom.
        self._vertices_limite_zoom = None

        # Pequena folga entre a câmera e a parte mais próxima
        # da malha.
        self._margem_limite_zoom = 0.0

    def resizeEvent(self, event):
        """
        Reposiciona os controles sobrepostos quando a view muda de tamanho.
        """
        super().resizeEvent(event)

        self._reposicionar_zoom_slider()

    def _reposicionar_zoom_slider(self):
        """
        Mantém o slider no canto inferior direito da área 3D.
        """
        if not hasattr(self, "zoom_slider"):
            return

        largura = 24

        # Slider mais curto e discreto.
        altura = min(165, max(115, int(self.height() * 0.19)))

        self.zoom_slider.resize(largura, altura)

        margem_direita = 14
        margem_inferior = 22

        x = (self.width()
            - largura
            - margem_direita)

        y = (self.height()
            - altura
            - margem_inferior)

        self.zoom_slider.move(max(0, x), max(0, y))

        self.zoom_slider.raise_()

    def _aplicar_zoom_slider(self, valor):
        """
        Aplica zoom exponencial relativo ao enquadramento da malha.

        Valor 50:
            enquadramento original.

        Valores acima de 50:
            aproximação progressivamente mais detalhada.

        Valores abaixo de 50:
            afastamento progressivo.
        """
        try:
            distancia_central = max(self._zoom_min_absoluto, float(self._zoom_center_distance))

            valor_minimo = float(
                self.zoom_slider.minimum())

            valor_maximo = float(self.zoom_slider.maximum())
            valor_central = 50.0

            distancia_minima = (self._distancia_minima_zoom_malha())
            distancia_maxima = (distancia_central * self._zoom_max_ratio)

            valor = float(valor)

            if valor >= valor_central:
                # Metade superior:
                # enquadramento padrão → aproximação máxima.
                faixa = max(1.0, valor_maximo - valor_central)

                proporcao = (valor - valor_central) / faixa
                distancia = (distancia_central * (distancia_minima / distancia_central) ** proporcao)

            else:
                # Metade inferior:
                # enquadramento padrão → afastamento máximo.
                faixa = max(1.0, valor_central - valor_minimo)

                proporcao = (valor_central - valor) / faixa
                distancia = (distancia_central * (distancia_maxima / distancia_central) ** proporcao)

            distancia = max(distancia_minima, min(distancia_maxima, distancia))

            self.setCameraPosition(distance=distancia)

            self.update()

        except Exception:
            pass  # nosec B110

    def definir_limite_zoom_malha(self, vertices):
        """
        Registra os vértices da malha na escala visual utilizada
        pelo OpenGL para impedir que a câmera atravesse a superfície.
        """
        try:
            vertices = np.asarray(
                vertices,
                dtype=np.float64)

            if (vertices.ndim != 2
                or vertices.shape[0] == 0
                or vertices.shape[1] < 3):

                self._vertices_limite_zoom = None
                self._margem_limite_zoom = 0.0
                return

            vertices = vertices[:, :3]

            mascara = np.all(np.isfinite(vertices), axis=1)

            vertices = vertices[mascara]

            if len(vertices) == 0:
                self._vertices_limite_zoom = None
                self._margem_limite_zoom = 0.0
                return

            self._vertices_limite_zoom = vertices.copy()

            dimensoes = np.ptp(vertices, axis=0)

            diagonal = float(np.linalg.norm(dimensoes))

            # Folga de 0,2% da diagonal visual da malha.
            self._margem_limite_zoom = max(diagonal * 0.01, 0.001)

        except Exception:
            self._vertices_limite_zoom = None
            self._margem_limite_zoom = 0.0

    def _distancia_minima_zoom_malha(self):
        """
        Calcula a menor distância permitida para a câmera
        na direção atual da visualização.

        A câmera permanece à frente de toda a malha,
        evitando atravessar a superfície durante o zoom.
        """
        distancia_basica = max(self._zoom_min_absoluto,
            float(self._zoom_center_distance)
            * self._zoom_min_ratio)

        vertices = self._vertices_limite_zoom

        if vertices is None or len(vertices) == 0:
            return distancia_basica

        try:
            centro_qt = self.opts["center"]

            centro = np.array(
                [float(centro_qt.x()),
                    float(centro_qt.y()),
                    float(centro_qt.z())],
                dtype=np.float64)

            camera_qt = self.cameraPosition()

            camera = np.array(
                [float(camera_qt.x()),
                    float(camera_qt.y()),
                    float(camera_qt.z())],
                dtype=np.float64)

            vetor_camera = (camera - centro)
            comprimento = float(np.linalg.norm(vetor_camera))

            if comprimento <= 1e-12:
                return distancia_basica

            direcao_camera = (vetor_camera / comprimento)

            # Quanto cada vértice avança na direção da câmera.
            projecoes = ((vertices - centro)
                @ direcao_camera)

            projecoes = projecoes[np.isfinite(projecoes)]

            if projecoes.size == 0:
                return distancia_basica

            ponto_mais_frontal = float(np.max(projecoes))
            limite_geometrico = (ponto_mais_frontal + self._margem_limite_zoom)

            return max(distancia_basica, limite_geometrico)

        except Exception:
            return distancia_basica

    def sincronizar_slider_com_camera(self):
        """
        Sincroniza o slider com a distância atual da câmera.
        """
        if not hasattr(self, "zoom_slider"):
            return

        try:
            distancia_central = max(self._zoom_min_absoluto, float(self._zoom_center_distance))

            distancia = max(self._zoom_min_absoluto, float(self.opts.get( "distance", distancia_central)))

            distancia_minima = (self._distancia_minima_zoom_malha())
            distancia_maxima = (distancia_central * self._zoom_max_ratio)

            minimo_slider = float(self.zoom_slider.minimum())
            maximo_slider = float(self.zoom_slider.maximum())

            centro_slider = 50.0

            if distancia <= distancia_central:
                denominador = math.log(distancia_minima / distancia_central)

                if abs(denominador) < 1e-12:
                    proporcao = 0.0
                else:
                    proporcao = math.log(distancia / distancia_central) / denominador

                proporcao = max(0.0, min(1.0, proporcao))

                valor = (centro_slider + proporcao * (maximo_slider - centro_slider))

            else:
                denominador = math.log(distancia_maxima / distancia_central)

                if abs(denominador) < 1e-12:
                    proporcao = 0.0
                else:
                    proporcao = math.log(distancia / distancia_central) / denominador

                proporcao = max(0.0, min(1.0, proporcao))

                valor = (centro_slider - proporcao * (centro_slider - minimo_slider))

            self.zoom_slider.blockSignals(True)

            try:
                self.zoom_slider.setValue(int(round(valor)))
            finally:
                self.zoom_slider.blockSignals(False)

        except Exception:
            pass  # nosec B110

    def definir_zoom_central(self, distancia):
        """
        Define a distância de enquadramento correspondente
        ao centro do slider.
        """
        try:
            distancia = float(distancia)
        except Exception:
            return

        if not math.isfinite(distancia) or distancia <= 0:
            return

        self._zoom_center_distance = distancia

        self.zoom_slider.blockSignals(True)

        try:
            self.zoom_slider.setValue(50)
        finally:
            self.zoom_slider.blockSignals(False)

        self.setCameraPosition(
            distance=distancia)

        self.update()

    def _effective_dpr(self) -> float:
        try:
            return float(self.devicePixelRatioF())
        except Exception:
            return 1.0

    def _px_to_world_scale(self) -> float:
        """
        Converte um pixel do dispositivo em unidades do mundo para o PAN.

        A escala acompanha a distância da câmera, mas recebe uma
        compensação progressiva quando o zoom está muito próximo,
        evitando que o arraste fique excessivamente lento.
        """
        try:
            distancia = max(0.000001, float(self.opts.get("distance", 200.0)))

            distancia_central = max(0.000001, float(getattr(self, "_zoom_center_distance", distancia)))

            fov_graus = float(self.opts.get("fov", 60.0))

            fov_radianos = np.deg2rad(fov_graus)

            altura = max(1, self.height())

            dpr = self._effective_dpr()

            altura_efetiva = max(1.0, altura * dpr)

            altura_mundo_visivel = (2.0 * distancia * np.tan(fov_radianos * 0.5))

            escala_base = (altura_mundo_visivel / altura_efetiva) * self._sens

            # Relação maior que 1 indica que a câmera está mais próxima
            # do que o enquadramento central da malha.
            relacao_zoom = (distancia_central / distancia)

            if relacao_zoom > 1.0:
                # Crescimento suavizado pela raiz quadrada.
                # Não explode quando o zoom fica muito próximo.
                compensacao = (1.0 + (math.sqrt(relacao_zoom) - 1.0) * self._pan_zoom_boost)

                compensacao = min(compensacao, self._pan_zoom_boost_max)
            else:
                compensacao = 1.0

            return (escala_base * compensacao)

        except Exception:
            return self._sens

    def set_corner_axis_visible(self, visible: bool):
        """
        Exibe ou oculta o eixo XYZ de orientação no canto do visualizador.
        """
        self._corner_axis_visible = bool(visible)
        self.update()

    def _project_axis_to_screen(self, axis: QVector3D):
        """
        Transforma um vetor do mundo usando apenas a rotação atual da câmera
        e retorna sua direção projetada na tela.
        """
        try:
            matriz = self.viewMatrix()

            # mapVector ignora a translação e considera somente orientação/escala.
            vetor_camera = matriz.mapVector(axis)

            x = float(vetor_camera.x())
            y = float(vetor_camera.y())

            comprimento = math.hypot(x, y)

            if comprimento < 1e-9:
                return QPointF(0.0, 0.0)

            return QPointF(x / comprimento, -y / comprimento)

        except Exception:
            return QPointF(0.0, 0.0)

    def _draw_corner_axis(self, painter: QPainter):
        """
        Desenha um eixo XYZ fixo no canto inferior esquerdo.

        O eixo não acompanha o pan ou o zoom. Ele acompanha somente
        a rotação da câmera.
        """
        if not self._corner_axis_visible:
            return

        tamanho = float(self._corner_axis_size)
        margem = float(self._corner_axis_margin)

        origem = QPointF(margem + tamanho, self.height() - margem - tamanho)

        eixos = (
            ("X", QVector3D(1.0, 0.0, 0.0), QColor(220, 45, 45)),
            ("Y", QVector3D(0.0, 1.0, 0.0), QColor(35, 170, 70)),
            ("Z", QVector3D(0.0, 0.0, 1.0), QColor(40, 100, 230)))

        painter.save()
        painter.setRenderHint(QPainter.RenderHint.Antialiasing, True)

        # Fundo discreto para o eixo permanecer legível.
        raio_fundo = tamanho + 17.0

        painter.setPen(QPen(QColor(80, 80, 80, 100), 1.0))

        painter.setBrush(QColor(255, 255, 255, 185))

        painter.drawEllipse(origem, raio_fundo, raio_fundo)

        fonte = painter.font()
        fonte.setBold(True)
        fonte.setPointSize(9)
        painter.setFont(fonte)

        for texto, vetor, cor in eixos:
            direcao = self._project_axis_to_screen(vetor)

            fim = QPointF(
                origem.x() + direcao.x() * tamanho,
                origem.y() + direcao.y() * tamanho)

            pen = QPen(cor, self._corner_axis_line_width)

            pen.setCapStyle(Qt.PenCapStyle.RoundCap)

            painter.setPen(pen)
            painter.drawLine(origem, fim)

            # Ponta da seta.
            dx = fim.x() - origem.x()
            dy = fim.y() - origem.y()
            angulo = math.atan2(dy, dx)

            tamanho_seta = 8.0
            abertura = math.radians(28.0)

            p1 = QPointF(
                fim.x() - tamanho_seta * math.cos(angulo - abertura),
                fim.y() - tamanho_seta * math.sin(angulo - abertura))

            p2 = QPointF(
                fim.x() - tamanho_seta * math.cos(angulo + abertura),
                fim.y() - tamanho_seta * math.sin(angulo + abertura))

            painter.drawLine(fim, p1)
            painter.drawLine(fim, p2)

            # Identificação X, Y ou Z.
            painter.setPen(QPen(cor, 1.0))

            deslocamento_texto = 12.0

            pos_texto = QPointF(
                fim.x() + direcao.x() * deslocamento_texto - 4.0,
                fim.y() + direcao.y() * deslocamento_texto + 5.0)

            painter.drawText(pos_texto, texto)

        # Pequeno círculo na origem.
        painter.setPen(
            QPen(QColor(40, 40, 40), 1.0))

        painter.setBrush(QColor(40, 40, 40))

        painter.drawEllipse(origem, 3.0, 3.0)

        painter.restore()

    def _coletar_diagnostico_opengl(self, erro=None):
        """
        Coleta informações do contexto OpenGL para ajudar
        a identificar incompatibilidades de GPU ou driver.
        """
        linhas = []

        contexto = self.context()

        if contexto is None:
            linhas.append("Contexto OpenGL: não disponível")

        else:
            linhas.append("Contexto OpenGL válido: "
                + ("Sim" if contexto.isValid() else "Não"))

            try:
                formato = contexto.format()

                linhas.append(
                    "Versão do contexto: "
                    f"{formato.majorVersion()}."
                    f"{formato.minorVersion()}")

                linhas.append(f"Perfil: {formato.profile()}")

                linhas.append(f"Tipo de renderização: "
                    f"{formato.renderableType()}")

            except Exception as e:
                linhas.append(
                    f"Informações do contexto: "
                    f"não disponíveis ({e})")

        def texto_gl(valor):
            if valor is None:
                return "Não disponível"

            if isinstance(valor, bytes):
                return valor.decode("utf-8", errors="replace")

            return str(valor)

        if (contexto is not None
            and contexto.isValid()):

            try:
                linhas.append("Fabricante da GPU: "
                    + texto_gl(GL.glGetString(GL.GL_VENDOR)))

            except Exception:
                linhas.append("Fabricante da GPU: não disponível")

            try:
                linhas.append("Renderizador: "
                    + texto_gl(GL.glGetString(GL.GL_RENDERER)))

            except Exception:
                linhas.append("Renderizador: não disponível")

            try:
                linhas.append("Versão OpenGL: "
                    + texto_gl(GL.glGetString(GL.GL_VERSION)))

            except Exception:
                linhas.append("Versão OpenGL: não disponível")

            try:
                linhas.append("Versão GLSL: "
                    + texto_gl(GL.glGetString(GL.GL_SHADING_LANGUAGE_VERSION)))

            except Exception:
                linhas.append("Versão GLSL: não disponível")

        if erro is not None:
            linhas.append("")
            linhas.append(f"Erro OpenGL: {erro}")

        return "\n".join(linhas)

    def _registrar_falha_opengl(self, erro):
        """
        Registra a primeira falha OpenGL e envia o diagnóstico
        para a janela principal do visualizador.
        """
        if self._falha_opengl_reportada:
            return

        self._falha_opengl_reportada = True

        diagnostico = (self._coletar_diagnostico_opengl(erro))

        # O aviso não deve ser aberto diretamente durante paintGL,
        # pois isso poderia causar uma nova renderização recursiva.
        QTimer.singleShot(0,
            lambda texto=diagnostico:
                self.falhaOpenGL.emit(texto))

    def paintGL(self, *args, **kwargs):
        """
        Renderiza a cena OpenGL e captura falhas de
        compatibilidade do contexto gráfico.
        """
        if self._falha_opengl_reportada:
            return

        contexto = self.context()

        if (contexto is None
            or not contexto.isValid()):

            self._registrar_falha_opengl("O contexto OpenGL não pôde ser criado ou não é válido.")

            return

        try:
            super().paintGL(*args, **kwargs)

        except GLError as e:
            self._registrar_falha_opengl(e)
            return

        if not self._corner_axis_visible:
            return

        painter = QPainter(self)

        try:
            self._draw_corner_axis(painter)

        finally:
            painter.end()

    def definir_cursor_reposo(self, cursor):
        """
        Define o cursor que deve voltar após terminar
        uma operação de pan ou rotação.
        """
        self._cursor_reposo = cursor

        # Só altera imediatamente quando não há operação ativa.
        if not self._panning and not self._rotating:
            try:
                self.setCursor(self._cursor_reposo)
            except Exception:
                pass  # nosec B110

    def definir_modo_edicao_arestas(self, habilitado):
        """
        Ativa ou desativa o modo de edição de arestas.
        """
        self._modo_edicao_arestas = bool(habilitado)

        if self._modo_edicao_arestas:
            self._atualizar_cursor_edicao()
            self.setFocus(Qt.FocusReason.MouseFocusReason)
        else:
            self.definir_cursor_reposo(Qt.CursorShape.OpenHandCursor)

            try:
                self.setCursor(self._cursor_reposo)
            except Exception:
                pass  # nosec B110

    def _criar_cursor_circulo_cruz(self):
        """
        Cria um cursor formado por um círculo com uma cruz
        exatamente centralizada.

        O ponto ativo do cursor fica no centro da cruz.
        """
        tamanho = 32
        centro = tamanho // 2
        raio = 8

        pixmap = QPixmap(tamanho, tamanho)
        pixmap.fill(Qt.GlobalColor.transparent)

        painter = QPainter(pixmap)

        try:
            painter.setRenderHint(QPainter.RenderHint.Antialiasing, True)

            # Contorno branco externo para melhorar a leitura
            # sobre superfícies escuras.
            caneta_externa = QPen(QColor(255, 255, 255, 235))
            caneta_externa.setWidth(4)

            painter.setPen(caneta_externa)
            painter.setBrush(Qt.BrushStyle.NoBrush)

            painter.drawEllipse(QPoint(centro, centro), raio, raio)

            painter.drawLine(centro - 5, centro, centro + 5, centro)

            painter.drawLine(centro, centro - 5, centro, centro + 5)

            # Traço escuro interno.
            caneta_interna = QPen(QColor(25, 25, 25, 255))
            caneta_interna.setWidth(2)

            painter.setPen(caneta_interna)

            painter.drawEllipse(QPoint(centro, centro), raio,  raio)

            painter.drawLine(centro - 5, centro, centro + 5, centro)

            painter.drawLine(centro, centro - 5, centro, centro + 5)

        finally:
            painter.end()

        # Hotspot exatamente no centro do "+"
        return QCursor(pixmap, centro, centro)

    def _atualizar_cursor_edicao(self):
        """
        Atualiza o cursor conforme o modo de edição
        e o estado da tecla Ctrl.
        """
        if not self._modo_edicao_arestas:
            return

        modificadores = (QApplication.keyboardModifiers())

        ctrl_ativo = bool(modificadores
            & Qt.KeyboardModifier.ControlModifier)

        try:
            if ctrl_ativo:
                self.setCursor(self._cursor_edicao_ctrl)
            else:
                self.setCursor(self._cursor_edicao_normal)
        except Exception:
            pass  # nosec B110

    def leaveEvent(self, event):
        """
        Informa que o cursor saiu da área do visualizador.
        """
        self.mouseLeft3D.emit()
        super().leaveEvent(event)

    def wheelEvent(self, ev):
        """
        Aplica zoom direcionado para a posição do cursor.

        Ao aproximar ou afastar, desloca o centro da câmera
        para manter aproximadamente o ponto sob o mouse
        na mesma posição da tela.
        """
        delta = ev.angleDelta().x()

        if delta == 0:
            delta = ev.angleDelta().y()

        if delta == 0:
            ev.ignore()
            return

        # Mantém o comportamento original do pyqtgraph para
        # Ctrl + roda, que altera o campo de visão.
        if (ev.modifiers()
            & Qt.KeyboardModifier.ControlModifier):

            super().wheelEvent(ev)
            return

        distancia_atual = max(
            self._zoom_min_absoluto,
            float(self.opts.get("distance", self._zoom_center_distance)))

        # Mesmo fator utilizado pelo GLViewWidget original.
        fator_zoom = 0.999 ** delta

        nova_distancia = (distancia_atual * fator_zoom)

        # Respeita os mesmos limites utilizados
        # pelo slider de zoom.
        distancia_central = max(self._zoom_min_absoluto,
            float(self._zoom_center_distance))

        distancia_minima = max(self._zoom_min_absoluto, distancia_central * self._zoom_min_ratio)

        distancia_maxima = (distancia_central * self._zoom_max_ratio)
        nova_distancia = max(distancia_minima, min(distancia_maxima, nova_distancia))

        if math.isclose(
            distancia_atual,
            nova_distancia,
            rel_tol=1e-12,
            abs_tol=1e-12):

            ev.accept()
            return

        # Posição do cursor dentro do visualizador.
        try:
            pos = ev.position()
        except AttributeError:
            pos = ev.pos()

        largura = max(1.0, float(self.width()))
        altura = max(1.0, float(self.height()))

        # Distância do cursor ao centro da tela,
        # expressa em pixels da própria view.
        dx_cursor = (float(pos.x()) - largura * 0.5)

        # No sistema da tela Y cresce para baixo.
        # No plano da câmera +Y aponta para cima.
        dy_cursor = (altura * 0.5 - float(pos.y()))

        # Razão entre a nova distância
        # e a distância anterior.
        razao = (nova_distancia / distancia_atual)

        # Primeiro aplica a nova distância.
        self.opts["distance"] = (nova_distancia)

        # Como pan(relative="view") trabalha no plano da câmera,
        # deslocamos o centro na quantidade necessária para que
        # a posição sob o mouse permaneça aproximadamente fixa.
        if razao > 1e-12:
            correcao = ((1.0 - razao) / razao)

            dx_pan = -dx_cursor * correcao
            dy_pan = dy_cursor * correcao

            try:
                self.pan(dx_pan, dy_pan, 0.0, relative="view")

            except TypeError:
                self.pan(dx_pan, dy_pan, 0.0)

        distancia_minima = (self._distancia_minima_zoom_malha())
        distancia_atual = float(self.opts.get("distance", self._zoom_center_distance))

        if distancia_atual < distancia_minima:
            self.opts["distance"] = distancia_minima
            self.update()

        # Mantém o slider lateral coerente com o zoom feito pela roda.
        self.sincronizar_slider_com_camera()

        self.update()
        ev.accept()

    def mousePressEvent(self, ev):
        """
        Controles:
        - Botão esquerdo: rotação
        - Botão direito: deslocamento
        - Ctrl + botão esquerdo: inverter aresta
        """
        modificadores = ev.modifiers()

        # Ctrl + clique esquerdo para editar a aresta
        if (self._modo_edicao_arestas
            and ev.button() == Qt.MouseButton.LeftButton
            and (modificadores
                & Qt.KeyboardModifier.ControlModifier)):
            self.ctrlCliqueEsquerdo3D.emit()
            ev.accept()
            return

        # Botão direito: PAN
        if ev.button() == Qt.MouseButton.RightButton:
            self._panning = True
            self._lastPosPan = ev.pos()

            try:
                self.setCursor(Qt.CursorShape.ClosedHandCursor)
            except Exception:
                pass  # nosec B110

            ev.accept()
            return

        # Botão esquerdo normal: rotação
        if ev.button() == Qt.MouseButton.LeftButton:
            self._rotating = True
            self._lastPosRot = ev.pos()
            self._rot_sx = 0.0
            self._rot_sy = 0.0

            ev.accept()
            return

        super().mousePressEvent(ev)

    def mouseMoveEvent(self, ev):
        try:
            self.mouseMoved3D.emit(QPointF(ev.position()))
        except Exception:
            try:
                self.mouseMoved3D.emit(QPointF(ev.pos()))
            except Exception:
                pass  # nosec B110

        if (self._modo_edicao_arestas
            and not self._panning
            and not self._rotating):
            self._atualizar_cursor_edicao()

        # ROTAÇÃO (LMB)
        if self._rotating and self._lastPosRot is not None:
            raw = ev.pos() - self._lastPosRot
            self._lastPosRot = ev.pos()

            # converte para device px (corrige HiDPI)
            dpr = self._effective_dpr()
            dx = float(raw.x()) * dpr
            dy = float(raw.y()) * dpr

            # suavização leve (deixa "apenas mais suave")
            a = self._rot_alpha
            self._rot_sx = (1.0 - a) * self._rot_sx + a * dx
            self._rot_sy = (1.0 - a) * self._rot_sy + a * dy

            # limita picos de delta para evitar trancos
            max_px_step = 60.0
            sx = np.clip(self._rot_sx, -max_px_step, max_px_step)
            sy = np.clip(self._rot_sy, -max_px_step, max_px_step)

            # aplica rotação em GRAUS por device-pixel (mesma convenção do GLViewWidget):
            # → azim: -dx; elev: +dy
            self.orbit(-sx * self._rot_sens, sy * self._rot_sens)
            ev.accept()
            return

        # PAN (RMB)
        if self._panning and self._lastPosPan is not None:
            raw = ev.pos() - self._lastPosPan
            self._lastPosPan = ev.pos()

            # logical → device px
            dpr = self._effective_dpr()
            dx_px = float(raw.x()) * dpr
            dy_px = float(raw.y()) * dpr

            # px → mundo; mesmo sentido do mouse
            k = self._px_to_world_scale()
            dx_world =  dx_px * k      # direita → direita
            dy_world =  dy_px * k      # cima    → cima  (ajuste que você pediu)

            try:
                self.pan(dx_world, dy_world, 0.0, relative='view')
            except TypeError:
                self.pan(dx_world, dy_world, 0.0)

            ev.accept()
            return

        # sem pan/rot → padrão
        super().mouseMoveEvent(ev)

    def mouseReleaseEvent(self, ev):
        """
        Finaliza pan ou rotação e restaura o cursor
        adequado ao modo atual do visualizador.
        """
        if ev.button() == Qt.MouseButton.RightButton:
            self._panning = False
            self._lastPosPan = None

            try:
                self.setCursor(self._cursor_reposo)
            except Exception:
                pass  # nosec B110

            ev.accept()
            return

        if ev.button() == Qt.MouseButton.LeftButton:
            self._rotating = False
            self._lastPosRot = None

            try:
                self.setCursor(self._cursor_reposo)
            except Exception:
                pass  # nosec B110

            ev.accept()
            return

        super().mouseReleaseEvent(ev)

    def keyPressEvent(self, event):
        """
        Controla os atalhos de edição da malha.
        """
        if self._modo_edicao_arestas:

            modificadores = event.modifiers()

            # Ctrl + Z: desfazer
            if (event.key() == Qt.Key.Key_Z
                and (modificadores
                    & Qt.KeyboardModifier.ControlModifier)):
                self.desfazerEdicao3D.emit()
                event.accept()
                return

            # Ctrl + Y: refazer
            if (event.key() == Qt.Key.Key_Y
                and (modificadores
                    & Qt.KeyboardModifier.ControlModifier)):
                self.refazerEdicao3D.emit()
                event.accept()
                return

            # Ctrl pressionado: cursor circular com "+"
            if event.key() == Qt.Key.Key_Control:
                try:
                    self.setCursor(self._cursor_edicao_ctrl)
                except Exception:
                    pass  # nosec B110

                event.accept()
                return

        super().keyPressEvent(event)

    def keyReleaseEvent(self, event):
        """
        Ao soltar Ctrl, retorna imediatamente ao cursor '+'.
        """
        if (self._modo_edicao_arestas
            and event.key() == Qt.Key.Key_Control):
            try:
                self.setCursor(self._cursor_edicao_normal)
            except Exception:
                pass  # nosec B110

            event.accept()
            return

        super().keyReleaseEvent(event)

class HoverZoomSlider(QSlider):
    """
    Slider vertical de zoom sobreposto ao visualizador 3D.

    O valor central representa o enquadramento completo da malha.
    """
    def __init__(self, parent=None):
        super().__init__(
            Qt.Orientation.Vertical,
            parent)

        self.setMouseTracking(True)
        self.setCursor(
            Qt.CursorShape.PointingHandCursor)

        self.setRange(0, 100)

        # Posição neutra e central.
        self.setValue(50)

        self.setSingleStep(1)
        self.setPageStep(5)

        self.setTickPosition(
            QSlider.TickPosition.NoTicks)

        # Slider mais estreito.
        self.setFixedWidth(24)

        self._aplicar_estilo(
            destacado=False)

    def _aplicar_estilo(self, destacado=False):
        """
        Aplica transparência diferente no estado normal e no hover.
        """
        if destacado:
            fundo = "rgba(255, 255, 255, 205)"
            borda = "rgba(80, 80, 80, 190)"
            trilho = "rgba(75, 75, 75, 150)"
            controle = "rgba(45, 125, 220, 245)"
        else:
            fundo = "rgba(255, 255, 255, 20)"
            borda = "rgba(80, 80, 80, 30)"
            trilho = "rgba(75, 75, 75, 35)"
            controle = "rgba(45, 125, 220, 50)"

        self.setStyleSheet(f"""
            QSlider {{
                background-color: {fundo};
                border: 1px solid {borda};
                border-radius: 7px;
                padding: 5px;
            }}

            QSlider::groove:vertical {{
                background: {trilho};
                width: 3px;
                border-radius: 1px;
            }}

            QSlider::handle:vertical {{
                background: {controle};
                border: 1px solid rgba(30, 70, 130, 210);

                /* Retângulo horizontal arredondado */
                height: 9px;
                width: 16px;
                margin: -4px -6px;
                border-radius: 3px;
            }}

            QSlider::sub-page:vertical {{
                background: rgba(50, 135, 230, 105);
                width: 3px;
                border-radius: 1px;
            }}

            QSlider::add-page:vertical {{
                background: rgba(110, 110, 110, 40);
                width: 3px;
                border-radius: 1px;}}
        """)

    def enterEvent(self, event):
        self._aplicar_estilo(
            destacado=True)

        super().enterEvent(event)

    def leaveEvent(self, event):
        self._aplicar_estilo(
            destacado=False)

        super().leaveEvent(event)

    def mousePressEvent(self, event):
        event.accept()
        super().mousePressEvent(event)

    def mouseMoveEvent(self, event):
        event.accept()
        super().mouseMoveEvent(event)

    def mouseReleaseEvent(self, event):
        event.accept()
        super().mouseReleaseEvent(event)

    def wheelEvent(self, event):
        delta = event.angleDelta().y()

        if delta > 0:
            self.setValue(
                min(
                    self.maximum(),
                    self.value() + 2))

        elif delta < 0:
            self.setValue(
                max(
                    self.minimum(),
                    self.value() - 2))

        event.accept()

class ColorBarWidget(QWidget):
    """
    Barra discreta com rótulos por faixa (estilo QGIS).
    Desenha todos os blocos, encolhendo-os se faltar altura.
    """
    def __init__(self, parent=None):
        super().__init__(parent)
        # sem altura fixa!
        self.setMinimumWidth(160)
        self._labels = []
        self._bands  = []
        # parâmetros base (podem ser ajustados)
        self._margin = 8
        self._gap    = 8
        self._box    = 22   # altura base de cada quadrado

    def update_discrete(self, labels, band_colors):
        self._labels = list(labels)
        norm = []
        for c in band_colors:
            if len(c) >= 4: r,g,b,a = c[:4]
            else:           r,g,b,a = (*c[:3], 1.0)
            norm.append((float(r), float(g), float(b), float(a)))
        # Robustez: garante pelo menos uma faixa placeholder
        if not norm:
            norm = [(0.85, 0.85, 0.85, 1.0)]
            if not self._labels:
                self._labels = [""]  # opcional: "Sem dados"

        self._bands = norm

        # define uma altura mínima suficiente para N faixas (sem compressão)
        n = max(1, len(self._bands))
        h_min = self._margin*2 + n*self._box + (n-1)*self._gap
        self.setMinimumHeight(int(h_min))
        self.updateGeometry()
        self.update()

    def sizeHint(self):
        # sugere altura baseada no nº de faixas
        n = max(1, len(self._bands))
        h = self._margin*2 + n*self._box + (n-1)*self._gap
        return QSize(180, int(h))

    def paintEvent(self, ev):
        """
        Desenha a barra de cores em faixas discretas.
        Robusto contra listas vazias ou desbalanceadas (_bands/_labels).
        """
        p = QPainter(self)
        p.setRenderHint(QPainter.RenderHint.Antialiasing, True)
        try:
            p.setRenderHint(QPainter.RenderHint.TextAntialiasing, True)
        except Exception:
            pass  # nosec B110

        # número de faixas a desenhar (pelo menos 1 para manter layout estável)
        bands_len = len(self._bands) if getattr(self, "_bands", None) is not None else 0
        labels_len = len(self._labels) if getattr(self, "_labels", None) is not None else 0
        n = max(1, bands_len)

        margin = self._margin
        gap_y  = self._gap

        w = self.width()
        h = self.height()

        # Altura disponível; encolhe o bloco se precisar, mas nunca deixa minúsculo
        avail = max(1, h - 2*margin - (n - 1)*gap_y)
        box = min(self._box, avail / n)
        box = max(12.0, box)

        x_color = margin
        x_text  = int(x_color + box + 10)
        y = margin

        p.setFont(p.font())
        for i in range(n):
            # COR: segura mesmo se _bands for menor que n
            if i < bands_len:
                r, g, b, a = self._bands[i]
            else:
                r, g, b, a = (0.85, 0.85, 0.85, 1.0)  # placeholder

            p.setPen(Qt.PenStyle.NoPen)
            p.setBrush(QColor.fromRgbF(float(r), float(g), float(b), float(a)))
            p.drawRoundedRect(QRect(int(x_color), int(y), int(box), int(box)), 4, 4)

            # RÓTULO: já protegido pelo len
            label = str(self._labels[i]) if i < labels_len else ""
            p.setPen(QColor(40, 40, 40))
            p.drawText(QRect(x_text, int(y), int(w - x_text - margin), int(box)),
                       Qt.AlignmentFlag.AlignVCenter | Qt.AlignmentFlag.AlignLeft, label)

            y += box + gap_y

        p.end()

class KMLStyleDialog(QDialog):
    """
    Esta classe cria um diálogo para a personalização dos estilos de exportação KML. O usuário pode definir
    a largura da linha, a transparência da linha, a cor da linha, a transparência das faces e a cor das faces.
    
    Detalhamento:
    1. Inicialização dos valores padrão para a cor da linha e a cor das faces.
    2. Configuração do layout principal do diálogo.
    3. Criação de um QFrame para manter os widgets de configuração.
    4. Adição de widgets para configurar a largura da linha.
    5. Adição de widgets para configurar a transparência da linha e escolher a cor da linha.
    6. Adição de widgets para configurar a transparência das faces e escolher a cor das faces.
    7. Adição de botões para confirmar ou cancelar a exportação.
    8. Configuração das interações, como a alteração da transparência da linha que desativa a largura da linha.

    Parâmetros:
    - parent: Widget pai do diálogo (padrão: None).

    Retorno:
    - Nenhum retorno direto. O diálogo coleta as configurações de estilo do usuário.

    Exceções tratadas:
    - Nenhuma exceção específica tratada nesta função.
    """
    
    def __init__(self, parent=None):
        super().__init__(parent)
        self.setWindowTitle(self.tr("Personalização de Estilos KML"))
        
        self.line_color = QColor(0, 0, 255)  # Cor padrão azul
        self.face_color = QColor(0, 255, 0)  # Cor padrão verde

        # Layout principal
        main_layout = QVBoxLayout()  # Cria o layout vertical principal

        # QFrame
        frame = QFrame()  # Cria um frame
        frame.setFrameShape(QFrame.Shape.StyledPanel)  # Define o estilo do frame
        frame.setFrameShadow(QFrame.Shadow.Raised)  # Define a sombra do frame
        frame_layout = QVBoxLayout()  # Cria um layout vertical para o frame

        # Largura da Linha
        line_width_layout = QHBoxLayout()  # Cria um layout horizontal para a largura da linha
        line_width_label = QLabel(self.tr("Largura da Linha:"))  # Cria um rótulo
        self.line_width_spinbox = QDoubleSpinBox()  # Cria um spinbox para a largura da linha
        self.line_width_spinbox.setRange(0.5, 10.0)  # Define o intervalo de valores
        self.line_width_spinbox.setSingleStep(0.5)  # Define o passo dos valores
        self.line_width_spinbox.setValue(1.0)  # Define o valor padrão
        line_width_layout.addWidget(line_width_label)  # Adiciona o rótulo ao layout
        line_width_layout.addWidget(self.line_width_spinbox)  # Adiciona o spinbox ao layout
        
        # Opacidade da Linha
        line_opacity_layout = QHBoxLayout()  # Cria um layout horizontal para a opacidade da linha
        line_opacity_label = QLabel(self.tr("Transparência das Linhas:"))  # Cria um rótulo
        self.line_opacity_spinbox = QSpinBox()  # Cria um spinbox para a opacidade da linha
        self.line_opacity_spinbox.setRange(0, 100)  # Define o intervalo de valores
        self.line_opacity_spinbox.setSingleStep(5)  # Define o passo dos valores
        self.line_opacity_spinbox.setSuffix("%")  # Define o sufixo "%" para o spinbox
        self.line_opacity_spinbox.setValue(100)  # Define o valor padrão
        self.line_opacity_spinbox.valueChanged.connect(self.update_line_width_state)  # Conecta o sinal de alteração de valor ao método update_line_width_state
        self.line_color_button = QPushButton(self.tr("Cor"))  # Cria um botão para escolher a cor da linha
        self.line_color_button.setFixedSize(30, 20)  # Define o tamanho fixo do botão
        self.line_color_button.clicked.connect(self.choose_line_color)  # Conecta o clique do botão ao método choose_line_color
        self.update_button_color(self.line_color_button, self.line_color)  # Atualiza a cor do botão
        line_opacity_layout.addWidget(line_opacity_label)  # Adiciona o rótulo ao layout
        line_opacity_layout.addWidget(self.line_opacity_spinbox)  # Adiciona o spinbox ao layout
        line_opacity_layout.addWidget(self.line_color_button)  # Adiciona o botão ao layout
        
        # Transparência das Faces
        face_opacity_layout = QHBoxLayout()  # Cria um layout horizontal para a opacidade das faces
        face_opacity_label = QLabel(self.tr("Transparência das Faces:"))  # Cria um rótulo
        self.face_opacity_spinbox = QSpinBox()  # Cria um spinbox para a opacidade das faces
        self.face_opacity_spinbox.setRange(0, 100)  # Define o intervalo de valores
        self.face_opacity_spinbox.setSingleStep(5)  # Define o passo dos valores
        self.face_opacity_spinbox.setSuffix("%")  # Define o sufixo "%" para o spinbox
        self.face_opacity_spinbox.setValue(50)  # Define o valor padrão
        self.face_color_button = QPushButton(self.tr("Cor"))  # Cria um botão para escolher a cor das faces
        self.face_color_button.setFixedSize(30, 20)  # Define o tamanho fixo do botão
        self.face_color_button.clicked.connect(self.choose_face_color)  # Conecta o clique do botão ao método choose_face_color
        self.update_button_color(self.face_color_button, self.face_color)  # Atualiza a cor do botão
        face_opacity_layout.addWidget(face_opacity_label)  # Adiciona o rótulo ao layout
        face_opacity_layout.addWidget(self.face_opacity_spinbox)  # Adiciona o spinbox ao layout
        face_opacity_layout.addWidget(self.face_color_button)  # Adiciona o botão ao layout
        
        # Botões
        self.ok_button = QPushButton(self.tr("Exportar"))  # Cria o botão de confirmação
        self.ok_button.clicked.connect(self.accept)  # Conecta o clique do botão ao método accept
        self.cancel_button = QPushButton(self.tr("Cancelar"))  # Cria o botão de cancelamento
        self.cancel_button.clicked.connect(self.reject)  # Conecta o clique do botão ao método reject
        buttons_layout = QHBoxLayout()  # Cria um layout horizontal para os botões
        buttons_layout.addWidget(self.ok_button)  # Adiciona o botão de confirmação ao layout
        buttons_layout.addWidget(self.cancel_button)  # Adiciona o botão de cancelamento ao layout
        
        # Adicionando ao frame layout
        frame_layout.addLayout(line_width_layout)  # Adiciona o layout da largura da linha ao layout do frame
        frame_layout.addLayout(line_opacity_layout)  # Adiciona o layout da opacidade da linha ao layout do frame
        frame_layout.addLayout(face_opacity_layout)  # Adiciona o layout da opacidade das faces ao layout do frame
        frame_layout.addLayout(buttons_layout)  # Adiciona o layout dos botões ao layout do frame
        frame.setLayout(frame_layout)  # Define o layout do frame
        
        # Adicionando ao layout principal
        main_layout.addWidget(frame)  # Adiciona o frame ao layout principal
        self.setLayout(main_layout)  # Define o layout principal do diálogo

    def choose_line_color(self):
        """
        Abre um diálogo de seleção de cores para escolher a cor da linha.
        Atualiza a cor do botão de seleção de cor da linha se uma cor válida for escolhida.

        Detalhamento:
        1. Abre o diálogo de seleção de cores com a cor atual da linha como padrão.
        2. Verifica se a cor escolhida pelo usuário é válida.
        3. Atualiza a cor da linha com a cor escolhida.
        4. Atualiza a cor do botão de seleção de cor da linha para refletir a nova cor.

        Parâmetros:
        - Nenhum

        Retorno:
        - Nenhum retorno direto. A função atualiza a cor da linha e a cor do botão de seleção.

        Exceções tratadas:
        - Nenhuma exceção específica tratada nesta função.
        """
        # Abre o diálogo de seleção de cores com a cor atual da linha como padrão
        color = QColorDialog.getColor(self.line_color, self)

        # Verifica se a cor escolhida pelo usuário é válida
        if color.isValid():
            # Atualiza a cor da linha com a cor escolhida
            self.line_color = color

            # Atualiza a cor do botão de seleção de cor da linha para refletir a nova cor
            self.update_button_color(self.line_color_button, self.line_color)

    def choose_face_color(self):
        """
        Abre um diálogo de seleção de cores para escolher a cor das faces.
        Atualiza a cor do botão de seleção de cor das faces se uma cor válida for escolhida.

        Detalhamento:
        1. Abre o diálogo de seleção de cores com a cor atual das faces como padrão.
        2. Verifica se a cor escolhida pelo usuário é válida.
        3. Atualiza a cor das faces com a cor escolhida.
        4. Atualiza a cor do botão de seleção de cor das faces para refletir a nova cor.

        Parâmetros:
        - Nenhum

        Retorno:
        - Nenhum retorno direto. A função atualiza a cor das faces e a cor do botão de seleção.

        Exceções tratadas:
        - Nenhuma exceção específica tratada nesta função.
        """
        # Abre o diálogo de seleção de cores com a cor atual das faces como padrão
        color = QColorDialog.getColor(self.face_color, self)

        # Verifica se a cor escolhida pelo usuário é válida
        if color.isValid():
            # Atualiza a cor das faces com a cor escolhida
            self.face_color = color
            # Atualiza a cor do botão de seleção de cor das faces para refletir a nova cor
            self.update_button_color(self.face_color_button, self.face_color)

    def update_button_color(self, button, color):
        """
        Atualiza a cor de fundo de um botão para refletir a cor selecionada.

        Detalhamento:
        1. Obtém a paleta atual do botão.
        2. Define a nova cor de fundo do botão na paleta.
        3. Habilita o preenchimento automático de fundo do botão.
        4. Aplica a nova paleta ao botão.
        5. Atualiza o botão para refletir as mudanças.

        Parâmetros:
        - button: O botão cuja cor de fundo será atualizada.
        - color: A nova cor a ser aplicada ao botão.

        Retorno:
        - Nenhum retorno direto. A função atualiza a cor de fundo do botão.

        Exceções tratadas:
        - Nenhuma exceção específica tratada nesta função.
        """
        # Obtém a paleta atual do botão
        palette = button.palette()

        # Define a nova cor de fundo do botão na paleta
        palette.setColor(QPalette.ColorRole.Button, color)

        # Habilita o preenchimento automático de fundo do botão
        button.setAutoFillBackground(True)

        # Aplica a nova paleta ao botão
        button.setPalette(palette)

        # Atualiza o botão para refletir as mudanças
        button.update()

    def update_line_width_state(self):
        """
        Atualiza o estado de habilitação do spinbox da largura da linha com base no valor da opacidade da linha.

        Detalhamento:
        1. Verifica se o valor do spinbox de opacidade da linha é igual a 0.
        2. Se a opacidade da linha for 0, desativa o spinbox da largura da linha.
        3. Se a opacidade da linha for diferente de 0, ativa o spinbox da largura da linha.

        Parâmetros:
        - Nenhum

        Retorno:
        - Nenhum retorno direto. A função atualiza o estado de habilitação do spinbox da largura da linha.

        Exceções tratadas:
        - Nenhuma exceção específica tratada nesta função.
        """
        # Verifica se o valor do spinbox de opacidade da linha é igual a 0
        if self.line_opacity_spinbox.value() == 0:
            # Se a opacidade da linha for 0, desativa o spinbox da largura da linha
            self.line_width_spinbox.setEnabled(False)
        else:
            # Se a opacidade da linha for diferente de 0, ativa o spinbox da largura da linha
            self.line_width_spinbox.setEnabled(True)

    def get_style_options(self):
        """
        Retorna as opções de estilo definidas pelo usuário para a exportação KML.

        Detalhamento:
        1. Obtém o valor da largura da linha do spinbox correspondente.
        2. Converte o valor da opacidade da linha de percentual (0-100%) para uma escala de 0 a 255.
        3. Obtém a cor da linha selecionada pelo usuário.
        4. Converte o valor da opacidade das faces de percentual (0-100%) para uma escala de 0 a 255.
        5. Obtém a cor das faces selecionada pelo usuário.

        Parâmetros:
        - Nenhum

        Retorno:
        - Um dicionário contendo as opções de estilo:
            - "line_width": Largura da linha (float).
            - "line_opacity": Opacidade da linha (int, 0-255).
            - "line_color": Cor da linha (QColor).
            - "face_opacity": Opacidade das faces (int, 0-255).
            - "face_color": Cor das faces (QColor).

        Exceções tratadas:
        - Nenhuma exceção específica tratada nesta função.
        """

        # Retorna um dicionário com as opções de estilo
        return {
            "line_width": self.line_width_spinbox.value(),  # Obtém o valor da largura da linha
            "line_opacity": int(self.line_opacity_spinbox.value() * 2.55),  # Converte a opacidade da linha de % para 0-255
            "line_color": self.line_color,  # Obtém a cor da linha
            "face_opacity": int(self.face_opacity_spinbox.value() * 2.55),  # Converte a opacidade das faces de % para 0-255
            "face_color": self.face_color}  # Obtém a cor das faces

class ExportaMalha3D(QDialog):
    def __init__(self, parent=None):
        """
        Inicializa a interface de diálogo para exportação de malha 3D.

        Funções e Ações Desenvolvidas:
        - Configura o título da janela do diálogo.
        - Cria e organiza os layouts e botões do diálogo.
        - Aplica estilos personalizados aos botões.
        - Adiciona efeitos de sombra aos textos dos botões.

        :param parent: O widget pai do diálogo, se houver.
        """
        super().__init__(parent)
        
        self.setWindowTitle(self.tr("Exportar Malha 3D"))  # Define o título da janela do diálogo
        
        main_layout = QVBoxLayout()  # Cria o layout principal do tipo QVBoxLayout
        
        # Cria um frame para os botões com estilo de painel
        frame = QFrame()
        frame.setFrameShape(QFrame.Shape.StyledPanel)
        frame.setFrameShadow(QFrame.Shadow.Raised)
        
        frame_layout = QVBoxLayout()  # Cria o layout do frame do tipo QVBoxLayout
        
        # Layout superior com dois botões (DXF e DAE)
        top_layout = QHBoxLayout()
        self.button_dxf = QPushButton("DXF")
        self.button_dae = QPushButton("DAE")
        top_layout.addWidget(self.button_dxf)
        top_layout.addWidget(self.button_dae)
        
        # Layout inferior com dois botões (STL e OBJ)
        bottom_layout = QHBoxLayout()
        self.button_stl = QPushButton("STL")
        self.button_obj = QPushButton("OBJ")
        bottom_layout.addWidget(self.button_stl)
        bottom_layout.addWidget(self.button_obj)
        
        # Adiciona os layouts superior e inferior ao layout do frame
        frame_layout.addLayout(top_layout)
        frame_layout.addLayout(bottom_layout)
        frame.setLayout(frame_layout)  # Define o layout do frame
        
        # Botão de cancelar
        self.button_cancel = QPushButton(self.tr("Cancelar"))
        self.button_cancel.clicked.connect(self.reject)  # Conecta o botão cancelar à função reject
        
        # Adiciona o frame e o botão de cancelar ao layout principal
        main_layout.addWidget(frame)
        main_layout.addWidget(self.button_cancel)
        
        self.setLayout(main_layout)  # Define o layout principal do diálogo
        
        # Personalizar os botões
        self.estilizar_botoes()
        self.adicionar_sombra_nos_textos()

    def estilizar_botoes(self):
        """
        Aplica estilos personalizados aos botões de formato de exportação.

        Funções e Ações Desenvolvidas:
        - Define um estilo base para todos os botões.
        - Aplica estilos específicos para cada botão (DXF, DAE, STL, OBJ).
        """
        estilo_base = """
            QPushButton {
                border: 2px solid #8f8f91;
                border-radius: 5px;
                background-color: #f0f0f0;
                min-width: 70px;
                padding: 5px;
                font: bold 12px;
            }
            QPushButton:pressed {
                background-color: #e0e0e0;
            }
            QPushButton:hover {
                background-color: #d0d0d0;
            }
        """

        # Estilo personalizado para o botão DXF
        self.button_dxf.setStyleSheet(estilo_base + """
            QPushButton {
                border-color: #0078d7;
                color: #0078d7;
            }
            QPushButton:pressed {
                background-color: #005bb5;
                color: #ffffff;
            }
            QPushButton:hover {
                background-color: #3399ff;
            }
        """)

        # Estilo personalizado para o botão DAE
        self.button_dae.setStyleSheet(estilo_base + """
            QPushButton {
                border-color: #d70022;
                color: #d70022;
            }
            QPushButton:pressed {
                background-color: #b5001a;
                color: #ffffff;
            }
            QPushButton:hover {
                background-color: #ff3344;
            }
        """)

        # Estilo personalizado para o botão STL
        self.button_stl.setStyleSheet(estilo_base + """
            QPushButton {
                border-color: #008000;
                color: #008000;
            }
            QPushButton:pressed {
                background-color: #005500;
                color: #ffffff;
            }
            QPushButton:hover {
                background-color: #33cc33;
            }
        """)

        # Estilo personalizado para o botão OBJ
        self.button_obj.setStyleSheet(estilo_base + """
            QPushButton {
                border-color: #ffa500;
                color: #ffa500;
            }
            QPushButton:pressed {
                background-color: #cc8400;
                color: #ffffff;
            }
            QPushButton:hover {
                background-color: #ffc966;
            }
        """)

    def adicionar_sombra_nos_textos(self):
        """
        Adiciona efeitos de sombra aos textos dos botões de formato de exportação.

        Funções e Ações Desenvolvidas:
        - Cria um efeito de sombra para cada botão.
        - Aplica o efeito de sombra aos botões de formato de exportação.
        """
        botoes = [self.button_dxf, self.button_dae, self.button_stl, self.button_obj]  # Lista de botões

        # Itera sobre cada botão e aplica o efeito de sombra
        for botao in botoes:
            efeito_sombra = QGraphicsDropShadowEffect()
            efeito_sombra.setBlurRadius(10)  # Define o raio do desfoque da sombra
            efeito_sombra.setColor(QColor(0, 0, 0, 160))  # Define a cor da sombra com opacidade
            efeito_sombra.setOffset(2, 2)  # Define o deslocamento da sombra
            botao.setGraphicsEffect(efeito_sombra)  # Aplica o efeito de sombra ao botão

class CustomDelegate(QStyledItemDelegate):
    """
    CustomDelegate é uma classe que herda de QStyledItemDelegate.
    Esta classe é usada para personalizar a aparência de itens em um QTreeView, especificamente
    para desenhar ícones que representam camadas de malha no QGIS.
    
    Métodos:
    - __init__: Inicializa a classe CustomDelegate.
    - paint: Desenha o ícone personalizado para a camada de malha.
    - sizeHint: Define o tamanho dos itens no QTreeView.
    """
    def __init__(self, parent=None):
        """
        Inicializa a instância de CustomDelegate.

        Parâmetros:
        - parent: O pai do delegado, geralmente o QTreeView.
        """
        super(CustomDelegate, self).__init__(parent)

    def paint(self, painter, option, index):
        """
        Desenha o ícone personalizado para a camada de malha.

        Parâmetros:
        - painter: O QPainter usado para desenhar o ícone.
        - option: As opções de estilo usadas para desenhar o item.
        - index: O índice do item no modelo.
        """
        super(CustomDelegate, self).paint(painter, option, index)  # Chama o método paint da classe base
        layer_id = index.data(Qt.ItemDataRole.UserRole)
        layer = QgsProject.instance().mapLayer(layer_id)   # busca objeto
        if isinstance(layer, QgsMeshLayer):  # Verifica se a camada é do tipo QgsMeshLayer
            icon_size = 14  # Define o tamanho do ícone
            pixmap = QPixmap(icon_size, icon_size)  # Cria um QPixmap do tamanho do ícone
            pixmap.fill(Qt.GlobalColor.transparent)  # Preenche o QPixmap com transparência
            icon_painter = QPainter(pixmap)  # Cria um QPainter para desenhar no QPixmap
            icon_painter.setRenderHint(QPainter.RenderHint.Antialiasing)  # Habilita antialiasing para suavizar o desenho

            pen = QPen(Qt.GlobalColor.blue)  # Cria uma caneta com a cor azul
            pen.setWidth(1)  # Define a largura da caneta
            icon_painter.setPen(pen)  # Define a caneta no QPainter

            # Define points for the triangles
            points = [
                QPoint(0, 0), QPoint(icon_size // 2, 0), QPoint(icon_size - 1, 0),
                QPoint(0, icon_size // 2), QPoint(icon_size // 2, icon_size // 2), QPoint(icon_size - 1, icon_size // 2),
                QPoint(0, icon_size - 1), QPoint(icon_size // 2, icon_size - 1), QPoint(icon_size - 1, icon_size - 1)]

            # Define triangles with corresponding colors
            triangles = [
                (0, 1, 4, QColor(255, 255, 0)),  # Amarelo
                (0, 3, 4, QColor(255, 165, 0)),  # Laranja
                (1, 2, 4, QColor(255, 0, 255)),  # Roxo
                (3, 4, 7, QColor(255, 0, 255)),  # Roxo
                (3, 6, 7, QColor(255, 165, 0)),  # Laranja
                (4, 5, 8, QColor(255, 255, 0)),  # Amarelo
                (4, 7, 8, QColor(255, 0, 255))]   # Roxo

            # Draw the triangles with colors
            for t in triangles:
                icon_painter.setBrush(t[3])  # Define o pincel com a cor do triângulo
                icon_painter.drawPolygon(points[t[0]], points[t[1]], points[t[2]])  # Desenha o triângulo

            icon_painter.end()  # Finaliza o desenho

            icon = QIcon(pixmap)  # Cria um ícone a partir do QPixmap
            icon_rect = option.rect  # Obtém o retângulo de desenho
            icon_rect.setSize(QSize(icon_size, icon_size))  # Define o tamanho do retângulo do ícone
            icon_rect.moveLeft(option.rect.left() - 16)  # Move o ícone para a esquerda
            icon.paint(painter, icon_rect, Qt.AlignmentFlag.AlignVCenter | Qt.AlignmentFlag.AlignLeft)  # Desenha o ícone no retângulo

    def sizeHint(self, option, index):
        """
        Define o tamanho dos itens no QTreeView.

        Parâmetros:
        - option: As opções de estilo usadas para desenhar o item.
        - index: O índice do item no modelo.

        Retorna:
        - QSize: O tamanho sugerido para o item.
        """
        size = super(CustomDelegate, self).sizeHint(option, index)  # Obtém o tamanho sugerido da classe base
        return QSize(size.width(), max(size.height(), 15))  # Retorna o tamanho ajustado