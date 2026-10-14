from qgis.PyQt.QtWidgets import QInputDialog, QTreeView, QStyledItemDelegate, QColorDialog, QMenu, QLineEdit, QDialog, QVBoxLayout, QLabel, QPushButton, QHBoxLayout, QFileDialog, QComboBox, QFrame, QCheckBox, QDoubleSpinBox, QRadioButton, QButtonGroup, QProgressBar, QDialogButtonBox, QGraphicsView, QListWidget, QGraphicsScene, QToolTip, QGraphicsRectItem, QGraphicsLineItem, QListWidgetItem, QWidget, QListView, QAbstractItemView, QScrollArea, QSizePolicy, QMessageBox, QGridLayout
from qgis.core import QgsProject, QgsMapLayer, QgsWkbTypes, QgsSingleSymbolRenderer, QgsCategorizedSymbolRenderer, QgsSymbol, Qgis, QgsVectorLayerSimpleLabeling, QgsSimpleLineSymbolLayer, QgsRenderContext, QgsCoordinateReferenceSystem, QgsCoordinateTransform, QgsMessageLog, QgsLayerTreeLayer, QgsSymbolLayer, QgsGeometry, QgsSpatialIndex, QgsVectorFileWriter, QgsDefaultValue, QgsEditorWidgetSetup, QgsEditFormConfig, QgsVectorLayer, QgsFields, QgsField, QgsFeature, QgsPointXY, QgsPoint, QgsPalLayerSettings, QgsProperty, QgsMarkerSymbol, QgsMapLayerStyle
from qgis.PyQt.QtGui import QStandardItemModel, QStandardItem, QIcon, QPixmap, QPainter, QColor, QPen, QFont, QBrush, QGuiApplication, QTransform, QCursor, QPainterPath, QPolygonF, QWheelEvent, QDesktopServices
from qgis.PyQt.QtCore import Qt, QRect, QEvent, QCoreApplication, QSettings, QItemSelectionModel, QPointF, QSize, QUrl, QVariant, QObject, QTimer, QStandardPaths, QMetaType
from qgis.PyQt.QtNetwork import QNetworkAccessManager, QNetworkRequest, QNetworkReply
from qgis.gui import QgsProjectionSelectionDialog
from PIL import Image, UnidentifiedImageError
from ezdxf.colors import rgb2int, aci2rgb
from lxml import etree as XmlET
try:
    from defusedxml import ElementTree as DefusedET
    from defusedxml.common import DefusedXmlException
    DEFUSEDXML_OK = True
except ImportError:
    DefusedET = None
    DefusedXmlException = Exception
    DEFUSEDXML_OK = False
from itertools import zip_longest
from ezdxf import colors
from io import BytesIO
import html as _html
import processing
import re as _re
import tempfile
import openpyxl
import requests
import hashlib
import random
import ezdxf
import time
import math
import csv
import os
import re
import gc

# Importe as Classes Externas
from .gerenciar_etiquetas_dialog import GerenciarEtiquetasDialog
from .salvar_multiplos import DialogoSalvarFormatos
from .criar_pontos import CamadaPontosManager

class UiManagerT:
    """
    Gerencia a interface do usuário, interagindo com um QTreeView para listar e gerenciar camadas de pontos no QGIS.
    """
    def __init__(self, iface, dialog, plugin):
        """
        Inicializa a instância da classe UiManagerO, responsável por gerenciar a interface do usuário
        que interage com um QTreeView para listar e gerenciar camadas de pontos no QGIS.

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
        self.plugin = plugin

        # Cria e configura o modelo de dados para o QTreeView
        self.treeViewModel = QStandardItemModel()
        self.dlg.treeViewListaPonto.setModel(self.treeViewModel)

        # Atualiza a visualização da lista de camadas no QTreeView
        self.atualizar_treeView_lista_ponto()

        # Aplica estilos CSS para aprimorar a interação visual com os itens do QTreeView
        self.dlg.treeViewListaPonto.setStyleSheet("""
            QTreeView::item:hover:!selected {
                background-color: #def2fc;
            }
            QTreeView::item:selected {
            }""")

        # Inicia a conexão de sinais para tratar a mudança de nome das camadas no projeto
        self.connect_name_changed_signals()

        # Conecta os sinais do QGIS e da interface do usuário para sincronizar ações e eventos
        self.connect_signals()

        # TreeView: tooltip + drag&drop (UMA ÚNICA instalação do filtro)
        tv = self.dlg.treeViewListaPonto

        # Mouse move no viewport (tooltip/hovers)
        tv.setMouseTracking(True)
        tv.viewport().setMouseTracking(True)

        # Drag & Drop de arquivos/pastas
        tv.setAcceptDrops(True)
        tv.viewport().setAcceptDrops(True)
        tv.setDragDropMode(QAbstractItemView.DragDropMode.DropOnly)
        tv.setDefaultDropAction(Qt.DropAction.CopyAction)

        # Instala apenas UM filtro (tooltip + drop)
        self._tree_filter = TreeViewEventFilter(self)
        tv.viewport().installEventFilter(self._tree_filter)

        # instancia uma vez só o manager
        self.pontos_manager = CamadaPontosManager(iface) 

        # Controla os ítens da etiqueta
        self.fieldColors = {}  # Armazenará as cores atribuídas aos campos
        self.fieldVisibility = {}  # Armazena a visibilidade dos campos

        # Mantém na memória a última posição  
        self.ultimo_caminho_salvo = ""  # Inicializa a variável para armazenar o último caminho

        self.atualizar_treeView_lista_ponto()
        # Evita conectar os sinais de tratamento de pontos mais de uma vez
        # na mesma camada.
        self._camadas_ponto_tratadas = set()

    def tr(self, message):
        """
        Traduz textos deste diálogo.
        O contexto precisa ser estável para o Qt Linguist encontrar as traduções.
        """
        return QCoreApplication.translate("UiManagerT", message)

    def connect_signals(self):
        """
        Conecta os sinais do QGIS e do QTreeView para sincronizar a interface com o estado atual do projeto.
        Este método garante que mudanças no ambiente do QGIS se reflitam na interface do usuário e que ações na
        interface desencadeiem reações apropriadas no QGIS.

        Funções e Ações Desenvolvidas:
        - Conexão com sinais de adição e remoção de camadas para atualizar a visualização da árvore.
        - Sincronização do modelo do QTreeView com mudanças de seleção e propriedades das camadas no QGIS.
        - Tratamento da mudança de nome das camadas para manter consistência entre a interface e o estado interno.
        """
        # Conecta sinais do QGIS para lidar com a adição e remoção de camadas no projeto
        QgsProject.instance().layersAdded.connect(self.layers_added)

        # Conecta o evento de mudança em um item do QTreeView para atualizar a visibilidade da camada no QGIS
        self.treeViewModel.itemChanged.connect(self.on_item_changed)

        # Sincroniza o estado das camadas no QGIS com o checkbox do QTreeView sempre que as camadas do mapa mudam
        self.iface.mapCanvas().layersChanged.connect(self.sync_from_qgis_to_treeview)

        # Conecta mudanças na seleção do QTreeView para atualizar a camada ativa no QGIS
        self.dlg.treeViewListaPonto.selectionModel().selectionChanged.connect(self.on_treeview_selection_changed)

        # Sincroniza a seleção no QGIS com a seleção no QTreeView quando a camada ativa no QGIS muda
        self.iface.currentLayerChanged.connect(self.on_current_layer_changed)

        # Conecta o evento de duplo clique em um item para manipulação de cores da camada
        self.dlg.treeViewListaPonto.doubleClicked.connect(self.on_item_double_clicked)

        # Define e aplica um delegado personalizado para customização da exibição de itens no QTreeView
        self.treeViewDelegate = CircleDelegate(self.dlg.treeViewListaPonto)
        self.dlg.treeViewListaPonto.setItemDelegate(self.treeViewDelegate)

        # Configura a política de menu de contexto para permitir menus personalizados em cliques com o botão direito
        self.dlg.treeViewListaPonto.setContextMenuPolicy(Qt.ContextMenuPolicy.CustomContextMenu)
        self.dlg.treeViewListaPonto.customContextMenuRequested.connect(self.open_context_menu)

        # Conecta o botão para criar uma camada de pontos ao método que adiciona a camada e atualiza o treeView
        self.dlg.ButtonCriarPonto.clicked.connect(self.adicionar_camada_e_atualizar)

        # Conecta o botão ao novo método do botão cria uma camada como o nome
        self.dlg.ButtonCriarPontoNome.clicked.connect(self.abrir_caixa_nome_camada)

        # Conecta o botão ao método de exportação do KML
        self.dlg.pushButtonExportaKmlT.clicked.connect(self.exportar_para_kml)
        
        # Conecta o botão ao método de exportação do DXF
        self.dlg.pushButtonExportaDXFT.clicked.connect(self.exportar_para_dxf)

        # Conecta o botão para reprojetar a camada
        self.dlg.pushButtonReprojetarT.clicked.connect(self.abrir_dialogo_crs)

        # seleção via mouse (funciona mesmo com 1 Camada de Pontos)
        self.dlg.treeViewListaPonto.clicked.connect(lambda _: self.on_treeview_selection_changed(None, None))

        # fallback para aplicar o checkbox no QGIS mesmo se o Qt não emitir itemChanged como esperado
        self._tree_sync_depth = getattr(self, "_tree_sync_depth", 0)

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

        # Conectando o botão pushButtonFecharT à função que fecha o diálogo
        self.dlg.pushButtonFecharT.clicked.connect(self.close_dialog)

        # Remove outras camadas sem alterar ações de camadas de outros tipos
        QgsProject.instance().layerWillBeRemoved.connect(self._on_layer_will_be_removed)

        #Diálogo que permite ao usuário selecionar campos da camada atual que serão
        self.dlg.pushButtonCampoT.clicked.connect(self.abrir_dialogo_selecao_campos_ponto)

        # Conecta o botão para Zoom
        self.dlg.pushButtonVisualizarT.clicked.connect(self.visualizar_ponto_selecionado)

        # Conectar o botão de renomear à função de renomear a camada
        self.dlg.pushButtonRenomeT.clicked.connect(self.renomear_camada_selecionada)

        # Conectar o botão de deletar à função de remover a camada
        self.dlg.pushButtonDelT.clicked.connect(self.remover_camada_selecionada)

        # Conectar o botão 'salvar como' à função 'salvar_camada_multiplo' para salvar em múltiplos formatos
        self.dlg.pushButtonSalvaMultiplosT.clicked.connect(self.salvar_camada_multiplo)

        # Conectar o botão de salvar permanente à função de salvar a camada
        self.dlg.pushButton_PermanenteT.clicked.connect(self.salvar_camada_permanente)

        # Conectar o botão 'pushButtonTabelaT' à função de abrir a tabela de atributos
        self.dlg.pushButtonTabelaT.clicked.connect(self.abrir_tabela_atributos)

        # Conecta o botão para Clocar a Camada de Pontos
        self.dlg.pushButtonClonarPonto.clicked.connect(self.clone_layer_ponto)

        # Conectando o botão à função pushButtonAbrirT
        self.dlg.pushButtonAbrirT.clicked.connect(self.abrir_adicionar_arquivo)

    def atualizar_estado_botoes(self):
        """
        Atualiza o estado (habilitado/desabilitado) dos botões da interface gráfica conforme a presença de camadas no treeView de pontos.

        Detalhamento do Processo:
        1. Verifica se o modelo associado ao treeViewListaPonto está vazio, ou seja, sem nenhuma camada listada.
        2. Se o modelo estiver vazio, todos os botões que dependem de camada devem ser desabilitados para evitar operações inválidas.
        3. Caso contrário, os botões são habilitados, permitindo ao usuário interagir normalmente com as funções associadas a uma camada de ponto.
        4. Os botões afetados incluem:
            - Deletar camada (`pushButtonDelT`)
            - Renomear camada (`pushButtonRenomeT`)
            - Tornar camada permanente (`pushButton_PermanenteT`)
            - Salvar em múltiplos formatos (`pushButtonSalvaMultiplosT`)
            - Abrir tabela de atributos (`pushButtonTabelaT`)
            - Gerenciar campos/etiquetas (`pushButtonCampoT`)
            - Exportar para DXF (`pushButtonExportaDXFT`)
            - Exportar para KML (`pushButtonExportaKmlT`)
            - Visualizar pontos associados (`pushButtonVisualizarT`)
            - Clonar pontos (`pushButtonClonarT`)
            - Reprojetar camada (`pushButtonReprojetarT`)
        5. Garante uma experiência segura e intuitiva, evitando erros por ações em contexto inválido.
        """
        # Verifica se o modelo do treeView está vazio
        modelo_vazio = self.dlg.treeViewListaPonto.model().rowCount() == 0

        # Atualiza o estado dos botões baseado na presença ou ausência de itens no modelo
        self.dlg.pushButtonDelT.setEnabled(not modelo_vazio)
        self.dlg.pushButtonRenomeT.setEnabled(not modelo_vazio)
        self.dlg.pushButton_PermanenteT.setEnabled(not modelo_vazio)
        self.dlg.pushButtonSalvaMultiplosT.setEnabled(not modelo_vazio)
        self.dlg.pushButtonTabelaT.setEnabled(not modelo_vazio)
        self.dlg.pushButtonCampoT.setEnabled(not modelo_vazio)
        self.dlg.pushButtonExportaDXFT.setEnabled(not modelo_vazio)
        self.dlg.pushButtonExportaKmlT.setEnabled(not modelo_vazio)
        self.dlg.pushButtonVisualizarT.setEnabled(not modelo_vazio)
        self.dlg.pushButtonClonarPonto.setEnabled(not modelo_vazio)
        self.dlg.pushButtonReprojetarT.setEnabled(not modelo_vazio)

    def abrir_tabela_atributos(self):
        """
        Abre o Gerenciador de Tabelas para a camada de pontos selecionada no treeView.
        """
        selected_indexes = self.dlg.treeViewListaPonto.selectedIndexes()
        if not selected_indexes:
            return

        selected_index = selected_indexes[0]

        layer_id = selected_index.model().itemFromIndex(selected_index).data(Qt.ItemDataRole.UserRole)
        if layer_id is None:
            layer_id = selected_index.model().itemFromIndex(selected_index).data()

        layer = QgsProject.instance().mapLayer(layer_id)
        if not layer:
            return

        try:
            self.iface.setActiveLayer(layer)
        except Exception:
            pass  # nosec B110

        # Abre/reaproveita o diálogo central do plugin
        self.plugin.run_tabelas()

        dlg_tabelas = getattr(self.plugin, "tabelas_dlg", None)
        if dlg_tabelas is None:
            return

        try:
            # Como este manager é de pontos, já força o filtro correto
            dlg_tabelas.radioButtonPonto.setChecked(True)
            dlg_tabelas.update_combo_box_item()

            for i in range(dlg_tabelas.comboBoxCamada.count()):
                if dlg_tabelas.comboBoxCamada.itemData(i) == layer.id():
                    dlg_tabelas.comboBoxCamada.setCurrentIndex(i)
                    break

            dlg_tabelas.raise_()
            dlg_tabelas.activateWindow()

        except Exception:
            pass  # nosec B110

    def salvar_camada_multiplo(self):
        """
        Salva a camada selecionada em múltiplos formatos e exibe UMA mensagem final
        com apenas o botão 'Abrir pasta'.
        """
        # 1) Resolve a camada selecionada pelo ID salvo no Qt.UserRole
        selected_indexes = self.dlg.treeViewListaPonto.selectedIndexes()
        if not selected_indexes:
            self.mostrar_mensagem(self.tr("Selecione uma camada para exportar."), "Erro")
            return
        selected_index = selected_indexes[0]
        layer_id = selected_index.model().itemFromIndex(selected_index).data(Qt.ItemDataRole.UserRole)
        layer_to_save = QgsProject.instance().mapLayer(layer_id)
        if not layer_to_save or layer_to_save.type() != QgsMapLayer.LayerType.VectorLayer or not layer_to_save.isValid():
            self.mostrar_mensagem(self.tr("Nenhuma camada vetorial válida selecionada."), "Erro")
            return
        if layer_to_save.featureCount() == 0:
            self.mostrar_mensagem(self.tr("Nenhuma feição para exportar."), "Erro")
            return

        # 2) Diálogo de formatos (seu diálogo atual)
        formatos = {
            "DXF": ".dxf",
            "KML": ".kml",
            "GeoJSON": ".geojson",
            "CSV": ".csv",
            "Shapefile": ".shp",
            "TXT": ".txt",
            "Excel": ".xlsx",
            "Geopackage": ".gpkg"}
        dialogo = DialogoSalvarFormatos(formatos, self.dlg)
        if not dialogo.exec():
            return  # cancelado

        if not dialogo.formatos_selecionados:
            self.mostrar_mensagem(self.tr("Nenhum formato selecionado."), "Info")
            return

        # 3) Escolher 1 diretório (usar o padrão nativo aqui é ok; se preferir, faça um seletor não-nativo)
        diretorio = QFileDialog.getExistingDirectory(self.dlg, self.tr("Escolha um diretório para salvar os arquivos"))
        if not diretorio:
            return  # cancelado

        # 4) Exporta todos em silêncio e acumula resultados
        resultados = []  # (ext, caminho_final_ou_None, ok)
        for extensao in dialogo.formatos_selecionados:
            nome_arquivo = os.path.join(diretorio, f"{layer_to_save.name()}{extensao}")
            self.salvar_no_formato_especifico(layer_to_save, extensao, nome_arquivo, silencioso=True, coletor=resultados)

        # 5) Mensagem única com APENAS o botão "Abrir pasta"
        total = len(resultados)
        ok_list   = [r for r in resultados if r[2]]
        fail_list = [r for r in resultados if not r[2]]

        fmt_ok   = ", ".join(sorted({ext.lstrip(".").upper() for ext, _, ok in resultados if ok}))
        fmt_fail = ", ".join(sorted({ext.lstrip(".").upper() for ext, _, ok in resultados if not ok}))

        if not fail_list:
            msg = self.tr("Arquivos salvos com sucesso ({ok}/{total}): {fmt_ok}.").format(
                ok=len(ok_list),
                total=total,
                fmt_ok=fmt_ok)

            self.mostrar_mensagem(msg, "Sucesso", caminho_pasta=diretorio)
        else:
            msg = self.tr("Arquivos salvos ({ok}/{total}).").format(
                ok=len(ok_list),
                total=total)

            if fmt_ok:
                msg += " " + self.tr("OK: {fmt_ok}.").format(fmt_ok=fmt_ok)
            if fmt_fail:
                msg += " " + self.tr("Falharam: {fmt_fail}.").format(fmt_fail=fmt_fail)
            self.mostrar_mensagem(msg, "Info", caminho_pasta=diretorio)

    def salvar_no_formato_especifico(self, layer, extensao, nome_arquivo=None, *, silencioso=False, coletor=None):
        """
        Exporta uma camada QGIS para um formato específico (ex.: SHP, KML, DXF, TXT, XLSX).

        - Garante extensão correta no nome do arquivo;
        - Evita sobrescrita gerando nomes incrementais (_1, _2...);
        - Usa diálogos de "Salvar como" quando não há caminho informado;
        - Atualiza o último diretório salvo (`self.ultimo_caminho_salvo`);
        - Permite execução silenciosa (sem mensagens de sucesso/erro);
        - Opcionalmente registra resultados em `coletor` [(extensão, caminho, ok), ...].

        Retorna:
            bool: True se a camada foi salva com sucesso, False caso contrário.
        """
        # Validação básica
        if layer is None or not getattr(layer, "isValid", lambda: False)():
            if coletor is not None:
                coletor.append((extensao, None, False))
            if not silencioso:
                self.mostrar_mensagem(self.tr("Camada inválida para salvar."), "Erro")
            return False

        # Normaliza extensão
        ext = (extensao or "").strip().lower()
        if not ext:
            if coletor is not None:
                coletor.append((extensao, None, False))
            if not silencioso:
                self.mostrar_mensagem(self.tr("Extensão não informada."), "Erro")
            return False
        if not ext.startswith("."):
            ext = f".{ext}"

        # Filtro/driver
        tipos_de_arquivo = {
            ".dxf": ("DXF Files (*.dxf)", "DXF"),
            ".kml": ("KML Files (*.kml)", "KML"),
            ".shp": ("Shapefile Files (*.shp)", "ESRI Shapefile"),
            ".txt": ("Text Files (*.txt)", "TXT"),
            ".csv": ("CSV Files (*.csv)", "CSV"),
            ".geojson": ("GeoJSON Files (*.geojson)", "GeoJSON"),
            ".gpkg": ("Geopackage Files (*.gpkg)", "GPKG"),
            ".xlsx": ("Excel Files (*.xlsx)", "XLSX")}
        filtro, driver_name = tipos_de_arquivo.get(ext, (None, None))
        if not filtro:
            if coletor is not None:
                coletor.append((ext, None, False))
            if not silencioso:
                self.mostrar_mensagem(self.tr("Extensão não suportada: {ext}").format(ext=ext), "Erro")
            return False

        # Se veio diretório, vira arquivo dentro dele
        if nome_arquivo and os.path.isdir(nome_arquivo):
            nome_arquivo = os.path.join(nome_arquivo, f"{layer.name()}{ext}")

        # Se não veio arquivo, pergunta por um
        if not nome_arquivo:
            base_dir = getattr(self, "ultimo_caminho_salvo", "") or os.path.expanduser("~")
            sugestao = os.path.join(base_dir, f"{layer.name()}{ext}")
            nome_arquivo = self.escolher_local_para_salvar(sugestao, filtro)
            if not nome_arquivo:
                if coletor is not None:
                    coletor.append((ext, None, False))
                return False

        # Garante extensão
        if not nome_arquivo.lower().endswith(ext):
            nome_arquivo = f"{nome_arquivo}{ext}"

        # Evita overwrite
        base_sem_ext, _ = os.path.splitext(nome_arquivo)
        final_path = nome_arquivo
        c = 1
        while os.path.exists(final_path):
            final_path = f"{base_sem_ext}_{c}{ext}"
            c += 1

        # Atualiza último diretório
        try:
            ultimo_dir = os.path.dirname(final_path)
            if ultimo_dir:
                self.ultimo_caminho_salvo = ultimo_dir
        except Exception:
            pass  # nosec B110

        # Salvar (silencioso)
        ok = False
        try:
            if ext == ".txt":
                ok = self.salvar_como_txt(layer, final_path, silencioso=True)
            elif ext == ".xlsx":
                ok = self.salvar_como_xlsx(layer, final_path, silencioso=True)
            else:
                ok = self.salvar_camada(layer, final_path, driverName=driver_name, silencioso=True)
        except Exception as e:
            ok = False

        # Reporta no coletor
        if coletor is not None:
            coletor.append((ext, final_path if ok else None, ok))

        # Se não for silencioso, mostra a mensagem individual
        if not silencioso:
            ext_fmt = ext.lstrip(".").upper()
            if ok:
                self.mostrar_mensagem(self.tr("Arquivo salvo com sucesso ({ext}).").format(ext=ext_fmt), "Sucesso", caminho_pasta=os.path.dirname(final_path), caminho_arquivos=final_path)
            else:
                self.mostrar_mensagem(self.tr("Não foi possível salvar ({ext}).").format(ext=ext_fmt), "Erro")

        return ok

    def salvar_camada(self, layer, fileName, driverName, silencioso=True):
        """
        Salva uma camada vetorial nos formatos suportados pelo QGIS.
        """
        driver = (driverName or "").upper()

        options = QgsVectorFileWriter.SaveVectorOptions()
        options.driverName = driver
        options.fileEncoding = "UTF-8"
        options.onlySelectedFeatures = False

        lyr_to_write = layer

        if driver == "KML":
            try:
                target = QgsCoordinateReferenceSystem("EPSG:4326")

                if layer.crs().authid() != target.authid():
                    res = processing.run(
                        "native:reprojectlayer",
                        {"INPUT": layer,
                            "TARGET_CRS": target,
                            "OUTPUT": "memory:"})
                    lyr_to_write = res["OUTPUT"]

            except Exception:
                return False

            options.symbologyExport = (QgsVectorFileWriter.SymbologyExport.FeatureSymbology)

        elif driver == "CSV":
            if (lyr_to_write.geometryType()
                == QgsWkbTypes.GeometryType.PointGeometry):
                options.layerOptions = [
                    "GEOMETRY=AS_XY",
                    "CREATE_CSVT=YES"]
            else:
                options.layerOptions = [
                    "GEOMETRY=AS_WKT",
                    "CREATE_CSVT=YES"]

        elif driver == "ESRI SHAPEFILE":
            options.fileEncoding = "UTF-8"
            options.layerOptions = ["ENCODING=UTF-8"]

            conversor_precisao = (
                self._configurar_precisao_shapefile(
                    lyr_to_write,
                    options))

        elif driver == "DXF":
            options.skipAttributeCreation = True

        elif driver == "GEOJSON":
            options.layerOptions = ["COORDINATE_PRECISION=8"]

        elif driver == "GPKG":
            options.layerOptions = ["SPATIAL_INDEX=YES"]

        try:
            error, _ = (
                QgsVectorFileWriter.writeAsVectorFormat(lyr_to_write, fileName, options))

            if error != QgsVectorFileWriter.WriterError.NoError:
                return False

            if driver == "ESRI SHAPEFILE":
                # Garante a identificação UTF-8 do arquivo DBF.
                caminho_cpg = (os.path.splitext(fileName)[0] + ".cpg")

                try:
                    with open(
                        caminho_cpg,
                        "w",
                        encoding="ascii"
                    ) as arquivo_cpg:
                        arquivo_cpg.write("UTF-8")
                except OSError:
                    # A falha no .cpg não invalida o SHP criado.
                    pass  # nosec B110

            if (
                driver == "KML"
                and hasattr(
                    self,
                    "modificar_kml_para_tessellation")):
                try:
                    self.modificar_kml_para_tessellation(fileName)
                except Exception:
                    pass  # nosec B110

            return True

        except Exception:
            return False

    def salvar_camada_permanente(self):
        """
        Salva a camada selecionada como Shapefile, preservando
        simbologia, etiquetas e codificação UTF-8.
        """
        selected_indexes = (self.dlg.treeViewListaPonto.selectedIndexes())

        if not selected_indexes:
            self.mostrar_mensagem(self.tr("Selecione uma camada."), "Aviso")
            return

        idx = next(
            (i for i in selected_indexes
                if i.column() == 0), selected_indexes[0])

        item = idx.model().itemFromIndex(idx)

        layer_id = (item.data(Qt.ItemDataRole.UserRole)
            or item.data())

        layer_to_save = QgsProject.instance().mapLayer(layer_id)

        if (not layer_to_save
            or not layer_to_save.isValid()):
            self.mostrar_mensagem(self.tr("Camada não encontrada ou inválida."), "Erro")
            return

        # Guarda tudo antes do salvamento, pois o objeto original
        # pode ser removido ou substituído pelo QGIS.
        nome_camada = layer_to_save.name()

        is_temporary = (
            layer_to_save.dataProvider().name()
            == "memory")

        labels_enabled = layer_to_save.labelsEnabled()

        point_colors = self.get_point_colors(
            layer_to_save)

        renderer = (
            layer_to_save.renderer().clone()
            if layer_to_save.renderer()
            else None)

        etiquetas = (
            layer_to_save.labeling().clone()
            if layer_to_save.labeling()
            else None)

        if layer_to_save.isEditable():
            try:
                layer_to_save.commitChanges()
            except Exception:
                pass  # nosec B110

        base_dir = (
            getattr(self, "ultimo_caminho_salvo", "")
            or os.path.expanduser("~"))

        sugestao = os.path.join(
            base_dir,
            f"{nome_camada}.shp")

        nome_arquivo = self.escolher_local_para_salvar(sugestao, "ESRI Shapefile Files (*.shp)")

        if not nome_arquivo:
            return

        if not nome_arquivo.lower().endswith(".shp"):
            nome_arquivo += ".shp"

        # Usa o nome escolhido no diálogo como nome da nova camada.
        nome_camada_salva = os.path.splitext(os.path.basename(nome_arquivo))[0]

        try:
            self.ultimo_caminho_salvo = os.path.dirname(nome_arquivo)
        except Exception:
            pass  # nosec B110

        start = time.time()

        if not self.salvar_camada(
            layer_to_save,
            nome_arquivo,
            "ESRI Shapefile"):
            self.mostrar_mensagem(self.tr("Falha ao salvar a camada no formato Shapefile."), "Erro")
            return

        # Não utilizar layer_to_save abaixo deste ponto.
        new_layer = QgsVectorLayer(
            nome_arquivo,
            nome_camada_salva,
            "ogr")

        if not new_layer.isValid():
            self.mostrar_mensagem(self.tr("Falha ao carregar a nova camada."), "Erro")
            return

        try:
            new_layer.setProviderEncoding("UTF-8")
        except (AttributeError, TypeError):
            pass  # nosec B110

        if renderer:
            new_layer.setRenderer(renderer)

        if etiquetas:
            new_layer.setLabeling(etiquetas)
            new_layer.setLabelsEnabled(labels_enabled)

        self.tratar_pontos(new_layer)

        QgsProject.instance().addMapLayer(new_layer, False)

        root = QgsProject.instance().layerTreeRoot()

        grupo = (root.findGroup(self.tr("Camadas Salvas"))
            or root.addGroup(self.tr("Camadas Salvas")))

        grupo.addLayer(new_layer)

        if is_temporary:
            # A camada pode já ter sido removida durante o processo.
            if QgsProject.instance().mapLayer(layer_id):
                QgsProject.instance().removeMapLayer(layer_id)

        if point_colors:
            fill_color, border_color = point_colors

            self.apply_new_colors(new_layer, fill_color, border_color)

        try:
            new_layer.startEditing()
        except Exception:
            pass  # nosec B110

        elapsed = time.time() - start
        pasta = os.path.dirname(nome_arquivo)

        if pasta:
            self.ultimo_caminho_salvo = pasta

        self.mostrar_mensagem(self.tr("Camada salva em {elapsed:.2f} s.").format(elapsed=elapsed), "Sucesso", caminho_pasta=pasta)

    def _configurar_precisao_shapefile(self, layer, options):
        """
        Detecta a maior quantidade de casas decimais significativa
        de cada campo e aplica essa precisão ao Shapefile.
        """
        precisoes = {}
        tipos_decimais = {
            QMetaType.Type.Double,
            QMetaType.Type.Float}

        for indice, campo in enumerate(layer.fields()):
            if campo.type() not in tipos_decimais:
                continue

            maior_precisao = 0

            for feature in layer.getFeatures():
                valor = feature.attribute(indice)

                if valor is None:
                    continue

                try:
                    numero = float(valor)

                    if not math.isfinite(numero):
                        continue
                except (TypeError, ValueError):
                    continue

                # Tolera pequenos resíduos internos de números Double.
                tolerancia = max(
                    1e-9,
                    math.ulp(numero) * 16)

                casas_valor = 10

                for casas in range(11):
                    if abs(numero - round(numero, casas)) <= tolerancia:
                        casas_valor = casas
                        break

                maior_precisao = max(
                    maior_precisao,
                    casas_valor)

            precisoes[indice] = maior_precisao

        class ConversorPrecisao(
            QgsVectorFileWriter.FieldValueConverter):

            def __init__(self, campos, precisoes_campos):
                super().__init__()
                self.campos = QgsFields(campos)
                self.precisoes = dict(precisoes_campos)

            def fieldDefinition(self, campo):
                novo_campo = QgsField(campo)
                indice = self.campos.indexOf(campo.name())

                if indice in self.precisoes:
                    precisao = self.precisoes[indice]
                    novo_campo.setPrecision(precisao)

                    # Garante largura suficiente no DBF.
                    largura = novo_campo.length()

                    if largura <= 0:
                        largura = 20

                    novo_campo.setLength(
                        max(largura, precisao + 12))

                return novo_campo

            def convert(self, indice, valor):
                if indice not in self.precisoes:
                    return valor

                if valor is None:
                    return valor

                try:
                    return round(
                        float(valor),
                        self.precisoes[indice])

                except (TypeError, ValueError):
                    return valor

            def clone(self):
                return ConversorPrecisao(self.campos, self.precisoes)

        conversor = ConversorPrecisao(layer.fields(), precisoes)

        options.fieldValueConverter = conversor

        # Retorna para manter o objeto vivo durante a exportação.
        return conversor

    def salvar_como_txt(self, layer, fileName, silencioso=True):
        """
        Exporta os atributos de uma camada vetorial para um arquivo TXT (tabulado).

        Funcionalidades:
        - Exporta apenas os campos da tabela de atributos (sem X/Y calculados).
        - Escreve a primeira linha como cabeçalho.
        - Salva cada feição como uma linha de valores separados por tabulação.
        - Retorna True em caso de sucesso, False em caso de falha.
        """
        try:
            # Obtém nomes dos campos da tabela de atributos
            fields = [f.name() for f in layer.fields()]

            # Abre arquivo TXT para escrita com delimitador de tabulação
            with open(fileName, "w", encoding="utf-8", newline="") as f:
                writer = csv.writer(f, delimiter="\t")

                # Escreve cabeçalho (nomes dos campos)
                writer.writerow(fields)

                # Escreve cada feição (apenas atributos)
                for feat in layer.getFeatures():
                    writer.writerow(feat.attributes())

            return True
        except Exception:
            return False

    def salvar_como_xlsx(self, layer, file_path, silencioso=True):
        """
        Exporta apenas a TABELA DE ATRIBUTOS de uma camada para XLSX,
        usando exclusivamente o xlsxwriter.
        """
        if layer is None or layer.type() != QgsMapLayer.LayerType.VectorLayer or not layer.isValid():
            return False

        fields = [f.name() for f in layer.fields()]  # cabeçalho = nomes dos atributos

        try:
            import xlsxwriter
            wb = xlsxwriter.Workbook(file_path)
            ws = wb.add_worksheet(self.tr("Dados"))

            # Cabeçalho
            for c, h in enumerate(fields):
                ws.write(0, c, h)

            # Dados
            r = 1
            for feat in layer.getFeatures():
                for c, v in enumerate(feat.attributes()):
                    ws.write(r, c, v)
                r += 1

            wb.close()
            return True
        except Exception:
            return False

    def _selecionar_formato_salvamento(self, parent=None):
        """
        Mostra um combo simples para o usuário escolher o FORMATO de saída.
        Retorna a extensão escolhida (ex.: ".gpkg") ou None se cancelar.
        """
        parent = parent or getattr(self, "dlg", None) or self.iface.mainWindow()

        opcoes = [
            (self.tr("GeoPackage (.gpkg)"), ".gpkg"),
            (self.tr("Shapefile (.shp)"), ".shp"),
            (self.tr("GeoJSON (.geojson)"), ".geojson"),
            (self.tr("KML (.kml)"), ".kml"),
            (self.tr("DXF (.dxf)"), ".dxf"),
            (self.tr("CSV (.csv)"), ".csv"),
            (self.tr("TXT (.txt)"), ".txt"),
            (self.tr("Excel (.xlsx)"), ".xlsx")]
        labels = [lbl for (lbl, _) in opcoes]
        mapa = {lbl: ext for (lbl, ext) in opcoes}

        label, ok = QInputDialog.getItem(parent, self.tr("Salvar antes de remover"), self.tr("Formato de arquivo:"), labels, 0, False)
        if not ok or not label:
            return None
        return mapa.get(label)

    def remover_camada_selecionada(self):
        """
        Remove a camada selecionada no treeView após verificar o estado de edição e as mudanças pendentes.
        Se houver alterações não salvas, pergunta e permite escolher o FORMATO para salvar
        usando salvar_no_formato_especifico(...).
        """
        # Índices selecionados (use a 1ª coluna se possível)
        selected_indexes = self.dlg.treeViewListaPonto.selectedIndexes()
        if not selected_indexes:
            self.mostrar_mensagem(self.tr("Selecione uma camada."), "Aviso")
            return
        idx = next((i for i in selected_indexes if i.column() == 0), selected_indexes[0])

        # Resolve a camada via UserRole
        layer_id = idx.model().itemFromIndex(idx).data(Qt.ItemDataRole.UserRole)
        layer_to_remove = QgsProject.instance().mapLayer(layer_id)
        if not layer_to_remove:
            self.mostrar_mensagem(self.tr("Camada não encontrada."), "Erro")
            return

        # Se tem edição pendente, pergunta
        if layer_to_remove.isEditable() and layer_to_remove.isModified():
            resposta = QMessageBox.question(
                self.dlg, self.tr("Confirmar Remoção"),
                self.tr("Existem alterações não salvas. Deseja salvar antes de remover?"),
                QMessageBox.StandardButton.Yes | QMessageBox.StandardButton.No | QMessageBox.StandardButton.Cancel,
                QMessageBox.StandardButton.Yes)

            if resposta == QMessageBox.StandardButton.Yes:
                # Escolhe o FORMATO
                ext = self._selecionar_formato_salvamento(parent=self.dlg)
                if not ext:
                    return  # usuário cancelou a escolha do formato

                # Usa diretamente a sua função pronta (abre o 'Salvar como...' e mostra mensagem)
                ok = self.salvar_no_formato_especifico(layer_to_remove, ext, nome_arquivo=None, silencioso=False)
                if not ok:
                    return  # cancelado ou falhou ao salvar

                # Fecha a edição e confirma alterações
                try:
                    if layer_to_remove.isEditable():
                        layer_to_remove.commitChanges()
                except Exception:
                    pass  # nosec B110

            elif resposta == QMessageBox.StandardButton.No:
                # Descarta alterações
                try:
                    layer_to_remove.rollBack()
                except Exception:
                    pass  # nosec B110
            else:
                return  # Cancel

        # Remove a camada do projeto
        QgsProject.instance().removeMapLayer(layer_id)

        # Limpeza e UI
        try:
            del layer_to_remove
            gc.collect()
        except Exception:
            pass  # nosec B110

        self.atualizar_treeView_lista_ponto()
        self.iface.mapCanvas().refresh()

    def renomear_camada_selecionada(self):
        """
        Permite ao usuário renomear uma camada de Ponto selecionado no treeViewListaPonto,
        garantindo unicidade do nome no projeto.

        Fluxo:
        - Obtém o índice selecionado.
        - Recupera a camada associada ao item (usando Qt.UserRole).
        - Exibe um diálogo para o usuário digitar o novo nome.
        - Garante que o nome será único (ajusta se necessário).
        - Atualiza o nome da camada no QGIS e o texto do item no treeView.
        """
        # Obtém os índices atualmente selecionados no treeView de pontos
        selected_indexes = self.dlg.treeViewListaPonto.selectedIndexes()
        if selected_indexes:
            # Pega o primeiro índice selecionado
            selected_index = selected_indexes[0]
            # Recupera o ID da camada usando o papel UserRole (garante que é o ID real da camada QGIS)
            layer_id = selected_index.model().itemFromIndex(selected_index).data(Qt.ItemDataRole.UserRole)
            # Busca a camada correspondente no projeto QGIS
            selected_layer = QgsProject.instance().mapLayer(layer_id)
            if selected_layer:
                # Exibe um diálogo para o usuário digitar o novo nome (pré-preenchido com o nome atual)
                novo_nome, ok = QInputDialog.getText(
                    self.dlg, self.tr( "Renomear Camada"),
                    self.tr("Digite o novo nome da camada:"),
                    text=selected_layer.name())
                # Se o usuário confirmou e digitou algo
                if ok and novo_nome:
                    # Gera um nome único para evitar duplicidade no projeto
                    novo_nome = self.gerar_nome_unico(novo_nome, selected_layer.id())
                    # Renomeia a camada no QGIS (isso pode disparar sinais que atualizam a interface automaticamente)
                    selected_layer.setName(novo_nome)
                    # Em vez de tentar alterar diretamente o item do modelo (risco de crash), reconstrói o treeView do zero
                    self.atualizar_treeView_lista_ponto()

    def _calc_next_id(self, layer, *, exclude_fid=None) -> int:
        """
        Calcula o próximo ID disponível (max(ID)+1) varrendo as feições da camada.
        exclude_fid: ignora uma feição específica (útil para não considerar a recém-criada).
        """
        idx_id = layer.fields().indexOf("ID")
        if idx_id == -1:
            return 1

        max_id = 0
        for f in layer.getFeatures():
            if exclude_fid is not None and f.id() == exclude_fid:
                continue
            try:
                v = f["ID"]
                if v is None or str(v).strip() == "":
                    continue
                iv = int(float(v))  # aceita 2.0, 3.00 etc.
                if iv > max_id:
                    max_id = iv
            except Exception:  # nosec B112
                continue

        return max_id + 1

    def _on_ponto_feature_added(self, layer, fid):
        """
        Slot para quando uma feição é adicionada na camada de pontos.

        - Garante que o campo ID não fique duplicado (caso de Copiar/Mover feições).
        - Se ID vier vazio ou repetido, sobrescreve com max(ID)+1.
        - Atualiza X/Y/DMS da feição recém-criada.
        """
        try:
            idx_id = layer.fields().indexOf("ID")
            if idx_id != -1:
                feat = layer.getFeature(fid)
                if feat and feat.isValid():
                    # valor atual do ID (pode vir copiado)
                    cur = feat["ID"]

                    # tenta converter para inteiro
                    cur_int = None
                    try:
                        if cur is not None and str(cur).strip() != "":
                            cur_int = int(float(cur))
                    except Exception:
                        cur_int = None

                    # detecta duplicidade (existe outra feição com mesmo ID?)
                    duplicado = False
                    if cur_int is not None:
                        for f in layer.getFeatures():
                            if f.id() == fid:
                                continue
                            try:
                                v = f["ID"]
                                if v is None or str(v).strip() == "":
                                    continue
                                if int(float(v)) == cur_int:
                                    duplicado = True
                                    break
                            except Exception:  # nosec B112
                                continue

                    # se vier vazio ou duplicado, força novo ID
                    if cur_int is None or duplicado:
                        novo_id = self._calc_next_id(layer, exclude_fid=fid)

                        # garante edição ativa (normalmente já está, mas por segurança)
                        if not layer.isEditable():
                            layer.startEditing()

                        layer.changeAttributeValue(fid, idx_id, int(novo_id))
        except Exception:
            pass  # nosec B110

        # Mantém o comportamento atual: atualizar X/Y/DMS ao adicionar
        try:
            self.atualizar_posicao_xy(layer, fid)
        except Exception:
            pass  # nosec B110

    def gerar_nome_unico(self, base_nome, current_layer_id):
        """
        Gera um nome único para uma camada de ponto dentro do projeto QGIS,
        assegurando que não haja conflitos de nomeação entre as camadas de pontos.

        Parâmetros:
        - base_nome (str): O nome base proposto para a camada.
        - current_layer_id (str): O ID da camada que está sendo renomeada, usado para excluir seu nome atual da verificação de duplicidade.

        Funcionalidades:
        - Cria um dicionário dos nomes de todas as camadas de pontos existentes no projeto QGIS, excluindo a camada que está sendo renomeada.
        - Verifica se o nome base já existe entre as camadas de pontos. Se não existir, retorna o nome base como válido.
        - Se o nome base já existir, gera variações do nome acrescentando um sufixo numérico (por exemplo, "Nome_1", "Nome_2") até encontrar um nome não utilizado.
        - Retorna o novo nome único gerado.
        """
        # Restringe apenas para camadas vetoriais de pontos
        existing_names = {layer.name(): layer.id()
            for layer in QgsProject.instance().mapLayers().values()
            if (layer.id() != current_layer_id and
                layer.type() == QgsMapLayer.LayerType.VectorLayer and
                layer.geometryType() == QgsWkbTypes.GeometryType.PointGeometry)}
        if base_nome not in existing_names:
            return base_nome
        else:
            i = 1
            novo_nome = f"{base_nome}_{i}"
            while novo_nome in existing_names:
                i += 1
                novo_nome = f"{base_nome}_{i}"
            return novo_nome

    def visualizar_ponto_selecionado(self):
        """
        Aproxima a visualização do mapa para a camada de ponto selecionada no treeView.

        Observação: ao criar/adicionar feições recentemente, a extensão (extent) pode ainda
        não estar atualizada. Por isso, forçamos updateExtents() e, se necessário, tentamos
        novamente no próximo ciclo da UI.
        """
        index = self.dlg.treeViewListaPonto.currentIndex()
        if not index.isValid():
            return

        item = index.model().itemFromIndex(index)
        if item is None:
            return

        # Pontos: pega o layer_id do UserRole (mesma lógica do polígono)
        layer_id = item.data(Qt.ItemDataRole.UserRole)
        layer = QgsProject.instance().mapLayer(layer_id)
        if not layer or not hasattr(layer, "extent"):
            return

        def _do_zoom():
            # Força atualização da extensão (camadas recém-criadas podem vir com extent vazio)
            try:
                layer.updateExtents()
            except Exception:
                pass  # nosec B110

            rect = layer.extent()
            if not rect or rect.isEmpty():
                return

            # Garante que a camada selecionada é a ativa antes de aplicar o zoom do QGIS
            self.iface.setActiveLayer(layer)
            self.iface.zoomToActiveLayer()

        # Tentativa imediata
        _do_zoom()

        # Se ainda estiver sem extent, tenta mais uma vez no próximo "tick" da UI
        try:
            layer.updateExtents()
        except Exception:
            pass  # nosec B110

        if layer.extent().isEmpty():
            QTimer.singleShot(0, _do_zoom)

    def configurar_tooltip(self, index):
        """
        Configura um tooltip para exibir informações sobre a camada de ponto selecionada no treeView.

        A função extrai informações sobre a camada de ponto, como o tipo de geometria (ex: Point, MultiPoint) 
        e o sistema de referência de coordenadas (SRC) atual da camada. Essas informações são exibidas em 
        um tooltip que aparece quando o usuário passa o mouse sobre o item correspondente no treeView.

        Parâmetros:
        - index: QModelIndex do item atualmente sob o cursor no treeView.
        """
        item = index.model().itemFromIndex(index)  # Obtém o item do modelo de dados com base no índice fornecido
        layer_id = item.data(Qt.ItemDataRole.UserRole)  # Obtém o ID da camada associada ao item
        layer = QgsProject.instance().mapLayer(layer_id)  # Recupera a camada correspondente ao ID no projeto QGIS
        if layer:  # Verifica se a camada existe
            tipo_ponto = self.obter_tipo_de_ponto(layer)  # Obtém o tipo de geometria da camada (ex: Point, MultiPoint)
            crs = layer.crs().description() if layer.crs().isValid() else self.tr("Sem Georreferenciamento")  # Obtém a descrição do SRC da camada ou "Sem Georreferenciamento" se inválido
            tooltip_text = self.tr("Tipo: {tipo_ponto}\nSRC: {crs}").format(tipo_ponto=tipo_ponto, crs=crs) # Formata o texto do tooltip com as informações da camada
            QToolTip.showText(QCursor.pos(), tooltip_text)  # Exibe o tooltip na posição atual do cursor

    def obter_tipo_de_ponto(self, layer):
        """
        Retorna uma string que descreve o tipo de geometria da camada fornecida.

        A função obtém o tipo de geometria WKB (Well-Known Binary) da camada e converte esse tipo
        em uma string legível, como 'Point', 'MultiPoint', etc.

        Parâmetros:
        - layer: Objeto QgsVectorLayer representando a camada de onde o tipo de ponto será extraído.

        Retorno:
        - tipo_ponto (str): Uma string que descreve o tipo de geometria da camada.
        """
        geometry_type = layer.wkbType()  # Obtém o tipo de geometria WKB (Well-Known Binary) da camada
        tipo_ponto = QgsWkbTypes.displayString(geometry_type)  # Converte o tipo de geometria em uma string legível
        return tipo_ponto  # Retorna a string que descreve o tipo de geometria

    def _ativar_ferramenta_adicionar_ponto(self, layer):
        """
        Ativa a camada criada e inicia a ferramenta nativa
        de adicionar feições de ponto.

        Faz novas tentativas caso a interface do QGIS ainda
        não tenha terminado de atualizar a camada.
        """
        if (not isinstance(layer, QgsVectorLayer)
            or not layer.isValid()
            or layer.geometryType() != QgsWkbTypes.GeometryType.PointGeometry):
            return

        layer_id = layer.id()

        def ativar(tentativa=0):
            camada = QgsProject.instance().mapLayer(layer_id)

            if (not isinstance(camada, QgsVectorLayer)
                or not camada.isValid()):
                return

            # Garante modo de edição
            if not camada.isEditable():
                try:
                    camada.startEditing()
                except Exception:
                    pass  # nosec B110

            # Torna a camada ativa no QGIS
            try:
                self.iface.setActiveLayer(camada)
            except Exception:
                pass  # nosec B110

            # Seleciona também no painel de camadas do QGIS
            try:
                self.iface.layerTreeView().setCurrentLayer(camada)
            except Exception:
                pass  # nosec B110

            # Seleciona explicitamente a nova camada
            # no TreeView de pontos do plugin
            try:
                self.on_current_layer_changed(camada)
            except Exception:
                pass  # nosec B110

            QCoreApplication.processEvents()

            try:
                action = self.iface.actionAddFeature()
            except Exception:
                action = None

            if action is not None and action.isEnabled():
                try:
                    # Evita disparar novamente caso já esteja ativa
                    if not action.isChecked():
                        action.trigger()
                except Exception:
                    action.trigger()

                return

            # A interface ainda não terminou de preparar a camada
            if tentativa < 4:
                QTimer.singleShot(75, lambda: ativar(tentativa + 1))

        # Aguarda o TreeView e o painel de camadas se estabilizarem
        QTimer.singleShot(0, ativar)

    def adicionar_camada_e_atualizar(self):
        """
        Cria uma camada de pontos e já ativa
        a ferramenta Adicionar Ponto.
        """
        layer = self.pontos_manager.criar_camada_pontos()

        if not layer or not layer.isValid():
            return

        self._garantir_tratamento_camada_ponto(layer)
        self.atualizar_treeView_lista_ponto()

        self._ativar_ferramenta_adicionar_ponto(layer)

    def abrir_caixa_nome_camada(self):
        """
        Abre o diálogo para informar:

        - nome da camada;
        - cor opcional dos pontos;
        - SRC opcional da camada.
        """
        dialog = QDialog(self.dlg)
        dialog.setWindowTitle(self.tr("Nome da Camada"))

        layout = QVBoxLayout(dialog)

        # Frame principal
        frame = QFrame()
        frame.setFrameShape(QFrame.Shape.Box)
        frame.setFrameShadow(QFrame.Shadow.Raised)

        frame_layout = QVBoxLayout(frame)
        frame_layout.setContentsMargins(8, 8, 8, 8)
        frame_layout.setSpacing(6)

        # Nome da camada
        frame_layout.addWidget(QLabel(self.tr("Digite o nome da camada:")))

        lineEdit = QLineEdit()
        lineEdit.setText(self.tr("Pontos Temporários"))
        frame_layout.addWidget(lineEdit)

        QTimer.singleShot(0, lambda: (lineEdit.setFocus(), lineEdit.selectAll()))

        # Botões Cor e SRC
        layout_opcoes = QHBoxLayout()
        layout_opcoes.setSpacing(6)

        pushButtonCor = QPushButton(self.tr("Escolher Cor"))
        pushButtonCrs = QPushButton(self.tr("Projetar SRC"))

        layout_opcoes.addWidget(pushButtonCor)
        layout_opcoes.addWidget(pushButtonCrs)

        frame_layout.addLayout(layout_opcoes)

        # Opção para adicionar pontos sem abrir o formulário de atributos
        checkBoxNaoExibirDialogo = QCheckBox(self.tr("Não exibir diálogo de atributos"))
        checkBoxNaoExibirDialogo.setChecked(False)
        checkBoxNaoExibirDialogo.setToolTip(self.tr("Quando marcado, os pontos serão adicionados sem abrir o formulário de atributos."))

        frame_layout.addWidget(checkBoxNaoExibirDialogo)

        layout.addWidget(frame)

        # Valores opcionais escolhidos pelo usuário
        cor_preenchimento_selecionada = None
        cor_borda_selecionada = None
        crs_selecionado = None

        # Escolher cor
        def escolher_cor():
            nonlocal cor_preenchimento_selecionada
            nonlocal cor_borda_selecionada

            cor_inicial_preenchimento = (
                cor_preenchimento_selecionada
                if isinstance(cor_preenchimento_selecionada, QColor)
                else QColor(255, 255, 255))

            cor_inicial_borda = (cor_borda_selecionada
                if isinstance(cor_borda_selecionada, QColor)
                else QColor(0, 0, 0) )

            nova_cor_preenchimento, nova_cor_borda = (self.prompt_for_new_colors(cor_inicial_preenchimento, cor_inicial_borda, parent=dialog))

            # Mesmo comportamento do treeView:
            # cancelar os dois = nenhuma alteração
            if (nova_cor_preenchimento is None
                and nova_cor_borda is None):
                return

            cor_preenchimento_selecionada = QColor(nova_cor_preenchimento)

            cor_borda_selecionada = QColor( nova_cor_borda)

            fundo = ("transparent"
                if cor_preenchimento_selecionada.alpha() == 0
                else cor_preenchimento_selecionada.name())

            borda = ("transparent"
                if cor_borda_selecionada.alpha() == 0
                else cor_borda_selecionada.name())

            cor_texto = ("#000000"
                if cor_preenchimento_selecionada.alpha() == 0
                or cor_preenchimento_selecionada.lightness() > 150
                else "#ffffff")

            pushButtonCor.setStyleSheet(
                "QPushButton {"
                f"background-color: {fundo};"
                f"border: 3px solid {borda};"
                f"color: {cor_texto};"
                "}")

            texto_preenchimento = (self.tr("Transparente")
                if cor_preenchimento_selecionada.alpha() == 0
                else cor_preenchimento_selecionada.name().upper())

            texto_borda = (self.tr("Transparente")
                if cor_borda_selecionada.alpha() == 0
                else cor_borda_selecionada.name().upper())

            pushButtonCor.setToolTip(self.tr(
                    "Preenchimento: {fill}\n"
                    "Borda: {border}").format(fill=texto_preenchimento,
                    border=texto_borda))

        # Conecta o botão à função de seleção das duas cores
        pushButtonCor.clicked.connect(escolher_cor)

        # Escolher SRC
        def escolher_crs():
            nonlocal crs_selecionado

            dialog_crs = QgsProjectionSelectionDialog(dialog)

            crs_inicial = (crs_selecionado
                if isinstance(crs_selecionado,
                    QgsCoordinateReferenceSystem)
                and crs_selecionado.isValid()
                else QgsProject.instance().crs())

            dialog_crs.setCrs(crs_inicial)

            if dialog_crs.exec() != QDialog.DialogCode.Accepted:
                return

            novo_crs = dialog_crs.crs()

            if not novo_crs.isValid():
                return

            crs_selecionado = QgsCoordinateReferenceSystem(novo_crs)

            texto_crs = (novo_crs.authid()
                or novo_crs.description())

            pushButtonCrs.setText(texto_crs)

            pushButtonCrs.setToolTip(self.tr("{authid} - {description}").format(authid=novo_crs.authid(), description=novo_crs.description()))

        pushButtonCrs.clicked.connect(escolher_crs)

        # Botões Adicionar e Cancelar
        okButton = QPushButton(self.tr("Adicionar"))
        cancelButton = QPushButton(self.tr("Cancelar"))

        okButton.setEnabled(bool(lineEdit.text().strip()))

        lineEdit.textChanged.connect(lambda texto: okButton.setEnabled(bool(texto.strip())))

        buttonLayout = QHBoxLayout()
        buttonLayout.addWidget(okButton)
        buttonLayout.addWidget(cancelButton)

        layout.addLayout(buttonLayout)

        okButton.clicked.connect(dialog.accept)
        cancelButton.clicked.connect(dialog.reject)

        # Criação da camada
        if dialog.exec() != QDialog.DialogCode.Accepted:
            return

        nome_camada = lineEdit.text().strip()

        if not nome_camada:
            return

        # Se o usuário não escolher SRC, o manager usará
        # automaticamente o SRC atual do projeto.
        layer = self.pontos_manager.criar_camada_pontos(nome_camada=nome_camada, cor_preenchimento=cor_preenchimento_selecionada, cor_borda=cor_borda_selecionada, crs=crs_selecionado)

        if not layer or not layer.isValid():
            self.mostrar_mensagem(self.tr("Não foi possível criar a camada de pontos."), "Erro")

            return

        self._garantir_tratamento_camada_ponto(layer)
        self.atualizar_treeView_lista_ponto()

        # Configura a exibição do formulário apenas para esta camada
        try:
            cfg = layer.editFormConfig()

            if checkBoxNaoExibirDialogo.isChecked():
                try:
                    cfg.setSuppress(Qgis.AttributeFormSuppression.On)
                except Exception:
                    cfg.setSuppress(QgsEditFormConfig.FeatureFormSuppress.SuppressOn)
            else:
                try:
                    cfg.setSuppress(Qgis.AttributeFormSuppression.Off)
                except Exception:
                    cfg.setSuppress(QgsEditFormConfig.FeatureFormSuppress.SuppressOff)

            layer.setEditFormConfig(cfg)

        except Exception:
            pass  # nosec B110

        # Ativa a ferramenta somente depois de configurar o formulário
        self._ativar_ferramenta_adicionar_ponto(layer)

    def close_dialog(self):
        """
        Fecha o diálogo associado a este UiManagerT:
        """
        self.dlg.close()

    def _garantir_tratamento_camada_ponto(self, layer):
        """
        Aplica o tratamento automático às camadas de ponto criadas/adicionadas.

        Esse tratamento conecta os sinais que atualizam ID, X, Y, X_DMS e
        Y_DMS. Os nomes dos campos devem permanecer técnicos e fixos, sem
        tradução, porque outros métodos procuram exatamente por esses nomes.
        """
        if (not layer
            or layer.type() != QgsMapLayer.LayerType.VectorLayer
            or layer.geometryType() != QgsWkbTypes.GeometryType.PointGeometry):
            return

        layer_id = layer.id()
        if layer_id in self._camadas_ponto_tratadas:
            return

        campos_obrigatorios = {"ID", "X", "Y"}
        campos_layer = {field.name() for field in layer.fields()}

        if not campos_obrigatorios.issubset(campos_layer):
            return

        self.tratar_pontos(layer)
        self._camadas_ponto_tratadas.add(layer_id)

    def _on_layer_will_be_removed(self, layer_id):
        """
        Remove do TreeView **apenas** se a camada que vai sair
        for vetor de pontos.
        """
        layer = QgsProject.instance().mapLayer(layer_id)
        if not layer:
            return  # segurança

        if layer.type() != QgsMapLayer.LayerType.VectorLayer or layer.geometryType() != QgsWkbTypes.GeometryType.PointGeometry:
            # não é ponto → ignoramos
            return

        # Remove a linha correspondente no modelo
        for row in range(self.treeViewModel.rowCount()):
            item = self.treeViewModel.item(row)
            if item and item.data(Qt.ItemDataRole.UserRole) == layer_id:
                self.treeViewModel.removeRow(row)
                break

        # Garante que fique alguma seleção válida
        model = self.dlg.treeViewListaPonto.model()
        if model.rowCount() > 0 and not self.dlg.treeViewListaPonto.currentIndex().isValid():
            target_row = min(row, model.rowCount() - 1)
            idx = model.index(target_row, 0)
            self.dlg.treeViewListaPonto.setCurrentIndex(idx)
            self.dlg.treeViewListaPonto.scrollTo(idx)

        # Chama atualização dos botões após toda modificação
        self.atualizar_estado_botoes()

    def abrir_dialogo_crs(self):
        """
        Abre um diálogo de seleção de CRS e reprojeta a camada de pontos selecionada no treeViewListaPonto.

        A função permite ao usuário escolher um novo sistema de referência de coordenadas (SRC) para a camada 
        selecionada no treeViewListaPonto. Após a seleção, a camada é reprojetada usando o novo SRC, e a nova camada é 
        adicionada ao projeto QGIS com a mesma cor de ícone e rótulo da camada original.

        Parâmetros:
        - self: Referência à instância atual do objeto. (UiManagerT)

        A função não retorna valores, mas adiciona uma nova camada reprojetada ao projeto QGIS.
        """
        index = self.dlg.treeViewListaPonto.currentIndex()  # Obtém o índice atualmente selecionado no treeViewListaPonto
        if not index.isValid():  # Verifica se o índice é válido (se há uma seleção)
            return  # Sai da função se o índice não for válido
        
        layer_id = index.model().itemFromIndex(index).data(Qt.ItemDataRole.UserRole)  # Obtém o ID da camada associada ao item selecionado
        layer = QgsProject.instance().mapLayer(layer_id)  # Recupera a camada correspondente ao ID no projeto QGIS
        if not layer or layer.geometryType() != QgsWkbTypes.GeometryType.PointGeometry:  # Verifica se a camada existe e é de pontos
            self.mostrar_mensagem(self.tr("Por favor, selecione uma camada de pontos válida."), "Aviso")  # Exibe uma mensagem de aviso
            return  # Sai da função se a camada não for de pontos
        
        # Abre o diálogo de seleção de CRS para que o usuário possa escolher um novo SRC
        dialog = QgsProjectionSelectionDialog(self.dlg)  # Cria uma instância do diálogo de seleção de CRS
        dialog.setCrs(layer.crs())  # Configura o CRS atual da camada como o CRS padrão no diálogo
        if dialog.exec():  # Exibe o diálogo e verifica se o usuário confirmou a seleção
            novo_crs = dialog.crs()  # Obtém o novo CRS selecionado pelo usuário

            # Usa o processamento do QGIS para reprojetar a camada
            params = {
                'INPUT': layer,  # Define a camada original como entrada
                'TARGET_CRS': novo_crs,  # Define o novo CRS como o CRS alvo
                'OUTPUT': 'memory:'}  # Salva o resultado na memória

            resultado = processing.run('qgis:reprojectlayer', params)  # Executa o processo de reprojeção
            nova_camada = resultado['OUTPUT']  # Obtém a nova camada reprojetada a partir dos resultados

            # Verifique se a nova camada tem feições válidas
            if nova_camada and nova_camada.isValid():  # Verifica se a nova camada foi criada corretamente
                # Gerar nome único para a nova camada reprojetada
                novo_nome = self.gerar_nome_unico_rep(layer.name())  # Gera um nome único para evitar duplicidades
                nova_camada.setName(novo_nome)  # Define o nome da nova camada

                # Aplicar as cores do ícone e do rótulo da camada original
                cor_icone = self.obter_cor_icone(layer)  # Obtém a cor do ícone da camada original
                cor_rotulo = self.obter_cor_rotulo(layer)  # Obtém a cor do rótulo da camada original

                QgsProject.instance().addMapLayer(nova_camada)  # Adiciona a nova camada reprojetada ao projeto

                try:
                    root = QgsProject.instance().layerTreeRoot()
                    node = root.findLayer(nova_camada.id())
                    if node:
                        node.setItemVisibilityChecked(True)
                except Exception:
                    pass  # nosec B110

                QTimer.singleShot(0, self.sync_from_qgis_to_treeview)

                # Copiar estilo (simbologia + rótulos) da camada original
                copiou_estilo = False
                try:
                    # Método recomendado: captura o estilo inteiro da camada e aplica na nova
                    estilo = QgsMapLayerStyle()
                    if estilo.readFromLayer(layer):
                        estilo.writeToLayer(nova_camada)
                        copiou_estilo = True
                except Exception:
                    copiou_estilo = False

                if not copiou_estilo:
                    # Fallback: clonar renderer e labeling manualmente
                    try:
                        if layer.renderer():
                            nova_camada.setRenderer(layer.renderer().clone())
                        if layer.labelsEnabled() and layer.labeling():
                            nova_camada.setLabeling(layer.labeling().clone())
                            nova_camada.setLabelsEnabled(True)
                        # Copia também ajustes visuais úteis
                        if hasattr(layer, "opacity"):
                            nova_camada.setOpacity(layer.opacity())
                        if hasattr(layer, "blendMode"):
                            nova_camada.setBlendMode(layer.blendMode())
                    except Exception:
                        pass  # nosec B110

                # Força atualização visual
                try:
                    nova_camada.triggerRepaint()
                    self.iface.layerTreeView().refreshLayerSymbology(nova_camada.id())
                except Exception:
                    pass  # nosec B110

                # Atualiza a camada na tela
                layer.triggerRepaint()  # Recarrega a camada original (caso necessário)
                self.iface.mapCanvas().refresh()  # Atualiza a tela do mapa para refletir a nova camada

                # Exibe uma mensagem informando que a camada foi reprojetada
                if nova_camada and nova_camada.isValid():
                    texto_mensagem = self.tr("A camada '{layer_name}' foi reprojetada para {crs_authid} ({crs_description}) com o nome '{novo_nome}'.").format(layer_name=layer.name(), crs_authid=novo_crs.authid(), crs_description=novo_crs.description(), novo_nome=novo_nome)
                    self.mostrar_mensagem(texto_mensagem, "Sucesso")
                else:
                    self.mostrar_mensagem(self.tr("Erro na reprojeção da camada '{layer_name}'.").format(layer_name=layer.name()), "Erro")

    def gerar_nome_unico_rep(self, base_nome):
        """
        Gera um nome único para uma nova camada baseada no nome da camada original.

        A função cria um novo nome para a camada reprojetada, adicionando um sufixo incremental 
        (_rep1, _rep2, etc.) ao nome base, garantindo que o novo nome seja único dentro do projeto QGIS.

        Parâmetros:
        - self: Referência à instância atual do objeto. (UiManager)
        - base_nome (str): O nome original da camada, usado como base para gerar o novo nome.

        Retorno:
        - novo_nome (str): Um nome único gerado para a nova camada reprojetada.
        """
        # Cria um conjunto contendo todos os nomes de camadas existentes no projeto QGIS
        existing_names = {layer.name() for layer in QgsProject.instance().mapLayers().values()}

        # Se o nome base ainda não existir no projeto, retorna com o sufixo _rep1
        if base_nome not in existing_names:
            return f"{base_nome}_rep1"
        # Inicia o contador de sufixos em 1
        i = 1
        # Gera o primeiro nome com o sufixo _rep1
        novo_nome = f"{base_nome}_rep{i}"

        # Incrementa o sufixo até encontrar um nome que não exista no projeto
        while novo_nome in existing_names:
            i += 1
            novo_nome = f"{base_nome}_rep{i}"
        # Retorna o nome único gerado
        return novo_nome

    def on_treeview_selection_changed(self, selected, deselected):
        """
        Define a camada ativa no QGIS com base na seleção do TreeView.

        Funcionalidades:
        - Acessa os índices selecionados no TreeView.
        - Recupera o ID da camada associado ao item selecionado.
        - Define a camada correspondente como ativa no QGIS (iface.setActiveLayer).
        """
        # Obtém os índices selecionados no TreeView
        indexes = self.dlg.treeViewListaPonto.selectionModel().selectedIndexes()
        if indexes:
            # Recupera o ID da camada a partir do primeiro item selecionado
            layer_id = self.treeViewModel.itemFromIndex(indexes[0]).data(Qt.ItemDataRole.UserRole)
            # Obtém a camada no projeto QGIS através do ID
            layer = QgsProject.instance().mapLayer(layer_id)
            if layer:
                # Define a camada como ativa no QGIS
                self.iface.setActiveLayer(layer)

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

        model = self.dlg.treeViewListaPonto.model()
        if model is None:
            return

        target_id = layer_tree_layer.layerId()
        desired = (
            Qt.CheckState.Checked
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

    def layers_added(self, layers):
        """
        Atualiza o treeView quando novas camadas de ponto são adicionadas ao projeto,
        aguardando um ciclo da UI para o nó da árvore do QGIS estabilizar.
        """
        point_layers = [
            layer for layer in layers
            if layer.type() == QgsMapLayer.LayerType.VectorLayer
            and layer.geometryType() == QgsWkbTypes.GeometryType.PointGeometry]

        if not point_layers:
            return

        for layer in point_layers:
            try:
                layer.nameChanged.disconnect(self.on_layer_name_changed)
            except TypeError:
                pass  # nosec B110

            layer.nameChanged.connect(self.on_layer_name_changed)
            self._garantir_tratamento_camada_ponto(layer)

        def _refresh_after_qgis_tree_settles():
            self.atualizar_treeView_lista_ponto()
            self.sync_from_qgis_to_treeview()

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
        self.atualizar_treeView_lista_ponto()

    def abrir_dialogo_selecao_campos_ponto(self):
        """
        Abre o diálogo de gerenciamento de etiquetas para a camada de pontos selecionada em treeViewListaPonto.

        Detalhamento do Processo:
        1. Coleta os índices atualmente selecionados no QTreeView de pontos.
        2. Se não houver seleção, retorna imediatamente (nenhuma ação).
        3. Garante que usamos sempre a coluna 0 do modelo, onde está armazenado o ID da camada.
        4. Lê o ID da camada selecionada através de Qt.UserRole (não confundir com o texto do item).
        5. Recupera a camada no projeto QGIS usando este ID.
        6. Verifica se a camada existe e se sua geometria é do tipo ponto; caso contrário, aborta.
        7. Instancia o diálogo GerenciarEtiquetasDialog, passando:
           - a camada de pontos,
           - os dicionários de cores e visibilidade (stateful),
           - a interface QGIS (iface),
           - e o próprio diálogo principal como parent.
        8. Exibe o diálogo de forma modal com `exec_()`, permitindo ao usuário selecionar campos e cores.
        9. Ao fechar, quaisquer alterações de etiquetas ficam aplicadas na camada.

        Esta função facilita a configuração de etiquetas para pontos, reutilizando a mesma UI
        originalmente criada para pontos/linhas, mas validando geometria de ponto.
        """
        # 1) Obter todos os índices selecionados no treeView de pontos
        selected_indexes = self.dlg.treeViewListaPonto.selectedIndexes()
        # 2) Se não há seleção, interrompe aqui
        if not selected_indexes:
            return

        # 3) Garante uso da coluna zero onde o ID está armazenado
        idx = selected_indexes[0].sibling(selected_indexes[0].row(), 0)

        # 4) Extrai o ID da camada a partir do papel Qt.UserRole
        layer_id = idx.model().itemFromIndex(idx).data(Qt.ItemDataRole.UserRole)

        # 5) Busca a camada no projeto QGIS pelo ID
        layer = QgsProject.instance().mapLayer(layer_id)
        # 6) Verifica existência e tipo de geometria (ponto)
        if not layer or layer.geometryType() != QgsWkbTypes.GeometryType.PointGeometry:
            return

        # 7) Cria o diálogo de gerenciamento de etiquetas
        dialog = GerenciarEtiquetasDialog(
            layer,
            self.fieldColors,       # dicionário que mapeia campos→cores
            self.fieldVisibility,   # dicionário que mapeia campos→visibilidade
            self.iface,             # interface do QGIS
            self.dlg)                # diálogo principal como parent

        # 8) Exibe o diálogo de forma modal, bloqueando até o usuário fechar
        dialog.exec()

    def adjust_item_font(self, item, layer):
        """
        Ajusta a fonte do item no QTreeView com base no tipo de fonte de dados da camada associada.
        Este método modifica a fonte para itálico se a camada for temporária (em memória) e para negrito se for permanente.

        A visualização visual das camadas como itálicas ou negritas ajuda o usuário a identificar rapidamente
        o tipo de camada (temporária vs. permanente) diretamente pela interface do usuário.

        :param item: O item no QTreeView que representa uma camada no QGIS.
        :param layer: A camada do QGIS associada ao item no QTreeView.

        :return: Retorna o item com a fonte ajustada.

        Funções e Ações Desenvolvidas:
        - Configuração da fonte para itálico se a fonte de dados da camada for 'memory' (temporária).
        - Configuração da fonte para negrito se a fonte de dados da camada for permanente.
        """
        # Cria um objeto QFont para ajustar a fonte do item
        fonte_item = QFont()

        # Verifica se a camada é temporária (dados em memória) e ajusta a fonte para itálico
        if layer.dataProvider().name() == 'memory':
            fonte_item.setItalic(True)
        # Se não for temporária, ajusta a fonte para negrito, indicando uma camada permanente
        else:
            fonte_item.setBold(True)

        # Aplica a fonte ajustada ao item no QTreeView
        item.setFont(fonte_item)

        # Retorna o item com a fonte ajustada para uso posterior se necessário
        return item

    def atualizar_treeView_lista_ponto(self):
        """
        Atualiza o TreeView que lista as camadas de pontos no QGIS.

        Funcionalidades:
        1) Salva o ID da camada atualmente selecionada no TreeView, se houver.
        2) Limpa e reconstrói o modelo do TreeView:
           - Define o cabeçalho centralizado.
           - Itera sobre todas as camadas do projeto e adiciona ao modelo apenas as camadas vetoriais de pontos.
           - Para cada camada encontrada:
             * Cria um item com o nome da camada.
             * Torna o item checkable para controlar visibilidade.
             * Define flags para impedir edição direta do texto.
             * Armazena o ID único da camada no Qt.UserRole.
             * Ajusta o estado do checkbox de acordo com a visibilidade atual da camada no projeto.
             * Formata a fonte do item (itálico para memória, negrito para outras).
        3) Tenta restaurar a seleção anterior, buscando no modelo o item cujo ID corresponda ao salvo.
        4) Caso não haja seleção anterior ou a camada não exista mais, seleciona o primeiro item do modelo.
        5) Move o scroll para garantir que o item selecionado esteja visível.
        """
        # 1) Salva o ID da camada atualmente selecionada, se houver
        current_layer_id = None  # Armazena o layer.id() da seleção atual
        current_index = self.dlg.treeViewListaPonto.currentIndex()  # Índice selecionado no TreeView
        if current_index.isValid():  # Verifica se há uma seleção válida
            # Extrai o ID da camada do dado armazenado em Qt.UserRole
            current_layer_id = current_index.model().itemFromIndex(current_index).data(Qt.ItemDataRole.UserRole)

        # 2) Reconstrói o modelo do TreeView
        self.treeViewModel.clear()  # Limpa todos os itens existentes no modelo

        # Configura o cabeçalho da coluna com alinhamento central
        headerItem = QStandardItem(self.tr("Lista de Camadas de Pontos"))  # Título do cabeçalho
        headerItem.setTextAlignment(Qt.AlignmentFlag.AlignCenter)  # Centraliza o texto
        self.treeViewModel.setHorizontalHeaderItem(0, headerItem)  # Aplica o cabeçalho

        # Pega a raiz da árvore de camadas do QGIS para verificar visibilidade
        root = QgsProject.instance().layerTreeRoot()
        # Itera por todas as camadas do projeto
        for layer in QgsProject.instance().mapLayers().values():
            # Seleciona apenas camadas vetoriais do tipo pontos
            if (
                layer.type() == QgsMapLayer.LayerType.VectorLayer
                and layer.geometryType() == QgsWkbTypes.GeometryType.PointGeometry):
                item = QStandardItem(layer.name())  # Cria o item com o nome da camada
                item.setCheckable(True)  # Permite marcar/desmarcar para visibilidade
                # Remove flag de edição para impedir alteração do nome pelo usuário
                item.setEditable(False)
                # Armazena o ID da camada no item para referência futura
                item.setData(layer.id(), Qt.ItemDataRole.UserRole)

                # Ajusta o estado inicial do checkbox baseado na visibilidade da camada
                item.setCheckState(
                    Qt.CheckState.Checked
                    if self.camada_esta_visivel(layer)
                    else Qt.CheckState.Unchecked)

                # Aplica formatação de fonte: itálico para memória, negrito para outras
                self.adjust_item_font(item, layer)
                # Adiciona o item ao modelo, criando uma nova linha
                self.treeViewModel.appendRow(item)

        # 3) Restaura a seleção anterior, se possível
        model = self.dlg.treeViewListaPonto.model()  # Modelo atualizado
        target_index = None  # Índice que será selecionado

        if current_layer_id:
            # Busca pelo item que tenha o mesmo ID salvo anteriormente
            for row in range(model.rowCount()):
                item = model.item(row)
                if item and item.data(Qt.ItemDataRole.UserRole) == current_layer_id:
                    target_index = model.indexFromItem(item)
                    break  # Interrompe ao encontrar a correspondência

        # 4) Se não houver seleção anterior (ou não encontrada), seleciona o primeiro item
        if target_index is None and model.rowCount() > 0:
            target_index = model.index(0, 0)  # Pega a primeira linha do modelo

        # 5) Aplica a seleção e move o scroll para exibir o item
        if target_index is not None:
            self.dlg.treeViewListaPonto.setCurrentIndex(target_index)  # Seleciona
            self.dlg.treeViewListaPonto.scrollTo(target_index)  # Move o scroll

        # Chama atualização dos botões após toda modificação
        self.atualizar_estado_botoes()
        self.sync_from_qgis_to_treeview()

    def on_current_layer_changed(self, layer):
        """
        Atualiza a seleção do treeView quando a camada ativa do QGIS muda.

        Funcionalidades:
        - Verifica se a nova camada ativa é uma camada vetorial de pontos.
        - Percorre o modelo do treeView para encontrar o item correspondente ao ID da nova camada.
        - Se encontrar, seleciona e rola até o item correspondente no treeView.

        Parâmetro:
        - layer (QgsMapLayer): Nova camada ativa no QGIS.
        """
        # Obtém o modelo associado ao treeView de pontos
        model = self.dlg.treeViewListaPonto.model()

        # Verifica se a camada é válida, do tipo vetorial e com geometria de ponto
        if layer and layer.type() == QgsMapLayer.LayerType.VectorLayer and layer.geometryType() == QgsWkbTypes.GeometryType.PointGeometry:
            layer_id = layer.id()  # Obtém o ID único da camada

            # Percorre as linhas do modelo do treeView
            for row in range(model.rowCount()):
                item = model.item(row, 0)

                # Verifica se o item corresponde ao ID da camada ativa
                if item and item.data(Qt.ItemDataRole.UserRole) == layer_id:
                    index = model.indexFromItem(item)

                    # Define a seleção atual e rola até a linha correspondente
                    self.dlg.treeViewListaPonto.setCurrentIndex(index)
                    self.dlg.treeViewListaPonto.scrollTo(index)
                    break  # Encerra após encontrar a camada correspondente

    def on_layer_was_renamed(self, layerId, newName):
        """
        Responde ao evento de renomeação de uma camada no QGIS, atualizando o nome da camada no QTreeView.
        Este método garante que as mudanças de nome no projeto sejam refletidas na interface do usuário.

        :param layerId: ID da camada que foi renomeada.
        :param newName: Novo nome atribuído à camada.

        Funções e Ações Desenvolvidas:
        - Pesquisa no modelo do QTreeView pelo item que corresponde à camada renomeada.
        - Atualização do texto do item no QTreeView para refletir o novo nome.
        """
        # Itera sobre todos os itens no modelo do QTreeView para encontrar o item correspondente
        for i in range(self.treeViewModel.rowCount()):
            item = self.treeViewModel.item(i)
            layer = QgsProject.instance().mapLayer(layerId)
            # Verifica se o item corresponde à camada que foi renomeada
            if layer and item.text() == layer.name():
                item.setText(newName)  # Atualiza o nome do item no QTreeView
                break  # Sai do loop após atualizar o nome

    def prompt_for_new_colors(self, current_fill_color, current_border_color, parent=None):
        """
        Fluxo de seleção de cores para PONTOS:
          • Cancela borda       → borda transparente (segue para preenchimento).
          • Cancela preenchimento → preenchimento transparente (aplica borda).
          • Cancela AMBOS       → (None, None) ⇒ chamador não altera nada.
          • Se escolher nova cor de preenchimento e o alpha atual for 0,
            força alpha 255 (slider volta a 100%); caso contrário, mantém alpha atual.
        """
        parent = (parent
            or getattr(self, "dlg", None)
            or self.iface.mainWindow())

        # 1) Diálogo da BORDA
        border_qc = QColorDialog.getColor(current_border_color, parent, self.tr("Escolha a Cor da Borda"))
        border_valid = border_qc.isValid()
        new_border = border_qc if border_valid else QColor(0, 0, 0, 0)  # transparente

        # 2) Diálogo do PREENCHIMENTO
        fill_qc = QColorDialog.getColor(current_fill_color, parent, self.tr("Escolha a Cor de Preenchimento"))
        fill_valid = fill_qc.isValid()

        # 3) Ambos cancelados ⇒ nenhuma alteração
        if not border_valid and not fill_valid:
            return None, None

        # 4) Preenchimento: ajusta alpha se necessário
        if fill_valid:
            current_alpha = current_fill_color.alpha() if current_fill_color is not None else 255
            fill_qc.setAlpha(255 if current_alpha == 0 else current_alpha)
            new_fill = fill_qc
        else:
            new_fill = QColor(0, 0, 0, 0)  # transparente

        return new_fill, new_border

    def get_point_colors(self, layer):
        """
        Retorna (fill_color, border_color) da camada de PONTOS.
        Usa outlineColor/outlineWidth (QgsSimpleMarkerSymbolLayer) com fallback para stroke*.
        """
        symbols = layer.renderer().symbols(QgsRenderContext())
        if not symbols:
            return None, None

        sym = symbols[0]
        fill_color = sym.color()
        border_color = Qt.GlobalColor.black

        try:
            sl = sym.symbolLayer(0)
            if sl:
                if hasattr(sl, "outlineColor"):
                    border_color = sl.outlineColor()
                elif hasattr(sl, "strokeColor"):
                    border_color = sl.strokeColor()
        except Exception:
            pass  # nosec B110

        return fill_color, border_color

    def apply_new_colors(self, layer, fill_color, border_color):
        """
        Altera SOMENTE as cores do símbolo de PONTOS, preservando:
        - tamanho do marcador,
        - largura de contorno,
        - unidade/escala de tamanho,
        - demais propriedades já configuradas.
        """
        try:
            renderer = layer.renderer()
            sym = None

            # 1) Preferir clonar o símbolo atual (preserva tudo automaticamente)
            if isinstance(renderer, QgsSingleSymbolRenderer):
                sym = renderer.symbol().clone()

            # 2) Fallback raro: cria símbolo novo, mas copia tamanho/largura do atual
            size = unit = scale = width = None
            if sym is None:
                cur_syms = renderer.symbols(QgsRenderContext())
                if cur_syms:
                    cur_sl = cur_syms[0].symbolLayer(0)
                    if cur_sl:
                        if hasattr(cur_sl, "size"):           size  = cur_sl.size()
                        if hasattr(cur_sl, "sizeUnit"):       unit  = cur_sl.sizeUnit()
                        if hasattr(cur_sl, "sizeMapUnitScale"): scale = cur_sl.sizeMapUnitScale()
                        # largura do contorno (outlineWidth/strokeWidth)
                        if hasattr(cur_sl, "outlineWidth"):
                            width = cur_sl.outlineWidth()
                        elif hasattr(cur_sl, "strokeWidth"):
                            width = cur_sl.strokeWidth()

                sym = QgsSymbol.defaultSymbol(layer.geometryType())
        except Exception:
            # fallback total
            sym = QgsSymbol.defaultSymbol(layer.geometryType())
            size = unit = scale = width = None

        # 3) Ajustar apenas as CORES
        sym.setColor(fill_color)
        try:
            sl = sym.symbolLayer(0)
            if sl:
                # cor da borda/contorno
                if hasattr(sl, "setOutlineColor"):
                    sl.setOutlineColor(border_color)
                elif hasattr(sl, "setStrokeColor"):
                    sl.setStrokeColor(border_color)

                # Se viemos do fallback, restaurar tamanho/unidade/escala/largura
                if size is not None and hasattr(sl, "setSize"):
                    sl.setSize(size)
                if unit is not None and hasattr(sl, "setSizeUnit"):
                    sl.setSizeUnit(unit)
                if scale is not None and hasattr(sl, "setSizeMapUnitScale"):
                    sl.setSizeMapUnitScale(scale)
                if width is not None:
                    if hasattr(sl, "setOutlineWidth"):
                        sl.setOutlineWidth(width)
                    elif hasattr(sl, "setStrokeWidth"):
                        sl.setStrokeWidth(width)
        except Exception:
            pass  # nosec B110

        layer.setRenderer(QgsSingleSymbolRenderer(sym))
        layer.triggerRepaint()
        QgsProject.instance().layerWasAdded.emit(layer)
        self.iface.layerTreeView().refreshLayerSymbology(layer.id())

    def prompt_for_new_point_size(self, index):
        """
        Ajusta o tamanho do ponto com PRÉ-VISUALIZAÇÃO EM TEMPO REAL.
        - Enquanto o usuário move o controle, o tamanho é aplicado na camada (preview).
        - OK mantém o tamanho aplicado.
        - Cancel restaura exatamente o tamanho original.
        """
        # Resolve a camada a partir do item do treeView
        layer_id = index.model().itemFromIndex(index).data(Qt.ItemDataRole.UserRole)
        layer = QgsProject.instance().mapLayer(layer_id)
        if not layer or layer.geometryType() != QgsWkbTypes.GeometryType.PointGeometry:
            return

        # Guarda o renderizador original para poder restaurar se cancelar
        try:
            original_renderer = layer.renderer().clone()
        except Exception:
            original_renderer = None  # fallback

        current_size = self.get_current_point_size(layer) or 2.0

        # Diálogo simples com preview em tempo real
        dlg = QDialog(self.dlg)
        dlg.setWindowTitle(self.tr("Tamanho do Ponto"))
        vbox = QVBoxLayout(dlg)

        spin = QDoubleSpinBox(dlg)
        spin.setRange(0, 100)
        spin.setSingleStep(0.2)
        spin.setDecimals(2)
        spin.setValue(current_size)
        vbox.addWidget(spin)

        # Botões OK/Cancelar
        btns = QDialogButtonBox(QDialogButtonBox.StandardButton.Ok | QDialogButtonBox.StandardButton.Cancel, dlg)
        vbox.addWidget(btns)
        btns.accepted.connect(dlg.accept)
        btns.rejected.connect(dlg.reject)

        # PREVIEW: aplica em tempo real enquanto o usuário mexe no spin
        spin.valueChanged.connect(lambda val: self.apply_new_point_size(layer, val))

        # Abre diálogo
        if dlg.exec() == QDialog.DialogCode.Accepted:
            # Já está aplicado (nada extra a fazer)
            return
        else:
            # CANCEL: restaura o renderizador original
            if original_renderer is not None:
                try:
                    layer.setRenderer(original_renderer)
                    layer.triggerRepaint()
                    self.iface.layerTreeView().refreshLayerSymbology(layer.id())
                except Exception:
                    pass  # nosec B110

    def get_current_point_size(self, layer):
        """
        Retorna o tamanho do marcador (primeira symbol layer), se disponível.
        """
        try:
            r = layer.renderer()
            # Preferir caminho de símbolo único
            if isinstance(r, QgsSingleSymbolRenderer):
                sl = r.symbol().symbolLayer(0)
                if sl and hasattr(sl, "size"):
                    return sl.size()
            # Fallback: tenta via lista de símbolos
            syms = r.symbols(QgsRenderContext())
            if syms:
                sl = syms[0].symbolLayer(0)
                if sl and hasattr(sl, "size"):
                    return sl.size()
        except Exception:
            pass  # nosec B110
        return 2.0  # padrão

    def apply_new_point_size(self, layer, new_size):
        """
        Aplica o novo tamanho ao marcador ATUAL sem recriar o renderizador,
        para preservar cores, contorno, unidade e escala. Usado tanto no
        preview (tempo real) quanto na confirmação.
        """
        try:
            r = layer.renderer()

            # Caso mais comum: símbolo único
            if isinstance(r, QgsSingleSymbolRenderer):
                sym = r.symbol()
                sl = sym.symbolLayer(0)
                if sl and hasattr(sl, "setSize"):
                    sl.setSize(new_size)
            else:
                # Fallback leve: tenta ajustar o 1º símbolo retornado
                syms = r.symbols(QgsRenderContext())
                if syms:
                    sl = syms[0].symbolLayer(0)
                    if sl and hasattr(sl, "setSize"):
                        sl.setSize(new_size)
                # Observação: para renderizadores categorizados/graduados, um ajuste
                # completo exigiria iterar e substituir símbolos nas categorias.
                # Como seu fluxo usa símbolo único para pontos, este caminho já cobre o caso real.

            layer.triggerRepaint()
            self.iface.layerTreeView().refreshLayerSymbology(layer.id())
        except Exception:
            pass  # nosec B110

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

    def open_context_menu(self, position):
        """
        Cria e exibe um menu de contexto para ações específicas em um item selecionado no QTreeView.
        Este método é acionado com um clique do botão direito do mouse sobre um item da lista,
        apresentando opções como abrir propriedades da camada e alterar tamanho dos pontos da camada.

        Funções e Ações Desenvolvidas:
        - Verificação da seleção atual no QTreeView para determinar o item sobre o qual o menu será aberto.
        - Criação das opções do menu para manipulação das propriedades da camada e ajuste o tamanho do ponto.
        - Execução do menu no local do clique e execução da ação selecionada.

        :param position: A posição do cursor no momento do clique, usada para posicionar o menu de contexto.
        """
        # Obtém os índices selecionados no QTreeView
        indexes = self.dlg.treeViewListaPonto.selectedIndexes()
        if indexes:
            # Obter o índice da primeira coluna, que deve conter o ID da camada
            index = indexes[0].sibling(indexes[0].row(), 0)
            # Cria o menu de contexto
            menu = QMenu()
            # Adiciona opção para abrir propriedades da camada
            layer_properties_action = menu.addAction(self.tr("Abrir Propriedades da Camada"))
            # Adiciona opção para alterar a espessura da borda
            change_border_thickness_action = menu.addAction(self.tr("Tamanho do Ponto"))

            # Ação para Excel
            open_excel_action = menu.addAction(self.tr("Abrir Excel"))

            # Exibe o menu no local do clique e aguarda ação do usuário
            action = menu.exec(self.dlg.treeViewListaPonto.viewport().mapToGlobal(position))

            # Executa a ação correspondente à escolha do usuário
            if action == layer_properties_action:
                self.abrir_layer_properties(index)
            elif action == change_border_thickness_action:
                self.prompt_for_new_point_size(index)
            elif action == open_excel_action:  # Excel
                self.abrir_excel_atributos(index)

    def abrir_excel_atributos(self, index):
        """
        Exporta a TABELA DE ATRIBUTOS da camada selecionada para um XLSX
        em arquivo temporário e abre no Excel (ou app padrão do sistema).
        """
        # Resolve a camada a partir do item do treeView (igual ao abrir_layer_properties)
        layer_id = index.model().itemFromIndex(index).data(Qt.ItemDataRole.UserRole)
        layer = QgsProject.instance().mapLayer(layer_id)
        if not layer or layer.type() != QgsMapLayer.LayerType.VectorLayer or not layer.isValid():
            self.mostrar_mensagem(self.tr("Camada inválida para exportar ao Excel."), "Erro")
            return
        if layer.featureCount() == 0:
            self.mostrar_mensagem(self.tr("Nenhuma feição para exportar."), "Aviso")
            return

        def _sanitize(name: str) -> str:
            return re.sub(r'[<>/\\:";?*|=,]', '_', str(name))[:255]

        base = _sanitize(layer.name() or "camada")
        tmp_dir = tempfile.gettempdir()
        # Nome único por timestamp
        xlsx_path = os.path.join(tmp_dir, f"{base}_{int(time.time())}.xlsx")

        # Usa sua rotina pronta de XLSX (somente atributos)
        ok = self.salvar_como_xlsx(layer, xlsx_path, silencioso=True)
        if not ok:
            self.mostrar_mensagem(self.tr("Não foi possível gerar o XLSX."), "Erro")
            return

        # Abre o XLSX no aplicativo padrão do sistema por meio do Qt
        try:
            opened = bool(QDesktopServices.openUrl(QUrl.fromLocalFile(xlsx_path)))
        except (TypeError, RuntimeError):
            opened = False

        if opened:
            # Mensagem com botão "Abrir pasta" e link do arquivo
            self.mostrar_mensagem(self.tr("Arquivo gerado em:\n{xlsx_path}\nAbra manualmente no seu editor.").format(xlsx_path=xlsx_path), "Info", caminho_pasta=os.path.dirname(xlsx_path), caminho_arquivos=xlsx_path)

        else:
            self.mostrar_mensagem(self.tr("O arquivo XLSX foi gerado, mas não foi possível "
                    "abri-lo automaticamente:\n{xlsx_path}"
                ).format(xlsx_path=xlsx_path),
                "Aviso",
                caminho_pasta=os.path.dirname(xlsx_path),
                caminho_arquivos=xlsx_path)

    def on_item_double_clicked(self, index):
        """
        Manipula o evento de duplo clique em um item do QTreeView. Este método é acionado quando um usuário
        efetua um duplo clique em uma camada listada, permitindo que altere as cores de preenchimento e borda da camada.

        Funções e Ações Desenvolvidas:
        - Recuperação da camada associada ao item clicado.
        - Obtenção das cores atuais de preenchimento e borda da camada.
        - Exibição de um diálogo para que o usuário selecione novas cores.
        - Aplicação das cores selecionadas à camada, se novas cores foram escolhidas.

        :param index: QModelIndex que representa o item no modelo que foi duplo clicado.
        """
        # Obtém o ID da camada do item clicado usando o UserRole
        layer_id = index.model().itemFromIndex(index).data(Qt.ItemDataRole.UserRole)
        # Busca a camada correspondente no projeto QGIS usando o ID
        layer = QgsProject.instance().mapLayer(layer_id)
        if layer:
            # Obtém as cores atuais de preenchimento e borda da camada
            current_fill_color, current_border_color = self.get_point_colors(layer)
            # Solicita ao usuário que selecione novas cores para preenchimento e borda
            new_fill_color, new_border_color = self.prompt_for_new_colors(current_fill_color, current_border_color)
            # Se novas cores forem selecionadas, aplica estas cores à camada
            if new_fill_color and new_border_color:
                self.apply_new_colors(layer, new_fill_color, new_border_color)

    def tratar_pontos(self, new_layer):
        """
        Configura o comportamento automático de uma camada de pontos.

        - Mantém o campo ID visível;
        - define ID automático;
        - mantém X, Y e DMS atualizados;
        - oculta somente os campos calculados;
        - exibe normalmente o formulário de atributos.
        """
        if (not isinstance(new_layer, QgsVectorLayer)
            or not new_layer.isValid()
            or new_layer.geometryType() != QgsWkbTypes.GeometryType.PointGeometry):
            return

        # Campo ID
        idx_id = new_layer.fields().indexOf("ID")

        if idx_id != -1:
            new_layer.setDefaultValueDefinition(
                idx_id,
                QgsDefaultValue('coalesce(maximum("ID"),0)+1'))

            # Garante que o ID não permaneça oculto
            try:
                widget_id = new_layer.editorWidgetSetup(idx_id)

                if widget_id.type() == "Hidden":
                    new_layer.setEditorWidgetSetup(
                        idx_id,
                        QgsEditorWidgetSetup(
                            "Range",
                            {"Min": 1,
                                "Max": 2147483647,
                                "Step": 1,
                                "Precision": 0,
                                "AllowNull": False}))
            except Exception:
                pass  # nosec B110

        # Campos calculados
        hidden = QgsEditorWidgetSetup("Hidden", {})

        for nome_campo in (
            "X",
            "Y",
            "X_GMS",
            "Y_GMS"):
            idx = new_layer.fields().indexOf(nome_campo)

            if idx != -1:
                new_layer.setEditorWidgetSetup( idx, hidden)

        # Evita conexões duplicadas
        manager_conns = getattr(getattr(self, "pontos_manager", None), "_conns", {})

        # Camadas criadas por CamadaPontosManager já possuem
        # featureAdded e geometryChanged conectados.
        if new_layer.id() not in manager_conns:

            new_layer.featureAdded.connect(
                lambda fid, lyr=new_layer:
                self._on_ponto_feature_added(lyr, fid))

            new_layer.geometryChanged.connect(
                lambda fid, _geom, lyr=new_layer:
                self.atualizar_posicao_xy(lyr, fid))

        # Garante que o formulário seja exibido
        try:
            cfg = new_layer.editFormConfig()

            try:
                cfg.setSuppress(Qgis.AttributeFormSuppression.Off)
            except Exception:
                cfg.setSuppress(QgsEditFormConfig.FeatureFormSuppress.SuppressOff)

            new_layer.setEditFormConfig(cfg)

        except Exception:
            pass  # nosec B110

        # Atualiza as feições existentes
        iniciou_edicao = False

        if not new_layer.isEditable():
            iniciou_edicao = new_layer.startEditing()

        for feature in new_layer.getFeatures():
            self.atualizar_posicao_xy(new_layer, feature.id())

        if iniciou_edicao:
            try:
                new_layer.commitChanges()
            except Exception:
                pass  # nosec B110

    def atualizar_posicao_xy(self, camada, fid):
        """
        Atualiza os campos X, Y, X_DMS e Y_DMS conforme a geometria do ponto.

        X/Y ficam no CRS original da camada.
        X_DMS/Y_DMS são calculados em coordenadas geográficas, transformando para EPSG:4326 quando necessário.
        """
        feat = camada.getFeature(fid)
        if not feat or not feat.isValid():
            return

        geom = feat.geometry()
        if geom is None or geom.isEmpty():
            return

        idx_x = camada.fields().indexOf("X")
        idx_y = camada.fields().indexOf("Y")
        idx_x_dms = camada.fields().indexOf("X_GMS")
        idx_y_dms = camada.fields().indexOf("Y_GMS")

        try:
            pt = geom.asPoint()
        except Exception:
            return

        is_geografico = camada.crs().isGeographic()
        casas = 6 if is_geografico else 3

        if idx_x != -1:
            camada.changeAttributeValue(fid, idx_x, round(pt.x(), casas))

        if idx_y != -1:
            camada.changeAttributeValue(fid, idx_y, round(pt.y(), casas))

        x_dms, y_dms = self.calcular_dms_do_ponto(camada, pt)

        if idx_x_dms != -1:
            camada.changeAttributeValue(fid, idx_x_dms, x_dms)

        if idx_y_dms != -1:
            camada.changeAttributeValue(fid, idx_y_dms, y_dms)

    def calcular_posicao_xy(self, valor):
        """
        Converte coordenada decimal em graus, minutos e segundos.
        Deve receber longitude/latitude em graus decimais, não coordenada UTM/projetada.
        """
        if valor is None:
            return ""

        try:
            valor = float(valor)
        except Exception:
            return ""

        sinal = "-" if valor < 0 else ""
        total_segundos = round(abs(valor) * 3600.0, 2)

        graus = int(total_segundos // 3600)
        resto = total_segundos - (graus * 3600)

        minutos = int(resto // 60)
        segundos = resto - (minutos * 60)

        return f'{sinal}{graus}° {minutos}\' {segundos:.2f}"'

    def calcular_dms_do_ponto(self, layer, pt):
        """
        Retorna X_DMS e Y_DMS corretamente.

        - Se a camada já estiver em CRS geográfico, usa X/Y diretamente.
        - Se estiver em CRS projetado, transforma o ponto para EPSG:4326 antes.
        - X_DMS = longitude
        - Y_DMS = latitude
        """
        if layer is None or pt is None:
            return "", ""

        try:
            origem_crs = layer.crs()
            if not origem_crs.isValid():
                return "", ""

            ponto_xy = QgsPointXY(pt)

            if origem_crs.isGeographic():
                ponto_geo = ponto_xy
            else:
                destino_crs = QgsCoordinateReferenceSystem("EPSG:4326")
                transform = QgsCoordinateTransform(
                    origem_crs,
                    destino_crs,
                    QgsProject.instance().transformContext())
                ponto_geo = transform.transform(ponto_xy)

            x_dms = self.calcular_posicao_xy(ponto_geo.x())
            y_dms = self.calcular_posicao_xy(ponto_geo.y())

            return x_dms, y_dms

        except Exception:
            return "", ""

    def clone_layer_ponto(self):
        """
        Dispara a clonagem de uma camada de pontos selecionada no treeViewListaPonto.

        Funcionalidades:
        - Recupera o índice da camada de ponto selecionada na interface.
        - Obtém o ID da camada salvo no Qt.UserRole do item do treeView.
        - Busca a camada correspondente no projeto QGIS usando o ID.
        - Verifica se a camada existe e é do tipo ponto.
        - Instancia o gerenciador de clonagem para pontos (CloneManagerPt) e exibe as opções de clonagem ao usuário.
        - Atualiza o treeViewListaPonto para refletir eventuais novas camadas criadas.

        Observações:
        - Permite diferentes tipos de clonagem (somente feições, todos os atributos, combinação, exclusão de atributos).
        - Exibe mensagens de erro apropriadas para seleção inválida ou tipo de camada errado.
        """

        # Recupera os índices selecionados no treeViewListaPonto
        indexes = self.dlg.treeViewListaPonto.selectedIndexes()
        if not indexes:
            # Nenhuma camada selecionada: exibe mensagem de erro
            self.mostrar_mensagem(self.tr("Nenhuma camada de ponto selecionada."), "Erro")
            return

        # Pega o primeiro índice selecionado (assumindo seleção simples)
        index = indexes[0]
        # Obtém o ID da camada salvo em Qt.UserRole
        layer_id = index.data(Qt.ItemDataRole.UserRole)
        # Busca a camada correspondente no projeto QGIS
        layer = QgsProject.instance().mapLayer(layer_id)

        if not layer:
            # Camada não localizada (ID inválido ou removido)
            self.mostrar_mensagem(self.tr("Não foi possível localizar a camada no projeto."), "Erro")
            return

        # Garante que a camada selecionada seja de pontos
        if layer.geometryType() != QgsWkbTypes.GeometryType.PointGeometry:
            self.mostrar_mensagem(self.tr("A camada selecionada não é de pontos."), "Erro")
            return

        # Instancia o gerenciador de clonagem de pontos e exibe o diálogo de opções
        CloneManagerPt(self, layer).show_clone_options()
        # Atualiza a visualização do treeView de pontos na interface
        self.atualizar_treeView_lista_ponto()  # Mantenha igual ao dos outros tipos

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

        # Configura as opções da caixa de diálogo para salvar arquivos
        options = QFileDialog.Options()
        
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
        fileName, _ = QFileDialog.getSaveFileName(
            self.dlg,
            self.tr("Salvar Camada"),
            nome_completo_proposto,
            tipo_arquivo,
            options=options)

        # Verifica se um nome de arquivo foi escolhido
        if fileName:
            # Atualiza o último diretório usado nas configurações do QGIS
            settings.setValue("lastDir", os.path.dirname(fileName))

            # Assegura que o arquivo tenha a extensão correta
            if not fileName.endswith(extensao):
                fileName += extensao

        return fileName  # Retorna o caminho completo do arquivo escolhido ou None se cancelado

    def mostrar_mensagem(self, texto, tipo, duracao=3, caminho_pasta=None, caminho_arquivos=None):
        """
        Exibe uma mensagem na barra de mensagens do QGIS.

        Para mensagens de sucesso, pode apresentar:
        - botão para abrir a pasta;
        - botão para executar o arquivo;
        - botão para abrir o Google Earth Web quando o arquivo for KML/KMZ.
        """
        bar = self.iface.messageBar()

        if tipo == "Erro":
            bar.pushMessage(self.tr("Erro"), texto, level=Qgis.MessageLevel.Critical, duration=duracao)
            return

        if tipo == "Aviso":
            bar.pushMessage(self.tr("Aviso"), texto, level=Qgis.MessageLevel.Warning, duration=duracao)
            return

        if tipo != "Sucesso":
            bar.pushMessage(self.tr("Info"), texto, level=Qgis.MessageLevel.Info, duration=duracao)
            return

        # Mensagem personalizada de sucesso
        msg = bar.createMessage(self.tr("Sucesso"), texto)

        posicao_botao = 1

        # Botão Abrir Pasta
        if caminho_pasta:
            botao_abrir_pasta = QPushButton(self.tr("Abrir Pasta"))

            botao_abrir_pasta.clicked.connect(
                lambda _checked=False, caminho=caminho_pasta:
                    QDesktopServices.openUrl(
                        QUrl.fromLocalFile(
                            os.path.abspath(os.fspath(caminho)))))

            msg.layout().insertWidget(posicao_botao, botao_abrir_pasta)

            posicao_botao += 1

        # Botão Executar
        if caminho_arquivos:
            botao_executar = QPushButton(self.tr("Executar"))

            botao_executar.clicked.connect(
                lambda _checked=False, caminho=caminho_arquivos:
                    QDesktopServices.openUrl(
                        QUrl.fromLocalFile(
                            os.path.abspath(os.fspath(caminho)))))

            msg.layout().insertWidget(posicao_botao, botao_executar)

            posicao_botao += 1

        # Botão Google Earth Web somente para KML/KMZ
        caminho_earth = None

        if isinstance(caminho_arquivos, str):
            extensao = os.path.splitext(caminho_arquivos)[1].lower()

            if extensao in (".kml", ".kmz"):
                caminho_earth = caminho_arquivos

        if caminho_earth:
            botao_google_earth = QPushButton(self.tr("Abrir Google Earth Web"))

            botao_google_earth.setToolTip(
                self.tr("Abre o Google Earth Web e copia o caminho "
                    "do arquivo para a área de transferência."))

            botao_google_earth.clicked.connect(lambda _checked=False, caminho=caminho_earth:
                self.abrir_google_earth_web(caminho))

            msg.layout().insertWidget(posicao_botao, botao_google_earth)

        bar.pushWidget(msg, level=Qgis.MessageLevel.Info, duration=duracao)

    def abrir_google_earth_web(self, caminho_arquivo=None):
        """
        Abre o Google Earth Web e copia o caminho do KML/KMZ
        para a área de transferência.
        """
        if caminho_arquivo:
            try:
                caminho_normalizado = os.path.normpath(caminho_arquivo)

                QGuiApplication.clipboard().setText(caminho_normalizado)

            except Exception:
                pass  # nosec B110

        QDesktopServices.openUrl(QUrl("https://earth.google.com/web/"))

        # Mostra a orientação sem bloquear
        QTimer.singleShot(250,
            lambda: self.iface.messageBar().pushMessage(
                self.tr("Google Earth Web"),
                self.tr("Clique em Novo > Importar arquivo > "
                    "Dispositivo local. O caminho do KML foi copiado."), level=Qgis.MessageLevel.Info, duration=5))

    def iniciar_progress_bar(self, layer: QgsVectorLayer = None, message: str = None):
        """
        Inicia e exibe uma barra de progresso na interface do usuário para acompanhar o processamento de uma camada (por exemplo, exportação para DXF, carregamento de KML/KMZ, etc).

        Parâmetros:
        - layer (QgsVectorLayer, opcional): A camada relacionada ao processo. Se fornecida, será usada para obter o nome e o número de feições.
        - message (str, opcional): Texto personalizado a ser exibido na barra de mensagens. Se não informado, será utilizado um texto padrão relacionado ao layer.

        Funcionalidades:
        - Cria e exibe uma barra de progresso estilizada na barra de mensagens do QGIS, com texto customizável.
        - O progresso pode ser atualizado externamente (retorna os widgets para controle).
        - A barra de progresso permanece visível até ser explicitamente removida, evitando que seja deletada automaticamente pelo QGIS durante processos longos.
        - Define o valor máximo da barra de progresso conforme o número de feições da camada, se disponível.
        - Retorna os widgets para controle externo (atualização do progresso e fechamento).

        Retorno:
        - tuple: (QProgressBar, progressMessageBar) para que possam ser atualizados ou fechados pelo código chamador.
        """
        if message is None:
            if layer is not None:
                message = self.tr("Exportando camada para DXF: {layer_name}").format(layer_name=layer.name())
            else:
                message = self.tr("Processando, aguarde...")

        # Cria a mensagem personalizada na barra de mensagens
        progressMessageBar = self.iface.messageBar().createMessage(message)

        progressBar = QProgressBar()
        progressBar.setAlignment(Qt.AlignmentFlag.AlignLeft | Qt.AlignmentFlag.AlignVCenter)
        progressBar.setFormat(self.tr("%p% - %v de %m Feições processadas"))
        progressBar.setMinimumWidth(300)
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
            QProgressBar {
                min-height: 5px;}
        """)

        # Adiciona a progressBar ao layout e exibe na barra de mensagens (sem timeout automático)
        progressMessageBar.layout().addWidget(progressBar)
        self.iface.messageBar().pushWidget(progressMessageBar, Qgis.MessageLevel.Info, duration=0)

        # Define o valor máximo com base no número de feições da camada (se fornecida)
        if layer is not None:
            feature_count = layer.featureCount()
            progressBar.setMaximum(feature_count)

        return progressBar, progressMessageBar

    def _adicionar_arquivo_por_caminho(self, file_path: str) -> bool:
        """
        Adiciona um arquivo ao projeto usando o mesmo fluxo do botão, sem abrir QFileDialog.

        Para KML/KMZ:
        - cria grupo;
        - adiciona todas as camadas dentro do grupo;
        - remove .kml/.kmz dos nomes;
        - remove o nome do grupo do nome das camadas.
        """
        if not file_path:
            return False

        layer_name = self._limpar_nome_kml_kmz(os.path.basename(file_path))
        ext = os.path.splitext(file_path)[1].lower()

        start_time = time.time()

        root = QgsProject.instance().layerTreeRoot()
        layers_to_add: list[QgsVectorLayer] = []

        def _add_layer(lyr: QgsVectorLayer, group=None) -> bool:
            if not lyr or not lyr.isValid():
                return False

            # Remove duplicados por nome
            try:
                for old in list(QgsProject.instance().mapLayers().values()):
                    if old and old.name() == lyr.name():
                        QgsProject.instance().removeMapLayer(old.id())
            except Exception:
                pass  # nosec B110

            if group is not None:
                # Adiciona ao projeto SEM criar nó automático na raiz
                QgsProject.instance().addMapLayer(lyr, False)

                # Adiciona a camada dentro do grupo
                node = group.addLayer(lyr)

                # Remove apenas nós diretos da raiz, caso o QGIS tenha criado algum
                # Não mexe em nós dentro de grupos
                try:
                    for child in list(root.children()):
                        if isinstance(child, QgsLayerTreeLayer) and child.layerId() == lyr.id():
                            root.removeChildNode(child)
                except Exception:
                    pass  # nosec B110

                if node:
                    node.setItemVisibilityChecked(True)

            else:
                QgsProject.instance().addMapLayer(lyr)
                node = root.findLayer(lyr.id())
                if node:
                    node.setItemVisibilityChecked(True)

            return True

        # DXF
        if ext == ".dxf":
            pt_layer, text_layer = self._processar_dxf_pontos(file_path, layer_name)

            if pt_layer is None and text_layer is None:
                return False

            if pt_layer:
                layers_to_add.append(pt_layer)

            if text_layer:
                layers_to_add.append(text_layer)

        # KML/KMZ
        elif ext in (".kml", ".kmz"):
            res = self._processar_kml_kmz_pontos(file_path, layer_name) or []

            if isinstance(res, QgsVectorLayer):
                layers_to_add = [res]
            elif isinstance(res, (list, tuple)):
                layers_to_add = [candidate_layer for candidate_layer in res if candidate_layer and candidate_layer.isValid()]
            else:
                layers_to_add = []

            if not layers_to_add:
                return False

        # Outros vetores
        else:
            origem = QgsVectorLayer(file_path, layer_name, "ogr")
            if not origem.isValid():
                self.mostrar_mensagem(self.tr("Falha ao carregar o arquivo vetorial."), "Erro")
                return False

            mem = self._copiar_para_memoria_ponto(origem, layer_name)
            del origem

            if mem and mem.isValid():
                layers_to_add = [mem]
            else:
                return False

        # Grupo para KML/KMZ
        group = None
        if ext in (".kml", ".kmz"):
            group_name = self._inferir_nome_grupo_kml(layer_name, layers_to_add)

            # Se o grupo já existir, reaproveita
            group = root.findGroup(group_name)
            if group is None:
                group = root.addGroup(group_name)

            # Limpa os nomes das camadas antes de adicionar
            usados = set()
            for lyr in layers_to_add:
                nome_limpo = self._limpar_nome_camada_no_grupo(lyr.name(), group_name)
                nome_limpo = self._nome_unico_lista(nome_limpo, usados)
                lyr.setName(nome_limpo)

        added_any = False
        for lyr in layers_to_add:
            if _add_layer(lyr, group=group):
                added_any = True

        if not added_any:
            return False

        elapsed = time.time() - start_time
        tempo_formatado = (
            "{:.1f}s".format(elapsed)
            if elapsed < 60
            else "{:.0f}min {:.1f}s".format(elapsed // 60, elapsed % 60))

        self.mostrar_mensagem(self.tr("Camadas de '{layer_name}' adicionadas com sucesso em {tempo_formatado}.").format(layer_name=layer_name, tempo_formatado=tempo_formatado), "Sucesso")

        self.atualizar_treeView_lista_ponto()
        return True

    def abrir_adicionar_arquivo(self):
        """
        Abre o diálogo para selecionar e adicionar um arquivo de pontos.
        Os textos dos filtros ficam habilitados para tradução.
        """
        file_filter = ";;".join([
            self.tr("Todos os formatos suportados (*.dxf *.kml *.kmz *.shp *.geojson *.gpkg)"),
            self.tr("Arquivos DXF (*.dxf)"),
            self.tr("Arquivos KML (*.kml)"),
            self.tr("Arquivos KMZ (*.kmz)"),
            self.tr("Arquivos Shapefile (*.shp)"),
            self.tr("Arquivos GeoJSON (*.geojson)"),
            self.tr("Arquivos GeoPackage (*.gpkg)"),
            self.tr("Todos os arquivos (*.*)")])

        file_path, _ = QFileDialog.getOpenFileName(self.dlg, self.tr("Abrir Arquivo de Pontos"), "", file_filter)

        if not file_path:
            return

        try:
            ok = self._adicionar_arquivo_por_caminho(file_path)

            if not ok:
                self.mostrar_mensagem(self.tr("Nenhuma feição de ponto encontrada ou o arquivo não pôde ser carregado."), "Aviso")

        except Exception as e:
            self.mostrar_mensagem(self.tr("Erro ao adicionar arquivo: {error}").format(error=str(e)), "Erro")

    def obter_cor_rotulo(self, layer):
        """
        Obtém a cor do rótulo da camada e a converte para o formato de cor KML (AABBGGRR).

        Parâmetros:
        - layer (QgsVectorLayer): A camada de origem para obter a cor do rótulo.

        Funcionalidades:
        - Verifica se os rótulos estão habilitados para a camada.
        - Obtém o renderizador de rótulo e as configurações de texto.
        - Converte a cor do rótulo do formato Qt para o formato KML.
        - Retorna a cor do rótulo em formato hexadecimal (AABBGGRR).
        - Retorna branco como padrão se os rótulos não estiverem habilitados ou configurados.
        """
        if layer.labelsEnabled():
            labeling = layer.labeling()
            if labeling:
                text_format = labeling.settings().format()
                cor_texto = text_format.color()

                cor_kml = (
                    cor_texto.alpha() << 24
                    | cor_texto.blue() << 16
                    | cor_texto.green() << 8
                    | cor_texto.red())
                cor_kml_hex = format(cor_kml, '08x')
                return cor_kml_hex

        # Branco no formato KML AABBGGRR
        return 'ffffffff'

    def obter_cor_icone(self, layer):
        """
        Obtém a cor do ícone da camada e a converte para o formato de cor KML (AABBGGRR).

        Parâmetros:
        - layer (QgsVectorLayer): A camada de origem para obter a cor do ícone.

        Funcionalidades:
        - Verifica se a geometria da camada é do tipo ponto.
        - Obtém o renderizador de símbolo da camada.
        - Verifica se o renderizador é do tipo 'singleSymbol' e se o símbolo é um marcador.
        - Obtém a cor do símbolo do ícone.
        - Converte a cor do símbolo do formato Qt para o formato KML.
        - Retorna a cor do ícone em formato hexadecimal (AABBGGRR).
        - Retorna branco como padrão se a geometria não for do tipo ponto ou se o símbolo não for um marcador.
        """
        # Verifica se a geometria da camada é do tipo ponto
        if layer.geometryType() == QgsWkbTypes.GeometryType.PointGeometry:
            # Obtém o símbolo da camada
            renderer = layer.renderer()
            if renderer and renderer.type() == 'singleSymbol':
                symbol = renderer.symbol()
                if symbol and symbol.type() == QgsSymbol.SymbolType.Marker:
                    # Obtém a cor do símbolo
                    cor_icone = symbol.color()
                    cor_kml = cor_icone.alpha() << 24 | cor_icone.blue() << 16 | cor_icone.green() << 8 | cor_icone.red()
                    cor_kml_hex = format(cor_kml, '08x')
                    return cor_kml_hex

        # Retorna branco como padrão se não for um símbolo de ponto padrão
        return 'ffffffff'

    def url_para_link_html(self, url):
        """
        Converte um URL em um link HTML clicável. A função realiza as seguintes etapas:

        1. Verifica se o texto fornecido é um URL válido.
        2. Se for um URL válido, formata o texto "Link de acesso" como um link HTML com o URL correto.
        3. Se não for um URL, retorna o texto como está.

        Parâmetros:
        - url (str): O texto a ser verificado e possivelmente convertido em um link HTML.

        Funcionalidades:
        - Verificação de validade do URL usando expressão regular.
        - Formatação do texto como link HTML se o URL for válido.
        - Retorno do texto original se não for um URL válido.
        """
        # Verifica se o texto é um URL válido
        if re.match(r'https?://[^\s]+', url):
            # Retorna o texto "Acesso Aqui" formatado como link HTML com o URL correto
            return "<a href='{url}'>{label}</a>".format(url=url, label=self.tr("Link de acesso"))
        else:
            # Se não for um URL, retorna o texto como está
            return url

    def gerar_cor_suave(self):
        """
        Gera uma cor suave aleatória no formato hexadecimal. A função realiza as seguintes etapas:

        1. Gera valores aleatórios para os componentes RGB dentro do intervalo de cores suaves (180-255).
        2. Formata e retorna a cor como uma string hexadecimal.

        Funcionalidades:
        - Geração de valores aleatórios para os componentes vermelho, verde e azul (RGB).
        - Formatação da cor no formato hexadecimal.

        Retorna:
        - str: A cor gerada no formato hexadecimal (e.g., '#aabbcc').
        """
        # Cor aleatória usada somente para apresentação visual.
        r = random.randint(180, 255)  # nosec B311
        g = random.randint(180, 255)  # nosec B311
        b = random.randint(180, 255)  # nosec B311

        return f"#{r:02x}{g:02x}{b:02x}" # Retorna a cor formatada como uma string hexadecimal

    def qcolor_para_kml(self, cor: QColor) -> str:
        """
        Converte QColor para o formato KML AABBGGRR.
        """
        if cor is None or not cor.isValid():
            return 'ffffffff'

        cor_kml = (
            cor.alpha() << 24
            | cor.blue() << 16
            | cor.green() << 8
            | cor.red())
        return format(cor_kml, '08x')

    def aplicar_transparencia_kml(self, cor_kml_hex: str, transparencia_percentual: float) -> str:
        """
        Aplica transparência (0 a 100%) sobre uma cor KML no formato AABBGGRR.
        0   = opaco
        100 = totalmente transparente
        """
        try:
            transparencia_percentual = float(transparencia_percentual)
        except Exception:
            transparencia_percentual = 0.0

        transparencia_percentual = max(0.0, min(100.0, transparencia_percentual))

        # alpha no KML: 255 opaco, 0 transparente
        alpha = int(round(255 * (100.0 - transparencia_percentual) / 100.0))
        alpha_hex = f"{alpha:02x}"

        cor_kml_hex = (cor_kml_hex or "ffffffff").lower()
        if len(cor_kml_hex) != 8:
            cor_kml_hex = "ffffffff"

        return alpha_hex + cor_kml_hex[2:]

    def modificar_kml_para_tessellation(self, caminho_kml):
        """
        Modifica um arquivo KML para incluir a tag <tessellate> em cada elemento LineString, garantindo a visualização correta das pontos em plataformas que suportam KML, como o Google Earth.

        Parâmetros:
        - caminho_kml (str): O caminho do arquivo KML que será modificado.

        Funcionalidades:
        - Faz o parse do arquivo KML para acessar e modificar sua estrutura XML.
        - Registra o namespace do KML para garantir que as modificações no XML sejam corretamente reconhecidas e validadas.
        - Itera por cada elemento LineString no arquivo KML e adiciona um elemento filho <tessellate> com o valor '1'. Isso indica que o Google Earth e outros visualizadores devem tentar renderizar a linha de forma contínua, mesmo através do horizonte.
        - Salva as alterações no mesmo arquivo KML, substituindo o conteúdo anterior.
        """
        try:
            tree, root = self._parse_xml_file_seguro(caminho_kml)
            if tree is None or root is None:
                return

            ns = "http://www.opengis.net/kml/2.2"
            XmlET.register_namespace('', ns)

            for line_string in root.findall(f".//{{{ns}}}LineString"):
                if line_string.find(f"{{{ns}}}tessellate") is None:
                    tessellate = XmlET.SubElement(line_string, f"{{{ns}}}tessellate")
                    tessellate.text = "1"

            tree.write(caminho_kml, encoding="utf-8", xml_declaration=True)

        except Exception as e:
            self.mostrar_mensagem(self.tr("Erro ao modificar o arquivo KML: {error}").format(error=str(e)), "Erro")

    def _parse_xml_file_seguro(self, caminho_xml):
        """
        Faz parse seguro de XML/KML em arquivo.
        """
        if not DEFUSEDXML_OK:
            if not hasattr(self, "_avisou_defusedxml"):
                self._avisou_defusedxml = False

            if not self._avisou_defusedxml:
                self._avisou_defusedxml = True
                self.mostrar_mensagem(self.tr("A biblioteca 'defusedxml' não está instalada no Python do QGIS. Instale com: python -m pip install defusedxml"), "Erro", duracao=3)
            return None, None

        try:
            tree = DefusedET.parse(caminho_xml)
            root = tree.getroot()
            return tree, root
        except (DefusedET.ParseError, DefusedXmlException) as e:
            self.mostrar_mensagem(self.tr("XML/KML inválido ou inseguro: {error}").format(error=str(e)), "Erro", duracao=3)
            return None, None
        except Exception as e:
            self.mostrar_mensagem(self.tr("Erro ao abrir o arquivo KML: {error}").format(error=str(e)), "Erro", duracao=3)
            return None, None

    def exportar_para_kml(self):
        """
        Exporta a camada de PONTOS selecionada (treeViewListaPonto) para KML,
        usando diálogo NÃO-bloqueante (sem exec_()) para evitar crash por reentrância.
        """
        # Guard contra reentrância
        if getattr(self, "_kml_export_in_progress", False):
            return
        self._kml_export_in_progress = True

        # Resolve camada selecionada pelo ID (Qt.UserRole)
        idx = self.dlg.treeViewListaPonto.currentIndex()
        if not idx.isValid():
            sels = [i for i in self.dlg.treeViewListaPonto.selectionModel().selectedIndexes() if i.column() == 0]
            idx = sels[0] if sels else None
        if idx is None or not idx.isValid():
            self._kml_export_in_progress = False
            self.mostrar_mensagem(self.tr("Selecione uma camada para exportar."), "Erro")
            return

        item = idx.model().itemFromIndex(idx)
        layer_id = item.data(Qt.ItemDataRole.UserRole)
        layer = QgsProject.instance().mapLayer(layer_id)

        # Valida: vetorial + pontos + válida + com feições
        if (layer is None or
            layer.type() != QgsMapLayer.LayerType.VectorLayer or
            layer.geometryType() != QgsWkbTypes.GeometryType.PointGeometry or
            not layer.isValid()):
            self._kml_export_in_progress = False
            self.mostrar_mensagem(self.tr("Nenhuma camada vetorial de pontos válida selecionada."), "Aviso")
            return

        if layer.featureCount() == 0:
            self._kml_export_in_progress = False
            self.mostrar_mensagem(self.tr("Nenhuma feição para ser exportada."), "Erro")
            return

        # Cria diálogo (sem exec_); mantém referência viva
        parent = getattr(self, "dlg", None) or self.iface.mainWindow()
        try:
            dialog = IconFieldSelectionDialog(layer, parent=parent)
        except TypeError:
            dialog = IconFieldSelectionDialog(layer)

        dialog.setModal(True)
        dialog.setWindowModality(Qt.WindowModality.WindowModal)
        dialog.setAttribute(Qt.WidgetAttribute.WA_DeleteOnClose, False)
        self._icon_dialog_ref = dialog

        # Conecta handlers (sem bloquear)
        dialog.accepted.connect(lambda: self._kml_on_accepted(layer))
        dialog.rejected.connect(self._kml_on_rejected)

        # MOSTRAR com segurança (sem raise_/activateWindow)
        QTimer.singleShot(0, dialog.open)  # abre assíncrono; evita access violation

    def _kml_format_valor_rotulo(self, layer, feature, campo_id):
        """
        Formata o valor do campo `campo_id` para ser usado como rótulo no KML.

        Usa o mesmo formatador geral do KML para corrigir também campos
        de Data, Hora e Data/Hora.
        """
        try:
            v = feature[campo_id]
        except Exception:
            return ""

        try:
            return self._kml_format_value(layer.fields(), campo_id, v)
        except Exception:
            if v is None:
                return ""

            s = str(v)
            if re.fullmatch(r"-?\d+\.0+", s):
                return s.split(".", 1)[0]
            return s

    def _img_cache_dir(self) -> str:
        """
        Retorna (e garante) o diretório de cache local usado para armazenar imagens
        redimensionadas/temporárias durante a exportação KML/KMZ.

        Estratégia:
        - Tenta usar o CacheLocation do sistema (ideal).
        - Se não houver, cai para TempLocation.
        - Cria a pasta se não existir.

        Retorna:
        - Caminho absoluto (str) do diretório pronto para uso.
        """
        # Pega um diretório de cache do sistema (Windows/Linux/macOS)
        base = QStandardPaths.writableLocation(QStandardPaths.StandardLocation.CacheLocation)

        # Se o cache do sistema não existir/disponível, usa diretório temporário
        if not base:
            base = QStandardPaths.writableLocation(QStandardPaths.StandardLocation.TempLocation)

        # Monta a pasta específica do plugin para não misturar com outros caches
        d = os.path.join(base, "tempo_salvo_tools", "kml_img_cache")

        # Garante que o diretório existe
        os.makedirs(d, exist_ok=True)

        return d

    def _kml_on_accepted(self, layer):
        """
        Handler chamado quando o usuário confirma o diálogo de ícone/campo.
        Continua o fluxo: escolhe caminho, gera KML e salva.
        """
        dialog = getattr(self, "_icon_dialog_ref", None)
        if dialog is None:
            self._kml_export_in_progress = False
            self.mostrar_mensagem(self.tr("Diálogo encerrado antes da exportação."), "Aviso")
            return

        # Coleta seleções do diálogo
        try:
            (campo_id, icon_url, image_url, overlay_url, exportar_rotulos, cor_rotulo_escolhida, escala_rotulo, escala_icone, transparencia_icone) = dialog.get_selections()

        except Exception as e:
            self._kml_on_rejected()
            self.mostrar_mensagem(self.tr("Falha ao ler seleção do diálogo: {error}").format(error=str(e)), "Erro")
            return
        finally:
            try:
                dialog.hide()
            except Exception:
                pass  # nosec B110

        # Escolher caminho (sugestão com último diretório salvo)
        base_dir = getattr(self, "ultimo_caminho_salvo", "") or os.path.expanduser("~")
        sugestao = os.path.join(base_dir, f"{layer.name()}.kml")
        caminho_arquivo = self.escolher_local_para_salvar(sugestao, self.tr("Arquivos KML (*.kml)"))
        if not caminho_arquivo:
            self._kml_on_rejected(msg = self.tr("Exportação cancelada."))
            return

        # Atualiza já o último diretório escolhido
        try:
            ultimo_dir = os.path.dirname(caminho_arquivo)
            if ultimo_dir:
                self.ultimo_caminho_salvo = ultimo_dir
        except Exception:
            pass  # nosec B110

        # Barra de progresso
        progressBar = progressMessageBar = None
        try:
            progressBar, progressMessageBar = self.iniciar_progress_bar(layer)
        except Exception:
            pass  # nosec B110

        try:
            # Gera e grava o KML
            start_time = time.time()
            kml_element = self.criar_kml_em_memoria(layer, campo_id, icon_url, exportar_rotulos, progressBar, image_url, overlay_url, cor_rotulo_escolhida, escala_rotulo, escala_icone, transparencia_icone)

            tree = XmlET.ElementTree(kml_element)
            tree.write(caminho_arquivo, xml_declaration=True, encoding='utf-8', method="xml")
            execution_time = time.time() - start_time

            # Remove só a barra de progresso (não limpe toda a message bar!)
            try:
                if progressMessageBar:
                    # preferível remover apenas o widget da barra
                    self.iface.messageBar().popWidget(progressMessageBar)
            except Exception:
                # fallback se popWidget não estiver disponível
                self.iface.messageBar().clearWidgets()

            # Atualiza último diretório (de novo, por garantia)
            try:
                self.ultimo_caminho_salvo = os.path.dirname(caminho_arquivo)
            except Exception:
                pass  # nosec B110

            # Mensagem única de sucesso com botões (Abrir pasta / Executar)
            self.mostrar_mensagem(self.tr("Camada exportada para KML em {execution_time:.2f} segundos").format(execution_time=execution_time), "Sucesso", caminho_pasta=os.path.dirname(caminho_arquivo), caminho_arquivos=caminho_arquivo)

        except Exception as e:
            # Em erro, também remova a barra de progresso antes de avisar
            try:
                if progressMessageBar:
                    self.iface.messageBar().popWidget(progressMessageBar)
            except Exception:
                self.iface.messageBar().clearWidgets()
            self.mostrar_mensagem(self.tr("Falha ao criar/gravar KML: {error}").format(error=str(e)), "Erro")

        finally:
            self._kml_export_in_progress = False
            # solta a referência do diálogo com segurança
            try:
                dialog.deleteLater()
            except Exception:
                pass  # nosec B110
            self._icon_dialog_ref = None

    def _kml_on_rejected(self, msg=None):
        """Handler chamado quando o diálogo é cancelado/fechado."""
        try:
            self.iface.messageBar().clearWidgets()
        except Exception:
            pass  # nosec B110
        self._kml_export_in_progress = False

        dialog = getattr(self, "_icon_dialog_ref", None)
        if dialog is not None:
            try:
                dialog.hide()
                dialog.deleteLater()
            except Exception:
                pass  # nosec B110
        self._icon_dialog_ref = None

    def _kml_format_value(self, fields, field_name: str, value) -> str:
        """
        Formata valores para KML.

        Corrige QDate, QTime e QDateTime do PyQt/QGIS, evitando saídas
        como PyQt6.QtCore.QDateTime(...), e mantém a regra antiga de
        não exportar inteiros como "2.0".
        """
        if value is None:
            return ""

        # Trata NULL/invalid de objetos Qt, quando disponível.
        try:
            if hasattr(value, "isNull") and value.isNull():
                return ""
        except Exception:
            pass  # nosec B110

        try:
            if hasattr(value, "isValid") and not value.isValid():
                return ""
        except Exception:
            pass  # nosec B110

        # QDateTime
        try:
            if hasattr(value, "date") and hasattr(value, "time") and hasattr(value, "toString"):
                return value.toString("dd/MM/yyyy HH:mm:ss")
        except Exception:
            pass  # nosec B110

        # QDate
        try:
            if (hasattr(value, "year")
                and hasattr(value, "month")
                and hasattr(value, "day")
                and hasattr(value, "toString")):

                return value.toString("dd/MM/yyyy")
        except Exception:
            pass  # nosec B110

        # QTime
        try:
            if (hasattr(value, "hour")
                and hasattr(value, "minute")
                and hasattr(value, "second")
                and hasattr(value, "toString")):

                return value.toString("HH:mm:ss")
        except Exception:
            pass  # nosec B110

        # datetime/date/time nativos do Python
        try:
            if hasattr(value, "strftime"):
                if hasattr(value, "year") and hasattr(value, "hour"):
                    return value.strftime("%d/%m/%Y %H:%M:%S")
                if hasattr(value, "year"):
                    return value.strftime("%d/%m/%Y")
                if hasattr(value, "hour"):
                    return value.strftime("%H:%M:%S")
        except Exception:
            pass  # nosec B110

        # Detecta se o campo é do tipo inteiro.
        is_int_field = False
        try:
            if fields is not None:
                idx = fields.indexOf(field_name)
                if idx >= 0:
                    f = fields.field(idx)

                    int_types = set()
                    for type_name in ("Int", "LongLong", "UInt", "ULongLong"):
                        try:
                            int_types.add(getattr(QMetaType.Type, type_name))
                        except Exception:
                            pass  # nosec B110

                    try:
                        int_types.add(QVariant.UInt)
                    except Exception:
                        pass  # nosec B110

                    is_int_field = f.type() in int_types
        except Exception:
            pass  # nosec B110

        def _to_float(v):
            if isinstance(v, (int, float)):
                return float(v)

            s = str(v).strip()
            if not s:
                return None

            s = s.replace(",", ".").replace("\u2009", "").replace(" ", "")

            try:
                return float(s)
            except Exception:
                return None

        def _is_integer_like(f: float, eps: float = 1e-9) -> bool:
            return abs(f - round(f)) < eps

        # Se o campo é inteiro, tenta normalizar.
        if is_int_field:
            fval = _to_float(value)
            if fval is not None and _is_integer_like(fval):
                return str(int(round(fval)))
            return str(value)

        # Se não é inteiro, mas veio "2.0", normaliza só quando for inteiro-like.
        if isinstance(value, float):
            if _is_integer_like(value):
                return str(int(round(value)))
            return str(value)

        if isinstance(value, str):
            fval = _to_float(value)
            if fval is not None and _is_integer_like(fval):
                return str(int(round(fval)))
            return value

        return str(value)

    def criar_kml_em_memoria(self, layer, campo_id, icon_url, exportar_rotulos, progressBar, image_url, overlay_url, cor_rotulo_escolhida=None, escala_rotulo=1.0, escala_icone=1.0, transparencia_icone=0.0):
        """
        Cria o conteúdo KML em memória para a camada fornecida. A função realiza as seguintes etapas:

        1. Cria o elemento raiz do KML e o elemento Document.
        2. Obtém a cor do ícone e do rótulo da camada.
        3. Verifica se a camada está no sistema de referência de coordenadas WGS84 (EPSG:4326) e, se necessário, prepara a transformação de coordenadas.
        4. Itera sobre cada feição na camada e cria um Placemark para cada uma:
           - Adiciona um nome ao Placemark com o valor do campo ID.
           - Cria a tag Point com as coordenadas da feição.
           - Adiciona ExtendedData com os atributos da feição.
           - Define um estilo para o Placemark, incluindo ícone e rótulo.
        5. Atualiza a barra de progresso durante o processamento.
        6. Retorna o elemento raiz do KML.
        7. Cria um índice espacial para a camada

        Parâmetros:
        - layer (QgsVectorLayer): A camada de origem para a exportação.
        - campo_id (str): O campo de identificação a ser usado como nome dos Placemarks.
        - icon_url (str): A URL do ícone a ser usado para os Placemarks.
        - exportar_rotulos (bool): Indica se os rótulos devem ser exportados.
        - Adiciona um ScreenOverlay ao documento KML.
        - progressBar (QProgressBar): A barra de progresso a ser atualizada durante o processamento.

        Funcionalidades:
        - Criação de KML em memória com elementos e estilos configuráveis.
        - Transformação de coordenadas para WGS84, se necessário.
        - Adição de dados estendidos e estilos personalizados para cada Placemark.
        - Atualização da barra de progresso para informar o progresso do usuário.
        
        Retorna:
        - xml.etree.ElementTree.Element: O elemento raiz do KML criado.
        """
        # Cria um índice espacial para a camada
        spatial_index = QgsSpatialIndex()
        for feature in layer.getFeatures():
            spatial_index.insertFeature(feature)

        # Cria o elemento raiz do KML
        kml = XmlET.Element('kml', xmlns="http://www.opengis.net/kml/2.2")
        document = XmlET.SubElement(kml, 'Document')

        cor_icone = self.aplicar_transparencia_kml(self.obter_cor_icone(layer), transparencia_icone)

        if cor_rotulo_escolhida is not None and cor_rotulo_escolhida.isValid():
            cor_rotulo_kml = self.qcolor_para_kml(cor_rotulo_escolhida)
        else:
            cor_rotulo_kml = self.obter_cor_rotulo(layer)

        cor_rotulo_html = '#' + cor_rotulo_kml[6:] + cor_rotulo_kml[4:6] + cor_rotulo_kml[2:4]

        # Cor usada exclusivamente no título do balão de informações
        cor_titulo_balloon_html = cor_rotulo_html

        cor_escolhida_valida = (
            isinstance(cor_rotulo_escolhida, QColor)
            and cor_rotulo_escolhida.isValid())

        # Se o usuário solicitou rótulos, mas a camada não possui
        # rotulagem ativa, usa preto somente no título do balão.
        if (exportar_rotulos
            and not layer.labelsEnabled()
            and not cor_escolhida_valida):
            cor_titulo_balloon_html = "#000000"

        # Verifica se a camada já está em WGS84 (EPSG:4326)
        if layer.crs().authid() != 'EPSG:4326':
            # Define o sistema de referência de coordenadas para WGS84 (usado pelo KML)
            crsDestino = QgsCoordinateReferenceSystem(4326)  # WGS84
            transform = QgsCoordinateTransform(layer.crs(), crsDestino, QgsProject.instance())
            transformar = True
        else:
            transformar = False

        # Itera sobre cada feição na camada e cria um Placemark
        for i, feature in enumerate(layer.getFeatures(), start=1):
            placemark = XmlET.SubElement(document, 'Placemark')

            # Adiciona um nome ao Placemark com o valor do campo ID
            name = XmlET.SubElement(placemark, 'name')
            name.text = self._kml_format_valor_rotulo(layer, feature, campo_id)

            # Cria a tag Point com as coordenadas
            point = XmlET.SubElement(placemark, 'Point')
            coordinates = XmlET.SubElement(point, 'coordinates')
            geom = feature.geometry()
            # Aplica a transformação de coordenadas se necessário
            if transformar:
                geom.transform(transform)

            coord_text = f"{geom.asPoint().x()},{geom.asPoint().y()},0"  # Adicione altitude se necessário
            coordinates.text = coord_text

            # Adiciona ExtendedData com os atributos da feição
            extended_data = XmlET.SubElement(placemark, 'ExtendedData')
            for field in layer.fields():
                data = XmlET.SubElement(extended_data, 'Data', name=field.name())
                value = XmlET.SubElement(data, 'value')
                value.text = self._kml_format_value(layer.fields(), field.name(), feature[field.name()])

            # Define um estilo para o Placemark
            style = XmlET.SubElement(placemark, 'Style')
            icon_style = XmlET.SubElement(style, 'IconStyle')
            label_style = XmlET.SubElement(style, 'LabelStyle')

            # self.gerar_balloon_style(feature, campo_id, style, cor_rotulo_html, image_url, overlay_url)

            self.gerar_balloon_style(
                feature,
                campo_id,
                style,
                cor_titulo_balloon_html,
                image_url,
                overlay_url)

            # Condições para escala do ícone e rótulo
            if icon_url:
                icon = XmlET.SubElement(icon_style, 'Icon')
                href = XmlET.SubElement(icon, 'href')
                href.text = icon_url

                # Define a ponta inferior central do ícone como ponto de ancoragem
                XmlET.SubElement(
                    icon_style,
                    'hotSpot',
                    x="0.5",
                    y="0.0",
                    xunits="fraction",
                    yunits="fraction")

                color = XmlET.SubElement(icon_style, 'color')
                color.text = cor_icone

                icon_scale = XmlET.SubElement(icon_style, 'scale')
                icon_scale.text = f"{max(0.1, float(escala_icone)):.2f}"

                if not exportar_rotulos:
                    label_scale = XmlET.SubElement(label_style, 'scale')
                    label_scale.text = '0'

            if exportar_rotulos:
                label_scale = XmlET.SubElement(label_style, 'scale')
                label_scale.text = f"{max(0.0, float(escala_rotulo)):.2f}"

                color = XmlET.SubElement(label_style, 'color')
                color.text = cor_rotulo_kml

                if not icon_url:
                    icon_scale = XmlET.SubElement(icon_style, 'scale')
                    icon_scale.text = '0'

            progressBar.setValue(i)  # Atualiza a barra de progresso

        # Adiciona ScreenOverlay apenas se overlay_url for fornecida e não for vazia
        if overlay_url:
            # Redimensiona a imagem obtida a partir do URL
            imagem_redimensionada, nova_largura, nova_altura = self.redimensionar_imagem_proporcional_url(overlay_url, 300, 150)

            if imagem_redimensionada is not None:
                # Adiciona o ScreenOverlay ao KML usando a imagem redimensionada
                screen_overlay = XmlET.SubElement(document, 'ScreenOverlay') # Cria o elemento ScreenOverlay no documento KML
                name = XmlET.SubElement(screen_overlay, 'name')  # Define o nome do ScreenOverlay
                name.text = 'logo'

                # Define o ícone do ScreenOverlay, utilizando a URL da imagem fornecida
                icon = XmlET.SubElement(screen_overlay, 'Icon')
                href = XmlET.SubElement(icon, 'href')
                href.text = overlay_url

                # Configura a posição e o tamanho do overlay na tela
                overlay_xy = XmlET.SubElement(screen_overlay, 'overlayXY', x="1", y="1", xunits="fraction", yunits="fraction")
                screen_xy = XmlET.SubElement(screen_overlay, 'screenXY', x=f"{nova_largura}", y=f"{nova_altura}", xunits="pixels", yunits="pixels")
                rotation_xy = XmlET.SubElement(screen_overlay, 'rotationXY', x="0", y="0", xunits="fraction", yunits="fraction")
                # Define o tamanho do ScreenOverlay
                size = XmlET.SubElement(screen_overlay, 'size', x=f"{nova_largura}", y=f"{nova_altura}", xunits="pixels", yunits="pixels")

        # Retorna o elemento raiz do KML
        return kml

    def gerar_balloon_style(self, feature, campo_id, style, cor_rotulo_html, image_url, overlay_url):
        """
        Gera o BalloonStyle (balão do KML) para uma feição.

        Conteúdo do BalloonStyle:
        1) (Opcional) Miniatura no topo (image_url) usando CSS (sem download no export).
        2) Cabeçalho com o ID (campo_id) formatado para evitar "2.0" quando for inteiro.
        3) Tabela HTML com todos os atributos da feição.
           - Se o valor parecer um URL (http/https), vira link clicável.

        Nota:
        - overlay_url não é usado aqui (normalmente é aplicado como ScreenOverlay fora deste método).
        """
        # 1) ID formatado, incluindo Data/Hora quando o campo de rótulo for temporal
        fields = feature.fields()
        id_txt = self._kml_format_value(fields, campo_id, feature[campo_id]) if campo_id else ""

        # 2) Miniatura no topo (SEM download no export)
        alt_imagem = _html.escape(self.tr("Imagem"), quote=True)

        imagem_html = ""
        if image_url:
            safe_url = _html.escape(str(image_url), quote=True)
            imagem_html = (
                '<div style="text-align: center; padding: 10px 0;">'
                f'<img src="{safe_url}" style="max-width:150px; max-height:75px; width:auto; height:auto;" alt="{alt_imagem}">'
                '</div>')

        # 3) Tabela de atributos (links clicáveis)
        def _valor_para_html(nome_campo, valor) -> str:
            txt = self._kml_format_value(fields, nome_campo, valor).strip()
            if not txt:
                return ""

            # Se parecer URL, cria link
            if _re.match(r'https?://[^\s]+', txt):
                safe_href = _html.escape(txt, quote=True)
                return "<a href='{safe_href}'>{label}</a>".format(safe_href=safe_href, label=self.tr("Link de acesso"))

            return _html.escape(txt, quote=False)

        partes = []
        partes.append('<table border="1" style="border-collapse: collapse; border: 2px solid black; width: 100%;">')

        for field in feature.fields():
            cor_fundo = self.gerar_cor_suave()
            nome = field.name()
            nome_html = _html.escape(nome, quote=False)
            valor_html = _valor_para_html(nome, feature[nome])

            partes.append('<tr><td>')
            partes.append(f'<table border="0" style="background-color: {cor_fundo}; width: 100%;">')
            partes.append(f'<tr>'
                f'<td style="text-align: left;"><b>{nome_html}</b></td>'
                f'<td style="text-align: right;">{valor_html}</td>'
                f'</tr>')
            partes.append('</table>')
            partes.append('</td></tr>')

        partes.append('</table>')
        tabela_geral_html = "".join(partes)

        # 4) Monta o BalloonStyle no XML do KML
        balloon_style = XmlET.SubElement(style, 'BalloonStyle')
        text = XmlET.SubElement(balloon_style, 'text')

        cor_titulo = _html.escape(str(cor_rotulo_html or "#000000"), quote=True)
        campo_id_html = _html.escape(str(campo_id or ""), quote=False)
        id_txt_html = _html.escape(str(id_txt), quote=False)
        titulo_tabela = _html.escape(self.tr("Tabela de Informações:"), quote=False)

        balloon_html = f"""{imagem_html}<h3 style="margin-bottom:1px; color:{cor_titulo};">{campo_id_html}: {id_txt_html}</h3><p>{titulo_tabela}</p>{tabela_geral_html}"""
        text.text = balloon_html

    def redimensionar_imagem_proporcional_url(self, url_imagem, largura_max, altura_max):
        """
        Baixa a imagem de um URL e redimensiona proporcionalmente para caber dentro de uma caixa de largura e altura máximas.

        Parâmetros:
        - url_imagem (str): URL da imagem a ser redimensionada.
        - largura_max (int): Largura máxima da caixa.
        - altura_max (int): Altura máxima da caixa.

        Retorna:
        - Uma instância de `PIL.Image.Image` redimensionada proporcionalmente.
        - As novas dimensões da imagem (largura, altura).
        """
        headers = {
            'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/58.0.3029.110 Safari/537.3'}  # Define o cabeçalho de User-Agent para a solicitação HTTP

        try:
            response = requests.get(url_imagem, headers=headers, timeout=(10, 20))  # Faz o download da imagem do URL com o cabeçalho definido
            response.raise_for_status()  # Verifica se o download foi bem-sucedido

            imagem = Image.open(BytesIO(response.content))  # Abre a imagem a partir do conteúdo baixado
            largura_original, altura_original = imagem.size  # Obtém as dimensões originais da imagem

            proporcao_largura = largura_max / largura_original  # Calcula a proporção para a largura
            proporcao_altura = altura_max / altura_original  # Calcula a proporção para a altura
            proporcao_final = min(proporcao_largura, proporcao_altura)  # Usa a menor proporção para manter a imagem dentro da caixa

            nova_largura = int(largura_original * proporcao_final)  # Calcula a nova largura proporcional
            nova_altura = int(altura_original * proporcao_final)  # Calcula a nova altura proporcional

            imagem_redimensionada = imagem.resize((nova_largura, nova_altura), Image.LANCZOS)  # Redimensiona a imagem

            return imagem_redimensionada, nova_largura, nova_altura  # Retorna a imagem redimensionada e as novas dimensões

        except UnidentifiedImageError:
            # Captura o erro se a imagem não puder ser identificada e exibe uma mensagem de erro
            self.mostrar_mensagem(self.tr("Erro ao abrir a imagem. O arquivo não é uma imagem válida ou está corrompido."), "Erro")
            return None, None, None  # Retorna None se ocorrer um erro

        except Exception as e:
            # Captura qualquer outro erro, exibe uma mensagem de erro e continua
            self.mostrar_mensagem(self.tr("Erro ao processar a imagem: {error}").format(error=str(e)), "Erro")
            return None, None, None  # Retorna None se ocorrer um erro

    def exportar_para_dxf(self):
        """
        Exporta a camada selecionada para um arquivo DXF.

        Funcionalidades principais:
        1. Obtém a camada selecionada no treeView.
        2. Valida se a camada existe no projeto.
        3. Obtém a lista de campos disponíveis na camada.
        4. Filtra apenas campos do tipo STRING para validação.
        5. Verifica valores inválidos (vazios ou com caracteres proibidos) nesses campos string.
        6. Caso haja valores inválidos, mostra mensagem de erro e interrompe.
        7. Cria um documento DXF vazio (versão R2013).
        8. Inicializa o diálogo de escolha de blocos e campos.
        9. Executa o diálogo para permitir que o usuário configure exportação.
        10. Se o usuário confirmar, coleta configurações escolhidas:
            - Campo de agrupamento (campoEscolhido).
            - Valores selecionados.
            - Cores escolhidas.
            - Campos adicionais para rótulos.
            - Campo Z (para 3D).
            - Blocos selecionados para cada valor.
        11. Chama a função `exportar_camada_para_dxf` passando todas as configurações.
        """
        # Obtém a seleção atual no QTreeView
        indexes = self.dlg.treeViewListaPonto.selectionModel().selectedIndexes()
        if not indexes:
            self.mostrar_mensagem(self.tr("Selecione uma camada para exportar."), "Erro")
            return

        # Obtém o nome da camada selecionada
        selected_layer_name = self.treeViewModel.itemFromIndex(indexes[0]).text()
        layer = QgsProject.instance().mapLayersByName(selected_layer_name)[0]
        if not layer:
            self.mostrar_mensagem(self.tr("Camada não encontrada."), "Erro")
            return

        # Obtém os nomes de todos os campos
        campos = [field.name() for field in layer.fields()]

        # Filtra apenas campos string para validação
        campos_string = [
            f.name() for f in layer.fields()
            if layer.fields().field(f.name()).type() in (QMetaType.Type.QString, QVariant.StringList)]

        # Inicializa dicionário para armazenar campos inválidos
        campos_invalidos = {}
        caracteres_invalidos = set("/|\\*?%$#@!~")  # caracteres proibidos  # caracteres proibidos

        # Função auxiliar para checar se valor é inválido
        def valor_invalido(valor):
            if valor is None or str(valor).strip() == "":
                return True

            if any(char in caracteres_invalidos
                for char in str(valor)):
                return True

            return False

        # Valida apenas valores de campos string
        for feature in layer.getFeatures():
            for campo in campos_string:
                valor = feature[campo]
                if valor_invalido(valor):
                    if campo not in campos_invalidos:
                        campos_invalidos[campo] = []
                    campos_invalidos[campo].append(feature.id())

        # Se encontrou problemas, mostra erro e retorna
        if campos_invalidos:
            mensagem_erro = self.tr("Valores inválidos ou vazios encontrados nos seguintes campos (STRING):\n")
            for campo, ids in campos_invalidos.items():
                mensagem_erro += self.tr("{campo} (IDs: {ids})\n").format(campo=campo, ids=", ".join(map(str, ids)))
            self.mostrar_mensagem(mensagem_erro, "Erro")
            return

        # Cria novo documento DXF
        doc = ezdxf.new(dxfversion='R2013')
        cores = {}

        # Abre diálogo de escolha de blocos e configurações
        dialogo = BlocoEscolhaDialogo(campos, layer, self.dlg)
        self.dialogo = BlocoEscolhaDialogo(campos, layer, self.dlg)

        # Se usuário confirmou o diálogo
        if dialogo.exec() == QDialog.DialogCode.Accepted:
            cores = dialogo.cores
            nomes_blocos = self.dialogo.criar_blocos(doc, cores)
            campoEscolhido = dialogo.getCampoEscolhido()
            selecoes = dialogo.getSelecoes()
            camposSelecionados = dialogo.getCamposSelecionados() if hasattr(dialogo, 'camposCheckBoxes') else []
            campoZ = dialogo.getCampoZ()
            blocoSelecionado = dialogo.getBlocoSelecionado()

            # Só exporta se tiver campoEscolhido e seleções válidas
            if campoEscolhido and selecoes:
                self.exportar_camada_para_dxf(
                    layer, campoEscolhido, selecoes, cores,
                    camposSelecionados, campoZ, blocoSelecionado)

    def exportar_camada_para_dxf(self, layer, campoEscolhido, selecoes, cores, camposSelecionados, campoZ, blocoSelecoes):
        """
        Exporta a camada selecionada para um arquivo DXF.

        Regras de Z:
          - campoZ == "__GEOM_Z__": usar Z da geometria (se existir).
          - campoZ = nome de campo numérico: usar valor do campo.
          - caso contrário: exporta 2D.

        Suporta Point e MultiPoint. Em "Camada_0", tudo vai na mesma layer.
        """
        def _sanitize_name(name: str) -> str:
            return re.sub(r'[<>/\\:";?*|=,]', '_', str(name))[:255]

        def _z_from_attr(val):
            """Converte valor de atributo para float Z (aceita vírgula decimal). Retorna (z_float, ok_bool)."""
            if val is None:
                return 0.0, False
            if isinstance(val, (int, float)):
                return float(val), True
            s = str(val).strip()
            if not s:
                return 0.0, False
            s = s.replace(',', '.').replace('\u2009', '').replace(' ', '')
            try:
                return float(s), True
            except Exception:
                return 0.0, False

        def _iter_points(geom):
            """
            Retorna lista de QgsPoint usando a API de vértices (preserva Z).
            Funciona para Point e MultiPoint. Fallbacks mantidos por segurança.
            """
            pts = []
            try:
                it = geom.vertices()
                for p in it:
                    pts.append(p)  # QgsPoint (3D se houver)
            except Exception:
                pass  # nosec B110
            if not pts:
                # fallbacks conservadores
                try:
                    if geom.type() == QgsWkbTypes.GeometryType.PointGeometry and geom.isMultipart():
                        for p in (geom.asMultiPoint() or []):
                            pts.append(p)
                    else:
                        p = geom.asPoint()
                        if p:
                            pts.append(p)
                except Exception:
                    try:
                        p = geom.asPoint()
                        if p:
                            pts.append(p)
                    except Exception:
                        pass  # nosec B110
            return pts

        # (Opcional) índice espacial mantido
        try:
            spatial_index = QgsSpatialIndex()
            for ft_ in layer.getFeatures():
                spatial_index.insertFeature(ft_)
        except Exception:
            pass  # nosec B110

        nome_camada = layer.name()
        caminho_arquivo = self.escolher_local_para_salvar(f"{_sanitize_name(nome_camada)}.dxf", "DXF Files (*.dxf)")
        if not caminho_arquivo:
            return

        doc = ezdxf.new(dxfversion='R2013')
        msp = doc.modelspace()

        # blocos
        self.nomes_blocos = []
        if hasattr(self, 'dialogo') and hasattr(self.dialogo, 'criar_blocos'):
            try:
                self.nomes_blocos = self.dialogo.criar_blocos(doc, cores) or []
            except Exception:
                self.nomes_blocos = []

        # layers (true_color quando disponível)
        for valor_atributo, cor_rgb in (cores or {}).items():
            dxf_layer = _sanitize_name(valor_atributo)
            try:
                if dxf_layer not in doc.layers:
                    doc.layers.new(name=dxf_layer, dxfattribs={'true_color': rgb2int(cor_rgb)})
            except Exception:
                try:
                    if dxf_layer not in doc.layers:
                        doc.layers.new(name=dxf_layer)
                except Exception:
                    pass  # nosec B110

        # parâmetros de rótulo
        altura_texto = 0.5
        deslocamento_y = altura_texto * 1.2
        deslocamento_x = altura_texto * (-2.7)

        # progresso
        progressBar, progressMessageBar = self.iniciar_progress_bar(layer)
        total_feats = max(1, layer.featureCount())
        try:
            progressBar.setMaximum(total_feats)
            progressBar.setValue(0)
        except Exception:
            pass  # nosec B110
        start_time = time.time()

        modo_camada = (campoEscolhido == "Camada_0")
        selecoes_str = {str(nome_camada)} if modo_camada else {str(s) for s in (selecoes or set())}
        use_geom_z = (campoZ == "__GEOM_Z__")

        for i, feature in enumerate(layer.getFeatures(), start=1):
            # valor/layer alvo
            valor_atributo = nome_camada if modo_camada else feature[campoEscolhido]
            if modo_camada or str(valor_atributo) in selecoes_str:
                geom = feature.geometry()
                if not geom or geom.isEmpty():
                    try: progressBar.setValue(i)
                    except Exception: pass  # nosec B110
                    continue

                # pontos preservando Z
                pts = _iter_points(geom)

                dxf_layer = _sanitize_name(valor_atributo if not modo_camada else nome_camada)
                if dxf_layer not in doc.layers:
                    cor_rgb = (cores or {}).get(valor_atributo)
                    try:
                        if cor_rgb is not None:
                            doc.layers.new(name=dxf_layer, dxfattribs={'true_color': rgb2int(cor_rgb)})
                        else:
                            doc.layers.new(name=dxf_layer)
                    except Exception:
                        pass  # nosec B110

                # checagens de 3D
                geom_has_z = geom.is3D() if hasattr(geom, "is3D") else QgsWkbTypes.hasZ(geom.wkbType())

                for pt in pts:
                    if not pt:
                        continue

                    x, y = pt.x(), pt.y()
                    is_3d = False
                    z = 0.0

                    # 1) Z da geometria (quando solicitado e disponível)
                    if use_geom_z and geom_has_z:
                        try:
                            # prefira pt.is3D() se existir (QgsPoint), senão confie em geom_has_z
                            pt_has_z = pt.is3D() if hasattr(pt, "is3D") else geom_has_z
                            if pt_has_z:
                                z = float(pt.z())
                                is_3d = True
                        except Exception:
                            is_3d = False

                    # 2) Z por atributo (se definido e não usamos o Z geom)
                    if (not is_3d) and campoZ and campoZ != "__GEOM_Z__":
                        try:
                            valz = feature[campoZ]
                        except Exception:
                            valz = None
                        z_attr, ok_attr = _z_from_attr(valz)
                        if ok_attr:
                            z = z_attr
                            is_3d = True

                    # 3) adiciona o ponto
                    if is_3d:
                        msp.add_point((x, y, z), dxfattribs={'layer': dxf_layer})
                    else:
                        msp.add_point((x, y), dxfattribs={'layer': dxf_layer})

                    # bloco (opcional)
                    blocoNome = None
                    if isinstance(blocoSelecoes, dict):
                        blocoNome = blocoSelecoes.get(valor_atributo, blocoSelecoes.get(str(valor_atributo)))
                    if blocoNome and (self.nomes_blocos and blocoNome in self.nomes_blocos):
                        try:
                            br = msp.add_blockref(blocoNome, (x, y), dxfattribs={'layer': dxf_layer})
                            br.dxf.xscale = br.dxf.yscale = br.dxf.zscale = 1.0
                            br.dxf.rotation = 0.0
                        except Exception:
                            pass  # nosec B110

                    # rótulos (opcionais)
                    if camposSelecionados:
                        y_offset = y + (altura_texto / 2.0)
                        x_offset = x - (deslocamento_x / 2.0)
                        for campo in camposSelecionados:
                            try:
                                texto = feature[campo]
                            except Exception:
                                texto = ""
                            try:
                                msp.add_text(str(texto), dxfattribs={'insert': (x_offset, y_offset), 'height': altura_texto, 'layer': dxf_layer})
                            except Exception:
                                pass  # nosec B110
                            y_offset -= deslocamento_y

            try: progressBar.setValue(i)
            except Exception: pass  # nosec B110

        doc.saveas(caminho_arquivo)
        execution_time = time.time() - start_time

        try: self.iface.messageBar().clearWidgets()
        except Exception: pass  # nosec B110

        self.mostrar_mensagem(self.tr("Arquivo DXF salvo com sucesso em {execution_time:.2f} segundos").format(execution_time=execution_time), "Sucesso", caminho_pasta=os.path.dirname(caminho_arquivo), caminho_arquivos=caminho_arquivo)

    def _processar_kml_kmz_pontos(self, file_path: str, layer_name: str) -> list[QgsVectorLayer]:
        """
        Processa arquivos KML/KMZ com uma ou várias pastas/sublayers.

        - Varre todas as sublayers expostas pelo OGR/QGIS.
        - Cria uma camada em memória para cada pasta/sublayer que contenha pontos.
        - Mantém apenas Point/MultiPoint.
        - Para MultiPoint, cada ponto vira uma feição independente.
        - Retorna uma lista de QgsVectorLayer.
        """
        base = QgsVectorLayer(file_path, layer_name, "ogr")
        if not base.isValid():
            self.mostrar_mensagem(self.tr("Falha ao carregar KML/KMZ."), "Erro")
            return []

        campos_para_remover = {
            "description", "timestamp", "begin", "end",
            "altitudeMode", "tessellate", "extrude", "drawOrder",
            "visibility", "icon"}

        campos_fixos = [
            QgsField("ID", QMetaType.Type.Int),
            QgsField("X", QMetaType.Type.Double),
            QgsField("Y", QMetaType.Type.Double),
            QgsField("X_GMS", QMetaType.Type.QString),
            QgsField("Y_GMS", QMetaType.Type.QString)]

        nomes_fixos = {c.name() for c in campos_fixos}

        def _nome_limpo(txt):
            txt = str(txt or "").strip()
            txt = re.sub(r"[\\/:*?\"<>|]+", "_", txt)
            txt = re.sub(r"\s+", " ", txt)
            return txt or self.tr("Sem_nome")

        def _nome_unico(base_nome, usados):
            nome = _nome_limpo(base_nome)
            if nome not in usados:
                usados.add(nome)
                return nome

            i = 1
            while f"{nome}_{i}" in usados:
                i += 1

            novo = f"{nome}_{i}"
            usados.add(novo)
            return novo

        def _extrair_nome_sublayer(info):
            """
            O formato mais comum do QGIS/OGR é algo como:
            id!!::!!nome!!::!!featureCount!!::!!geometryType!!::!!...
            """
            partes = str(info).split("!!::!!")
            if len(partes) >= 2 and partes[1].strip():
                return partes[1].strip()

            return str(info).strip()

        def _criar_memoria_da_origem(origem: QgsVectorLayer, nome_memoria: str):
            if origem is None or not origem.isValid():
                return None

            crs_authid = origem.crs().authid()
            if not crs_authid:
                crs_authid = "EPSG:4326"

            campos_origem = [
                f for f in origem.fields()
                if f.name() not in campos_para_remover
                and f.name() not in nomes_fixos]

            uri = f"Point?crs={crs_authid}"
            mem = QgsVectorLayer(uri, nome_memoria, "memory")
            if not mem.isValid():
                return None

            prov = mem.dataProvider()
            prov.addAttributes(campos_fixos + campos_origem)
            mem.updateFields()

            # Conta pontos reais para barra de progresso
            feature_count = 0
            for feat in origem.getFeatures():
                geom = feat.geometry()
                if not geom or geom.isEmpty():
                    continue

                if QgsWkbTypes.geometryType(geom.wkbType()) != QgsWkbTypes.GeometryType.PointGeometry:
                    continue

                if geom.isMultipart():
                    feature_count += len(geom.asMultiPoint())
                else:
                    feature_count += 1

            if feature_count == 0:
                return None

            progressBar, progressMsgBar = self.iniciar_progress_bar(
                origem,
                message=self.tr('Carregando pontos de "{nome_memoria}", aguarde...').format(nome_memoria=nome_memoria))
            progressBar.setValue(0)
            progressBar.setMaximum(feature_count)

            feats = []
            idx = 1
            processed = 0
            casas = 6 if mem.crs().isGeographic() else 3

            try:
                for feat in origem.getFeatures():
                    geom = feat.geometry()
                    if not geom or geom.isEmpty():
                        continue

                    if QgsWkbTypes.geometryType(geom.wkbType()) != QgsWkbTypes.GeometryType.PointGeometry:
                        continue

                    if geom.isMultipart():
                        pontos = geom.asMultiPoint()
                    else:
                        pontos = [geom.asPoint()]

                    for pt in pontos:
                        if pt is None:
                            continue

                        pt_xy = QgsPointXY(pt)

                        f = QgsFeature()
                        f.setGeometry(QgsGeometry.fromPointXY(pt_xy))

                        x = round(pt_xy.x(), casas)
                        y = round(pt_xy.y(), casas)

                        if hasattr(self, "calcular_dms_do_ponto"):
                            x_dms, y_dms = self.calcular_dms_do_ponto(mem, pt_xy)
                        else:
                            x_dms = self.calcular_posicao_xy(pt_xy.x())
                            y_dms = self.calcular_posicao_xy(pt_xy.y())

                        attrs = [idx, x, y, x_dms, y_dms]

                        for field in campos_origem:
                            try:
                                attrs.append(feat[field.name()])
                            except Exception:
                                attrs.append(None)

                        f.setAttributes(attrs)
                        feats.append(f)

                        idx += 1
                        processed += 1

                        try:
                            progressBar.setValue(processed)
                        except RuntimeError:
                            self.mostrar_mensagem(self.tr("Processo cancelado pelo usuário."), "Aviso")
                            return None

                        QCoreApplication.processEvents()

            finally:
                try:
                    self.iface.messageBar().popWidget(progressMsgBar)
                except Exception:
                    pass  # nosec B110

            if not feats:
                return None

            prov.addFeatures(feats)
            mem.updateExtents()

            try:
                if origem.renderer():
                    mem.setRenderer(origem.renderer().clone())
            except Exception:
                pass  # nosec B110

            return mem

        # Descobre todas as pastas/sublayers do KML/KMZ
        candidatos = []

        try:
            sublayers = base.dataProvider().subLayers()
        except Exception:
            sublayers = []

        if sublayers:
            for info in sublayers:
                sub_name = _extrair_nome_sublayer(info)
                if not sub_name:
                    continue

                uri = f"{file_path}|layername={sub_name}"
                candidatos.append((uri, sub_name))
        else:
            candidatos.append((file_path, layer_name))

        layers_out = []
        nomes_usados = set()

        for uri, sub_name in candidatos:
            origem = QgsVectorLayer(uri, sub_name, "ogr")
            if not origem.isValid():
                continue

            nome_memoria = _nome_unico(f"{layer_name}_{sub_name}", nomes_usados)
            mem = _criar_memoria_da_origem(origem, nome_memoria)

            if mem and mem.isValid() and mem.featureCount() > 0:
                layers_out.append(mem)

        if not layers_out:
            self.mostrar_mensagem(self.tr("Nenhuma feição de ponto encontrada nas pastas do KML/KMZ."), "Aviso")

        return layers_out

    def _copiar_para_memoria_ponto(self, src: QgsVectorLayer, new_name: str) -> QgsVectorLayer:
        """
        Cria uma cópia em memória da camada `src`, mantendo apenas feições de ponto.

        O que esta função faz:
        1. Cria uma camada vetorial em memória, com o mesmo tipo de geometria (Point) e CRS da camada original.
        2. Copia todos os campos (atributos) da camada original para a camada em memória.
        3. Filtra e copia apenas as feições cuja geometria é do tipo ponto (Point ou MultiPoint).
        4. Copia a simbologia (renderer) da camada original para manter o mesmo estilo visual.
        5. Retorna a nova camada criada em memória.
        
        Parâmetros:
            src      : QgsVectorLayer
                Camada de origem, pode conter vários tipos de feição (serão filtrados apenas pontos).
            new_name : str
                Nome desejado para a camada em memória.

        Retorno:
            QgsVectorLayer
                Nova camada de pontos criada em memória.
        """

        # Define URI da camada (tipo de geometria + CRS)
        mem_uri = f"{QgsWkbTypes.displayString(src.wkbType())}?crs={src.crs().authid()}"
        mem = QgsVectorLayer(mem_uri, new_name, "memory")
        mem_dp = mem.dataProvider()

        # Copia todos os campos da camada original
        mem_dp.addAttributes(src.fields())
        mem.updateFields()

        # Filtra e copia apenas feições do tipo ponto
        feats = [f for f in src.getFeatures()
                 if QgsWkbTypes.geometryType(f.geometry().wkbType()) == QgsWkbTypes.GeometryType.PointGeometry]
        mem_dp.addFeatures(feats)
        mem.updateExtents()

        # Copia a simbologia do layer original (mantém visual)
        mem.setRenderer(src.renderer().clone())

        return mem

    def _limpar_nome_kml_kmz(self, nome: str) -> str:
        """
        Limpa nomes vindos de KML/KMZ:
        - remove caminho completo;
        - remove .kml/.kmz;
        - remove resíduos de URI do OGR;
        - organiza espaços.
        """
        nome = str(nome or "").strip()

        # Se vier caminho completo
        nome = os.path.basename(nome)

        # Se vier URI do OGR
        nome = nome.replace("|layername=", "_")

        # Remove extensão KML/KMZ em qualquer final útil
        nome = re.sub(r"\.(kml|kmz)$", "", nome, flags=re.IGNORECASE)

        # Limpeza final
        nome = re.sub(r"\s+", " ", nome)
        nome = nome.strip(" _-|")

        return nome or "Camada"

    def _inferir_nome_grupo_kml(self, nome_arquivo: str, layers: list) -> str:
        """
        Tenta identificar o nome do grupo a partir do prefixo comum das camadas.
        Exemplo:
        - 'Lugares temporários Clone Excluir Ponto Temp 1.kml'
        - 'Lugares temporários_Ponto Temp 1.kml'
        vira grupo: 'Lugares temporários'
        """
        nomes = []
        for lyr in layers:
            if lyr and lyr.isValid():
                n = self._limpar_nome_kml_kmz(lyr.name())
                n = n.replace("_", " ")
                n = re.sub(r"\s+", " ", n).strip()
                if n:
                    nomes.append(n)

        if len(nomes) >= 2:
            tokens = [n.split() for n in nomes if n.split()]
            comum = []

            for grupo_tokens in zip(*tokens):
                valores = {t.lower() for t in grupo_tokens}
                if len(valores) == 1:
                    comum.append(grupo_tokens[0])
                else:
                    break

            if len(comum) >= 2:
                return self._limpar_nome_kml_kmz(" ".join(comum))

        return self._limpar_nome_kml_kmz(nome_arquivo)

    def _limpar_nome_camada_no_grupo(self, nome_camada: str, nome_grupo: str) -> str:
        """
        Remove do nome da camada:
        - .kml/.kmz;
        - nome do grupo no início;
        - separadores sobrando.
        """
        nome = self._limpar_nome_kml_kmz(nome_camada)
        grupo = self._limpar_nome_kml_kmz(nome_grupo)

        if grupo and nome.lower().startswith(grupo.lower()):
            nome = nome[len(grupo):].strip(" _-|")

        nome = re.sub(r"\s+", " ", nome)
        nome = nome.strip(" _-|")

        return nome or self._limpar_nome_kml_kmz(nome_camada)

    def _nome_unico_lista(self, nome: str, usados: set) -> str:
        """
        Garante nomes únicos no lote importado.
        """
        base = self._limpar_nome_kml_kmz(nome)
        nome_final = base
        i = 1

        while nome_final.lower() in usados:
            nome_final = f"{base}_{i}"
            i += 1

        usados.add(nome_final.lower())
        return nome_final

    def carregar_texto_dxf(self, path_dxf: str, nome_layer: str, crs_authid: str = "EPSG:4326") -> QgsVectorLayer | None:
        """
        Lê um arquivo DXF e, se houver entidades de texto, cria uma camada de pontos em memória
        rotulada com o conteúdo e a formatação original, com suporte à cor ByLayer.

        Funcionalidades principais:
        1. Valida o caminho do arquivo DXF.
        2. Lê todas as entidades do tipo TEXT e MTEXT do modelspace do DXF usando ezdxf.
        3. Cria uma camada de pontos em memória (QGIS) com os campos:
            - text: conteúdo do texto.
            - height: altura do texto (quando disponível).
            - rotation: rotação (em graus, ajustada para sentido do QGIS).
            - x, y: coordenadas de inserção.
            - r, g, b: cor do texto (detecta true-color, ByLayer ou ACI, com fallback para preto em ByBlock).
        4. Monta um dicionário de cores das layers do DXF, para suportar textos com cor ByLayer.
        5. Para cada entidade, extrai atributos, converte e ajusta rotação, determina cor conforme prioridade:
            a. True-color direto (rgb);
            b. ByLayer (herda cor da layer do DXF);
            c. ByBlock ou sem cor definida: preto;
            d. Cor direta (ACI - AutoCAD Color Index).
        6. Adiciona todos os textos como feições à camada de pontos.
        7. Configura a camada para exibir rótulos (labels) com rotação e cor dinâmicas por campo.
        8. Torna o símbolo de ponto invisível para que apenas o texto apareça no mapa.

        Parâmetros:
            path_dxf   : str
                Caminho completo do arquivo DXF a ser lido.
            nome_layer : str
                Nome desejado para a camada criada.
            crs_authid : str (opcional)
                Código de referência espacial (ex: "EPSG:4326") para o sistema de coordenadas.

        Retorno:
            QgsVectorLayer | None
                Camada de pontos QGIS com textos e propriedades originais, ou None se não houver textos.
        """
        # Verifica existência do arquivo DXF
        if not path_dxf or not os.path.isfile(path_dxf):
            raise FileNotFoundError(self.tr("Caminho DXF inválido: {path}").format(path=repr(path_dxf)))

        doc = ezdxf.readfile(path_dxf)
        msp = doc.modelspace()
        entities = list(msp.query("TEXT MTEXT"))
        if not entities:
            return None  # Sem entidades de texto, retorna None

        # Cria camada de pontos em memória
        vl = QgsVectorLayer(f"Point?crs={crs_authid}", nome_layer, "memory")
        pr = vl.dataProvider()

        # Define os campos que serão utilizados na camada
        pr.addAttributes([
            QgsField("text",     QMetaType.Type.QString),
            QgsField("height",   QMetaType.Type.Double),
            QgsField("rotation", QMetaType.Type.Double),
            QgsField("x",        QMetaType.Type.Double),
            QgsField("y",        QMetaType.Type.Double),
            QgsField("r",        QMetaType.Type.Int),
            QgsField("g",        QMetaType.Type.Int),
            QgsField("b",        QMetaType.Type.Int)])
        vl.updateFields()

        # Monta dicionário de cores das layers (para suporte ao ByLayer)
        dxf_layers = {}
        for lay in doc.layers:
            aci = lay.color
            if hasattr(lay, 'rgb') and lay.rgb is not None:
                rgb = lay.rgb
            else:
                rgb = aci2rgb(aci)
            dxf_layers[lay.dxf.name] = rgb

        feats = []
        for ent in entities:
            # Obtém o texto (TEXT ou MTEXT)
            txt = ent.plain_text() if ent.dxftype() == "MTEXT" else ent.dxf.text
            ins = ent.dxf.insert  # Ponto de inserção
            rot = getattr(ent.dxf, "rotation", 0.0)  # Rotação bruta

            if rot is None:
                rot = 0.0
            # Converte rotação para graus, se necessário
            if rot > 2 * math.pi:
                rot = rot
            else:
                rot = math.degrees(rot)
            rot = -rot  # Ajusta sinal para QGIS

            ht = getattr(ent.dxf, "height", None)  # Altura do texto

            # === Determina a cor ===
            if hasattr(ent, 'rgb') and ent.rgb is not None:
                r, g, b = ent.rgb  # True-color
            else:
                aci = ent.dxf.color
                if aci == 256:  # ByLayer: pega cor do layer do DXF
                    layer_name = ent.dxf.layer
                    r, g, b = dxf_layers.get(layer_name, (0, 0, 0))
                elif aci == 0:  # ByBlock (ou indefinido): preto
                    r, g, b = (0, 0, 0)
                else:
                    r, g, b = aci2rgb(aci)  # ACI normal

            # Cria feature com atributos
            f = QgsFeature(vl.fields())
            f.setAttributes([txt, ht, rot, ins.x, ins.y, r, g, b])
            f.setGeometry(QgsGeometry.fromPointXY(QgsPointXY(ins.x, ins.y)))
            feats.append(f)

        # Adiciona feições à camada
        if feats:
            pr.addFeatures(feats)
            vl.updateExtents()
            vl.triggerRepaint()

        # Configura os rótulos da camada
        pal = QgsPalLayerSettings()  # Cria configurações de rótulos
        pal.fieldName = "text"  # Define o campo usado para os rótulos (conteúdo do texto)
        pal.placement = Qgis.LabelPlacement.OverPoint  # Define o posicionamento dos rótulos sobre os pontos

        # Configura a rotação dos rótulos com base no campo "rotation"
        pal.dataDefinedProperties().setProperty(
            QgsPalLayerSettings.Property.Rotation,
            QgsProperty.fromField("rotation"))  # Vincula o campo "rotation" à propriedade de rotação

        # Configura o posicionamento dos rótulos com base no campo "rotation"
        expression_rotation = f'"rotation"'  # Usa o campo "rotation" diretamente como expressão
        pal.dataDefinedProperties().setProperty(
            QgsPalLayerSettings.Property.LabelRotation,
            QgsProperty.fromExpression(expression_rotation))  # Aplica a rotação à posição dos rótulos

        # Configura a cor dos rótulos com base nos campos r, g, b
        pal.dataDefinedProperties().setProperty(
            QgsPalLayerSettings.Property.Color,
            QgsProperty.fromExpression('color_rgba("r","g","b",255)'))  # Define a cor usando RGBA

        # Aplica as configurações de rótulos à camada
        vl.setLabeling(QgsVectorLayerSimpleLabeling(pal))
        vl.setLabelsEnabled(True)  # Habilita os rótulos

        # Define um símbolo de ponto "invisível" para evitar sobreposição visual
        symbol = QgsMarkerSymbol.createSimple({"name": "circle", "size": "0"})  # Cria símbolo circular com tamanho 0
        vl.renderer().setSymbol(symbol)  # Define o símbolo para o renderizador da camada

        return vl  # Retorna a camada vetorial criada

    def _processar_dxf_pontos(self, file_path: str, layer_name: str, manter_original: bool = False) -> tuple[QgsVectorLayer | None, QgsVectorLayer | None]:
        """
        Lê um arquivo DXF contendo entidades POINT, cria e devolve uma camada
        temporária em memória (Point ou PointZ) pronta para uso no QGIS.

        Fluxo resumido
        1. Exibe uma barra indeterminada de “preparação”.
        2. Carrega as entidades POINT via OGR com **skipCrsValidation** para
           impedir o prompt automático de SRC.
        3. Se o DXF não possuir SRC, solicita ao usuário **uma única vez** –
           cancela todo o processo se o diálogo for fechado sem escolha.
        4. Lê o DXF bruto com *ezdxf* apenas para extrair o valor **Z** de cada
           ponto.
        5. Cria camada “memory” com campos fixos `[ID, X, Y, Z]` +
           todos os atributos relevantes do DXF (exceto PaperSpace, SubClasses,
           Linetype, EntityHandle e Text).
        6. Popula a camada, atualizando uma barra de progresso; se o usuário
           fechar a barra, o processamento é interrompido de forma limpa.
        7. Remove todas as barras (preparação / progresso) ao final ou na
           ocorrência de erro, exibindo mensagens de sucesso, aviso ou erro.
        8. Retorna a camada pronta ou **None** caso haja erro ou cancelamento.

        Parâmetros
        file_path : str
            Caminho absoluto do arquivo DXF.
        layer_name : str
            Nome-base para a camada gerada.
        manter_original : bool, opcional
            Reservado para compatibilidade; não usado aqui.

        Retorno
        QgsVectorLayer | None
            A camada de pontos criada ou **None** se o processo for cancelado/
            houver falha.
        """
        # 1) Barra de preparação indeterminada
        preparacao_msg = self.iface.messageBar().createMessage(self.tr("Preparando processamento do DXF, aguarde…"))
        preparacao_bar = QProgressBar()
        preparacao_bar.setMinimum(0)
        preparacao_bar.setMaximum(0)
        preparacao_msg.layout().addWidget(preparacao_bar)
        widget_preparacao = self.iface.messageBar().pushWidget(preparacao_msg, Qgis.MessageLevel.Info)
        QCoreApplication.processEvents()

        # 2) Cria camada OGR **sem** disparar prompt automático
        opts = QgsVectorLayer.LayerOptions()
        opts.skipCrsValidation = True                 # <── AQUI
        ogr_layer = QgsVectorLayer(
            f"{file_path}|layername=entities|geometrytype=Point",
            f"{layer_name}_pt", "ogr", opts)

        if not ogr_layer.isValid():
            self.iface.messageBar().popWidget(widget_preparacao)
            self.mostrar_mensagem(self.tr("Falha ao carregar pontos do DXF."), "Erro")
            return None, None

        # 3) Se ainda não tem CRS, peça UMA vez ao usuário
        if not ogr_layer.crs().isValid():
            dlg = QgsProjectionSelectionDialog()
            if not dlg.exec():                       # utilizador cancelou
                self.iface.messageBar().popWidget(widget_preparacao)
                self.mostrar_mensagem(self.tr("Operação cancelada pelo usuário."), "Aviso")
                return None, None
            chosen = dlg.crs()
            if not chosen.isValid():
                self.iface.messageBar().popWidget(widget_preparacao)
                self.mostrar_mensagem(self.tr("Nenhum SRC selecionado – operação cancelada."), "Aviso")
                return None, None
            ogr_layer.setCrs(chosen)

        # 4) Agora que o CRS é válido, prossiga normalmente
        try:
            dxf_doc = ezdxf.readfile(file_path)
            msp = dxf_doc.modelspace()
        except Exception as e:
            self.iface.messageBar().popWidget(widget_preparacao)
            self.mostrar_mensagem(self.tr("Erro ao abrir o DXF: {error}").format(error=str(e)), "Erro")
            return None, None

        msp = dxf_doc.modelspace()
        coords_z = [(float(ent.dxf.location.x),
                     float(ent.dxf.location.y),
                     float(ent.dxf.location.z))
                    for ent in msp.query("POINT")]

        skip_fields = {"PaperSpace", "SubClasses", "Linetype", "EntityHandle", "Text"}
        campos_fixos = [
            QgsField("ID", QMetaType.Type.Int),
            QgsField("X", QMetaType.Type.Double),
            QgsField("Y", QMetaType.Type.Double),
            QgsField("Z", QMetaType.Type.Double)]
        campos_ogr = [f for f in ogr_layer.fields()
            if f.name() not in skip_fields and f.name() not in {c.name() for c in campos_fixos}]

        tem_z = any(abs(z) > 1e-9 for _, _, z in coords_z)
        geom_str = "PointZ" if tem_z else "Point"
        uri = f"{geom_str}?crs={ogr_layer.crs().authid()}"

        mem = QgsVectorLayer(uri, f"{layer_name}_pt", "memory")
        prov = mem.dataProvider()
        prov.addAttributes(campos_fixos + campos_ogr)
        mem.updateFields()

        feat_count = min(len(coords_z), ogr_layer.featureCount())

        # Remove barra de preparação ANTES de iniciar a barra real de progresso
        try:
            self.iface.messageBar().popWidget(widget_preparacao)
        except RuntimeError:
            pass  # nosec B110

        progressBar, progressMsgBar = self.iniciar_progress_bar(ogr_layer, message=self.tr('Carregando pontos de "{layer_name}", aguarde...').format(layer_name=layer_name))

        progressBar.setValue(0)
        progressBar.setMaximum(feat_count if feat_count > 0 else 1)
        processed = 0

        feats_out = []
        cancelado = False
        for idx, (ogr_feat, xyz) in enumerate(
            zip_longest(ogr_layer.getFeatures(), coords_z), start=1):
            if ogr_feat is None or xyz is None:
                continue
            x, y, z_val = xyz

            # Cria geometria 2D ou 3D conforme necessário
            if tem_z:
                geom = QgsGeometry.fromPoint(QgsPoint(x, y, z_val))
            else:
                geom = QgsGeometry.fromPointXY(QgsPointXY(x, y))

            new_feat = QgsFeature(mem.fields())
            new_feat.setGeometry(geom)

            attrs = [idx, x, y, z_val]
            attrs += [ogr_feat[field.name()] for field in campos_ogr]
            new_feat.setAttributes(attrs)

            feats_out.append(new_feat)

            processed += 10
            try:
                progressBar.setValue(processed)
            except RuntimeError:
                cancelado = True
                self.mostrar_mensagem(self.tr("Processo cancelado pelo usuário."), "Aviso")
                break
            QCoreApplication.processEvents()

        # Finaliza barra de progresso
        try:
            self.iface.messageBar().popWidget(progressMsgBar)
        except RuntimeError:
            pass  # nosec B110

        # Garante que a barra de preparação foi removida (caso algo pule etapas)
        try:
            self.iface.messageBar().popWidget(widget_preparacao)
        except RuntimeError:
            pass  # nosec B110

        if cancelado:
            # Não adiciona camada nem feições se foi cancelado
            return None, None

        if not feats_out:
            self.mostrar_mensagem(self.tr("Nenhuma feição de ponto encontrada."), "Aviso")
            return None, None

        # Só adiciona se não foi cancelado e há feições
        prov.addFeatures(feats_out)
        mem.updateExtents()

        # ➕  cria camada de texto (se houver)
        txt_layer = None
        try:
            txt_layer = self.carregar_texto_dxf(file_path, f"{layer_name}_txt", mem.crs().authid() )
        except Exception as exc:
            self.mostrar_mensagem(self.tr("Erro ao ler TEXTOS do DXF: {error}").format(error=str(exc)), "Erro")

        return mem, txt_layer

class CloneManagerPt:
    def __init__(self, ui_manager, layer_to_clone):
        """
        Inicializa o gerenciador de clonagem de camadas de pontos.

        Parâmetros:
        - ui_manager: Referência ao gerenciador da interface do usuário (geralmente responsável por mensagens, atualizações e utilidades da UI).
        - layer_to_clone: A camada de pontos (QgsVectorLayer) que será clonada.

        Detalhes:
        - Armazena as referências para permitir o acesso a métodos utilitários e manipulação da camada durante o processo de clonagem.
        """
        self.ui = ui_manager                   # Referência à interface de gerenciamento
        self.layer = layer_to_clone            # Camada de pontos a ser clonada (QgsVectorLayer)

    def tr(self, message):
        return QCoreApplication.translate("CloneManagerPt", message)

    def show_clone_options(self):
        """
        Exibe um diálogo para o usuário escolher o tipo de clonagem para a camada de pontos.

        Funcionalidades:
        - Cria um diálogo modal com quatro opções de clonagem, cada uma apresentada como botão de rádio estilizado.
        - Disponibiliza opções para: clonar só feições, copiar tabela de atributos, combinar tabela e tratar pontos, excluir tabela e tratar pontos.
        - Centraliza os botões de ação (OK/Cancelar) na janela.
        - Após a seleção e confirmação do usuário, chama o método de clonagem correspondente à opção escolhida.
        """

        # Cria o diálogo modal como filho do diálogo principal da interface
        dialog = QDialog(self.ui.dlg)
        dialog.setWindowTitle(self.tr("Clonar Camada de Pontos"))
        layout = QVBoxLayout(dialog)               # Layout vertical para os elementos do diálogo
        button_group = QButtonGroup(dialog)        # Grupo para garantir seleção única dos rádios

        # Define as opções de clonagem via QRadioButton
        self.radio_buttons = {
            1: QRadioButton(self.tr("Clonar Feição, sem Tabela")),
            2: QRadioButton(self.tr("Copiar Tabela de Atributos")),
            3: QRadioButton(self.tr("Combinar Tabela e Tratar Pontos")),
            4: QRadioButton(self.tr("Excluir Tabela e Tratar Pontos"))}

        # Adiciona cada botão de rádio dentro de um QFrame estilizado
        for id, radio in self.radio_buttons.items():
            frame = QFrame(dialog)
            frame_layout = QVBoxLayout(frame)
            frame.setFrameShape(QFrame.Shape.StyledPanel)
            frame.setFrameShadow(QFrame.Shadow.Raised)
            frame.setFixedSize(220, 30)                # Tamanho para melhor alinhamento visual
            frame_layout.addWidget(radio)
            layout.addWidget(frame)
            button_group.addButton(radio, id)          # Adiciona ao grupo para controle de seleção
            if id == 1:
                radio.setChecked(True)                 # Primeira opção selecionada por padrão

        # Adiciona caixa de botões "Ok" e "Cancelar" ao diálogo
        buttonBox = QDialogButtonBox(QDialogButtonBox.StandardButton.Ok | QDialogButtonBox.StandardButton.Cancel)
        buttonBox.accepted.connect(dialog.accept)      # OK fecha e aceita
        buttonBox.rejected.connect(dialog.reject)      # Cancelar fecha sem ação
        layout.addWidget(buttonBox)

        # Layout horizontal para centralizar os botões de ação
        hLayout = QHBoxLayout()
        hLayout.addStretch()
        hLayout.addWidget(buttonBox)
        hLayout.addStretch()
        layout.addLayout(hLayout)

        # Executa o diálogo e verifica a ação do usuário
        result = dialog.exec()
        if result == QDialog.DialogCode.Accepted:
            # Percorre os botões para encontrar o selecionado
            for id, radio in self.radio_buttons.items():
                if radio.isChecked():
                    self.realizar_clonagem(id)         # Executa a clonagem conforme a escolha
                    break

    def _obter_grupo_camadas_clonadas(self):
        """
        Retorna sempre o mesmo grupo de camadas clonadas.

        Usa uma propriedade interna estável para evitar grupos duplicados,
        mesmo quando o idioma do plugin for alterado.
        """
        root = QgsProject.instance().layerTreeRoot()

        nome_grupo = self.tr("Camadas Clonadas")
        chave_grupo = "tempo_salvo_tools/grupo_camadas_clonadas"

        try:
            grupos = root.findGroups()
        except Exception:
            grupos = []

        # Primeiro procura pela propriedade interna estável
        for grupo in grupos:
            try:
                if grupo.customProperty(chave_grupo, False):
                    return grupo
            except Exception:
                pass  # nosec B110

        # Compatibilidade com grupos já existentes antes deste ajuste
        nomes_aceitos = {
            nome_grupo.strip().casefold(),
            "Camadas Clonadas".casefold(),
            "Cloned Layers".casefold()}

        for grupo in grupos:
            try:
                if grupo.name().strip().casefold() in nomes_aceitos:
                    grupo.setCustomProperty(chave_grupo, True)
                    return grupo
            except Exception:
                pass  # nosec B110

        # Só cria se realmente não existir
        grupo = root.addGroup(nome_grupo)
        grupo.setCustomProperty(chave_grupo, True)

        return grupo

    def criar_camada_clonada(self, suf, fields=None, feats=None, copy_renderer=True):
        """
        Cria uma nova camada de pontos clonada em memória, baseada em uma camada de referência.

        Funcionalidades:
        - Define o nome da nova camada com um sufixo e o nome original.
        - Mantém o mesmo SRC/CRS (sistema de referência de coordenadas) da camada original.
        - Permite especificar campos (QgsFields) e feições (lista de QgsFeature), ou copiar todos da camada original.
        - Copia a simbologia/renderizador da camada original, se solicitado.
        - Adiciona a camada ao grupo "Camadas Clonadas" no projeto QGIS.
        - Retorna a camada criada para possíveis manipulações posteriores.

        Parâmetros:
        - suf: Sufixo a ser adicionado ao nome da nova camada.
        - fields: (Opcional) Estrutura de campos (QgsFields) da camada.
        - feats: (Opcional) Lista de feições (QgsFeature) a serem adicionadas à nova camada.
        - copy_renderer: (bool) Se True, copia a simbologia/renderizador da camada original.

        Retorna:
        - clone: A camada de pontos criada (QgsVectorLayer), ou None se houver erro.
        """
        # Define o nome da nova camada com o sufixo e o nome original
        name = f"{suf}_{self.layer.name()}"
        # Recupera o CRS da camada original
        crs = self.layer.crs().authid()
        # Cria a camada em memória com tipo Point e mesmo CRS
        clone = QgsVectorLayer(f"Point?crs={crs}", name, "memory")

        # Verifica se a camada foi criada corretamente
        if not clone.isValid():
            QMessageBox.critical(None, self.tr("Erro"), self.tr("Não foi possível criar a camada clonada."))
            return None

        # Adiciona os campos (estrutura de atributos) à nova camada
        prov = clone.dataProvider()
        prov.addAttributes((fields or self.layer.fields()).toList())
        clone.updateFields()

        # Adiciona as feições (geometrias e atributos) à nova camada
        prov.addFeatures(feats or list(self.layer.getFeatures()))

        # Copia simbologia/renderizador da camada original, se solicitado
        if copy_renderer:
            clone.setRenderer(self.layer.renderer().clone())

        # Obtém o grupo existente ou cria apenas uma vez
        grp = self._obter_grupo_camadas_clonadas()

        # Adiciona a nova camada ao projeto e ao grupo existente
        QgsProject.instance().addMapLayer(clone, False)
        grp.addLayer(clone)

        return clone  # Retorna a camada criada para manipulação posterior

    def realizar_clonagem(self, tipo):
        """
        Executa a clonagem da camada de pontos conforme o tipo selecionado pelo usuário.

        Parâmetros:
        - tipo: (int) Número correspondente à opção de clonagem escolhida:
            1 - Clonar apenas as feições (somente geometria, sem atributos)
            2 - Clonar todos os atributos e geometrias (cópia completa)
            3 - Combinar tabela e tratar campos específicos (adiciona/calcula campos especiais)
            4 - Excluir tabela e tratar apenas campos essenciais (campos mínimos)

        Funcionamento:
        - Usa um dicionário para mapear o tipo à função correspondente.
        - Executa diretamente a função mapeada conforme o tipo selecionado.
        """
        # Seleciona e executa a função correspondente ao tipo de clonagem escolhido
        {1: self.clone_feicao,
         2: self.clone_atributos,
         3: self.clone_combinar,
         4: self.clone_excluir}[tipo]()

    def clone_feicao(self):
        """
        Clona somente as geometrias (feições) da camada de pontos original,
        sem copiar nenhum atributo (tabela vazia).

        Funcionalidades:
        - Cria novas feições mantendo apenas a geometria de cada ponto.
        - Não inclui atributos além dos padrões mínimos obrigatórios (estrutura vazia).
        - Cria uma nova camada em memória com essas feições clonadas.
        - Não copia a tabela de atributos da camada original.

        Fluxo:
        1. Percorre todas as feições da camada original, copiando apenas as geometrias.
        2. Cria uma camada clonada sem campos (tabela de atributos vazia).
        3. Adiciona todas as novas feições (com geometria apenas) à nova camada.
        """
        feats = []
        # Percorre todas as feições da camada original
        for f in self.layer.getFeatures():
            nf = QgsFeature()              # Cria uma nova feição vazia
            nf.setGeometry(f.geometry())   # Copia apenas a geometria
            feats.append(nf)               # Adiciona à lista de feições clonadas

        # Cria camada clonada sem tabela de atributos, apenas geometrias
        self.criar_camada_clonada(self.tr("Clone_SemTabela"), fields=QgsFields(), feats=feats)

    def clone_atributos(self):
        """
        Clona a camada de pontos mantendo todas as geometrias e atributos originais.

        Funcionalidades:
        - Copia todos os campos (estrutura da tabela de atributos) da camada original.
        - Para cada feição, clona tanto a geometria quanto todos os atributos.
        - Cria uma nova camada em memória idêntica à original.
        - Exibe mensagem de sucesso ao usuário ao finalizar.

        Processo:
        1. Percorre todas as feições da camada de pontos original.
        2. Cria novas feições com os mesmos campos e atributos, copiando também a geometria.
        3. Cria uma nova camada clonada com esses campos e feições.
        4. Informa o usuário que a clonagem foi concluída.
        """
        feats = []
        # Percorre todas as feições da camada original
        for f in self.layer.getFeatures():
            nf = QgsFeature(self.layer.fields())   # Cria nova feição com mesma estrutura de campos
            nf.setGeometry(f.geometry())           # Copia a geometria
            nf.setAttributes(f.attributes())       # Copia todos os atributos
            feats.append(nf)                       # Adiciona à lista de feições clonadas

        # Cria a nova camada clonada com campos e feições completos
        self.criar_camada_clonada(self.tr("Clone_Tabela"), fields=self.layer.fields(), feats=feats)

        # Exibe mensagem de sucesso ao usuário
        self.ui.mostrar_mensagem(self.tr("Clonagem completa concluída."), "Sucesso")

    def clone_combinar(self):
        """
        Clona a camada de pontos combinando campos essenciais ("ID", "X", "Y", "X_GMS", "Y_GMS") 
        e todos os outros campos originais (sem duplicidade), já preenchendo os valores calculados 
        para cada ponto.

        Funcionalidades:
        - Garante que os campos essenciais existam na camada clonada, criando-os se necessário.
        - Copia todos os demais campos da camada original, exceto os essenciais para evitar duplicidade.
        - Calcula e atribui valores para ID sequencial, coordenadas X e Y, e suas versões DMS.
        - Copia os demais atributos conforme presentes na camada original.
        - Chama tratamento adicional para pontos (sinais para atualização dinâmica de X, Y, DMS).
        - Exibe mensagem de sucesso ao usuário.

        Processo:
        1. Define a estrutura de campos da nova camada, priorizando os essenciais.
        2. Percorre todas as feições, calcula valores necessários e copia demais atributos.
        3. Cria a nova camada clonada e ativa o tratamento dinâmico para atualização dos campos especiais.
        4. Notifica o usuário do sucesso.
        """
        base = self.layer.fields()
        keep = {"ID", "X", "Y", "X_GMS", "Y_GMS"}
        fields = QgsFields()
        # Garante que os campos essenciais estejam presentes na camada
        for fld in ["ID", "X", "Y", "X_GMS", "Y_GMS"]:
            if base.indexOf(fld) == -1:
                # Cria campo se não existir
                if fld == "ID":
                    fields.append(QgsField("ID", QMetaType.Type.Int))
                else:
                    fields.append(QgsField(fld, QMetaType.Type.Double if fld in {"X", "Y"} else QMetaType.Type.QString))
            else:
                # Usa campo original se já existir
                fields.append(base.field(fld))
        # Adiciona todos os outros campos originais que não sejam essenciais
        for f in base:
            if f.name() not in keep:
                fields.append(f)

        feats = []
        # Para cada feição, calcula e preenche os valores dos campos essenciais e copia demais atributos
        for idx, f in enumerate(self.layer.getFeatures(), start=1):
            nf = QgsFeature(fields)
            nf.setGeometry(f.geometry())
            atr = [None] * len(fields)
            pt = f.geometry().asPoint()
            X = round(pt.x(), 6 if self.layer.crs().isGeographic() else 3)
            Y = round(pt.y(), 6 if self.layer.crs().isGeographic() else 3)
            atr[fields.indexOf("ID")] = idx          # ID sequencial
            atr[fields.indexOf("X")] = X             # Coordenada X
            atr[fields.indexOf("Y")] = Y             # Coordenada Y

            # Preenche os campos DMS se existirem na estrutura
            x_dms, y_dms = self.ui.calcular_dms_do_ponto(self.layer, pt)

            if fields.indexOf("X_GMS") != -1:
                atr[fields.indexOf("X_GMS")] = x_dms

            if fields.indexOf("Y_GMS") != -1:
                atr[fields.indexOf("Y_GMS")] = y_dms

            # Copia demais atributos
            for i, fld in enumerate(base):
                if fld.name() not in keep:
                    atr[fields.indexOf(fld.name())] = f[i]
            nf.setAttributes(atr)
            feats.append(nf)

        # Cria a camada clonada com os campos e feições preparados
        clone = self.criar_camada_clonada(self.tr("Clone_Combinado"), fields=fields, feats=feats)

        if clone is None or not clone.isValid():
            self.ui.mostrar_mensagem(self.tr("Falha ao criar a camada clonada."), "Erro")
            return

        # Ativa o tratamento automático da nova camada
        self.ui.tratar_pontos(clone)

        self.ui.mostrar_mensagem(self.tr("Combinação de tabela + tratamento concluída."), "Sucesso")

    def clone_excluir(self):
        """
        Cria uma camada clonada de pontos contendo apenas os campos essenciais:
        "ID", "X", "Y", "X_GMS", "Y_GMS" – todos os demais atributos são descartados.

        Funcionalidades:
        - Cria uma nova camada de pontos apenas com campos mínimos e valores calculados.
        - Para cada ponto, calcula as coordenadas X e Y (em decimal) e em DMS.
        - Define um ID sequencial para cada ponto.
        - Não copia a simbologia/renderizador da camada original.
        - Ativa o tratamento de atualização dinâmica dos campos calculados.
        - Exibe mensagem de sucesso ao usuário ao finalizar.

        Processo:
        1. Define os campos essenciais na nova camada.
        2. Percorre todas as feições da camada original, calculando valores para os campos essenciais.
        3. Cria uma nova camada em memória com esses campos e feições.
        4. Ativa sinais dinâmicos para atualizar os campos em futuras edições.
        5. Notifica o usuário do sucesso.
        """
        fields = QgsFields()
        fields.append(QgsField("ID", QMetaType.Type.Int))             # Campo ID sequencial
        fields.append(QgsField("X", QMetaType.Type.Double))           # Coordenada X (decimal)
        fields.append(QgsField("Y", QMetaType.Type.Double))           # Coordenada Y (decimal)
        fields.append(QgsField("X_GMS", QMetaType.Type.QString))       # Coordenada X em DMS
        fields.append(QgsField("Y_GMS", QMetaType.Type.QString))       # Coordenada Y em DMS

        feats = []
        # Para cada ponto, calcula valores essenciais e cria nova feição
        for idx, f in enumerate(self.layer.getFeatures(), start=1):
            nf = QgsFeature(fields)
            nf.setGeometry(f.geometry())
            pt = f.geometry().asPoint()
            X = round(pt.x(), 6 if self.layer.crs().isGeographic() else 3)
            Y = round(pt.y(), 6 if self.layer.crs().isGeographic() else 3)
            nf.setAttribute("ID", idx)                                  # ID sequencial
            nf.setAttribute("X", X)                                     # Coordenada X decimal
            nf.setAttribute("Y", Y)                                     # Coordenada Y decimal
            x_dms, y_dms = self.ui.calcular_dms_do_ponto(self.layer, pt)

            nf.setAttribute("X_GMS", x_dms)
            nf.setAttribute("Y_GMS", y_dms)
            feats.append(nf)

        # Cria camada clonada apenas com os campos essenciais e feições calculadas
        clone = self.criar_camada_clonada(self.tr("Clone_Excluir"), fields=fields, feats=feats, copy_renderer=False)

        if clone is None or not clone.isValid():
            self.ui.mostrar_mensagem(self.tr("Falha ao criar a camada clonada."), "Erro")
            return

        # Ativa o tratamento automático da nova camada
        self.ui.tratar_pontos(clone)

        self.ui.mostrar_mensagem(self.tr("Exclusão de atributos + tratamento concluída."),
            "Sucesso")

class TreeViewEventFilter(QObject):
    """
    Filtro de eventos do `treeViewListaPonto` para melhorar a interação do usuário.

    Responsabilidades:
    - Exibir tooltip ao mover o mouse sobre itens do treeView (reaproveita `UiManager.configurar_tooltip`).
    - Permitir adicionar arquivos por arrastar e soltar (drag & drop) sobre o treeView,
      chamando o fluxo de importação do UiManager (ex.: `_adicionar_arquivo_por_caminho`).

    Observação:
    - Este filtro é instalado no `viewport()` do QTreeView, pois é onde os eventos de mouse e drop
      realmente ocorrem para os itens exibidos.

    Parâmetros:
    - ui_manager: Referência à instância do `UiManagerP` que contém o diálogo (`dlg`) e as rotinas
      de importação/feedback (mostrar mensagens, adicionar camadas etc.).
    """
    def __init__(self, ui_manager):
        """
        Inicializa o filtro de eventos com uma referência ao UiManager.

        Parâmetros:
        - self: Referência à instância atual do objeto (TreeViewEventFilter).
        - ui_manager: Instância do UiManagerP que será usada para acessar e manipular a interface do usuário.
        """
        super().__init__()  # Inicializa a classe base QObject
        self.ui_manager = ui_manager  # Armazena a referência ao UiManager para uso posterior

    def tr(self, message):
        return QCoreApplication.translate("TreeViewEventFilter", message)

    def _is_ext_suportada(self, path: str) -> bool:
        """Retorna True se a extensão do arquivo é suportada pelo fluxo de adicionar."""
        ext = os.path.splitext(path)[1].lower()
        return ext in (".dxf", ".kml", ".kmz", ".shp", ".geojson", ".gpkg")

    def _coletar_paths_drop(self, paths: list[str]) -> list[str]:
        """
        Recebe uma lista de caminhos (arquivos e/ou pastas) e devolve uma lista
        de arquivos suportados.

        - Se for pasta, varre recursivo.
        - Remove duplicados.
        """
        out = []
        seen = set()

        for p in paths:
            if not p:
                continue

            if os.path.isdir(p):
                for root, _, files in os.walk(p):
                    for fn in files:
                        fp = os.path.join(root, fn)
                        if self._is_ext_suportada(fp) and fp not in seen:
                            seen.add(fp)
                            out.append(fp)
            else:
                if self._is_ext_suportada(p) and p not in seen:
                    seen.add(p)
                    out.append(p)

        return out

    def eventFilter(self, obj, event):
        """
        Intercepta eventos do `viewport()` do treeView para:
        - aceitar drag & drop de arquivos/pastas (adicionando camadas ao QGIS),
        - atualizar tooltip quando o mouse passa sobre um item,
        mantendo o comportamento padrão do QTreeView quando não for um evento tratado.
        """
        tv = self.ui_manager.dlg.treeViewListaPonto

        # Só intercepta eventos do viewport do treeView
        if obj != tv.viewport():
            return super().eventFilter(obj, event)

        event_type = event.type()

        # Drag & Drop (Adicionar)
        if event_type in (QEvent.Type.DragEnter, QEvent.Type.DragMove):
            md = event.mimeData()
            if md and md.hasUrls():
                paths = [u.toLocalFile() for u in md.urls() if u.isLocalFile()]
                if self._coletar_paths_drop(paths):
                    event.setDropAction(Qt.DropAction.CopyAction)
                    event.accept()
                    return True
            event.ignore()
            return True

        if event_type == QEvent.Type.Drop:
            md = event.mimeData()
            if md and md.hasUrls():
                raw_paths = [u.toLocalFile() for u in md.urls() if u.isLocalFile()]
                files = self._coletar_paths_drop(raw_paths)

                ok = 0
                for fp in files:
                    try:
                        if self.ui_manager._adicionar_arquivo_por_caminho(fp):
                            ok += 1

                    except Exception as e:
                        self.ui_manager.mostrar_mensagem(self.tr("Falha ao adicionar '{file_name}': {error}").format(file_name=os.path.basename(fp), error=e), "Erro")

                if ok == 0 and files:
                    self.ui_manager.mostrar_mensagem(self.tr("Nenhum arquivo foi adicionado (todos falharam)."), "Aviso")

                elif ok > 0 and len(files) > 1:
                    self.ui_manager.mostrar_mensagem(self.tr("{ok}/{total} arquivos adicionados via arrastar e soltar.").format(ok=ok, total=len(files)), "Sucesso")

                event.setDropAction(Qt.DropAction.CopyAction)
                event.accept()
                return True

            event.ignore()
            return True

        # Tooltip / Hover
        if event_type == QEvent.Type.MouseMove:
            index = tv.indexAt(event.pos())
            if index.isValid():
                self.ui_manager.configurar_tooltip(index)
            # não “consome” o mouse move, deixa o treeView continuar normal
            return False

        return super().eventFilter(obj, event)

class BlocoEscolhaDialogo(QDialog):
    """
    Diálogo para escolher campos e valores para exportação de pontos. Este diálogo permite ao usuário selecionar campos,
    definir cores, e escolher blocos para exportação em um formato específico.

    Parâmetros:
    - campos (list): Lista de nomes de campos disponíveis na camada.
    - layer (QgsVectorLayer): A camada de origem.
    - nomes_blocos (list): Lista de nomes de blocos disponíveis.
    - parent (QWidget): Widget pai do diálogo (opcional).

    Funcionalidades:
    - Seleção de campos de texto para exportação.
    - Definição de cores aleatórias para os valores selecionados.
    - Seleção de blocos específicos para cada valor.
    - Verificação de condições para habilitar/desabilitar o botão de exportação.
    """
    def __init__(self, campos, layer, parent=None):
        """
        Inicializa uma instância do diálogo BlocoEscolhaDialogo.
        
        Funções principais:
        - Configura a interface do usuário do diálogo.
        - Inicializa variáveis e estruturas de dados para armazenar informações sobre os campos e cores selecionados.
        - Configura e organiza os layouts e widgets do diálogo.

        Etapas detalhadas:
        1. Inicializa a superclasse QDialog.
        2. Armazena os parâmetros `campos` e `layer`.
        3. Cria um dicionário para armazenar as cores selecionadas.
        4. Inicializa um dicionário para armazenar checkboxes dos campos.
        5. Chama o método `criar_blocos` para inicializar os blocos.
        6. Inicializa um dicionário para armazenar o estado dos campos, todos desmarcados.
        7. Inicializa o QButtonGroup para botões de rádio.
        8. Configura o título, tamanho mínimo e máximo do diálogo.
        9. Configura o layout principal do diálogo.
        10. Configura e organiza widgets e layouts adicionais dentro do diálogo.
        11. Configura a lista de widgets para exibir valores de campos.
        12. Adiciona botões de controle (OK e Cancelar) ao diálogo.
        13. Inicializa o QListWidget com os valores do campo string.
        14. Embaralha uma lista de cores vibrantes.
        15. Verifica as condições para habilitar/desabilitar o botão Executar.
        16. Conecta sinais de checkboxes às funções de atualização de estado.

        Parâmetros:
        - campos (list): Lista de nomes dos campos.
        - layer (QgsVectorLayer): Camada de vetor do QGIS.
        - parent (QWidget): Widget pai opcional.
        """
        super().__init__(parent)
        self.campos = campos # Armazena os campo
        self.layer = layer # Armazena a camada
        self.cores = {}  # Dicionário para armazenar as cores selecionadas
        self.camposCheckBoxes = {} # Dicionário para armazenar checkboxes dos campos
        # Inicialização dos blocos
        self.nomes_blocos = self.criar_blocos(ezdxf.new(dxfversion='R2013'), {})
        self.estadoCampos = {campo: False for campo in campos}  # Inicializa todos os campos como desmarcados
        
        # Inicialize radioGroup no construtor
        self.radioGroup = QButtonGroup(self)        

        self.setWindowTitle(self.tr("Escolha o Campo e o Valor para os Pontos")) # Define o título da janela
        self.setMinimumSize(325, 400)  # Define o tamanho mínimo do diálogo
        self.setMaximumSize(370, 600)  # Define o tamanho máximo do diálogo

        layout = QVBoxLayout(self) # Layout principal vertical

        self.frame = QFrame(self) # Cria um frame
        self.frame.setFrameShape(QFrame.Shape.StyledPanel) # Define o formato do frame
        self.frame.setLineWidth(int(0.6)) # Define a largura da linha do frame
        frameLayout = QVBoxLayout(self.frame) # Layout vertical para o frame

        self.comboBoxLayout = QHBoxLayout() # Layout horizontal para o comboBox
        self.label = QLabel(self.tr('Selecione o campo:')) # Label para o comboBox
        self.comboBoxLayout.addWidget(self.label) # Adiciona o label ao layout

        self.comboBox = QComboBox(self.frame) # Cria o comboBox

        # Adicionar apenas campos do tipo string ao comboBox
        added = 0
        for campo in self.campos:
            field = self.layer.fields().field(campo)
            if field and field.type() in (QMetaType.Type.QString, QVariant.StringList):
                self.comboBox.addItem(campo)
                added += 1

        # Se não houver nenhum campo string, adiciona o fallback 'Camada_0'
        if added == 0:
            self.comboBox.addItem("Camada_0")

        self.comboBox.setStyleSheet("""
        QComboBox { combobox-popup: 0; }
        QComboBox QAbstractItemView {
            min-height: 80px;
            max-height: 80px;
            min-width: 100px;}""")

        self.comboBox.currentIndexChanged.connect(self.atualizarListWidget)

        self.comboBoxLayout.addWidget(self.comboBox) # Adiciona o comboBox ao layout
        frameLayout.addLayout(self.comboBoxLayout) # Adiciona o layout do comboBox ao layout do frame

        # Layout horizontal para o checkbox e o botão de cores aleatórias
        topLayout = QHBoxLayout() # Layout horizontal para o topo
        frameLayout.addLayout(topLayout) # Adiciona o layout ao frame

        # Adiciona QCheckBox para selecionar todos
        self.selectAllCheckBox = QCheckBox(self.tr("Selecionar Camadas")) # Cria o checkbox para selecionar todos
        self.selectAllCheckBox.setChecked(False) # Define o estado inicial como desmarcado
        # Conecta o sinal de mudança de estado à função selecionarTodos
        self.selectAllCheckBox.stateChanged.connect(self.selecionarTodos)
        topLayout.addWidget(self.selectAllCheckBox) # Adiciona o checkbox ao layout

        # Layout horizontal para os botões "Rótulos" e "3D"
        buttonsLayout = QHBoxLayout() # Layout horizontal para os botões
        frameLayout.addLayout(buttonsLayout) # Adiciona o layout ao frame

        # Adiciona botão para abrir a lista de campos numéricos para 3D
        self.btn3D = QPushButton(self.tr("Altimetria")) # Cria o botão "Altimetria"
        # Conecta o sinal de clique à função mostrarCamposNumericos
        self.btn3D.clicked.connect(self.mostrarCamposNumericos)
        buttonsLayout.addWidget(self.btn3D) # Adiciona o botão ao layout

        # Botão "Rótulos"
        self.camposButton = QPushButton(self.tr("Rótulos"))
        # Conecta o sinal de clique à função mostrarCampos
        self.camposButton.clicked.connect(self.mostrarCampos) 
        buttonsLayout.addWidget(self.camposButton) # Adiciona o botão ao layout

        # Adiciona botão para definir cores aleatórias
        self.randomColorButton = QPushButton(self.tr("Cores Aleatórias"))
        # Conecta o sinal de clique à função definirCoresAleatorias
        self.randomColorButton.clicked.connect(self.definirCoresAleatorias)
        topLayout.addWidget(self.randomColorButton) # Adiciona o botão ao layout

        # Layout para o QLineEdit e o novo botão
        lineEditLayout = QHBoxLayout() # Layout horizontal para o QLineEdit
        self.lineEdit = QLineEdit(self.frame) # Cria o QLineEdit
        self.lineEdit.setReadOnly(True)  # Torna o QLineEdit somente leitura
        self.lineEdit.setPlaceholderText(self.tr("Feições: Selecione!")) # Define o texto de espaço reservado
        self.lineEdit.setSizePolicy(QSizePolicy.Policy.Preferred, QSizePolicy.Policy.Fixed) # Define a política de tamanho
        lineEditLayout.addWidget(self.lineEdit) # Adiciona o QLineEdit ao layout

        # Criação do botão "Bloco Aleatório"
        self.blocoAleatorioButton = QPushButton(self.tr("Bloco Aleatório"))
        # Conecta o sinal de clique à função definirBlocoAleatorio
        self.blocoAleatorioButton.clicked.connect(self.definirBlocoAleatorio)
        lineEditLayout.addWidget(self.blocoAleatorioButton) # Adiciona o botão ao layout

        # Adicionando o layout do QLineEdit e botão ao layout principal
        frameLayout.addLayout(lineEditLayout)

        self.listWidget = QListWidget(self.frame) # Cria o QListWidget
        self.listWidget.setMinimumSize(200, 220) # Define o tamanho mínimo do QListWidget
        # Conecta o sinal de mudança de seleção à função atualizarLineEdit
        self.listWidget.itemSelectionChanged.connect(self.atualizarLineEdit)
        frameLayout.addWidget(self.listWidget)  # Adiciona o QListWidget ao frame

        # Adiciona os botões OK e Cancelar
        self.buttonBox = QDialogButtonBox(QDialogButtonBox.StandardButton.Ok | QDialogButtonBox.StandardButton.Cancel, self)
        self.buttonBox.button(QDialogButtonBox.StandardButton.Ok).setText(self.tr("Exportar"))  # Altera o texto do botão OK para Exportar
        self.buttonBox.accepted.connect(self.accept)  # Se Exportar for clicado, aceita o diálogo
        self.buttonBox.rejected.connect(self.reject)  # Se Cancelar for clicado, rejeita o diálogo

        # Centraliza o buttonBox no layout
        frameLayout.addWidget(self.buttonBox, 0, Qt.AlignmentFlag.AlignCenter)  # Adiciona o buttonBox ao layout com alinhamento centralizado

        layout.addWidget(self.frame) # Adiciona o frame ao layout principal

        # Isto carregará os valores do campo string no QListWidget
        self.atualizarListWidget(0)

        # Embaralha uma lista de cores vibrantes
        self.cores_vibrantes_embaralhadas = self.embaralhar_cores_vibrantes()

        self.verificarCondicoesParaExecutar()  # Chama a função verificarCondicoesParaExecutar

        # Conecta o sinal de mudança de estado à função atualizarEstadoBotaoExportar
        self.selectAllCheckBox.stateChanged.connect(self.atualizarEstadoBotaoExportar)
        # Conecta o sinal de mudança de estado à função verificarCondicoesParaExecutar
        self.selectAllCheckBox.stateChanged.connect(self.verificarCondicoesParaExecutar)

    def definirBlocoAleatorio(self):
        """
        Define um bloco aleatório para cada item no QListWidget. A função realiza as seguintes etapas:

        1. Cria uma cópia da lista de blocos disponíveis.
        2. Inicializa uma lista para armazenar os blocos já utilizados.
        3. Percorre cada item do QListWidget:
           - Obtém o texto do QLabel e o QComboBox associados ao item.
           - Verifica se o texto do label corresponde a algum nome de bloco.
           - Se houver correspondência, seleciona o bloco correspondente e o remove da lista de blocos disponíveis.
           - Se não houver correspondência, escolhe um bloco aleatório dos disponíveis.
           - Atualiza as listas de controle de blocos disponíveis e utilizados.

        Funcionalidades:
        - Seleção automática de blocos para itens em uma lista.
        - Evita a repetição de blocos até que todos tenham sido utilizados.
        """
        blocos_disponiveis = self.nomes_blocos.copy()  # Cria uma cópia da lista de blocos disponíveis
        blocos_utilizados = []  # Lista para armazenar os blocos já utilizados

        # Percorre cada item do QListWidget
        for i in range(self.listWidget.count()):
            item = self.listWidget.item(i)
            widget = self.listWidget.itemWidget(item)
            label = widget.findChild(QLabel).text()  # Obtém o texto do QLabel
            combo = widget.findChild(QComboBox)
            
            # Verifica se o nome no label corresponde a algum nome de bloco
            bloco_correspondente = next((bloco for bloco in self.nomes_blocos if bloco.lower() == label.lower()), None)

            if bloco_correspondente:
                # Se houver correspondência, seleciona o bloco correspondente
                indice_bloco = combo.findData(bloco_correspondente, Qt.ItemDataRole.UserRole)
                if indice_bloco >= 0:
                    combo.setCurrentIndex(indice_bloco)

                # Remove o bloco correspondente da lista de disponíveis, se necessário
                if bloco_correspondente in blocos_disponiveis:
                    blocos_disponiveis.remove(bloco_correspondente)
                    blocos_utilizados.append(bloco_correspondente)
            else:
                # Se não houver blocos disponíveis, reinicia a lista
                if not blocos_disponiveis:
                    blocos_disponiveis = blocos_utilizados.copy()
                    blocos_utilizados.clear()

                # Escolha usada somente para distribuir visualmente os blocos.
                bloco_aleatorio = random.choice(blocos_disponiveis)  # nosec B311
                indice_bloco = combo.findData(bloco_aleatorio, Qt.ItemDataRole.UserRole)

                if indice_bloco >= 0:
                    combo.setCurrentIndex(indice_bloco)

                # Atualiza as listas de controle
                blocos_disponiveis.remove(bloco_aleatorio)
                blocos_utilizados.append(bloco_aleatorio)

    def tr(self, message):
        return QCoreApplication.translate("BlocoEscolhaDialogo", message)

    def _nome_bloco_exibicao(self, nome_tecnico):
        """
        Retorna o nome traduzido para exibição, mantendo o nome
        técnico original do bloco para desenho e exportação DXF.
        """
        nomes_traduzidos = {
            "CirculoX": self.tr("CírculoX"),
            "CirculoCruz": self.tr("CírculoCruz"),
            "CirculoTraço": self.tr("CírculoTraço"),
            "CirculoPonto": self.tr("CírculoPonto"),
            "Árvore": self.tr("Árvore"),
            "Poste": self.tr("Poste"),
            "Bandeira": self.tr("Bandeira"),
            "Bandeira 2": self.tr("Bandeira 2"),
            "Cerca": self.tr("Cerca"),
            "Rocha": self.tr("Rocha"),
            "Bueiro": self.tr("Bueiro"),
            "QuadradoX": self.tr("QuadradoX"),
            "QuadradoCruz": self.tr("QuadradoCruz"),
            "QuadradoTraço": self.tr("QuadradoTraço"),
            "QuadradoPonto": self.tr("QuadradoPonto"),
            "TrianguloX": self.tr("TriânguloX"),
            "TrianguloCruz": self.tr("TriânguloCruz"),
            "TrianguloPonto": self.tr("TriânguloPonto"),
            "TrianguloTraço": self.tr("TriânguloTraço"),
            "Casa": self.tr("Casa"),
            "Topografia GPS": self.tr("Topografia GPS")}

        return nomes_traduzidos.get(nome_tecnico, nome_tecnico)

    def atualizarEstadoBotaoExportar(self):
        """
        Atualiza o estado do botão Exportar com base no estado do checkbox Selecionar Camadas.
        A função realiza as seguintes etapas:

        1. Verifica o estado do checkbox Selecionar Camadas.
        2. Habilita ou desabilita o botão Exportar de acordo com o estado do checkbox.

        Funcionalidades:
        - Habilitação e desabilitação dinâmica do botão Exportar.
        """
        # Atualiza o estado do botão Exportar com base no checkbox Selecionar Camadas
        self.buttonBox.button(QDialogButtonBox.StandardButton.Ok).setEnabled(self.selectAllCheckBox.isChecked())

    def verificarCondicoesParaExecutar(self):
        """
        Verifica se todas as condições necessárias para habilitar o botão Executar são satisfeitas.
        A função realiza as seguintes etapas:

        1. Verifica se a camada possui feições.
        2. Verifica se a camada possui campos.
        3. Verifica se o checkbox "Selecionar Camadas" está marcado.
        4. Habilita o botão Executar somente se todas as condições forem verdadeiras.

        Funcionalidades:
        - Verificação da presença de feições na camada.
        - Verificação da presença de campos na camada.
        - Verificação do estado do checkbox "Selecionar Camadas".
        - Habilitação do botão Executar apenas quando todas as condições são atendidas.
        """
        # Verifica se a camada possui feições
        tem_feicoes = self.layer.featureCount() > 0

        # Verifica se a camada possui campos
        tem_campos = len(self.campos) > 0

        # Verifica se o checkBox "Selecionar Camadas" está marcado
        selecao_ativa = self.selectAllCheckBox.isChecked()

        # Habilita o botão Executar somente se todas as condições forem verdadeiras
        self.buttonBox.button(QDialogButtonBox.StandardButton.Ok).setEnabled(tem_feicoes and tem_campos and selecao_ativa)

    def mostrarCamposNumericos(self):
        """
        Diálogo de seleção de Z:
          - Checkbox "Altimetria da Camada" (usa Z da geometria).
          - Radios com campos numéricos (Z por atributo).
          - Regras:
            * Se a camada não tiver Z → checkbox desativado.
            * Ao marcar o checkbox → limpa e desativa os radios.
            * Ao desmarcar → reativa os radios (se existirem).
            * Se não houver radios e a camada não tiver Z → "Sem Dados para Z".
        """
        # Diálogo
        self.campos3DDialog = QDialog(self)
        self.campos3DDialog.setWindowTitle(self.tr("Campos para Altimetria"))
        self.campos3DDialog.resize(200, 220)

        dialogLayout = QVBoxLayout(self.campos3DDialog)

        # Checkbox "Altimetria da Camada"
        self.cbAltimetriaCamada = QCheckBox(self.tr("Altimetria da Camada"), self.campos3DDialog)

        # Detecta Z pela assinatura WKB e, se necessário, por uma feição exemplo
        has_z = QgsWkbTypes.hasZ(self.layer.wkbType())
        if not has_z:
            f = next(self.layer.getFeatures(), None)
            if f:
                g = f.geometry()
                if g and not g.isEmpty():
                    # Prefira geometry.is3D(), senão cheque o WKB da geometria
                    has_z = g.is3D() if hasattr(g, "is3D") else QgsWkbTypes.hasZ(g.wkbType())

        if not has_z:
            self.cbAltimetriaCamada.setChecked(False)
            self.cbAltimetriaCamada.setEnabled(False)
            self.cbAltimetriaCamada.setToolTip(self.tr("Camada sem coordenada Z na geometria."))

        dialogLayout.addWidget(self.cbAltimetriaCamada)

        # Lista de radios (campos numéricos)
        campos3DWidget = QWidget(self.campos3DDialog)
        campos3DLayout = QVBoxLayout(campos3DWidget)

        self._radios3d = []
        for campo in self.campos:
            fld = self.layer.fields().field(campo)
            if fld and fld.isNumeric():
                rb = QRadioButton(campo, campos3DWidget)
                self.radioGroup.addButton(rb)
                rb.toggled.connect(self.atualizarTextoBotao3D)
                campos3DLayout.addWidget(rb)
                self._radios3d.append(rb)

        scrollArea = QScrollArea(self.campos3DDialog)
        scrollArea.setWidgetResizable(True)
        scrollArea.setWidget(campos3DWidget)
        dialogLayout.addWidget(scrollArea)

        # Se não há radios e também não há Z na geometria → avisa
        if not self._radios3d and not has_z:
            QMessageBox.information(self, self.tr("Aviso"), self.tr("Sem Dados para Z"))

        # Integração do checkbox com os radios
        self.cbAltimetriaCamada.toggled.connect(self._on_altimetria_camada_toggled)
        self._on_altimetria_camada_toggled(self.cbAltimetriaCamada.isChecked())

        # Botões OK/Cancelar
        buttonBox = QDialogButtonBox(QDialogButtonBox.StandardButton.Ok | QDialogButtonBox.StandardButton.Cancel, self.campos3DDialog)
        buttonBox.accepted.connect(self.campos3DDialog.accept)
        buttonBox.rejected.connect(self.campos3DDialog.reject)
        dialogLayout.addWidget(buttonBox)

        # Atualiza estado visual do botão "Altimetria" na janela principal
        self.atualizarTextoBotao3D()

        self.campos3DDialog.exec()

    def _on_altimetria_camada_toggled(self, checked: bool):
        """
        Marca 'Altimetria da Camada' -> limpa e desativa radios.
        Desmarca -> reativa radios (se existirem).
        """
        for rb in getattr(self, "_radios3d", []):
            rb.setEnabled(not checked)
            if checked and rb.isChecked():
                rb.setChecked(False)
        self.atualizarTextoBotao3D()

    def atualizarTextoBotao3D(self):
        """
        Atualiza o texto do botão "Altimetria" na janela principal:
          ✓ quando usar Z da camada (checkbox) ou algum radio estiver marcado.
        """
        use_geom_z = hasattr(self, "cbAltimetriaCamada") and self.cbAltimetriaCamada.isChecked()
        has_radio = any(button.isChecked() for button in self.radioGroup.buttons())
        if use_geom_z or has_radio:
            self.btn3D.setText(self.tr("Altimetria ✓"))
            self.btn3D.setStyleSheet("color: blue;")
        else:
            self.btn3D.setText(self.tr("Altimetria"))
            self.btn3D.setStyleSheet("")

    def atualizarEstadoCampos(self, campo, checked):
        """
        Atualiza o estado de seleção de um campo específico.

        Parâmetros:
        - campo (str): O nome do campo cujo estado está sendo atualizado.
        - checked (bool): O novo estado do campo (True se selecionado, False se desmarcado).

        Funcionalidades:
        - Atualiza o dicionário self.estadoCampos com o novo estado do campo.
        """
        # Atualiza o estado de seleção do campo específico
        self.estadoCampos[campo] = checked

    def mostrarCampos(self):
        """
        Exibe um diálogo para selecionar campos da tabela de atributos. A função realiza as seguintes etapas:

        1. Cria e configura o diálogo.
        2. Adiciona checkboxes para cada campo da camada, restaurando o estado anterior de seleção.
        3. Configura a área de rolagem para acomodar muitos campos.
        4. Adiciona botões OK e Cancelar ao diálogo.
        5. Exibe o diálogo.

        Funcionalidades:
        - Seleção de campos para exportação.
        - Atualização do estado dos checkboxes com base na seleção anterior.
        - Verificação dinâmica da seleção de checkboxes.
        """
        # Cria o diálogo para seleção de campos
        self.camposDialog = QDialog(self)
        self.camposDialog.setWindowTitle(self.tr("Campos da Tabela de Atributos"))  # Define o título do diálogo
        self.camposDialog.resize(150, 150)  # Define o tamanho do diálogo
        
        dialogLayout = QVBoxLayout(self.camposDialog)  # Layout vertical para o diálogo

        camposWidget = QWidget()  # Cria um widget para conter os checkboxes
        camposLayout = QVBoxLayout(camposWidget)  # Layout vertical para os checkboxes

        self.camposCheckBoxes = {}  # Dicionário para armazenar os checkboxes
        for campo in self.campos:
            checkBox = QCheckBox(campo)  # Cria um checkbox para cada campo
            checkBox.setChecked(self.estadoCampos[campo])  # Restaura o estado anterior de seleção
            checkBox.stateChanged.connect(lambda checked, c=campo: self.atualizarEstadoCampos(c, checked))  # Conecta o estado do checkbox ao método de atualização de estado
            checkBox.stateChanged.connect(self.verificarSelecao)  # Conecta o estado do checkbox ao método de verificação de seleção
            self.camposCheckBoxes[campo] = checkBox  # Armazena o checkbox no dicionário
            camposLayout.addWidget(checkBox)  # Adiciona o checkbox ao layout de campos

        scrollArea = QScrollArea(self.camposDialog)  # Cria uma área de rolagem para o diálogo
        scrollArea.setWidgetResizable(True)  # Define a área de rolagem como redimensionável
        scrollArea.setWidget(camposWidget)  # Define o widget de campos como o widget da área de rolagem
        dialogLayout.addWidget(scrollArea)  # Adiciona a área de rolagem ao layout do diálogo

        buttonBox = QDialogButtonBox(QDialogButtonBox.StandardButton.Ok | QDialogButtonBox.StandardButton.Cancel, self.camposDialog)  # Cria botões OK e Cancelar para o diálogo
        buttonBox.accepted.connect(self.camposDialog.accept)  # Conecta o botão OK ao método de aceitação do diálogo
        buttonBox.rejected.connect(self.camposDialog.reject)  # Conecta o botão Cancelar ao método de rejeição do diálogo
        dialogLayout.addWidget(buttonBox)  # Adiciona o buttonBox ao layout do diálogo

        self.camposDialog.exec()  # Exibe o diálogo

    def verificarSelecao(self):
        """
        Verifica a seleção dos checkboxes representando os campos de atributos na interface gráfica.
        A função realiza as seguintes etapas:

        1. Calcula a quantidade de checkboxes selecionados.
        2. Atualiza o texto e a cor do botão 'Rótulos' com base na quantidade de seleções.
        3. Desabilita checkboxes não selecionados se três ou mais campos estiverem selecionados.
        4. Habilita todos os checkboxes se menos de três campos estiverem selecionados.

        Funcionalidades:
        - Verificação dinâmica da seleção de checkboxes.
        - Atualização visual do botão 'Rótulos' com base na seleção.
        - Gerenciamento do estado (habilitado/desabilitado) dos checkboxes com base na quantidade de seleções.
        """
        # Calcula a quantidade de checkboxes selecionados
        selecionados = sum(checkBox.isChecked() for checkBox in self.camposCheckBoxes.values())
        # Atualiza o texto e a cor do botão 'Rótulos' com base na quantidade de seleções
        if selecionados > 0:
            self.camposButton.setText(self.tr("Rótulos ✓")) # Adiciona um checkmark se houver seleção
            self.camposButton.setStyleSheet("QPushButton { color: green; }") # Muda a cor para verde
        else:
            self.camposButton.setText(self.tr("Rótulos"))  # Texto padrão sem seleção
            self.camposButton.setStyleSheet("")  # Retorna ao estilo padrão

        # Se três ou mais campos estão selecionados, desabilita os checkboxes não selecionados
        if selecionados >= 3:
            for checkBox in self.camposCheckBoxes.values():
                if not checkBox.isChecked():
                    checkBox.setDisabled(True) # Desabilita checkboxes não selecionados
        else:
            # Se menos de três campos estão selecionados, habilita todos os checkboxes
            for checkBox in self.camposCheckBoxes.values():
                checkBox.setEnabled(True) # Habilita todos os checkboxes
    @staticmethod
    def embaralhar_cores_vibrantes():
        """
        Embaralha uma lista de cores vibrantes. A função realiza as seguintes etapas:

        1. Define uma lista de cores vibrantes usando objetos QColor.
        2. Embaralha aleatoriamente a lista de cores.
        3. Retorna a lista embaralhada de cores.

        Funcionalidades:
        - Criação de uma lista de cores vibrantes predefinidas.
        - Embaralhamento aleatório da lista de cores.
        - Retorno da lista de cores embaralhadas.

        Retorna:
        - list: Lista de cores vibrantes embaralhadas.
        """

        cores_vibrantes = [
            QColor(255, 0, 0),  # Vermelho
            QColor(0, 255, 0),  # Verde
            QColor(0, 0, 255),  # Azul
            QColor(255, 255, 0),  # Amarelo
            QColor(0, 255, 255),  # Ciano
            QColor(255, 0, 255),  # Magenta
            QColor(255, 165, 0),  # Laranja
            QColor(128, 0, 128)]  # Roxo
            # Adicione mais cores conforme necessário

        random.shuffle(cores_vibrantes)  # Embaralha a lista de cores
        return cores_vibrantes  # Retorna a lista embaralhada

    def definirCoresAleatorias(self):
        # Embaralha uma lista de cores vibrantes
        cores_vibrantes = self.embaralhar_cores_vibrantes()
        cores_iter = iter(cores_vibrantes)  # Cria um iterador para a lista de cores

        # Percorre cada item no QListWidget
        for i in range(self.listWidget.count()):
            item = self.listWidget.item(i)
            widget = self.listWidget.itemWidget(item)
            
            # Encontrando o botão e o label no widget
            button = widget.findChildren(QPushButton)[0]
            label = widget.findChildren(QLabel)[0]
            
            try:
                cor_aleatoria = next(cores_iter)  # Obtém a próxima cor do iterador
            except StopIteration:
                # Se chegar ao final da lista de cores, comece novamente
                cores_iter = iter(cores_vibrantes)
                cor_aleatoria = next(cores_iter)

            # Definindo a cor do botão e do texto do label
            button.setStyleSheet(f"QPushButton {{ background-color: {cor_aleatoria.name()}; }}")
            label.setStyleSheet(f"QLabel {{ color: {cor_aleatoria.name()}; font-weight: bold; font-style: italic; background-color: white; border: 1px solid gray; }}")

            valor = button.property('valor_atributo')  # Obtém o valor do atributo associado ao botão
            self.cores[valor] = (cor_aleatoria.red(), cor_aleatoria.green(), cor_aleatoria.blue())  # Armazena a cor selecionada

            # Atualiza o bloco gráfico com a nova cor
            combo = widget.findChildren(QComboBox)[0]  # Encontra o QComboBox no widget do item
            self.atualizarBlocoGrafico(widget, combo, button)

    def selecionarTodos(self, state):
        """
        Seleciona ou desmarca todos os checkboxes no QListWidget com base no estado do checkbox "Selecionar Todos".
        A função realiza as seguintes etapas:

        1. Itera sobre todos os itens no QListWidget.
        2. Para cada item, obtém o widget associado e encontra o QCheckBox.
        3. Define o estado do QCheckBox com base no estado do checkbox "Selecionar Todos".
        4. Atualiza o estado do botão Exportar.

        Funcionalidades:
        - Seleção ou desmarcação de todos os checkboxes no QListWidget.
        - Atualização do estado do botão Exportar com base na seleção.

        Parâmetros:
        - state (Qt.CheckState): O estado do checkbox "Selecionar Todos" (Qt.Checked ou Qt.Unchecked).
        """
        # Itera sobre todos os itens no QListWidget
        for i in range(self.listWidget.count()):
            item = self.listWidget.item(i)
            widget = self.listWidget.itemWidget(item)
            checkbox = widget.findChild(QCheckBox)  # Encontra o QCheckBox no widget do item
            checkbox.setChecked(state == Qt.CheckState.Checked)  # Define o estado do QCheckBox com base no estado do checkbox "Selecionar Todos"
        
        # Chama a função para atualizar o estado do botão Exportar sempre que selecionar todos é alterado
        self.atualizarEstadoBotaoExportar()

    def selecionarCor(self, button, label):
        """
        Abre um diálogo de seleção de cor e aplica a cor escolhida ao botão e ao label.
        A função realiza as seguintes etapas:

        1. Abre um diálogo de seleção de cor.
        2. Verifica se uma cor válida foi selecionada.
        3. Se uma cor válida foi selecionada:
           - Define a cor de fundo do botão com a cor selecionada.
           - Define a cor do texto e o estilo do label com a cor selecionada.
           - Armazena a cor selecionada em um dicionário de cores.
           - Atualiza a cor do bloco gráfico correspondente.

        Funcionalidades:
        - Seleção de cor pelo usuário.
        - Aplicação da cor selecionada a um botão e um label.
        - Armazenamento da cor selecionada para referência futura.
        - Atualização da cor do bloco gráfico.

        Parâmetros:
        - button (QPushButton): O botão cuja cor de fundo será alterada.
        - label (QLabel): O label cujo texto e estilo serão alterados.
        """
        color = QColorDialog.getColor()  # Abre o diálogo de seleção de cor
        if color.isValid():  # Verifica se uma cor foi selecionada
            button.setStyleSheet(f"QPushButton {{ background-color: {color.name()}; }}")  # Define a cor de fundo do botão
            label.setStyleSheet(f"QLabel {{ color: {color.name()}; font-weight: bold; font-style: italic; background-color: white; border: 1px solid gray; }}")  # Define a cor do texto e o estilo do label
            valor = button.property('valor_atributo')  # Obtém o valor do atributo associado ao botão
            # Armazena a cor como uma tupla RGB
            self.cores[valor] = (color.red(), color.green(), color.blue())  # Armazena a cor selecionada

            # Atualiza a cor do bloco gráfico
            item_widget = button.parentWidget()
            combo = item_widget.findChild(QComboBox)
            self.atualizarBlocoGrafico(item_widget, combo, button)

    def atualizarLineEdit(self):
        """
        Atualiza o texto do QLineEdit com a contagem total de feições do item selecionado no QListWidget.
        A função realiza as seguintes etapas:

        1. Obtém os itens selecionados no QListWidget.
        2. Se houver itens selecionados:
           - Recupera o texto do primeiro item selecionado.
           - Obtém a contagem de feições para o valor selecionado.
           - Atualiza o texto do QLineEdit com a contagem total de feições.
        3. Se não houver itens selecionados, limpa o texto do QLineEdit.

        Funcionalidades:
        - Atualização dinâmica do QLineEdit com informações sobre o item selecionado.
        - Limpeza do QLineEdit quando nenhum item está selecionado.
        """
        selectedItems = self.listWidget.selectedItems()  # Obtém os itens selecionados no QListWidget
        if selectedItems:
            valor = selectedItems[0].text()  # Recupera o texto do primeiro item selecionado
            contagem = self.valorContagem.get(valor, 0)  # Obtém a contagem para esse valor
            self.lineEdit.setText(self.tr("Total de Feições: {contagem}").format(contagem=contagem))  # Atualiza o QLineEdit com a contagem total de feições
        else:
            self.lineEdit.clear()  # Limpa o texto do QLineEdit

    def verificarCheckBoxes(self):
        """
        Verifica o estado dos checkboxes e atualiza o estado do checkbox "Selecionar Todos" e do botão Exportar.
        A função realiza as seguintes etapas:

        1. Verifica se todos os checkboxes estão selecionados.
        2. Verifica se algum checkbox está selecionado.
        3. Atualiza o estado do checkbox "Selecionar Todos" com base nas seleções dos checkboxes.
        4. Habilita o botão Exportar apenas se algum item estiver selecionado.

        Funcionalidades:
        - Verificação dinâmica da seleção de todos os checkboxes.
        - Atualização do estado do checkbox "Selecionar Todos".
        - Habilitação do botão Exportar com base na seleção dos checkboxes.
        """
        # Verifica se todos os checkboxes estão selecionados
        todos_selecionados = all(
            checkbox.isChecked() for i in range(self.listWidget.count())
            for checkbox in [self.listWidget.itemWidget(self.listWidget.item(i)).findChild(QCheckBox)])

        # Verifica se algum checkbox está selecionado
        algum_selecionado = any(
            checkbox.isChecked() for i in range(self.listWidget.count())
            for checkbox in [self.listWidget.itemWidget(self.listWidget.item(i)).findChild(QCheckBox)])

        self.selectAllCheckBox.blockSignals(True)  # Bloqueia sinais para evitar loops de sinal
        self.selectAllCheckBox.setChecked(todos_selecionados or algum_selecionado)  # Atualiza o estado do checkbox "Selecionar Todos"
        self.selectAllCheckBox.setTristate(algum_selecionado and not todos_selecionados)  # Define o estado tri-state
        self.selectAllCheckBox.blockSignals(False)  # Desbloqueia sinais

        # Habilita o botão Exportar apenas se algum item estiver selecionado
        self.buttonBox.button(QDialogButtonBox.StandardButton.Ok).setEnabled(algum_selecionado)

    def atualizarListWidget(self, index):
        """
        Atualiza o QListWidget com os valores únicos do campo selecionado no comboBox.

        Funcionalidades principais:
        1. Obtém o nome do campo atualmente selecionado no comboBox.
        2. Se o campo for 'Camada_0', insere apenas um item com o nome da camada
           e o número total de feições como contagem.
        3. Caso contrário, varre todas as feições da camada para extrair os valores
           únicos do campo selecionado e contabilizar suas ocorrências.
        4. Limpa o QListWidget e insere um item para cada valor único encontrado.
        5. Para cada item criado:
           - Cria um layout com QLabel, QCheckBox, botão de cor, QComboBox e QGraphicsView.
           - Define estilos visuais (fonte, cor, borda).
           - Conecta sinais (cliques, seleção, mudança de índice) às funções auxiliares.
           - Atualiza o bloco gráfico associado para exibir pré-visualização.
        6. No final, chama verificarCheckBoxes() para atualizar o estado do botão Exportar.
        """
        # Obtém o campo selecionado no comboBox
        campoSelecionado = self.comboBox.itemText(index)
        if not campoSelecionado:
            # Desabilita botão Exportar se nenhum campo for selecionado
            self.buttonBox.button(QDialogButtonBox.StandardButton.Ok).setEnabled(False)
            return

        valoresUnicos = set()          # Conjunto de valores únicos
        self.valorContagem = {}        # Dicionário de contagem de ocorrências

        # Caso especial: campo 'Camada_0' -> usa nome da camada como valor único
        if campoSelecionado == "Camada_0":
            unico = self.layer.name()
            valoresUnicos = {unico}
            self.valorContagem[unico] = self.layer.featureCount()
        else:
            # Percorre todas as feições e coleta valores únicos do campo selecionado
            for feature in self.layer.getFeatures():
                valor = feature[campoSelecionado]
                svalor = str(valor)
                valoresUnicos.add(svalor)
                self.valorContagem[svalor] = self.valorContagem.get(svalor, 0) + 1

        # Limpa a lista antes de adicionar novos itens
        self.listWidget.clear()

        # Cria um item no QListWidget para cada valor único
        for valor in sorted(valoresUnicos):
            item = QListWidgetItem(valor)
            item.setForeground(QBrush(QColor(255, 255, 255)))  # Cor inicial do texto
            self.listWidget.addItem(item)

            # Cria o widget personalizado para o item
            item_widget = QWidget()
            item_layout = QHBoxLayout(item_widget)
            item_layout.setSpacing(5)
            item_layout.setContentsMargins(2, 1, 2, 1)

            # Label com o texto do valor
            label = QLabel(valor)
            label.setStyleSheet("font-weight: bold; font-style: italic; background-color: white; border: 1px solid gray;")
            label.setSizePolicy(QSizePolicy.Policy.Expanding, QSizePolicy.Policy.Preferred) 
            item_layout.addWidget(label)

            # Checkbox para seleção
            checkbox = QCheckBox()
            checkbox.setChecked(self.selectAllCheckBox.isChecked())
            checkbox.stateChanged.connect(self.verificarCheckBoxes)
            item_layout.addWidget(checkbox)

            # Botão de cor
            button = QPushButton(self.tr("Cor"))
            button.setFixedSize(50, 20)
            button.clicked.connect(lambda _checked=False, botao=button, rotulo=label: self.selecionarCor(botao, rotulo))
            item_layout.addWidget(button)

            # ComboBox para blocos
            combo = QComboBox()
            combo.setMaxVisibleItems(5)
            combo.setStyleSheet("""
            QComboBox { combobox-popup: 0; }
            QComboBox QAbstractItemView {
                min-height: 140px; max-height: 140px;
                min-width: 100px;  max-width: 100px;
            }""")
            for nome_bloco in self.nomes_blocos:
                combo.addItem(self._nome_bloco_exibicao(nome_bloco), nome_bloco)
            combo.setFixedSize(80, 20)
            item_layout.addWidget(combo)

            # QGraphicsView para pré-visualização do bloco
            graphics_view = QGraphicsView()
            graphics_view.setRenderHints(QPainter.RenderHint.Antialiasing | QPainter.RenderHint.SmoothPixmapTransform)
            graphics_view.setFixedSize(20, 20)
            scene = QGraphicsScene()
            graphics_view.setScene(scene)
            item_layout.addWidget(graphics_view)

            # Define o layout final do item
            button.setProperty('valor_atributo', valor)
            item_widget.setLayout(item_layout)
            item.setSizeHint(item_widget.sizeHint())
            self.listWidget.setItemWidget(item, item_widget)

            # Atualiza a pré-visualização inicial do bloco
            self.atualizarBlocoGrafico(item_widget, combo, button)

            # Conecta sinais do combo e checkbox
            combo.currentIndexChanged.connect(lambda i, w=item_widget, c=combo, b=button: self.atualizarBlocoGrafico(w, c, b))
            checkbox.stateChanged.connect(self.verificarCheckBoxes)

        # Atualiza o estado inicial dos checkboxes e do botão Exportar
        self.verificarCheckBoxes()

    def atualizarBlocoGrafico(self, item_widget, combo, button):
        """
        Atualiza o gráfico do bloco no QGraphicsView com base na seleção do QComboBox e na cor do QPushButton.
        
        Funções principais:
        - Limpa a cena atual no QGraphicsView.
        - Desenha o bloco correspondente à seleção atual do QComboBox.
        - Aplica a cor selecionada ao bloco.
        - Centraliza o bloco na cena do QGraphicsView.
        
        Etapas detalhadas:
        1. Encontra o QGraphicsView no item_widget.
        2. Limpa a cena atual do QGraphicsView.
        3. Obtém o nome do bloco selecionado no QComboBox.
        4. Obtém a cor do QPushButton associado.
        5. Desenha o bloco na cena com a cor selecionada.
        6. Centraliza a cena e ajusta a visualização.

        Parâmetros:
        - item_widget (QWidget): O widget do item contendo o QGraphicsView.
        - combo (QComboBox): O QComboBox com a seleção do bloco.
        - button (QPushButton): O QPushButton com a cor selecionada.
        """
        graphics_view = item_widget.findChild(QGraphicsView)  # Encontra o QGraphicsView no item_widget
        scene = graphics_view.scene()  # Obtém a cena do QGraphicsView
        scene.clear()  # Limpa a cena atual

        nome_bloco = (combo.currentData(Qt.ItemDataRole.UserRole)
            or combo.currentText())
        cor = button.palette().button().color()  # Obtém a cor do botão
        if nome_bloco:
            self.desenharBloco(scene, nome_bloco, cor)  # Desenha o bloco na cena com a cor selecionada

        # Centralizar a cena
        rect = scene.itemsBoundingRect()  # Obtém o retângulo delimitador dos itens na cena
        scene.setSceneRect(rect)  # Define o retângulo delimitador como o retângulo da cena
        graphics_view.setSceneRect(rect)  # Define o retângulo delimitador como o retângulo da visualização
        graphics_view.fitInView(rect, Qt.AspectRatioMode.KeepAspectRatio)  # Ajusta a visualização para manter a proporção do retângulo

    def desenharBloco(self, scene, nome_bloco, cor):
        """
        Desenha um bloco específico na cena fornecida com base no nome do bloco e na cor fornecida.
        
        Funções principais:
        - Define a cor e a largura da caneta para desenhar.
        - Ajusta a escala dos blocos.
        - Desenha diferentes formas geométricas (círculos, linhas, pontos) para representar vários blocos.
        
        Etapas detalhadas:
        1. Define a cor e a largura da caneta.
        2. Define um fator de escala para ajustar os blocos ao tamanho desejado.
        3. Desenha o bloco específico com base no nome do bloco fornecido.
        4. Cada bloco é desenhado com as formas geométricas apropriadas (círculos, linhas, pontos).

        Parâmetros:
        - scene (QGraphicsScene): A cena onde o bloco será desenhado.
        - nome_bloco (str): O nome do bloco a ser desenhado.
        - cor (QColor): A cor para desenhar o bloco.
        """
        pen = QPen(cor)  # Define a cor da caneta
        pen.setWidth(int(0.80))  # Define a largura da caneta
        scale_factor = 1  # Escala para ajustar os blocos ao tamanho desejado

        if nome_bloco == 'CirculoX':
            # Desenha um círculo com um X dentro
            scene.addEllipse(-0.5 * scale_factor, -0.5 * scale_factor, 1.0 * scale_factor, 1.0 * scale_factor, pen)
            scene.addLine(-0.35 * scale_factor, -0.35 * scale_factor, 0.35 * scale_factor, 0.35 * scale_factor, pen)
            scene.addLine(-0.35 * scale_factor, 0.35 * scale_factor, 0.35 * scale_factor, -0.35 * scale_factor, pen)

        elif nome_bloco == 'CirculoCruz':
            # Desenha um círculo com uma cruz dentro
            scene.addEllipse(-0.5 * scale_factor, -0.5 * scale_factor, 1.0 * scale_factor, 1.0 * scale_factor, pen)
            scene.addLine(-0.5 * scale_factor, 0, 0.5 * scale_factor, 0, pen)
            scene.addLine(0, -0.5 * scale_factor, 0, 0.5 * scale_factor, pen)

        elif nome_bloco == 'CirculoTraço':
            # Desenha um círculo com um traço vertical no centro
            scene.addEllipse(-0.5 * scale_factor, -0.5 * scale_factor, 1.0 * scale_factor, 1.0 * scale_factor, pen)
            scene.addLine(0, 0, 0, -0.6 * scale_factor, pen)

        elif nome_bloco == 'CirculoPonto':
            # Desenha um círculo com um ponto no centro
            scene.addEllipse(-0.5 * scale_factor, -0.5 * scale_factor, 1.0 * scale_factor, 1.0 * scale_factor, pen)
            scene.addEllipse(-0.05 * scale_factor, -0.05 * scale_factor, 0.1 * scale_factor, 0.1 * scale_factor, pen)

        elif nome_bloco == 'Árvore':
            # Desenha a copa da árvore com elipses e o tronco com uma linha
            scene.addEllipse(-0.4 * scale_factor, -0.1 * scale_factor, 0.8 * scale_factor, 0.6 * scale_factor, pen)
            scene.addEllipse(-0.3 * scale_factor, -0.3 * scale_factor, 0.6 * scale_factor, 0.7 * scale_factor, pen)
            scene.addEllipse(-0.2 * scale_factor, -0.2 * scale_factor, 0.4 * scale_factor, 0.7 * scale_factor, pen)
            scene.addLine(0, 0.5 * scale_factor, 0, 1.0 * scale_factor, pen)

        elif nome_bloco == 'Poste':
            # Desenha o poste principal e suas travessas e fios
            scene.addLine(0, 0, 0, -2.4 * scale_factor, pen)
            # Desenha a travessa superior
            scene.addLine(-0.4 * scale_factor, -2.0 * scale_factor, 0.4 * scale_factor, -2.0 * scale_factor, pen)
            # Desenha a travessa inferior
            scene.addLine(-0.8 * scale_factor, -1.6 * scale_factor, 0.8 * scale_factor, -1.6 * scale_factor, pen)
            # Desenha os fios inclinados
            scene.addLine(0, -1.6 * scale_factor, -0.5656 * scale_factor, -1.0344 * scale_factor, pen)
            scene.addLine(0, -1.6 * scale_factor, 0.5656 * scale_factor, -1.0344 * scale_factor, pen)

        elif nome_bloco == 'Bandeira':
            # Desenha a haste da bandeira e um triângulo como bandeira
            scene.addLine(0, 0, 0, -1.5 * scale_factor, pen)

            # Desenha a bandeira como um triângulo maior à esquerda
            base_triangular = -0.85 * scale_factor
            altura_triangular = 0.75 * scale_factor
            pontos_bandeira = [(0, -1.5 * scale_factor), 
                               (base_triangular, -1.5 * scale_factor + altura_triangular / 2), 
                               (0, -1.5 * scale_factor + altura_triangular), 
                               (0, -1.5 * scale_factor)]
            scene.addPolygon(QPolygonF([QPointF(p[0], p[1]) for p in pontos_bandeira]), pen)

            # Desenha a linha horizontal maior na base da haste
            scene.addLine(-0.5 * scale_factor, 0, 0.5 * scale_factor, 0, pen)

        elif nome_bloco == 'Bandeira 2':
            # Desenha a haste da bandeira e um retângulo como bandeira
            scene.addLine(0, 0, 0, -1.5 * scale_factor, pen)

            # Desenha a bandeira como um retângulo à esquerda
            largura_bandeira = -0.75 * scale_factor
            altura_bandeira = 0.6 * scale_factor
            topo_bandeira = -1.5 * scale_factor
            base_bandeira = topo_bandeira + altura_bandeira
            pontos_bandeira = [
                (0, topo_bandeira),
                (largura_bandeira, topo_bandeira),
                (largura_bandeira, base_bandeira),
                (0, base_bandeira),
                (0, topo_bandeira)  # Fecha o ponto voltando ao ponto inicial
            ]
            scene.addPolygon(QPolygonF([QPointF(p[0], p[1]) for p in pontos_bandeira]), pen)

            # Desenha a linha horizontal na base da haste
            scene.addLine(-0.25 * scale_factor, 0, 0.25 * scale_factor, 0, pen)

        elif nome_bloco == 'Cerca':
            # Desenha postes verticais e painéis horizontais para a cerca
            altura_poste = 0.8 * scale_factor  # Altura dos postes da cerca
            largura_painel = 0.1 * scale_factor  # Largura dos painéis horizontais
            numero_postes = 3  # Número de postes na cerca

            # Desenha os postes verticais e os painéis horizontais
            for i in range(numero_postes):
                x_pos = i * largura_painel * 2
                # Desenha o poste vertical
                scene.addLine(x_pos, 0, x_pos, -altura_poste, pen)

                # Desenha os painéis horizontais conectando os postes
                if i < numero_postes - 1:
                    scene.addLine(x_pos, -altura_poste / 2, x_pos + largura_painel * 2, -altura_poste / 2, pen)
                    scene.addLine(x_pos, -altura_poste / 4, x_pos + largura_painel * 2, -altura_poste / 4, pen)
                    scene.addLine(x_pos, -altura_poste * 3 / 4, x_pos + largura_painel * 2, -altura_poste * 3 / 4, pen)

        elif nome_bloco == 'Rocha':
            # Desenha a rocha como uma forma poligonal
            pontos_rocha = [
                (-0.5 * scale_factor, 0),
                (-0.3 * scale_factor, 0.3 * scale_factor),
                (0, 0.5 * scale_factor),
                (0.3 * scale_factor, 0.3 * scale_factor),
                (0.5 * scale_factor, 0),
                (0.3 * scale_factor, -0.3 * scale_factor),
                (0, -0.5 * scale_factor),
                (-0.3 * scale_factor, -0.3 * scale_factor),
                (-0.5 * scale_factor, 0)
            ]
            scene.addPolygon(QPolygonF([QPointF(p[0], p[1]) for p in pontos_rocha]), pen)

        elif nome_bloco == 'Bueiro':
            # Desenha dois círculos concêntricos e uma cruz no centro para representar um bueiro
            scene.addEllipse(-0.5 * scale_factor, -0.5 * scale_factor, 1.0 * scale_factor, 1.0 * scale_factor, pen)
            scene.addEllipse(-0.4 * scale_factor, -0.4 * scale_factor, 0.8 * scale_factor, 0.8 * scale_factor, pen)

            # Adiciona uma cruz pequena no centro
            cruz_tamanho = 0.1 * scale_factor
            scene.addLine(-cruz_tamanho, 0, cruz_tamanho, 0, pen)
            scene.addLine(0, -cruz_tamanho, 0, cruz_tamanho, pen)

        elif nome_bloco == 'QuadradoX':
            # Desenha um quadrado com um X dentro
            scene.addPolygon(QPolygonF([
                QPointF(-0.5 * scale_factor, -0.5 * scale_factor),
                QPointF(-0.5 * scale_factor, 0.5 * scale_factor),
                QPointF(0.5 * scale_factor, 0.5 * scale_factor),
                QPointF(0.5 * scale_factor, -0.5 * scale_factor),
                QPointF(-0.5 * scale_factor, -0.5 * scale_factor)
            ]), pen)

            # Desenha um X dentro do quadrado
            scene.addLine(-0.5 * scale_factor, -0.5 * scale_factor, 0.5 * scale_factor, 0.5 * scale_factor, pen)
            scene.addLine(0.5 * scale_factor, -0.5 * scale_factor, -0.5 * scale_factor, 0.5 * scale_factor, pen)

        elif nome_bloco == 'QuadradoTraço':
            # Desenha um quadrado com um traço vertical no centro
            scene.addPolygon(QPolygonF([
                QPointF(-0.5 * scale_factor, -0.5 * scale_factor),
                QPointF(-0.5 * scale_factor, 0.5 * scale_factor),
                QPointF(0.5 * scale_factor, 0.5 * scale_factor),
                QPointF(0.5 * scale_factor, -0.5 * scale_factor),
                QPointF(-0.5 * scale_factor, -0.5 * scale_factor)
            ]), pen)

            # Desenha um traço vertical no centro do quadrado, se estendendo um pouco acima
            scene.addLine(0, 0 * scale_factor, 0, -0.6 * scale_factor, pen)

        elif nome_bloco == 'QuadradoCruz':
            # Desenha um quadrado com uma cruz dentro
            scene.addPolygon(QPolygonF([
                QPointF(-0.5 * scale_factor, -0.5 * scale_factor),
                QPointF(-0.5 * scale_factor, 0.5 * scale_factor),
                QPointF(0.5 * scale_factor, 0.5 * scale_factor),
                QPointF(0.5 * scale_factor, -0.5 * scale_factor),
                QPointF(-0.5 * scale_factor, -0.5 * scale_factor)
            ]), pen)

            # Desenha uma cruz dentro do quadrado
            scene.addLine(-0.4 * scale_factor, 0, 0.4 * scale_factor, 0, pen)
            scene.addLine(0, -0.4 * scale_factor, 0, 0.4 * scale_factor, pen)

        elif nome_bloco == 'TrianguloX':
            # Desenha um triângulo com um X dentro
            scene.addPolygon(QPolygonF([
                QPointF(-0.5 * scale_factor, 0.289 * scale_factor),
                QPointF(0.5 * scale_factor, 0.289 * scale_factor),
                QPointF(0, -0.577 * scale_factor),
                QPointF(-0.5 * scale_factor, 0.289 * scale_factor)
            ]), pen)

            # Desenha o X, centralizado no ponto (0, 0)
            x_size = 0.20 * scale_factor
            y_size = 0.289 * scale_factor
            scene.addLine(-x_size, -y_size, x_size, y_size, pen)
            scene.addLine(-x_size, y_size, x_size, -y_size, pen)

        elif nome_bloco == 'QuadradoPonto':
            # Desenha um quadrado com um ponto no centro
            scene.addPolygon(QPolygonF([
                QPointF(-0.5 * scale_factor, -0.5 * scale_factor),
                QPointF(-0.5 * scale_factor, 0.5 * scale_factor),
                QPointF(0.5 * scale_factor, 0.5 * scale_factor),
                QPointF(0.5 * scale_factor, -0.5 * scale_factor),
                QPointF(-0.5 * scale_factor, -0.5 * scale_factor)
            ]), pen)
            # Desenha um ponto no centro do quadrado
            brush = QBrush(cor)
            scene.addEllipse(-0.05 * scale_factor, -0.05 * scale_factor, 0.1 * scale_factor, 0.1 * scale_factor, pen, brush)

        elif nome_bloco == 'TrianguloPonto':
            # Desenha um triângulo com um ponto no centro
            scene.addPolygon(QPolygonF([
                QPointF(-0.5 * scale_factor, 0.289 * scale_factor),
                QPointF(0.5 * scale_factor, 0.289 * scale_factor),
                QPointF(0, -0.577 * scale_factor),
                QPointF(-0.5 * scale_factor, 0.289 * scale_factor)
            ]), pen)
            # Desenha o ponto
            brush = QBrush(cor)
            scene.addEllipse(-0.05 * scale_factor, -0.05 * scale_factor, 0.1 * scale_factor, 0.1 * scale_factor, pen, brush)

        elif nome_bloco == 'TrianguloTraço':
            # Desenha um triângulo com um traço vertical no centro
            scene.addPolygon(QPolygonF([
                QPointF(-0.5 * scale_factor, 0.289 * scale_factor),
                QPointF(0.5 * scale_factor, 0.289 * scale_factor),
                QPointF(0, -0.577 * scale_factor),
                QPointF(-0.5 * scale_factor, 0.289 * scale_factor)
            ]), pen)
            # Desenha o traço vertical no centro do triângulo
            scene.addLine(0, 0, 0, -0.577 * scale_factor, pen)

        elif nome_bloco == 'Casa':
            # Desenha a base da casa e o telhado
            scene.addPolygon(QPolygonF([
                QPointF(-0.5 * scale_factor, 0.25 * scale_factor),
                QPointF(-0.5 * scale_factor, -0.25 * scale_factor),
                QPointF(0.5 * scale_factor, -0.25 * scale_factor),
                QPointF(0.5 * scale_factor, 0.25 * scale_factor),
                QPointF(-0.5 * scale_factor, 0.25 * scale_factor)
            ]), pen)
            # Desenha o telhado
            scene.addPolygon(QPolygonF([
                QPointF(-0.5 * scale_factor, -0.25 * scale_factor),
                QPointF(0, -0.5 * scale_factor),
                QPointF(0.5 * scale_factor, -0.25 * scale_factor)
            ]), pen)

        elif nome_bloco == 'TrianguloCruz':
            # Desenha um triângulo com uma cruz dentro
            scene.addPolygon(QPolygonF([
                QPointF(-0.5 * scale_factor, 0.289 * scale_factor),
                QPointF(0.5 * scale_factor, 0.289 * scale_factor),
                QPointF(0 * scale_factor, -0.577 * scale_factor),
                QPointF(-0.5 * scale_factor, 0.289 * scale_factor)
            ]), pen)
            # Desenha a cruz centralizada
            scene.addLine(0, -0.289 * scale_factor, 0, 0.289 * scale_factor, pen)
            scene.addLine(-0.289 * scale_factor, 0, 0.289 * scale_factor, 0, pen)

        elif nome_bloco == 'Topografia GPS':
            # Desenha o tripé e o GPS no topo
            altura_tripe = 1.5 * scale_factor
            largura_base = 0.8 * scale_factor
            largura_gps = 0.2 * scale_factor
            altura_gps = 0.1 * scale_factor
            offset = altura_tripe / 2

            # Desenha as pernas do tripé apontando para baixo
            scene.addLine(0, -offset, -largura_base / 2, offset, pen)
            scene.addLine(0, -offset, largura_base / 2, offset, pen)
            scene.addLine(0, -offset, 0, -offset + 0.2 * scale_factor, pen)

            # Desenha a linha vertical no centro para simular um tripé
            scene.addLine(0, -offset, 0, offset, pen)

            # Desenha o retângulo para representar o GPS no topo do tripé
            scene.addPolygon(QPolygonF([
                QPointF(-largura_gps, -offset + altura_gps),
                QPointF(-largura_gps, -offset - altura_gps),
                QPointF(largura_gps, -offset - altura_gps),
                QPointF(largura_gps, -offset + altura_gps),
                QPointF(-largura_gps, -offset + altura_gps)
            ]), pen)

            # Adiciona um detalhe no GPS, como um pequeno círculo (botão)
            scene.addEllipse(-0.02 * scale_factor, -offset - 0.02 * scale_factor, 0.04 * scale_factor, 0.04 * scale_factor, pen)

    def criar_blocos(self, doc, cores):
        """
        Cria e adiciona blocos predefinidos ao documento DXF. A função realiza as seguintes etapas:

        1. Verifica se cada bloco predefinido já existe no documento DXF.
        2. Se o bloco não existir, cria o bloco usando a função correspondente.
        3. Adiciona o nome do bloco criado à lista de nomes de blocos.

        Parâmetros:
        - doc (ezdxf.document): O documento DXF onde os blocos serão adicionados.
        - cores (dict): Dicionário de cores escolhidas.

        Funcionalidades:
        - Criação de vários tipos de blocos predefinidos (círculos, quadrados, triângulos, etc.).
        - Verificação da existência dos blocos antes de criá-los.
        - Retorno de uma lista com os nomes dos blocos criados.

        Retorna:
        - list: Lista com os nomes dos blocos criados.
        """
        nomes_blocos = []

        # Nome técnico do bloco DXF. Não traduzir.
        BLOCO_CIRCULO_X = "CirculoX"
        BLOCO_CIRCULO_CRUZ = "CirculoCruz"
        BLOCO_CIRCULO_TRACO = "CirculoTraço"
        BLOCO_CIRCULO_PONTO = "CirculoPonto"
        BLOCO_ARVORE = "Árvore"
        BLOCO_POSTE = "Poste"
        BLOCO_BANDEIRA = "Bandeira"
        BLOCO_BANDEIRA_2 = "Bandeira 2"
        BLOCO_CERCA = "Cerca"
        BLOCO_ROCHA = "Rocha"
        BLOCO_BUEIRO = "Bueiro"
        BLOCO_QUADRADO_X = "QuadradoX"
        BLOCO_QUADRADO_CRUZ = "QuadradoCruz"
        BLOCO_QUADRADO_TRACO = "QuadradoTraço"
        BLOCO_QUADRADO_PONTO = "QuadradoPonto"
        BLOCO_TRIANGULO_X = "TrianguloX"
        BLOCO_TRIANGULO_CRUZ = "TrianguloCruz"
        BLOCO_TRIANGULO_PONTO = "TrianguloPonto"
        BLOCO_TRIANGULO_TRACO = "TrianguloTraço"
        BLOCO_CASA = "Casa"
        BLOCO_TOPOGRAFIA_GPS = "Topografia GPS"

        # Verifica se os blocos já existem antes de criar novos
        if BLOCO_CIRCULO_X not in doc.blocks:
            nome_bloco_x = self.criar_bloco_circulo_com_linhas(doc, BLOCO_CIRCULO_X, cores, [((-0.35, -0.35), (0.35, 0.35)), ((-0.35, 0.35), (0.35, -0.35))])
            nomes_blocos.append(nome_bloco_x)

        if BLOCO_CIRCULO_CRUZ not in doc.blocks:
            nome_bloco_cruz = self.criar_bloco_circulo_com_linhas(doc, BLOCO_CIRCULO_CRUZ, cores, [((-0.5, 0), (0.5, 0)), ((0, -0.5), (0, 0.5))])
            nomes_blocos.append(nome_bloco_cruz)

        if BLOCO_CIRCULO_TRACO not in doc.blocks:
            nome_bloco_traco_vertical = self.criar_bloco_circulo_com_linhas(doc, BLOCO_CIRCULO_TRACO, cores, [((0, 0), (0, 0.6))])
            nomes_blocos.append(nome_bloco_traco_vertical)

        # Criação do bloco CirculoComPontoCentral
        if BLOCO_CIRCULO_PONTO not in doc.blocks:
            nome_bloco_ponto_central = self.criar_bloco_circulo_com_ponto(doc, BLOCO_CIRCULO_PONTO, cores)
            nomes_blocos.append(nome_bloco_ponto_central)

        # Criação do bloco ÁRVORE
        if BLOCO_ARVORE not in doc.blocks:
            nome_bloco_arvore = self.criar_bloco_arvore(doc, BLOCO_ARVORE, cores)
            nomes_blocos.append(nome_bloco_arvore)

        # Criação do bloco POSTE
        if BLOCO_POSTE not in doc.blocks:
            nome_bloco_poste = self.criar_bloco_poste(doc, BLOCO_POSTE, cores)
            nomes_blocos.append(nome_bloco_poste)

        # Criação do bloco BANDEIRA
        if BLOCO_BANDEIRA not in doc.blocks:
            nome_bloco_bandeira = self.criar_bloco_bandeira(doc, BLOCO_BANDEIRA, cores)
            nomes_blocos.append(nome_bloco_bandeira)

        # Criação do bloco BANDEIRA 2
        if BLOCO_BANDEIRA_2 not in doc.blocks:
            nome_bloco_bandeira_Q = self.criar_bloco_bandeira_Q(doc, BLOCO_BANDEIRA_2, cores)
            nomes_blocos.append(nome_bloco_bandeira_Q)

        # Criação do bloco CERCA
        if BLOCO_CERCA not in doc.blocks:
            nome_bloco_cerca = self.criar_bloco_cerca(doc, BLOCO_CERCA, cores)
            nomes_blocos.append(nome_bloco_cerca)

        # Verifica e cria o bloco de rocha
        if BLOCO_ROCHA not in doc.blocks:
            nome_bloco_rocha = self.criar_bloco_rocha(doc, BLOCO_ROCHA, cores)
            nomes_blocos.append(nome_bloco_rocha)

        # Verifica e cria o bloco de bueiro
        if BLOCO_BUEIRO not in doc.blocks:
            nome_bloco_bueiro = self.criar_bloco_bueiro(doc, BLOCO_BUEIRO, cores)
            nomes_blocos.append(nome_bloco_bueiro)

        # Criação do o bloco QuadradoComX 
        if BLOCO_QUADRADO_X not in doc.blocks:
            nome_bloco_QuadradoComX = self.criar_bloco_quadrado_com_x(doc, BLOCO_QUADRADO_X, cores)
            nomes_blocos.append(nome_bloco_QuadradoComX)

        # Criação do bloco QuadradoComCruz
        if BLOCO_QUADRADO_CRUZ not in doc.blocks:
            nome_bloco_QuadradoComCruz = self.criar_bloco_quadrado_com_cruz(doc, BLOCO_QUADRADO_CRUZ, cores)
            nomes_blocos.append(nome_bloco_QuadradoComCruz)

        # Criação do bloco QuadradoComTraco
        if BLOCO_QUADRADO_TRACO not in doc.blocks:
            nome_bloco_QuadradoComTraco = self.criar_bloco_quadrado_com_traco(doc, BLOCO_QUADRADO_TRACO, cores)
            nomes_blocos.append(nome_bloco_QuadradoComTraco)

        # Criação do bloco QuadradoComPonto
        if BLOCO_QUADRADO_PONTO not in doc.blocks:
            nome_bloco_QuadradoComPonto = self.criar_bloco_quadrado_com_ponto(doc, BLOCO_QUADRADO_PONTO, cores)
            nomes_blocos.append(nome_bloco_QuadradoComPonto)

        # Criação do bloco TrianguloComX
        if BLOCO_TRIANGULO_X not in doc.blocks:
            nome_bloco_triangulo_com_X = self.criar_bloco_triangulo_com_x(doc, BLOCO_TRIANGULO_X, cores)
            nomes_blocos.append(nome_bloco_triangulo_com_X)

        # Criação do bloco TrianguloComCruz
        if BLOCO_TRIANGULO_CRUZ not in doc.blocks:
            nome_bloco_triangulo_cruz = self.criar_bloco_triangulo_com_cruz(doc, BLOCO_TRIANGULO_CRUZ, cores)
            nomes_blocos.append(nome_bloco_triangulo_cruz)

        # Criação do bloco TrianguloComPonto
        if BLOCO_TRIANGULO_PONTO not in doc.blocks:
            nome_bloco_ponto = self.criar_bloco_triangulo_com_ponto(doc, BLOCO_TRIANGULO_PONTO, cores)
            nomes_blocos.append(nome_bloco_ponto)

        # Criação do bloco TrianguloComTraco
        if BLOCO_TRIANGULO_TRACO not in doc.blocks:
            nome_bloco_traco = self.criar_bloco_triangulo_com_traco(doc, BLOCO_TRIANGULO_TRACO, cores)
            nomes_blocos.append(nome_bloco_traco)

        # Criação do bloco Casa
        if BLOCO_CASA not in doc.blocks:
            nome_bloco_casa = self.criar_bloco_casa(doc, BLOCO_CASA, cores)
            nomes_blocos.append(nome_bloco_casa)

        # Criação do bloco Topografia
        if BLOCO_TOPOGRAFIA_GPS not in doc.blocks:
            nome_bloco_gps = self.criar_bloco_gps_tripe(doc, BLOCO_TOPOGRAFIA_GPS, cores)
            nomes_blocos.append(nome_bloco_gps)

            return nomes_blocos

    def criar_bloco_gps_tripe(self, doc, nome_bloco, cores):
        bloco = doc.blocks.new(name=nome_bloco)
        cor_tripe = cores.get('cor_tripe', (0, 0, 0))  # Cor padrão preta para o tripé
        cor_gps = cores.get('cor_gps', (0, 0, 0))  # Cor padrão 
        cor_detalhe = cores.get('cor_detalhe', (0, 0, 0))  # Cor padrão 

        # Altura e largura do tripé
        altura_tripe = 1.5
        largura_base = 0.8

        # Desenha as pernas do tripé apontando para baixo
        bloco.add_line(start=(0, altura_tripe), end=(-largura_base / 2, 0), dxfattribs={'color': rgb2int(cor_tripe)})
        bloco.add_line(start=(0, altura_tripe), end=(largura_base / 2, 0), dxfattribs={'color': rgb2int(cor_tripe)})
        bloco.add_line(start=(0, altura_tripe), end=(0, 0.2), dxfattribs={'color': rgb2int(cor_tripe)})

        # Desenha o retângulo para representar o GPS no topo do tripé
        largura_gps = 0.2
        altura_gps = 0.1
        bloco.add_lwpolyline([(0 - largura_gps / 2, altura_tripe + altura_gps / 2), 
                              (0 - largura_gps / 2, altura_tripe - altura_gps / 2),
                              (0 + largura_gps / 2, altura_tripe - altura_gps / 2), 
                              (0 + largura_gps / 2, altura_tripe + altura_gps / 2), 
                              (0 - largura_gps / 2, altura_tripe + altura_gps / 2)], 
                              dxfattribs={'color': rgb2int(cor_gps)})

        # Adiciona um detalhe no GPS, como um pequeno círculo (botão)
        bloco.add_circle(center=(0, altura_tripe), radius=0.02, dxfattribs={'color': rgb2int(cor_detalhe)})

        return nome_bloco

    def criar_bloco_casa(self, doc, nome_bloco, cores):
        bloco = doc.blocks.new(name=nome_bloco)
        cor_linha = cores.get(nome_bloco, (128, 0, 0))  # Cor padrão vermelha para a edificação

        # Desenha a base da casa
        bloco.add_lwpolyline([(-0.5, -0.25), (-0.5, 0.25), (0.5, 0.25), (0.5, -0.25), (-0.5, -0.25)], dxfattribs={'color': rgb2int(cor_linha)})

        # Desenha o telhado
        bloco.add_lwpolyline([(-0.5, 0.25), (0, 0.5), (0.5, 0.25)], dxfattribs={'color': rgb2int(cor_linha)})

        return nome_bloco

    def criar_bloco_rocha(self, doc, nome_bloco, cores):
        bloco = doc.blocks.new(name=nome_bloco)
        cor_linha = cores.get(nome_bloco, (105, 105, 105))  # Cor padrão cinza

        # Ajustando os pontos para que o ponto esteja centralizado no ponto (0,0)
        pontos_rocha = [(-0.5, 0), (-0.3, 0.3), (0, 0.5), (0.3, 0.3), (0.5, 0), (0.3, -0.3), (0, -0.5), (-0.3, -0.3), (-0.5, 0)]
        bloco.add_lwpolyline(pontos_rocha, dxfattribs={'color': rgb2int(cor_linha)})

        return nome_bloco

    def criar_bloco_bueiro(self, doc, nome_bloco, cores):
        bloco = doc.blocks.new(name=nome_bloco)
        cor_linha = cores.get(nome_bloco, (0, 0, 0))  # Cor padrão preta para o bueiro

        # Adiciona dois círculos concêntricos para representar a parte superior do bueiro
        bloco.add_circle(center=(0, 0), radius=0.5, dxfattribs={'color': rgb2int(cor_linha)})
        bloco.add_circle(center=(0, 0), radius=0.4, dxfattribs={'color': rgb2int(cor_linha)})

        # Adiciona uma cruz pequena no centro
        cruz_tamanho = 0.1
        bloco.add_line(start=(-cruz_tamanho, 0), end=(cruz_tamanho, 0), dxfattribs={'color': rgb2int(cor_linha)})
        bloco.add_line(start=(0, -cruz_tamanho), end=(0, cruz_tamanho), dxfattribs={'color': rgb2int(cor_linha)})

        return nome_bloco

    def criar_bloco_triangulo_com_x(self, doc, nome_bloco, cores):
        bloco = doc.blocks.new(name=nome_bloco)
        cor_linha = cores.get(nome_bloco, (0, 0, 0))  # Cor padrão preta
        # Desenha o triângulo
        bloco.add_lwpolyline([(-0.5, -0.289), (0.5, -0.289), (0, 0.577), (-0.5, -0.289)], dxfattribs={'color': rgb2int(cor_linha)})
        # Desenha o X, centralizado no ponto (0, 0.192)
        x_center = 0
        y_center = 0
        x_size = 0.35
        y_size = 0.54 # A altura de um triângulo menor que seria formado pelo X
        bloco.add_line(start=(x_center - x_size / 2, y_center - y_size / 2), end=(x_center + x_size / 2, y_center + y_size / 2), dxfattribs={'color': rgb2int(cor_linha)})
        bloco.add_line(start=(x_center - x_size / 2, y_center + y_size / 2), end=(x_center + x_size / 2, y_center - y_size / 2), dxfattribs={'color': rgb2int(cor_linha)})
        return nome_bloco

    def criar_bloco_triangulo_com_cruz(self, doc, nome_bloco, cores):
        bloco = doc.blocks.new(name=nome_bloco)
        cor_linha = cores.get(nome_bloco, (0, 0, 0))
        # Desenha o triângulo
        bloco.add_lwpolyline([(-0.5, -0.289), (0.5, -0.289), (0, 0.577), (-0.5, -0.289)], dxfattribs={'color': rgb2int(cor_linha)})
        # Desenha a cruz
        bloco.add_line(start=(0, -0.1156), end=(0, 0.404), dxfattribs={'color': rgb2int(cor_linha)})
        bloco.add_line(start=(-0.3, 0.1442), end=(0.3, 0.1442), dxfattribs={'color': rgb2int(cor_linha)})
        return nome_bloco

    def criar_bloco_triangulo_com_ponto(self, doc, nome_bloco, cores):
        bloco = doc.blocks.new(name=nome_bloco)
        cor_linha = cores.get(nome_bloco, (0, 0, 0))
        # Desenha o triângulo
        bloco.add_lwpolyline([(-0.5, -0.289), (0.5, -0.289), (0, 0.577), (-0.5, -0.289)], dxfattribs={'color': rgb2int(cor_linha)})
        # Desenha o ponto
        bloco.add_circle(center=(0, 0), radius=0.05, dxfattribs={'color': rgb2int(cor_linha)})
        return nome_bloco

    def criar_bloco_triangulo_com_traco(self, doc, nome_bloco, cores):
        bloco = doc.blocks.new(name=nome_bloco)
        cor_linha = cores.get(nome_bloco, (0, 0, 0))
        # Desenha o triângulo
        bloco.add_lwpolyline([(-0.5, -0.289), (0.5, -0.289), (0, 0.577), (-0.5, -0.289)], dxfattribs={'color': rgb2int(cor_linha)})

        bloco.add_line(start=(0, 0), end=(0, 0.677), dxfattribs={'color': rgb2int(cor_linha)})
        return nome_bloco

    def criar_bloco_quadrado_com_x(self, doc, nome_bloco, cores):
        bloco = doc.blocks.new(name=nome_bloco)
        cor_linha = cores.get('cor_linha', (0, 0, 0))  # Cor padrão preta
        # Desenha o quadrado centralizado
        bloco.add_lwpolyline([(-0.5, -0.5), (-0.5, 0.5), (0.5, 0.5), (0.5, -0.5), (-0.5, -0.5)], dxfattribs={'color': rgb2int(cor_linha)})
        # Desenha um X dentro do quadrado
        bloco.add_line(start=(-0.5, -0.5), end=(0.5, 0.5), dxfattribs={'color': rgb2int(cor_linha)})
        bloco.add_line(start=(0.5, -0.5), end=(-0.5, 0.5), dxfattribs={'color': rgb2int(cor_linha)})
        return nome_bloco

    def criar_bloco_quadrado_com_cruz(self, doc, nome_bloco, cores):
        bloco = doc.blocks.new(name=nome_bloco)
        cor_linha = cores.get('cor_linha', (0, 0, 0))
        # Desenha o quadrado centralizado
        bloco.add_lwpolyline([(-0.5, -0.5), (-0.5, 0.5), (0.5, 0.5), (0.5, -0.5), (-0.5, -0.5)], dxfattribs={'color': rgb2int(cor_linha)})
        # Desenha uma cruz dentro do quadrado
        bloco.add_line(start=(-0.4, 0), end=(0.4, 0), dxfattribs={'color': rgb2int(cor_linha)})
        bloco.add_line(start=(0, -0.4), end=(0, 0.4), dxfattribs={'color': rgb2int(cor_linha)})
        return nome_bloco

    def criar_bloco_quadrado_com_traco(self, doc, nome_bloco, cores):
        bloco = doc.blocks.new(name=nome_bloco)
        cor_linha = cores.get('cor_linha', (0, 0, 0))
        # Desenha o quadrado centralizado
        bloco.add_lwpolyline([(-0.5, -0.5), (-0.5, 0.5), (0.5, 0.5), (0.5, -0.5), (-0.5, -0.5)], dxfattribs={'color': rgb2int(cor_linha)})
        # Desenha um traço vertical no centro do quadrado, se estendendo um pouco acima
        bloco.add_line(start=(0, 0), end=(0, 0.6), dxfattribs={'color': rgb2int(cor_linha)})
        return nome_bloco

    def criar_bloco_quadrado_com_ponto(self, doc, nome_bloco, cores):
        bloco = doc.blocks.new(name=nome_bloco)
        cor_ponto = cores.get('cor_ponto', (0, 0, 0))
        # Desenha o quadrado centralizado
        bloco.add_lwpolyline([(-0.5, -0.5), (-0.5, 0.5), (0.5, 0.5), (0.5, -0.5), (-0.5, -0.5)], dxfattribs={'color': rgb2int(cor_ponto)})
        # Desenha um ponto no centro do quadrado
        bloco.add_point((0, 0), dxfattribs={'color': rgb2int(cor_ponto)})
        return nome_bloco

    def criar_bloco_cerca(self, doc, nome_bloco, cores):
        bloco = doc.blocks.new(name=nome_bloco)

        # Define a cor para a cerca
        cor_cerca = cores.get('cor_cerca', (139, 69, 19))  # Cor padrão marrom para a cerca

        # Parâmetros para o desenho da cerca
        altura_poste = 0.8  # Altura dos postes da cerca
        largura_painel = 0.1  # Largura dos painéis horizontais
        numero_postes = 3  # Número de postes na cerca

        # Desenha os postes verticais e os painéis horizontais
        for i in range(numero_postes):
            x_pos = i * largura_painel * 2
            # Desenha o poste vertical
            bloco.add_line(start=(x_pos, 0), end=(x_pos, altura_poste), dxfattribs={'color': rgb2int(cor_cerca)})

            # Desenha os painéis horizontais conectando os postes
            if i < numero_postes - 1:
                bloco.add_line(start=(x_pos, altura_poste / 2), end=(x_pos + largura_painel * 2, altura_poste / 2), dxfattribs={'color': rgb2int(cor_cerca)})
                bloco.add_line(start=(x_pos, altura_poste / 4), end=(x_pos + largura_painel * 2, altura_poste / 4), dxfattribs={'color': rgb2int(cor_cerca)})
                bloco.add_line(start=(x_pos, altura_poste * 3 / 4), end=(x_pos + largura_painel * 2, altura_poste * 3 / 4), dxfattribs={'color': rgb2int(cor_cerca)})

        return nome_bloco

    def criar_bloco_bandeira(self, doc, nome_bloco, cores):
        bloco = doc.blocks.new(name=nome_bloco)
        
        # Define as cores
        cor_haste = cores.get('cor_haste', (105, 105, 105))  # Cor padrão cinza para a haste
        cor_bandeira = cores.get('cor_bandeira', (255, 0, 0))  # Cor padrão vermelha para a bandeira

        # Adiciona uma linha vertical para representar a haste da bandeira
        altura_haste = 1.5
        bloco.add_line(start=(0, 0), end=(0, altura_haste), dxfattribs={'color': rgb2int(cor_haste)})

        # Adiciona um triângulo maior para representar a bandeira à esquerda
        base_triangular = -0.85  # Agora negativo para ir à esquerda
        altura_triangular = 0.75
        pontos_bandeira = [(0, altura_haste), (base_triangular, altura_haste - altura_triangular / 2), (0, altura_haste - altura_triangular), (0, altura_haste)]
        bloco.add_lwpolyline(points=pontos_bandeira, dxfattribs={'color': rgb2int(cor_bandeira)})

        # Adiciona uma linha horizontal maior na base da haste
        bloco.add_line(start=(-0.5, 0), end=(0.5, 0), dxfattribs={'color': rgb2int(cor_haste)})

        return nome_bloco

    def criar_bloco_bandeira_Q(self, doc, nome_bloco, cores):
        bloco = doc.blocks.new(name=nome_bloco)
        
        # Define as cores
        cor_haste = cores.get('cor_haste', (105, 105, 105))  # Cor padrão cinza para a haste
        cor_bandeira = cores.get('cor_bandeira', (255, 0, 0))  # Cor padrão vermelha para a bandeira

        # Adiciona uma linha vertical para representar a haste da bandeira
        altura_haste = 1.5
        bloco.add_line(start=(0, 0), end=(0, altura_haste), dxfattribs={'color': rgb2int(cor_haste)})

        # Adiciona um retângulo para representar a bandeira no topo da haste e à esquerda
        largura_bandeira = -0.75  # Largura negativa para a esquerda
        altura_bandeira = 0.6
        topo_bandeira = altura_haste
        base_bandeira = topo_bandeira - altura_bandeira
        bloco.add_lwpolyline([
            (0, topo_bandeira),
            (largura_bandeira, topo_bandeira),
            (largura_bandeira, base_bandeira),
            (0, base_bandeira),
            (0, topo_bandeira)  # Fecha o ponto voltando ao ponto inicial
        ], dxfattribs={'color': rgb2int(cor_bandeira)})

        # Adiciona uma linha horizontal na base da haste
        bloco.add_line(start=(-0.25, 0), end=(0.25, 0), dxfattribs={'color': rgb2int(cor_haste)})

        return nome_bloco

    def criar_bloco_poste(self, doc, nome_bloco, cores):
        bloco = doc.blocks.new(name=nome_bloco)
        cor_poste = cores.get('cor_poste', (0, 0, 0))

        # Poste principal (linha vertical)
        bloco.add_line(start=(0, 0), end=(0, 2.4), dxfattribs={'color': rgb2int(cor_poste)})

        # Travessa superior (linha horizontal menor)
        bloco.add_line(start=(-0.4, 2.0), end=(0.4, 2.0), dxfattribs={'color': rgb2int(cor_poste)})

        # Travessa inferior (linha horizontal maior)
        bloco.add_line(start=(-0.8, 1.6), end=(0.8, 1.6), dxfattribs={'color': rgb2int(cor_poste)})

        # Fio inclinado esquerdo (a partir da interseção da linha vertical com a linha horizontal mais baixa)
        bloco.add_line(start=(0, 1.6), end=(-0.5656, 1.0344), dxfattribs={'color': rgb2int(cor_poste)})

        # Fio inclinado direito (a partir da interseção da linha vertical com a linha horizontal mais baixa)
        bloco.add_line(start=(0, 1.6), end=(0.5656, 1.0344), dxfattribs={'color': rgb2int(cor_poste)})

        return nome_bloco

    def criar_bloco_arvore(self, doc, nome_bloco, cores):
        bloco = doc.blocks.new(name=nome_bloco)
        
        # Define as cores
        cor_copa = cores.get('cor_copa', (34, 139, 34))  # Cor padrão verde escuro para a copa
        cor_tronco = cores.get('cor_tronco', (139, 69, 19))  # Cor padrão marrom para o tronco

        # Adiciona as elipses para representar a copa da árvore
        # Primeira elipse
        bloco.add_ellipse(center=(0, 1), major_axis=(0.4, 0), ratio=0.6, start_param=0, end_param=2 * math.pi, dxfattribs={'color': rgb2int(cor_copa)})

        # Segunda elipse, rotacionada
        bloco.add_ellipse(center=(0.2, 0.8), major_axis=(0.3, 0), ratio=0.7, start_param=0, end_param=2 * math.pi, dxfattribs={'color': rgb2int(cor_copa)})

        # Terceira elipse, também rotacionada
        bloco.add_ellipse(center=(-0.2, 0.8), major_axis=(0.3, 0), ratio=0.7, start_param=0, end_param=2 * math.pi, dxfattribs={'color': rgb2int(cor_copa)})

        # Adiciona uma linha para representar o tronco da árvore
        bloco.add_line(start=(0, 0), end=(0, 0.6), dxfattribs={'color': rgb2int(cor_tronco)})

        return nome_bloco

    def criar_bloco_circulo_com_linhas(self, doc, nome_bloco, cores, linhas):
        bloco = doc.blocks.new(name=nome_bloco)
        cor_bloco = cores.get(nome_bloco, (255, 0, 0))  # Cor padrão vermelha
        cor_int = rgb2int(cor_bloco)

        # Adiciona um círculo ao bloco
        bloco.add_circle(center=(0, 0), radius=0.5, dxfattribs={'color': cor_int})

        # Adiciona linhas específicas ao bloco
        for linha in linhas:
            bloco.add_line(start=linha[0], end=linha[1], dxfattribs={'color': cor_int})

        return nome_bloco

    def criar_bloco_circulo_com_ponto(self, doc, nome_bloco, cores):
        bloco = doc.blocks.new(name=nome_bloco)
        cor_bloco = cores.get(nome_bloco, (255, 0, 0))  # Cor padrão vermelha
        cor_int = rgb2int(cor_bloco)

        # Adiciona um círculo ao bloco
        bloco.add_circle(center=(0, 0), radius=0.5, dxfattribs={'color': cor_int})

        # Adiciona um ponto no centro
        bloco.add_point((0, 0), dxfattribs={'color': cor_int})

        return nome_bloco

    def getCampoEscolhido(self):
        """
        Retorna o campo atualmente selecionado no comboBox.
        
        Funcionalidades:
        - Recupera o texto do campo selecionado no comboBox.

        Retorna:
        - str: O texto do campo atualmente selecionado no comboBox.
        """
        return self.comboBox.currentText()  # Retorna o texto do campo selecionado no comboBox

    def getSelecoes(self):
        """
        Retorna um conjunto com os valores dos atributos selecionados pelo usuário.
        A função realiza as seguintes etapas:

        1. Cria um conjunto vazio para armazenar as seleções.
        2. Itera sobre todos os itens no QListWidget.
        3. Para cada item, obtém o widget associado e encontra o QCheckBox.
        4. Se o QCheckBox estiver marcado, adiciona o texto do item ao conjunto de seleções.
        5. Retorna o conjunto de seleções.

        Funcionalidades:
        - Recuperação dos valores dos atributos selecionados pelo usuário no QListWidget.

        Retorna:
        - set: Conjunto com os valores dos atributos selecionados.
        """
        selecoes = set()  # Cria um conjunto vazio para armazenar as seleções
        for i in range(self.listWidget.count()):  # Itera sobre todos os itens no QListWidget
            item = self.listWidget.item(i)
            widget = self.listWidget.itemWidget(item)
            checkbox = widget.findChild(QCheckBox)  # Encontra o QCheckBox no widget do item
            if checkbox.isChecked():  # Verifica se o QCheckBox está marcado
                selecoes.add(item.text())  # Adiciona o valor do atributo ao conjunto
        return selecoes  # Retorna o conjunto de seleções

    def getCamposSelecionados(self):
        """
        Retorna uma lista com os nomes dos campos selecionados pelo usuário.
        A função realiza as seguintes etapas:

        1. Cria uma lista vazia para armazenar os campos selecionados.
        2. Verifica se o objeto possui o atributo 'camposCheckBoxes'.
        3. Itera sobre os itens no dicionário 'camposCheckBoxes'.
        4. Para cada campo, verifica se o checkbox está marcado.
        5. Se o checkbox estiver marcado, adiciona o nome do campo à lista de campos selecionados.
        6. Retorna a lista de campos selecionados.

        Funcionalidades:
        - Recuperação dos nomes dos campos selecionados pelo usuário.

        Retorna:
        - list: Lista com os nomes dos campos selecionados.
        """
        camposSelecionados = []  # Cria uma lista vazia para armazenar os campos selecionados
        if hasattr(self, 'camposCheckBoxes'):  # Verifica se o objeto possui o atributo 'camposCheckBoxes'
            for campo, checkbox in self.camposCheckBoxes.items():  # Itera sobre os itens no dicionário 'camposCheckBoxes'
                if checkbox.isChecked():  # Verifica se o checkbox está marcado
                    camposSelecionados.append(campo)  # Adiciona o nome do campo à lista de campos selecionados
        return camposSelecionados  # Retorna a lista de campos selecionados

    def getCampoZ(self):
        """
        Retorna "__GEOM_Z__" se 'Altimetria da Camada' estiver marcado,
        senão o nome do campo numérico selecionado (ou None).
        """
        if hasattr(self, "cbAltimetriaCamada") and self.cbAltimetriaCamada.isChecked():
            return "__GEOM_Z__"
        selecionado = self.radioGroup.checkedButton()
        return selecionado.text() if selecionado else None

    def getBlocoSelecionado(self):
        """
        Retorna um dicionário com os valores dos atributos e os blocos selecionados pelo usuário.
        A função realiza as seguintes etapas:

        1. Cria um dicionário vazio para armazenar as seleções de blocos.
        2. Itera sobre todos os itens no QListWidget.
        3. Para cada item, obtém o valor do atributo e o widget associado.
        4. Encontra o QComboBox no widget do item.
        5. Se o QComboBox existir, adiciona o valor do atributo e o texto do bloco selecionado ao dicionário.
        6. Retorna o dicionário de seleções de blocos.

        Funcionalidades:
        - Recuperação dos blocos selecionados pelo usuário para cada valor de atributo.

        Retorna:
        - dict: Dicionário com os valores dos atributos como chaves e os blocos selecionados como valores.
        """
        blocoSelecoes = {}  # Cria um dicionário vazio para armazenar as seleções de blocos
        for i in range(self.listWidget.count()):  # Itera sobre todos os itens no QListWidget
            item = self.listWidget.item(i)
            valor = item.text()  # Obtém o valor do atributo
            widget = self.listWidget.itemWidget(item)
            combo = widget.findChild(QComboBox)  # Encontra o QComboBox no widget do item
            if combo:
                blocoSelecoes[valor] = (combo.currentData(Qt.ItemDataRole.UserRole)
                    or combo.currentText()) # Adiciona o valor do atributo e o texto do bloco selecionado ao dicionário
        return blocoSelecoes  # Retorna o dicionário de seleções de blocos

class IconFieldSelectionDialog(QDialog):
    icon_cache = {}  # Dicionário de cache de ícones como atributo da classe
    # Atributos de classe para armazenar os URLs
    ultimoTextoUrl = ""
    ultimoTextoUrl2 = ""
    def __init__(self, layer, parent=None):
        """
        Inicializa o diálogo de seleção de campo e ícone.

        Parâmetros:
        - layer: A camada para a qual os campos e ícones serão selecionados.
        - parent: O widget pai do diálogo.
        """
        super(IconFieldSelectionDialog, self).__init__(parent)
        self.setWindowTitle(self.tr("Escolher Campo e Ícone"))

        self.setMinimumWidth(300)  # Define a largura mínima do diálogo
        self.setMaximumWidth(300)  # Define a largura máxima do diálogo

        self.layer = layer # Armazena a camada GIS
        self.selected_icon_url = None # URL do ícone selecionado
        self.selected_field = None # Campo selecionado

        try:
            from qgis.core import QgsNetworkAccessManager
            self.network_manager = QgsNetworkAccessManager.instance()
        except Exception:
            self.network_manager = QNetworkAccessManager(self)

        layout = QVBoxLayout(self) # Layout vertical principal do diálogo

        # Parte para escolha do campo e CheckBox
        field_layout = QHBoxLayout()

        field_layout.addWidget(QLabel(self.tr("Campo de identificação:")))
        self.combo_box = QComboBox()
        for field in self.layer.fields():
            self.combo_box.addItem(field.name())
        field_layout.addWidget(self.combo_box)

        self.check_box = QCheckBox(self.tr("Rótulos"))
        self.check_box.setChecked(True)
        field_layout.addWidget(self.check_box)

        layout.addLayout(field_layout)

        # Frame de configurações
        frame_rotulos = QFrame()
        frame_rotulos.setFrameShape(QFrame.Shape.Box)
        frame_rotulos.setFrameShadow(QFrame.Shadow.Sunken)
        frame_rotulos.setLineWidth(1)

        frame_rotulos_layout = QGridLayout(frame_rotulos)

        # Margens e espaçamentos menores para aproveitar melhor a largura do frame
        frame_rotulos_layout.setContentsMargins(6, 5, 6, 5)
        frame_rotulos_layout.setHorizontalSpacing(6)
        frame_rotulos_layout.setVerticalSpacing(5)

        # A primeira coluna absorve o espaço restante
        frame_rotulos_layout.setColumnStretch(0, 1)
        frame_rotulos_layout.setColumnStretch(1, 0)
        frame_rotulos_layout.setColumnStretch(2, 0)

        # Larguras padronizadas das colunas de controles
        largura_coluna_1 = 50
        largura_coluna_2 = 50
        altura_controle = 20

        # Valores iniciais
        cor_inicial_rotulo = self._obter_cor_rotulo_inicial()

        # Linha 1: cor e tamanho dos rótulos
        label_estilo_rotulo = QLabel(self.tr("Cor e Tamanho dos Rótulos:"))
        label_estilo_rotulo.setSizePolicy(QSizePolicy.Policy.Expanding, QSizePolicy.Policy.Preferred)

        frame_rotulos_layout.addWidget(label_estilo_rotulo, 0, 0)

        self.buttonCorRotulo = QPushButton(self.tr("Cor"))

        # Botão Cor
        self.buttonCorRotulo.setFixedSize(
            largura_coluna_1,
            altura_controle)

        self._atualizar_cor_botao(self.buttonCorRotulo, cor_inicial_rotulo)

        self.buttonCorRotulo.clicked.connect(
            self.escolher_cor_rotulo)

        frame_rotulos_layout.addWidget(self.buttonCorRotulo, 0, 1, Qt.AlignmentFlag.AlignCenter)

        # Tamanho do rótulo no Google Earth
        self.doubleSpinBoxTamanhoRotulo = QDoubleSpinBox()
        self.doubleSpinBoxTamanhoRotulo.setDecimals(1)
        self.doubleSpinBoxTamanhoRotulo.setMinimum(0.1)
        self.doubleSpinBoxTamanhoRotulo.setMaximum(10.0)
        self.doubleSpinBoxTamanhoRotulo.setSingleStep(0.1)

        # Tamanho do rótulo
        self.doubleSpinBoxTamanhoRotulo.setFixedSize(largura_coluna_2, altura_controle)

        # Tamanho 10 no QGIS corresponde à escala 1.0 no Google Earth
        tamanho_rotulo_qgis = self._obter_tamanho_rotulo_inicial()

        escala_rotulo_inicial = tamanho_rotulo_qgis / 10.0
        escala_rotulo_inicial = max(0.1, min(10.0, escala_rotulo_inicial))

        self.doubleSpinBoxTamanhoRotulo.setValue(escala_rotulo_inicial)

        frame_rotulos_layout.addWidget(self.doubleSpinBoxTamanhoRotulo, 0, 2, Qt.AlignmentFlag.AlignCenter)

        # Linha 2: tamanho do ícone e transparência
        label_estilo_icone = QLabel(self.tr("Ícone e Transparência:"))
        label_estilo_icone.setSizePolicy(QSizePolicy.Policy.Expanding, QSizePolicy.Policy.Preferred)

        frame_rotulos_layout.addWidget(label_estilo_icone, 1, 0)

        self.doubleSpinBoxTamanhoIcone = QDoubleSpinBox()
        self.doubleSpinBoxTamanhoIcone.setDecimals(1)
        self.doubleSpinBoxTamanhoIcone.setMinimum(0.1)
        self.doubleSpinBoxTamanhoIcone.setMaximum(20.0)
        self.doubleSpinBoxTamanhoIcone.setSingleStep(0.1)
        self.doubleSpinBoxTamanhoIcone.setValue(1.0)

        # Tamanho do ícone
        self.doubleSpinBoxTamanhoIcone.setFixedSize(
            largura_coluna_1,
            altura_controle)

        frame_rotulos_layout.addWidget(self.doubleSpinBoxTamanhoIcone, 1, 1, Qt.AlignmentFlag.AlignCenter)

        self.doubleSpinBoxTransparencia = QDoubleSpinBox()
        self.doubleSpinBoxTransparencia.setDecimals(1)
        self.doubleSpinBoxTransparencia.setMinimum(0.0)
        self.doubleSpinBoxTransparencia.setMaximum(100.0)
        self.doubleSpinBoxTransparencia.setSingleStep(5.0)
        self.doubleSpinBoxTransparencia.setSuffix(" %")
        self.doubleSpinBoxTransparencia.setValue(self._obter_transparencia_icone_inicial())

        # Transparência
        self.doubleSpinBoxTransparencia.setFixedSize(
            largura_coluna_2,
            altura_controle)

        frame_rotulos_layout.addWidget(
            self.doubleSpinBoxTransparencia,
            1,
            2,
            Qt.AlignmentFlag.AlignCenter)

        frame_rotulos_layout.addWidget(self.doubleSpinBoxTransparencia, 1, 2)

        layout.addWidget(frame_rotulos)

        # Atualiza estados conforme checkbox
        self.check_box.toggled.connect(self.atualizar_estado_rotulos)
        self.atualizar_estado_rotulos()

        # Parte para escolha do ícone
        layout.addWidget(QLabel(self.tr("Selecione um ícone:")))
        self.list_widget = QListWidget()
        self.list_widget.setIconSize(QSize(30, 30))  # Ajusta o tamanho do ícone
        self.list_widget.setViewMode(QListView.ViewMode.IconMode)  # Exibe os itens em modo de ícone
        self.list_widget.setSpacing(5)  # Adiciona espaço entre os ícones
        self.list_widget.setSelectionMode(QAbstractItemView.SelectionMode.SingleSelection)  # Modo de seleção única
        self.list_widget.setDragEnabled(False)  # Desativa o arrastar-e-soltar

        # Limita a largura do QListWidget para forçar os ícones a se organizarem em múltiplas linhas
        self.list_widget.setMaximumWidth(280)  # Ajuste este valor conforme necessário

        # Configura a folha de estilos para alterar a aparência dos itens selecionados
        self.list_widget.setStyleSheet("""
        QListWidget::item:selected {
            border: 2px solid #0563c1;
            background-color: #d8eaff;
        }
        QListWidget::item:hover {
            background-color: #b8daff;
        }
        """)
        self.setup_icon_list() # Configura a lista de ícones
        layout.addWidget(self.list_widget) # Adiciona o QListWidget ao layout principal

        # Adicione um atributo para rastrear o item anteriormente selecionado
        self.previous_selected_item = None  
        # Conecte o sinal itemClicked ao slot que irá desselecionar o ícone se ele já estiver selecionado
        self.list_widget.itemClicked.connect(self.toggle_icon_selection)

        self.list_widget.setResizeMode(QListView.ResizeMode.Adjust)
        self.list_widget.setGridSize(QSize(42, 42))

        # Criação do QFrame para conter os campos de URL
        frame = QFrame()
        frame.setFrameShape(QFrame.Shape.Box)  # Define a forma do frame como uma caixa
        frame.setFrameShadow(QFrame.Shadow.Raised)  # Define o estilo Raised
        frame.setLineWidth(1)  # Define a largura da borda

        # Layout para o QFrame
        frame_layout = QVBoxLayout(frame)

        # Primeiro QLineEdit e QPushButton para o URL da imagem
        self.labelImageUrl = QLabel(self.tr("URL da Imagem para a Tabela:"))
        frame_layout.addWidget(self.labelImageUrl)

        urlLayout1 = QHBoxLayout()
        self.lineEditImageUrl = QLineEdit()
        self.lineEditImageUrl.setPlaceholderText(self.tr("Colar o URL da IMG para a Tabela: Opcional"))
        self.lineEditImageUrl.setClearButtonEnabled(True)  # Habilita o botão de limpeza
        self.btnAbrirImagem = QPushButton(self.tr("Colar"))
        self.btnAbrirImagem.setMaximumWidth(35)
        urlLayout1.addWidget(self.lineEditImageUrl)
        urlLayout1.addWidget(self.btnAbrirImagem)

        frame_layout.addLayout(urlLayout1)   # Adiciona layout de URL da imagem ao layout do frame

        self.btnAbrirImagem.clicked.connect(self.colarTexto) # Conecta botão para colar texto

        # Segundo QLineEdit e QPushButton para o URL da imagem
        self.labelImageUrl2 = QLabel(self.tr("URL para ScreenOverlay:"))
        frame_layout.addWidget(self.labelImageUrl2)

        urlLayout2 = QHBoxLayout()
        self.lineEditImageUrl2 = QLineEdit()
        self.lineEditImageUrl2.setPlaceholderText(self.tr("Colar o URL para o ScreenOverlay: Opcional"))
        self.lineEditImageUrl2.setClearButtonEnabled(True)  # Habilita o botão de limpeza
        self.btnAbrirImagem2 = QPushButton(self.tr("Colar"))
        self.btnAbrirImagem2.setMaximumWidth(35)
        urlLayout2.addWidget(self.lineEditImageUrl2)
        urlLayout2.addWidget(self.btnAbrirImagem2)
        frame_layout.addLayout(urlLayout2)

        self.btnAbrirImagem2.clicked.connect(self.colarTexto2)

        # Setar o texto dos QLineEdit com os últimos valores usados
        self.lineEditImageUrl.setText(self.ultimoTextoUrl)
        self.lineEditImageUrl2.setText(self.ultimoTextoUrl2)

        # Conecta o sinal textChanged a um novo método para lidar com a atualização do texto
        self.lineEditImageUrl.textChanged.connect(self.verificarTexto)
        self.lineEditImageUrl2.textChanged.connect(self.verificarTexto2)

        layout.addWidget(frame)  # Adiciona o QFrame ao layout principal

        # Botões de Exportar e Cancelar
        buttons_layout = QHBoxLayout()
        self.button_ok = QPushButton(self.tr("Exportar"))
        self.button_ok.clicked.connect(self.accept)
        buttons_layout.addWidget(self.button_ok)

        button_cancel = QPushButton(self.tr("Cancelar"))
        button_cancel.clicked.connect(self.reject)
        buttons_layout.addWidget(button_cancel)

        # Conecta a mudança de índice do ComboBox ao método validate_ok_button_state
        self.combo_box.currentIndexChanged.connect(self.validate_ok_button_state)

        # Conecta a mudança de estado do CheckBox ao método validate_ok_button_state
        self.check_box.stateChanged.connect(self.validate_ok_button_state)
        # Conecta a mudança de seleção do QListWidget ao método validate_ok_button_state
        self.list_widget.itemSelectionChanged.connect(self.validate_ok_button_state)

        layout.addLayout(buttons_layout) # Adiciona o layout dos botões ao layout principal

        self.validate_ok_button_state() # Valida o estado inicial do botão OK

    def _atualizar_cor_botao(self, botao, cor: QColor):
        if cor is None or not cor.isValid():
            cor = QColor("white")

        self._cor_rotulo_escolhida = QColor(cor)

        botao.setStyleSheet("QPushButton {{ background-color: {}; }}".format(cor.name()))

    def _obter_cor_rotulo_inicial(self) -> QColor:
        """
        Obtém a cor inicial do rótulo da camada.
        Se houver indicação de cor variável/data-defined, retorna branco.
        """
        try:
            if not self.layer or not self.layer.labelsEnabled():
                return QColor("white")

            labeling = self.layer.labeling()
            if not labeling:
                return QColor("white")

            settings = labeling.settings()

            # Se houver propriedades data-defined ativas, assume "variada"
            try:
                ddp = settings.dataDefinedProperties()
                if ddp and ddp.hasActiveProperties():
                    return QColor("white")
            except Exception:
                pass  # nosec B110

            fmt = settings.format()
            cor = fmt.color()
            if cor and cor.isValid():
                return cor

        except Exception:
            pass  # nosec B110

        return QColor("white")

    def _obter_tamanho_rotulo_inicial(self) -> float:
        """
        Obtém o tamanho atual do rótulo da camada.
        """
        try:
            if self.layer and self.layer.labelsEnabled() and self.layer.labeling():
                fmt = self.layer.labeling().settings().format()
                valor = float(fmt.size())
                if valor > 0:
                    return valor
        except Exception:
            pass  # nosec B110

        return 10.0

    def _obter_transparencia_icone_inicial(self) -> float:
        """
        Obtém a transparência inicial do símbolo da camada, em %.
        0 = opaco
        100 = transparente
        """
        try:
            renderer = self.layer.renderer()
            if renderer and renderer.type() == 'singleSymbol':
                symbol = renderer.symbol()
                if symbol:
                    try:
                        opacidade = float(symbol.opacity())  # 0..1
                    except Exception:
                        opacidade = 1.0
                    transparencia = (1.0 - opacidade) * 100.0
                    return max(0.0, min(100.0, transparencia))
        except Exception:
            pass  # nosec B110

        return 0.0

    def escolher_cor_rotulo(self):
        cor_atual = getattr(self, "_cor_rotulo_escolhida", QColor("white"))
        cor = QColorDialog.getColor(cor_atual, self, self.tr("Escolher cor do rótulo"))
        if cor.isValid():
            self._atualizar_cor_botao(self.buttonCorRotulo, cor)

    def atualizar_estado_rotulos(self):
        """
        Se o checkbox de rótulos estiver desmarcado:
        - botão Cor desabilita
        - tamanho do rótulo desabilita
        - transparência vai para 0
        - itens da imagem da tabela desabilitam
        """
        ativo = self.check_box.isChecked()

        self.buttonCorRotulo.setEnabled(ativo)
        self.doubleSpinBoxTamanhoRotulo.setEnabled(ativo)

        # Itens da imagem da tabela
        try:
            self.labelImageUrl.setEnabled(ativo)
            self.lineEditImageUrl.setEnabled(ativo)
            self.btnAbrirImagem.setEnabled(ativo)
        except Exception:
            pass  # nosec B110

        if not ativo:
            self.doubleSpinBoxTransparencia.setValue(0.0)

    def _fator_escala_rotulo_kml(self) -> float:
        """
        Retorna diretamente a escala escolhida para o Google Earth.

        Exemplos:
        1.0 = tamanho normal
        1.5 = 50% maior
        0.8 = 20% menor
        """
        try:
            return max(0.0, float(self.doubleSpinBoxTamanhoRotulo.value()))
        except Exception:
            return 1.0

    def verificarValidadeURL(self, url):
        """
        Verifica se a string fornecida é uma URL válida usando uma expressão regular.

        Parâmetros:
        - url (str): A URL a ser validada.

        Funcionalidades:
        - Compila uma expressão regular que valida URLs de forma abrangente, cobrindo protocolos, domínios, IPs, portas, caminhos, query strings e fragmentos.
        - Verifica se a URL fornecida corresponde à expressão regular.

        Retorno:
        - Retorna True se a URL for válida, False caso contrário.

        Utilização:
        - Utilizada para garantir que as URLs inseridas para imagens ou links em campos de URL sejam válidas antes de serem utilizadas para evitar erros na aplicação ou na visualização do KML.
        """
        # Expressão regular atualizada para validar URLs de forma mais abrangente.
        padrao_url = re.compile(
            r'^(https?:\/\/)?'  # http:// ou https://
            r'((([a-z\d]([a-z\d-]*[a-z\d])*)\.)+[a-z]{2,}|'  # domínio
            r'((\d{1,3}\.){3}\d{1,3}))'  # ou ip
            r'(\:\d+)?(\/[-a-z\d%_.~+]*)*'  # porta e caminho
            r'(\?[;&a-z\d%_.~+=-]*)?'  # query string
            r'(\#[-a-z\d_]*)?$', re.IGNORECASE)  # fragmento
        return re.match(padrao_url, url) is not None

    def colarTexto(self):
        """
        Obtém o texto do clipboard e insere no campo QLineEdit destinado ao URL da imagem, 
        se o texto for uma URL válida.

        Funcionalidades:
        - Acessa o conteúdo do clipboard do sistema.
        - Verifica se o texto é uma URL válida.
        - Insere a URL válida no campo de texto se for válida.

        Utilização:
        - Usado para facilitar a inserção de URLs por meio do uso de clipboard, evitando a necessidade de digitação manual, 
          aumentando a eficiência do usuário e reduzindo a chance de erro de entrada.
        """
        # Acessa o clipboard do sistema
        clipboard = QGuiApplication.clipboard() # Obtém o objeto clipboard do sistema
        texto = clipboard.text() # Lê o texto atualmente armazenado no clipboard
        
        # Verifica se o texto copiado é uma URL válida
        if self.verificarValidadeURL(texto): # Chama o método para verificar a validade da URL
            self.lineEditImageUrl.setText(texto) # Insere o texto no QLineEdit se for uma URL válida

    def colarTexto2(self):
        """
        Obtém o texto do clipboard e insere no campo QLineEdit destinado ao URL para ScreenOverlay,
        se o texto for uma URL válida.

        Funcionalidades:
        - Acessa o conteúdo do clipboard do sistema.
        - Verifica se o texto é uma URL válida.
        - Insere a URL válida no campo de texto destinado ao ScreenOverlay se for válida.

        Utilização:
        - Usado para facilitar a inserção de URLs de ScreenOverlay por meio do uso de clipboard, 
          evitando a necessidade de digitação manual e melhorando a eficiência do usuário.
        """
        # Acessa o clipboard do sistema
        clipboard = QGuiApplication.clipboard() # Obtém o objeto clipboard do sistema
        texto = clipboard.text() # Lê o texto atualmente armazenado no clipboard

        # Verifica se o texto copiado é uma URL válida
        if self.verificarValidadeURL(texto): # Chama o método para verificar a validade da URL
            self.lineEditImageUrl2.setText(texto) # Insere o texto no QLineEdit destinado ao ScreenOverlay se for uma URL válida

    def verificarValidadeURLImagem(self, url):
        """
        Verifica se a URL fornecida termina com uma extensão de arquivo de imagem aceitável. 
        Este método é usado para garantir que URLs inseridas para imagens sejam de formatos compatíveis para visualização.

        Parâmetros:
        - url (str): A URL da imagem a ser validada.

        Funcionalidades:
        - Define uma lista de extensões de arquivo de imagem que são aceitáveis.
        - Verifica se a URL fornecida termina com uma dessas extensões.

        Retorno:
        - Retorna True se a URL terminar com uma extensão de arquivo de imagem válida, False caso contrário.

        Utilização:
        - Utilizada para validar URLs de imagens, assegurando que os links fornecidos apontem para arquivos de imagem reais que podem ser carregados e exibidos corretamente no KML.
        """
        # Define as extensões de arquivo de imagem que são aceitáveis
        extensoes_validas = ['.jpg', '.jpeg', '.png', '.gif', '.bmp', '.tif', '.tiff', '.webp']
        # Verifica se a URL termina com alguma das extensões válidas
        return any(url.lower().endswith(ext) for ext in extensoes_validas) # Verifica se a URL corresponde a uma extensão válida

    def verificarTexto(self):
        """
        Verifica o conteúdo do campo de entrada para URL da imagem, ajusta a cor do texto baseada na validade da URL
        e atualiza o último texto de URL válido armazenado. Este método é usado para fornecer feedback visual imediato 
        sobre a validade da URL inserida.

        Funcionalidades:
        - Obtém o texto atual do campo QLineEdit destinado à URL da imagem.
        - Verifica se o texto é uma URL válida e se corresponde a uma extensão de arquivo de imagem aceitável.
        - Atualiza o armazenamento do último texto válido ou o limpa se o texto atual não for válido.
        - Altera a cor do texto do QLineEdit para azul se a URL for válida, para vermelho se for inválida, e retorna para a cor padrão se o campo estiver vazio.

        Utilização:
        - Essencial para fornecer uma resposta visual instantânea ao usuário sobre a validade da URL inserida, 
          facilitando a correção de erros e garantindo que apenas URLs válidas sejam utilizadas.
        """
        # Obtém o texto atual do QLineEdit
        texto = self.lineEditImageUrl.text() # Lê o texto da caixa de entrada de URL da imagem
        
        # Verifica a validade da URL e se a URL é uma imagem
        if self.verificarValidadeURL(texto) and self.verificarValidadeURLImagem(texto):
            IconFieldSelectionDialog.ultimoTextoUrl = texto # Atualiza o último texto válido se a URL for válida
            self.lineEditImageUrl.setStyleSheet("QLineEdit { color: blue; }") # Muda a cor do texto para azul
        else:
            IconFieldSelectionDialog.ultimoTextoUrl = "" # Limpa o último texto válido se a URL for inválida
            if texto.strip() != "": # Verifica se o campo não está vazio
                self.lineEditImageUrl.setStyleSheet("QLineEdit { color: red; }") # Muda a cor do texto para vermelho se houver texto inválido
            else:
                self.lineEditImageUrl.setStyleSheet("") # Retorna a cor do texto para o padrão se o campo estiver vazio

    def verificarTexto2(self):
        """
        Verifica o conteúdo do campo de entrada para o URL do ScreenOverlay, ajusta a cor do texto baseada na validade da URL,
        e atualiza o último texto de URL válido armazenado. Este método é usado para fornecer feedback visual imediato 
        sobre a validade da URL inserida.

        Funcionalidades:
        - Obtém o texto atual do campo QLineEdit destinado ao URL do ScreenOverlay.
        - Verifica se o texto é uma URL válida e se corresponde a uma extensão de arquivo de imagem aceitável.
        - Atualiza o armazenamento do último texto válido ou o limpa se o texto atual não for válido.
        - Altera a cor do texto do QLineEdit para azul se a URL for válida, para vermelho se for inválida, e retorna para a cor padrão se o campo estiver vazio.

        Utilização:
        - Essencial para fornecer uma resposta visual instantânea ao usuário sobre a validade da URL inserida para o ScreenOverlay,
          facilitando a correção de erros e garantindo que apenas URLs válidas sejam utilizadas para o ScreenOverlay.
        """
        # Obtém o texto atual do QLineEdit destinado ao URL do ScreenOverlay
        texto = self.lineEditImageUrl2.text()  # Lê o texto da caixa de entrada de URL para o ScreenOverlay

        # Verifica a validade da URL e se a URL é uma imagem
        if self.verificarValidadeURL(texto) and self.verificarValidadeURLImagem(texto):
            IconFieldSelectionDialog.ultimoTextoUrl2 = texto # Atualiza o último texto válido se a URL for válida
            self.lineEditImageUrl2.setStyleSheet("QLineEdit { color: blue; }") # Muda a cor do texto para azul
        else:
            IconFieldSelectionDialog.ultimoTextoUrl2 = "" # Limpa o último texto válido se a URL for inválida
            if texto.strip() != "": # Verifica se o campo não está vazio
                self.lineEditImageUrl2.setStyleSheet("QLineEdit { color: red; }") # Muda a cor do texto para vermelho se houver texto inválido
            else:
                self.lineEditImageUrl2.setStyleSheet("") # Retorna a cor do texto para o padrão se o campo estiver vazio

    def toggle_icon_selection(self, item):
        """
        Alterna a seleção de um ícone na lista de ícones. Se o ícone já estiver selecionado,
        ele será desmarcado. Caso contrário, ele será selecionado.

        Ações executadas pela função:
        1. Verifica se o item clicado é o mesmo que o item anteriormente selecionado.
        2. Se for o mesmo item, desmarca-o, limpa a URL do ícone selecionado e
           reseta a referência ao item anteriormente selecionado.
        3. Se for um item diferente, seleciona o novo item, atualiza a URL do ícone
           selecionado e a referência ao item anteriormente selecionado.
        4. Valida o estado do botão OK após a alteração na seleção.

        Parâmetros:
        - item: O item clicado na lista de ícones.
        """
        # Verifique se o item clicado já está selecionado
        if self.previous_selected_item == item:
            # Se for o mesmo item que o anteriormente selecionado, deselecione-o
            self.list_widget.clearSelection() # Limpa a seleção na lista de ícones
            self.selected_icon_url = None # Reseta a URL do ícone selecionado
            self.previous_selected_item = None  # Limpa o item anteriormente selecionado
        else:
            # Se for um item diferente, selecione-o e atualize o item anteriormente selecionado
            self.list_widget.setCurrentItem(item)  # Define o item atual na lista de ícones
            self.selected_icon_url = item.data(Qt.ItemDataRole.UserRole) # Obtém a URL do ícone selecionado
            self.previous_selected_item = item  # Atualiza o item anteriormente selecionado

        # Após a alteração na seleção, valide o estado do botão OK
        self.validate_ok_button_state()

    def validate_ok_button_state(self):
        """
        Valida o estado do botão OK no diálogo.

        Ações executadas pela função:
        1. Verifica se algum ícone está selecionado na lista de ícones.
        2. Verifica se o checkbox está marcado.
        3. Verifica se o ComboBox não está vazio.
        4. Habilita o botão OK apenas se:
           - Algum ícone estiver selecionado OU o checkbox estiver marcado,
           E
           - O ComboBox não estiver vazio.

        Linhas de código explicadas:
        """
        # Verifica se algum ícone está selecionado
        has_icon_selected = any(item.isSelected() for item in self.list_widget.selectedItems())
        # Verifica se o checkbox está marcado
        is_checkbox_checked = self.check_box.isChecked()
        # Verifica se o QComboBox não está vazio
        is_combobox_not_empty = self.combo_box.count() > 0

        # O botão "OK" só será habilitado se houver ícones selecionados OU o checkbox estiver marcado,
        # E o QComboBox não estiver vazio.
        self.button_ok.setEnabled((is_checkbox_checked or has_icon_selected) and is_combobox_not_empty)

    def setup_icon_list(self):
        """
        Configura a lista de ícones no diálogo.

        Ações executadas pela função:
        1. Define uma lista de URLs de ícones a serem baixados.
        2. Itera sobre cada URL na lista.
        3. Chama a função `download_icon` para cada URL para baixar e exibir o ícone na lista de ícones (`QListWidget`).

        Linhas de código explicadas:
        """
        # Define uma lista de URLs de ícones a serem baixados
        icon_urls = [
            "https://maps.google.com/mapfiles/kml/shapes/man.png",
            "http://maps.google.com/mapfiles/kml/shapes/woman.png",
            "http://maps.google.com/mapfiles/kml/shapes/wheel_chair_accessible.png",
            "https://maps.google.com/mapfiles/kml/shapes/arrow.png", "https://maps.google.com/mapfiles/kml/paddle/wht-blank.png",
            "https://maps.google.com/mapfiles/kml/paddle/wht-circle.png",
            "https://maps.google.com/mapfiles/kml/paddle/wht-diamond.png",
            "https://maps.google.com/mapfiles/kml/paddle/wht-square.png", "https://maps.google.com/mapfiles/kml/paddle/wht-stars.png", "https://maps.google.com/mapfiles/kml/shapes/triangle.png",
            "https://maps.google.com/mapfiles/kml/shapes/info-i.png",
            "https://maps.google.com/mapfiles/kml/shapes/square.png",
            "https://maps.google.com/mapfiles/kml/shapes/placemark_square.png",
            "http://maps.google.com/mapfiles/kml/pal4/icon57.png",
            "http://maps.google.com/mapfiles/kml/shapes/open-diamond.png",
            "http://maps.google.com/mapfiles/kml/shapes/forbidden.png",
            "http://maps.google.com/mapfiles/kml/pushpin/wht-pushpin.png",
            "https://maps.google.com/mapfiles/kml/shapes/parks.png", "https://maps.google.com/mapfiles/kml/shapes/campground.png",
            "https://maps.google.com/mapfiles/kml/shapes/cabs.png", "https://maps.google.com/mapfiles/kml/shapes/airports.png",
            "https://maps.google.com/mapfiles/kml/shapes/caution.png", 
            "https://maps.google.com/mapfiles/kml/shapes/flag.png",
            "https://maps.google.com/mapfiles/kml/pal5/icon13.png",
            "https://maps.google.com/mapfiles/kml/shapes/picnic.png",
            "https://maps.google.com/mapfiles/kml/shapes/church.png",
            "http://maps.google.com/mapfiles/kml/shapes/rail.png",
            "http://maps.google.com/mapfiles/kml/shapes/hiker.png",
            "http://maps.google.com/mapfiles/kml/shapes/ranger_station.png",
            "https://www.gstatic.com/earth/images/stockicons/190201-2016-animal-paw_4x.png",
            ]

        # Limpa a lista para evitar duplicação ao reabrir o diálogo
        self.list_widget.clear()

        for url in icon_urls:
            # Chama a função download_icon para baixar e exibir o ícone na lista de ícones
            self.download_icon(url)

    def download_icon(self, url):
        """
        Faz o download assíncrono de um ícone a partir de uma URL.

        Funcionalidades:
        - Usa cache em memória para evitar downloads repetidos;
        - Utiliza QNetworkAccessManager sem bloquear a interface;
        - Configura a política de redirecionamento de forma compatível
          com Qt5 e Qt6;
        - Define um User-Agent para reduzir bloqueios por servidores.
        """
        # Usa o ícone armazenado em cache, caso já tenha sido baixado.
        if url in IconFieldSelectionDialog.icon_cache:
            self.add_icon_to_list(url, IconFieldSelectionDialog.icon_cache[url])
            return

        # Cria a requisição para a URL informada.
        req = QNetworkRequest(QUrl(url))

        # Compatibilidade entre enums do Qt5 e Qt6.
        try:
            grupo_atributo = getattr(QNetworkRequest, "Attribute", QNetworkRequest)

            grupo_redirect = getattr(QNetworkRequest, "RedirectPolicy", QNetworkRequest)

            atributo_redirect = getattr(grupo_atributo, "RedirectPolicyAttribute")

            politica_redirect = getattr(grupo_redirect, "NoLessSafeRedirectPolicy")

            req.setAttribute(atributo_redirect, politica_redirect)

        except (AttributeError, TypeError):
            # Algumas versões antigas do Qt podem não disponibilizar
            # essa política de redirecionamento.
            pass  # nosec B110

        # Define um User-Agent para evitar bloqueios em alguns servidores.
        try:
            req.setRawHeader(b"User-Agent", b"Mozilla/5.0")
        except (AttributeError, TypeError):
            pass  # nosec B110

        # Inicia o download assíncrono.
        reply = self.network_manager.get(req)

        # Armazena a URL original no objeto da resposta.
        reply.setProperty("icon_url_original", url)

        # Processa o resultado quando o download terminar.
        reply.finished.connect(self.on_download_finished)

    def on_download_finished(self):
        """
        Callback chamado quando um download de ícone termina.
        """
        reply = self.sender()
        if reply is None:
            return

        try:
            err = reply.error()

            # comparação explícita: não use "if reply.error():"
            if err != QNetworkReply.NetworkError.NoError:
                try:
                    url0 = str(reply.property("icon_url_original") or reply.url().toString())
                    QgsMessageLog.logMessage(self.tr("Falha ao baixar ícone: {url} | erro: {error}").format(url=url0, error=reply.errorString()), "TempoSalvoTools", Qgis.MessageLevel.Warning)

                except Exception:
                    pass  # nosec B110
                return

            url_final = reply.url().toString()
            url_key = str(reply.property("icon_url_original") or url_final)

            data = reply.readAll()
            data_bytes = bytes(data)

            if not data_bytes:
                try:
                    QgsMessageLog.logMessage(self.tr("Resposta vazia ao baixar ícone: {url_key}").format(url_key=url_key), "TempoSalvoTools", Qgis.MessageLevel.Warning)
                except Exception:
                    pass  # nosec B110
                return

            pixmap = QPixmap()
            ok = pixmap.loadFromData(data_bytes)

            if ok and not pixmap.isNull():
                IconFieldSelectionDialog.icon_cache[url_key] = pixmap
                self.add_icon_to_list(url_key, pixmap)
            else:
                try:
                    QgsMessageLog.logMessage(self.tr("Não foi possível decodificar o ícone: {url_key}").format(url_key=url_key), "TempoSalvoTools", Qgis.MessageLevel.Warning)
                except Exception:
                    pass  # nosec B110
        finally:
            reply.deleteLater()

    def add_icon_to_list(self, url, pixmap):
        """
        Adiciona um ícone à lista de ícones no QListWidget.

        Ações executadas pela função:
        1. Cria um objeto QIcon a partir do QPixmap fornecido.
        2. Cria um item de QListWidget sem texto.
        3. Define o ícone do item de lista para o QIcon criado.
        4. Armazena a URL do ícone no item de lista usando Qt.UserRole.
        5. Adiciona o item de lista ao QListWidget.

        Linhas de código explicadas:
        """
        icon = QIcon(pixmap)  # Cria um objeto QIcon a partir do QPixmap fornecido
        item = QListWidgetItem()  # Cria um item de lista sem texto
        item.setIcon(icon)  # Define o ícone do item
        item.setData(Qt.ItemDataRole.UserRole, url)  # Armazena a URL do ícone no item de lista usando Qt.UserRole
        self.list_widget.addItem(item)  # Adiciona o item de lista ao QListWidget

    def accept(self):
        self.selected_field = self.combo_box.currentText()

        current_item = self.list_widget.currentItem()
        if current_item:
            self.selected_icon_url = current_item.data(Qt.ItemDataRole.UserRole)

        self.selected_image_url = self.lineEditImageUrl.text() if self.check_box.isChecked() else ""
        self.selected_image_url2 = self.lineEditImageUrl2.text()

        self.selected_exportar_rotulos = self.check_box.isChecked()
        self.selected_cor_rotulo = getattr(self, "_cor_rotulo_escolhida", QColor("white"))
        self.selected_escala_rotulo = self._fator_escala_rotulo_kml()
        self.selected_escala_icone = self.doubleSpinBoxTamanhoIcone.value()
        self.selected_transparencia_icone = self.doubleSpinBoxTransparencia.value()

        super(IconFieldSelectionDialog, self).accept()

    def get_selections(self):
        """
        Retorna:
        campo, icon_url, image_url, overlay_url,
        exportar_rotulos, cor_rotulo, escala_rotulo, escala_icone, transparencia_icone
        """
        return (
            self.selected_field,
            self.selected_icon_url,
            self.selected_image_url,
            self.selected_image_url2,
            self.selected_exportar_rotulos,
            self.selected_cor_rotulo,
            self.selected_escala_rotulo,
            self.selected_escala_icone,
            self.selected_transparencia_icone)

class CircleDelegate(QStyledItemDelegate):
    """
    Delegate para desenhar um círculo colorido ao lado de cada item em uma lista de itens.
    
    Ações executadas pela função:
    1. Desenha um círculo colorido ao lado do item, com cor e borda configuráveis.
    2. Ajusta a posição do texto do item para não sobrepor o círculo.
    3. Busca a camada no projeto do QGIS usando o ID e tenta obter as cores do símbolo da camada.
    """
    def paint(self, painter, option, index):
        """
        Sobrescreve o método paint para desenhar um círculo ao lado do item.
        
        Parâmetros:
        - painter (QPainter): O objeto de pintura usado para desenhar o item.
        - option (QStyleOptionViewItem): Opções de estilo para o item.
        - index (QModelIndex): Índice do item no modelo.
        """
        super().paint(painter, option, index)

        # Obtém o ID da camada do item do modelo
        layer_id = index.data(Qt.ItemDataRole.UserRole)
        if not layer_id:
            layer_id = index.model().itemFromIndex(index).data()

        # Busca a camada no projeto do QGIS usando o ID
        layer = QgsProject.instance().mapLayer(layer_id)

        # Define as cores padrão para o círculo e a borda
        circle_color = QColor("white")
        border_color = QColor("black")
        border_width = 2  # Definindo a espessura da borda

        # Tenta obter as cores do símbolo da camada, se disponível
        if layer:
            symbols = layer.renderer().symbols(QgsRenderContext())
            if symbols:
                circle_color = symbols[0].color()
                # Verifica se existe um contorno e obtém a cor do contorno
                if symbols[0].symbolLayerCount() > 0:
                    border_layer = symbols[0].symbolLayer(0)
                    if hasattr(border_layer, 'strokeColor'):
                        border_color = border_layer.strokeColor()
 
        # Calcula a posição e o tamanho do círculo
        offset = -15
        radius = 6
        # Assegurando que os valores passados para QRect sejam inteiros
        x = int(option.rect.left() + offset)
        y = int(option.rect.top() + (option.rect.height() - radius * 2) / 2)
        diameter = int(radius * 2)
        circleRect = QRect(x, y, diameter, diameter) # Retângulo que define o círculo

        painter.setBrush(QBrush(circle_color)) # Define a cor de preenchimento e a borda para o círculo
        painter.setPen(QPen(border_color, border_width))  # Configurando a cor e a espessura da borda
        painter.drawEllipse(circleRect) # Desenha o círculo

        # Ajusta a posição do texto no item para não sobrepor o círculo
        option.rect.setLeft(option.rect.left() + offset + radius*2 + 8)