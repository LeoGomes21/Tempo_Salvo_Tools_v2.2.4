from qgis.PyQt.QtWidgets import QInputDialog, QTreeView, QStyledItemDelegate, QColorDialog, QMenu, QLineEdit, QDialog, QVBoxLayout, QLabel, QPushButton, QHBoxLayout, QFileDialog, QComboBox, QFrame, QCheckBox, QDoubleSpinBox, QRadioButton, QButtonGroup, QProgressBar, QDialogButtonBox, QGraphicsView, QListWidget, QScrollBar, QGraphicsEllipseItem, QGraphicsScene, QToolTip, QGraphicsPathItem, QGraphicsRectItem, QGraphicsPolygonItem, QGraphicsLineItem, QGraphicsItemGroup, QMessageBox, QSlider, QAbstractItemView
from qgis.core import QgsProject, QgsMapLayer, QgsWkbTypes, QgsSingleSymbolRenderer, QgsCategorizedSymbolRenderer, QgsSymbol, Qgis, QgsVectorLayerSimpleLabeling, QgsRenderContext, QgsSymbolLayerUtils, QgsCoordinateReferenceSystem, QgsCoordinateTransform, QgsMessageLog, QgsLayerTreeLayer, QgsSymbolLayer, QgsGeometry, QgsVectorFileWriter, QgsVectorLayer, QgsDistanceArea, QgsDefaultValue, QgsEditorWidgetSetup, QgsFields, QgsField, QgsFeature, QgsPointXY, QgsFillSymbol, QgsProperty, QgsPalLayerSettings, QgsMarkerSymbol, QgsMapLayerStyle
from qgis.PyQt.QtGui import QStandardItemModel, QStandardItem, QIcon, QPixmap, QPainter, QColor, QPen, QFont, QBrush, QGuiApplication, QTransform, QCursor, QPainterPath, QPolygonF, QMouseEvent, QWheelEvent, QDesktopServices
from qgis.PyQt.QtCore import Qt, QPoint, QRect, QEvent, QCoreApplication, QSettings, QItemSelectionModel, QPointF, QObject, QVariant, QMetaType, QTimer, QRectF, QUrl
from qgis.gui import QgsProjectionSelectionDialog
from PIL import Image, UnidentifiedImageError
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
from ezdxf.colors import aci2rgb
from ezdxf import colors
from io import BytesIO
import xlsxwriter
import processing
import requests
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
from .criar_poligonos import CamadaPoligonosManager

class UiManagerP:
    """
    Gerencia a interface do usuário, interagindo com um QTreeView para listar e gerenciar camadas de polígonos no QGIS.
    """
    def __init__(self, iface, dialog, plugin):
        """
        Inicializa a instância da classe UiManagerP, responsável por gerenciar a interface do usuário
        que interage com um QTreeView para listar e gerenciar camadas de polígonos no QGIS.

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
        self.dlg.treeViewListaPoligono.setModel(self.treeViewModel)

        self._tree_item_changed_connected = False

        # TreeView: tooltip + drag&drop (UMA ÚNICA instalação do filtro)
        tv = self.dlg.treeViewListaPoligono

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

        # Aplica estilos CSS para aprimorar a interação visual com os itens do QTreeView
        self.dlg.treeViewListaPoligono.setStyleSheet("""
            QTreeView::item:hover:!selected {
                background-color: #def2fc;
            }
            QTreeView::item:selected {
            }""")

        # Atualiza a visualização da lista de camadas no QTreeView
        self.atualizar_treeView_lista_poligono()

        self.treeViewModel.itemChanged.connect(self.on_item_changed)
        self._tree_item_changed_connected = True

        # Conecta os sinais do QGIS e da interface do usuário para sincronizar ações e eventos
        self.connect_signals()

        # instancia uma vez só o manager
        self.poligono_manager = CamadaPoligonosManager(self.iface)

        # Controla os ítens da etiqueta
        self.fieldColors = {}  # Armazenará as cores atribuídas aos campos
        self.fieldVisibility = {}  # Armazena a visibilidade dos campos

        # Mantém na memória a última posição  
        self.ultimo_caminho_salvo = ""  # Inicializa a variável para armazenar o último caminho

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

        # Sincroniza o estado das camadas no QGIS com o checkbox do QTreeView sempre que as camadas do mapa mudam
        self.iface.mapCanvas().layersChanged.connect(self.sync_from_qgis_to_treeview)

        # Conecta mudanças na seleção do QTreeView para atualizar a camada ativa no QGIS
        self.dlg.treeViewListaPoligono.selectionModel().selectionChanged.connect(self.on_treeview_selection_changed)

        # Conecta o evento de duplo clique em um item para manipulação de cores da camada
        self.dlg.treeViewListaPoligono.doubleClicked.connect(self.on_item_double_clicked)

        # Garante uma única conexão do checkbox do treeView
        try:
            self.treeViewModel.itemChanged.disconnect(self.on_item_changed)
        except TypeError:
            pass  # nosec B110

        # Sincroniza mudanças vindas da árvore de camadas nativa do QGIS
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

        # Define e aplica um delegado personalizado para customização da exibição de itens no QTreeView
        self.treeViewDelegate = PolygonDelegate(self.dlg.treeViewListaPoligono)
        self.dlg.treeViewListaPoligono.setItemDelegate(self.treeViewDelegate)

        # Configura a política de menu de contexto para permitir menus personalizados em cliques com o botão direito
        self.dlg.treeViewListaPoligono.setContextMenuPolicy(Qt.ContextMenuPolicy.CustomContextMenu)
        self.dlg.treeViewListaPoligono.customContextMenuRequested.connect(self.open_context_menu)

        # Conecta o botão para criar uma camada de polígonos ao método que adiciona a camada e atualiza o treeView
        self.dlg.ButtonCriarPoligono.clicked.connect(self.adicionar_camada_e_atualizar)

        # Conecta o botão ao novo método do botão cria uma camada com o nome
        self.dlg.ButtonCriarPoligonoNome.clicked.connect(self.abrir_caixa_nome_camada)

        # Conecta o botão de exportação DXF a uma função que maneja a exportação de camadas
        self.dlg.pushButtonExportaDXF_P.clicked.connect(self.exportar_para_dxf)

        # Conecta o botão para exportar a camada para KML
        self.dlg.pushButtonExportaKmlP.clicked.connect(self.exportar_para_kml)

        # seleção via mouse (funciona mesmo com 1 Camada de Polígono)
        self.dlg.treeViewListaPoligono.clicked.connect(lambda _: self.on_treeview_selection_changed(None, None))

        self.dlg.treeViewListaPoligono.clicked.connect(self.on_treeview_item_clicked)

        # Sincroniza a seleção no QGIS com a seleção no QTreeView quando a camada ativa no QGIS muda
        self.iface.currentLayerChanged.connect(self.on_current_layer_changed)

        # Inicia a conexão de sinais para tratar a mudança de nome das camadas no projeto
        self.connect_name_changed_signals()

        # Conecta o botão para reprojetar a camada
        self.dlg.pushButtonReprojetarP.clicked.connect(self.abrir_dialogo_crs)

        # Conectando o botão pushButtonFecharP à função que fecha o diálogo
        self.dlg.pushButtonFecharP.clicked.connect(self.dlg.close)

        # Remove outras camadas sem alterar ações de camadas de outros tipos
        QgsProject.instance().layersRemoved.connect(self.on_layers_removed)

        #Diálogo que permite ao usuário selecionar campos da camada atual que serão
        self.dlg.pushButtonCampoP.clicked.connect(self.abrir_dialogo_selecao_campos_poligono)

        # Conecta o botão para Zoom
        self.dlg.pushButtonVisualizarP.clicked.connect(self.visualizar_poligono_selecionada)

        # Conectar o botão de renomear à função de renomear a camada
        self.dlg.pushButtonRenomeP.clicked.connect(self.renomear_camada_selecionada)

        # Conectar o botão de deletar à função de remover a camada
        self.dlg.pushButtonDelP.clicked.connect(self.remover_camada_selecionada)

        # Conectar o botão 'salvar como' à função 'salvar_camada_multiplo' para salvar em múltiplos formatos
        self.dlg.pushButtonSalvaMultiplosP.clicked.connect(self.salvar_camada_multiplo)

        # Conectar o botão de salvar permanente à função de salvar a camada
        self.dlg.pushButton_PermanenteP.clicked.connect(self.salvar_camada_permanente)

        # Conectar o botão 'pushButtonTabelaP' à função de abrir a tabela de atributos
        self.dlg.pushButtonTabelaP.clicked.connect(self.abrir_tabela_atributos)

        # Conecta o botão para Clocar a Camada de Polígono
        self.dlg.pushButtonClonarPoligono.clicked.connect(self.clone_layer_poligono)

        # Conectando o botão à função pushButtonAbrirP
        self.dlg.pushButtonAbrirP.clicked.connect(self.abrir_adicionar_arquivo_poligono)

    def tr(self, message):
        """
        Traduz textos deste diálogo.
        O contexto precisa ser estável para o Qt Linguist encontrar as traduções.
        """
        return QCoreApplication.translate("UiManagerP", message)

    def atualizar_estado_botoes(self):
        """
        Atualiza o estado (habilitado/desabilitado) dos botões da interface gráfica conforme a presença de camadas no treeView de polígonos.

        Detalhamento do Processo:
        1. Verifica se o modelo associado ao treeViewListaPoligono está vazio, ou seja, sem nenhuma camada listada.
        2. Se o modelo estiver vazio, todos os botões que dependem de camada devem ser desabilitados para evitar operações inválidas.
        3. Caso contrário, os botões são habilitados, permitindo ao usuário interagir normalmente com as funções associadas a uma camada de polígono.
        4. Os botões afetados incluem:
            - Deletar camada (`pushButtonDelP`)
            - Renomear camada (`pushButtonRenomeP`)
            - Tornar camada permanente (`pushButton_PermanenteP`)
            - Salvar em múltiplos formatos (`pushButtonSalvaMultiplosP`)
            - Abrir tabela de atributos (`pushButtonTabelaP`)
            - Gerenciar campos/etiquetas (`pushButtonCampoP`)
            - Exportar para DXF (`pushButtonExportaDXF_P`)
            - Exportar para KML (`pushButtonExportaKmlP`)
            - Visualizar pontos associados (`pushButtonVisualizarP`)
            - Clonar pontos (`pushButtonClonarP`)
            - Reprojetar camada (`pushButtonReprojetarP`)
        5. Garante uma experiência segura e intuitiva, evitando erros por ações em contexto inválido.
        """
        # Verifica se o modelo do treeView está vazio
        modelo_vazio = self.dlg.treeViewListaPoligono.model().rowCount() == 0

        # Atualiza o estado dos botões baseado na presença ou ausência de itens no modelo
        self.dlg.pushButtonDelP.setEnabled(not modelo_vazio)
        self.dlg.pushButtonRenomeP.setEnabled(not modelo_vazio)
        self.dlg.pushButton_PermanenteP.setEnabled(not modelo_vazio)
        self.dlg.pushButtonSalvaMultiplosP.setEnabled(not modelo_vazio)
        self.dlg.pushButtonTabelaP.setEnabled(not modelo_vazio)
        self.dlg.pushButtonCampoP.setEnabled(not modelo_vazio)
        self.dlg.pushButtonExportaDXF_P.setEnabled(not modelo_vazio)
        self.dlg.pushButtonExportaKmlP.setEnabled(not modelo_vazio)
        self.dlg.pushButtonVisualizarP.setEnabled(not modelo_vazio)
        self.dlg.pushButtonClonarPoligono.setEnabled(not modelo_vazio)
        self.dlg.pushButtonReprojetarP.setEnabled(not modelo_vazio)

    def abrir_tabela_atributos(self):
        """
        Abre o Gerenciador de Tabelas para a camada de polígono selecionada no treeView.
        """
        selected_indexes = self.dlg.treeViewListaPoligono.selectedIndexes()
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

        # Abre/reaproveita o diálogo já controlado pelo plugin principal
        self.plugin.run_tabelas()

        dlg_tabelas = getattr(self.plugin, "tabelas_dlg", None)
        if dlg_tabelas is None:
            return

        try:
            # Como este manager é de polígonos, já força o filtro correto
            dlg_tabelas.radioButtonPoligono.setChecked(True)
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
        selected_indexes = self.dlg.treeViewListaPoligono.selectedIndexes()
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
            msg = self.tr("Arquivos salvos com sucesso ({ok}/{total}): {fmt_ok}.").format(ok=len(ok_list), total=total, fmt_ok=fmt_ok)
            self.mostrar_mensagem(msg, "Sucesso", caminho_pasta=diretorio)
        else:
            msg = self.tr("Arquivos salvos ({ok}/{total}).").format(ok=len(ok_list), total=total)
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
            if ok:
                self.mostrar_mensagem(self.tr("Arquivo salvo com sucesso ({ext}).").format(ext=ext.lstrip('.').upper()), "Sucesso", caminho_pasta=os.path.dirname(final_path), caminho_arquivos=final_path)
            else:
                self.mostrar_mensagem(self.tr("Não foi possível salvar ({ext}).").format(ext=ext.lstrip('.').upper()), "Erro")

        return ok

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
        selected_indexes = self.dlg.treeViewListaPoligono.selectedIndexes()
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
            resposta = QMessageBox.question(self.dlg, self.tr("Confirmar Remoção"), self.tr("Existem alterações não salvas. Deseja salvar antes de remover?"), QMessageBox.StandardButton.Yes | QMessageBox.StandardButton.No | QMessageBox.StandardButton.Cancel, QMessageBox.StandardButton.Yes)

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

        self.atualizar_treeView_lista_poligono()
        self.iface.mapCanvas().refresh()

    def salvar_camada(self, layer, fileName, driverName, silencioso=True):
        """
        Salva uma camada vetorial, preservando UTF-8 e a precisão
        dos campos numéricos no Shapefile.
        """
        driver = (driverName or "").upper()

        options = QgsVectorFileWriter.SaveVectorOptions()
        options.driverName = driver
        options.fileEncoding = "UTF-8"
        options.onlySelectedFeatures = False

        lyr_to_write = layer

        # Mantém o conversor em memória durante a exportação.
        conversor_precisao = None

        if driver == "KML":
            try:
                target = QgsCoordinateReferenceSystem("EPSG:4326")

                if layer.crs().authid() != target.authid():
                    resultado = processing.run(
                        "native:reprojectlayer",
                        {"INPUT": layer,
                            "TARGET_CRS": target,
                            "OUTPUT": "memory:"})

                    lyr_to_write = resultado["OUTPUT"]

            except Exception:
                return False

            options.symbologyExport = Qgis.FeatureSymbologyExport.PerFeature

        elif driver == "CSV":
            if (lyr_to_write.geometryType()
                == QgsWkbTypes.GeometryType.PointGeometry):
                options.layerOptions = [
                    "GEOMETRY=AS_XY",
                    "CREATE_CSVT=YES"]
            else:
                # Polígonos e linhas são exportados como WKT.
                options.layerOptions = [
                    "GEOMETRY=AS_WKT",
                    "CREATE_CSVT=YES"]

        elif driver == "ESRI SHAPEFILE":
            options.fileEncoding = "UTF-8"
            options.layerOptions = [
                "ENCODING=UTF-8"]

            conversor_precisao = (
                self._configurar_precisao_shapefile(lyr_to_write, options))

        elif driver == "DXF":
            options.skipAttributeCreation = True

        elif driver == "GEOJSON":
            options.layerOptions = ["COORDINATE_PRECISION=8"]

        elif driver == "GPKG":
            options.layerOptions = ["SPATIAL_INDEX=YES"]

        try:
            error, _ = (
                QgsVectorFileWriter.writeAsVectorFormat(
                    lyr_to_write,
                    fileName,
                    options))

            if error != QgsVectorFileWriter.WriterError.NoError:
                return False

            if driver == "ESRI SHAPEFILE":
                caminho_cpg = (os.path.splitext(fileName)[0]
                    + ".cpg")

                try:
                    with open(
                        caminho_cpg,
                        "w",
                        encoding="ascii"
                    ) as arquivo_cpg:
                        arquivo_cpg.write("UTF-8")
                except OSError:
                    pass  # nosec B110

            if (driver == "KML"
                and hasattr(self,
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
        Salva a camada de polígonos selecionada como Shapefile,
        preservando estilo, etiquetas, UTF-8 e precisão numérica.
        """
        selected_indexes = (self.dlg.treeViewListaPoligono.selectedIndexes())

        if not selected_indexes:
            self.mostrar_mensagem(self.tr("Selecione uma camada."), "Aviso")
            return

        idx = next(
            (i for i in selected_indexes
                if i.column() == 0),
            selected_indexes[0])

        item = idx.model().itemFromIndex(idx)

        layer_id = (item.data(Qt.ItemDataRole.UserRole)
            or item.data())

        if not isinstance(layer_id, str):
            self.mostrar_mensagem(self.tr("Camada selecionada inválida."), "Erro")
            return

        layer_to_save = QgsProject.instance().mapLayer(layer_id)

        if (not layer_to_save
            or not layer_to_save.isValid()):
            self.mostrar_mensagem(self.tr("Camada não encontrada ou inválida."), "Erro")
            return

        if (layer_to_save.geometryType()
            != QgsWkbTypes.GeometryType.PolygonGeometry):
            self.mostrar_mensagem(self.tr("A camada selecionada não é uma camada de polígonos."), "Aviso")
            return

        # Guarda os dados antes da exportação.
        nome_camada_original = layer_to_save.name()

        is_temporary = (layer_to_save.dataProvider().name()
            == "memory")

        # Guarda o estilo completo da camada
        estilo_camada = QgsMapLayerStyle()

        try:
            estilo_camada.readFromLayer(layer_to_save)
        except Exception:
            estilo_camada = None

        # Fallback para renderizador e rótulos
        renderer = (layer_to_save.renderer().clone()
            if layer_to_save.renderer()
            else None)

        etiquetas = (layer_to_save.labeling().clone()
            if layer_to_save.labeling()
            else None)

        labels_enabled = layer_to_save.labelsEnabled()

        if layer_to_save.isEditable():
            try:
                layer_to_save.commitChanges()
            except Exception:
                pass  # nosec B110

        base_dir = (getattr(self, "ultimo_caminho_salvo", "")
            or os.path.expanduser("~"))

        sugestao = os.path.join(base_dir, f"{nome_camada_original}.shp")

        nome_arquivo = self.escolher_local_para_salvar(sugestao, self.tr("Arquivos Shapefile (*.shp)"))

        if not nome_arquivo:
            return

        if not nome_arquivo.lower().endswith(".shp"):
            nome_arquivo += ".shp"

        # Nome da camada igual ao nome escolhido no salvamento.
        nome_camada_salva = os.path.splitext(
            os.path.basename(nome_arquivo))[0]

        pasta = os.path.dirname(nome_arquivo)

        if pasta:
            self.ultimo_caminho_salvo = pasta

        start = time.time()

        if not self.salvar_camada(layer_to_save, nome_arquivo, "ESRI Shapefile"):
            self.mostrar_mensagem(self.tr("Falha ao salvar a camada no formato Shapefile."), "Erro")
            return

        # Não acessar layer_to_save abaixo deste ponto.
        new_layer = QgsVectorLayer(nome_arquivo, nome_camada_salva, "ogr")

        if not new_layer.isValid():
            self.mostrar_mensagem(self.tr("Falha ao carregar a nova camada."), "Erro")
            return

        try:
            new_layer.setProviderEncoding("UTF-8")
        except (AttributeError, TypeError):
            pass  # nosec B110

        # Primeiro configura campos, sinais e cálculos da camada salva
        self.tratar_poligonos(new_layer)

        # Depois restaura o estilo completo da camada original
        estilo_aplicado = False

        if estilo_camada is not None:
            try:
                estilo_camada.writeToLayer(new_layer)
                estilo_aplicado = True
            except Exception:
                estilo_aplicado = False

        # Fallback caso o estilo completo não possa ser aplicado
        if not estilo_aplicado:
            if renderer is not None:
                try:
                    new_layer.setRenderer(renderer)
                except Exception:
                    pass  # nosec B110

            if etiquetas is not None:
                try:
                    new_layer.setLabeling(etiquetas)
                    new_layer.setLabelsEnabled(labels_enabled)
                except Exception:
                    pass  # nosec B110

        # Garante os aliases traduzidos dos campos após restaurar o estilo
        idx_peri = new_layer.fields().indexOf("Perimetro")
        if idx_peri != -1:
            new_layer.setFieldAlias(idx_peri, self.tr("Perímetro"))

        idx_area = new_layer.fields().indexOf("Area")
        if idx_area != -1:
            new_layer.setFieldAlias(idx_area, self.tr("Área"))

        QgsProject.instance().addMapLayer(new_layer, False)

        root = QgsProject.instance().layerTreeRoot()

        grupo = (root.findGroup(self.tr("Camadas Salvas"))
            or root.addGroup(self.tr("Camadas Salvas")))

        grupo.addLayer(new_layer)

        if (is_temporary
            and QgsProject.instance().mapLayer(layer_id)):
            QgsProject.instance().removeMapLayer(layer_id )

        try:
            new_layer.startEditing()
        except Exception:
            pass  # nosec B110

        elapsed = time.time() - start

        self.mostrar_mensagem(self.tr("Camada salva em {elapsed:.2f} s.").format(elapsed=elapsed), "Sucesso", caminho_pasta=pasta)

    def _configurar_precisao_shapefile(self, layer, options):
        """
        Detecta a maior quantidade de casas decimais significativa
        de cada campo e aplica essa precisão ao Shapefile.
        """
        precisoes = {}
        tipos_decimais = {QMetaType.Type.Double, QMetaType.Type.Float}

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
                tolerancia = max(1e-9, math.ulp(numero) * 16)

                casas_valor = 10

                for casas in range(11):
                    if abs(numero - round(numero, casas)) <= tolerancia:
                        casas_valor = casas
                        break

                maior_precisao = max(maior_precisao, casas_valor)

            precisoes[indice] = maior_precisao

        class ConversorPrecisao(QgsVectorFileWriter.FieldValueConverter):
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

                    novo_campo.setLength(max(largura, precisao + 12))

                return novo_campo

            def convert(self, indice, valor):
                if indice not in self.precisoes:
                    return valor

                if valor is None:
                    return valor

                try:
                    return round(float(valor), self.precisoes[indice])
                except (TypeError, ValueError):
                    return valor

            def clone(self):
                return ConversorPrecisao(self.campos, self.precisoes)

        conversor = ConversorPrecisao(layer.fields(), precisoes)

        options.fieldValueConverter = conversor

        # Retorna para manter o objeto vivo durante a exportação.
        return conversor

    def renomear_camada_selecionada(self):
        """
        Permite ao usuário renomear uma camada de polígono selecionada no treeViewListaPoligono,
        garantindo unicidade do nome no projeto.

        Fluxo:
        - Obtém o índice selecionado.
        - Recupera a camada associada ao item (usando Qt.UserRole).
        - Exibe um diálogo para o usuário digitar o novo nome.
        - Garante que o nome será único (ajusta se necessário).
        - Atualiza o nome da camada no QGIS e o texto do item no treeView.
        """
        # Obtém os índices atualmente selecionados no treeView de polígonos
        selected_indexes = self.dlg.treeViewListaPoligono.selectedIndexes()
        if selected_indexes:
            # Pega o primeiro índice selecionado
            selected_index = selected_indexes[0]
            # Recupera o ID da camada usando o papel UserRole (garante que é o ID real da camada QGIS)
            layer_id = selected_index.model().itemFromIndex(selected_index).data(Qt.ItemDataRole.UserRole)
            # Busca a camada correspondente no projeto QGIS
            selected_layer = QgsProject.instance().mapLayer(layer_id)
            if selected_layer:
                # Exibe um diálogo para o usuário digitar o novo nome (pré-preenchido com o nome atual)
                novo_nome, ok = QInputDialog.getText(self.dlg,
                    self.tr("Renomear Camada"),
                    self.tr("Digite o novo nome da camada:"),
                    text=selected_layer.name())
                # Se o usuário confirmou e digitou algo
                if ok and novo_nome:
                    # Gera um nome único para evitar duplicidade no projeto
                    novo_nome = self.gerar_nome_unico(novo_nome, selected_layer.id())
                    # Renomeia a camada no QGIS (isso pode disparar sinais que atualizam a interface automaticamente)
                    selected_layer.setName(novo_nome)
                    # Em vez de tentar alterar diretamente o item do modelo (risco de crash), reconstrói o treeView do zero
                    self.atualizar_treeView_lista_poligono()

    def gerar_nome_unico(self, base_nome, current_layer_id):
        """
        Gera um nome único para uma camada de polígono dentro do projeto QGIS,
        assegurando que não haja conflitos de nomeação entre as camadas de polígonos.

        Parâmetros:
        - base_nome (str): O nome base proposto para a camada.
        - current_layer_id (str): O ID da camada que está sendo renomeada, usado para excluir seu nome atual da verificação de duplicidade.

        Funcionalidades:
        - Cria um dicionário dos nomes de todas as camadas de polígonos existentes no projeto QGIS, excluindo a camada que está sendo renomeada.
        - Verifica se o nome base já existe entre as camadas de polígonos. Se não existir, retorna o nome base como válido.
        - Se o nome base já existir, gera variações do nome acrescentando um sufixo numérico (por exemplo, "Nome_1", "Nome_2") até encontrar um nome não utilizado.
        - Retorna o novo nome único gerado.
        """
        # Restringe apenas para camadas vetoriais de polígonos
        existing_names = {layer.name(): layer.id()
            for layer in QgsProject.instance().mapLayers().values()
            if (layer.id() != current_layer_id and
                layer.type() == QgsMapLayer.LayerType.VectorLayer and
                layer.geometryType() == QgsWkbTypes.GeometryType.PolygonGeometry)}
        if base_nome not in existing_names:
            return base_nome
        else:
            i = 1
            novo_nome = f"{base_nome}_{i}"
            while novo_nome in existing_names:
                i += 1
                novo_nome = f"{base_nome}_{i}"
            return novo_nome

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
            tipo_poligono = self.obter_tipo_de_poligono(layer)  # Obtém o tipo de geometria da camada (ex: Point, MultiPoint)
            crs = layer.crs().description() if layer.crs().isValid() else self.tr("Sem Georreferenciamento")  # Obtém a descrição do SRC da camada ou "Sem Georreferenciamento" se inválido
            tooltip_text = self.tr("Tipo: {tipo_poligono}\nSRC: {crs}").format(tipo_poligono=tipo_poligono, crs=crs)  # Formata o texto do tooltip com as informações da camada
            QToolTip.showText(QCursor.pos(), tooltip_text)  # Exibe o tooltip na posição atual do cursor

    def obter_tipo_de_poligono(self, layer):
        """
        Retorna uma string que descreve o tipo de geometria da camada fornecida.

        A função obtém o tipo de geometria WKB (Well-Known Binary) da camada e converte esse tipo
        em uma string legível, como 'Point', 'MultiPoint', etc.

        Parâmetros:
        - layer: Objeto QgsVectorLayer representando a camada de onde o tipo de ponto será extraído.

        Retorno:
        - tipo_poligono (str): Uma string que descreve o tipo de geometria da camada.
        """
        geometry_type = layer.wkbType()  # Obtém o tipo de geometria WKB (Well-Known Binary) da camada
        tipo_poligono = QgsWkbTypes.displayString(geometry_type)  # Converte o tipo de geometria em uma string legível
        return tipo_poligono  # Retorna a string que descreve o tipo de geometria

    def visualizar_poligono_selecionada(self):
        """
        Aproxima a visualização do mapa para a camada de polígono selecionada no treeView.

        Observação: ao criar/adicionar feições recentemente, a extensão (extent) pode ainda
        não estar atualizada. Por isso, forçamos updateExtents() e, se necessário, tentamos
        novamente no próximo ciclo da UI.
        """
        index = self.dlg.treeViewListaPoligono.currentIndex()
        if not index.isValid():
            return

        item = index.model().itemFromIndex(index)
        if item is None:
            return

        # Polígonos: pega o layer_id do UserRole (como você já fazia corretamente)
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

    def adicionar_camada_e_atualizar(self):
        """
        Método chamado ao clicar no botão para criar uma camada de polígono.
        Cria a camada de polígono e atualiza o treeView.
        """
        # Chamada para a função que cria uma nova camada de polígonos
        self.poligono_manager.criar_camada_poligonos()  

        # Após adicionar a camada, atualize o treeView
        self.atualizar_treeView_lista_poligono()

    def abrir_caixa_nome_camada(self):
        """
        Abre o diálogo de criação da camada de polígonos, permitindo:

        - definir o nome da camada;
        - escolher cor de preenchimento e borda;
        - escolher o SRC;
        - desabilitar o formulário de atributos.
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

        # Texto real e editável
        lineEdit.setText(self.gerar_nome_unico(self.tr("Polígonos Temporários"), ""))

        frame_layout.addWidget(lineEdit)

        # Botões Escolher Cor e Projetar SRC
        layout_opcoes = QHBoxLayout()
        layout_opcoes.setSpacing(6)

        pushButtonCor = QPushButton(self.tr("Escolher Cor"))
        pushButtonCrs = QPushButton(self.tr("Projetar SRC"))

        layout_opcoes.addWidget(pushButtonCor)
        layout_opcoes.addWidget(pushButtonCrs)

        frame_layout.addLayout(layout_opcoes)

        # Checkbox para ocultar o formulário
        checkBoxNaoExibirDialogo = QCheckBox(self.tr("Não exibir diálogo de atributos"))

        checkBoxNaoExibirDialogo.setChecked(False)

        checkBoxNaoExibirDialogo.setToolTip(
            self.tr("Quando marcado, os polígonos serão adicionados sem abrir o formulário de atributos."))

        frame_layout.addWidget(checkBoxNaoExibirDialogo)

        layout.addWidget(frame)

        # Valores escolhidos pelo usuário
        cor_preenchimento_selecionada = None
        cor_borda_selecionada = None
        crs_selecionado = None

        # Escolher preenchimento e borda usando a mesma lógica do treeView
        def escolher_cor():
            nonlocal cor_preenchimento_selecionada
            nonlocal cor_borda_selecionada

            cor_inicial_preenchimento = (
                cor_preenchimento_selecionada
                if (isinstance(cor_preenchimento_selecionada, QColor)
                    and cor_preenchimento_selecionada.isValid())
                else QColor(255, 255, 255))

            cor_inicial_borda = (
                cor_borda_selecionada
                if (isinstance(cor_borda_selecionada, QColor)
                    and cor_borda_selecionada.isValid())
                else QColor(0, 0, 0))

            nova_cor_preenchimento, nova_cor_borda = self.prompt_for_new_colors(
                cor_inicial_preenchimento,
                cor_inicial_borda,
                parent=dialog)

            if nova_cor_preenchimento is None or nova_cor_borda is None:
                return

            cor_preenchimento_selecionada = QColor(nova_cor_preenchimento)
            cor_borda_selecionada = QColor(nova_cor_borda)

            cor_texto = ("#000000"
                if cor_preenchimento_selecionada.lightness() > 150
                else "#ffffff")

            preenchimento_css = ("transparent"
                if cor_preenchimento_selecionada.alpha() == 0
                else cor_preenchimento_selecionada.name())

            borda_css = ("transparent"
                if cor_borda_selecionada.alpha() == 0
                else cor_borda_selecionada.name())

            pushButtonCor.setStyleSheet("QPushButton {"
                f"background-color: {preenchimento_css};"
                f"border: 3px solid {borda_css};"
                f"color: {cor_texto};"
                "}")

            pushButtonCor.setToolTip(
                self.tr("Preenchimento: {fill}\nBorda: {border}").format(fill=(self.tr("Transparente")
                        if cor_preenchimento_selecionada.alpha() == 0
                        else cor_preenchimento_selecionada.name().upper()),
                    border=(self.tr("Transparente")
                        if cor_borda_selecionada.alpha() == 0
                        else cor_borda_selecionada.name().upper())))

        pushButtonCor.clicked.connect(escolher_cor)

        # Escolher SRC
        def escolher_crs():
            nonlocal crs_selecionado

            dialog_crs = QgsProjectionSelectionDialog(dialog)

            crs_inicial = (crs_selecionado
                if (isinstance(crs_selecionado,
                        QgsCoordinateReferenceSystem)
                    and crs_selecionado.isValid())
                else QgsProject.instance().crs())

            dialog_crs.setCrs(crs_inicial)

            if (dialog_crs.exec()
                != QDialog.DialogCode.Accepted):
                return

            novo_crs = dialog_crs.crs()

            if not novo_crs.isValid():
                return

            crs_selecionado = QgsCoordinateReferenceSystem(novo_crs)

            texto_crs = (novo_crs.authid()
                or self.tr("SRC selecionado"))

            pushButtonCrs.setText(texto_crs)

            pushButtonCrs.setToolTip(self.tr("{authid} - {description}").format(authid=novo_crs.authid(), description=novo_crs.description()))

        pushButtonCrs.clicked.connect(escolher_crs)

        # Botões Adicionar e Cancelar
        okButton = QPushButton(self.tr("Adicionar"))

        cancelButton = QPushButton(self.tr("Cancelar"))

        # O nome já começa preenchido
        okButton.setEnabled(bool(lineEdit.text().strip()))

        lineEdit.textChanged.connect(lambda texto:
            okButton.setEnabled(bool(texto.strip())))

        buttonLayout = QHBoxLayout()
        buttonLayout.addWidget(okButton)
        buttonLayout.addWidget(cancelButton)

        layout.addLayout(buttonLayout)

        okButton.clicked.connect(dialog.accept)
        cancelButton.clicked.connect(dialog.reject)

        # Deixa "Polígonos Temporários" selecionado ao abrir
        QTimer.singleShot(0, lambda: (lineEdit.setFocus(), lineEdit.selectAll()))

        # Executa o diálogo
        if (dialog.exec()
            != QDialog.DialogCode.Accepted):
            return

        nome_camada = lineEdit.text().strip()

        if not nome_camada:
            return

        # Garante nome único para a nova camada
        nome_camada = self.gerar_nome_unico(nome_camada, "")

        # Cria a camada
        nova_camada = self.poligono_manager.criar_camada_poligonos(nome_camada=nome_camada, suprimir_formulario=checkBoxNaoExibirDialogo.isChecked())

        if (not isinstance(nova_camada, QgsVectorLayer)
            or not nova_camada.isValid()):
            self.mostrar_mensagem(self.tr("Não foi possível criar a camada de polígonos."), "Erro")
            return

        # Aplica o SRC escolhido
        if (isinstance(crs_selecionado, QgsCoordinateReferenceSystem)
            and crs_selecionado.isValid()):
            try:
                nova_camada.setCrs( crs_selecionado)
            except Exception:
                pass  # nosec B110

        # Aplica preenchimento e borda
        if (isinstance(cor_preenchimento_selecionada, QColor)
            and cor_preenchimento_selecionada.isValid()
            and isinstance(cor_borda_selecionada,
                QColor)
            and cor_borda_selecionada.isValid()):
            try:
                self.apply_new_colors(nova_camada,
                    cor_preenchimento_selecionada,
                    cor_borda_selecionada)
            except Exception:
                pass  # nosec B110

        # Atualiza primeiro a lista de camadas
        self.atualizar_treeView_lista_poligono()

        def selecionar_e_ativar_nova_camada():
            try:
                # Garante que a camada recém-criada seja a camada ativa
                self.iface.setActiveLayer(nova_camada)
                self.iface.layerTreeView().setCurrentLayer(nova_camada)

                # Seleciona explicitamente a nova camada no TreeView do plugin
                model = self.dlg.treeViewListaPoligono.model()

                if model is not None:
                    for row in range(model.rowCount()):
                        item = model.item(row, 0)

                        if (item
                            and item.data(Qt.ItemDataRole.UserRole) == nova_camada.id()):
                            index = model.indexFromItem(item)

                            self.dlg.treeViewListaPoligono.setCurrentIndex(index)

                            self.dlg.treeViewListaPoligono.scrollTo(index)

                            break

                # Ativa a ferramenta "Adicionar Polígono"
                action = self.iface.actionAddFeature()

                if (action is not None
                    and action.isEnabled()
                    and not action.isChecked()):
                    action.trigger()

            except Exception:
                pass  # nosec B110

        # Executa após o TreeView e o QGIS concluírem a atualização
        QTimer.singleShot(0, selecionar_e_ativar_nova_camada)

    def _copiar_para_memoria_poligono(self, src: QgsVectorLayer, new_name: str, campos_para_remover: set[str] | None = None) -> QgsVectorLayer | None:
        """
        Copia SOMENTE feições poligonais (Polygon/MultiPolygon) para uma camada em memória (MultiPolygon),
        mantendo atributos (opcionalmente removendo campos indesejados, útil para KML/KMZ).
        """
        if not isinstance(src, QgsVectorLayer) or not src.isValid():
            return None

        crs_authid = src.crs().authid() if src.crs() and src.crs().isValid() else "EPSG:4326"

        # Campos a manter
        if campos_para_remover:
            fields_to_keep = [f for f in src.fields() if f.name() not in campos_para_remover]
            keep_names = [f.name() for f in fields_to_keep]
        else:
            fields_to_keep = list(src.fields())
            keep_names = None  # não precisa

        mem = QgsVectorLayer(f"MultiPolygon?crs={crs_authid}", new_name, "memory")
        if not mem.isValid():
            return None

        dp = mem.dataProvider()
        dp.addAttributes(fields_to_keep)
        mem.updateFields()

        def _to_multipolygon_xy(g: QgsGeometry) -> QgsGeometry | None:
            if not g or g.isEmpty():
                return None

            gg = QgsGeometry(g)

            # Tenta “normalizar” para polígono (segmentiza curvas quando possível)
            try:
                gg.convertToType(QgsWkbTypes.GeometryType.PolygonGeometry, True)
            except Exception:
                pass  # nosec B110

            def _ptxy(p):
                # p pode ser QgsPoint, QgsPointXY ou tupla
                try:
                    return QgsPointXY(p)
                except Exception:
                    return QgsPointXY(p[0], p[1])

            if QgsWkbTypes.isMultiType(gg.wkbType()):
                mp = gg.asMultiPolygon()
                if mp:
                    mp_xy = []
                    for poly in mp:
                        poly_xy = []
                        for ring in poly:
                            poly_xy.append([_ptxy(v) for v in ring])
                        mp_xy.append(poly_xy)
                    return QgsGeometry.fromMultiPolygonXY(mp_xy)

            p = gg.asPolygon()
            if p:
                p_xy = []
                for ring in p:
                    p_xy.append([_ptxy(v) for v in ring])
                return QgsGeometry.fromMultiPolygonXY([p_xy])

            return None

        feats_out = []
        for feat in src.getFeatures():
            geom = feat.geometry()
            if not geom or geom.isEmpty():
                continue

            if QgsWkbTypes.geometryType(geom.wkbType()) != QgsWkbTypes.GeometryType.PolygonGeometry:
                continue

            mg = _to_multipolygon_xy(geom)
            if not mg or mg.isEmpty():
                continue

            nf = QgsFeature(mem.fields())
            nf.setGeometry(mg)

            if keep_names is None:
                # mesma ordem do src.fields()
                nf.setAttributes(feat.attributes())
            else:
                # mesma ordem de fields_to_keep
                nf.setAttributes([feat.attribute(n) for n in keep_names])

            feats_out.append(nf)

        if not feats_out:
            return None

        dp.addFeatures(feats_out)
        mem.updateExtents()

        # tenta clonar renderer (quando fizer sentido)
        try:
            if src.renderer():
                mem.setRenderer(src.renderer().clone())
        except Exception:
            pass  # nosec B110

        mem.triggerRepaint()
        return mem

    def _processar_kml_kmz_poligonos(self, file_path: str, layer_name: str) -> list[QgsVectorLayer]:
        """
        Abre KML/KMZ e retorna TODAS as camadas/sublayers de POLÍGONOS em memória.
        Resolve o caso clássico: KML com Placemarks dentro de Folders -> OGR expõe como sublayers.
        Retorno: list[QgsVectorLayer] (memory) ou [].
        """
        out_layers: list[QgsVectorLayer] = []
        seen: set[tuple[str, str]] = set()
        used_names: set[str] = set()

        campos_para_remover = {
            "description", "timestamp", "begin", "end",
            "altitudeMode", "tessellate", "extrude", "drawOrder",
            "visibility", "icon"}

        def _limpar_nome(nome: str) -> str:
            if not nome:
                return layer_name

            nome = str(nome).strip()

            low = nome.lower()
            if low.endswith(".kml") or low.endswith(".kmz"):
                nome = os.path.splitext(nome)[0].strip()

            low_nome = nome.lower()
            low_prefix = layer_name.lower()
            if low_nome.startswith(low_prefix):
                resto = nome[len(layer_name):].lstrip(" _-–—").strip()
                if resto:
                    nome = resto

            return nome or layer_name

        def _nome_unico(base: str) -> str:
            n = base
            i = 2
            while n in used_names:
                n = f"{base} ({i})"
                i += 1
            used_names.add(n)
            return n

        def _infer_geom_type(layer: QgsVectorLayer):
            gt = QgsWkbTypes.geometryType(layer.wkbType())
            if gt in (QgsWkbTypes.GeometryType.UnknownGeometry, QgsWkbTypes.GeometryType.NullGeometry):
                for f in layer.getFeatures():
                    g = f.geometry()
                    if g and not g.isEmpty():
                        gt = QgsWkbTypes.geometryType(g.wkbType())
                        break
            return gt

        def _yield_sublayers():
            # 1) provider metadata (quando disponível)
            try:
                from qgis.core import QgsProviderRegistry
                md = QgsProviderRegistry.instance().providerMetadata("ogr")
                details = md.querySublayers(file_path)
                for d in details or []:
                    uri = d.uri() if hasattr(d, "uri") else None
                    name = d.name() if hasattr(d, "name") else None
                    if uri and name:
                        key = (uri, name)
                        if key in seen:
                            continue
                        seen.add(key)
                        yield uri, name
                if details:
                    return
            except Exception:
                pass  # nosec B110

            # 2) fallback: subLayers() do provider
            dummy = QgsVectorLayer(file_path, layer_name, "ogr")
            if not dummy.isValid():
                return

            try:
                subs = dummy.dataProvider().subLayers() or []
            except Exception:
                subs = []

            if subs:
                for s in subs:
                    parts = s.split(":")
                    if len(parts) >= 2:
                        name = parts[1]
                        uri = f"{file_path}|layername={name}"
                        key = (uri, name)
                        if key in seen:
                            continue
                        seen.add(key)
                        yield uri, name
            else:
                yield file_path, layer_name

        any_valid = False

        for uri, subname in _yield_sublayers():
            src = QgsVectorLayer(uri, subname, "ogr")
            if not src.isValid():
                continue

            any_valid = True

            if _infer_geom_type(src) != QgsWkbTypes.GeometryType.PolygonGeometry:
                del src
                continue

            clean = _nome_unico(_limpar_nome(subname))

            mem = self._copiar_para_memoria_poligono(src, clean, campos_para_remover=campos_para_remover)
            if mem and mem.isValid():
                out_layers.append(mem)

            del src

        if not any_valid:
            self.mostrar_mensagem(self.tr("Falha ao carregar KML/KMZ."), "Erro")
            return []

        if not out_layers:
            self.mostrar_mensagem(self.tr("Nenhuma camada de POLÍGONOS encontrada no KML/KMZ."), "Aviso")
            return []

        return out_layers

    def abrir_adicionar_arquivo_poligono(self):
        """
        Importa arquivos de polígonos usando o mesmo fluxo do drag-and-drop.

        Isso garante que KML/KMZ com várias pastas/sublayers sejam adicionados
        por completo, dentro de grupo, sem repetir .kml/.kmz no nome.
        """
        file_filter = (
            "All Supported Formats (*.dxf *.kml *.kmz *.shp *.geojson *.gpkg);;"
            "DXF Files (*.dxf);;"
            "KML Files (*.kml);;"
            "KMZ Files (*.kmz);;"
            "Shapefiles (*.shp);;"
            "GeoJSON Files (*.geojson);;"
            "Geopackage Files (*.gpkg)")

        file_path, _ = QFileDialog.getOpenFileName(self.dlg, self.tr("Abrir Arquivo de Polígonos"), "", file_filter)

        if not file_path:
            return

        try:
            ok = self._adicionar_arquivo_por_caminho(file_path)
            if not ok:
                self.mostrar_mensagem(self.tr("Nenhuma feição de polígono encontrada ou o arquivo não pôde ser carregado."), "Aviso")
        except Exception as e:
            self.mostrar_mensagem(self.tr("Erro ao adicionar arquivo: {error}").format(error=e), "Erro")

    def _processar_dxf_poligonos(self, file_path: str, layer_name: str, manter_original: bool = False) -> tuple[QgsVectorLayer | None, QgsVectorLayer | None]:
        """
        Lê um arquivo **DXF** e devolve:

        1. **Camada de polígonos** em memória, contendo apenas entidades fechadas que possam ser
           representadas como *Polygon* (LWPOLYLINE/POLYLINE fechadas e HATCH).
        2. **Camada de textos** (opcional) se o DXF contiver entidades `TEXT` ou `MTEXT`
           ─ criada por :py:meth:`carregar_texto_dxf`.

        (docstring mantida como você escreveu)
        """
        # Exibe barra de progresso indeterminada enquanto prepara o DXF
        preparacao_msg = self.iface.messageBar().createMessage(self.tr("Preparando processamento do DXF, aguarde..."))
        preparacao_bar = QProgressBar()
        preparacao_bar.setMinimum(0)
        preparacao_bar.setMaximum(0)  # Indeterminado
        preparacao_bar.setTextVisible(True)
        preparacao_bar.setMinimumWidth(300)
        preparacao_msg.layout().addWidget(preparacao_bar)
        widget_preparacao = self.iface.messageBar().pushWidget(preparacao_msg, Qgis.MessageLevel.Info)

        QCoreApplication.processEvents()

        # Tenta ler o DXF e garantir modelspace
        try:
            dxf_doc = ezdxf.readfile(file_path)
            msp = dxf_doc.modelspace()
        except Exception as e:
            try:
                self.iface.messageBar().popWidget(widget_preparacao)
            except Exception:
                pass  # nosec B110
            self.mostrar_mensagem(self.tr("Erro ao abrir o DXF: {error}").format(error=e), "Erro")
            return None, None

        # Escolhe CRS
        dlg = QgsProjectionSelectionDialog()
        try:
            ok = dlg.exec()
        except Exception:
            ok = dlg.exec()

        if not ok:
            try:
                self.iface.messageBar().popWidget(widget_preparacao)
            except Exception:
                pass  # nosec B110
            self.mostrar_mensagem(self.tr("Operação cancelada pelo usuário."), "Aviso")
            return None, None

        crs = dlg.crs()
        crs_authid = crs.authid()

        try:
            self.iface.messageBar().popWidget(widget_preparacao)
        except Exception:
            pass  # nosec B110

        # Prepara campos básicos
        fields = [
            QgsField("layer", QMetaType.Type.QString),
            QgsField("r", QMetaType.Type.Int),
            QgsField("g", QMetaType.Type.Int),
            QgsField("b", QMetaType.Type.Int)]

        vl = QgsVectorLayer(f"Polygon?crs={crs_authid}", f"{layer_name}_poly", "memory")
        pr = vl.dataProvider()
        pr.addAttributes(fields)
        vl.updateFields()

        idx_r = vl.fields().indexFromName("r")
        idx_g = vl.fields().indexFromName("g")
        idx_b = vl.fields().indexFromName("b")

        feats_out = []
        total_polyline = 0
        total_hatch = 0

        # Pré-varredura (listas) para máximo coerente
        entities_polyline = list(msp.query("LWPOLYLINE POLYLINE"))
        entities_hatch = list(msp.query("HATCH"))

        # Cores das layers do DXF.
        # Necessário para entidades configuradas como ByLayer (ACI 256).
        dxf_layers = {}

        for lay in dxf_doc.layers:
            try:
                if (hasattr(lay, "rgb")
                    and lay.rgb is not None):
                    rgb = lay.rgb

                else:
                    aci = abs(int(lay.color))

                    if 1 <= aci <= 255:
                        rgb = aci2rgb(aci)

                    else:
                        rgb = (0, 0, 0)

                dxf_layers[lay.dxf.name] = (
                    int(rgb[0]),
                    int(rgb[1]),
                    int(rgb[2]))

            except Exception:
                dxf_layers[lay.dxf.name] = (0, 0, 0)

        def _cor_entidade_dxf(ent):
            """
            Retorna a cor RGB efetivamente exibida pela entidade no DXF.

            Prioridade:
            1. True Color;
            2. ByLayer;
            3. ByBlock;
            4. ACI explícito.
            """
            try:
                if (hasattr(ent, "rgb")
                    and ent.rgb is not None):
                    rgb = ent.rgb

                    return (
                        int(rgb[0]),
                        int(rgb[1]),
                        int(rgb[2]))

                aci = int(getattr(ent.dxf,"color", 256))

                # 256 = ByLayer
                if aci == 256:
                    layer_name = getattr(ent.dxf, "layer", "")

                    return dxf_layers.get(layer_name, (0, 0, 0))

                # 0 = ByBlock.
                # Como estamos importando para uma camada QGIS independente,
                # usamos a cor da layer como melhor representação visual.
                if aci == 0:
                    layer_name = getattr(ent.dxf, "layer", "")

                    return dxf_layers.get(layer_name, (0, 0, 0))

                if 1 <= abs(aci) <= 255:
                    rgb = aci2rgb(abs(aci))

                    return (
                        int(rgb[0]),
                        int(rgb[1]),
                        int(rgb[2]))

            except Exception:
                pass  # nosec B110

            return (0, 0, 0)

        total_entities = sum(1 for e in entities_polyline if getattr(e, "is_closed", False)) + len(entities_hatch)
        processed = 0

        progressBar, progressMsgBar = self.iniciar_progress_bar(message=self.tr('Processando polígonos do DXF "{layer_name}", aguarde...').format(layer_name=layer_name))
        progressBar.setValue(0)
        progressBar.setMaximum(total_entities if total_entities > 0 else 1)

        def _safe_pop(w):
            try:
                self.iface.messageBar().popWidget(w)
            except Exception:
                pass  # nosec B110

        # 🔧 Throttle de UI
        UI_UPDATE_EVERY = 25  # ajuste aqui (25/50/100)
        last_ui_value = -1

        def _ui_tick(force: bool = False) -> bool:
            """
            Atualiza a barra e processa eventos só ocasionalmente.
            Retorna False se der RuntimeError (cancelamento/fechamento do widget).
            """
            nonlocal last_ui_value
            if not force and (processed % UI_UPDATE_EVERY != 0):
                return True

            if processed == last_ui_value and not force:
                return True

            try:
                progressBar.setValue(processed)
            except RuntimeError:
                return False

            last_ui_value = processed
            QCoreApplication.processEvents()
            return True

        def _hatch_path_to_ring(path):
            """
            Converte um boundary path de HATCH em um anel QGIS fechado.

            Preserva visualmente:
            - linhas;
            - arcos;
            - elipses;
            - splines;
            - curvas Bézier.

            As curvas são discretizadas em pequenos segmentos antes
            da criação do polígono QGIS.
            """
            verts_2d = []

            try:
                # O ezdxf interpreta corretamente os diferentes
                # tipos de aresta existentes no HATCH.
                caminho = ezdxf.path.from_hatch_boundary_path(path)

                # Tolerância máxima da aproximação da curva.
                # Para desenho em metros:
                # 0.01 = aproximadamente 1 cm.
                vertices = list(caminho.flattening(distance=0.01, segments=8))

                verts_2d = [(float(v.x), float(v.y))
                    for v in vertices]

            except Exception:
                # Fallback para HATCH simples.
                try:
                    if hasattr(path, "vertices"):
                        verts_2d = [(float(v[0]), float(v[1]))
                            for v in path.vertices]

                except Exception:
                    return []

            # Remove vértices consecutivos repetidos
            limpos = []

            for xy in verts_2d:
                if (not limpos
                    or xy != limpos[-1]):
                    limpos.append(xy)

            if len(limpos) < 3:
                return []

            # Garante fechamento
            if limpos[0] != limpos[-1]:
                limpos.append(limpos[0])

            return [QgsPointXY(x, y)
                for x, y in limpos]

        def _ring_key(ring):
            """
            Cria uma assinatura do anel independente:
            - do vértice inicial;
            - do sentido horário/anti-horário.

            Serve para detectar POLYLINE/LWPOLYLINE
            que já é contorno de um HATCH.
            """
            coords = [(round(float(p.x()), 6), round(float(p.y()), 6))
                for p in ring]

            if (len(coords) > 1
                and coords[0] == coords[-1]):
                coords = coords[:-1]

            if len(coords) < 3:
                return None

            def _normalizar(seq):
                menor = min(seq)
                candidatos = []

                for i, valor in enumerate(seq):
                    if valor == menor:
                        candidatos.append(tuple(seq[i:] + seq[:i]))

                return min(candidatos)

            direta = _normalizar(coords)
            inversa = _normalizar(list(reversed(coords)))

            return min(direta, inversa)

        # Contornos que pertencem a HATCH.
        #
        # Esses contornos não devem ser importados novamente
        # como polígonos independentes, pois um anel interno
        # acabaria preenchendo o próprio buraco.
        hatch_boundary_keys = set()

        for hatch in entities_hatch:
            for path in hatch.paths:
                ring = _hatch_path_to_ring(path)

                if not ring:
                    continue

                key = _ring_key(ring)

                if key is not None:
                    hatch_boundary_keys.add(key)

        try:
            # POLYLINE/LWPOLYLINE fechada
            for ent in entities_polyline:
                if not getattr(ent, "is_closed", False):
                    continue

                pts = []

                try:
                    caminho = ezdxf.path.make_path(ent)

                    vertices = list(
                        caminho.flattening(distance=0.01, segments=8))

                    pts = [
                        QgsPointXY(float(v.x), float(v.y))
                        for v in vertices]

                except Exception:
                    # Fallback para polylines somente com segmentos retos
                    try:
                        pts = [QgsPointXY(*v[:2])
                            for v in ent.vertices()]

                    except Exception:
                        pts = []

                if len(pts) >= 3:
                    ring = (pts + [pts[0]]
                        if pts[0] != pts[-1]
                        else pts)

                    # Se o contorno já pertence a um HATCH,
                    # não cria outro polígono.
                    # Isso é especialmente importante nos anéis
                    # internos, pois eles representam BURACOS.
                    if _ring_key(ring) in hatch_boundary_keys:
                        processed += 1

                        if not _ui_tick():
                            self.mostrar_mensagem(self.tr("Processo cancelado pelo usuário."), "Aviso")
                            return None, None

                        continue

                    geom_qgs = QgsGeometry.fromPolygonXY([ring])

                    if geom_qgs.isGeosValid():
                        r, g, b = _cor_entidade_dxf(ent)

                        layer_dxf = getattr(ent.dxf, "layer", "")

                        feat = QgsFeature(vl.fields())
                        feat.setGeometry(geom_qgs)
                        feat.setAttributes([layer_dxf, r, g, b])
                        feats_out.append(feat)
                        total_polyline += 1

                processed += 1
                if not _ui_tick():
                    self.mostrar_mensagem(self.tr("Processo cancelado pelo usuário."), "Aviso")
                    return None, None

            # HATCH
            #
            # Todos os boundary paths da mesma entidade são
            # tratados em conjunto.
            #
            # A diferença simétrica (XOR) reconstrói corretamente:
            # - contorno externo;
            # - buracos internos;
            # - ilhas dentro de buracos;
            # - múltiplas partes.
            for ent in entities_hatch:
                geom_hatch = None

                for path in ent.paths:
                    ring = _hatch_path_to_ring(path)

                    if not ring:
                        continue

                    geom_ring = QgsGeometry.fromPolygonXY([ring])

                    if (geom_ring.isNull()
                        or geom_ring.isEmpty()
                        or not geom_ring.isGeosValid()):
                        continue

                    if geom_hatch is None:
                        geom_hatch = QgsGeometry(geom_ring)

                    else:
                        geom_resultante = None

                        try:
                            geom_resultante = (geom_hatch.symDifference(geom_ring))

                        except Exception:
                            geom_resultante = None

                        if geom_resultante is not None:
                            geom_hatch = geom_resultante

                # Nenhum contorno válido nesse HATCH
                if (geom_hatch is None
                    or geom_hatch.isNull()
                    or geom_hatch.isEmpty()):
                    processed += 1

                    if not _ui_tick():
                        self.mostrar_mensagem(self.tr("Processo cancelado pelo usuário."), "Aviso")
                        return None, None

                    continue

                # Cor real do HATCH
                r, g, b = _cor_entidade_dxf(ent)

                layer_dxf = getattr(ent.dxf, "layer", "")

                # XOR pode produzir Polygon ou MultiPolygon.
                # Como a camada de memória é Polygon,
                # separa somente as partes externas,
                # preservando os anéis internos de cada parte.
                geometrias_saida = []

                if geom_hatch.isMultipart():
                    try:
                        for polygon in geom_hatch.asMultiPolygon():
                            if not polygon:
                                continue

                            geom_parte = (QgsGeometry.fromPolygonXY(polygon))

                            if (not geom_parte.isNull()
                                and not geom_parte.isEmpty()
                                and geom_parte.isGeosValid()):
                                geometrias_saida.append(geom_parte)

                    except Exception:
                        pass  # nosec B110

                else:
                    if geom_hatch.isGeosValid():
                        geometrias_saida.append(geom_hatch)

                # Cada parte externa vira uma feição.
                # Os buracos permanecem dentro da geometria.
                for geom_qgs in geometrias_saida:
                    feat = QgsFeature(vl.fields())
                    feat.setGeometry(geom_qgs)
                    feat.setAttributes([layer_dxf, r, g, b])
                    feats_out.append(feat)

                    total_hatch += 1

                processed += 1

                if not _ui_tick():
                    self.mostrar_mensagem(self.tr("Processo cancelado pelo usuário."), "Aviso")
                    return None, None

        finally:
            _safe_pop(progressMsgBar)

        # Adiciona as feições
        if feats_out:
            pr.addFeatures(feats_out)
            vl.updateExtents()
            vl.triggerRepaint()

            sym = QgsFillSymbol.createSimple({
                "style": "solid",
                "outline_style": "solid",
                "outline_width": "0.15"})

            symbol_layer = sym.symbolLayer(0)

            cor_dxf = QgsProperty.fromExpression('color_rgb("r","g","b")')

            # Preenchimento com a cor original do DXF
            symbol_layer.dataDefinedProperties().setProperty(QgsSymbolLayer.Property.FillColor, cor_dxf)

            # Borda com a mesma cor original
            symbol_layer.dataDefinedProperties().setProperty(
                QgsSymbolLayer.Property.StrokeColor,
                QgsProperty.fromExpression('color_rgb("r","g","b")'))

            vl.setRenderer(QgsSingleSymbolRenderer(sym))

            for idx in (idx_r, idx_g, idx_b):
                vl.setEditorWidgetSetup(idx, QgsEditorWidgetSetup("Hidden", {}))
            cfg = vl.attributeTableConfig()
            for idx in (idx_r, idx_g, idx_b):
                cfg.setColumnHidden(idx, True)
            vl.setAttributeTableConfig(cfg)

            vl_texto = self.carregar_texto_dxf(file_path, f"{layer_name}_txt", crs_authid)
            return vl, vl_texto

        self.mostrar_mensagem(self.tr("Nenhum polígono encontrado no DXF."), "Aviso")
        return None, None

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
            raise FileNotFoundError(self.tr("Caminho DXF inválido: {path_dxf}").format(path_dxf=repr(path_dxf)))

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

    def tratar_poligonos(self, new_layer):
        """
        Configura sinais e comportamentos personalizados para uma nova camada de polígonos.
        """
        if not new_layer or not new_layer.isValid():
            return

        # evita duplicar conexões se tratar_poligonos for chamado mais de uma vez na mesma layer
        if new_layer.customProperty("ts_tratar_poligonos_done", False):
            return

        # ao adicionar feição: garante ID sequencial e recalcula perímetro/área
        new_layer.featureAdded.connect(lambda fid, lyr=new_layer: self._poligonos_on_feature_added(lyr, fid))

        # ao alterar geometria: recalcula perímetro/área
        new_layer.geometryChanged.connect(lambda fid, _g, lyr=new_layer: self.atualizar_perimetro_area(lyr, fid))

        # ID automático via expressão (continua útil para digitalização “normal”)
        idx_id = new_layer.fields().indexOf("ID")
        if idx_id != -1:
            new_layer.setDefaultValueDefinition(idx_id, QgsDefaultValue('coalesce(maximum("ID"),0)+1'))
            new_layer.setEditorWidgetSetup(idx_id, QgsEditorWidgetSetup("Hidden", {}))

        # (resto do seu código continua igual daqui pra baixo...)
        # Oculta os campos 'Perimetro' e 'Area' (e quaisquer outros exceto ID)
        for i in range(new_layer.fields().count()):
            if i != idx_id:
                new_layer.setEditorWidgetSetup(i, QgsEditorWidgetSetup("Hidden", {}))

        cfg = new_layer.editFormConfig()
        cfg.setSuppress(Qgis.AttributeFormSuppression.On)
        new_layer.setEditFormConfig(cfg)

        # Atualiza Perímetro e Área para feições existentes (mantém como já está)
        idx_peri = new_layer.fields().indexOf("Perimetro")
        idx_area = new_layer.fields().indexOf("Area")

        if idx_peri != -1:
            new_layer.setFieldAlias(idx_peri, self.tr("Perímetro"))

        if idx_area != -1:
            new_layer.setFieldAlias(idx_area, self.tr("Área"))

        if idx_peri != -1 and idx_area != -1:
            new_layer.startEditing()
            for f in new_layer.getFeatures():
                if f.geometry():
                    perimetro, area = self.calcular_perimetro_area(new_layer, f.geometry())
                    new_layer.changeAttributeValue(f.id(), idx_peri, perimetro)
                    new_layer.changeAttributeValue(f.id(), idx_area, area)
            new_layer.commitChanges()

        # Marca a camada somente após concluir as configurações críticas.
        new_layer.setCustomProperty("ts_tratar_poligonos_done", True)

    def _poligonos_on_feature_added(self, layer: QgsVectorLayer, fid: int):
        """Ao criar feição (inclusive via 'Copiar e mover'), garante ID único e atualiza perímetro/área."""
        self._poligonos_garantir_id_sequencial(layer, fid)
        self.atualizar_perimetro_area(layer, fid)

    def _poligonos_garantir_id_sequencial(self, layer: QgsVectorLayer, fid: int):
        """Se o ID vier NULL ou duplicado (caso de cópia), força ID = max(ID)+1."""
        if not layer or not layer.isValid() or not layer.isEditable():
            return

        idx_id = layer.fields().indexOf("ID")
        if idx_id == -1:
            return

        feat = layer.getFeature(fid)
        if not feat:
            return

        def _to_int(v):
            try:
                if v is None:
                    return None
                # QVariant/str/int
                return int(v)
            except Exception:
                return None

        cur = _to_int(feat[idx_id])

        # Detecta duplicação (ex.: Copiar e mover copia o ID igual)
        duplicado = (cur is None)
        if not duplicado:
            for f in layer.getFeatures():
                if f.id() == fid:
                    continue
                if _to_int(f[idx_id]) == cur:
                    duplicado = True
                    break

        if not duplicado:
            return

        # calcula max(ID) excluindo a própria feição nova
        max_id = 0
        for f in layer.getFeatures():
            if f.id() == fid:
                continue
            v = _to_int(f[idx_id])
            if v is not None and v > max_id:
                max_id = v

        layer.changeAttributeValue(fid, idx_id, max_id + 1)

    def atualizar_perimetro_area(self, camada: QgsVectorLayer, fid: int):
        """
        Atualiza os campos 'Perimetro' e 'Area' de uma feição específica ao adicionar/modificar.
        """
        idx_peri = camada.fields().indexOf("Perimetro")
        idx_area = camada.fields().indexOf("Area")
        # Aceita nomes truncados se shapefile
        if idx_peri == -1:
            idx_peri = camada.fields().indexOf("Perimetro"[:10])
        if idx_area == -1:
            idx_area = camada.fields().indexOf("Area")
        if idx_peri == -1 or idx_area == -1:
            return  # Campos não encontrados

        feature = camada.getFeature(fid)
        if feature and feature.geometry():
            perimetro, area = self.calcular_perimetro_area(camada, feature.geometry())
            camada.changeAttributeValue(fid, idx_peri, perimetro)
            camada.changeAttributeValue(fid, idx_area, area)

    def calcular_perimetro_area(self, camada: QgsVectorLayer, geom):
        """
        Calcula o perímetro e a área considerando o CRS da camada.
        """
        medida = QgsDistanceArea()
        if camada.crs().isGeographic():
            medida.setSourceCrs(camada.crs(), QgsProject.instance().transformContext())
            medida.setEllipsoid(QgsProject.instance().crs().ellipsoidAcronym())
            perimetro = round(medida.measurePerimeter(geom), 3)
            area = round(medida.measureArea(geom), 3)
        else:
            perimetro = round(geom.length(), 3)
            area = round(geom.area(), 3)
        return perimetro, area

    def on_layers_removed(self, removed_ids):
        """
        Remove apenas as linhas do TreeView de polígonos
        cujos IDs correspondem às camadas removidas.
        Mantém a seleção válida ao final.
        """
        model = self.dlg.treeViewListaPoligono.model()
        if model is None or model.rowCount() == 0:
            return

        view = self.dlg.treeViewListaPoligono
        cur_idx = view.currentIndex()
        old_row = cur_idx.row() if cur_idx.isValid() else 0

        # Remove linhas cujo Qt.UserRole == layer_id removido
        removed_set = set(removed_ids or [])
        if removed_set:
            # Remove de baixo para cima para não bagunçar os índices
            for row in reversed(range(model.rowCount())):
                item = model.item(row)
                if item and item.data(Qt.ItemDataRole.UserRole) in removed_set:
                    # Se removeu algo acima da seleção, ajusta a referência
                    if row < old_row:
                        old_row -= 1
                    model.removeRow(row)

        # Garante que sempre reste uma seleção válida
        if model.rowCount() > 0:
            cur_idx2 = view.currentIndex()
            if (not cur_idx2.isValid()) or cur_idx2.row() < 0 or cur_idx2.row() >= model.rowCount():
                target_row = max(0, min(old_row, model.rowCount() - 1))
                idx = model.index(target_row, 0)
                view.setCurrentIndex(idx)
                view.scrollTo(idx)

        # Chama atualização dos botões após toda modificação
        self.atualizar_estado_botoes()

    def abrir_dialogo_crs(self):
        """
        Abre um diálogo de seleção de CRS e reprojeta a camada de polígonos selecionada
        no treeViewListaPoligono, copiando simbologia (cores) e rótulos da camada original.
        """
        index = self.dlg.treeViewListaPoligono.currentIndex()
        if not index.isValid():
            return

        layer_id = index.model().itemFromIndex(index).data(Qt.ItemDataRole.UserRole)
        layer = QgsProject.instance().mapLayer(layer_id)

        # Confere tipo: polígonos
        if not layer or layer.geometryType() != QgsWkbTypes.GeometryType.PolygonGeometry:
            self.mostrar_mensagem(self.tr("Por favor, selecione uma camada de polígonos válida."), "Aviso")
            return

        # Diálogo de seleção de CRS
        dialog = QgsProjectionSelectionDialog(self.dlg)
        dialog.setCrs(layer.crs())
        if not dialog.exec():
            return

        novo_crs = dialog.crs()

        # Reprojetar via processing
        params = {
            "INPUT": layer,
            "TARGET_CRS": novo_crs,
            "OUTPUT": "memory:"}
        try:
            resultado = processing.run("native:reprojectlayer", params)
        except Exception as e:
            self.mostrar_mensagem(self.tr("Erro ao reprojetar: {error}").format(error=e), "Erro")
            return

        nova_camada = resultado.get("OUTPUT")
        if not nova_camada or not nova_camada.isValid():
            self.mostrar_mensagem(self.tr("Erro na reprojeção da camada '{layer_name}'.").format(layer_name=layer.name()), "Erro")
            return

        # Nome único para a nova camada
        novo_nome = self.gerar_nome_unico_rep(layer.name())
        nova_camada.setName(novo_nome)

        # Copiar estilo (simbologia + rótulos) da camada original
        copiou_estilo = False
        try:
            estilo = QgsMapLayerStyle()
            if estilo.readFromLayer(layer):
                estilo.writeToLayer(nova_camada)
                copiou_estilo = True
        except Exception:
            copiou_estilo = False

        if not copiou_estilo:
            # Fallback manual: renderer + labeling + propriedades visuais comuns
            try:
                if layer.renderer():
                    nova_camada.setRenderer(layer.renderer().clone())
            except Exception:
                pass  # nosec B110
            try:
                if layer.labelsEnabled() and layer.labeling():
                    nova_camada.setLabeling(layer.labeling().clone())
                    nova_camada.setLabelsEnabled(True)
            except Exception:
                pass  # nosec B110
            # Extras visuais úteis
            try:
                nova_camada.setOpacity(layer.opacity())
            except Exception:
                pass  # nosec B110
            try:
                nova_camada.setBlendMode(layer.blendMode())
            except Exception:
                pass  # nosec B110
            # Faixa de visibilidade por escala (se aplicável)
            try:
                nova_camada.setMinimumScale(layer.minimumScale())
                nova_camada.setMaximumScale(layer.maximumScale())
            except Exception:
                pass  # nosec B110

        # Adiciona a nova camada ao projeto
        QgsProject.instance().addMapLayer(nova_camada)

        # Garante que a camada recém-adicionada nasça marcada/visível
        try:
            root = QgsProject.instance().layerTreeRoot()
            node = root.findLayer(nova_camada.id())
            if node:
                node.setItemVisibilityChecked(True)
        except Exception:
            pass  # nosec B110

        # Atualiza a visualização/simbologia
        try:
            nova_camada.triggerRepaint()
            if hasattr(self.iface, "layerTreeView"):
                self.iface.layerTreeView().refreshLayerSymbology(nova_camada.id())
        except Exception:
            pass  # nosec B110

        # Sincroniza o treeView no próximo ciclo da UI
        try:
            QTimer.singleShot(0, self.sync_from_qgis_to_treeview)
        except Exception:
            self.sync_from_qgis_to_treeview()

        # Mensagem final
        texto_mensagem = self.tr("A camada '{layer_name}' foi reprojetada para {crs_authid} ({crs_description}) com o nome '{novo_nome}'.").format(layer_name=layer.name(), crs_authid=novo_crs.authid(), crs_description=novo_crs.description(), novo_nome=novo_nome)
        self.mostrar_mensagem(texto_mensagem, "Sucesso")

        # Opcional: focar/selecionar a nova camada no painel de camadas
        try:
            root = QgsProject.instance().layerTreeRoot()
            node = root.findLayer(nova_camada.id())
            if node:
                self.iface.layerTreeView().setCurrentLayer(nova_camada)
        except Exception:
            pass  # nosec B110

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
        Atualiza o treeView quando novas camadas de polígono são adicionadas ao projeto,
        aguardando um ciclo da UI para o nó da árvore do QGIS estabilizar.
        """
        polygon_layers = [
            layer for layer in layers
            if layer.type() == QgsMapLayer.LayerType.VectorLayer
            and layer.geometryType() == QgsWkbTypes.GeometryType.PolygonGeometry]

        if not polygon_layers:
            return

        for layer in polygon_layers:
            try:
                layer.nameChanged.disconnect(self.on_layer_name_changed)
            except TypeError:
                pass  # nosec B110
            layer.nameChanged.connect(self.on_layer_name_changed)

        def _refresh_after_qgis_tree_settles():
            self.atualizar_treeView_lista_poligono()
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
        self.atualizar_treeView_lista_poligono()

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

    def on_treeview_selection_changed(self, selected, deselected):
        """
        Define a camada ativa no QGIS com base na seleção do TreeView.

        Funcionalidades:
        - Acessa os índices selecionados no TreeView.
        - Recupera o ID da camada associado ao item selecionado.
        - Define a camada correspondente como ativa no QGIS (iface.setActiveLayer).
        """
        # Obtém os índices selecionados no TreeView
        indexes = self.dlg.treeViewListaPoligono.selectionModel().selectedIndexes()
        if indexes:
            # Recupera o ID da camada a partir do primeiro item selecionado
            layer_id = self.treeViewModel.itemFromIndex(indexes[0]).data(Qt.ItemDataRole.UserRole)
            # Obtém a camada no projeto QGIS através do ID
            layer = QgsProject.instance().mapLayer(layer_id)
            if layer:
                # Define a camada como ativa no QGIS
                self.iface.setActiveLayer(layer)

    def on_current_layer_changed(self, layer):
        """
        Atualiza a seleção do treeView quando a camada ativa do QGIS muda.

        Funcionalidades:
        - Verifica se a nova camada ativa é uma camada vetorial de polígonos.
        - Percorre o modelo do treeView para encontrar o item correspondente ao ID da nova camada.
        - Se encontrar, seleciona e rola até o item correspondente no treeView.

        Parâmetro:
        - layer (QgsMapLayer): Nova camada ativa no QGIS.
        """
        # Obtém o modelo associado ao treeView de polígonos
        model = self.dlg.treeViewListaPoligono.model()

        # Verifica se a camada é válida, do tipo vetorial e com geometria de polígono
        if layer and layer.type() == QgsMapLayer.LayerType.VectorLayer and layer.geometryType() == QgsWkbTypes.GeometryType.PolygonGeometry:
            layer_id = layer.id()  # Obtém o ID único da camada

            # Percorre as linhas do modelo do treeView
            for row in range(model.rowCount()):
                item = model.item(row, 0)

                # Verifica se o item corresponde ao ID da camada ativa
                if item and item.data(Qt.ItemDataRole.UserRole) == layer_id:
                    index = model.indexFromItem(item)

                    # Define a seleção atual e rola até a linha correspondente
                    self.dlg.treeViewListaPoligono.setCurrentIndex(index)
                    self.dlg.treeViewListaPoligono.scrollTo(index)
                    break  # Encerra após encontrar a camada correspondente

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

        model = self.dlg.treeViewListaPoligono.model()
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

    def atualizar_treeView_lista_poligono(self):
        """
        Atualiza o TreeView que lista as camadas de polígonos no QGIS.

        Funcionalidades:
        1) Salva o ID da camada atualmente selecionada no TreeView, se houver.
        2) Limpa e reconstrói o modelo do TreeView:
           - Define o cabeçalho centralizado.
           - Itera sobre todas as camadas do projeto e adiciona ao modelo apenas as camadas vetoriais de polígonos.
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
        current_index = self.dlg.treeViewListaPoligono.currentIndex()  # Índice selecionado no TreeView
        if current_index.isValid():  # Verifica se há uma seleção válida
            # Extrai o ID da camada do dado armazenado em Qt.UserRole
            current_layer_id = current_index.model().itemFromIndex(current_index).data(Qt.ItemDataRole.UserRole)

        # 2) Reconstrói o modelo do TreeView
        self.treeViewModel.clear()  # Limpa todos os itens existentes no modelo

        # Configura o cabeçalho da coluna com alinhamento central
        headerItem = QStandardItem(self.tr("Lista de Camadas de Polígonos"))  # Título do cabeçalho
        headerItem.setTextAlignment(Qt.AlignmentFlag.AlignCenter)  # Centraliza o texto
        self.treeViewModel.setHorizontalHeaderItem(0, headerItem)  # Aplica o cabeçalho

        # Pega a raiz da árvore de camadas do QGIS para verificar visibilidade
        root = QgsProject.instance().layerTreeRoot()
        # Itera por todas as camadas do projeto
        for layer in QgsProject.instance().mapLayers().values():
            # Seleciona apenas camadas vetoriais do tipo polígono
            if (
                layer.type() == QgsMapLayer.LayerType.VectorLayer
                and layer.geometryType() == QgsWkbTypes.GeometryType.PolygonGeometry):
                item = QStandardItem(layer.name())  # Cria o item com o nome da camada
                item.setCheckable(True)  # Permite marcar/desmarcar para visibilidade
                # Remove flag de edição para impedir alteração do nome pelo usuário
                item.setEditable(False)
                # Armazena o ID da camada no item para referência futura
                item.setData(layer.id(), Qt.ItemDataRole.UserRole)

                item.setCheckState(
                    Qt.CheckState.Checked
                    if self.camada_esta_visivel(layer)
                    else Qt.CheckState.Unchecked)

                # Aplica formatação de fonte: itálico para memória, negrito para outras
                self.adjust_item_font(item, layer)
                # Adiciona o item ao modelo, criando uma nova linha
                self.treeViewModel.appendRow(item)

        # 3) Restaura a seleção anterior, se possível
        model = self.dlg.treeViewListaPoligono.model()  # Modelo atualizado
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
            self.dlg.treeViewListaPoligono.setCurrentIndex(target_index)  # Seleciona
            self.dlg.treeViewListaPoligono.scrollTo(target_index)  # Move o scroll

        # Chama atualização dos botões após toda modificação
        self.atualizar_estado_botoes()
        self.sync_from_qgis_to_treeview()

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

    def clone_layer_poligono(self):
        """
        Clona uma camada de polígono selecionada no treeViewListaPoligono.

        Funcionalidades:
        - Recupera o índice da camada selecionada na interface (treeViewListaPoligono).
        - Obtém o ID real da camada salvo no Qt.UserRole.
        - Busca a camada correspondente no projeto QGIS.
        - Verifica se a camada existe e é do tipo polígono.
        - Cria uma instância do gerenciador de clonagem (CloneManagerP) para conduzir o processo.
        - Exibe as opções de clonagem para o usuário (geometria, atributos, tratamento, etc.).
        - Após a clonagem, atualiza a visualização do treeViewListaPoligono para refletir as novas camadas.

        Observações:
        - Garante que apenas camadas de polígono possam ser clonadas.
        - Exibe mensagens de erro apropriadas caso a seleção não seja válida.
        - Permite diferentes tipos de clonagem conforme as opções do usuário.
        """
        # Recupera índices selecionados no treeViewListaPoligono
        selected_indexes = self.dlg.treeViewListaPoligono.selectedIndexes()
        if not selected_indexes:
            # Nenhuma camada selecionada: exibe mensagem de erro
            self.mostrar_mensagem(self.tr("Nenhuma camada de polígono selecionada."), "Erro")
            return

        # Pega o primeiro índice selecionado (assumindo seleção simples)
        selected_index = selected_indexes[0]
        # Obtém o ID da camada salvo em Qt.UserRole
        layer_id = selected_index.data(Qt.ItemDataRole.UserRole)
        # Busca a camada correspondente no projeto
        layer_to_clone = QgsProject.instance().mapLayer(layer_id)

        if not layer_to_clone:
            # Camada não localizada (ID inválido ou removido)
            self.mostrar_mensagem(self.tr("Não foi possível localizar a camada no projeto."), "Erro")
            return

        # Garante que seja uma camada de polígono
        if layer_to_clone.geometryType() != QgsWkbTypes.GeometryType.PolygonGeometry:
            self.mostrar_mensagem(self.tr("A camada selecionada não é um polígono."), "Erro")
            return

        # Instancia o gerenciador de clonagem de polígonos
        clone_manager = CloneManagerP(self, layer_to_clone)
        # Exibe diálogo de opções de clonagem para o usuário
        clone_manager.show_clone_options()
        # Atualiza a árvore de camadas de polígono na interface
        self.atualizar_treeView_lista_poligono()  # Implemente igual ao das linhas

    def get_polygon_colors(self, layer):
        """
        Obtém as cores de preenchimento e borda de um polígono a partir da camada especificada.
        Este método acessa o renderizador da camada para extrair as configurações de cor atuais do símbolo do polígono.
        
        Funções e Ações Desenvolvidas:
        - Acesso ao renderizador da camada para obter os símbolos usados na renderização.
        - Extração da cor de preenchimento e da cor da borda do primeiro símbolo de polígono.
        - Retorno das cores obtidas ou (None, None) se as cores não puderem ser determinadas.
        
        :param layer: Camada do QGIS de onde as cores serão obtidas (deve ser uma camada de vetor de polígono).
        
        :return: Uma tupla contendo a cor de preenchimento e a cor da borda do polígono, respectivamente.
                 Retorna (None, None) se não conseguir extrair as cores.
        """
        # Acessa o renderizador da camada para obter a lista de símbolos usados na renderização
        symbols = layer.renderer().symbols(QgsRenderContext())
        if symbols:
            # Extrai a cor de preenchimento do primeiro símbolo (geralmente usado para o preenchimento de polígonos)
            fill_color = symbols[0].color()
            # Define uma cor padrão para a borda caso não seja especificada
            border_color = Qt.GlobalColor.black  # Cor padrão se não houver contorno definido
            # Verifica se há camadas de símbolo no símbolo do polígono
            if symbols[0].symbolLayerCount() > 0:
                border_layer = symbols[0].symbolLayer(0)
                # Se o símbolo da borda tiver uma propriedade de cor de borda, extrai essa cor
                if hasattr(border_layer, 'strokeColor'):
                    border_color = border_layer.strokeColor()
            # Retorna as cores de preenchimento e borda
            return fill_color, border_color
        # Retorna None para ambos se não houver símbolos ou se as cores não puderem ser determinadas
        return None, None

    def get_current_border_thickness(self, layer):
        """
        Recupera a espessura atual da borda de uma camada específica no QGIS. Este método acessa o renderizador da camada,
        e extrai a espessura da borda do primeiro símbolo de polígono encontrado, que é geralmente utilizado para a renderização
        das bordas dos polígonos.

        Funções e Ações Desenvolvidas:
        - Acesso ao renderizador da camada para obter os símbolos usados na renderização.
        - Extração da espessura da borda do primeiro símbolo de polígono se disponível.
        - Retorno da espessura atual da borda ou 0 se não for possível determinar.

        :param layer: Camada do QGIS cuja espessura da borda precisa ser obtida.
        :return: Espessura da borda da camada ou 0 se não for possível determinar a espessura.
        """
        # Acessa o renderizador da camada para obter a lista de símbolos utilizados
        symbols = layer.renderer().symbols(QgsRenderContext())
        if symbols and symbols[0].symbolLayerCount() > 0:
            # Extrai o primeiro símbolo de polígono, que é comumente usado para renderizar bordas
            border_layer = symbols[0].symbolLayer(0)
            # Verifica se o símbolo da borda possui um atributo para espessura da linha
            if hasattr(border_layer, 'strokeWidth'):
                # Retorna a espessura da borda se disponível
                return border_layer.strokeWidth()
        # Retorna 0 como valor padrão caso a espessura da borda não seja acessível ou não esteja definida
        return 0

    def apply_new_border_thickness(self, layer, thickness):
        """
        Aplica uma nova espessura de borda para a camada especificada no QGIS. Este método modifica diretamente
        o símbolo de polígono usado para renderizar a camada, garantindo que as alterações sejam visíveis imediatamente
        no mapa.

        Funções e Ações Desenvolvidas:
        - Acesso ao renderizador da camada para modificar a espessura da borda de cada símbolo de polígono.
        - Aplicação da nova espessura da borda.
        - Disparo de eventos para atualizar a visualização e a interface do usuário no QGIS.

        :param layer: Camada do QGIS que terá a espessura da borda ajustada.
        :param thickness: Nova espessura da borda a ser aplicada.
        """
        # Acessa o renderizador da camada para obter os símbolos usados na renderização
        symbols = layer.renderer().symbols(QgsRenderContext())
        if symbols:
            # Itera sobre cada símbolo na lista de símbolos da camada
            for symbol in symbols:
                # Verifica se há camadas de símbolo disponíveis no símbolo atual
                if symbol.symbolLayerCount() > 0:
                    border_layer = symbol.symbolLayer(0)
                    # Verifica se o símbolo da borda possui um método para definir a espessura da borda
                    if hasattr(border_layer, 'setStrokeWidth'):
                        # Aplica a nova espessura da borda
                        border_layer.setStrokeWidth(thickness)
            # Dispara o repintura da camada para atualizar a visualização no mapa
            layer.triggerRepaint()
            # Emite um sinal indicando que a camada foi adicionada para atualizar interfaces de usuário dependentes
            QgsProject.instance().layerWasAdded.emit(layer)
            # Refresca a simbologia da camada na árvore de camadas do QGIS
            self.iface.layerTreeView().refreshLayerSymbology(layer.id())

    def open_context_menu(self, position):
        """
        Cria e exibe um menu de contexto para ações específicas em um item selecionado no QTreeView.
        Este método é acionado com um clique do botão direito do mouse sobre um item da lista,
        apresentando opções como abrir propriedades da camada e alterar a espessura da borda da camada.

        Funções e Ações Desenvolvidas:
        - Verificação da seleção atual no QTreeView para determinar o item sobre o qual o menu será aberto.
        - Criação das opções do menu para manipulação das propriedades da camada e ajuste de sua espessura.
        - Execução do menu no local do clique e execução da ação selecionada.

        :param position: A posição do cursor no momento do clique, usada para posicionar o menu de contexto.
        """
        # Obtém os índices selecionados no QTreeView
        indexes = self.dlg.treeViewListaPoligono.selectedIndexes()
        if indexes:
            # Obter o índice da primeira coluna, que deve conter o ID da camada
            index = indexes[0].sibling(indexes[0].row(), 0)
            # Cria o menu de contexto
            menu = QMenu()
            # Adiciona opção para abrir propriedades da camada
            layer_properties_action = menu.addAction(self.tr("Abrir Propriedades da Camada"))
            # Adiciona opção para alterar a espessura da borda
            change_border_thickness_action = menu.addAction(self.tr("Espessura da Borda e Transparência"))
            # Exibe o menu no local do clique e aguarda ação do usuário
            action = menu.exec(self.dlg.treeViewListaPoligono.viewport().mapToGlobal(position))

            # Executa a ação correspondente à escolha do usuário
            if action == layer_properties_action:
                self.abrir_layer_properties(index)
            elif action == change_border_thickness_action:
                self.prompt_for_new_border_thickness(index)

    def prompt_for_new_border_thickness(self, index):
        """
        Exibe um diálogo modal para o usuário ajustar em tempo real a espessura da borda
        e a transparência (alfa) do preenchimento de uma camada de polígono QGIS,
        com ambos os controles agrupados em um QFrame sunken e o botão OK centralizado.

        Detalhamento do Processo:
        1. Recupera o ID da camada de polígono associada ao item selecionado no QTreeView.
        2. Obtém os valores atuais de espessura da borda e de transparência do preenchimento da camada.
        3. Cria um diálogo (QDialog) contendo:
            - Um QFrame em estilo "sunken" (rebaixado), agrupando os controles visuais.
            - Um QDoubleSpinBox para editar a espessura da borda (com atualização em tempo real).
            - Um QSlider horizontal para editar a transparência do preenchimento (com atualização em tempo real).
            - Um QLabel exibindo o valor percentual atual da opacidade.
        4. O botão "OK" fica centralizado logo abaixo do QFrame e fecha o diálogo ao ser pressionado.
        5. Enquanto o usuário interage com os controles:
            - Alterar o slider atualiza imediatamente a transparência do preenchimento da camada no mapa.
            - Alterar o spinbox atualiza imediatamente a espessura da borda da camada no mapa.
        6. O método não retorna valor — as alterações são persistidas diretamente na camada QGIS ao interagir.

        Parâmetros:
        - index (QModelIndex): Índice do item selecionado no QTreeView, utilizado para recuperar a camada alvo.

        Observações:
        - Não há botão de cancelar; o usuário pode fechar a janela a qualquer momento, mas todas as alterações são imediatas.
        - A função é adequada para ajuste visual rápido e intuitivo de camadas poligonais criadas tanto em memória quanto permanentes.
        """

        layer_id = index.model().itemFromIndex(index).data(Qt.ItemDataRole.UserRole)
        layer = QgsProject.instance().mapLayer(layer_id)
        if layer:
            current_thickness = self.get_current_border_thickness(layer)
            symbols = layer.renderer().symbols(QgsRenderContext())
            current_alpha = 255
            if symbols:
                fill_color = symbols[0].color()
                current_alpha = fill_color.alpha()

            # Diálogo principal
            dlg = QDialog(self.dlg)
            dlg.setWindowTitle(self.tr("Espessura da Borda e Transparência"))
            main_layout = QVBoxLayout(dlg)

            # Frame sunken (QFrame)
            frame = QFrame(dlg)
            frame.setFrameShape(QFrame.Shape.StyledPanel)
            frame.setFrameShadow(QFrame.Shadow.Sunken)
            frame_layout = QVBoxLayout(frame)

            # Linha: Espessura da Borda (texto à esquerda, spinbox à direita)
            row_border = QHBoxLayout()
            row_border.addWidget(QLabel(self.tr("Espessura da Borda:"), frame))
            spinBox = QDoubleSpinBox(frame)
            spinBox.setRange(0, 100)
            spinBox.setSingleStep(0.2)
            spinBox.setValue(current_thickness)
            spinBox.setDecimals(2)
            row_border.addWidget(spinBox)
            frame_layout.addLayout(row_border)

            # Espaçamento
            frame_layout.addSpacing(8)

            # Linha: Transparência do Preenchimento
            frame_layout.addWidget(QLabel(self.tr("Transparência do Preenchimento:"), frame))
            slider = QSlider(Qt.Orientation.Horizontal, frame)
            slider.setMinimum(0)      # 0 = totalmente transparente
            slider.setMaximum(255)    # 255 = totalmente opaco
            slider.setValue(current_alpha)

            # Label percentual à direita do slider
            percent_label = QLabel(frame)
            percent_label.setFixedWidth(70)
            percent_label.setAlignment(Qt.AlignmentFlag.AlignRight | Qt.AlignmentFlag.AlignVCenter)
            def update_label(val):
                percent_label.setText(self.tr("{percent}% opaco").format(percent=int(val / 255 * 100)))
            slider.valueChanged.connect(update_label)
            update_label(current_alpha)

            # Layout do slider + percentual
            slider_row = QHBoxLayout()
            slider_row.addWidget(slider)
            slider_row.addWidget(percent_label)
            frame_layout.addLayout(slider_row)

            # Adiciona o frame ao layout principal do diálogo
            main_layout.addWidget(frame)

            # Botão OK centralizado
            buttonLayout = QHBoxLayout()
            buttonLayout.addStretch(1)
            okButton = QPushButton(self.tr("OK"), dlg)
            buttonLayout.addWidget(okButton)
            buttonLayout.addStretch(1)
            main_layout.addLayout(buttonLayout)

            # Atualização da transparência em tempo real
            slider.valueChanged.connect(lambda val: self.apply_fill_opacity(layer, val))
            # Atualização da espessura da borda em tempo real
            spinBox.valueChanged.connect(lambda val: self.apply_new_border_thickness(layer, val))

            # Ação do OK
            okButton.clicked.connect(dlg.accept)

            # Exibe o diálogo
            dlg.exec()

    def apply_fill_opacity(self, layer, alpha):
        """
        Atualiza a opacidade (transparência) do preenchimento dos polígonos em uma camada,
        sem alterar a cor base, a cor da borda ou a espessura já definidas.

        Detalhamento do Processo:
        1. Obtém todos os símbolos (estilos de renderização) atualmente aplicados à camada.
        2. Para cada símbolo encontrado:
            - Recupera a cor de preenchimento do polígono.
            - Altera apenas o canal alfa (transparência) para o valor especificado.
            - Atualiza a cor do símbolo com o novo valor de opacidade.
        3. Solicita a repintura da camada, força a atualização da simbologia na árvore de camadas
           e emite sinal de atualização do QGIS.
        4. Não modifica a cor da borda, espessura ou outros estilos.

        Parâmetros:
        - layer (QgsVectorLayer): Camada de polígono cuja opacidade do preenchimento será alterada.
        - alpha (int): Novo valor de opacidade (0 = totalmente transparente, 255 = opaco).

        Observações:
        - Recomendado para uso com sliders ou widgets de transparência.
        - Funciona tanto para camadas temporárias quanto permanentes.
        - Preserva todos os outros estilos já aplicados ao polígono.
        """
        # Obtém todos os símbolos usados na renderização da camada (normalmente apenas 1)
        symbols = layer.renderer().symbols(QgsRenderContext())
        if symbols:
            for symbol in symbols:
                color = symbol.color()      # Recupera a cor de preenchimento do símbolo
                color.setAlpha(alpha)       # Atualiza apenas o canal alfa (transparência)
                symbol.setColor(color)      # Aplica a nova cor ao símbolo (mantendo RGB original)
            layer.triggerRepaint()          # Solicita a repintura da camada no mapa
            QgsProject.instance().layerWasAdded.emit(layer)  # Emite sinal de atualização de camada (refresca painéis QGIS)
            self.iface.layerTreeView().refreshLayerSymbology(layer.id())  # Atualiza a simbologia na árvore de camadas

    def prompt_for_new_colors(self, current_fill_color, current_border_color, parent=None):
        """
        Fluxo completo de seleção de cor:
          • Cancela borda   → borda transparente (mas segue para preenchimento).
          • Cancela preenchimento → preenchimento transparente (mas aplica borda).
          • Cancela AMBOS  → retorna (None, None)   → o chamador não faz nenhuma alteração.
          • Se escolher nova cor de preenchimento:
              - Se o alpha atual é 0  → força alpha 255 (slider volta a 100 %).
              - Caso contrário        → mantém o alpha atual.
        """
        parent = parent or self.dlg
        # Diálogo da BORDA
        border_qc = QColorDialog.getColor(current_border_color, parent, self.tr("Escolha a Cor da Borda"))
        border_valid = border_qc.isValid()
        new_border = border_qc if border_valid else QColor(0, 0, 0, 0)   # transparente

        # Diálogo do PREENCHIMENTO
        fill_qc = QColorDialog.getColor(current_fill_color, parent, self.tr("Escolha a Cor de Preenchimento"))
        fill_valid = fill_qc.isValid()

        # Se cancelou ambos, não altera nada
        if not border_valid and not fill_valid:
            return None, None

        if fill_valid:
            current_alpha = current_fill_color.alpha()
            fill_qc.setAlpha(255 if current_alpha == 0 else current_alpha)
            new_fill = fill_qc
        else:
            new_fill = QColor(0, 0, 0, 0)  # transparente

        return new_fill, new_border

    def apply_new_colors(self, layer, fill_color, border_color):
        """
        Aplica novas cores preservando espessura e usando o alpha que vier no QColor.
        """
        symbols = layer.renderer().symbols(QgsRenderContext())

        # Obtém strokeWidth existente
        stroke = 0.26
        if symbols and symbols[0].symbolLayerCount():
            bl = symbols[0].symbolLayer(0)
            if hasattr(bl, 'strokeWidth'):
                stroke = bl.strokeWidth()

        # Novo símbolo
        sym = QgsSymbol.defaultSymbol(layer.geometryType())
        sym.setColor(fill_color)                               # mantém alpha recebido
        sym.symbolLayer(0).setStrokeColor(border_color)
        sym.symbolLayer(0).setStrokeWidth(stroke)              # preserva espessura

        layer.setRenderer(QgsSingleSymbolRenderer(sym))
        layer.triggerRepaint()
        QgsProject.instance().layerWasAdded.emit(layer)
        self.iface.layerTreeView().refreshLayerSymbology(layer.id())

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
            current_fill_color, current_border_color = self.get_polygon_colors(layer)
            # Solicita ao usuário que selecione novas cores para preenchimento e borda
            new_fill_color, new_border_color = self.prompt_for_new_colors(
                current_fill_color, current_border_color)

            # Aplica somente se o usuário confirmou os DOIS diálogos
            if new_fill_color is not None and new_border_color is not None:
                self.apply_new_colors(layer, new_fill_color, new_border_color)

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

    def abrir_dialogo_selecao_campos_poligono(self):
        """
        Abre o diálogo de gerenciamento de etiquetas para a camada de polígonos selecionada no treeViewListaPoligono.

        Detalhamento do Processo:
        1. Obtém o índice atualmente selecionado no QTreeView de camadas de polígonos.
        2. Garante que exista pelo menos uma seleção válida; caso contrário, retorna sem ação.
        3. Garante que sempre será utilizada a coluna zero do modelo (onde está armazenado o ID da camada).
        4. Recupera o ID único da camada selecionada usando o papel Qt.UserRole (garante que não será confundido com o nome da camada).
        5. Busca a camada correspondente no projeto QGIS utilizando o ID recuperado.
        6. Verifica se a camada existe e se é do tipo polígono; retorna se não atender a esses critérios.
        7. Cria uma instância do diálogo GerenciarEtiquetasDialog, passando:
           - a camada selecionada,
           - os dicionários de cores e visibilidade de campo (armazenam as preferências do usuário),
           - a interface do QGIS (iface),
           - e o diálogo principal como parent.
        8. Exibe o diálogo de gerenciamento de etiquetas de forma modal (`exec_()`), permitindo ao usuário configurar campos e estilos de etiquetas.
        9. Ao fechar o diálogo, as configurações de etiquetas podem ser aplicadas na camada.

        A função melhora a usabilidade do plugin, permitindo ao usuário controlar de forma visual e centralizada como as informações dos polígonos serão exibidas via etiquetas no mapa.
        """
        # Obtém todos os índices selecionados no treeView de polígonos
        selected_indexes = self.dlg.treeViewListaPoligono.selectedIndexes()
        if not selected_indexes:
            # Se nenhum item está selecionado, interrompe a função
            return

        # Garante o uso da coluna zero, onde está o ID da camada
        selected_index = selected_indexes[0].sibling(selected_indexes[0].row(), 0)

        # Recupera o ID da camada a partir do Qt.UserRole (não o texto/nome)
        layer_id = selected_index.model().itemFromIndex(selected_index).data(Qt.ItemDataRole.UserRole)

        # Busca a camada no projeto QGIS pelo ID
        layer = QgsProject.instance().mapLayer(layer_id)
        if not layer or layer.geometryType() != QgsWkbTypes.GeometryType.PolygonGeometry:
            # Se não encontrou camada válida de polígonos, interrompe
            return

        # Instancia o diálogo de gerenciamento de etiquetas, passando os parâmetros necessários
        dialog = GerenciarEtiquetasDialog(layer, self.fieldColors, self.fieldVisibility, self.iface, self.dlg)

        # Exibe o diálogo de forma modal (bloqueia a janela principal até fechar)
        dialog.exec()

    def _adicionar_arquivo_por_caminho(self, file_path: str) -> bool:
        """
        Adiciona um arquivo ao projeto usando o mesmo fluxo do botão, sem abrir QFileDialog.

        Para KML/KMZ:
        - cria/reaproveita grupo;
        - adiciona todas as camadas poligonais dentro do grupo;
        - remove .kml/.kmz dos nomes;
        - remove o nome do grupo do nome das camadas.
        """
        if not file_path:
            return False

        layer_name = self._limpar_nome_kml_kmz(os.path.basename(file_path))
        ext = os.path.splitext(file_path)[1].lower()

        start_time = time.time()

        project = QgsProject.instance()
        root = project.layerTreeRoot()
        layers_to_add: list[QgsVectorLayer] = []

        def _nome_unico_no_projeto(nome: str) -> str:
            base = (nome or layer_name).strip()
            nomes_existentes = {lyr.name() for lyr in project.mapLayers().values() if lyr}

            if base not in nomes_existentes:
                return base

            numero = 2
            novo_nome = f"{base} ({numero})"

            while novo_nome in nomes_existentes:
                numero += 1
                novo_nome = f"{base} ({numero})"

            return novo_nome

        def _add_layer(lyr: QgsVectorLayer, group=None):
            if not lyr or not lyr.isValid():
                return False

            lyr.setName(_nome_unico_no_projeto(lyr.name()))

            if group is not None:
                # Adiciona ao projeto sem criar nó automático na raiz
                project.addMapLayer(lyr, False)

                # Adiciona a camada diretamente dentro do grupo
                node = group.addLayer(lyr)

                # Se por algum motivo existir nó direto na raiz, remove apenas esse nó
                try:
                    for child in list(root.children()):
                        if isinstance(child, QgsLayerTreeLayer) and child.layerId() == lyr.id():
                            root.removeChildNode(child)
                except Exception:
                    pass  # nosec B110

                if node is not None:
                    node.setItemVisibilityChecked(True)

            else:
                project.addMapLayer(lyr)

                node = root.findLayer(lyr.id())
                if node is not None:
                    node.setItemVisibilityChecked(True)

            return True

        # DXF
        if ext == ".dxf":
            poly_layer, text_layer = self._processar_dxf_poligonos(file_path, layer_name)

            if poly_layer is None and text_layer is None:
                return False

            if poly_layer:
                layers_to_add.append(poly_layer)

            if text_layer:
                layers_to_add.append(text_layer)

        # KML/KMZ
        elif ext in (".kml", ".kmz"):
            res = self._processar_kml_kmz_poligonos(file_path, layer_name) or []

            if isinstance(res, QgsVectorLayer):
                layers_to_add = [res]
            elif isinstance(res, (list, tuple)):
                layers_to_add = [layer
                    for layer in res
                    if layer and layer.isValid()]
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

            mem = self._copiar_para_memoria_poligono(origem, layer_name)
            del origem

            if mem and mem.isValid():
                layers_to_add = [mem]
            else:
                return False

        # Grupo para KML/KMZ, mesmo quando vier apenas uma camada
        group = None
        if ext in (".kml", ".kmz"):
            group_name = self._inferir_nome_grupo_kml(layer_name, layers_to_add)

            group = root.findGroup(group_name)
            if group is None:
                group = root.addGroup(group_name)

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

        self.atualizar_treeView_lista_poligono()
        return True

    def abrir_adicionar_arquivo(self):
        """
        Abre o diálogo para selecionar e adicionar um arquivo de polígonos.
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

        file_path, _ = QFileDialog.getOpenFileName(self.dlg, self.tr("Abrir Arquivo"), "", file_filter)

        if not file_path:
            return

        try:
            ok = self._adicionar_arquivo_por_caminho(file_path)

            if not ok:
                self.mostrar_mensagem(self.tr("Nenhuma feição de polígono encontrada ou o arquivo não pôde ser carregado."), "Aviso")

        except Exception as e:
            self.mostrar_mensagem(self.tr("Erro ao adicionar arquivo: {error}").format(error=e), "Erro")

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

    def exportar_para_dxf(self):
        """
        Gerencia a exportação de uma camada selecionada para um arquivo DXF. Este método inclui várias etapas:
        seleção da camada, configuração das opções de exportação e salvamento do arquivo.

        Funções e Ações Desenvolvidas:
        - Seleção de uma camada para exportação.
        - Exibição de um diálogo para definir opções de exportação.
        - Escolha de local para salvar o arquivo.
        - Exportação da camada para o formato DXF.
        - Feedback sobre o sucesso ou falha da exportação.
        """
        # Obtém a seleção atual no QTreeView
        indexes = self.dlg.treeViewListaPoligono.selectionModel().selectedIndexes()
        if not indexes:
            self.mostrar_mensagem(self.tr("Selecione uma camada para exportar."), "Erro")
            return

        # Obtém o nome da camada selecionada
        idx = next((i for i in indexes if i.column() == 0), indexes[0])
        item = self.treeViewModel.itemFromIndex(idx)
        layer_id = item.data(Qt.ItemDataRole.UserRole)
        layer = QgsProject.instance().mapLayer(layer_id)

        if not layer:
            self.mostrar_mensagem(self.tr("Camada não encontrada."), "Erro")
            return

        # Inicializando e exibindo o diálogo de exportação
        dialogo_exportacao = ExportacaoDialogoDXF(layer, self)
        if dialogo_exportacao.exec() != QDialog.DialogCode.Accepted:
            return              # cancelado pelo usuário

        # Parâmetros escolhidos
        campo_camada, campo_rotulo, ezdxf_pattern, escala, rotacao, transparencia = dialogo_exportacao.Obter_Valores()
        if not dialogo_exportacao.checkBoxCampoRotulo.isChecked():
            campo_rotulo = None  # não exportar rótulos

        nome_padrao = f"{layer.name()}.dxf"
        tipo_arquivo = self.tr("Arquivos DXF (*.dxf)")
        fileName     = self.escolher_local_para_salvar(nome_padrao, tipo_arquivo)
        if not fileName:
            return              # usuário desistiu

        # Exportação propriamente dita
        inicio = time.time()
        self.salvar_camada_como_dxf(
            layer, fileName,
            campo_camada,
            campo_rotulo,
            ezdxf_pattern,
            escala,
            rotacao,
            transparencia)
        duracao = time.time() - inicio

        self.mostrar_mensagem(self.tr("Arquivo DXF salvo com sucesso em {duracao:.2f} s").format(duracao=duracao), "Sucesso", caminho_pasta=os.path.dirname(fileName), caminho_arquivos=fileName)

    def salvar_camada_como_dxf(self, layer, fileName, nome_atributo, nome_campo_rotulo, ezdxf_pattern, escala, rotacao, transparencia=0.0):
        """
        Exporta uma camada de polígonos para DXF com hachura, borda e rótulos.

        Correções:
        - ignora feições com geometria nula;
        - ignora feições com geometria vazia;
        - trata Polygon e MultiPolygon com segurança;
        - evita erro: ValueError: Null geometry cannot be converted to a polygon.
        """
        # Inicia a barra de progresso
        progressBar, progressMessageBar = self.iniciar_progress_bar(layer)

        # Criação do documento DXF
        doc = ezdxf.new(dxfversion='R2010')
        msp = doc.modelspace()

        # Obter cores de preenchimento e borda
        fill_color, border_color = self.obter_cores_da_camada(layer)

        # Transparência DXF:
        # 0%   = opaco
        # 100% = totalmente transparente
        try:
            transparencia_float = max(0.0, min(100.0, float(transparencia))) / 100.0
        except Exception:
            transparencia_float = 0.0

        try:
            dxf_transparency = colors.float2transparency(transparencia_float)
        except Exception:
            dxf_transparency = None

        # Nome da camada DXF
        nome_camada_dxf = nome_atributo or layer.name()

        processed_features = 0
        exported_features = 0
        ignored_features = 0

        def _ring_to_dxf_points(ring):
            """
            Converte anel QGIS para lista de tuplas aceitas pelo ezdxf.
            """
            pts = []

            if not ring:
                return pts

            for p in ring:
                try:
                    pts.append((float(p.x()), float(p.y())))
                except Exception:
                    try:
                        pts.append((float(p[0]), float(p[1])))
                    except Exception:
                        pass  # nosec B110

            # Um polígono precisa de pelo menos 3 vértices úteis
            if len(pts) < 3:
                return []

            # Garante fechamento do anel
            if pts[0] != pts[-1]:
                pts.append(pts[0])

            return pts

        def _iter_polygon_parts(geometry):
            """
            Retorna polígonos preservando anel externo e anéis internos.
            Cada item retornado é uma lista de rings:
            [anel_externo, anel_interno_1, anel_interno_2, ...]
            """
            if geometry is None:
                return []

            try:
                if geometry.isNull() or geometry.isEmpty():
                    return []
            except Exception:
                return []

            try:
                if QgsWkbTypes.geometryType(geometry.wkbType()) != QgsWkbTypes.GeometryType.PolygonGeometry:
                    return []
            except Exception:
                return []

            parts = []

            # Garante que geometrias curvas do QGIS sejam convertidas
            # em segmentos suficientemente densos antes da exportação DXF.
            try:
                if QgsWkbTypes.isCurvedType(geometry.wkbType()):
                    geometry = QgsGeometry(geometry)

                    geometry.convertToStraightSegment(math.radians(1.0))

            except Exception:
                pass  # nosec B110

            try:
                polygons = geometry.asMultiPolygon() if geometry.isMultipart() else [geometry.asPolygon()]

                for polygon in polygons:
                    if not polygon:
                        continue

                    rings = []
                    for ring in polygon:
                        pts = _ring_to_dxf_points(ring)
                        if pts:
                            rings.append(pts)

                    if rings:
                        parts.append(rings)

            except Exception:
                return []

            return parts

        try:
            for feature in layer.getFeatures():
                geometry = feature.geometry()
                polygon_parts = _iter_polygon_parts(geometry)

                if not polygon_parts:
                    ignored_features += 1
                    processed_features += 1
                    try:
                        progressBar.setValue(processed_features)
                    except Exception:
                        pass  # nosec B110
                    continue

                for rings in polygon_parts:
                    try:
                        hatch = msp.add_hatch()
                        hatch.dxf.hatch_style = 0

                        hatch.set_pattern_fill(ezdxf_pattern, scale=escala, angle=rotacao)
                        hatch.dxf.true_color = fill_color
                        hatch.dxf.layer = nome_camada_dxf

                        if dxf_transparency is not None and transparencia_float > 0:
                            try:
                                hatch.dxf.transparency = dxf_transparency
                            except Exception:
                                pass  # nosec B110

                        for ring in rings:
                            hatch.paths.add_polyline_path(ring, is_closed=True)

                            msp.add_lwpolyline(
                                ring,
                                close=True,
                                dxfattribs={
                                    "true_color": border_color,
                                    "layer": nome_camada_dxf})

                        exported_features += 1

                    except Exception:  # nosec B112
                        ignored_features += 1
                        continue

                processed_features += 1
                try:
                    progressBar.setValue(processed_features)
                except Exception:
                    pass  # nosec B110

            # Rótulos também precisam ignorar geometria nula
            self.exportar_rotulos_para_dxf(msp, layer, nome_campo_rotulo)

            doc.saveas(fileName)

            if ignored_features > 0:
                self.mostrar_mensagem(self.tr("DXF exportado. {ignored_features} feição(ões) sem geometria válida foram ignoradas.").format(ignored_features=ignored_features), "Aviso", duracao=3)

        finally:
            try:
                self.iface.messageBar().popWidget(progressMessageBar)
            except Exception:
                try:
                    self.iface.messageBar().clearWidgets()
                except Exception:
                    pass  # nosec B110

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

    def obter_cores_da_camada(self, layer):
        """
        Obtém as cores de preenchimento e borda de uma camada específica no QGIS. Este método considera diferentes tipos
        de renderizadores e extrai as cores do primeiro símbolo disponível ou de uma categoria específica.

        Funções e Ações Desenvolvidas:
        - Determinação do tipo de renderizador usado pela camada.
        - Extração do símbolo usado para o desenho da camada.
        - Obtenção da cor de preenchimento e, se disponível, da cor da borda.
        - Conversão das cores RGB para o formato de inteiro usado em arquivos DXF.

        :param layer: Camada do QGIS da qual as cores serão obtidas.
        :return: Uma tupla contendo as cores de preenchimento e borda no formato inteiro para uso em DXF.
        """
        # Define cores padrão em caso de não conseguir extrair do renderizador
        fill_color = (0, 0, 0)  # Preto como cor padrão de preenchimento
        border_color = (0, 0, 0)  # Preto como cor padrão da borda
        symbol = None
        fill_color_tuple = (0, 0, 0)  # Inicializa com preto padrão
        border_color_tuple = (0, 0, 0)  # Inicializa com preto padrão

        # Obtém o renderizador da camada e determina o tipo
        renderer = layer.renderer()
        if isinstance(renderer, QgsCategorizedSymbolRenderer):
            # Se for um renderizador categorizado, extrai o símbolo da primeira categoria
            for category in renderer.categories():
                symbol = category.symbol()
                break  # Pegar o símbolo da primeira categoria apenas para exemplo
        elif isinstance(renderer, QgsSingleSymbolRenderer):
            # Se for um renderizador de símbolo único, usa esse símbolo diretamente
            symbol = renderer.symbol()

        # Se um símbolo foi obtido, extrai as cores
        if symbol:
            fill_color = symbol.color()
            fill_color_tuple = (fill_color.red(), fill_color.green(), fill_color.blue())

            # Tenta obter a camada de símbolo de linha para a cor da borda
            border_symbol_layer = symbol.symbolLayers()[0] if symbol.symbolLayerCount() > 0 else None
            if border_symbol_layer and hasattr(border_symbol_layer, 'strokeColor'):
                border_color = border_symbol_layer.strokeColor()
                border_color_tuple = (border_color.red(), border_color.green(), border_color.blue())
            else:
                border_color_tuple = fill_color_tuple  # Usa a cor de preenchimento se não houver cor de borda específica

        # Converte as cores RGB para o formato de inteiro usado em arquivos DXF
        fill_color_int = ezdxf.colors.rgb2int(fill_color_tuple)
        border_color_int = ezdxf.colors.rgb2int(border_color_tuple)

        return fill_color_int, border_color_int

    def exportar_rotulos_para_dxf(self, msp, layer, nome_campo_rotulo):
        """
        Adiciona rótulos ao DXF com base no campo especificado.

        Correções:
        - ignora feições sem geometria;
        - ignora geometrias vazias;
        - evita asPolygon() em geometria nula;
        - usa pointOnSurface como alternativa segura ao centroid.
        """
        if not nome_campo_rotulo:
            return

        try:
            if layer.fields().indexOf(nome_campo_rotulo) == -1:
                return
        except Exception:
            return

        doc = msp.doc

        if "BoldStyle" not in doc.styles:
            doc.styles.new(
                "BoldStyle",
                dxfattribs={'font': 'Calibri Light'})

        for feature in layer.getFeatures():
            geometry = feature.geometry()

            if geometry is None:
                continue

            try:
                if geometry.isNull() or geometry.isEmpty():
                    continue
            except Exception:
                try:
                    if geometry.isEmpty():
                        continue
                except Exception:  # nosec B112
                    continue

            try:
                if QgsWkbTypes.geometryType(geometry.wkbType()) != QgsWkbTypes.GeometryType.PolygonGeometry:
                    continue
            except Exception:  # nosec B112
                continue

            try:
                ponto_geom = geometry.pointOnSurface()
                if not ponto_geom or ponto_geom.isEmpty():
                    ponto_geom = geometry.centroid()

                if not ponto_geom or ponto_geom.isEmpty():
                    continue

                ponto_central = ponto_geom.asPoint()
            except Exception:  # nosec B112
                continue

            try:
                rotulo = str(feature[nome_campo_rotulo])
            except Exception:
                rotulo = ""

            if not rotulo:
                continue

            try:
                msp.add_text(
                    rotulo,
                    dxfattribs={
                        'insert': (ponto_central.x(), ponto_central.y()),
                        'height': 1,
                        'style': 'BoldStyle',
                        'width': 1.5,
                        'oblique': 15})

            except Exception:
                pass  # nosec B110

    def obter_cores(self, layer):
        """
        Obtém as cores de borda e preenchimento de uma camada de polígonos.

        Esta função verifica se a camada é uma camada de polígonos, e se sim, extrai as cores de borda e preenchimento
        do símbolo da camada. Se as cores não puderem ser obtidas, a função retorna cores padrão (branco opaco).

        Args:
        - layer: A camada de mapa cujas cores serão obtidas.

        Returns:
        - Uma tupla contendo as cores de borda e preenchimento no formato KML (ARGB).
        """
        # Define a cor branca opaca como padrão
        cor_linha_kml = "ffffffff"  # Branco opaco para borda
        cor_preenchimento_kml = "ffffffff"  # Branco opaco para preenchimento

        if layer.type() == QgsMapLayer.LayerType.VectorLayer and layer.geometryType() == QgsWkbTypes.GeometryType.PolygonGeometry:
            renderer = layer.renderer()
            simbologia = None

            # Checa se o renderer suporta o método symbol()
            if hasattr(renderer, 'symbol'):
                try:
                    simbologia = renderer.symbol()
                except Exception:
                    pass  # nosec B110

            if simbologia and simbologia.symbolLayerCount() > 0:
                # Pega a primeira camada de símbolo para borda
                symbolLayer = simbologia.symbolLayer(0)
                if hasattr(symbolLayer, 'strokeColor'):  # Verifica se a camada do símbolo tem cor de borda
                    cor_linha = symbolLayer.strokeColor()
                    if cor_linha.isValid():
                        cor_linha_kml = self.cor_qgis_para_kml(cor_linha)

                # Cor de preenchimento
                if hasattr(simbologia, 'color'):
                    cor_preenchimento = simbologia.color()
                    if cor_preenchimento.isValid():
                        cor_preenchimento_kml = self.cor_qgis_para_kml(cor_preenchimento)

        return cor_linha_kml, cor_preenchimento_kml

    def cor_qgis_para_kml(self, cor_qgis):
        """
        Converte uma cor do QGIS para o formato de cor KML (aabbggrr).
        """
        # Converte os componentes RGB e alfa para hexadecimal
        a = format(cor_qgis.alpha(), '02x')
        b = format(cor_qgis.blue(), '02x')
        g = format(cor_qgis.green(), '02x')
        r = format(cor_qgis.red(), '02x')
        # Retorna a cor no formato KML
        return a + b + g + r

    def _limpar_nome_kml_kmz(self, nome: str) -> str:
        """
        Limpa nomes vindos de KML/KMZ:
        - remove caminho completo;
        - remove .kml/.kmz;
        - remove resíduos de URI do OGR;
        - organiza espaços e separadores.
        """
        nome = str(nome or "").strip()

        # Se vier caminho completo
        nome = os.path.basename(nome)

        # Se vier URI do OGR
        nome = nome.replace("|layername=", "_")

        # Remove .kml/.kmz no final
        nome = re.sub(r"\.(kml|kmz)$", "", nome, flags=re.IGNORECASE)

        # Limpeza final
        nome = re.sub(r"\s+", " ", nome)
        nome = nome.strip(" _-|")

        return nome or self.tr("Camada")

    def _inferir_nome_grupo_kml(self, nome_arquivo: str, layers: list) -> str:
        """
        Tenta identificar o nome do grupo a partir do prefixo comum das camadas.

        Exemplo:
        - 'Lugares temporários Talhão 1'
        - 'Lugares temporários Talhão 2'
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
        Garante nomes únicos dentro do lote importado.
        """
        base = self._limpar_nome_kml_kmz(nome)
        nome_final = base
        i = 1

        while nome_final.lower() in usados:
            nome_final = f"{base}_{i}"
            i += 1

        usados.add(nome_final.lower())
        return nome_final

    def gerar_cor_suave(self):
        """
        Gera uma cor suave em formato hexadecimal.

        Esta função cria uma cor suave, selecionando valores aleatórios para os componentes
        vermelho (R), verde (G) e azul (B) dentro de um intervalo alto (180 a 255), garantindo
        que a cor gerada seja relativamente clara. Isso é útil para fundos de texto ou elementos
        gráficos que precisam ser suavemente coloridos sem dominar o conteúdo sobreposto.

        Retorna:
        - Uma string representando a cor no formato hexadecimal (ex: '#ffeedd').
        """
        # Cor aleatória usada somente para apresentação visual.
        r = random.randint(180, 255)  # nosec B311
        g = random.randint(180, 255)  # nosec B311
        b = random.randint(180, 255)  # nosec B311

        return f"#{r:02x}{g:02x}{b:02x}" # Retorna a cor formatada como uma string hexadecimal

    def exportar_para_kml(self):
        """
        Exporta uma camada selecionada para um arquivo KML.

        Esta função realiza as seguintes etapas:
        1. Verifica se alguma camada está selecionada na treeView.
        2. Obtém a camada selecionada.
        3. Abre o diálogo para configuração da exportação.
        4. Se o diálogo for aceito, obtém os valores fornecidos pelo usuário.
        5. Define o nome padrão e o tipo de arquivo para salvar.
        6. Solicita ao usuário o local para salvar o arquivo.
        7. Cria uma barra de progresso para acompanhar o processo de exportação.
        8. Inicia a exportação da camada para KML em memória.
        9. Escreve o conteúdo KML no arquivo especificado.
        10. Limpa a barra de progresso após a conclusão.
        11. Exibe uma mensagem de sucesso após a exportação.

        Returns:
        - None
        """
        # Obtém a seleção atual no QTreeView
        indexes = self.dlg.treeViewListaPoligono.selectionModel().selectedIndexes()
        if not indexes:
            self.mostrar_mensagem(self.tr("Selecione uma camada para exportar."), "Erro")
            return

        # Obtém o nome da camada selecionada
        idx = next((i for i in indexes if i.column() == 0), indexes[0])
        item = self.treeViewModel.itemFromIndex(idx)
        layer_id = item.data(Qt.ItemDataRole.UserRole)
        layer = QgsProject.instance().mapLayer(layer_id)

        if not layer:
            self.mostrar_mensagem(self.tr("Camada não encontrada."), "Erro")
            return

        dialog = ExportarKMLDialog(layer, self.dlg)
        if dialog.exec() == QDialog.DialogCode.Accepted:
            values = dialog.getValues()  # Obter valores usando a função getValues
            selected_field, include_table, line_width, line_opacity, area_opacity, height, use_3d, is_elevated, is_solido, is_edges, image_url, overlay_url = values
            
        else:
            self.mostrar_mensagem(self.tr("Exportação cancelada."), "Info")
            return # Usuário cancelou a operação

        nome_padrao = f"{layer.name()}.kml"
        tipo_arquivo = f"{self.tr('Arquivos KML')} (*.kml)"
        caminho_arquivo = self.escolher_local_para_salvar(nome_padrao, tipo_arquivo)
        if not caminho_arquivo:
            self.mostrar_mensagem(self.tr("Exportação cancelada."), "Info")
            return  # Usuário cancelou a seleção do arquivo para salvar

        # Inicia a barra de progresso
        progressBar, progressMessageBar = self.iniciar_progress_bar(layer)

        feature_count = layer.featureCount()
        progressBar.setMaximum(feature_count)

        # Medir o tempo de execução da criação do KML e da escrita no arquivo
        start_time = time.time()

        # Iniciando a exportação
        kml_element = self.criar_kml_em_memoria(layer, selected_field, include_table, line_width, line_opacity, area_opacity, height, use_3d, is_elevated, is_solido, is_edges, image_url, overlay_url, progressBar)

        tree = XmlET.ElementTree(kml_element)
        tree.write(caminho_arquivo, xml_declaration=True, encoding='utf-8', method="xml")

        end_time = time.time()

        # Calcula o tempo de execução
        execution_time = end_time - start_time

        self.iface.messageBar().clearWidgets()  # Remove a barra de progresso após a conclusão

        # Exibir mensagem de sucesso com o tempo de execução e caminhos dos arquivos
        self.mostrar_mensagem(self.tr("Camada exportada para KML em {execution_time:.2f} segundos").format(execution_time=execution_time), "Sucesso", caminho_pasta=os.path.dirname(caminho_arquivo), caminho_arquivos=caminho_arquivo)

    def redimensionar_imagem_proporcional_url(self, url_imagem, largura_max, altura_max):
        """
        Baixa imagem de um URL e redimensiona proporcionalmente.

        Otimização:
        - Cache por (url, largura_max, altura_max) para não baixar/redimensionar repetidas vezes.
        - Timeout no requests.get para evitar travas em URL lenta.
        """
        if not url_imagem:
            return None, None, None

        # Cache na instância
        if not hasattr(self, "_img_resize_cache"):
            self._img_resize_cache = {}

        key = (str(url_imagem), int(largura_max), int(altura_max))
        if key in self._img_resize_cache:
            return self._img_resize_cache[key]

        headers = {'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120 Safari/537.36'}
        try:
            response = requests.get(url_imagem, headers=headers, timeout=10)
            response.raise_for_status()

            imagem = Image.open(BytesIO(response.content))
            largura_original, altura_original = imagem.size

            proporcao_largura = largura_max / largura_original
            proporcao_altura = altura_max / altura_original
            proporcao_final = min(proporcao_largura, proporcao_altura)

            nova_largura = max(1, int(largura_original * proporcao_final))
            nova_altura = max(1, int(altura_original * proporcao_final))

            imagem_redimensionada = imagem.resize((nova_largura, nova_altura), Image.LANCZOS)

            out = (imagem_redimensionada, nova_largura, nova_altura)
            self._img_resize_cache[key] = out
            return out

        except UnidentifiedImageError:
            self._img_resize_cache[key] = (None, None, None)
            self.mostrar_mensagem(self.tr("Erro ao abrir a imagem. O arquivo não é uma imagem válida ou está corrompido."), "Erro")
            return None, None, None

        except Exception as e:
            self._img_resize_cache[key] = (None, None, None)
            self.mostrar_mensagem(self.tr("Erro ao processar a imagem: {error}").format(error=e), "Erro")
            return None, None, None

    def criar_kml_em_memoria(self, layer, campo_id, include_table, line_width, line_opacity, area_opacity, height, use_3d, is_elevated, is_solido, is_edges, image_url, overlay_url, progressBar=None):
        """
        Cria um documento KML em memória com base nos parâmetros fornecidos.

        Esta função realiza as seguintes etapas:
        1. Inicializa um elemento KML e um elemento Document.
        2. Obtém as cores da linha e do preenchimento para a camada.
        3. Verifica se é necessário transformar as coordenadas da camada para EPSG:4326.
        4. Itera sobre as feições da camada, criando placemarks KML para cada uma delas.
        5. Atualiza a barra de progresso, se fornecida.
        6. Adiciona um ScreenOverlay ao documento KML, se uma URL válida for fornecida para a imagem do overlay.

        Args:
        - layer: A camada QgsVectorLayer a ser exportada para KML.
        - campo_id: O nome do campo a ser usado como identificador de cada placemark.
        - include_table: Booleano que indica se os atributos da feição devem ser incluídos na descrição do placemark.
        - line_width: Largura da linha do placemark.
        - line_opacity: Opacidade da linha do placemark.
        - area_opacity: Opacidade da área do placemark.
        - height: Altura do placemark em metros.
        - use_3d: Booleano que indica se o placemark deve ser renderizado em 3D.
        - is_elevated: Booleano que indica se a elevação deve ser ajustada automaticamente.
        - is_solido: Booleano que indica se o placemark deve ter uma aparência sólida.
        - is_edges: Booleano que indica se as bordas do placemark devem ser exibidas.
        - image_url: A URL da imagem a ser usada como ícone do placemark.
        - overlay_url: A URL da imagem a ser usada como overlay.

        Returns:
        - O elemento KML contendo o documento.
        """
        kml = XmlET.Element('kml', xmlns="http://www.opengis.net/kml/2.2")
        document = XmlET.SubElement(kml, 'Document')

        # Obtém as cores da linha e do preenchimento para a camada
        cor_linha_kml, cor_preenchimento_kml = self.obter_cores(layer)

        transform = None
        if layer.crs().authid() != 'EPSG:4326':
            crsDestino = QgsCoordinateReferenceSystem(4326)
            transform = QgsCoordinateTransform(layer.crs(), crsDestino, QgsProject.instance())
            transformar = True
        else:
            transformar = False

        # Atualização da barra de progresso durante a iteração
        for count, feature in enumerate(layer.getFeatures()):
            if progressBar:
                progressBar.setValue(count)
            self.criar_placemark_kml(document, feature, campo_id, transformar, transform, cor_linha_kml, cor_preenchimento_kml, include_table, line_width, line_opacity, area_opacity, height, use_3d, is_elevated, is_solido, is_edges, image_url, overlay_url)

        # Finaliza a barra de progresso
        if progressBar:
            progressBar.setValue(layer.featureCount())

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

        return kml

    def formatar_valor_kml(self, valor):
        """
        Formata valores de atributos para exportação KML.

        Corrige principalmente QDate, QTime e QDateTime do PyQt/QGIS,
        evitando saída do tipo:
        PyQt6.QtCore.QDateTime(...)
        """
        if valor is None:
            return ""

        # Trata NULL/invalid de objetos Qt, quando disponível
        try:
            if hasattr(valor, "isNull") and valor.isNull():
                return ""
        except Exception:
            pass  # nosec B110

        try:
            if hasattr(valor, "isValid") and not valor.isValid():
                return ""
        except Exception:
            pass  # nosec B110

        # QDateTime
        try:
            if hasattr(valor, "date") and hasattr(valor, "time") and hasattr(valor, "toString"):
                return valor.toString("dd/MM/yyyy HH:mm:ss")
        except Exception:
            pass  # nosec B110

        # QDate
        try:
            if (hasattr(valor, "year")
                and hasattr(valor, "month")
                and hasattr(valor, "day")
                and hasattr(valor, "toString")):
                return valor.toString("dd/MM/yyyy")
        except Exception:
            pass  # nosec B110

        # QTime
        try:
            if (hasattr(valor, "hour")
                and hasattr(valor, "minute")
                and hasattr(valor, "second")
                and hasattr(valor, "toString")):
                return valor.toString("HH:mm:ss")
        except Exception:
            pass  # nosec B110

        # datetime/date/time nativos do Python
        try:
            if hasattr(valor, "strftime"):
                if hasattr(valor, "year") and hasattr(valor, "hour"):
                    return valor.strftime("%d/%m/%Y %H:%M:%S")
                if hasattr(valor, "year"):
                    return valor.strftime("%d/%m/%Y")
                if hasattr(valor, "hour"):
                    return valor.strftime("%H:%M:%S")
        except Exception:
            pass  # nosec B110

        return str(valor)

    def criar_placemark_kml(self, document, feature, campo_id, transformar, transform, cor_linha_kml, cor_preenchimento_kml, include_table, line_width, line_opacity, area_opacity, height, use_3d, is_elevated, is_solido, is_edges, image_url, overlay_url):
        """
        Cria um elemento Placemark KML para uma feição poligonal, preservando corretamente
        a estrutura da geometria original.

        Funcionalidades:
        - Trata geometrias Polygon e MultiPolygon.
        - Preserva o anel externo como outerBoundaryIs.
        - Preserva os anéis internos como innerBoundaryIs, mantendo vazios/recortes gerados
          por operações como diferença entre polígonos.
        - Cria MultiGeometry quando a feição possuir mais de um polígono.
        - Aplica estilo de preenchimento, borda, opacidade e espessura da linha.
        - Aplica configurações 3D, elevação, sólido ou apenas arestas quando habilitadas.
        - Inclui nome, dados estendidos e tabela HTML de atributos quando solicitado.
        - Inclui imagem no BalloonStyle quando uma URL válida for informada.

        Parâmetros:
        - document: Elemento Document do KML onde o Placemark será inserido.
        - feature: Feição QgsFeature que será exportada.
        - campo_id: Nome do campo usado como identificação do Placemark.
        - transformar: Indica se as coordenadas precisam ser transformadas para EPSG:4326.
        - transform: Transformação QgsCoordinateTransform usada quando transformar=True.
        - cor_linha_kml: Cor da linha no formato KML.
        - cor_preenchimento_kml: Cor de preenchimento no formato KML.
        - include_table: Define se os atributos serão incluídos na descrição do Placemark.
        - line_width: Espessura da linha no KML.
        - line_opacity: Opacidade da linha em percentual.
        - area_opacity: Opacidade do preenchimento em percentual.
        - height: Altura usada nas coordenadas do KML.
        - use_3d: Define se o modo 3D será aplicado.
        - is_elevated: Define se o modo elevado será aplicado.
        - is_solido: Define se o modo sólido será aplicado.
        - is_edges: Define se apenas as arestas serão exibidas.
        - image_url: URL da imagem exibida no BalloonStyle.
        - overlay_url: URL de overlay recebida por compatibilidade com o fluxo de exportação.

        Retorno:
        - None. O Placemark é adicionado diretamente ao elemento document.
        """
        placemark = XmlET.SubElement(document, 'Placemark')

        geometry = feature.geometry()
        if not geometry or geometry.isEmpty():
            return

        if geometry.type() != QgsWkbTypes.GeometryType.PolygonGeometry:
            return

        if geometry.isMultipart():
            poligonos = geometry.asMultiPolygon()
        else:
            poligonos = [geometry.asPolygon()]

        if not poligonos:
            return

        opacidade_preenchimento_hex = format(int(area_opacity * 255 / 100), '02x')
        cor_preenchimento_completa = opacidade_preenchimento_hex + cor_preenchimento_kml[2:]

        opacidade_hex = format(int(line_opacity * 255 / 100), '02x')
        cor_linha_completa = opacidade_hex + cor_linha_kml[2:]

        style = XmlET.SubElement(placemark, 'Style')
        poly_style = XmlET.SubElement(style, 'PolyStyle')
        color = XmlET.SubElement(poly_style, 'color')
        color.text = cor_preenchimento_completa

        line_style = XmlET.SubElement(style, 'LineStyle')
        color = XmlET.SubElement(line_style, 'color')
        color.text = cor_linha_completa
        width = XmlET.SubElement(line_style, 'width')
        width.text = str(line_width)

        if len(poligonos) > 1:
            geometry_element = XmlET.SubElement(placemark, 'MultiGeometry')
        else:
            geometry_element = placemark

        for poligono in poligonos:
            if not poligono:
                continue

            polygon = XmlET.SubElement(geometry_element, 'Polygon')
            self.processar_poligono(polygon, poligono, height, transformar, transform, use_3d)
            self.processar_poligono_elevado(polygon, poligono[0], height, transformar, transform, use_3d, poly_style, is_elevated, is_solido, is_edges, image_url, overlay_url)

        if include_table:
            valor_campo_id = self.formatar_valor_kml(feature[campo_id])

            name = XmlET.SubElement(placemark, 'name')
            name.text = valor_campo_id

            extended_data = XmlET.SubElement(placemark, 'ExtendedData')
            for field in feature.fields():
                valor_formatado = self.formatar_valor_kml(feature[field.name()])

                data = XmlET.SubElement(extended_data, 'Data', name=field.name())
                value = XmlET.SubElement(data, 'value')
                value.text = valor_formatado

            tabela_geral_html = '<table border="1" style="border-collapse: collapse; border: 2px solid black; width: 100%;">'
            for field in feature.fields():
                valor_formatado = self.formatar_valor_kml(feature[field.name()])
                cor_fundo = self.gerar_cor_suave()

                tabela_geral_html += f'<tr><td><table border="0" style="background-color: {cor_fundo}; width: 100%;">'
                tabela_geral_html += f'<tr><td style="text-align: left;"><b>{field.name()}</b></td>'
                tabela_geral_html += f'<td style="text-align: right;">{valor_formatado}</td></tr></table></td></tr>'

            tabela_geral_html += '</table>'

            texto_alt_icone = self.tr("Ícone")
            titulo_tabela = self.tr("Tabela de Informações:")

            imagem_html = ""
            if image_url:
                imagem_redimensionada, nova_largura, nova_altura = self.redimensionar_imagem_proporcional_url(image_url, 150, 75)
                if imagem_redimensionada is not None:
                    imagem_html = f'<div style="text-align: center;"><img src="{image_url}" alt="{texto_alt_icone}" width="{nova_largura}" height="{nova_altura}" style="margin-top: 1px; margin-bottom: -15px; margin-left: 0px; margin-right: 0px;"></div>'

            balloon_style = XmlET.SubElement(style, 'BalloonStyle')
            text = XmlET.SubElement(balloon_style, 'text')
            balloon_html = f"""
            {imagem_html}
            <h3 style="margin-bottom:1px;">{campo_id}: {valor_campo_id}</h3>
            <p>{titulo_tabela}</p>
            {tabela_geral_html}
            """
            text.text = balloon_html

    def processar_poligono(self, polygon_element, poligono, height, transformar, transform, use_3d):
        """
        Processa um polígono KML preservando anel externo e anéis internos.
        poligono = [anel_externo, anel_interno_1, anel_interno_2, ...]
        """
        if not poligono:
            return

        def adicionar_anel(parent_element, anel):
            linear_ring = XmlET.SubElement(parent_element, 'LinearRing')
            coordinates = XmlET.SubElement(linear_ring, 'coordinates')

            coords = []
            for point in anel:
                if transformar:
                    point = transform.transform(point.x(), point.y())
                coords.append(f"{point[0]},{point[1]},{height}")

            coordinates.text = ' '.join(coords)

        outer_boundary = XmlET.SubElement(polygon_element, 'outerBoundaryIs')
        adicionar_anel(outer_boundary, poligono[0])

        for anel_interno in poligono[1:]:
            inner_boundary = XmlET.SubElement(polygon_element, 'innerBoundaryIs')
            adicionar_anel(inner_boundary, anel_interno)

        if not use_3d and height == 0:
            tessellate = XmlET.SubElement(polygon_element, 'tessellate')
            tessellate.text = '1'
        else:
            altitudeMode = XmlET.SubElement(polygon_element, 'altitudeMode')
            altitudeMode.text = 'relativeToGround' if use_3d else 'clampToGround'

    def processar_poligono_elevado(self, polygon_element, anel, height, transformar, transform, use_3d, poly_style, is_elevated, is_solido, is_edges, image_url, overlay_url):
        """
        Processa as configurações de elevação, 3D e bordas para um elemento de polígono KML.

        Esta função realiza as seguintes etapas:
        1. Verifica se o modo 3D está ativado e aplica a configuração de altitudeMode se necessário.
        2. Aplica configurações adicionais com base nos modos específicos (elevado, sólido, bordas).

        Args:
        - polygon_element: O elemento Polygon ao qual as configurações serão aplicadas.
        - anel: O anel de coordenadas do polígono.
        - height: A altura do polígono em metros.
        - transformar: Booleano que indica se as coordenadas devem ser transformadas para EPSG:4326.
        - transform: O objeto QgsCoordinateTransform usado para transformar as coordenadas, se necessário.
        - use_3d: Booleano que indica se o modo 3D está ativado.
        - poly_style: O elemento Style associado ao polígono.
        - is_elevated: Booleano que indica se o modo 'Elevado' está ativado.
        - is_solido: Booleano que indica se o modo 'Sólido' está ativado.
        - is_edges: Booleano que indica se o modo 'Bordas' está ativado.
        - image_url: A URL da imagem a ser usada como ícone do Placemark.
        - overlay_url: A URL da imagem a ser usada como overlay.

        Returns:
        - None
        """
        # Se o checkBox3D estiver ativado, mas nenhum modo específico foi selecionado, então não faz nada
        if use_3d and not (is_elevated or is_solido or is_edges):
            return

        if use_3d:
            altitudeMode = XmlET.SubElement(polygon_element, 'altitudeMode')
            altitudeMode.text = 'relativeToGround'
            extrude = XmlET.SubElement(polygon_element, 'extrude')
            extrude.text = '1'  # As laterais se estendem até o solo

        # Se algum modo específico estiver ativo, aplica as configurações
        if is_elevated or is_solido or is_edges:
            outline = XmlET.SubElement(poly_style, 'outline')
            outline.text = '1'  # Mostra as bordas
            fill = XmlET.SubElement(poly_style, 'fill')
            fill.text = '0' if is_edges else '1'  # Sem preenchimento se for 'Edges', preenchido para outros

        # Especificamente para o modo 'Sólido', não mostrar as bordas
        if is_solido:
            outline.text = '0'

class CloneManagerP:
    def __init__(self, ui_manager, layer_to_clone):
        """
        Inicializa o gerenciador de clonagem para camadas do QGIS.

        Parâmetros:
        - ui_manager: Instância do gerenciador da interface do usuário, utilizada para interações, mensagens e chamadas de métodos utilitários.
        - layer_to_clone: Camada QGIS (QgsVectorLayer) que será clonada, podendo ser ponto, linha ou polígono, conforme o contexto do gerenciador.

        Detalhes:
        - Armazena referências essenciais para o processo de clonagem e para atualização da interface após a operação.
        - Permite acesso direto às funções de tratamento (como tratar_linhas, tratar_poligonos, etc.) após a criação da camada clonada.
        """
        # Referência ao gerenciador da interface do usuário
        self.ui_manager = ui_manager
        # Camada QGIS original que será clonada
        self.layer_to_clone = layer_to_clone

    def tr(self, message):
        return QCoreApplication.translate("CloneManagerP", message)

    def show_clone_options(self):
        """
        Exibe uma janela de diálogo para o usuário escolher o tipo de clonagem da camada de polígono.

        Funcionalidades:
        - Cria um diálogo modal com quatro opções de clonagem (através de botões de rádio).
        - Disponibiliza as opções: clonar só feições, só atributos, combinar e tratar, excluir e tratar.
        - O layout estiliza cada botão dentro de um QFrame para melhor apresentação visual.
        - Após confirmação, identifica a opção escolhida e chama a clonagem correspondente.
        """
        # Cria o diálogo como filho do diálogo principal da interface
        dialog = QDialog(self.ui_manager.dlg)
        dialog.setWindowTitle(self.tr("Escolher Tipo de Clonagem"))
        layout = QVBoxLayout(dialog)  # Layout vertical para organização dos elementos
        button_group = QButtonGroup(dialog)  # Grupo para garantir seleção única dos rádios

        # Define as opções de clonagem via QRadioButton, indexadas numericamente
        self.radio_buttons = {
            1: QRadioButton(self.tr("Clonar Feição, sem a Tabela")),
            2: QRadioButton(self.tr("Copiar Tabela de Atributos")),
            3: QRadioButton(self.tr("Combinar Tabela e Tratar Polígonos")),
            4: QRadioButton(self.tr("Excluir Tabela e Tratar Polígonos"))}

        # Adiciona cada botão de rádio dentro de um QFrame estilizado e ao layout do diálogo
        for id, radio in self.radio_buttons.items():
            frame = QFrame(dialog)
            frame_layout = QVBoxLayout(frame)
            frame.setFrameShape(QFrame.Shape.StyledPanel)
            frame.setFrameShadow(QFrame.Shadow.Raised)
            frame.setFixedSize(220, 30)  # Define o tamanho do frame para melhor alinhamento visual
            frame_layout.addWidget(radio)
            layout.addWidget(frame)
            button_group.addButton(radio, id)  # Adiciona o botão ao grupo para controle de seleção
            if id == 1:
                radio.setChecked(True)  # Define a primeira opção como padrão selecionada

        # Adiciona caixa de botões "Ok" e "Cancelar" ao diálogo
        buttonBox = QDialogButtonBox(QDialogButtonBox.StandardButton.Ok | QDialogButtonBox.StandardButton.Cancel)
        buttonBox.accepted.connect(dialog.accept)   # Conecta o Ok à aceitação do diálogo
        buttonBox.rejected.connect(dialog.reject)   # Conecta o Cancelar ao fechamento sem ação
        layout.addWidget(buttonBox)

        # Layout horizontal para centralizar os botões de ação
        hLayout = QHBoxLayout()
        hLayout.addStretch()
        hLayout.addWidget(buttonBox)
        hLayout.addStretch()
        layout.addLayout(hLayout)

        # Executa o diálogo e aguarda resposta do usuário
        result = dialog.exec()
        if result == QDialog.DialogCode.Accepted:
            # Percorre os botões para encontrar o selecionado
            for id, radio in self.radio_buttons.items():
                if radio.isChecked():
                    self.realizar_clonagem(id)  # Executa a clonagem conforme escolha
                    break

    def _obter_grupo_camadas_clonadas(self):
        """
        Retorna o grupo existente de camadas clonadas.

        Usa uma propriedade interna fixa para evitar duplicação
        quando o idioma do plugin for alterado.
        """
        root = QgsProject.instance().layerTreeRoot()

        nome_grupo = self.tr("Camadas Clonadas")
        chave_grupo = "tempo_salvo_tools/grupo_camadas_clonadas"

        try:
            grupos = root.findGroups()
        except Exception:
            grupos = []

        # Procura primeiro pela propriedade interna estável
        for grupo in grupos:
            try:
                valor = grupo.customProperty(chave_grupo, False)

                if valor in (
                    True,
                    1,
                    "1",
                    "true",
                    "True"):
                    return grupo

            except Exception:
                pass  # nosec B110

        # Compatibilidade com grupos criados anteriormente
        nomes_aceitos = {
            nome_grupo.strip().casefold(),
            "Camadas Clonadas".casefold(),
            "Cloned Layers".casefold()}

        for grupo in grupos:
            try:
                nome_atual = grupo.name().strip().casefold()

                if nome_atual in nomes_aceitos:
                    grupo.setCustomProperty(chave_grupo, True)
                    return grupo

            except Exception:
                pass  # nosec B110

        # Cria somente quando nenhum grupo foi encontrado
        grupo = root.addGroup(nome_grupo)

        grupo.setCustomProperty(chave_grupo, True)

        return grupo

    def criar_camada_clonada(self, name_suffix, fields=None, features_to_add=None, set_renderer=True):
        """
        Cria uma nova camada clonada baseada em uma camada existente do QGIS.

        Funcionalidades:
        - Define o nome da camada clonada adicionando um sufixo.
        - Mantém o tipo de geometria e SRC (CRS) da camada original.
        - Cria a camada como 'memory', ou seja, camada temporária em memória.
        - Permite especificar novos campos e/ou feições, ou copiar todos da camada original.
        - (Opcional) Copia o renderizador/simbologia da camada original.
        - Adiciona a camada ao grupo "Camadas Clonadas" no projeto QGIS.
        - Retorna a camada criada para possível uso posterior.

        Parâmetros:
        - name_suffix: Sufixo a ser adicionado ao nome da camada clonada.
        - fields: (Opcional) Campos a serem usados na camada clonada (QgsFields).
        - features_to_add: (Opcional) Lista de feições a serem adicionadas à camada clonada.
        - set_renderer: (bool) Define se deve copiar o renderizador da camada original.
        """
        # Define o nome da camada clonada com sufixo e nome original
        clone_name = f"{name_suffix}_{self.layer_to_clone.name()}"
        # Verifica se a camada original é temporária
        is_temporary = "memory:" in self.layer_to_clone.source()
        # Recupera o tipo de geometria da camada (0: Ponto, 1: Linha, 2: Polígono)
        geom_type = self.layer_to_clone.geometryType()
        geom_type_str = ["Point", "LineString", "Polygon"][geom_type]
        # Recupera o CRS (SRC) da camada original
        crs = self.layer_to_clone.crs().authid()
        # Cria a camada de memória clonada com o mesmo tipo de geometria e CRS
        clone = QgsVectorLayer(f"{geom_type_str}?crs={crs}", clone_name, "memory")

        # Verifica se a camada foi criada com sucesso
        if not clone.isValid():
            QMessageBox.critical(None, self.tr("Erro"), self.tr("Não foi possível criar a camada clonada."))
            return None

        # Obtém o provedor de dados da nova camada clonada
        clone_provider = clone.dataProvider()

        # Adiciona campos: usa os campos informados ou copia todos da original
        if fields is not None:
            clone_provider.addAttributes(fields.toList())
        else:
            clone_provider.addAttributes(self.layer_to_clone.fields().toList())
        clone.updateFields()

        # Preserva os aliases dos campos da camada original
        for i, field in enumerate(clone.fields()):
            idx_original = self.layer_to_clone.fields().indexOf(field.name())

            if idx_original != -1:
                alias = self.layer_to_clone.attributeAlias(idx_original)

                if alias:
                    clone.setFieldAlias(i, alias)

        # Adiciona feições: usa as informadas ou copia todas da original
        if features_to_add is not None:
            clone_provider.addFeatures(features_to_add)
        else:
            all_features = [feat for feat in self.layer_to_clone.getFeatures()]
            clone_provider.addFeatures(all_features)

        # Copia simbologia/renderizador da original se solicitado
        if set_renderer:
            clone.setRenderer(self.layer_to_clone.renderer().clone())

        # Obtém o grupo existente ou cria apenas uma vez
        grupo_clonadas = self._obter_grupo_camadas_clonadas()

        # Adiciona a camada ao projeto sem inserção automática
        QgsProject.instance().addMapLayer(clone, False)

        # Adiciona ao grupo já existente
        grupo_clonadas.addLayer(clone)

        clone.updateExtents()
        clone.triggerRepaint()

        return clone  # Retorna a camada criada para manipulação posterior

    def realizar_clonagem(self, tipo_clonagem):
        """
        Executa o tipo de clonagem selecionado pelo usuário, direcionando para o método específico.

        Parâmetros:
        - tipo_clonagem: (int) Indica a opção selecionada de clonagem:
            1 - Clonar apenas as feições (geometria, sem atributos).
            2 - Clonar tabela de atributos (geometria + todos os atributos).
            3 - Combinar tabela e tratamento específico (campos/atributos adaptados).
            4 - Excluir tabela e tratar apenas campos essenciais.

        Funcionamento:
        - Recebe o número da opção (via botão de rádio).
        - Chama o método correspondente para realizar a clonagem conforme solicitado.
        """
        # Opção 1: Clonar só feições
        if tipo_clonagem == 1:
            self.clone_feicao()
        # Opção 2: Clonar feições + atributos
        elif tipo_clonagem == 2:
            self.clone_atributos()
        # Opção 3: Combinar atributos e realizar tratamento especial
        elif tipo_clonagem == 3:
            self.clone_combinar()
        # Opção 4: Excluir atributos e tratar apenas campos essenciais
        elif tipo_clonagem == 4:
            self.clone_excluir()

    def clone_feicao(self):
        """
        Clona somente as geometrias dos polígonos,
        sem copiar a tabela de atributos.
        """
        features_to_add = []

        for feature in self.layer_to_clone.getFeatures():
            nova_feature = QgsFeature()
            nova_feature.setGeometry(
                QgsGeometry(feature.geometry()))
            features_to_add.append(nova_feature)

        clone = self.criar_camada_clonada(
            self.tr("Clone_SemTabela"),
            fields=QgsFields(),
            features_to_add=features_to_add,
            set_renderer=True)

        if clone is None or not clone.isValid():
            self.ui_manager.mostrar_mensagem(self.tr("Falha ao criar a camada clonada."), "Erro")
            return

        self.cloned_layer = clone

        self.ui_manager.mostrar_mensagem(self.tr("Clonagem de feição realizada com sucesso."), "Sucesso" )

    def clone_atributos(self):
        """
        Clona uma camada mantendo todas as geometrias e atributos originais.

        Funcionalidades:
        - Copia todos os campos (atributos) da camada original.
        - Cria novas feições clonando tanto a geometria quanto os atributos de cada feição original.
        - Cria uma nova camada em memória contendo todas as feições e campos.
        - Copia a simbologia/renderizador da camada original para a clonada.
        - Armazena referência da nova camada clonada.
        - Exibe mensagem de sucesso ao concluir a clonagem.

        Processo passo a passo:
        1. Recupera os campos (estrutura de atributos) da camada original.
        2. Percorre todas as feições da camada, copiando geometria e atributos.
        3. Cria a nova camada clonada, adicionando campos e feições.
        4. (Se necessário) Copia a simbologia da camada original.
        5. Atualiza referência interna e notifica o usuário.
        """

        # Recupera os campos da camada original
        fields = self.layer_to_clone.fields()
        # Lista todas as feições da camada original
        features = [feat for feat in self.layer_to_clone.getFeatures()]
        new_features = []
        # Percorre todas as feições para copiar geometria e atributos
        for feature in features:
            new_feature = QgsFeature(fields)  # Cria uma nova feição com os mesmos campos
            new_feature.setGeometry(feature.geometry())  # Copia a geometria da feição
            # Copia cada atributo pelo nome do campo
            for field in fields.names():
                new_feature.setAttribute(field, feature[field])
            new_features.append(new_feature)  # Adiciona à lista de novas feições

        # Cria camada clonada com os campos e as feições copiadas
        clone = self.criar_camada_clonada(self.tr("Clone_Tabela"), fields, new_features)
        if not clone:
            # Falhou ao criar a camada clonada
            return

        # Copia simbologia/renderizador da original para a camada clonada
        clone.setRenderer(self.layer_to_clone.renderer().clone())
        # Armazena referência para uso posterior (se necessário)
        self.cloned_layer = clone

        # Notifica o usuário do sucesso
        self.ui_manager.mostrar_mensagem(self.tr("Clonagem de atributos realizada com sucesso."), "Sucesso")

    def clone_combinar(self):
        """
        Cria uma camada clonada de polígonos combinando campos e tratamento especial.

        Funcionalidades:
        - Cria uma nova camada com os campos "ID", "Perimetro", "Area" adicionados antes dos demais.
        - Copia todos os outros campos da camada original, exceto "ID", "Perimetro" e "Area" para evitar duplicidade.
        - Para cada feição, calcula e atribui um novo ID sequencial, o perímetro e a área reais.
        - Copia os demais atributos da feição original.
        - Chama o tratamento adicional para polígonos (atualização automática dos campos especiais).
        - Exibe mensagem de sucesso ao concluir.

        Processo passo a passo:
        1. Define os campos da camada clonada, priorizando os essenciais.
        2. Percorre todas as feições da camada original.
        3. Calcula o perímetro e a área, define ID sequencial, e copia os outros atributos.
        4. Cria e popula a nova camada clonada com os campos e feições.
        5. Chama método para ativar sinais de atualização automática nos campos essenciais.
        6. Notifica o usuário.
        """
        # Define a estrutura de campos da nova camada clonada
        fields_to_add = QgsFields()
        fields_to_add.append(QgsField("ID", QMetaType.Type.Int))             # Campo sequencial ID
        fields_to_add.append(QgsField("Perimetro", QMetaType.Type.Double))   # Campo Perímetro
        fields_to_add.append(QgsField("Area", QMetaType.Type.Double))        # Campo Área

        original_fields = self.layer_to_clone.fields()
        # Copia todos os campos originais, exceto ID, Perímetro e Área
        for field in original_fields:
            if field.name() not in ["ID", "Perimetro", "Area"]:
                fields_to_add.append(field)

        new_features = []
        # Para cada feição da camada original, calcula e popula os novos campos
        for index, feature in enumerate(self.layer_to_clone.getFeatures(), start=1):
            new_feature = QgsFeature(fields_to_add)
            new_feature.setGeometry(feature.geometry())
            new_attributes = [None] * len(fields_to_add)
            # Calcula perímetro e área da geometria atual
            perimetro, area = self.ui_manager.calcular_perimetro_area(self.layer_to_clone, feature.geometry())
            new_attributes[0] = index                # ID sequencial
            new_attributes[1] = perimetro            # Perímetro calculado
            new_attributes[2] = area                 # Área calculada
            original_attributes = feature.attributes()
            # Copia demais atributos, ajustando índices para os novos campos
            for i, field in enumerate(original_fields):
                if field.name() not in ["ID", "Perimetro", "Area"]:
                    new_index = fields_to_add.indexOf(field.name())
                    new_attributes[new_index] = original_attributes[i]
            new_feature.setAttributes(new_attributes)
            new_features.append(new_feature)

        # Cria a nova camada clonada com a estrutura e feições montadas
        clone = self.criar_camada_clonada(self.tr("Clone_Combinado"), fields=fields_to_add, features_to_add=new_features)
        # Ativa sinais de atualização automática para perímetro e área na nova camada
        self.ui_manager.tratar_poligonos(clone)
        if clone:
            self.ui_manager.mostrar_mensagem(self.tr("Combinação de tabela e tratamento de polígonos realizados com sucesso."), "Sucesso")
        return clone

    def clone_excluir(self):
        """
        Cria uma camada clonada de polígonos excluindo todos os campos originais,
        mantendo apenas "ID", "Perimetro" e "Area", e aplicando o tratamento pós-clonagem.

        Funcionalidades:
        - Define uma nova estrutura de campos mínima: "ID", "Perimetro" e "Area".
        - Para cada feição da camada original, copia apenas a geometria.
        - Calcula e armazena o ID sequencial, perímetro e área em cada nova feição.
        - Cria a nova camada em memória com as feições e campos definidos.
        - Ativa o tratamento de atualização automática para perímetro e área.
        - Exibe mensagem de sucesso ao concluir.

        Fluxo:
        1. Monta os campos essenciais na camada nova.
        2. Percorre as feições originais, calcula atributos e monta a lista de novas feições.
        3. Cria a camada clonada.
        4. Ativa o tratamento de polígonos (sinais para atualização dinâmica).
        5. Atualiza referência e notifica o usuário.
        """

        # Define os campos essenciais: ID, Perimetro e Area
        new_fields = QgsFields()
        new_fields.append(QgsField("ID", QMetaType.Type.Int))                # Campo sequencial ID
        new_fields.append(QgsField("Perimetro", QMetaType.Type.Double))      # Campo Perímetro
        new_fields.append(QgsField("Area", QMetaType.Type.Double))           # Campo Área

        new_features = []
        # Para cada feição, calcula e atribui apenas os campos essenciais
        for index, feature in enumerate(self.layer_to_clone.getFeatures(), start=1):
            new_feature = QgsFeature(new_fields)                       # Nova feição com os novos campos
            new_feature.setGeometry(feature.geometry())                # Copia a geometria
            perimetro, area = self.ui_manager.calcular_perimetro_area(self.layer_to_clone, feature.geometry())
            new_feature.setAttribute("ID", index)                      # ID sequencial
            new_feature.setAttribute("Perimetro", perimetro)           # Perímetro calculado
            new_feature.setAttribute("Area", area)                     # Área calculada
            new_features.append(new_feature)                           # Adiciona à lista

        # Cria a camada clonada com campos mínimos e as novas feições
        clone = self.criar_camada_clonada(self.tr("Clone_Excluir"), new_fields, new_features)
        if clone is None:
            QMessageBox.critical(None, self.tr("Erro"), self.tr("Falha ao criar a camada clonada."))  # Erro ao criar camada
            return

        # Ativa tratamento automático de perímetro e área na nova camada
        self.ui_manager.tratar_poligonos(clone)
        # Armazena referência da camada clonada para uso posterior
        self.cloned_layer = clone
        # Notifica o usuário do sucesso
        self.ui_manager.mostrar_mensagem(self.tr("Exclusão de tabela e tratamento de polígonos realizados com sucesso."), "Sucesso")

class TreeViewEventFilter(QObject):
    """
    Filtro de eventos do `treeViewListaPoligono` para melhorar a interação do usuário.

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
        tv = self.ui_manager.dlg.treeViewListaPoligono

        # Só intercepta eventos do viewport do treeView
        if obj != tv.viewport():
            return super().eventFilter(obj, event)

        et = event.type()

        # Drag & Drop (Adicionar)
        if et in (QEvent.Type.DragEnter, QEvent.Type.DragMove):
            md = event.mimeData()
            if md and md.hasUrls():
                paths = [u.toLocalFile() for u in md.urls() if u.isLocalFile()]
                if self._coletar_paths_drop(paths):
                    event.setDropAction(Qt.DropAction.CopyAction)
                    event.accept()
                    return True
            event.ignore()
            return True

        if et == QEvent.Type.Drop:
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
        if et == QEvent.Type.MouseMove:
            index = tv.indexAt(event.pos())
            if index.isValid():
                self.ui_manager.configurar_tooltip(index)
            # não “consome” o mouse move, deixa o treeView continuar normal
            return False

        return super().eventFilter(obj, event)

class ExportarKMLDialog(QDialog):

    # Atributos de classe para armazenar os URLs
    ultimoTextoUrl = ""
    ultimoTextoUrl2 = ""

    def __init__(self, layer, parent=None):
        super().__init__(parent)
        
        self.layer = layer
        self.setWindowTitle(self.tr("Configurações de Exportação para KML"))

        # Obtém as opacidades atuais da borda e do preenchimento
        opacidade_linha_inicial, opacidade_area_inicial = (self._obter_opacidades_iniciais())

        mainLayout = QVBoxLayout(self)

        frame = QFrame()
        frame.setFrameShape(QFrame.Shape.StyledPanel)
        frame.setFrameShadow(QFrame.Shadow.Raised)
        frameLayout = QVBoxLayout(frame)

        # ComboBox para campo de identificação
        identificationLayout = QHBoxLayout()
        self.comboBox = QComboBox()
        self.populate_fields()
        identificationLayout.addWidget(QLabel(self.tr("Campo de Identificação:")))
        identificationLayout.addWidget(self.comboBox)

        # CheckBox para opção Tabela
        self.tableCheckBox = QCheckBox(self.tr("Tabela"))
        self.tableCheckBox.setChecked(True)
        identificationLayout.addWidget(self.tableCheckBox)
        frameLayout.addLayout(identificationLayout)

        # DoubleSpinBox para largura da linha
        lineLayout = QHBoxLayout()
        self.lineWidthSpinBox = QDoubleSpinBox()
        self.lineWidthSpinBox.setValue(1.0)  # Valor padrão
        self.lineWidthSpinBox.setSingleStep(0.1)
        self.lineWidthSpinBox.setDecimals(1)
        lineLayout.addWidget(QLabel(self.tr("Largura da Linha:")))
        lineLayout.addWidget(self.lineWidthSpinBox)

        # DoubleSpinBox para opacidade da linha
        self.lineOpacitySpinBox = QDoubleSpinBox()
        self.lineOpacitySpinBox.setRange(0, 100)
        self.lineOpacitySpinBox.setValue(opacidade_linha_inicial)
        self.lineOpacitySpinBox.setSingleStep(5)
        self.lineOpacitySpinBox.setDecimals(0)
        self.lineOpacitySpinBox.setSuffix(" %")
        lineLayout.addWidget(QLabel(self.tr("Opacidade:")))
        lineLayout.addWidget(self.lineOpacitySpinBox)
        frameLayout.addLayout(lineLayout)

        # DoubleSpinBox para altura
        heightLayout = QHBoxLayout()
        self.heightSpinBox = QDoubleSpinBox()
        self.heightSpinBox.setSuffix(" m")
        self.heightSpinBox.setSingleStep(0.5)
        self.heightSpinBox.setValue(0.00)  # Valor padrão
        self.heightSpinBox.setRange(0, 1000)
        self.heightSpinBox.setDecimals(2)  # Define a precisão decimal para dois dígitos
        heightLayout.addWidget(QLabel(self.tr("Altura:")))
        heightLayout.addWidget(self.heightSpinBox)

        # DoubleSpinBox para opacidade da área
        self.areaOpacitySpinBox = QDoubleSpinBox()
        self.areaOpacitySpinBox.setRange(0, 100)
        self.areaOpacitySpinBox.setValue(opacidade_area_inicial)
        self.areaOpacitySpinBox.setSingleStep(5)
        self.areaOpacitySpinBox.setDecimals(0)
        self.areaOpacitySpinBox.setSuffix(" %")
        heightLayout.addWidget(QLabel(self.tr("Opacidade da Área:")))
        heightLayout.addWidget(self.areaOpacitySpinBox)
        frameLayout.addLayout(heightLayout)

        # Layout para opções 3D
        options3DLayout = QHBoxLayout()

        # CheckBox para opção 3D
        self.checkBox3D = QCheckBox(self.tr("3D"))
        options3DLayout.addWidget(self.checkBox3D)

        # Conecta o sinal toggled do checkBox3D ao slot que atualiza o estado do DoubleSpinBox da altura
        self.checkBox3D.toggled.connect(self.updateHeightSpinBoxState)

        # Atualiza o estado inicial do DoubleSpinBox da altura com base no estado inicial do checkBox3D
        self.updateHeightSpinBoxState(self.checkBox3D.isChecked())

        # RadioButtons para opções de visualização 3D
        self.radioElevated = QRadioButton(self.tr("Elevado"))
        self.radioSolid = QRadioButton(self.tr("Sólido"))
        self.radioEdges = QRadioButton(self.tr("Arestas"))

        # Adicionar os RadioButtons a um grupo (opcional)
        self.visualization3DGroup = QButtonGroup(self)
        self.visualization3DGroup.addButton(self.radioElevated)
        self.visualization3DGroup.addButton(self.radioSolid)
        self.visualization3DGroup.addButton(self.radioEdges)

        # Adicionar RadioButtons ao layout
        options3DLayout.addWidget(self.radioElevated)
        options3DLayout.addWidget(self.radioSolid)
        options3DLayout.addWidget(self.radioEdges)

        # Adicionar o layout das opções 3D ao layout principal do frame
        frameLayout.addLayout(options3DLayout)

        # Primeiro QLineEdit e QPushButton para o URL da imagem
        self.labelImageUrl = QLabel(self.tr("URL da Imagem para a Tabela:"))
        frameLayout.addWidget(self.labelImageUrl)
        
        urlLayout1 = QHBoxLayout()
        self.lineEditImageUrl = QLineEdit()
        self.lineEditImageUrl.setPlaceholderText(self.tr("Colar o URL da IMG para a Tabela: Opcional"))
        self.lineEditImageUrl.setClearButtonEnabled(True)  # Habilita o botão de limpeza
        self.btnAbrirImagem = QPushButton(self.tr("Colar"))
        self.btnAbrirImagem.setMaximumWidth(40)
        urlLayout1.addWidget(self.lineEditImageUrl)
        urlLayout1.addWidget(self.btnAbrirImagem)
        frameLayout.addLayout(urlLayout1)

        self.btnAbrirImagem.clicked.connect(self.colarTextop)

        # Segundo QLineEdit e QPushButton para o URL da imagem
        self.labelImageUrl2 = QLabel(self.tr("URL para ScreenOverlay:"))
        frameLayout.addWidget(self.labelImageUrl2)
        
        urlLayout2 = QHBoxLayout()
        self.lineEditImageUrl2 = QLineEdit()
        self.lineEditImageUrl2.setPlaceholderText(self.tr("Colar o URL para o ScreenOverlay: Opcional"))
        self.lineEditImageUrl2.setClearButtonEnabled(True)  # Habilita o botão de limpeza
        self.btnColarImagem2 = QPushButton(self.tr("Colar"))
        self.btnColarImagem2.setMaximumWidth(40)
        urlLayout2.addWidget(self.lineEditImageUrl2)
        urlLayout2.addWidget(self.btnColarImagem2)
        frameLayout.addLayout(urlLayout2)

        self.btnColarImagem2.clicked.connect(self.colarTexto2p)

        # Setar o texto dos QLineEdit com os últimos valores usados
        self.lineEditImageUrl.setText(self.ultimoTextoUrl)
        self.lineEditImageUrl2.setText(self.ultimoTextoUrl2)

        # Conecta o sinal textChanged a um novo método para lidar com a atualização do texto
        self.lineEditImageUrl.textChanged.connect(self.verificarTexto)
        self.lineEditImageUrl2.textChanged.connect(self.verificarTexto2)

        # Botões Exportar e Cancelar
        buttonLayout = QHBoxLayout()
        self.okButton = QPushButton(self.tr("Exportar"))
        self.okButton.clicked.connect(self.accept)
        self.cancelButton = QPushButton(self.tr("Cancelar"))
        self.cancelButton.clicked.connect(self.reject)
        buttonLayout.addWidget(self.okButton)
        buttonLayout.addWidget(self.cancelButton)
        frameLayout.addLayout(buttonLayout)

        mainLayout.addWidget(frame)

        # Conectar sinais aos slots
        self.tableCheckBox.toggled.connect(self.updateUIElements)
        self.radioSolid.toggled.connect(self.updateUIElements)
        self.radioEdges.toggled.connect(self.updateUIElements)
        self.checkBox3D.toggled.connect(self.updateUIElements)

        # Atualizar a UI inicialmente
        self.updateUIElements()

    def _obter_opacidades_iniciais(self):
        """
        Obtém a opacidade visual atual da borda e do preenchimento
        da camada, retornando os valores no intervalo de 0 a 100.

        Considera:
        - alfa da cor da borda;
        - alfa da cor do preenchimento;
        - opacidade geral do símbolo;
        - opacidade geral da camada, quando disponível.
        """
        opacidade_linha = 100.0
        opacidade_area = 100.0

        try:
            renderer = self.layer.renderer()

            if renderer is None:
                return opacidade_linha, opacidade_area

            simbolos = []

            # Renderizador de símbolo único
            try:
                simbolo = renderer.symbol()

                if simbolo is not None:
                    simbolos.append(simbolo)

            except Exception:
                pass  # nosec B110

            # Renderizadores categorizados, graduados ou por regras
            if not simbolos:
                try:
                    simbolos = list(
                        renderer.symbols(QgsRenderContext()))
                except Exception:
                    simbolos = []

            if not simbolos:
                return opacidade_linha, opacidade_area

            simbolo = simbolos[0]

            # Opacidade geral do símbolo
            try:
                opacidade_simbolo = float(simbolo.opacity())
            except Exception:
                opacidade_simbolo = 1.0

            opacidade_simbolo = max(0.0, min(1.0, opacidade_simbolo))

            # Opacidade geral da camada
            try:
                opacidade_camada = float(self.layer.opacity())
            except Exception:
                opacidade_camada = 1.0

            opacidade_camada = max(0.0, min(1.0, opacidade_camada))

            fator_geral = (opacidade_simbolo * opacidade_camada)

            cor_preenchimento = None
            cor_borda = None

            # Procura as cores nas camadas que compõem o símbolo
            for indice in range(simbolo.symbolLayerCount()):
                symbol_layer = simbolo.symbolLayer(indice)

                if symbol_layer is None:
                    continue

                # Cor de preenchimento
                if cor_preenchimento is None:
                    try:
                        cor = symbol_layer.fillColor()

                        if cor is not None and cor.isValid():
                            cor_preenchimento = QColor(cor)

                    except Exception:
                        pass  # nosec B110

                # Cor da borda
                if cor_borda is None:
                    try:
                        cor = symbol_layer.strokeColor()

                        if cor is not None and cor.isValid():
                            cor_borda = QColor(cor)

                    except Exception:
                        try:
                            cor = symbol_layer.outlineColor()

                            if cor is not None and cor.isValid():
                                cor_borda = QColor(cor)

                        except Exception:
                            pass  # nosec B110

                if (cor_preenchimento is not None
                    and cor_borda is not None):
                    break

            # Fallback para preenchimento
            if cor_preenchimento is None:
                try:
                    cor = simbolo.color()

                    if cor is not None and cor.isValid():
                        cor_preenchimento = QColor(cor)

                except Exception:
                    pass  # nosec B110

            alfa_preenchimento = 1.0
            alfa_borda = 1.0

            if cor_preenchimento is not None:
                alfa_preenchimento = (cor_preenchimento.alphaF())

            if cor_borda is not None:
                alfa_borda = cor_borda.alphaF()

            opacidade_area = (alfa_preenchimento * fator_geral * 100.0)

            opacidade_linha = (alfa_borda * fator_geral * 100.0)

        except Exception:
            return 100.0, 100.0

        return (max(0.0, min(100.0, opacidade_linha)),
            max(0.0, min(100.0, opacidade_area)))

    def updateHeightSpinBoxState(self, checked):
        """
        Atualiza o estado do QSpinBox associado à altura com base no valor de checked.

        Args:
        - checked (bool): Indica se a caixa de seleção relacionada está marcada (True) ou desmarcada (False).
        """

        # Define se o QSpinBox associado à altura deve ser ativado ou desativado com base no valor de checked
        self.heightSpinBox.setEnabled(checked)

    def updateUIElements(self):
        """
        Atualiza os elementos da interface do usuário (UI) com base no estado atual dos widgets.

        Esta função realiza as seguintes etapas:
        1. Verifica se há feições na camada e se há campos na camada.
        2. Atualiza a ativação dos widgets com base nas condições de presença de feições e estado dos checkboxes.
        3. Habilita ou desabilita os widgets conforme necessário, dependendo das opções 3D e dos radio buttons selecionados.

        Args:
        - None

        Returns:
        - None
        """
        # Atualiza os elementos da UI com base no estado atual dos widgets
        hasFeatures = self.layer.featureCount() > 0 and len(self.layer.fields()) > 0
        # Habilita ou desabilita os widgets conforme necessário
        self.comboBox.setEnabled(hasFeatures and self.tableCheckBox.isChecked())
        self.okButton.setEnabled(hasFeatures)
        self.lineEditImageUrl.setEnabled(self.tableCheckBox.isChecked())
        self.btnAbrirImagem.setEnabled(self.tableCheckBox.isChecked())

        # Opções 3D e radio buttons
        isElevatedChecked = self.radioSolid.isChecked() and self.checkBox3D.isChecked()
        isEdgesChecked = self.radioEdges.isChecked() and self.checkBox3D.isChecked()
        # Desabilita a configuração da opacidade da linha se 'isElevatedChecked' estiver verdadeiro
        self.lineOpacitySpinBox.setEnabled(not isElevatedChecked)
        # Desabilita a configuração da largura da linha se 'isElevatedChecked' estiver verdadeiro
        self.lineWidthSpinBox.setEnabled(not isElevatedChecked)
        # Desabilita a configuração da opacidade da área se 'isEdgesChecked' estiver verdadeiro
        self.areaOpacitySpinBox.setEnabled(not isEdgesChecked)

        # Atualizar a ativação dos radio buttons com base no checkBox 3D
        self.radioElevated.setEnabled(self.checkBox3D.isChecked())
        self.radioSolid.setEnabled(self.checkBox3D.isChecked())
        self.radioEdges.setEnabled(self.checkBox3D.isChecked())

    def verificarValidadeURL(self, url):
        """
        Verifica a validade de uma URL de acordo com um padrão regex.

        Args:
        - url (str): A URL a ser verificada.

        Returns:
        - bool: True se a URL for válida, False caso contrário.
        """

        # Define o padrão regex para verificar a validade da URL
        padrao_url = re.compile(
            r'^(https?:\/\/)?'  # http:// ou https://
            r'((([a-z\d]([a-z\d-]*[a-z\d])*)\.)+[a-z]{2,}|'  # domínio
            r'((\d{1,3}\.){3}\d{1,3}))'  # ou ip
            r'(\:\d+)?(\/[-a-z\d%_.~+=]*)*'  # porta e caminho, incluído '=' no caminho
            r'(\?[;&a-z\d%_.~+=-]*)?'  # query string
            r'(\#[-a-z\d_]*)?$', re.IGNORECASE)  # fragmento
        return re.match(padrao_url, url) is not None

    def colarTextop(self):
        """
        Cola o texto da área de transferência na caixa de texto QLineEdit.

        Esta função verifica se o texto colado da área de transferência é uma URL válida.
        Se for uma URL válida, o texto é definido como o texto da caixa de texto QLineEdit.

        Nota: A validação da URL é realizada utilizando a função verificarValidadeURL.

        """
        # Obtém o objeto de área de transferência da aplicação
        clipboard = QGuiApplication.clipboard()
        texto = clipboard.text() # Obtém o texto da área de transferência
        
        # Verifica se o texto da área de transferência é uma URL válida
        if self.verificarValidadeURL(texto):
            self.lineEditImageUrl.setText(texto) # Define o texto colado como o texto da caixa de texto QLineEdit

    def colarTexto2p(self):
        """
        Cola o texto da área de transferência na caixa de texto QLineEdit.

        Esta função verifica se o texto colado da área de transferência é uma URL válida.
        Se for uma URL válida, o texto é definido como o texto da caixa de texto QLineEdit.

        Nota: A validação da URL é realizada utilizando a função verificarValidadeURL.

        """
        # Obtém o objeto de área de transferência da aplicação
        clipboard = QGuiApplication.clipboard()
        texto = clipboard.text() # Obtém o texto da área de transferência
        # Verifica se o texto da área de transferência é uma URL válida
        if self.verificarValidadeURL(texto):
            # Define o texto colado como o texto da caixa de texto QLineEdit
            self.lineEditImageUrl2.setText(texto)

    def verificarValidadeURLImagem(self, url):
        """
        Verifica se a URL fornecida leva a uma imagem válida.

        Esta função verifica se a URL termina com uma das extensões de arquivo de imagem
        aceitáveis. Se a URL terminar com uma dessas extensões, ela é considerada uma URL
        válida para uma imagem.

        Args:
            url (str): A URL a ser verificada.

        Returns:
            bool: True se a URL levar a uma imagem válida, False caso contrário.
        """
        # Define as extensões de arquivo de imagem que são aceitáveis
        extensoes_validas = ['.jpg', '.jpeg', '.png', '.gif', '.bmp', '.tif', '.tiff', '.webp']
        # Verifica se a URL termina com uma das extensões de arquivo de imagem válidas
        return any(url.lower().endswith(ext) for ext in extensoes_validas)

    def verificarTexto(self):
        """
        Verifica o texto inserido no lineEdit da URL.

        Esta função verifica se o texto inserido na caixa de texto da URL é uma URL válida e se leva a uma imagem válida.
        Se a URL for válida e levar a uma imagem válida, a cor do texto na caixa de texto da URL será alterada para azul.
        Se a URL não for válida ou não levar a uma imagem válida, a cor do texto na caixa de texto da URL será alterada para vermelho.

        """
        # Obtém o texto da caixa de texto da URL
        texto = self.lineEditImageUrl.text()
        # Verifica se o texto é uma URL válida e se leva a uma imagem válida
        if self.verificarValidadeURL(texto) and self.verificarValidadeURLImagem(texto):
            # Se a URL for válida e levar a uma imagem válida, define a cor do texto como azul
            ExportarKMLDialog.ultimoTextoUrl = texto 
            self.lineEditImageUrl.setStyleSheet("QLineEdit { color: blue; }")
        else:
            # Se a URL não for válida ou não levar a uma imagem válida, limpa a última URL válida e
            # define a cor do texto como vermelho, se o texto não estiver vazio
            ExportarKMLDialog.ultimoTextoUrl = ""
            if texto.strip() != "":
                self.lineEditImageUrl.setStyleSheet("QLineEdit { color: red; }")
            else:
                # Se o texto estiver vazio, remove qualquer estilo de cor
                self.lineEditImageUrl.setStyleSheet("")

    def verificarTexto2(self):
        """
        Verifica o texto inserido no lineEdit da segunda URL.

        Esta função verifica se o texto inserido na caixa de texto da segunda URL é uma URL válida e se leva a uma imagem válida.
        Se a URL for válida e levar a uma imagem válida, a cor do texto na caixa de texto da segunda URL será alterada para azul.
        Se a URL não for válida ou não levar a uma imagem válida, a cor do texto na caixa de texto da segunda URL será alterada para vermelho.

        """
        # Obtém o texto da caixa de texto da segunda URL
        texto = self.lineEditImageUrl2.text()
        if self.verificarValidadeURL(texto) and self.verificarValidadeURLImagem(texto):
            ExportarKMLDialog.ultimoTextoUrl2 = texto
            self.lineEditImageUrl2.setStyleSheet("QLineEdit { color: blue; }")
        else:
            ExportarKMLDialog.ultimoTextoUrl2 = ""
            if texto.strip() != "":
                self.lineEditImageUrl2.setStyleSheet("QLineEdit { color: red; }")
            else:
                self.lineEditImageUrl2.setStyleSheet("")

    def populate_fields(self):
        """
        Preenche o comboBox com os nomes dos campos da camada.

        Esta função obtém os campos da camada atual e adiciona os nomes dos campos ao comboBox na interface do usuário.
        """
        # Obtém os campos da camada
        fields = self.layer.fields()
        # Adiciona os nomes dos campos ao comboBox
        for field in fields:
            self.comboBox.addItem(field.name())

    def getValues(self):
        """
        Obtém os valores dos elementos da interface do usuário.

        Retorna uma tupla contendo os valores dos elementos da interface do usuário, que serão usados para exportação.
        """
        return (
            self.comboBox.currentText(), # Valor selecionado no comboBox
            self.tableCheckBox.isChecked(), # Estado de seleção do checkBox
            self.lineWidthSpinBox.value(),  # Valor do spinBox de largura da linha
            self.lineOpacitySpinBox.value(), # Valor do spinBox de opacidade da linha
            self.areaOpacitySpinBox.value(), # Valor do spinBox de opacidade da área
            self.heightSpinBox.value(),  # Valor do spinBox de altura
            self.checkBox3D.isChecked(), # Estado de seleção do checkBox 3D
            self.radioElevated.isChecked(), # Estado de seleção do radioButton 'Elevated'
            self.radioSolid.isChecked(), # Estado de seleção do radioButton 'Solid'
            self.radioEdges.isChecked(),  # Estado de seleção do radioButton 'Edges'
            self.lineEditImageUrl.text(),  # Texto inserido no lineEdit para URL de imagem
            self.lineEditImageUrl2.text(), # Texto inserido no segundo lineEdit para URL de imagem (se houver)
            #... [adicione mais valores conforme necessário]
        )

class ExportacaoDialogoDXF(QDialog):
    def __init__(self, layer, ui_manager, parent=None):
        """
        Inicializa uma instância do diálogo de exportação DXF, configurando variáveis iniciais e preparando a interface do usuário.
        
        :param layer: A camada do QGIS de onde os dados serão exportados.
        :param ui_manager: Instância do gerenciador de interface do usuário para acessar métodos e dados adicionais.
        :param parent: O widget pai deste diálogo, se houver.
        """
        super(ExportacaoDialogoDXF, self).__init__(parent)
        self.layer = layer  # Armazena a camada QGIS para uso posterior
        self.ui_manager = ui_manager  # Armazena a instância de UiManagerO para acessar métodos específicos

        # Dicionário para armazenar estilos de hachura personalizados
        self.hatchStyles = {}

        self.has_features = False
        self.has_fields = False

        # Mapeamento das hachuras do Qt para os padrões correspondentes em EZDXF
        self.qt_to_ezdxf_hatch_map = {
            Qt.BrushStyle.CrossPattern: "NET",
            Qt.BrushStyle.FDiagPattern: "ANS131",
            Qt.BrushStyle.HorPattern: "LINE",
            Qt.BrushStyle.SolidPattern: "SOLID"}

        # Inicializa a interface do usuário configurando controles e layouts
        self.initUI()

        # Utiliza o método do UiManagerO para obter a cor de preenchimento da camada em formato inteiro
        fill_color_int, _ = self.ui_manager.obter_cores_da_camada(self.layer)
        # Converte o inteiro para um QColor para uso em estilos de hachura
        fill_color_qcolor = QColor.fromRgb(fill_color_int)

        # Cria estilos de hachura com base na cor obtida
        self.create_hatch_styles(fill_color_qcolor)

        # Conecta a mudança de item no listWidget para ativar/desativar opções de exportação
        try:
            self.listWidget.currentItemChanged.disconnect(self.toggleExportOptions)
        except Exception:
            pass  # nosec B110

        self.listWidget.currentItemChanged.connect(self.toggleExportOptions)

        # Seleção inicial obrigatória.
        # Sem isso, a janela abre com escala, rotação, preview e botão Exportar bloqueados.
        if self.listWidget.count() > 0:
            self.listWidget.setCurrentRow(0)

        # Força estado inicial correto da interface
        self.toggleExportOptions(self.listWidget.currentItem(), None)
        self.checkLayerFeaturesAndFields()
        self.update_hatch_style()

    def initUI(self):
        """
        Configura a interface do usuário para o diálogo de exportação, organizando todos os controles necessários,
        incluindo seletores de campos, opções de visualização gráfica e botões de ação.

        Funções e Ações Desenvolvidas:
        - Estruturação de layouts e adição de widgets para configuração de campos, rótulos e visualização gráfica.
        - Configuração de conexões de sinais e slots para interatividade.
        - Inicialização e configuração de elementos gráficos e de controle.
        """
        frame = QFrame()
        frame.setFrameShape(QFrame.Shape.StyledPanel)
        frame.setFrameShadow(QFrame.Shadow.Raised)
        frameLayout = QVBoxLayout(frame)

        # ComboBox para seleção do campo da camada
        campoCamadaLayout = QHBoxLayout()
        labelCampoCamada = QLabel(self.tr("Selecione o Campo da Camada:"))
        campoCamadaLayout.addWidget(labelCampoCamada)

        self.comboBoxCampoCamada = QComboBox()
        self.comboBoxCampoCamada.addItems([field.name() for field in self.layer.fields()])
        self.comboBoxCampoCamada.setMaxVisibleItems(5)
        campoCamadaLayout.addWidget(self.comboBoxCampoCamada)

        frameLayout.addLayout(campoCamadaLayout)

        # ComboBox e CheckBox para seleção do campo do rótulo
        campoRotuloLayout = QHBoxLayout()
        labelCampoRotulo = QLabel(self.tr("Selecione o Campo do Rótulo:"))
        campoRotuloLayout.addWidget(labelCampoRotulo)

        self.checkBoxCampoRotulo = QCheckBox(self.tr("Ativar"))
        self.checkBoxCampoRotulo.setChecked(False)  # Inicia desmarcado
        campoRotuloLayout.addWidget(self.checkBoxCampoRotulo)

        self.comboBoxCampoRotulo = QComboBox()
        self.comboBoxCampoRotulo.addItems([field.name() for field in self.layer.fields()])
        self.comboBoxCampoRotulo.setMaxVisibleItems(5)
        self.comboBoxCampoRotulo.setEnabled(False)  # Inicia inativo
        campoRotuloLayout.addWidget(self.comboBoxCampoRotulo)

        frameLayout.addLayout(campoRotuloLayout)

        # Conectando o sinal do QCheckBox ao slot que irá ativar/desativar o QComboBox
        self.checkBoxCampoRotulo.stateChanged.connect(self.toggleComboBoxCampoRotulo)

        # Layout principal horizontal para todos os controles
        mainControlLayout = QHBoxLayout()

        # Configurando o QListWidget
        self.listWidget = QListWidget()
        self.listWidget.setFixedWidth(120)
        self.listWidget.setMinimumHeight(169)

        # Mantém a lista alinhada pelo topo da coluna direita
        mainControlLayout.addWidget(self.listWidget, 0, Qt.AlignmentFlag.AlignTop)

        # Layout vertical para scaleSpinBox, angleScrollBar e graphicsView
        rightSideLayout = QVBoxLayout()

        # Label e QDoubleSpinBox para a escala
        scaleLayout = QHBoxLayout()
        scaleLabel = QLabel(self.tr("Escala:"))
        scaleLayout.addWidget(scaleLabel)

        self.scaleSpinBox = QDoubleSpinBox()
        self.scaleSpinBox.setRange(0.1, 10.0)  # Define a faixa de valores
        self.scaleSpinBox.setSingleStep(0.5)  # Define o incremento dos passos
        self.scaleSpinBox.setValue(1.0)  # Define o valor inicial
        scaleLayout.addWidget(self.scaleSpinBox)

        rightSideLayout.addLayout(scaleLayout)

        # Label e QScrollBar para a rotação
        angleLayout = QHBoxLayout()
        angleLabel = QLabel(self.tr("Rotação:"))
        angleLayout.addWidget(angleLabel)

        self.angleScrollBar = QScrollBar(Qt.Orientation.Horizontal)
        self.angleScrollBar.setRange(0, 360)  # Ângulo de 0 a 360 graus
        self.angleScrollBar.setSingleStep(1)  # Passo de 1 grau
        self.angleScrollBar.setFixedHeight(10)  # Controla a espessura do QScrollBar
        self.angleScrollBar.setMinimumWidth(100)  # Controla o comprimento mínimo do QScrollBar
        angleLayout.addWidget(self.angleScrollBar)

        rightSideLayout.addLayout(angleLayout)

        # Label e QDoubleSpinBox para transparência
        transparencyLayout = QHBoxLayout()
        transparencyLabel = QLabel(self.tr("Transparência:"))
        transparencyLayout.addWidget(transparencyLabel)

        self.transparencySpinBox = QDoubleSpinBox()
        self.transparencySpinBox.setRange(0.0, 100.0)
        self.transparencySpinBox.setSingleStep(5.0)
        self.transparencySpinBox.setDecimals(0)
        self.transparencySpinBox.setValue(0.0)  # 0% = totalmente opaco
        self.transparencySpinBox.setSuffix(" %")
        self.transparencySpinBox.setToolTip(self.tr("0% = opaco | 100% = totalmente transparente"))
        transparencyLayout.addWidget(self.transparencySpinBox)

        rightSideLayout.addLayout(transparencyLayout)

        # Configurando o QGraphicsView
        self.graphicsView = QGraphicsView()
        self.graphicsView.setFixedSize(150, 120)
        # Definir políticas de barra de rolagem para nunca mostrar barras de rolagem
        self.graphicsView.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        self.graphicsView.setVerticalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)

        # Adicionando dicas de renderização para suavização
        self.graphicsView.setRenderHint(QPainter.RenderHint.Antialiasing, True)

        rightSideLayout.addWidget(self.graphicsView)

        # Adicionando o layout vertical à direita ao layout principal horizontal
        mainControlLayout.addLayout(rightSideLayout)

        # Adicionando o layout principal horizontal ao layout do frame
        frameLayout.addLayout(mainControlLayout)

        # Configuração do layout principal do diálogo
        mainLayout = QVBoxLayout()
        mainLayout.setContentsMargins(10, 10, 10, 10)
        mainLayout.setSpacing(8)

        # O frame fica sozinho, apenas com as configurações de exportação
        mainLayout.addWidget(frame)

        # Botões fora do frame, abaixo dele
        hbox = QHBoxLayout()
        hbox.addStretch(1)

        self.exportButton = QPushButton(self.tr("Exportar"))
        self.exportButton.clicked.connect(self.accept)
        hbox.addWidget(self.exportButton, 0, Qt.AlignmentFlag.AlignCenter)

        self.cancelButton = QPushButton(self.tr("Cancelar"))
        self.cancelButton.clicked.connect(self.reject)
        hbox.addWidget(self.cancelButton, 0, Qt.AlignmentFlag.AlignCenter)

        hbox.addStretch(1)

        mainLayout.addLayout(hbox)

        self.setLayout(mainLayout)

        # Definições do título e geometria do diálogo
        self.setWindowTitle(self.tr("Configurações de Exportação"))
        self.resize(300, 150)
        self.adjustSize()  # Ajusta o tamanho com base nos widgets
        self.centerDialog()

        # Configuração da cena do QGraphicsView
        self.scene = QGraphicsScene()
        self.graphicsView.setScene(self.scene)
        self.graphicsView.setBackgroundBrush(QBrush(QColor("white")))
        self.graphicsView.setRenderHint(QPainter.RenderHint.Antialiasing, True)

        # Conectando o sinal de mudança do QListWidget ao slot de atualização da cena
        self.listWidget.currentRowChanged.connect(self.update_hatch_style)

        # Conecta o sinal valueChanged do scaleSpinBox ao slot de atualização
        self.scaleSpinBox.valueChanged.connect(self.update_graphics_view_transform)

        # Conecta o sinal valueChanged do angleScrollBar ao slot de atualização
        self.angleScrollBar.valueChanged.connect(self.update_graphics_view_transform)

        self.transparencySpinBox.valueChanged.connect(self.update_graphics_view_transform)

        # Conecta o sinal valueChanged do angleScrollBar ao slot de atualização
        self.angleScrollBar.valueChanged.connect(self.show_angle_tooltip)

        self.toggleExportOptions(self.listWidget.currentItem(), None)

        # Checagem de feições e campos
        self.checkLayerFeaturesAndFields()

        # Ajusta a altura da lista após o Qt calcular o layout real
        QTimer.singleShot(0, self._alinhar_lista_com_preview)

    def _alinhar_lista_com_preview(self):
        """
        Ajusta a altura do QListWidget para terminar alinhado com a base do preview.

        Isso evita o vazio abaixo da lista quando a coluna direita ganha novos controles,
        como Transparência.
        """
        try:
            top_lista = self.listWidget.geometry().top()
            bottom_preview = self.graphicsView.geometry().bottom()

            nova_altura = bottom_preview - top_lista + 1
            nova_altura = max(169, int(nova_altura))

            self.listWidget.setFixedHeight(nova_altura)

            # Recalcula a janela após o ajuste
            self.adjustSize()

        except Exception:
            # Fallback seguro caso o layout ainda não tenha geometria calculada
            self.listWidget.setFixedHeight(190)
            self.adjustSize()

    def checkLayerFeaturesAndFields(self):
        """
        Verifica se a camada selecionada possui feições e campos, e atualiza os componentes da interface do usuário
        baseados nessas verificações. Este método ajusta a ativação de controles da UI e atualiza as listas de opções
        com base na presença de dados válidos na camada.

        Funções e Ações Desenvolvidas:
        - Verificação da contagem de feições e da existência de campos na camada.
        - Habilitação ou desabilitação de componentes da interface com base na disponibilidade de dados.
        - Atualização dos itens no comboBox e no botão de exportação baseados nas condições da camada.

        :return: None
        """
        # Atualiza o estado dos atributos da classe para refletir a presença de feições e campos
        self.has_features = self.layer.featureCount() > 0
        self.has_fields = len(self.layer.fields()) > 0

        # Habilita o comboBox para seleção de campos somente se houver feições e campos disponíveis
        self.comboBoxCampoCamada.setEnabled(self.has_features and self.has_fields)

        # Habilita o botão de exportação se houver um item selecionado no listWidget e a camada tiver feições e campos
        self.exportButton.setEnabled(self.has_features and self.has_fields and self.listWidget.currentItem() is not None)

        # Se a camada possui feições e campos, popula o comboBox com os nomes dos campos
        if self.has_features and self.has_fields:
            # Limpa itens existentes e adiciona os novos com base nos campos disponíveis
            self.comboBoxCampoCamada.clear()
            self.comboBoxCampoCamada.addItems([field.name() for field in self.layer.fields()])
        else:
            # Caso não haja campos disponíveis, limpa o comboBox e adiciona um item indicativo
            self.comboBoxCampoCamada.clear()
            self.comboBoxCampoCamada.addItem(self.tr("Nenhum campo disponível"))

    def toggleExportOptions(self, current, previous):
        """
        Atualiza a disponibilidade (habilitado/desabilitado) de várias opções e controles de exportação com base na
        seleção atual de um item e na disponibilidade de feições e campos na camada. Este método é crucial para garantir
        que o usuário só possa interagir com controles relevantes quando um item válido está selecionado.

        Funções e Ações Desenvolvidas:
        - Ativação ou desativação do botão de exportação dependendo da seleção e da presença de feições e campos.
        - Ativação ou desativação de controles como spinboxes e barras de rolagem com base na seleção de um item.

        :param current: O item atualmente selecionado (pode ser None se nenhum item estiver selecionado).
        :param previous: O item anteriormente selecionado (não utilizado diretamente, mas disponível para referência).
        """
        # Habilita o botão de exportar se um item está selecionado e a camada tem feições e campos válidos
        self.exportButton.setEnabled(current is not None and self.has_features and self.has_fields)
        
        # Habilita o spinbox de escala se um item está selecionado
        self.scaleSpinBox.setEnabled(current is not None)

        # Habilita a barra de rolagem de ângulo se um item está selecionado
        self.angleScrollBar.setEnabled(current is not None)

        self.transparencySpinBox.setEnabled(current is not None)

        # Habilita a visualização gráfica se um item está selecionado
        self.graphicsView.setEnabled(current is not None)

    def toggleComboBoxCampoRotulo(self):
        """
        Ativa ou desativa o comboBox de seleção de campos de rótulo com base no estado de um checkBox.
        Esta função é usada para garantir que o usuário só possa escolher um campo de rótulo quando a opção
        correspondente estiver ativa, evitando confusão e erros de configuração.

        Funções e Ações Desenvolvidas:
        - Leitura do estado do checkBox e atualização do estado de habilitação do comboBox.

        :return: None
        """
        # Ajusta a disponibilidade do comboBox de campos de rótulo de acordo com o estado do checkBox
        self.comboBoxCampoRotulo.setEnabled(self.checkBoxCampoRotulo.isChecked())

    def show_angle_tooltip(self, value):
        """
        Mostra o valor atual da rotação.
        O redesenho já é feito por update_graphics_view_transform.
        """
        tooltip_text = self.tr("Ângulo: {value}°").format(value=value)
        QToolTip.showText(QCursor.pos(), tooltip_text, self.angleScrollBar)

    def create_hatch_styles(self, fill_color):
        """
        Cria e adiciona estilos de hachura para serem usados na renderização gráfica ou em exportações.
        Define uma variedade de padrões visuais que podem representar diferentes materiais ou características,
        como linhas cruzadas para grades, sólidos para áreas preenchidas, ou padrões simulados para texturas específicas.

        Funções e Ações Desenvolvidas:
        - Adiciona estilos de hachura com padrões básicos e simulados.
        - Associa cada estilo de hachura a uma representação gráfica específica e a uma chave de mapeamento para exportação.

        :param fill_color: Cor de preenchimento a ser usada para todos os estilos de hachura.
        """
        # Adiciona estilos de hachura usando padrões do Qt e mapeamento para padrões do EZDXF
        self.add_hatch_style(self.tr("Linhas Cruzadas"), Qt.BrushStyle.CrossPattern, fill_color, self.qt_to_ezdxf_hatch_map[Qt.BrushStyle.CrossPattern])
        self.add_hatch_style(self.tr("Linhas Diagonais"), Qt.BrushStyle.FDiagPattern, fill_color, self.qt_to_ezdxf_hatch_map[Qt.BrushStyle.FDiagPattern])
        self.add_hatch_style(self.tr("Linhas Horizontais"), Qt.BrushStyle.HorPattern, fill_color, self.qt_to_ezdxf_hatch_map[Qt.BrushStyle.HorPattern])
        self.add_hatch_style(self.tr("Sólido"), Qt.BrushStyle.SolidPattern, fill_color, self.qt_to_ezdxf_hatch_map[Qt.BrushStyle.SolidPattern])

        # Padrão nativo DXF de pontos
        self.add_hatch_style("DOTS", Qt.BrushStyle.Dense7Pattern, fill_color, "DOTS")

        # Adiciona estilos de hachura com nomes e padrões simulados para representar diferentes texturas ou elementos
        self.add_hatch_style(self.tr("Cascalho (Simulado)"), Qt.BrushStyle.Dense7Pattern, fill_color, "GRAVEL")

        # Adiciona estilos de hachura com nomes e padrões simulados para representar diferentes texturas ou elementos
        self.add_hatch_style(self.tr("Cascalho (Simulado)"), Qt.BrushStyle.Dense7Pattern, fill_color, "GRAVEL")
        self.add_hatch_style(self.tr("Tijolo (Simulado)"), Qt.BrushStyle.BDiagPattern, fill_color, "BRICK")
        self.add_hatch_style(self.tr("Favo de Mel (Simulado)"), Qt.BrushStyle.Dense7Pattern, fill_color, "HONEY")
        self.add_hatch_style(self.tr("Triângulo (Simulado)"), Qt.BrushStyle.Dense7Pattern, fill_color, "TRIANG")
        self.add_hatch_style(self.tr("Flex (Simulado)"), Qt.BrushStyle.Dense7Pattern, fill_color, "FLEX")
        self.add_hatch_style(self.tr("Plantas (Simulado)"), Qt.BrushStyle.Dense7Pattern, fill_color, "SWAMP")

        if self.listWidget.count() > 0 and self.listWidget.currentRow() < 0:
            self.listWidget.setCurrentRow(0)

        self.update_hatch_style()

    def _draw_dots_preview(self, color):
        """
        Desenha o preview do padrão DOTS centralizado, com escala,
        rotação e transparência aplicadas visualmente.
        """
        rect = self._prepare_preview_scene()

        try:
            scale_value = float(self.scaleSpinBox.value() or 1.0)
        except Exception:
            scale_value = 1.0

        try:
            rotation_angle = float(self.angleScrollBar.value() or 0.0)
        except Exception:
            rotation_angle = 0.0

        scale_value = max(0.1, scale_value)

        diag = math.hypot(rect.width(), rect.height())
        pattern_w = diag * 2.2
        pattern_h = diag * 2.2

        group = QGraphicsItemGroup()
        self.scene.addItem(group)

        pen = QPen(color)
        pen.setWidthF(0.8)
        pen.setCosmetic(True)

        brush = QBrush(color)

        # Escala maior = espaçamento maior, semelhante à lógica da hachura DXF
        spacing = max(5.0, 8.0 * scale_value)
        dot_radius = max(0.8, 1.2 * min(scale_value, 2.0))

        rows = int(pattern_h / spacing) + 4
        cols = int(pattern_w / spacing) + 4

        for row in range(rows):
            y = row * spacing

            for col in range(cols):
                x = col * spacing

                dot = QGraphicsEllipseItem(
                    x - dot_radius,
                    y - dot_radius,
                    dot_radius * 2.0,
                    dot_radius * 2.0
                )
                dot.setPen(pen)
                dot.setBrush(brush)
                group.addToGroup(dot)

        group.setTransformOriginPoint(pattern_w / 2.0, pattern_h / 2.0)

        group.setPos(
            rect.center().x() - pattern_w / 2.0,
            rect.center().y() - pattern_h / 2.0)

        group.setRotation(rotation_angle)
        group.setZValue(10)

        self._add_preview_border(rect)
        self.scene.update()
        return True

    def draw_approximate_swamp_pattern(self, fill_color):
        """
        Desenha um padrão de hachura simulando um pântano na cena gráfica. O padrão consiste em uma combinação de
        linhas horizontais, verticais e inclinadas que criam uma representação visual de vegetação densa típica de pântanos.

        :param fill_color: A cor usada para desenhar o padrão.

        Funções e Ações Desenvolvidas:
        - Calcula a quantidade de padrões que cabem na área visível com base no tamanho da janela.
        - Desenha cada padrão repetidamente de acordo com a quantidade calculada.
        """
        # Parâmetros para o desenho do padrão SWAMP
        horizontal_length = 50
        vertical_length = 15  # Metade do comprimento pois estamos desenhando apenas a parte superior
        incline_length = 20
        space_between_patterns = 20  # Espaçamento adicional entre os padrões

        # Ajustando o espaçamento total incluindo o espaço entre os padrões
        pattern_spacing = horizontal_length + space_between_patterns
        width = self.graphicsView.width()
        height = self.graphicsView.height()

        # Obter escala e rotação dos controles da interface
        scale_factor = self.scaleSpinBox.value()
        rotation_angle = self.angleScrollBar.value()

        # Calcula quantos padrões cabem na altura e largura, adicionando extra para cobrir área rotacionada
        cols = int(width // pattern_spacing) + 2
        rows = int(height // (vertical_length + space_between_patterns)) + 2

        # Criar um QGraphicsItemGroup para agrupar todos os padrões SWAMP
        swamp_group = QGraphicsItemGroup()

        for i in range(rows):
            for j in range(cols):
                # Posição central do padrão
                x_center = j * pattern_spacing + pattern_spacing / 2
                y_center = i * (vertical_length + space_between_patterns) + vertical_length / 2

                # Criando o caminho para o padrão SWAMP
                path = QPainterPath()
                # Linha horizontal
                path.moveTo(x_center - horizontal_length / 2, y_center)
                path.lineTo(x_center + horizontal_length / 2, y_center)
                # Linha vertical superior
                path.moveTo(x_center, y_center)
                path.lineTo(x_center, y_center - vertical_length)
                # Linhas inclinadas
                path.moveTo(x_center, y_center)
                path.lineTo(x_center - incline_length * math.cos(math.radians(45)),
                            y_center - incline_length * math.sin(math.radians(45)))
                path.moveTo(x_center, y_center)
                path.lineTo(x_center + incline_length * math.cos(math.radians(45)),
                            y_center - incline_length * math.sin(math.radians(45)))

                # Criando o item gráfico com o caminho e adicionando ao grupo
                swamp_item = QGraphicsPathItem(path)
                swamp_item.setPen(QPen(fill_color, 1))
                swamp_group.addToGroup(swamp_item)

        # Centralizar o grupo do padrão SWAMP em torno do ponto (0, 0)
        pattern_width = cols * pattern_spacing
        pattern_height = rows * (vertical_length + space_between_patterns)
        swamp_group.setTransformOriginPoint(pattern_width / 2, pattern_height / 2)

        # Aplicar escala e rotação
        transform = QTransform()
        transform.scale(scale_factor, scale_factor)
        transform.rotate(rotation_angle)
        swamp_group.setTransform(transform)

        # Posicionar o grupo no centro do QGraphicsView
        view_center = self.graphicsView.viewport().rect().center()
        scene_center = self.graphicsView.mapToScene(view_center)
        swamp_group.setPos(scene_center.x() - pattern_width / 2, scene_center.y() - pattern_height / 2)

        # Adicionar o grupo à cena
        self.scene.addItem(swamp_group)

    def draw_approximate_triangle_pattern(self, fill_color):
        """
        Desenha um padrão de triângulos na cena gráfica, posicionando-os de forma regular para cobrir toda a área visível.
        Este método é útil para visualizações que requerem uma representação geométrica estilizada, como em interfaces de design gráfico ou visualização de dados.

        :param fill_color: A cor usada para desenhar o contorno dos triângulos.

        Funções e Ações Desenvolvidas:
        - Calcula o número de triângulos que cabem na largura e altura da área de visualização.
        - Cria e posiciona cada triângulo com base em seu índice de coluna e linha.
        - Adiciona cada triângulo à cena gráfica.
        """
        # Configurações para o tamanho e o espaçamento dos triângulos
        triangle_height = 15
        triangle_base = 15
        spacing = 10  # Espaço adicional entre os triângulos
        width = self.graphicsView.width()
        height = self.graphicsView.height()
        
        # Obter escala e rotação dos controles da interface
        scale_factor = self.scaleSpinBox.value()
        rotation_angle = self.angleScrollBar.value()

        # Calcular o número de colunas e linhas de triângulos e adicionar extra para cobrir área rotacionada
        cols = int(width / (triangle_base + spacing)) + 2
        rows = int(height / (triangle_height + spacing / 2)) + 2

        # Criar um QGraphicsItemGroup para agrupar todos os triângulos
        triangle_group = QGraphicsItemGroup()

        for col in range(cols):
            for row in range(rows):
                # Posiciona o triângulo baseado na coluna e linha atual
                x = col * (triangle_base + spacing)
                y = row * (triangle_height + spacing / 2)
                
                # Cria o caminho para o triângulo
                path = QPainterPath()
                path.moveTo(x, y)
                path.lineTo(x + triangle_base / 2, y + triangle_height)
                path.lineTo(x - triangle_base / 2, y + triangle_height)
                path.closeSubpath()
                
                # Cria o item gráfico e adiciona ao grupo
                triangle_item = QGraphicsPathItem(path)
                triangle_item.setPen(QPen(fill_color, 1))  # A cor da borda e a espessura
                triangle_group.addToGroup(triangle_item)

        # Centralizar o grupo de triângulos em torno do ponto (0, 0)
        pattern_width = cols * (triangle_base + spacing)
        pattern_height = rows * (triangle_height + spacing / 2)
        triangle_group.setTransformOriginPoint(pattern_width / 2, pattern_height / 2)

        # Aplicar escala e rotação
        transform = QTransform()
        transform.scale(scale_factor, scale_factor)
        transform.rotate(rotation_angle)
        triangle_group.setTransform(transform)

        # Posicionar o grupo no centro do QGraphicsView
        view_center = self.graphicsView.viewport().rect().center()
        scene_center = self.graphicsView.mapToScene(view_center)
        triangle_group.setPos(scene_center.x() - pattern_width / 2, scene_center.y() - pattern_height / 2)

        # Adicionar o grupo à cena
        self.scene.addItem(triangle_group)

    def draw_approximate_flex_pattern(self, fill_color):
        """
        Desenha um padrão flexível em ziguezague na cena gráfica. Este padrão é formado por linhas retas com pequenas
        inclinações nas extremidades, dando a impressão de movimento ou flexibilidade.

        :param fill_color: Cor usada para desenhar o padrão.

        Funções e Ações Desenvolvidas:
        - Calcula a disposição do padrão na área de visualização.
        - Cria e posiciona linhas em um padrão de ziguezague com deslocamentos inclinados.
        - Adiciona cada linha criada à cena gráfica.
        """
        # Configurações iniciais para as dimensões e espaçamentos do padrão
        segment_length = 20  # Comprimento do segmento reto
        incline_offset = 5   # Deslocamento das partes inclinadas
        row_spacing = 10     # Espaçamento vertical entre as linhas do padrão
        pattern_spacing = 20 # Espaçamento entre os padrões ziguezague
        width = self.graphicsView.width()
        height = self.graphicsView.height()

        # Obter escala e rotação dos controles da interface
        scale_factor = self.scaleSpinBox.value()
        rotation_angle = self.angleScrollBar.value()

        # Calcular o número de colunas e linhas, adicionando extra para cobrir área rotacionada
        num_cols = int((width / (segment_length + pattern_spacing))) + 2
        num_rows = int((height / row_spacing)) + 2

        # Criar um QGraphicsItemGroup para agrupar todas as linhas do padrão FLEX
        flex_group = QGraphicsItemGroup()

        # Inicia o desenho do padrão
        for row in range(num_rows):
            y = row * row_spacing
            for col in range(num_cols):
                x = col * (segment_length + pattern_spacing)

                # Ponto inicial da linha retilínea do meio
                start_point = QPointF(x, y)
                # Ponto final da linha retilínea do meio
                end_point = QPointF(x + segment_length, y)

                # Calcula os pontos de inclinação com base nos ângulos dados
                left_incline = QPointF(
                    start_point.x() - incline_offset * math.cos(math.radians(-45)),
                    start_point.y() - incline_offset * math.sin(math.radians(-45)))
                right_incline = QPointF(
                    end_point.x() + incline_offset * math.cos(math.radians(-45)),
                    end_point.y() + incline_offset * math.sin(math.radians(-45)))

                # Cria o caminho para o padrão 'FLEX'
                path = QPainterPath()
                path.moveTo(left_incline)
                path.lineTo(start_point)
                path.lineTo(end_point)
                path.lineTo(right_incline)

                # Cria o item gráfico e adiciona ao grupo
                flex_item = QGraphicsPathItem(path)
                flex_item.setPen(QPen(fill_color, 2))
                flex_group.addToGroup(flex_item)

        # Calcular as dimensões totais do padrão
        pattern_width = num_cols * (segment_length + pattern_spacing)
        pattern_height = num_rows * row_spacing

        # Centralizar o grupo do padrão flex em torno do ponto (0, 0)
        flex_group.setTransformOriginPoint(pattern_width / 2, pattern_height / 2)

        # Aplicar escala e rotação
        transform = QTransform()
        transform.scale(scale_factor, scale_factor)
        transform.rotate(rotation_angle)
        flex_group.setTransform(transform)

        # Posicionar o grupo no centro do QGraphicsView
        view_center = self.graphicsView.viewport().rect().center()
        scene_center = self.graphicsView.mapToScene(view_center)
        flex_group.setPos(scene_center.x() - pattern_width / 2, scene_center.y() - pattern_height / 2)

        # Adicionar o grupo à cena
        self.scene.addItem(flex_group)

    def draw_approximate_gravel_pattern(self, fill_color):
        """
        Desenha um padrão de cascalho simulando pedras irregulares espalhadas aleatoriamente.
        O padrão é centralizado, escalável e rotacionável de acordo com os controles da interface.

        A função executa as seguintes etapas:
        1. Define parâmetros iniciais, incluindo o número de formas (num_shapes) e o tamanho máximo das pedras (max_size).
        2. Calcula o tamanho da área do padrão (pattern_width e pattern_height) com base nas dimensões da `graphicsView`.
        3. Calcula o tamanho das células da grade (grid_size) para distribuir uniformemente as formas.
        4. Cria um grupo gráfico (`QGraphicsItemGroup`) para agrupar todas as formas de cascalho.
        5. Para cada célula na grade, posiciona aleatoriamente uma forma de cascalho dentro da célula, centralizando o padrão em torno da origem (0, 0).
        6. Cria formas irregulares para simular pedras, usando `QPainterPath`, e adiciona ao grupo.
        7. Centraliza o grupo de cascalho em torno do ponto (0, 0) no espaço gráfico.
        8. Aplica transformações de escala e rotação ao grupo com base nos controles da interface.
        9. Posiciona o grupo de forma que o centro do padrão coincida com o centro da área visível do `QGraphicsView`.
        10. Adiciona o grupo à cena gráfica para que o padrão seja exibido na interface.

        :param fill_color: A cor usada para desenhar as bordas das formas de cascalho.
        """
        num_shapes = 80
        max_size = 10  # Máximo tamanho dos "cascalhos"

        # Obter escala e rotação dos controles da interface
        scale_factor = self.scaleSpinBox.value()
        rotation_angle = self.angleScrollBar.value()

        # Definir as dimensões do padrão (ajustadas para centralização)
        pattern_width = self.graphicsView.width()
        pattern_height = self.graphicsView.height()

        # Calcula o tamanho da célula da grade com base no número desejado de cascalhos
        grid_size = int(math.sqrt(pattern_width * pattern_height / num_shapes))
        cols = int(pattern_width / grid_size) + 2  # Adiciona extra para cobrir área rotacionada
        rows = int(pattern_height / grid_size) + 2

        # Criar um QGraphicsItemGroup para agrupar todas as formas de cascalho
        gravel_group = QGraphicsItemGroup()

        for i in range(cols):
            for j in range(rows):
                # Posição inicial da célula, centralizada em torno de (0, 0)
                x_start = (i - cols / 2) * grid_size
                y_start = (j - rows / 2) * grid_size

                # Variações aleatórias usadas somente para desenhar o cascalho.
                x_center = x_start + random.uniform(  # nosec B311
                    max_size,
                    grid_size - max_size)
                y_center = y_start + random.uniform(  # nosec B311
                    max_size,
                    grid_size - max_size)

                size = random.uniform(max_size * 0.5, max_size)  # nosec B311
                path = QPainterPath()

                start_angle = random.uniform(0, 2 * math.pi)  # nosec B311

                path.moveTo(
                    x_center + size * math.cos(start_angle),
                    y_center + size * math.sin(start_angle))

                for angle in range(1, 360,
                    random.randint(20, 50)):  # nosec B311
                
                    irregularity = random.uniform(1, 1.2)  # nosec B311
                    
                    theta = math.radians(angle) + start_angle
                    x = x_center + irregularity * size * math.cos(theta)
                    y = y_center + irregularity * size * math.sin(theta)
                    path.lineTo(x, y)
                path.closeSubpath()

                # Cria um item gráfico com o caminho e adiciona ao grupo
                gravel = QGraphicsPathItem(path)
                gravel.setPen(QPen(fill_color, 1.1))
                gravel_group.addToGroup(gravel)

        # Centralizar o grupo de cascalhos em torno do ponto (0, 0)
        gravel_group.setTransformOriginPoint(0, 0)

        # Aplicar escala e rotação
        transform = QTransform()
        transform.scale(scale_factor, scale_factor)
        transform.rotate(rotation_angle)
        gravel_group.setTransform(transform)

        # Posicionar o grupo no centro do QGraphicsView
        view_center = self.graphicsView.viewport().rect().center()
        scene_center = self.graphicsView.mapToScene(view_center)
        gravel_group.setPos(scene_center.x(), scene_center.y())

        # Adicionar o grupo à cena
        self.scene.addItem(gravel_group)

    def draw_approximate_brick_pattern(self, fill_color):
        """
        Desenha um padrão de tijolos retangulares em uma cena gráfica dentro do QGraphicsView. O padrão é ajustado
        para permitir rotação e escala com base nos controles de interface (scaleSpinBox e angleScrollBar), 
        e é centralizado na área visível da interface gráfica.

        A função executa as seguintes etapas:
        1. Define as dimensões dos tijolos (brick_width e brick_height).
        2. Obtém o valor da escala e rotação a partir dos controles da interface.
        3. Calcula o número de colunas e linhas de tijolos necessárias para cobrir a área visível, adicionando
           um extra para garantir que a área seja completamente coberta após a rotação.
        4. Cria um grupo de gráficos (`QGraphicsItemGroup`) para agrupar todos os tijolos.
        5. Para cada linha e coluna, cria tijolos individuais (`QGraphicsRectItem`), aplicando um deslocamento
           alternado em linhas ímpares para simular um padrão de alvenaria (offset horizontal).
        6. Centraliza o padrão de tijolos em torno do ponto (0, 0) no espaço gráfico, aplicando as transformações
           de escala e rotação.
        7. Posiciona o padrão de tijolos de forma que o centro do padrão coincida com o centro da área visível
           do `QGraphicsView`.
        8. Adiciona o grupo de tijolos à cena gráfica para que o padrão seja exibido na interface.

        :param fill_color: A cor usada para desenhar as bordas dos tijolos.
        """
        # Definir as dimensões do tijolo e obter escala e rotação dos controles da interface
        brick_width = 40
        brick_height = 20
        scale_factor = self.scaleSpinBox.value()
        rotation_angle = self.angleScrollBar.value()
        
        # Preparar variáveis
        width = self.graphicsView.width()
        height = self.graphicsView.height()
        
        # Determinar quantos tijolos cabem horizontalmente e verticalmente
        num_cols = int(width / brick_width) + 2  # Adicionar extra para cobrir área rotacionada
        num_rows = int(height / brick_height) + 2
        
        # Calcular as dimensões totais do padrão
        pattern_width = num_cols * brick_width
        pattern_height = num_rows * brick_height
        
        # Criar um QGraphicsItemGroup para agrupar todos os tijolos
        brick_group = QGraphicsItemGroup()
        
        for row in range(num_rows):
            # Alternar o deslocamento de linha (offset horizontal)
            row_offset = (row % 2) * (brick_width / 2)
            y = row * brick_height
            
            for col in range(num_cols):
                x = col * brick_width + row_offset
                # Criar um item retangular representando o tijolo
                brick = QGraphicsRectItem(x, y, brick_width, brick_height)
                brick.setPen(QPen(fill_color, 1))
                # Adicionar o tijolo ao grupo
                brick_group.addToGroup(brick)
        
        # Centralizar o padrão em torno do ponto (0, 0)
        brick_group.setTransformOriginPoint(pattern_width / 2, pattern_height / 2)
        
        # Aplicar escala e rotação
        transform = QTransform()
        transform.scale(scale_factor, scale_factor)
        transform.rotate(rotation_angle)
        brick_group.setTransform(transform)
        
        # Posicionar o grupo no centro do QGraphicsView
        view_center = self.graphicsView.viewport().rect().center()
        scene_center = self.graphicsView.mapToScene(view_center)
        brick_group.setPos(scene_center.x() - pattern_width / 2, scene_center.y() - pattern_height / 2)
        
        # Adicionar o grupo à cena
        self.scene.addItem(brick_group)

    def draw_approximate_honey_pattern(self, fill_color):
        """
        Desenha um padrão de favo de mel com hexágonos regulares na cena gráfica. O padrão simula a estrutura natural
        de um favo de mel, amplamente utilizado em visualizações que necessitam de padrões geométricos repetidos.

        :param fill_color: Cor utilizada para desenhar o contorno dos hexágonos.

        Funções e Ações Desenvolvidas:
        - Calcula o número de colunas e linhas de hexágonos que cabem na área de visualização.
        - Alternância do deslocamento horizontal a cada linha para imitar a disposição natural de um favo de mel.
        - Criação e posicionamento de cada hexágono dentro da área da visualização.
        """
        # Configurações iniciais para o tamanho dos hexágonos
        hex_radius = 15  # Raio do hexágono
        hex_apothem = hex_radius * math.sqrt(3) / 2  # Distância do centro do hexágono ao meio de uma das arestas
        
        # Obter escala e rotação dos controles da interface
        scale_factor = self.scaleSpinBox.value()
        rotation_angle = self.angleScrollBar.value()

        # Dimensões da área de visualização
        width = self.graphicsView.width()
        height = self.graphicsView.height()

        # Calcula quantas colunas e linhas cabem na área disponível
        rows = int(height // (hex_radius * 1.5)) + 2  # Adiciona extra para cobrir área rotacionada
        cols = int(width // (hex_apothem * 2)) + 2

        # Criar um QGraphicsItemGroup para agrupar todos os hexágonos
        honeycomb_group = QGraphicsItemGroup()

        # Itera sobre cada linha e coluna para desenhar os hexágonos
        for row in range(rows):
            for col in range(cols):
                # Alternar o deslocamento a cada outra linha
                if row % 2 == 0:
                    x_offset = col * hex_apothem * 2
                else:
                    x_offset = col * hex_apothem * 2 + hex_apothem

                y_offset = row * (hex_radius * 1.5)

                # Cria o caminho do hexágono
                path = QPainterPath()
                angle_deg = 30
                angle_rad = math.pi / 180 * angle_deg

                # Adiciona os pontos para formar o hexágono
                for i in range(6):
                    x = hex_radius * math.cos(angle_rad + (math.pi / 3 * i)) + x_offset
                    y = hex_radius * math.sin(angle_rad + (math.pi / 3 * i)) + y_offset
                    if i == 0:
                        path.moveTo(x, y)
                    else:
                        path.lineTo(x, y)
                path.closeSubpath()

                # Cria o item do hexágono e adiciona ao grupo
                hex_item = QGraphicsPathItem(path)
                hex_item.setPen(QPen(fill_color, 1))  # Define a borda do favo de mel
                honeycomb_group.addToGroup(hex_item)

        # Centralizar o grupo de hexágonos em torno do ponto (0, 0)
        pattern_width = cols * hex_apothem * 2
        pattern_height = rows * hex_radius * 1.5
        honeycomb_group.setTransformOriginPoint(pattern_width / 2, pattern_height / 2)

        # Aplicar escala e rotação
        transform = QTransform()
        transform.scale(scale_factor, scale_factor)
        transform.rotate(rotation_angle)
        honeycomb_group.setTransform(transform)

        # Posicionar o grupo no centro do QGraphicsView
        view_center = self.graphicsView.viewport().rect().center()
        scene_center = self.graphicsView.mapToScene(view_center)
        honeycomb_group.setPos(scene_center.x() - pattern_width / 2, scene_center.y() - pattern_height / 2)

        # Adicionar o grupo à cena
        self.scene.addItem(honeycomb_group)

    def _prepare_preview_scene(self):
        """
        Prepara a cena do preview com fundo branco e dimensões consistentes.
        Retorna o retângulo útil do preview.
        """
        self.scene.clear()

        try:
            self.graphicsView.resetTransform()
        except Exception:
            pass  # nosec B110

        try:
            self.graphicsView.setBackgroundBrush(QBrush(QColor("white")))
        except Exception:
            pass  # nosec B110

        try:
            view_w = max(120, self.graphicsView.viewport().width())
            view_h = max(90, self.graphicsView.viewport().height())
        except Exception:
            view_w, view_h = 150, 120

        self.scene.setSceneRect(0, 0, view_w, view_h)

        rect = QRectF(4, 4, view_w - 8, view_h - 8)

        fundo = QGraphicsRectItem(rect)
        fundo.setBrush(QBrush(QColor("white")))
        fundo.setPen(QPen(QColor(180, 180, 180), 1))
        fundo.setZValue(-10)
        self.scene.addItem(fundo)

        return rect

    def _add_preview_border(self, rect):
        """
        Mascara tudo que sair da área útil do preview e desenha a moldura por cima.
        Isso evita que padrões rotacionados apareçam fora do gráfico.
        """
        if rect is None:
            return

        scene_rect = self.scene.sceneRect()
        mask_brush = QBrush(QColor("white"))
        mask_pen = QPen(Qt.PenStyle.NoPen)

        masks = [
            # topo
            QRectF(
                scene_rect.left(),
                scene_rect.top(),
                scene_rect.width(),
                rect.top() - scene_rect.top()),
            # baixo
            QRectF(
                scene_rect.left(),
                rect.bottom(),
                scene_rect.width(),
                scene_rect.bottom() - rect.bottom()),
            # esquerda
            QRectF(
                scene_rect.left(),
                rect.top(),
                rect.left() - scene_rect.left(),
                rect.height()),
            # direita
            QRectF(
                rect.right(),
                rect.top(),
                scene_rect.right() - rect.right(),
                rect.height())]

        for r in masks:
            if r.width() <= 0 or r.height() <= 0:
                continue
            item = QGraphicsRectItem(r)
            item.setBrush(mask_brush)
            item.setPen(mask_pen)
            item.setZValue(900)
            self.scene.addItem(item)

        borda = QGraphicsRectItem(rect)
        borda.setBrush(QBrush(Qt.BrushStyle.NoBrush))
        borda.setPen(QPen(QColor(120, 120, 120), 1))
        borda.setZValue(999)
        self.scene.addItem(borda)

    def _draw_simulated_pattern_preview(self, style_name, color):
        """
        Desenha os padrões simulados centralizados e recortados dentro do preview.

        Corrige:
        - padrões saindo da área do gráfico;
        - deslocamento ao rotacionar;
        - desenhos simulados ficando presos no canto.
        """
        rect = self._prepare_preview_scene()

        try:
            scale_value = float(self.scaleSpinBox.value() or 1.0)
        except Exception:
            scale_value = 1.0

        try:
            rotation_angle = float(self.angleScrollBar.value() or 0.0)
        except Exception:
            rotation_angle = 0.0

        scale_value = max(0.1, scale_value)

        # Área grande o suficiente para continuar cobrindo o preview após rotação
        diag = math.hypot(rect.width(), rect.height())
        pattern_w = diag * 2.4
        pattern_h = diag * 2.4

        group = QGraphicsItemGroup()
        self.scene.addItem(group)

        pen = QPen(color)
        pen.setWidthF(1.0)
        pen.setCosmetic(True)

        style_name = str(style_name or "")

        def add_path(path, width=1.0):
            item = QGraphicsPathItem(path)
            p = QPen(color)
            p.setWidthF(width)
            p.setCosmetic(True)
            item.setPen(p)
            item.setBrush(QBrush(Qt.BrushStyle.NoBrush))
            group.addToGroup(item)

        def add_rect(x, y, w, h):
            item = QGraphicsRectItem(x, y, w, h)
            item.setPen(pen)
            item.setBrush(QBrush(Qt.BrushStyle.NoBrush))
            group.addToGroup(item)

        if style_name == self.tr("Tijolo (Simulado)"):
            brick_w = 34.0
            brick_h = 17.0

            rows = int(pattern_h / brick_h) + 4
            cols = int(pattern_w / brick_w) + 4

            for row in range(rows):
                offset = (brick_w / 2.0) if row % 2 else 0.0
                y = row * brick_h
                for col in range(cols):
                    x = col * brick_w - offset
                    add_rect(x, y, brick_w, brick_h)

        elif style_name == self.tr("Favo de Mel (Simulado)"):
            radius = 10.0
            apothem = radius * math.sqrt(3.0) / 2.0

            row_step = radius * 1.5
            col_step = apothem * 2.0

            rows = int(pattern_h / row_step) + 4
            cols = int(pattern_w / col_step) + 4

            for row in range(rows):
                for col in range(cols):
                    x0 = col * col_step + (apothem if row % 2 else 0.0)
                    y0 = row * row_step

                    path = QPainterPath()
                    for i in range(6):
                        a = math.radians(30 + 60 * i)
                        x = x0 + radius * math.cos(a)
                        y = y0 + radius * math.sin(a)

                        if i == 0:
                            path.moveTo(x, y)
                        else:
                            path.lineTo(x, y)

                    path.closeSubpath()
                    add_path(path)

        elif style_name == self.tr("Triângulo (Simulado)"):
            tri_w = 18.0
            tri_h = 16.0
            spacing_x = 24.0
            spacing_y = 22.0

            rows = int(pattern_h / spacing_y) + 4
            cols = int(pattern_w / spacing_x) + 4

            for row in range(rows):
                for col in range(cols):
                    x = col * spacing_x
                    y = row * spacing_y

                    path = QPainterPath()
                    path.moveTo(x, y)
                    path.lineTo(x + tri_w / 2.0, y + tri_h)
                    path.lineTo(x - tri_w / 2.0, y + tri_h)
                    path.closeSubpath()

                    add_path(path)

        elif style_name == self.tr("Flex (Simulado)"):
            segment = 22.0
            incline = 6.0
            spacing_x = 42.0
            spacing_y = 13.0

            rows = int(pattern_h / spacing_y) + 4
            cols = int(pattern_w / spacing_x) + 4

            for row in range(rows):
                y = row * spacing_y
                for col in range(cols):
                    x = col * spacing_x

                    path = QPainterPath()
                    path.moveTo(x - incline, y + incline)
                    path.lineTo(x, y)
                    path.lineTo(x + segment, y)
                    path.lineTo(x + segment + incline, y - incline)

                    add_path(path, width=1.2)

        elif style_name == self.tr("Plantas (Simulado)"):
            spacing_x = 42.0
            spacing_y = 28.0
            stem = 13.0
            arm = 13.0

            rows = int(pattern_h / spacing_y) + 4
            cols = int(pattern_w / spacing_x) + 4

            for row in range(rows):
                for col in range(cols):
                    x = col * spacing_x
                    y = row * spacing_y

                    path = QPainterPath()

                    # base horizontal
                    path.moveTo(x - 17, y)
                    path.lineTo(x + 17, y)

                    # haste
                    path.moveTo(x, y)
                    path.lineTo(x, y - stem)

                    # folhas
                    path.moveTo(x, y)
                    path.lineTo(x - arm, y - arm)

                    path.moveTo(x, y)
                    path.lineTo(x + arm, y - arm)

                    add_path(path)

        elif style_name == self.tr("Cascalho (Simulado)"):
            rnd = random.Random(12345)  # nosec B311

            cell = 16.0
            rows = int(pattern_h / cell) + 4
            cols = int(pattern_w / cell) + 4

            for row in range(rows):
                for col in range(cols):
                    cx = col * cell + rnd.uniform(3, cell - 3)
                    cy = row * cell + rnd.uniform(3, cell - 3)
                    size = rnd.uniform(2.5, 5.5)

                    path = QPainterPath()
                    steps = rnd.randint(5, 8)

                    for i in range(steps):
                        a = (2.0 * math.pi * i / steps) + rnd.uniform(-0.25, 0.25)
                        r = size * rnd.uniform(0.75, 1.25)
                        x = cx + r * math.cos(a)
                        y = cy + r * math.sin(a)

                        if i == 0:
                            path.moveTo(x, y)
                        else:
                            path.lineTo(x, y)

                    path.closeSubpath()
                    add_path(path, width=0.9)

        else:
            return False

        # Centro geométrico do padrão em coordenadas locais
        group.setTransformOriginPoint(pattern_w / 2.0, pattern_h / 2.0)

        # Posiciona o centro do padrão no centro do preview
        group.setPos(
            rect.center().x() - pattern_w / 2.0,
            rect.center().y() - pattern_h / 2.0)

        # Rotação e escala sempre pelo centro
        group.setScale(scale_value)
        group.setRotation(rotation_angle)
        group.setZValue(10)

        # Recorta visualmente tudo que ultrapassar o retângulo útil
        self._add_preview_border(rect)

        self.scene.update()
        return True

    def _get_transparency_percent(self) -> float:
        """
        Retorna a transparência configurada na interface.

        0   = opaco
        100 = totalmente transparente
        """
        try:
            value = float(self.transparencySpinBox.value())
        except Exception:
            value = 0.0

        return max(0.0, min(100.0, value))

    def _color_with_export_transparency(self, color: QColor) -> QColor:
        """
        Aplica a transparência do spinBox à cor usada no preview.
        """
        c = QColor(color)
        transparency = self._get_transparency_percent()

        alpha = int(round(255.0 * (1.0 - transparency / 100.0)))
        alpha = max(0, min(255, alpha))

        c.setAlpha(alpha)
        return c

    def update_hatch_style(self, index=None):
        """
        Atualiza o preview da hachura selecionada.

        - Linhas básicas: desenho manual com rotação real.
        - Itens simulados: chama os métodos próprios de desenho.
        - Sólido: usa preenchimento simples.
        """
        if not hasattr(self, "scene") or self.scene is None:
            return

        item = self.listWidget.currentItem()

        if item is None:
            if isinstance(index, int) and index >= 0:
                item = self.listWidget.item(index)
                if item is not None:
                    self.listWidget.setCurrentItem(item)
            else:
                return

        if item is None:
            return

        style_name = item.text()

        if style_name not in self.hatchStyles:
            return

        pattern, color, ezdxf_pattern = self.hatchStyles[style_name]
        preview_color = self._color_with_export_transparency(color)

        try:
            angle = float(self.angleScrollBar.value())
        except Exception:
            angle = 0.0

        try:
            scale = float(self.scaleSpinBox.value())
        except Exception:
            scale = 1.0

        # 1) Padrões lineares com rotação real
        if style_name in (self.tr("Linhas Cruzadas"), self.tr("Linhas Diagonais"), self.tr("Linhas Horizontais")):
            if self._draw_rotated_line_preview(style_name, preview_color, angle, scale):
                return

        if style_name == "DOTS":
            if self._draw_dots_preview(preview_color):
                return

        # 2) Padrões simulados com desenho próprio
        if style_name in (
            self.tr("Cascalho (Simulado)"),
            self.tr("Tijolo (Simulado)"),
            self.tr("Favo de Mel (Simulado)"),
            self.tr("Triângulo (Simulado)"),
            self.tr("Flex (Simulado)"),
            self.tr("Plantas (Simulado)")):
            if self._draw_simulated_pattern_preview(style_name, preview_color):
                return

        # 3) Fallback, principalmente para Sólido
        rect = self._prepare_preview_scene()

        preview = QGraphicsRectItem(rect)

        if pattern == Qt.BrushStyle.TexturePattern:
            brush = QBrush(preview_color)
        else:
            brush = QBrush(pattern)
            brush.setColor(preview_color)

        preview.setBrush(brush)
        preview.setPen(QPen(QColor(120, 120, 120), 1))
        self.scene.addItem(preview)

        self._add_preview_border(rect)
        self.scene.update()

    def add_hatch_style(self, style_name, qt_pattern, color, ezdxf_pattern):
        """
        Adiciona um estilo de hachura ao dicionário interno e à lista de interface do usuário para seleção.
        Cada estilo contém um padrão do Qt, uma cor, e um padrão correspondente do EZDXF, permitindo que seja 
        usado tanto para renderização gráfica quanto para exportação para arquivos DXF.

        Funções e Ações Desenvolvidas:
        - Registro do estilo de hachura no dicionário interno para referência futura.
        - Adição do nome do estilo na lista de interface do usuário para facilitar a seleção pelo usuário.

        :param style_name: Nome descritivo do estilo de hachura.
        :param qt_pattern: Padrão de hachura do Qt usado para a renderização gráfica.
        :param color: Cor aplicada ao padrão de hachura.
        :param ezdxf_pattern: Padrão correspondente no formato EZDXF, utilizado para exportação para DXF.
        """
        # Armazena o estilo de hachura no dicionário com o nome como chave
        self.hatchStyles[style_name] = (qt_pattern, color, ezdxf_pattern)
        
        # Adiciona o nome do estilo ao listWidget para permitir seleção pelo usuário
        self.listWidget.addItem(style_name)

    def _draw_line_family(self, rect, angle_deg, spacing, pen):
        """
        Desenha uma família de linhas paralelas cobrindo todo o retângulo.

        Diferente do desenho anterior, esta função calcula as interseções
        das linhas com as bordas do retângulo. Assim as diagonais não ficam
        pela metade.
        """
        if rect is None or rect.isEmpty():
            return

        cx = rect.center().x()
        cy = rect.center().y()

        theta = math.radians(float(angle_deg or 0.0))

        # Vetor diretor da linha
        dx = math.cos(theta)
        dy = math.sin(theta)

        # Vetor normal, usado para deslocar linhas paralelas
        nx = -dy
        ny = dx

        diag = math.hypot(rect.width(), rect.height())
        spacing = max(3.0, float(spacing or 8.0))

        left = rect.left()
        right = rect.right()
        top = rect.top()
        bottom = rect.bottom()

        offset = -diag
        while offset <= diag:
            px = cx + nx * offset
            py = cy + ny * offset

            candidates = []

            # Interseções com x = left e x = right
            if abs(dx) > 1e-9:
                for x in (left, right):
                    t = (x - px) / dx
                    y = py + t * dy
                    if top - 0.5 <= y <= bottom + 0.5:
                        candidates.append(QPointF(x, y))

            # Interseções com y = top e y = bottom
            if abs(dy) > 1e-9:
                for y in (top, bottom):
                    t = (y - py) / dy
                    x = px + t * dx
                    if left - 0.5 <= x <= right + 0.5:
                        candidates.append(QPointF(x, y))

            # Remove pontos duplicados aproximados
            unique = []
            for p in candidates:
                exists = False
                for q in unique:
                    if abs(p.x() - q.x()) < 0.5 and abs(p.y() - q.y()) < 0.5:
                        exists = True
                        break
                if not exists:
                    unique.append(p)

            if len(unique) >= 2:
                line = QGraphicsLineItem(
                    unique[0].x(),
                    unique[0].y(),
                    unique[1].x(),
                    unique[1].y())
                line.setPen(pen)
                self.scene.addItem(line)

            offset += spacing

    def _draw_rotated_line_preview(self, style_name, color, angle, scale):
        """
        Desenha o preview das hachuras lineares com rotação real:

        - Linhas Cruzadas
        - Linhas Diagonais
        - Linhas Horizontais
        """
        rect = self._prepare_preview_scene()

        pen = QPen(color)
        pen.setWidthF(0.8)
        pen.setCosmetic(True)

        try:
            scale_value = float(scale or 1.0)
        except Exception:
            scale_value = 1.0

        spacing = max(4.0, 8.0 * scale_value)

        style_name = str(style_name or "")
        angle = float(angle or 0.0)

        # Retângulo interno para a hachura.
        # Evita que as linhas ultrapassem visualmente a moldura do preview.
        line_rect = rect.adjusted(2.0, 2.0, -2.0, -2.0)

        if style_name == self.tr("Linhas Horizontais"):
            self._draw_line_family(line_rect, angle, spacing, pen)

        elif style_name == self.tr("Linhas Diagonais"):
            self._draw_line_family(line_rect, 45.0 + angle, spacing, pen)

        elif style_name == self.tr("Linhas Cruzadas"):
            self._draw_line_family(line_rect, angle, spacing, pen)
            self._draw_line_family(line_rect, 90.0 + angle, spacing, pen)

        else:
            return False

        self._add_preview_border(rect)
        self.scene.update()
        return True

    def update_graphics_view_transform(self, *args):
        """
        Atualiza o preview da hachura.

        Em vez de rotacionar o QGraphicsView inteiro, redesenha o padrão.
        Isso permite que linhas cruzadas, diagonais e horizontais girem de verdade.
        """
        try:
            self.graphicsView.resetTransform()
        except Exception:
            pass  # nosec B110

        self.update_hatch_style()

    def centerDialog(self):
        """
        Centraliza o diálogo na tela atual do usuário.

        Funções e Ações Desenvolvidas:
        - Obtém a geometria atual da janela do diálogo.
        - Obtém a tela associada ao próprio widget; se não houver, usa a tela principal.
        - Calcula o centro da área disponível da tela.
        - Ajusta a posição da janela para que seu centro coincida com o centro da tela.

        :return: None
        """
        # Captura a geometria atual da janela do diálogo
        frameGeometry = self.frameGeometry()

        # Obtém a tela do próprio widget; se não existir ainda, usa a tela principal
        screen = self.screen() or QGuiApplication.primaryScreen()
        if not screen:
            return

        # Captura o centro da área disponível da tela
        centerPoint = screen.availableGeometry().center()

        # Ajusta a geometria da janela para alinhar ao centro da tela
        frameGeometry.moveCenter(centerPoint)

        # Move a janela para a nova posição calculada
        self.move(frameGeometry.topLeft())

    def Obter_Valores(self):
        """
        Coleta e retorna os valores configurados na interface do usuário para campos relacionados à camada,
        rótulos, escala de hachura, rotação e padrões de hachura. Este método é útil para operações que
        necessitam dessas configurações, como a exportação de dados ou a aplicação de estilos gráficos.

        Funções e Ações Desenvolvidas:
        - Obtenção do texto atual do comboBox para o campo da camada e do campo de rótulo.
        - Verificação se o checkbox para o campo de rótulo está marcado e, em caso afirmativo, obtenção do campo correspondente.
        - Coleta dos valores de escala e rotação das hachuras.
        - Obtenção do estilo de hachura selecionado e do padrão correspondente para exportação.

        :return: Tupla contendo o nome do campo da camada, campo de rótulo (ou None), padrão de hachura para DXF, escala e rotação de hachura.
        """
        # Obtém o texto do campo atualmente selecionado no comboBox da camada
        campo_camada = self.comboBoxCampoCamada.currentText()
        # Verifica se o checkbox para rótulos está marcado e obtém o campo correspondente, se aplicável
        campo_rotulo = self.comboBoxCampoRotulo.currentText() if self.checkBoxCampoRotulo.isChecked() else None
        # Coleta o valor de escala da hachura do spinBox
        escala_hachura = self.scaleSpinBox.value()
        # Coleta o valor de rotação da hachura da barra de rolagem
        rotacao_hachura = self.angleScrollBar.value()
        # Obtém o nome do estilo de hachura selecionado no listWidget
        estilo_hachura = self.listWidget.currentItem().text()
        # Acessa o padrão de hachura correspondente para exportação, definido no dicionário de estilos
        ezdxf_pattern = self.hatchStyles[estilo_hachura][2]

        transparencia_percentual = self._get_transparency_percent()

        return (campo_camada,
            campo_rotulo,
            ezdxf_pattern,
            escala_hachura,
            rotacao_hachura,
            transparencia_percentual)

class PolygonDelegate(QStyledItemDelegate):

    def paint(self, painter, option, index):
        """
        Sobrescreve o método de pintura para adicionar uma representação gráfica (retângulo) 
        que reflete a cor da camada do polígono e a cor da borda do símbolo antes da caixinha de visibilidade de cada item no treeView.
        """
        super().paint(painter, option, index)

        # Obtém o ID da camada do item do modelo
        layer_id = index.data(Qt.ItemDataRole.UserRole)
        if not layer_id:
            layer_id = index.model().itemFromIndex(index).data()

        layer = QgsProject.instance().mapLayer(layer_id)

        if layer:
            # Define a cor padrão para o retângulo e a borda
            rect_color = QColor("white")
            border_color = QColor("black")
            min_border_thickness = 1.1  # Espessura mínima da borda
            #
            symbols = layer.renderer().symbols(QgsRenderContext())

            cor_por_atributo = False

            # Camadas importadas do DXF possuem a cor real
            # armazenada nos campos r, g e b.
            if (layer.fields().indexFromName("r") >= 0
                and layer.fields().indexFromName("g") >= 0
                and layer.fields().indexFromName("b") >= 0):
                try:
                    feature = next(layer.getFeatures(), None)

                    if feature is not None:
                        r = int(feature["r"])
                        g = int(feature["g"])
                        b = int(feature["b"])

                        rect_color = QColor(r, g, b)

                        # Para as camadas DXF, a borda acompanha
                        # a mesma cor exibida no mapa.
                        border_color = QColor(r, g, b)

                        cor_por_atributo = True

                except (TypeError, ValueError):
                    cor_por_atributo = False


            # Para as demais camadas, mantém exatamente
            # o comportamento atual.
            if not cor_por_atributo:
                if symbols:
                    rect_color = symbols[0].color()

                    if symbols[0].symbolLayerCount() > 0:
                        border_layer = symbols[0].symbolLayer(0)

                        if hasattr(
                            border_layer, "strokeColor"):
                            border_color = (border_layer.strokeColor())

                        if hasattr(border_layer, "strokeWidth"):
                            border_thickness = max(border_layer.strokeWidth(), min_border_thickness)

                        else:
                            border_thickness = (min_border_thickness)

                    else:
                        border_thickness = (min_border_thickness)

                else:
                    border_thickness = (min_border_thickness)

            else:
                border_thickness = (min_border_thickness)

            # Desenho do retângulo com a cor da camada e borda
            polygonRect = QRect(option.rect.left() - 15, option.rect.top() + 12, 15, option.rect.height() - 25)
            painter.setBrush(QBrush(rect_color))
            painter.setPen(QPen(border_color, border_thickness))
            painter.drawRect(polygonRect)

            # Desloca o texto para a direita para dar espaço ao retângulo
            option.rect.setLeft(int(option.rect.left() + 20 + border_thickness))  # Converte border_thickness para int