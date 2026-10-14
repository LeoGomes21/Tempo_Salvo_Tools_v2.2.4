from qgis.core import (QgsProject, QgsRasterLayer, QgsMapLayer, QgsMapSettings, QgsMapRendererCustomPainterJob, QgsMessageLog, Qgis, QgsProcessing, QgsProcessingFeedback, QgsApplication, QgsVectorLayer, QgsTask, QgsProcessingUtils, QgsProcessingAlgRunnerTask, QgsProcessingContext, QgsField, QgsFields, QgsVectorFileWriter, QgsFeature, QgsDistanceArea, QgsCoordinateReferenceSystem, QgsWkbTypes, QgsLayerTreeGroup, QgsLayerTreeLayer, QgsEditFormConfig, QgsPointXY, QgsGeometry, QgsArrowSymbolLayer, QgsLineSymbol, QgsFillSymbol, QgsSingleSymbolRenderer, QgsProperty, QgsSymbolLayer, QgsPalLayerSettings, QgsTextFormat, QgsVectorLayerSimpleLabeling, QgsRasterBandStats, QgsRasterShader, QgsColorRampShader, QgsSingleBandPseudoColorRenderer, QgsRasterTransparency, QgsCategorizedSymbolRenderer, QgsRendererCategory, QgsRenderContext, QgsExpressionContextUtils, QgsStyle)
from qgis.PyQt.QtWidgets import (QDockWidget, QGraphicsScene, QGraphicsPixmapItem, QVBoxLayout, QPushButton, QLabel, QDoubleSpinBox, QFormLayout, QGroupBox, QProgressBar, QApplication, QMessageBox, QRadioButton, QButtonGroup, QWidget, QHBoxLayout, QMenu, QAction, QActionGroup, QTableView, QDialog, QDialogButtonBox, QAbstractItemView, QTableWidget, QTableWidgetItem, QHeaderView, QAbstractSpinBox, QLineEdit, QStyledItemDelegate, QFileDialog, QFrame)
from qgis.PyQt.QtGui import QImage, QPainter, QPixmap, QColor, QPen, QBrush, QFont,  QStandardItemModel, QStandardItem, QDoubleValidator, QDesktopServices, QCursor
from qgis.analysis import QgsRasterCalculator, QgsRasterCalculatorEntry, QgsZonalStatistics
from qgis.PyQt.QtCore import Qt, QSize, QVariant, QPointF, QLineF, QPoint, QModelIndex, QTimer, QLocale, QRectF, QRect, QEvent, QSettings, QObject, pyqtSignal, QMetaType, QCoreApplication, QUrl
from qgis.gui import QgsMapTool, QgsRubberBand
from collections import Counter, deque
from ezdxf.colors import rgb2int
from functools import partial
from qgis.utils import iface
from qgis import processing
from qgis.PyQt import uic
import pyqtgraph as pg
from osgeo import gdal
import numpy as np
import unicodedata
import subprocess
import traceback
import tempfile
import inspect
import sqlite3
import bisect
import shutil
import ezdxf
import math
import re
import os

FORM_CLASS, _ = uic.loadUiType(os.path.join(os.path.dirname(__file__), 'CriarRedesDrenagem.ui'))

class RedesDrenagem(QDockWidget, FORM_CLASS):
    def __init__(self, parent=None):
        """Constructor."""
        super(RedesDrenagem, self).__init__(parent)

        # Configura a interface do usuário a partir do Designer.
        self.setupUi(self)

        # Altera o título da janela
        self.setWindowTitle(self.tr("Redes de Drenagem"))

        # Armazena a referência da interface QGIS
        self.iface = iface

        # Conjunto de camadas raster com nameChanged conectado
        self._raster_layers_connected = set()

        # Controle de sincronização com o painel de Camadas
        self._layer_sync_connected = False
        self._syncing_layer_selection = False

        # Cria uma cena gráfica para o QGraphicsView
        self.scene = QGraphicsScene(self)
        self.graphicsViewRaster.setScene(self.scene)

        # Refit do preview quando o widget realmente aparecer (troca de abas / resize)
        try:
            self.graphicsViewTipo.viewport().installEventFilter(self)
        except Exception:
            pass  # nosec B110
        # tenta desenhar/ajustar depois que o layout estabilizar
        QTimer.singleShot(0, self._refresh_graphics_tipo_when_visible)

        # Flag usada pelo mostrar_mensagem
        self._lock_messagebar = False

        # Adiciona o dock widget à interface QGIS na parte inferior
        self.iface.addDockWidget(Qt.DockWidgetArea.BottomDockWidgetArea, self)

        # Inicializa o ComboBox de Raster
        self.init_combo_box_raster()

        # textEdit com resumo do raster (somente leitura)
        self.textEditMDT.setReadOnly(True)
        # opcional: deixa mais "tabelado"
        self.textEditMDT.setFontFamily("Consolas")
        self.textEditMDT.setFontPointSize(9)

        # Cria controles específicos de SAGA dentro do scrollAreaAtividades
        self._setup_saga_controls()

        # Cria controles específicos de TauDEM dentro do scrollAreaAtividades
        self._setup_taudem_controls()

        # Cria controles específicos de WhiteboxTools dentro do scrollAreaAtividades
        self._setup_whitebox_controls()

        # Conecta seleção de motor (SAGA / TauDEM / WhiteboxTools)
        self.radioButtonSAGA.toggled.connect(self._update_motor_ui)
        self.radioButtonTauDem.toggled.connect(self._update_motor_ui)
        self.radioButtonTools.toggled.connect(self._update_motor_ui)

        # Atualiza a interface inicial conforme o radio selecionado
        self._update_motor_ui()

        self._safe_dem_cache = {} #Salva o Raster Usado

        # Botão Executar começa desabilitado
        self.pushButtonExecutar.setEnabled(False)

        self._init_combo_canais() # Lista de Canais

        self._selected_lista_code = None
        self._init_lista_menu()
        self._init_pushButtonCamada()
        self._init_pushButtonCamadaDXF()
        self._init_pushButtonGraficoDXF()
        self._init_pushButtonSalvar()
        self._init_pushButtonAbrir()

        # Já existiam:
        self._CN_Trapezoidalcked_layers: set[str] = set() # camadas já conectadas ao sinal

        # Índice e sequência por camada
        self._cn_layer_order: dict[str, int] = {}  # layer_id -> número da camada (1,2,3,...)
        self._cn_layer_seq: dict[str, int] = {}    # layer_id -> último seq usado (1,2,...)
        self._camadas_model = None
        self._feicao_model = None
        self._current_canal_layer = None

        # gráfico global da aba PROJETO
        self._grafico_projeto_plot_widget = None
        self._grafico_projeto_canal_curve = None
        self._grafico_projeto_terreno_curve = None
        self._grafico_projeto_legend = None
        self._grafico_projeto_segments = []
        self._grafico_projeto_trecho_item = None
        self._grafico_projeto_trecho_text = None
        self._grafico_projeto_hover_selected_fid = None
        self._grafico_projeto_hover_selected_layer_id = None
        self._grafico_projeto_vline = None
        self._grafico_projeto_hline = None
        self._grafico_projeto_coord_text = None
        self._grafico_projeto_sync_point = None
        self._grafico_projeto_mouse_proxy = None

        self._grafico_projeto_fill_items = []

        self._lista_canais_model = None
        self._syncing_lista_canais_selection = False
        self._wbt_inund_task = None

        # controle do checkbox para CAD nativo do QGIS
        self._cad_enable_connected = False
        self._cad_visibility_connected = False

        self._init_checkBoxMapTool()

        # Inicializa o tableViewCamada a partir do grupo 'CANAIS'
        self._init_tableViewFeicao()
        self._init_tableViewCamada()
        self._init_tableViewListaCanais()
        self._init_scrollAreaResultado()
        self._init_scrollAreaGrafico()
        self._init_checkBoxAcima_Abaixo()
        self._init_pushButtonCalcular()
        self._init_pushButtonInverter()
        self._init_lineEditRugosidade()
        self._init_textBrowserInfo()
        self._init_scrollAreaProjetoGrafico()
        self._init_checkBoxHachura()
        self._init_checkBoxAltimetria()
        self._init_checkBoxTrecho()

        self._sim2_ensure_init()  # prepara simulação 2 (idempotente)

        # Conecta os sinais aos slots
        self.connect_signals()

    def tr(self, message):
        """
        Traduz textos deste diálogo.
        O contexto precisa ser estável para o Qt Linguist encontrar as traduções.
        """
        return QCoreApplication.translate("RedesDrenagem", message)

    def connect_signals(self):
        """Conecta os sinais do combo e do projeto QGIS."""
        # Quando mudar o raster selecionado, atualiza a visualização
        self.comboBoxRaster.currentIndexChanged.connect(self.display_raster)

        # gráfico global da aba PROJETO
        self.comboBoxRaster.currentIndexChanged.connect(self._update_grafico_projeto_from_current_layer)

        # botão executar
        self.pushButtonExecutar.clicked.connect(self.on_executar_clicked)

        # botão profundidade mínima (poças / alagamento local)
        self.comboBoxRaster.currentIndexChanged.connect(self._update_executar_button_state)
        self.comboBoxRaster.currentIndexChanged.connect(self._update_action_buttons_state)

        # Motores também atualizam o estado do botão
        self.radioButtonSAGA.toggled.connect(self._update_executar_button_state)
        self.radioButtonTauDem.toggled.connect(self._update_executar_button_state)
        self.radioButtonTools.toggled.connect(self._update_executar_button_state)
        self.radioButtonSAGA.toggled.connect(self._update_action_buttons_state)
        self.radioButtonTauDem.toggled.connect(self._update_action_buttons_state)
        self.radioButtonTools.toggled.connect(self._update_action_buttons_state)

        # Sinais do projeto para atualizar o combo quando camadas mudarem
        project = QgsProject.instance()
        project.layersAdded.connect(self.on_layers_added)
        project.layersRemoved.connect(self.on_layers_removed)
        project.cleared.connect(self.init_combo_box_raster)

        QgsProject.instance().layerWillBeRemoved.connect(self._on_layer_will_be_removed)

        # Simulação de inundação (tempo real)
        if hasattr(self, "pushButtonInundacaoTreal"):
            try:
                self.pushButtonInundacaoTreal.clicked.disconnect()
            except Exception:
                pass  # nosec B110
            self.pushButtonInundacaoTreal.clicked.connect(self.on_pushButtonInundacaoTreal_clicked)

        # opcional: se quiser que mudar o tempo ajuste a simulação em tempo real
        if hasattr(self, "doubleSpinBoxTempo"):
            try:
                self.doubleSpinBoxTempo.valueChanged.disconnect()
            except Exception:
                pass  # nosec B110
            self.doubleSpinBoxTempo.valueChanged.connect(self._inun_on_tempo_changed)

        # botão inundação (HAND / lâmina)
        if hasattr(self, "pushButtonInundacao"):
            try:
                self.pushButtonInundacao.clicked.disconnect()
            except Exception:
                pass  # nosec B110
            self.pushButtonInundacao.clicked.connect(self.on_pushButtonInundacao_clicked)

        # Atualiza habilitação quando parâmetros de simulação mudarem
        for attr in ("doubleSpinBoxMinimo", "doubleSpinBoxMaximo", "spinBoxPasso"):
            if hasattr(self, attr):
                w = getattr(self, attr)
                try:
                    w.valueChanged.connect(self._update_action_buttons_state)
                except Exception:
                    pass  # nosec B110

    def on_layers_added(self, layers):
        """Chamado quando camadas são adicionadas ao projeto."""
        self.update_combo_box()

        try:
            self._update_action_buttons_state()
        except Exception:
            pass  # nosec B110

    def on_layers_removed(self, layer_ids):
        """Chamado quando camadas são removidas do projeto."""
        self.update_combo_box()

        try:
            self._update_action_buttons_state()
        except Exception:
            pass  # nosec B110

    def showEvent(self, event):
        """
        Sobrescreve o evento de exibição do diálogo para resetar os Widgets
        e re-sincronizar o tableViewCamada com o grupo 'CANAIS' (caso camadas
        tenham sido removidas enquanto o dock estava fechado).
        """
        # (re)conecta sinais que podem ter sido desconectados no closeEvent
        project = QgsProject.instance()

        try:
            project.layerWillBeRemoved.disconnect(self._on_layer_will_be_removed)
        except TypeError:
            pass  # nosec B110
        try:
            project.layerWillBeRemoved.connect(self._on_layer_will_be_removed)
        except TypeError:
            pass  # nosec B110

        try:
            cad = self.iface.cadDockWidget()
            if cad is not None:
                act = cad.enableAction()

                if act is not None and not self._cad_enable_connected:
                    act.toggled.connect(self._on_cad_enable_action_toggled)
                    self._cad_enable_connected = True

                if not self._cad_visibility_connected:
                    cad.visibilityChanged.connect(self._on_cad_dock_visibility_changed)
                    self._cad_visibility_connected = True
        except Exception:
            pass  # nosec B110

        try:
            self._update_checkBoxMapTool_state()
        except Exception:
            pass  # nosec B110

        # Mantém seu fluxo atual de “reset”
        self.display_raster()
        self.init_combo_box_raster()
        self._update_action_buttons_state()
        self._update_executar_button_state()
        self._update_pushButtonCalcular_state()

        self._connect_layer_sync()  # Conecta o toolTip

        #  Recarrega a lista de camadas do grupo CANAIS (remove entradas antigas)
        prev_layer_id = None
        try:
            if hasattr(self, "tableViewCamada") and self.tableViewCamada is not None:
                idx = self.tableViewCamada.currentIndex()
                if idx.isValid():
                    prev_layer_id = idx.data(Qt.ItemDataRole.UserRole)
        except Exception:
            prev_layer_id = None

        try:
            if hasattr(self, "_reload_tableViewCamada_from_group"):
                self._reload_tableViewCamada_from_group()
            # tenta restaurar seleção anterior (se ainda existir)
            if prev_layer_id and hasattr(self, "_select_camada_row_by_layer_id"):
                self._select_camada_row_by_layer_id(prev_layer_id)
        except Exception:
            pass  # nosec B110

        super(RedesDrenagem, self).showEvent(event)

    def closeEvent(self, event):
        """
        Quando o diálogo/dock é fechado, removemos sincronizações relevantes.
        """
        try:
            # já existente (e aqui deve ser DISCONNECT, não connect)
            self._disconnect_layer_sync()
        except Exception:
            pass  # nosec B110

        project = QgsProject.instance()

        # layerWillBeRemoved
        try:
            project.layerWillBeRemoved.disconnect(self._on_layer_will_be_removed)
        except TypeError:
            pass  # nosec B110

        try:
            cad = self.iface.cadDockWidget()
            if cad is not None:
                act = cad.enableAction()

                if act is not None and self._cad_enable_connected:
                    act.toggled.disconnect(self._on_cad_enable_action_toggled)
                    self._cad_enable_connected = False

                if self._cad_visibility_connected:
                    cad.visibilityChanged.disconnect(self._on_cad_dock_visibility_changed)
                    self._cad_visibility_connected = False
        except Exception:
            pass  # nosec B110

        # Reseta o gráfico do Projeto
        try:
            self._reset_grafico_projeto()
        except Exception:
            pass  # nosec B110

        super().closeEvent(event)

    def init_combo_box_raster(self):
        """
        Inicializa o comboBox de raster, populando-o com as camadas raster do projeto
        e ajusta a seleção e visualização conforme necessário.
        """
        # Armazenar o ID atualmente selecionado
        current_raster_id = self.comboBoxRaster.currentData()

        layers = QgsProject.instance().mapLayers().values()
        raster_layers = []
        for layer in layers:
            if not isinstance(layer, QgsRasterLayer):
                continue

            # pula rasters que estão nos grupos de drenagem gerados pelo plugin
            if self._layer_in_excluded_group(layer.id()):
                continue

            raster_layers.append(layer)

        # Evita disparar currentIndexChanged enquanto repovoa
        self.comboBoxRaster.blockSignals(True)
        self.comboBoxRaster.clear()

        for raster_layer in raster_layers:
            self.comboBoxRaster.addItem(raster_layer.name(), raster_layer.id())

        # Restaura seleção anterior, se possível
        if current_raster_id:
            index = self.comboBoxRaster.findData(current_raster_id)
            if index != -1:
                self.comboBoxRaster.setCurrentIndex(index)
            elif self.comboBoxRaster.count() > 0:
                self.comboBoxRaster.setCurrentIndex(0)
        else:
            if self.comboBoxRaster.count() > 0:
                self.comboBoxRaster.setCurrentIndex(0)

        self.comboBoxRaster.blockSignals(False)

        # Atualiza conexões de nameChanged para as camadas raster atuais
        self._refresh_raster_name_connections(raster_layers)

        # Atualiza a visualização do raster selecionado (se houver)
        self.display_raster()

        # Garante que o estado do botão Executar reflita o novo combo
        self._update_executar_button_state()
        self._update_action_buttons_state()

    def _refresh_raster_name_connections(self, raster_layers):
        """
        (Re)conecta o sinal nameChanged das camadas raster atuais
        para que o comboBoxRaster seja atualizado imediatamente
        quando o nome da camada for alterado.
        """
        project = QgsProject.instance()

        # Garante que o atributo exista
        if not hasattr(self, "_raster_layers_connected"):
            self._raster_layers_connected = set()

        # Desconecta sinais antigos
        for layer_id in list(self._raster_layers_connected):
            layer = project.mapLayer(layer_id)
            if layer is not None:
                try:
                    layer.nameChanged.disconnect(self.on_raster_name_changed)
                except TypeError:
                    pass  # nosec B110
        self._raster_layers_connected.clear()

        # Conecta sinais para as camadas raster atuais
        for layer in raster_layers:
            try:
                layer.nameChanged.connect(self.on_raster_name_changed)
                self._raster_layers_connected.add(layer.id())
            except TypeError:
                # Se já estiver conectado, ignora
                pass  # nosec B110

    def on_raster_name_changed(self):
        """
        Atualiza o texto do comboBoxRaster quando o nome de uma camada raster muda.
        """
        layer = self.sender()
        if not isinstance(layer, QgsRasterLayer):
            return

        layer_id = layer.id()
        new_name = layer.name()

        # Atualiza o item correspondente no comboBoxRaster
        for i in range(self.comboBoxRaster.count()):
            if self.comboBoxRaster.itemData(i) == layer_id:
                self.comboBoxRaster.setItemText(i, new_name)
                break

    def update_combo_box(self):
        """
        Atualiza o comboBox de raster ao adicionar ou remover camadas no projeto,
        tentando manter a seleção anterior quando possível.
        """
        # Armazena a seleção atual para restaurar após a atualização
        current_index = self.comboBoxRaster.currentIndex()
        current_layer_id = self.comboBoxRaster.itemData(current_index)

        # Atualiza o combo box
        self.init_combo_box_raster()

        # Tenta restaurar a seleção anterior
        if current_layer_id:
            index = self.comboBoxRaster.findData(current_layer_id)
            if index != -1:
                self.comboBoxRaster.setCurrentIndex(index)
            else:
                if self.comboBoxRaster.count() > 0:
                    self.comboBoxRaster.setCurrentIndex(0)

    def _layer_in_excluded_group(self, layer_id: str) -> bool:
        """
        Retorna True se a camada (layer_id) estiver dentro de algum
        dos grupos de drenagem gerados pelo plugin:
        - 'SAGA - Drenagem'
        - 'TauDEM - Drenagem'
        - 'WhiteboxTools - Drenagem'
        """
        excluded_groups = {self.tr("SAGA - Drenagem"), self.tr("TauDEM - Drenagem"), self.tr("WhiteboxTools - Drenagem")}

        project = QgsProject.instance()
        root = project.layerTreeRoot()
        if root is None:
            return False

        node = root.findLayer(layer_id)
        if node is None:
            # camada ainda não está em nenhuma árvore (ou foi removida)
            return False

        parent = node.parent()
        from qgis.core import QgsLayerTreeGroup  # se já estiver importado no topo, pode remover esta linha

        while parent is not None:
            if isinstance(parent, QgsLayerTreeGroup):
                if parent.name() in excluded_groups:
                    return True
            parent = parent.parent()

        return False

    def display_raster(self):
        """
        Renderiza a camada raster selecionada no QGraphicsView, ajustando a visualização
        e atualiza o resumo no textEditMDT.
        """
        # Garante que a cena exista
        if not hasattr(self, "scene") or self.scene is None:
            self.scene = QGraphicsScene(self)
            self.graphicsViewRaster.setScene(self.scene)

        # Limpa a cena antes de adicionar um novo item
        self.scene.clear()

        # Obtém o ID da camada raster selecionada
        selected_raster_id = self.comboBoxRaster.currentData()
        if not selected_raster_id:
            # nada selecionado → limpa o textEdit também
            self.textEditMDT.clear()
            self.textEditMDT.setPlainText(self.tr("Nenhum raster selecionado."))
            return

        # Busca a camada raster pelo ID
        selected_layer = QgsProject.instance().mapLayer(selected_raster_id)

        # Atualiza o textEditMDT com as informações do raster
        if isinstance(selected_layer, QgsRasterLayer):
            self._update_mdt_info()
        else:
            self.textEditMDT.clear()
            self.textEditMDT.setPlainText(self.tr("Nenhum raster selecionado."))
            return

        if isinstance(selected_layer, QgsRasterLayer):
            # Configurações do mapa
            map_settings = QgsMapSettings()
            map_settings.setLayers([selected_layer])
            map_settings.setBackgroundColor(QColor(255, 255, 255))

            width = self.graphicsViewRaster.viewport().width()
            height = self.graphicsViewRaster.viewport().height()
            if width <= 0 or height <= 0:
                return

            map_settings.setOutputSize(QSize(width, height))
            map_settings.setExtent(selected_layer.extent())

            image = QImage(width, height, QImage.Format.Format_ARGB32)
            image.fill(Qt.GlobalColor.transparent)

            painter = QPainter(image)
            render_job = QgsMapRendererCustomPainterJob(map_settings, painter)

            render_job.start()
            render_job.waitForFinished()
            painter.end()

            pixmap = QPixmap.fromImage(image)
            pixmap_item = QGraphicsPixmapItem(pixmap)

            self.scene.addItem(pixmap_item)
            self.graphicsViewRaster.setSceneRect(pixmap_item.boundingRect())

    def _update_mdt_info(self):
        """
        Atualiza o textEditMDT com informações do raster
        atualmente selecionado no comboBoxRaster.
        """
        if not hasattr(self, "textEditMDT"):
            return

        layer_id = self.comboBoxRaster.currentData()
        layer = QgsProject.instance().mapLayer(layer_id)

        if not isinstance(layer, QgsRasterLayer):
            self.textEditMDT.setHtml(self.tr("<b>Nenhum MDT selecionado.</b>"))
            return

        pr = layer.dataProvider()
        extent = layer.extent()
        crs = layer.crs()

        cols = layer.width()
        rows = layer.height()

        # Resolução (tamanho de pixel)
        res_x = extent.width() / cols if cols else 0
        res_y = extent.height() / rows if rows else 0

        # Área total aproximada (em unidades² do CRS)
        area = extent.width() * extent.height()

        # Se o CRS for em metros, mostra também em hectares
        area_info = self.tr("{area:,.2f} (unidades² do CRS)").format(area=area)
        try:
            from qgis.core import QgsUnitTypes
            if crs.mapUnits() == QgsUnitTypes.DistanceUnit.DistanceMeters:
                area_ha = area / 10000.0
                area_info = f"{area:,.2f} m² ({area_ha:,.2f} ha)"
        except Exception:
            # Se der qualquer problema com QgsUnitTypes, fica só com unidades²
            pass  # nosec B110

        # Fonte (tira parâmetros muito grandes se quiser)
        source = pr.dataSourceUri()
        # Opcional: só o caminho até o " |" (caso seja um raster no disco)
        if " |" in source:
            source = source.split(" |", 1)[0]

        html = []

        html.append(self.tr("<b>Nome:</b> {layer_name}").format(layer_name=layer.name()))
        html.append(self.tr("<b>Fonte:</b> {source}").format(source=source))
        html.append(self.tr("<b>CRS:</b> {authid} - {description}").format(authid=crs.authid(), description=crs.description()))

        html.append(self.tr("<b>Extensão:</b>"))
        html.append(self.tr("  Xmin: {xmin:.3f}").format(xmin=extent.xMinimum()))
        html.append(self.tr("  Xmax: {xmax:.3f}").format(xmax=extent.xMaximum()))
        html.append(self.tr("  Ymin: {ymin:.3f}").format(ymin=extent.yMinimum()))
        html.append(self.tr("  Ymax: {ymax:.3f}").format(ymax=extent.yMaximum()))

        html.append(self.tr("<b>Dimensões (col x lin):</b> {cols} x {rows}").format(cols=cols, rows=rows))
        html.append(self.tr("<b>Resolução:</b> {res_x:.3f} x {res_y:.3f} (unidades do CRS)").format(res_x=res_x, res_y=res_y))
        html.append(self.tr("<b>Área (aprox.):</b> {area_info}").format(area_info=area_info))

        # Se quiser, pode manter mais campos aqui (tipo de pixel, NoData, etc.)

        self.textEditMDT.setReadOnly(True)
        self.textEditMDT.setHtml("<br>".join(html))

    def mostrar_mensagem(self, texto, tipo, duracao=3, caminho_pasta=None, caminho_arquivo=None, forcar=False):
        """
        Exibe uma mensagem na barra de mensagens do QGIS.
        Respeita self._lock_messagebar para não sobrepor barras de progresso.
        """
        if getattr(self, "_lock_messagebar", False) and not forcar:
            return

        bar = self.iface.messageBar()

        if tipo == "Erro":
            bar.pushMessage(self.tr("Erro"), texto, level=Qgis.MessageLevel.Critical, duration=duracao)

        elif tipo == "Aviso":
            bar.pushMessage(self.tr("Aviso"), texto, level=Qgis.MessageLevel.Warning, duration=duracao)

        elif tipo == "Sucesso":
            msg = bar.createMessage(self.tr("Sucesso"), texto)

            if caminho_pasta:
                botao_abrir_pasta = QPushButton(self.tr("Abrir Pasta"))
                botao_abrir_pasta.clicked.connect(
                    lambda _checked=False, caminho=caminho_pasta:
                        QDesktopServices.openUrl(
                            QUrl.fromLocalFile(
                                os.path.abspath(os.fspath(caminho)))))
                msg.layout().insertWidget(1, botao_abrir_pasta)

            if caminho_arquivo:
                botao_executar = QPushButton(self.tr("Executar"))
                botao_executar.clicked.connect(
                    lambda _checked=False, caminho=caminho_arquivo:
                        QDesktopServices.openUrl(
                            QUrl.fromLocalFile(
                                os.path.abspath(os.fspath(caminho)))))
                msg.layout().insertWidget(2, botao_executar)

            bar.pushWidget(msg, level=Qgis.MessageLevel.Info, duration=duracao)

        else:
            bar.pushMessage("Info", texto, level=Qgis.MessageLevel.Info, duration=duracao)

    def _setup_saga_controls(self):
        """
        Cria, dentro do scrollAreaAtividades, os controles de parâmetros
        específicos do SAGA (MINSLOPE e THRESHOLD).
        """
        container = self.scrollAreaAtividades.widget()
        if container is None:
            return

        layout = container.layout()
        if layout is None:
            layout = QVBoxLayout(container)
            container.setLayout(layout)

        # Grupo visual só pra organizar
        self.groupSagaParams = QGroupBox(self.tr("Parâmetros SAGA - Drenagem"), container)
        form = QFormLayout(self.groupSagaParams)

        # MINSLOPE
        label_minslope = QLabel(self.tr("Declividade mínima (MINSLOPE %):"), self.groupSagaParams)
        self.spinMINSLOPE = QDoubleSpinBox(self.groupSagaParams)
        self.spinMINSLOPE.setDecimals(3)
        self.spinMINSLOPE.setSingleStep(0.01)
        self.spinMINSLOPE.setRange(0.0, 10.0)   # 0% a 10%
        self.spinMINSLOPE.setValue(0.1)         # padrão: 0,1%

        form.addRow(label_minslope, self.spinMINSLOPE)

        # THRESHOLD
        label_threshold = QLabel(self.tr("Ordem mínima de canal (THRESHOLD):"), self.groupSagaParams)
        self.spinTHRESHOLD = QDoubleSpinBox(self.groupSagaParams)
        self.spinTHRESHOLD.setDecimals(0)       # queremos valores inteiros
        self.spinTHRESHOLD.setSingleStep(1.0)
        self.spinTHRESHOLD.setRange(1.0, 20.0)  # limite prático: 1 a 20
        self.spinTHRESHOLD.setValue(5.0)        # padrão típico

        form.addRow(label_threshold, self.spinTHRESHOLD)

        layout.addWidget(self.groupSagaParams)

    def _update_motor_ui(self):
        """
        Mostra/esconde os grupos de parâmetros conforme o motor selecionado.
        - SAGA: mostra groupSagaParams
        - TauDEM: mostra groupTauDemParams
        - WhiteboxTools: mostra groupWbtParams
        """
        is_saga = self.radioButtonSAGA.isChecked()
        is_taudem = self.radioButtonTauDem.isChecked()
        is_wbt = self.radioButtonTools.isChecked()

        if hasattr(self, "groupSagaParams"):
            self.groupSagaParams.setVisible(is_saga)

        if hasattr(self, "groupTauDemParams"):
            self.groupTauDemParams.setVisible(is_taudem)

        if hasattr(self, "groupWbtParams"):
            self.groupWbtParams.setVisible(is_wbt)

        # Atualiza também o estado do botão Executar
        self._update_executar_button_state()
        self._update_action_buttons_state()

    def on_executar_clicked(self):
        """
        Handler do botão Executar.
        """
        # garante que há um raster selecionado
        layer_id = self.comboBoxRaster.currentData()
        dem_layer = QgsProject.instance().mapLayer(layer_id)

        if not isinstance(dem_layer, QgsRasterLayer):
            self.mostrar_mensagem(self.tr("Selecione um raster válido no combo antes de executar."), "Erro")
            return

        # Descobre qual motor está selecionado
        if self.radioButtonSAGA.isChecked():
            self._executar_saga_drenagem(dem_layer)

        elif self.radioButtonTauDem.isChecked():
            self._executar_taudem_drenagem(dem_layer)

        elif self.radioButtonTools.isChecked():
            # WhiteboxTools
            self._executar_whitebox_drenagem(dem_layer)

        else:
            self.mostrar_mensagem(self.tr("Selecione um motor (SAGA, TauDEM ou WhiteboxTools) antes de executar."), "Erro")

    @staticmethod
    def _make_ascii_filename(original_path: str, prefix: str = "") -> str:
        """
        Gera um nome de arquivo “seguro” (ASCII) a partir de um caminho original.

        - Remove acentos e caracteres especiais (normalização NFKD + encode ASCII ignore)
        - Troca espaços por underscore
        - Substitui qualquer caractere fora de [A-Za-z0-9._-] por underscore
        - Opcionalmente adiciona um prefixo (ex.: 'dem_', 'tmp_')

        Retorna apenas o nome do arquivo (basename), não o diretório.
        """
        base = os.path.basename(original_path)  # pega só o nome do arquivo, sem pasta
        nfkd = unicodedata.normalize("NFKD", base)  # separa letras + diacríticos (ex.: 'ç' -> 'c' + '¸')
        ascii_name = nfkd.encode("ascii", "ignore").decode("ascii")  # remove diacríticos e qualquer não-ASCII
        ascii_name = ascii_name.replace(" ", "_")  # evita espaços em nomes de saída (compatibilidade)
        ascii_name = re.sub(r"[^A-Za-z0-9._-]", "_", ascii_name)  # sanitiza caracteres restantes
        if prefix:
            ascii_name = f"{prefix}_{ascii_name}"  # prefixo para agrupar/identificar arquivos gerados
        return ascii_name

    @staticmethod
    def _create_safe_workspace(prefix: str = "ts_drenagem_") -> str:
        """
        Cria um diretório temporário exclusivo para executar os processos (workspace).

        - Usa a pasta temporária do sistema (tempfile)
        - Gera um caminho único (evita conflito entre execuções simultâneas)
        - Retorna o caminho completo do diretório criado

        Observação: a limpeza (remoção) desse diretório deve ser feita pelo fluxo do plugin
        quando o processamento terminar, se você quiser evitar acúmulo em %TEMP%.
        """
        return tempfile.mkdtemp(prefix=prefix)  # cria pasta temporária única com o prefixo informado

    def _needs_safe_copy(self, path: str) -> bool:
        """
        Retorna True se o caminho tiver caracteres não ASCII ou espaços,
        ou seja, se for mais seguro copiar para um caminho 'limpo'.
        """
        # Espaços no caminho
        if " " in path:
            return True

        # Qualquer caractere não-ASCII (acentos, ç, etc.)
        if any(ord(ch) > 127 for ch in path):
            return True

        return False

    def _get_safe_dem_layer(self, dem_layer: QgsRasterLayer) -> QgsRasterLayer:
        """
        Retorna uma camada raster com caminho 'seguro' (sem acentos/espaços),
        reutilizando uma cópia já existente se possível.

        - Se não precisar de cópia, devolve o próprio dem_layer.
        - Se precisar, usa um cache para não copiar o mesmo arquivo toda hora.
        """
        original_dem_path = dem_layer.source()

        # Se não for um arquivo no disco, nem tenta copiar
        if not os.path.isfile(original_dem_path):
            return dem_layer

        # Se o caminho já é "ok", usa diretamente
        if not self._needs_safe_copy(original_dem_path):
            return dem_layer

        # Garante que o cache exista
        if not hasattr(self, "_safe_dem_cache"):
            self._safe_dem_cache = {}

        safe_path = self._safe_dem_cache.get(original_dem_path)

        # Se já temos um caminho seguro em cache e o arquivo ainda existe, tenta usar
        if safe_path and os.path.exists(safe_path):
            safe_layer = QgsRasterLayer(safe_path, dem_layer.name())

            if safe_layer.isValid():
                return safe_layer
            # se a camada não for válida, vamos recriar a cópia

        # Não tinha cache ou estava inválido → criar/atualizar cópia
        base_temp = tempfile.gettempdir()
        cache_dir = os.path.join(base_temp, "ts_drenagem_dem_cache")
        os.makedirs(cache_dir, exist_ok=True)

        safe_name = self._make_ascii_filename(original_dem_path, prefix="dem")
        safe_path = os.path.join(cache_dir, safe_name)

        try:
            shutil.copy2(original_dem_path, safe_path)
        except Exception as e:
            self.mostrar_mensagem(self.tr("Erro ao copiar DEM para caminho temporário seguro: {error}").format(error=str(e)), "Erro")
            # fallback: usa o próprio DEM original
            return dem_layer

        # Atualiza cache
        self._safe_dem_cache[original_dem_path] = safe_path
        safe_layer = QgsRasterLayer(safe_path, dem_layer.name())

        if not safe_layer.isValid():
            self.mostrar_mensagem(self.tr("Falha ao carregar DEM copiado para caminho seguro."), "Erro")
            return dem_layer  # fallback

        return safe_layer

    def _executar_saga_drenagem(self, dem_layer: QgsRasterLayer):
        """
        Dispara o processamento de drenagem com SAGA em segundo plano
        usando QgsProcessingAlgRunnerTask (sem travar a interface).
        """
        # 1) Lê parâmetros configurados na interface (SAGA)
        minslope = 0.1
        if hasattr(self, "spinMINSLOPE"):
            minslope = self.spinMINSLOPE.value()

        strahler_threshold = 5
        if hasattr(self, "spinTHRESHOLD"):
            strahler_threshold = int(self.spinTHRESHOLD.value())

        # 2) Verifica se o provider SAGA NextGen está disponível
        provider = QgsApplication.processingRegistry().providerById("sagang")
        if provider is None:
            self.mostrar_mensagem(self.tr("Provider 'SAGA Next Gen' (sagang) não está disponível no Processing.\nVerifique em Configurações ► Opções ► Processamento ► Provedores."), "Erro")
            return

        # 3) Obtém DEM em caminho "seguro" (pode ser o próprio ou cópia cacheada)
        safe_dem_layer = self._get_safe_dem_layer(dem_layer)
        if not safe_dem_layer or not safe_dem_layer.isValid():
            self.mostrar_mensagem(self.tr("Falha ao obter DEM em caminho seguro para processamento."), "Erro")
            return

        # 4) Cria e inicia o runner assíncrono
        #    Guardamos em self para o objeto não ser coletado pelo GC
        self._saga_runner = SagaDrenagemRunner(plugin=self, dem_layer=dem_layer, safe_dem_layer=safe_dem_layer, minslope=minslope, strahler_threshold=strahler_threshold)
        self._saga_runner.start()

    def _add_saga_raster(self, layer: QgsRasterLayer, short_code: str):
        """
        Adiciona um raster gerado pelo SAGA ao projeto,
        dentro do grupo 'SAGA - Drenagem', sem expandir o grupo.
        """
        log_prefix = "SAGA - Tempo Salvo Tools"

        if not isinstance(layer, QgsRasterLayer) or not layer.isValid():
            QgsMessageLog.logMessage(self.tr("[{short_code}] Raster SAGA inválido, não será adicionado.").format(short_code=short_code), log_prefix, level=Qgis.MessageLevel.Warning)
            return

        project = QgsProject.instance()

        # Não adiciona direto na raiz
        project.addMapLayer(layer, addToLegend=False)

        root = project.layerTreeRoot()
        group_name = self.tr("SAGA - Drenagem")
        group = root.findGroup(group_name)
        if group is None:
            group = root.addGroup(group_name)

        group.addLayer(layer)

        # Garante que nem o grupo nem a camada fiquem expandidos
        group.setExpanded(True)
        node = root.findLayer(layer.id())
        if node:
            node.setExpanded(False)

    def _setup_taudem_controls(self):
        """
        Cria, dentro do scrollAreaAtividades, os controles de parâmetros
        específicos do TauDEM (MINSLOPE e THRESHOLD, por enquanto).
        """
        container = self.scrollAreaAtividades.widget()
        if container is None:
            return

        layout = container.layout()
        if layout is None:
            layout = QVBoxLayout(container)
            container.setLayout(layout)

        # Grupo visual para organizar os parâmetros do TauDEM
        self.groupTauDemParams = QGroupBox(self.tr("Parâmetros TauDEM - Drenagem"), container)
        form = QFormLayout(self.groupTauDemParams)

        # THRESHOLD TauDEM
        label_threshold_tau = QLabel(self.tr("Ordem mínima de canal (THRESHOLD):"), self.groupTauDemParams)
        self.spinTauTHRESHOLD = QDoubleSpinBox(self.groupTauDemParams)
        self.spinTauTHRESHOLD.setDecimals(0)       # inteiros
        self.spinTauTHRESHOLD.setSingleStep(10.0)
        self.spinTauTHRESHOLD.setRange(1.0, 1000.0)  # limite prático
        self.spinTauTHRESHOLD.setValue(100.0)        # padrão típico

        form.addRow(label_threshold_tau, self.spinTauTHRESHOLD)

        layout.addWidget(self.groupTauDemParams)

        # Inicialmente escondido; quem controla é o _update_motor_ui
        self.groupTauDemParams.setVisible(False)

    def _executar_taudem_drenagem(self, dem_layer: QgsRasterLayer):
        """
        Dispara o processamento de drenagem com TauDEM em segundo plano
        usando QgsTask, sem registrar provider no Processing.
        """
        # 1) Garante que o TauDEM está configurado (GUI/main thread)
        if not TAUDEM_CONFIG.setup_taudem_config():
            return

        # 2) Obtém DEM em caminho "seguro"
        safe_dem_layer = self._get_safe_dem_layer(dem_layer)
        if not safe_dem_layer or not safe_dem_layer.isValid():
            self.mostrar_mensagem(self.tr("Falha ao obter DEM em caminho seguro para processamento TauDEM."), "Erro")
            return

        # 3) Workspace temporário
        workspace = self._create_safe_workspace(prefix="ts_taudem_")

        # 4) Lê o THRESHOLD da interface (área mínima para canal)
        tau_threshold = 5.0
        if hasattr(self, "spinTauTHRESHOLD"):
            tau_threshold = float(self.spinTauTHRESHOLD.value())

        # 5) Cria a task TauDEM (agora com threshold)
        task = TauDEMDrenagemTask( plugin=self, dem_layer=dem_layer, safe_dem_layer=safe_dem_layer, workspace=workspace, threshold=tau_threshold)

        task.taskCompleted.connect(lambda: self._on_taudem_task_finished(task, True))
        task.taskTerminated.connect(lambda: self._on_taudem_task_finished(task, False))

        QgsApplication.taskManager().addTask(task)

        self.mostrar_mensagem(self.tr("Processamento de drenagem com TauDEM iniciado em segundo plano..."), "Info")

    def _on_taudem_task_finished(self, task, success: bool):
        """
        Slot chamado pelos sinais taskCompleted (success=True)
        e taskTerminated (success=False).
        Cuida de adicionar ao projeto:
        - FEL, P, SD8, AD8 (rasters básicos)
        - SRC (raster binário de canais)
        - ORD (ordem de canais)
        - W (raster de bacias)
        - NET (vetor de rede de drenagem)
        """
        log_prefix = "TauDEM - Tempo Salvo Tools"

        QgsMessageLog.logMessage(self.tr("_on_taudem_task_finished chamado. success={success}").format(success=success), log_prefix, level=Qgis.MessageLevel.Info)

        # Falha / cancelamento
        if not success:
            err = getattr(task, "error_message", None)
            if err:
                self.mostrar_mensagem(err, "Erro", forcar=True)
            elif task.isCanceled():
                self.mostrar_mensagem(self.tr("Processamento TauDEM cancelado pelo usuário."), "Erro", forcar=True)
            else:
                self.mostrar_mensagem(self.tr("Ocorreu uma falha no processamento TauDEM."), "Erro", forcar=True)
            return

        # CRS original do DEM
        dem_crs = task.dem_layer.crs()

        # Rede de drenagem vetorial (NET)
        self._add_taudem_vector(path=task.net_path, name=self.tr("{dem_name} - Rede de drenagem (TauDEM)").format(dem_name=task.dem_name), dem_crs=dem_crs, short_code="NET")

        # Rasters básicos
        self._add_taudem_raster(path=task.fel_path, name=self.tr("{dem_name} - FEL (TauDEM)").format(dem_name=task.dem_name), dem_crs=dem_crs, short_code="FEL")

        self._add_taudem_raster(path=task.p_path, name=self.tr("{dem_name} - D8 FlowDir (P)").format(dem_name=task.dem_name), dem_crs=dem_crs, short_code="P")

        self._add_taudem_raster(path=task.sd8_path, name=self.tr("{dem_name} - Slope D8 (SD8)").format(dem_name=task.dem_name), dem_crs=dem_crs, short_code="SD8")

        self._add_taudem_raster(path=task.ad8_path, name=self.tr("{dem_name} - Área de contribuição D8 (AD8)").format(dem_name=task.dem_name), dem_crs=dem_crs, short_code="AD8")

        # Threshold: raster de canais (SRC)
        self._add_taudem_raster(path=task.src_path, name=self.tr("{dem_name} - Canais (SRC TauDEM)").format(dem_name=task.dem_name), dem_crs=dem_crs, short_code="SRC")

        # Ordem de canais (ORD) - opcional
        self._add_taudem_raster(path=task.ord_path, name=self.tr("{dem_name} - Ordem de canais (ORD TauDEM)").format(dem_name=task.dem_name), dem_crs=dem_crs, short_code="ORD")

        # Bacias (W raster)
        self._add_taudem_raster(path=task.w_path, name=self.tr("{dem_name} - Bacias (W TauDEM)").format(dem_name=task.dem_name), dem_crs=dem_crs, short_code="W")

        # Mensagem final (apenas UMA vez)
        self.mostrar_mensagem(self.tr("Processamento de drenagem com TauDEM concluído (em segundo plano)."), "Sucesso", forcar=True)

    def _add_taudem_vector(self, path: str, name: str, dem_crs, short_code: str):
        """
        Adiciona um vetor TauDEM ao projeto, sem expandir grupos no painel de camadas.
        """
        log_prefix = "TauDEM - Tempo Salvo Tools"

        if not path or not os.path.exists(path):
            QgsMessageLog.logMessage(self.tr("[{short_code}] Arquivo vetorial não encontrado: {path}").format(short_code=short_code, path=path), log_prefix, level=Qgis.MessageLevel.Warning)
            return

        layer = QgsVectorLayer(path, name, "ogr")
        if dem_crs and dem_crs.isValid():
            layer.setCrs(dem_crs)

        if not layer.isValid():
            self.mostrar_mensagem(self.tr("Falha ao carregar vetor {short_code} do TauDEM.").format(short_code=short_code), "Erro", forcar=True)
            return

        project = QgsProject.instance()

        # Não adicionar direto na raiz
        project.addMapLayer(layer, addToLegend=False)

        root = project.layerTreeRoot()
        group_name = self.tr("TauDEM - Drenagem")
        group = root.findGroup(group_name)
        if group is None:
            group = root.addGroup(group_name)

        group.addLayer(layer)

        group.setExpanded(True)
        node = root.findLayer(layer.id())
        if node:
            node.setExpanded(False)

        # Se for rede (NET), aplica estilo por ORDEM (verde-azulado)
        if short_code == "NET":
            try:
                self._style_taudem_channels_by_order(layer)
            except Exception as exc:
                QgsMessageLog.logMessage(self.tr("[{short_code}] Erro ao aplicar estilo por ordem: {error}").format(short_code=short_code, error=str(exc)), log_prefix, level=Qgis.MessageLevel.Warning)

    def _style_taudem_channels_by_order(self, layer: QgsVectorLayer):
        """
        Aplica estilo de canais TauDEM (NET) baseado em um campo de ordem:
          - Cada ordem vira uma categoria
          - Quanto maior a ordem, mais grossa a linha
          - Verde-azulado claro -> verde-azulado escuro
        """
        if not isinstance(layer, QgsVectorLayer) or not layer.isValid():
            return

        # TauDEM/StreamNet costuma trazer um campo de ordem com nomes variados.
        candidates = ["strmOrder", "StrmOrder", "STRMORDER", "ORDER", "Order", "order", "ORD", "Ord", "ord"]

        field_name = None
        for fn in candidates:
            if layer.fields().indexOf(fn) >= 0:
                field_name = fn
                break

        # fallback: qualquer campo que contenha "order" ou seja "ord"
        if field_name is None:
            for f in layer.fields():
                n = (f.name() or "").lower()
                if n == "ord" or "order" in n:
                    field_name = f.name()
                    break

        if field_name is None:
            # Sem campo de ordem, não estiliza
            return

        idx = layer.fields().indexOf(field_name)
        if idx < 0:
            return

        # Coleta valores únicos (inteiros)
        orders: set[int] = set()
        for feat in layer.getFeatures():
            val = feat.attribute(idx)
            if val is None:
                continue
            try:
                orders.add(int(val))
            except (TypeError, ValueError):
                continue

        if not orders:
            return

        sorted_orders = sorted(orders)
        n = len(sorted_orders)

        # Verde-azulado (turquesa claro -> teal escuro)
        base_color = QColor(214, 244, 255)  # claro
        top_color  = QColor(0, 94, 135)     # escuro

        # Espessura em mm (ajustável)
        min_w = 0.10
        max_w = 0.90

        def interp_color(c1: QColor, c2: QColor, t: float) -> QColor:
            t = max(0.0, min(1.0, t))
            r = int(c1.red()   + (c2.red()   - c1.red())   * t)
            g = int(c1.green() + (c2.green() - c1.green()) * t)
            b = int(c1.blue()  + (c2.blue()  - c1.blue())  * t)
            return QColor(r, g, b)

        # Se o campo for string, a categoria precisa receber string
        is_string_field = (layer.fields()[idx].type() == QMetaType.Type.QString)

        cats: list[QgsRendererCategory] = []
        for i, order_val in enumerate(sorted_orders):
            t = 0.0 if n == 1 else float(i) / float(n - 1)

            color = interp_color(base_color, top_color, t)
            width = min_w + (max_w - min_w) * t

            symbol = QgsLineSymbol.createSimple({})
            symbol.setWidth(width)
            symbol.setColor(color)

            label = self.tr("Ordem {order_val}").format(order_val=order_val)
            cat_value = str(order_val) if is_string_field else order_val
            cats.append(QgsRendererCategory(cat_value, symbol, label))

        renderer = QgsCategorizedSymbolRenderer(field_name, cats)
        layer.setRenderer(renderer)
        layer.triggerRepaint()

    def _setup_whitebox_controls(self):
        """
        Cria, dentro do scrollAreaAtividades, os controles de parâmetros
        específicos do WhiteboxTools (por enquanto só THRESHOLD).
        """
        container = self.scrollAreaAtividades.widget()
        if container is None:
            return

        layout = container.layout()
        if layout is None:
            layout = QVBoxLayout(container)
            container.setLayout(layout)

        # Grupo visual para organizar os parâmetros do WhiteboxTools
        self.groupWbtParams = QGroupBox(self.tr("Parâmetros WhiteboxTools - Drenagem"), container)
        form = QFormLayout(self.groupWbtParams)

        # THRESHOLD WhiteboxTools
        label_threshold_wbt = QLabel(self.tr("(THRESHOLD, em nº de células):"), self.groupWbtParams)
        self.spinWbtTHRESHOLD = QDoubleSpinBox(self.groupWbtParams)
        self.spinWbtTHRESHOLD.setDecimals(0)       # inteiros
        self.spinWbtTHRESHOLD.setSingleStep(100.0)
        self.spinWbtTHRESHOLD.setRange(10.0, 1000000.0)
        self.spinWbtTHRESHOLD.setValue(1000.0)     # valor padrão inicial

        # Modo de bacias (Whitebox)
        form.addRow(QLabel(self.tr("Modo de bacias:"), self.groupWbtParams))

        self.radioWbtBasins = QRadioButton(self.tr("Bacias simples (Basins)"), self.groupWbtParams)
        self.radioWbtSubbasins = QRadioButton(self.tr("Sub-bacias ligadas à rede (Subbasins)"), self.groupWbtParams)

        # Por padrão, usar Subbasins (mais parecido com SAGA)
        self.radioWbtSubbasins.setChecked(True)

        # Coloca um embaixo do outro
        form.addRow(self.radioWbtBasins)
        form.addRow(self.radioWbtSubbasins)

        form.addRow(label_threshold_wbt, self.spinWbtTHRESHOLD)

        layout.addWidget(self.groupWbtParams)

        # Inicialmente escondido; quem controla é o _update_motor_ui
        self.groupWbtParams.setVisible(False)

    def _executar_whitebox_drenagem(self, dem_layer: QgsRasterLayer):
        """
        Dispara o processamento de drenagem com WhiteboxTools em segundo plano
        usando QgsProcessingAlgRunnerTask (sem travar a interface).
        """
        # Verifica se há um provider WhiteboxTools disponível
        provider = self._get_wbt_provider()
        if provider is None:
            self.mostrar_mensagem(
                self.tr("O provider Whitebox não está disponível no Processing.\n"
                    "Verifique se o plugin Whitebox Workflows está instalado, habilitado e com o backend carregado."), "Erro")
            return

        try:
            provider.refreshAlgorithms()
        except Exception:
            pass  # nosec B110

        try:
            algoritmos_whitebox = list(provider.algorithms())
        except Exception:
            algoritmos_whitebox = []

        if not algoritmos_whitebox:
            self.mostrar_mensagem(
                self.tr(
                    "O provider Whitebox foi localizado, mas nenhum algoritmo "
                    "está disponível. Verifique o backend do Whitebox Workflows "
                    "e atualize o catálogo do plugin."),
                "Erro")
            return

        # DEM em caminho seguro (sem acentos/espaços)
        safe_dem_layer = self._get_safe_dem_layer(dem_layer)
        if not safe_dem_layer or not safe_dem_layer.isValid():
            self.mostrar_mensagem(self.tr("Falha ao obter DEM em caminho seguro para processamento WhiteboxTools."), "Erro")
            return

        # THRESHOLD (número de células) da interface
        wbt_threshold = 1000.0
        if hasattr(self, "spinWbtTHRESHOLD"):
            wbt_threshold = float(self.spinWbtTHRESHOLD.value())

        # Cria e inicia o runner assíncrono
        self._whitebox_runner = WhiteboxDrenagemRunner(plugin=self, dem_layer=dem_layer, safe_dem_layer=safe_dem_layer, threshold=wbt_threshold)
        self._whitebox_runner.start()

    def _get_wbt_provider(self):
        """
        Localiza e recupera o provider Whitebox Workflows.

        Estratégia:
        1. Procura no Processing Registry.
        2. Procura diretamente no plugin Whitebox carregado.
        3. Se encontrar o provider no plugin, mas ele não estiver registrado,
           registra novamente no Processing.
        4. Atualiza o catálogo de algoritmos.
        """
        reg = QgsApplication.processingRegistry()
        log_prefix = "WhiteboxTools - Tempo Salvo Tools"

        # 1. IDs conhecidos no Processing
        ids_conhecidos = (
            "whitebox_workflows",
            "whitebox",
            "wbt",
            "wbw",
            "whiteboxtools")

        for provider_id in ids_conhecidos:
            provider = reg.providerById(provider_id)

            if provider is not None:
                try:
                    provider.refreshAlgorithms()
                except Exception:
                    pass  # nosec B110

                QgsMessageLog.logMessage(
                    self.tr(
                        "Provider Whitebox encontrado no Processing: "
                        "{provider_id} -> {provider_name}").format(
                        provider_id=provider.id(),
                        provider_name=provider.name()),
                    log_prefix,
                    level=Qgis.MessageLevel.Info)

                return provider

        # 2. Procura qualquer provider Whitebox já registrado
        for provider in reg.providers():
            try:
                provider_name = str(provider.name() or "")
            except Exception as e:
                QgsMessageLog.logMessage(self.tr("Falha ao consultar um provider do Processing: {error}").format(error=str(e)), "Tempo Salvo Tools", level=Qgis.MessageLevel.Warning)
                continue

            texto = f"{provider_id} {provider_name}".lower()

            if "whitebox" not in texto:
                continue

            try:
                provider.refreshAlgorithms()
            except Exception:
                pass  # nosec B110

            return provider

        # 3. Provider não está no Registry:
        #    tenta recuperar diretamente do plugin Whitebox carregado
        try:
            from qgis import utils as qgis_utils

            plugin_whitebox = qgis_utils.plugins.get(
                "whitebox_workflows_qgis")

            # Caso o nome interno mude novamente, procura dinamicamente
            if plugin_whitebox is None:
                for plugin_id, plugin_obj in qgis_utils.plugins.items():
                    texto = str(plugin_id or "").lower()

                    if "whitebox" in texto:
                        plugin_whitebox = plugin_obj
                        break

            if plugin_whitebox is not None:
                provider = getattr(plugin_whitebox, "provider", None)

                if provider is not None:
                    try:
                        provider_id = provider.id()
                    except Exception:
                        provider_id = "whitebox_workflows"

                    QgsMessageLog.logMessage(
                        self.tr(
                            "Provider Whitebox encontrado dentro do plugin "
                            "carregado: {provider_id}").format(provider_id=provider_id),
                        log_prefix,
                        level=Qgis.MessageLevel.Info)

                    # 4. Registra o MESMO provider do plugin no Processing
                    registrado = reg.providerById(provider_id)

                    if registrado is None:
                        try:
                            reg.addProvider(provider)
                        except Exception as e:
                            QgsMessageLog.logMessage(
                                self.tr(
                                    "Falha ao registrar novamente o provider "
                                    "Whitebox: {error}").format(error=str(e)), log_prefix,
                                level=Qgis.MessageLevel.Warning)

                    # Busca novamente pelo Registry
                    registrado = reg.providerById(provider_id)

                    if registrado is not None:
                        try:
                            registrado.refreshAlgorithms()
                        except Exception:
                            pass  # nosec B110

                        return registrado

                    # Mesmo que o Registry não devolva, ainda temos
                    # o objeto real pertencente ao plugin
                    try:
                        provider.refreshAlgorithms()
                    except Exception:
                        pass  # nosec B110

                    return provider

        except Exception as e:
            QgsMessageLog.logMessage(self.tr("Erro ao acessar diretamente o plugin Whitebox: {error}").format(error=str(e)), log_prefix, level=Qgis.MessageLevel.Warning)

        # 5. Diagnóstico final
        try:
            providers = [
                f"{p.id()} -> {p.name()}"
                for p in reg.providers()]

            plugins_carregados = []

            from qgis import utils as qgis_utils

            plugins_carregados = list(qgis_utils.plugins.keys())

            QgsMessageLog.logMessage(
                self.tr(
                    "Whitebox não localizado.\n"
                    "Providers registrados:\n{providers}\n\n"
                    "Plugins carregados:\n{plugins}"
                ).format(
                    providers="\n".join(providers),
                    plugins="\n".join(plugins_carregados)),
                log_prefix,
                level=Qgis.MessageLevel.Warning)

        except Exception:
            pass  # nosec B110

        return None

    def _add_whitebox_vector(self, path: str, name: str, dem_crs, short_code: str):
        """
        Adiciona um vetor gerado pelo WhiteboxTools ao projeto,
        colocando-o dentro do grupo 'WhiteboxTools - Drenagem'
        sem expandir o grupo no painel de camadas.
        """
        log_prefix = "WhiteboxTools - Tempo Salvo Tools"

        if not path or not os.path.exists(path):
            QgsMessageLog.logMessage(self.tr("[{short_code}] Arquivo vetorial não encontrado: {path}").format(short_code=short_code, path=path), log_prefix, level=Qgis.MessageLevel.Warning)
            return

        layer = QgsVectorLayer(path, name, "ogr")
        if dem_crs and dem_crs.isValid():
            layer.setCrs(dem_crs)

        if not layer.isValid():
            self.mostrar_mensagem(self.tr("Falha ao carregar vetor {short_code} gerado pelo WhiteboxTools.").format(short_code=short_code), "Erro", forcar=True)
            return

        project = QgsProject.instance()

        # Não adiciona direto na raiz (evita expandir tudo)
        project.addMapLayer(layer, addToLegend=False)

        root = project.layerTreeRoot()
        group_name = self.tr("WhiteboxTools - Drenagem")
        group = root.findGroup(group_name)
        if group is None:
            group = root.addGroup(group_name)

        group.addLayer(layer)

        # Garante que nem o grupo nem a camada fiquem expandidos
        group.setExpanded(True)
        node = root.findLayer(layer.id())
        if node:
            node.setExpanded(False)

        # Whitebox -> preencher ORDER e estilizar
        if short_code == "NET":
            runner = getattr(self, "_whitebox_runner", None)
            order_path = getattr(runner, "order_path", None) if runner else None

            if order_path and os.path.exists(order_path):
                self._whitebox_fill_vector_order_from_raster(layer, order_path, field_name="ORDER")

            self._style_whitebox_channels_by_order(layer)

    def _whitebox_fill_vector_order_from_raster(self, layer: QgsVectorLayer, order_raster_path: str, field_name: str = "ORDER"):
        if not isinstance(layer, QgsVectorLayer) or not layer.isValid():
            return
        if not order_raster_path or not os.path.exists(order_raster_path):
            return

        rlayer = QgsRasterLayer(order_raster_path, "tmp_order_whitebox", "gdal")
        if not rlayer.isValid():
            return

        rprov = rlayer.dataProvider()

        idx = layer.fields().indexOf(field_name)
        if idx < 0:
            if not layer.isEditable():
                layer.startEditing()
            layer.dataProvider().addAttributes([QgsField(field_name, QMetaType.Type.Int)])
            layer.updateFields()
            idx = layer.fields().indexOf(field_name)

        if idx < 0:
            if layer.isEditable():
                layer.rollBack()
            return

        changes = {}

        for f in layer.getFeatures():
            g = f.geometry()
            if not g or g.isEmpty():
                continue

            try:
                pt = g.interpolate(g.length() * 0.5).asPoint()
            except Exception:  # nosec B112
                continue

            try:
                val, ok = rprov.sample(QgsPointXY(pt), 1)
            except Exception:  # nosec B112
                continue

            if not ok or val is None:
                continue

            try:
                ov = int(round(float(val)))
            except Exception:  # nosec B112
                continue

            if ov <= 0:
                continue

            changes[f.id()] = {idx: ov}

        if not layer.isEditable():
            layer.startEditing()

        if changes:
            layer.dataProvider().changeAttributeValues(changes)

        layer.commitChanges()

    def _style_whitebox_channels_by_order(self, layer: QgsVectorLayer):
        if not isinstance(layer, QgsVectorLayer) or not layer.isValid():
            return

        field_name = "ORDER"
        idx = layer.fields().indexOf(field_name)
        if idx < 0:
            return

        orders = set()
        for feat in layer.getFeatures():
            v = feat.attribute(idx)
            if v is None:
                continue
            try:
                orders.add(int(v))
            except Exception:
                pass  # nosec B110

        if not orders:
            return

        sorted_orders = sorted(orders)
        n = len(sorted_orders)

        # azul-esverdeado (claro -> escuro)
        base_color = QColor(214, 244, 255)
        top_color  = QColor(0, 94, 135)

        min_w = 0.10
        max_w = 0.80

        def interp(c1, c2, t):
            t = max(0.0, min(1.0, t))
            return QColor(
                int(c1.red()   + (c2.red()   - c1.red())   * t),
                int(c1.green() + (c2.green() - c1.green()) * t),
                int(c1.blue()  + (c2.blue()  - c1.blue())  * t))

        cats = []
        for i, ov in enumerate(sorted_orders):
            t = 0.0 if n == 1 else i / (n - 1)
            sym = QgsLineSymbol.createSimple({})
            sym.setColor(interp(base_color, top_color, t))
            sym.setWidth(min_w + (max_w - min_w) * t)
            cats.append(QgsRendererCategory(ov, sym, self.tr("Ordem {ov}").format(ov=ov)))

        layer.setRenderer(QgsCategorizedSymbolRenderer(field_name, cats))
        layer.setOpacity(0.9)
        layer.triggerRepaint()

    def _find_saga_filled_layer(self, dem_layer: QgsRasterLayer) -> QgsRasterLayer | None:
        """
        Tenta localizar o DEM preenchido gerado pelo fluxo SAGA
        para o MDT de entrada.

        Por padrão o SagaDrenagemRunner nomeia como:
        "<nome do MDT> - DEM preenchido"
        """
        if not isinstance(dem_layer, QgsRasterLayer):
            return None

        target_name = self.tr("{dem_name} - DEM preenchido").format(dem_name=dem_layer.name())

        for lyr in QgsProject.instance().mapLayers().values():
            if isinstance(lyr, QgsRasterLayer) and lyr.name() == target_name:
                return lyr

        return None

    def _escolher_motor_profundidade(self, dem_layer):
        """
        Decide qual motor (SAGA ou TauDEM) usar para profundidade de depressões
        para o DEM atual. Retorna uma tupla: (motor, layer_preenchido)
        motor ∈ {"taudem", "saga"} ou None.
        """
        if not isinstance(dem_layer, QgsRasterLayer):
            return None, None

        dem_name = dem_layer.name()
        project = QgsProject.instance()
        root = project.layerTreeRoot()

        # Procurar produto TauDEM (FEL) deste DEM
        grupo_taudem = root.findGroup(self.tr("TauDEM - Drenagem"))
        fel_layer = None
        if grupo_taudem:
            fel_prefix = self.tr("{dem_name} - FEL").format(dem_name=dem_name)

            for child in grupo_taudem.findLayers():
                lyr = child.layer()

                if isinstance(lyr, QgsRasterLayer) and lyr.name().startswith(fel_prefix):
                    fel_layer = lyr
                    break

        # Procurar produto SAGA (DEM preenchido) deste DEM
        grupo_saga = root.findGroup(self.tr("SAGA - Drenagem"))
        dem_preenchido_layer = None
        if grupo_saga:
            for child in grupo_saga.findLayers():
                lyr = child.layer()
                if isinstance(lyr, QgsRasterLayer) and lyr.name().startswith(self.tr("{dem_name} - DEM preenchido").format(dem_name=dem_name)):
                    dem_preenchido_layer = lyr
                    break

        # 1) Respeita o radioButton, se possível
        if self.radioButtonTauDem.isChecked() and fel_layer:
            return "taudem", fel_layer

        if self.radioButtonSAGA.isChecked() and dem_preenchido_layer:
            return "saga", dem_preenchido_layer

        # 2) Fallback se o motor escolhido não tem produto
        # Se marcou TauDEM mas só tem SAGA
        if self.radioButtonTauDem.isChecked() and not fel_layer and dem_preenchido_layer:
            self.mostrar_mensagem(self.tr("Produtos TauDEM não encontrados para este MDT. Usando DEM preenchido do SAGA para calcular depressões."), "Info")
            return "saga", dem_preenchido_layer

        # Se marcou SAGA mas só tem TauDEM
        if self.radioButtonSAGA.isChecked() and not dem_preenchido_layer and fel_layer:
            self.mostrar_mensagem(self.tr("Produtos SAGA não encontrados para este MDT. Usando FEL do TauDEM para calcular depressões."), "Info")
            return "taudem", fel_layer

        # 3) Se nenhum radio resolve (ex: Whitebox selecionado) ou nenhum marcado,
        # adota uma prioridade fixa quando ambos existem
        if fel_layer and dem_preenchido_layer:
            # exemplo: priorizar TauDEM
            return "taudem", fel_layer

        # Só tem um dos dois
        if fel_layer:
            return "taudem", fel_layer
        if dem_preenchido_layer:
            return "saga", dem_preenchido_layer

        # Nada encontrado
        return None, None

    def _calcular_profundidade_saga(self, dem_layer, filled_layer, h_min, *, gerar_vetor: bool = True):
        """Executa profundidade (SAGA) em segundo plano (sem travar o QGIS)."""
        if getattr(self, "_depth_runner", None) is not None:
            self.mostrar_mensagem(self.tr("Já existe um cálculo de profundidade em andamento."), "Info")
            return

        if not isinstance(dem_layer, QgsRasterLayer) or not dem_layer.isValid():
            self.mostrar_mensagem(self.tr("MDT inválido para calcular profundidade (SAGA)."), "Erro")
            return

        if not isinstance(filled_layer, QgsRasterLayer) or not filled_layer.isValid():
            self.mostrar_mensagem(self.tr("DEM preenchido (SAGA) inválido para calcular profundidade."), "Erro")
            return

        self._depth_runner = DepthPocasRunner(self, motor="saga", dem_layer=dem_layer, base_layer=filled_layer, h_min=float(h_min), gerar_vetor=gerar_vetor)
        self._depth_runner.start()

    def _calcular_profundidade_taudem(self, dem_layer: QgsRasterLayer, fel_layer: QgsRasterLayer, h_min: float, *, gerar_vetor: bool = True):
        """Executa profundidade (TauDEM) em segundo plano (sem travar o QGIS)."""
        if getattr(self, "_depth_runner", None) is not None:
            self.mostrar_mensagem(self.tr("Já existe um cálculo de profundidade em andamento."), "Info")
            return

        if not isinstance(dem_layer, QgsRasterLayer) or not dem_layer.isValid():
            self.mostrar_mensagem(self.tr("MDT inválido para calcular profundidade (TauDEM)."), "Erro")
            return

        if not isinstance(fel_layer, QgsRasterLayer) or not fel_layer.isValid():
            self.mostrar_mensagem(self.tr("FEL (TauDEM) inválido para calcular profundidade."), "Erro")
            return

        self._depth_runner = DepthPocasRunner(self, motor="taudem", dem_layer=dem_layer, base_layer=fel_layer, h_min=float(h_min), gerar_vetor=gerar_vetor)

        self._depth_runner.start()

    def _find_taudem_fel_layer(self, dem_layer: QgsRasterLayer) -> QgsRasterLayer | None:
        """
        Tenta localizar o FEL (PitRemove) gerado pelo TauDEM
        para o MDT de entrada.

        Nome esperado:
        "<nome do MDT> - FEL (TauDEM)"
        """
        if not isinstance(dem_layer, QgsRasterLayer):
            return None

        dem_name = dem_layer.name()
        project = QgsProject.instance()
        root = project.layerTreeRoot()

        grupo_taudem = root.findGroup(self.tr("TauDEM - Drenagem"))
        if not grupo_taudem:
            return None

        for node in grupo_taudem.findLayers():
            lyr = node.layer()
            if (isinstance(lyr, QgsRasterLayer)
                and lyr.name().startswith(self.tr("{dem_name} - FEL").format(dem_name=dem_name))):
                return lyr

        return None

    def _vetorizar_pocas(self, depth_layer: QgsRasterLayer, dem_layer: QgsRasterLayer, group_name: str):
        """
        A partir de um raster de profundidade (DEPTH),
        gera uma camada vetorial de poças com área e volume.

        Volume ≈ área * profundidade_média (por poça).

        Se já existir uma camada "<MDT> - Poças (vetor)" no grupo alvo,
        ela é removida antes de adicionar a nova (evita duplicatas).
        """
        log_prefix = "Profundidade - Tempo Salvo Tools"

        if not isinstance(depth_layer, QgsRasterLayer) or not depth_layer.isValid():
            self.mostrar_mensagem(self.tr("Camada de profundidade inválida para vetorizar poças."), "Erro")
            return

        depth_path = depth_layer.source()
        if not os.path.isfile(depth_path):
            self.mostrar_mensagem(self.tr("Raster de profundidade não está em um arquivo físico (não é possível vetorizar)."), "Erro")
            return

        # Workspace e caminhos temporários
        workspace = self._create_safe_workspace(prefix="ts_pocas_")
        ascii_name = self._make_ascii_filename(depth_path, prefix="pocas")
        if ascii_name.lower().endswith(".tif"):
            base = ascii_name[:-4]
        else:
            base = ascii_name

        mask_path = os.path.join(workspace, f"{base}_mask.tif")
        poly_tmp_path = os.path.join(workspace, f"{base}_poly_tmp.gpkg")
        out_vec_path = os.path.join(workspace, f"{base}_pocas.gpkg")

        # 1) Criar raster máscara (depth > 0) com QgsRasterCalculator
        entries: list[QgsRasterCalculatorEntry] = []

        e_depth = QgsRasterCalculatorEntry()
        e_depth.ref = "depth@1"
        e_depth.raster = depth_layer
        e_depth.bandNumber = 1
        entries.append(e_depth)

        expr = "depth@1 > 0"

        calc = QgsRasterCalculator(expr,  mask_path, "GTiff", depth_layer.extent(), depth_layer.width(), depth_layer.height(), entries)
        res = calc.processCalculation()
        if res != 0:
            self.mostrar_mensagem(self.tr("Erro ao criar raster máscara das poças (depth > 0)."), "Erro")
            return

        # 2) Polygonize da máscara (gdal:polygonize)
        params_poly = {
            "INPUT": mask_path,
            "BAND": 1,
            "FIELD": "ID",
            "EIGHT_CONNECTEDNESS": False,
            "OUTPUT": poly_tmp_path}

        try:
            result = processing.run("gdal:polygonize", params_poly, context=QgsProcessingContext(), feedback=QgsProcessingFeedback())
        except Exception as e:
            QgsMessageLog.logMessage(self.tr("Erro em gdal:polygonize: {error}").format(error=str(e)), log_prefix, level=Qgis.MessageLevel.Critical)
            self.mostrar_mensagem(self.tr("Erro ao vetorizar poças (gdal:polygonize)."), "Erro")
            return

        poly_path = result.get("OUTPUT", poly_tmp_path)

        poly_tmp_layer = QgsVectorLayer(poly_path, "poças_tmp", "ogr")
        if not poly_tmp_layer.isValid():
            self.mostrar_mensagem(self.tr("Falha ao carregar camada vetorial temporária de poças."), "Erro")
            return

        # 3) Criar camada de saída (memória) apenas com poças (ID > 0)
        crs = dem_layer.crs() if dem_layer and dem_layer.isValid() else depth_layer.crs()

        dem_name = dem_layer.name() if dem_layer else ""
        depth_name = depth_layer.name() if depth_layer else ""

        # Tenta aproveitar o “final” do nome da camada de profundidade
        # Ex.: depth_name = "MDT - Profundidade mínima ≥ 0.05 m"
        #      => nome_vec = "MDT - Poças - Profundidade mínima ≥ 0.05 m"
        if dem_name and depth_name.startswith(dem_name):
            suffix = depth_name[len(dem_name):]  # inclui " - Profundidade mínima..."
            nome_vec = self.tr("{dem_name} - Poças{suffix}").format(dem_name=dem_name, suffix=suffix)
        elif dem_name:
            nome_vec = self.tr("{dem_name} - Poças").format(dem_name=dem_name)
        else:
            nome_vec = self.tr("Poças")

        pocas_layer = QgsVectorLayer(f"Polygon?crs={crs.authid()}", nome_vec, "memory")
        prov = pocas_layer.dataProvider()

        prov.addAttributes([
            QgsField("id", QMetaType.Type.Int),
            QgsField("area_m2", QMetaType.Type.Double),
            QgsField("vol_m3", QMetaType.Type.Double)])
        pocas_layer.updateFields()

        id_field_name = "ID"
        if poly_tmp_layer.fields().indexFromName("ID") < 0:
            # fallback padrão do gdal:polygonize
            id_field_name = "DN"

        features_out = []
        idx = 1

        for f in poly_tmp_layer.getFeatures():
            try:
                val = float(f[id_field_name])
            except Exception:
                val = 0.0

            if val <= 0.0:
                # ignora o polígono de fundo (valor 0)
                continue

            geom = f.geometry()
            if geom is None or geom.isEmpty():
                continue

            new_f = QgsFeature(pocas_layer.fields())
            new_f.setGeometry(geom)
            area = geom.area()  # assume CRS métrico
            new_f["id"] = idx
            new_f["area_m2"] = area
            new_f["vol_m3"] = 0.0  # será preenchido após ZonalStatistics
            features_out.append(new_f)
            idx += 1

        if not features_out:
            self.mostrar_mensagem(self.tr("Nenhuma poça encontrada para vetorizar (todas profundidades = 0)."), "Info")
            return

        prov.addFeatures(features_out)
        pocas_layer.updateExtents()

        # 4) ZonalStatistics para profundidade média por poça
        depth_rlayer = QgsRasterLayer(depth_path, "depth_tmp")
        if not depth_rlayer.isValid():
            self.mostrar_mensagem(self.tr("Raster de profundidade inválido: {depth_path}").format(depth_path=depth_path), "Erro")
            return

        zs = QgsZonalStatistics(pocas_layer, depth_rlayer, "DEP_", 1, QgsZonalStatistics.Statistic.Mean)
        zs.calculateStatistics(None)

        # Descobre o campo DEP_* criado
        fields = pocas_layer.fields()
        idx_dep = -1
        for i, fld in enumerate(fields):
            if fld.name().upper().startswith("DEP_"):
                idx_dep = i
                break

        if idx_dep == -1:
            self.mostrar_mensagem(self.tr("Campo de profundidade média (DEP_*) não encontrado após ZonalStatistics."), "Erro")
            return

        idx_area = fields.indexFromName("area_m2")
        idx_vol = fields.indexFromName("vol_m3")

        pocas_layer.startEditing()
        for f in pocas_layer.getFeatures():
            mean_depth = f[idx_dep]
            try:
                mean_depth = float(mean_depth)
            except (TypeError, ValueError):
                mean_depth = 0.0

            area = f["area_m2"]
            try:
                area = float(area)
            except (TypeError, ValueError):
                area = 0.0

            vol = area * mean_depth
            pocas_layer.changeAttributeValue(f.id(), idx_vol, vol)
        pocas_layer.commitChanges()

        # 5) Salvar em disco (GPKG) e adicionar ao projeto
        #    removendo camadas antigas com o mesmo nome dentro do grupo.
        res = QgsVectorFileWriter.writeAsVectorFormat(pocas_layer, out_vec_path, "utf-8", crs, "GPKG")

        # Compatível com retorno int ou (int, msg)
        if isinstance(res, tuple):
            err, _ = res
        else:
            err = res

        if err != QgsVectorFileWriter.WriterError.NoError:
            self.mostrar_mensagem(self.tr("Erro ao salvar camada vetorial de poças (código {error_code}).").format(error_code=err), "Erro")
            return

        final_layer = QgsVectorLayer(out_vec_path, nome_vec, "ogr")
        if not final_layer.isValid():
            self.mostrar_mensagem(self.tr("Camada vetorial de poças salva, mas falhou ao ser carregada no QGIS."), "Erro")
            return

        project = QgsProject.instance()
        root = project.layerTreeRoot()
        group = root.findGroup(group_name)
        if group is None:
            group = root.addGroup(group_name)

        # Remove camadas antigas "nome_vec" dentro do grupo
        for node in group.findLayers():
            lyr = node.layer()
            if lyr and lyr.name() == nome_vec:
                group.removeChildNode(node)
                project.removeMapLayer(lyr.id())

        # Agora adiciona apenas a nova
        project.addMapLayer(final_layer, addToLegend=False)
        group.addLayer(final_layer)
        group.setExpanded(True)

        node = root.findLayer(final_layer.id())
        if node:
            node.setExpanded(False)

        self.mostrar_mensagem(self.tr("Camada vetorial de poças gerada com sucesso (área e volume)."), "Sucesso")

    def _add_taudem_raster(self, path: str, name: str, dem_crs, short_code: str, visible=True):
        """
        Adiciona um raster TauDEM ao projeto, sem expandir grupos no painel de camadas.
        Retorna a camada adicionada (ou None em caso de erro).
        """
        log_prefix = "TauDEM - Tempo Salvo Tools"

        if not path or not os.path.exists(path):
            QgsMessageLog.logMessage(self.tr("[{short_code}] Arquivo raster não encontrado: {path}").format(short_code=short_code, path=path), log_prefix, level=Qgis.MessageLevel.Warning)
            return None

        layer = QgsRasterLayer(path, name, "gdal")
        if dem_crs and dem_crs.isValid():
            layer.setCrs(dem_crs)

        if not layer.isValid():
            self.mostrar_mensagem(self.tr("Falha ao carregar raster {short_code} do TauDEM.").format(short_code=short_code), "Erro", forcar=True)
            return None

        project = QgsProject.instance()

        # Não adiciona direto na raiz (evita comportamento padrão de expandir)
        project.addMapLayer(layer, addToLegend=False)

        # Coloca dentro de um grupo fixo (por exemplo “TauDEM - Drenagem”)
        root = project.layerTreeRoot()
        group_name = self.tr("TauDEM - Drenagem")
        group = root.findGroup(group_name)
        if group is None:
            group = root.addGroup(group_name)

        group.addLayer(layer)

        # Garante que nem o grupo nem a camada fiquem expandidos
        group.setExpanded(True)
        node = root.findLayer(layer.id())
        if node:
            node.setExpanded(False)

        self._set_layer_visibility(layer, visible)

        return layer

    def _get_wbt_algorithm(self, tool_name: str, human_name: str):
        """
        Resolve o algoritmo WhiteboxTools a partir do nome lógico da ferramenta.
        Ex.: tool_name = 'DepthInSink'
        """
        log_prefix = "WhiteboxTools - Tempo Salvo Tools"

        reg = QgsApplication.processingRegistry()
        provider = self._get_wbt_provider()
        if provider is None:
            self.mostrar_mensagem(self.tr("Provider 'WhiteboxTools' (wbt) não está disponível no Processing.\nVerifique se o plugin 'WhiteboxTools for Processing' está instalado e habilitado."), "Erro")
            return None

        prov_id = provider.id()  # normalmente 'wbt'

        # 1) Tentativa direta: 'wbt:DepthInSink'
        alg_id_direct = f"{prov_id}:{tool_name}"
        alg = reg.algorithmById(alg_id_direct)
        if alg is not None:
            QgsMessageLog.logMessage(self.tr("Algoritmo resolvido diretamente: '{alg_id_direct}'").format(alg_id_direct=alg_id_direct), log_prefix, level=Qgis.MessageLevel.Info)
            return alg

        # 2) Fallback: compara ignorando maiúsculas/minúsculas e underscores
        norm_tool = re.sub(r"[^a-z0-9]+", "", tool_name.lower())
        exact_match = None
        partial_match = None

        for a in provider.algorithms():
            aid = a.id()  # ex.: 'wbt:DepthInSink'
            base = aid.split(":")[1] if ":" in aid else aid
            norm_base = re.sub(r"[^a-z0-9]+", "", base.lower())

            if norm_base == norm_tool:
                exact_match = a
                break

            if partial_match is None and (norm_tool in norm_base or norm_base in norm_tool):
                partial_match = a

        if exact_match is not None:
            QgsMessageLog.logMessage(self.tr("Resolvendo '{tool_name}' para algoritmo '{algorithm_id}' (WhiteboxTools).").format(tool_name=tool_name, algorithm_id=exact_match.id()), log_prefix, level=Qgis.MessageLevel.Info)
            return exact_match

        if partial_match is not None:
            QgsMessageLog.logMessage(self.tr("Resolvendo '{tool_name}' (match parcial) para algoritmo '{algorithm_id}' (WhiteboxTools).").format(tool_name=tool_name, algorithm_id=partial_match.id()), log_prefix, level=Qgis.MessageLevel.Info)
            return partial_match

        # 3) Não achou nada → logar alguns IDs disponíveis
        try:
            all_ids = [a.id() for a in provider.algorithms()]
            sample_ids = ", ".join(sorted(all_ids)[:20])
        except Exception:
            sample_ids = self.tr("Não foi possível obter a lista de algoritmos.")

        QgsMessageLog.logMessage(self.tr("Algoritmo '{tool_name}' não encontrado no provider '{prov_id}'. Alguns ids disponíveis: {sample_ids}").format(tool_name=tool_name, prov_id=prov_id, sample_ids=sample_ids), log_prefix, level=Qgis.MessageLevel.Warning)

        self.mostrar_mensagem(self.tr("Algoritmo WhiteboxTools '{human_name}' não encontrado (id esperado parecido com '{expected_id}').").format(human_name=human_name, expected_id=f"{prov_id}:{tool_name}"), "Erro")
        return None

    def _build_wbt_in_out_params(self, alg, input_path: str, output_path: str, tool_desc: str):
        """
        Para ferramentas simples do WhiteboxTools (1 raster de entrada, 1 de saída),
        tenta adivinhar o primeiro parâmetro de entrada e o primeiro destino.
        """
        log_prefix = "WhiteboxTools - Tempo Salvo Tools"

        in_name = None
        out_name = None

        for p in alg.parameterDefinitions():
            # Destino → saída
            if p.isDestination():
                if out_name is None:
                    out_name = p.name()
                continue

            # Primeiro parâmetro "normal" → entrada principal
            if in_name is None:
                in_name = p.name()

        QgsMessageLog.logMessage(self.tr("{tool_desc}: param entrada='{in_name}', saída='{out_name}'").format(tool_desc=tool_desc, in_name=in_name, out_name=out_name), log_prefix, level=Qgis.MessageLevel.Info)

        if not in_name or not out_name:
            QgsMessageLog.logMessage(self.tr("{tool_desc}: não conseguiu identificar parâmetros de entrada/saída.").format(tool_desc=tool_desc), log_prefix, level=Qgis.MessageLevel.Critical)
            self.mostrar_mensagem(self.tr("Não foi possível identificar parâmetros de entrada/saída para '{tool_desc}' no WhiteboxTools (veja o Registro de Mensagens).").format(tool_desc=tool_desc), "Erro")
            return None

        return {in_name: input_path, out_name: output_path}

    def _calcular_profundidade_whitebox(self, dem_layer, h_min, *, gerar_vetor: bool = True):
        """
        Calcula a profundidade de depressões usando WhiteboxTools (DepthInSink).

        Passos:
        - Executa DepthInSink em cima do DEM (caminho seguro).
        - Aplica limiar mínimo h_min (m) via QgsRasterCalculator.
        - Adiciona o raster final ao grupo 'WhiteboxTools - Drenagem'.
        - Gera camada vetorial de poças.
        """
        if not isinstance(dem_layer, QgsRasterLayer) or not dem_layer.isValid():
            self.mostrar_mensagem(self.tr("Selecione um MDT válido para calcular a profundidade (Whitebox)."), "Erro")
            return

        # Provider / algoritmo
        provider = self._get_wbt_provider()
        if provider is None:
            # _get_wbt_provider já mostra mensagem
            return

        alg = self._get_wbt_algorithm("DepthInSink", "Depth in sink")
        if alg is None:
            return

        # DEM em caminho seguro (sem acentos/espaços)
        safe_dem_layer = self._get_safe_dem_layer(dem_layer)
        if not safe_dem_layer or not safe_dem_layer.isValid():
            self.mostrar_mensagem(self.tr("Falha ao obter DEM em caminho seguro para DepthInSink (Whitebox)."), "Erro")
            return

        dem_path = safe_dem_layer.source()

        # Workspace e nomes de saída
        workspace = self._create_safe_workspace(prefix="ts_wbt_depth_")
        base_ascii = self._make_ascii_filename(dem_path, prefix="DepthInSink")

        if not base_ascii.lower().endswith(".tif"):
            base_ascii += ".tif"

        depth_raw_path = os.path.join(workspace, base_ascii)

        # Monta parâmetros simples (entrada DEM, saída raster)
        params = self._build_wbt_in_out_params(alg, input_path=dem_path, output_path=depth_raw_path, tool_desc="DepthInSink")
        if params is None:
            return

        # Executa DepthInSink de forma síncrona
        context = QgsProcessingContext()
        context.setProject(QgsProject.instance())
        feedback = QgsProcessingFeedback()

        try:
            processing.run(alg.id(), params, context=context, feedback=feedback)
        except Exception as e:
            QgsMessageLog.logMessage(self.tr("Erro ao executar DepthInSink (WhiteboxTools): {error}").format(error=str(e)), "WhiteboxTools - Tempo Salvo Tools", level=Qgis.MessageLevel.Critical)
            self.mostrar_mensagem(self.tr("Erro ao executar DepthInSink (WhiteboxTools)."), "Erro")
            return

        # Carrega o raster bruto do DepthInSink (sem limiar)
        depth_raw_layer = QgsRasterLayer(depth_raw_path, f"{dem_layer.name()} - DepthInSink (raw)", "gdal")
        if not depth_raw_layer.isValid():
            self.mostrar_mensagem(self.tr("Raster DepthInSink gerado, mas falhou ao ser carregado."), "Erro")
            return

        # Agora aplica o limiar mínimo h_min (como nos outros motores)
        entries: list[QgsRasterCalculatorEntry] = []

        e_depth = QgsRasterCalculatorEntry()
        e_depth.ref = "depth@1"
        e_depth.raster = depth_raw_layer
        e_depth.bandNumber = 1
        entries.append(e_depth)

        base_expr = "depth@1"

        if h_min <= 0.0:
            # Mantém apenas valores > 0
            expr = f"({base_expr}) * (({base_expr}) > 0)"
        else:
            # Mantém apenas profundidades >= h_min
            expr = f"({base_expr}) * (({base_expr}) >= {h_min})"

        out_name = self._make_ascii_filename(depth_raw_path, prefix="depth_wbt")
        if not out_name.lower().endswith(".tif"):
            out_name += ".tif"
        out_path = os.path.join(workspace, out_name)

        calc = QgsRasterCalculator(expr, out_path, "GTiff", depth_raw_layer.extent(), depth_raw_layer.width(), depth_raw_layer.height(), entries)

        res = calc.processCalculation()
        if res != 0:
            self.mostrar_mensagem(self.tr("Erro ao aplicar limiar mínimo à profundidade (WhiteboxTools)."), "Erro")
            return

        # Nome amigável da camada final
        titulo = self.tr("{dem_name} - Profundidade mínima (Whitebox)").format(dem_name=dem_layer.name())
        if h_min > 0.0:
            titulo += f" ≥ {h_min:.2f} m"

        depth_layer = QgsRasterLayer(out_path, titulo, "gdal")
        if not depth_layer.isValid():
            self.mostrar_mensagem(self.tr("Raster de profundidade mínima (Whitebox) gerado, mas falhou ao ser carregado no QGIS."), "Erro")
            return

        # Estilo graduado azul para o raster de poças
        self._apply_depth_raster_style(depth_layer)

        # Adiciona no grupo 'WhiteboxTools - Drenagem', evitando duplicatas de nome
        project = QgsProject.instance()
        root = project.layerTreeRoot()
        group_name = self.tr("WhiteboxTools - Drenagem")
        group = root.findGroup(group_name)
        if group is None:
            group = root.addGroup(group_name)

        # Remove camadas anteriores com o mesmo nome dentro do grupo
        for node in list(group.findLayers()):
            lyr = node.layer()
            if isinstance(lyr, QgsRasterLayer) and lyr.name() == depth_layer.name():
                group.removeChildNode(node)
                project.removeMapLayer(lyr.id())

        # Agora adiciona somente a nova
        project.addMapLayer(depth_layer, addToLegend=False)
        group.addLayer(depth_layer)

        # Mantém o grupo aberto e as camadas colapsadas (como combinamos)
        group.setExpanded(True)
        node = root.findLayer(depth_layer.id())
        if node:
            node.setExpanded(False)

        self.mostrar_mensagem(self.tr("Raster de profundidade mínima (WhiteboxTools / DepthInSink) gerado com sucesso."), "Sucesso")

        # Gera camada vetorial de poças (área e volume)
        if gerar_vetor:
            self._vetorizar_pocas(depth_layer=depth_layer, dem_layer=dem_layer, group_name=group_name)
        else:
            self.mostrar_mensagem(self.tr("Vetorização desativada (simulação). Mantendo apenas o raster de profundidade."), "Info")

    def _update_executar_button_state(self):
        """
        Habilita o pushButtonExecutar apenas quando:
        - existe um raster válido selecionado no comboBoxRaster; e
        - um dos motores (SAGA, TauDEM ou WhiteboxTools) está selecionado.
        """
        has_raster = (
            self.comboBoxRaster.count() > 0 and
            self.comboBoxRaster.currentData() is not None)

        motor_selected = (
            self.radioButtonSAGA.isChecked() or
            self.radioButtonTauDem.isChecked() or
            self.radioButtonTools.isChecked())

        self.pushButtonExecutar.setEnabled(has_raster and motor_selected)

    def _start_depth_raster(self):
        """Calcula o raster de profundidade (base - DEM) e aplica limiar (h_min/epsilon) para limpar ruído."""
        # Entradas do RasterCalculator
        entries: list[QgsRasterCalculatorEntry] = []

        e_dem = QgsRasterCalculatorEntry()
        e_dem.ref = "dem@1"
        e_dem.raster = self.dem_layer
        e_dem.bandNumber = 1
        entries.append(e_dem)

        # SAGA usa "filled"; demais motores usam "fel"
        if self.motor == "saga":
            base_ref = "filled@1"
        else:
            base_ref = "fel@1"

        e_base = QgsRasterCalculatorEntry()
        e_base.ref = base_ref
        e_base.raster = self.base_layer
        e_base.bandNumber = 1
        entries.append(e_base)

        base_expr = f"{base_ref} - dem@1"

        # Ajuste: SAGA pode gerar "microprofundidades" positivas (ruído).
        # Se o usuário não definiu h_min, aplicamos epsilon para preservar contraste.
        thr = float(self.h_min or 0.0)
        if self.motor == "saga" and thr <= 0.0:
            thr = 0.01  # 1 cm (ajuste aqui se quiser mais/menos agressivo)

        if thr <= 0.0:
            expr = f"({base_expr}) * (({base_expr}) > 0)"
        else:
            expr = f"({base_expr}) * (({base_expr}) >= {thr})"

        title = self.tr("Profundidade ({motor}) - Raster").format(motor=self.motor.upper())

        grid_layer = (
            self.base_layer
            if isinstance(self.base_layer, QgsRasterLayer) and self.base_layer.isValid()
            else self.dem_layer)

        self.task_depth = _RasterCalcTask(
            title,
            expr=expr,
            out_path=self.depth_path,
            extent=grid_layer.extent(),
            width=grid_layer.width(),
            height=grid_layer.height(),
            entries=[e_dem, e_base])

        self.task_depth.taskCompleted.connect(self._on_depth_finished)
        self.task_depth.taskTerminated.connect(self._on_depth_terminated)

        QgsApplication.taskManager().addTask(self.task_depth)

    def _apply_depth_raster_style(self, depth_layer: QgsRasterLayer):
        """
        Aplica um estilo graduado (azul claro -> azul escuro) para rasters
        de profundidade de poças (banda 1 em metros).

        - Valores > 0: gradiente azul
        - Valor 0: totalmente transparente
        - Topo da rampa: usa P95 dos valores > 0 (melhor contraste, menos influência de outliers)
        """
        if not isinstance(depth_layer, QgsRasterLayer) or not depth_layer.isValid():
            return

        prov = depth_layer.dataProvider()
        if prov is None:
            return

        try:
            stats = prov.bandStatistics(1, QgsRasterBandStats.Stats.All, depth_layer.extent(), 0)
        except Exception:
            return

        min_val = stats.minimumValue
        max_val = stats.maximumValue
        if min_val is None or max_val is None:
            return

        if min_val < 0:
            min_val = 0.0

        # Se tudo for 0, não há poça pra exibir
        if max_val <= 0.0:
            return

        # Ajuste: usar P95 (valores > 0) para topo da rampa
        max_used = max_val
        try:
            sw = min(256, max(1, depth_layer.width()))
            sh = min(256, max(1, depth_layer.height()))
            blk = prov.block(1, depth_layer.extent(), sw, sh)

            vals = []
            for y in range(sh):
                for x in range(sw):
                    try:
                        if hasattr(blk, "isNoData") and blk.isNoData(x, y):
                            continue
                    except Exception:
                        pass  # nosec B110

                    try:
                        v = float(blk.value(x, y))
                    except Exception:  # nosec B112
                        continue

                    if v > 0.0 and math.isfinite(v):
                        vals.append(v)

            if vals:
                vals.sort()
                p95 = vals[int(0.95 * (len(vals) - 1))]
                if p95 > 0.0:
                    max_used = min(max_val, p95)  # garante não ultrapassar o máximo real
        except Exception:
            pass  # nosec B110

        # Gradiente apenas para > 0
        v0 = 0.0
        v1 = max_used * 0.25
        v2 = max_used * 0.60
        v3 = max_used

        shader = QgsRasterShader()
        ramp_shader = QgsColorRampShader()
        ramp_shader.setColorRampType(QgsColorRampShader.Type.Interpolated)

        items = [
            QgsColorRampShader.ColorRampItem(v0, QColor(230, 245, 255, 0),   f"{v0:.2f}"),
            QgsColorRampShader.ColorRampItem(v1, QColor(198, 219, 239, 80),  f"{v1:.2f}"),
            QgsColorRampShader.ColorRampItem(v2, QColor(107, 174, 214, 130), f"{v2:.2f}"),
            QgsColorRampShader.ColorRampItem(v3, QColor(8, 81, 156, 170),    f"{v3:.2f}")]
        ramp_shader.setColorRampItemList(items)
        shader.setRasterShaderFunction(ramp_shader)

        renderer = QgsSingleBandPseudoColorRenderer(prov, 1, shader)

        # Transparência: 0 totalmente transparente
        transparency = QgsRasterTransparency()
        tr = QgsRasterTransparency.TransparentSingleValuePixel()
        tr.min = 0.0
        tr.max = 0.0
        tr.percentTransparent = 100

        tr_list = transparency.transparentSingleValuePixelList()
        tr_list.append(tr)
        transparency.setTransparentSingleValuePixelList(tr_list)

        renderer.setRasterTransparency(transparency)

        depth_layer.setRenderer(renderer)
        depth_layer.setOpacity(0.8)

    def on_pushButtonPronfundidade_clicked(self, checked=False, *, gerar_vetor: bool = True, h_min_override: float | None = None):
        """
        Handler do botão de profundidade de depressões.

        - Lê o MDT atual do comboBoxRaster
        - Lê a profundidade mínima do doubleSpinBoxMinimo (a menos que venha override)
        - Se WhiteboxTools estiver selecionado, usa DepthInSink
        - Caso contrário, usa _escolher_motor_profundidade para decidir entre SAGA / TauDEM
        """
        # MDT atual
        layer_id = self.comboBoxRaster.currentData()
        dem_layer = QgsProject.instance().mapLayer(layer_id)

        if not isinstance(dem_layer, QgsRasterLayer):
            self.mostrar_mensagem(self.tr("Selecione um MDT válido no combo antes de calcular a profundidade das depressões."), "Erro")
            return

        # Profundidade mínima (em metros): usa override se fornecido
        if h_min_override is not None:
            try:
                h_min = float(h_min_override)
            except Exception:
                h_min = 0.01
        else:
            h_min = 0.01
            if hasattr(self, "doubleSpinBoxMinimo"):
                h_min = float(self.doubleSpinBoxMinimo.value())

        # segurança
        if h_min < 0.0:
            h_min = 0.0

        # 1) Se WhiteboxTools estiver selecionado, usar DepthInSink
        if self.radioButtonTools.isChecked():
            self._calcular_profundidade_whitebox(dem_layer, h_min, gerar_vetor=gerar_vetor)
            return

        # 2) Caso contrário, decide entre SAGA / TauDEM
        motor, layer_preenchido = self._escolher_motor_profundidade(dem_layer)

        if motor == "saga" and layer_preenchido is not None:
            self._calcular_profundidade_saga(dem_layer, layer_preenchido, h_min, gerar_vetor=gerar_vetor)
        elif motor == "taudem" and layer_preenchido is not None:
            self._calcular_profundidade_taudem(dem_layer, layer_preenchido, h_min, gerar_vetor=gerar_vetor)
        else:
            self.mostrar_mensagem(self.tr("Não encontrei DEM preenchido (SAGA) nem FEL (TauDEM) para este MDT.\nExecute primeiro a drenagem com SAGA ou TauDEM."), "Erro")

    def _add_saga_vector(self, layer: QgsVectorLayer, short_code: str):
        """
        Adiciona um vetor gerado pelo SAGA ao projeto,
        dentro do grupo 'SAGA - Drenagem', sem expandir o grupo.
        """
        log_prefix = "SAGA - Tempo Salvo Tools"

        if not isinstance(layer, QgsVectorLayer) or not layer.isValid():
            QgsMessageLog.logMessage(self.tr("[{short_code}] Vetor inválido, não será adicionado.").format(short_code=short_code), log_prefix, level=Qgis.MessageLevel.Warning)
            return

        project = QgsProject.instance()

        # Não adiciona direto na raiz
        project.addMapLayer(layer, addToLegend=False)

        root = project.layerTreeRoot()
        group_name = self.tr("SAGA - Drenagem")
        group = root.findGroup(group_name)
        if group is None:
            group = root.addGroup(group_name)

        group.addLayer(layer)

        group.setExpanded(True)
        node = root.findLayer(layer.id())
        if node:
            node.setExpanded(False)

        # Se for camada de canais (SEGMENTS), aplica estilo por ORDER
        if short_code == "SEGMENTS":
            try:
                self._style_saga_channels_by_order(layer)
            except Exception as exc:
                QgsMessageLog.logMessage(self.tr("[{short_code}] Erro ao aplicar estilo por ORDER: {error}").format(short_code=short_code, error=str(exc)), log_prefix, level=Qgis.MessageLevel.Warning)

        elif short_code == "BASINS":
            try:
                self.aplicar_simbologia_bacias_por_order(layer)
            except Exception as exc:
                QgsMessageLog.logMessage(self.tr("[{short_code}] Erro ao aplicar simbologia por ORDER: {error}").format(short_code=short_code, error=str(exc)), log_prefix, level=Qgis.MessageLevel.Warning)

    def _style_saga_channels_by_order(self, layer: QgsVectorLayer):
        """
        Aplica estilo de canais SAGA baseado no campo ORDER:
          - Cada ordem (1,2,3,...) vira uma categoria
          - Quanto maior a ordem, mais grossa a linha
          - Azul claro para ordens baixas, azul escuro para ordens altas
        """
        if not isinstance(layer, QgsVectorLayer) or not layer.isValid():
            return

        field_name = "ORDER"
        idx = layer.fields().indexOf(field_name)
        if idx < 0:
            # Camada sem ORDER, não faz nada
            return

        # Coleta valores únicos de ORDER (inteiros)
        orders: set[int] = set()
        try:
            for feat in layer.getFeatures():
                val = feat.attribute(idx)
                if val is None:
                    continue
                try:
                    o = int(val)
                except (TypeError, ValueError):
                    continue
                orders.add(o)
        except Exception:
            return

        if not orders:
            return

        sorted_orders = sorted(orders)
        n = len(sorted_orders)

        # Azul claro -> azul escuro (pode ajustar)
        base_color = QColor(198, 219, 239)  # mais claro
        top_color  = QColor(8, 81, 156)     # mais escuro

        # Espessura em mm (pode ajustar)
        min_w = 0.1
        max_w = 0.80

        def interp_color(c1: QColor, c2: QColor, t: float) -> QColor:
            t = max(0.0, min(1.0, t))
            r = int(c1.red()   + (c2.red()   - c1.red())   * t)
            g = int(c1.green() + (c2.green() - c1.green()) * t)
            b = int(c1.blue()  + (c2.blue()  - c1.blue())  * t)
            return QColor(r, g, b)

        cats: list[QgsRendererCategory] = []

        for i, order_val in enumerate(sorted_orders):
            t = 0.0 if n == 1 else float(i) / float(n - 1)

            color = interp_color(base_color, top_color, t)
            width = min_w + (max_w - min_w) * t

            symbol = QgsLineSymbol.createSimple({})
            symbol.setWidth(width)
            symbol.setColor(color)

            label = self.tr("Ordem {order_val}").format(order_val=order_val)
            cat = QgsRendererCategory(order_val, symbol, label)
            cats.append(cat)

        renderer = QgsCategorizedSymbolRenderer(field_name, cats)
        layer.setRenderer(renderer)

        # Opcional: deixa um pouquinho translúcido
        layer.setOpacity(0.9)

        layer.triggerRepaint()

    def aplicar_simbologia_bacias_por_order(self, layer: QgsVectorLayer):
        """
        Aplica simbologia (polígonos) para as bacias SAGA baseada no campo ORDER.

        - Se o campo ORDER não existir, não aplica nada (e registra no log).
        - Cada ORDER vira uma categoria com cor interpolada (claro -> escuro).
        """
        log_prefix = "SAGA - Tempo Salvo Tools"

        if not isinstance(layer, QgsVectorLayer) or not layer.isValid():
            return

        # tenta localizar o campo ORDER (alguns outputs podem variar caixa)
        candidates = ("ORDER", "Order", "STRAHLER", "Strahler", "STRAHLER_ORD", "ORDER_")
        field_name = None
        idx = -1
        for cand in candidates:
            i_cand = layer.fields().indexOf(cand)
            if i_cand >= 0:
                field_name = cand
                idx = i_cand
                break

        if idx < 0:
            QgsMessageLog.logMessage(self.tr("[BASINS] Campo ORDER não encontrado na camada '{layer_name}'.").format(layer_name=layer.name()), log_prefix, level=Qgis.MessageLevel.Warning)
            return

        # Coleta valores únicos (inteiros)
        orders: set[int] = set()
        try:
            for feat in layer.getFeatures():
                val = feat.attribute(idx)
                if val is None:
                    continue
                try:
                    o = int(val)
                except (TypeError, ValueError):
                    continue
                orders.add(o)
        except Exception as exc:
            QgsMessageLog.logMessage(self.tr("[BASINS] Falha ao ler valores de {field_name}: {error}").format(field_name=field_name, error=str(exc)), log_prefix, level=Qgis.MessageLevel.Warning)
            return

        if not orders:
            return

        sorted_orders = sorted(orders)
        n = len(sorted_orders)

        # Paleta (verde claro -> verde escuro) para diferenciar dos canais
        base_color = QColor(229, 245, 224)  # mais claro
        top_color  = QColor(0, 109, 44)     # mais escuro

        def interp_color(c1: QColor, c2: QColor, t: float) -> QColor:
            t = max(0.0, min(1.0, t))
            r = int(c1.red()   + (c2.red()   - c1.red())   * t)
            g = int(c1.green() + (c2.green() - c1.green()) * t)
            b = int(c1.blue()  + (c2.blue()  - c1.blue())  * t)
            return QColor(r, g, b)

        cats: list[QgsRendererCategory] = []
        for i_order, order_val in enumerate(sorted_orders):
            t = 0.0 if n <= 1 else (i_order / float(n - 1))
            col = interp_color(base_color, top_color, t)
            col.setAlpha(90)  # transparência do preenchimento

            sym = QgsFillSymbol.createSimple({"color": col.name(), "outline_color": "80,80,80,120", "outline_width": "0.10"})
            try:
                sym.setColor(col)
            except Exception:
                pass  # nosec B110

            cats.append(QgsRendererCategory(order_val, sym, self.tr("ORDER {order_val}").format(order_val=order_val)))

        renderer = QgsCategorizedSymbolRenderer(field_name, cats)
        layer.setRenderer(renderer)

        # garante refresh imediato
        try:
            layer.triggerStyleChanged()
        except Exception:
            pass  # nosec B110
        layer.triggerRepaint()

    def _find_saga_canais_vector_layer(self, dem_layer: QgsRasterLayer) -> QgsVectorLayer | None:
        """
        Procura o vetor de canais gerado pelo fluxo SAGA (SagaDrenagemRunner),
        que costuma se chamar: "<DEM> - Canais SAGA"
        """
        if not isinstance(dem_layer, QgsRasterLayer) or not dem_layer.isValid():
            return None

        target_name = self.tr("{dem_name} - Canais SAGA").format(dem_name=dem_layer.name())
        for lyr in QgsProject.instance().mapLayers().values():
            if isinstance(lyr, QgsVectorLayer) and lyr.isValid() and lyr.name() == target_name:
                return lyr
        return None

    def _find_saga_channels_vector_layer(self, dem_layer: QgsRasterLayer) -> QgsVectorLayer | None:
        """
        Procura o vetor de canais gerado pelo fluxo SAGA para este MDT.

        Nome esperado:
          "<nome do MDT> - Canais SAGA"
        """
        if not isinstance(dem_layer, QgsRasterLayer) or not dem_layer.isValid():
            return None

        target_name = self.tr("{dem_name} - Canais SAGA").format(dem_name=dem_layer.name())
        project = QgsProject.instance()
        root = project.layerTreeRoot()

        # 1) Primeiro tenta dentro do grupo "SAGA - Drenagem" (mais organizado)
        grupo = root.findGroup(self.tr("SAGA - Drenagem"))
        if grupo:
            for node in grupo.findLayers():
                lyr = node.layer()
                if isinstance(lyr, QgsVectorLayer) and lyr.isValid():
                    nm = lyr.name() or ""
                    if nm == target_name or nm.startswith(target_name):
                        return lyr

        # 2) Fallback: varre tudo
        for lyr in project.mapLayers().values():
            if isinstance(lyr, QgsVectorLayer) and lyr.isValid():
                nm = lyr.name() or ""
                if nm == target_name or nm.startswith(target_name):
                    return lyr

        return None
#////////////////////////////////////////////
    def _init_combo_canais(self):
        """
        Preenche o comboBoxCanais e conecta a atualização do scrollAreaDados.
        """
        if not hasattr(self, "comboBoxCanais"):
            return

        self.comboBoxCanais.clear()

        tipos_canais = [
            (self.tr("Triangulares"), "triangular"),
            (self.tr("Trapezoidais"), "trapezoidal"),
            (self.tr("Retangulares"), "retangular"),
            (self.tr("Circulares"), "circular")]

        for rotulo, codigo in tipos_canais:
            self.comboBoxCanais.addItem(rotulo, codigo)

        # Conecta a mudança de tipo à atualização dos campos
        self.comboBoxCanais.currentIndexChanged.connect(self._update_canais_dados)

        # Atualiza a primeira vez
        self._update_canais_dados()

    def _clear_layout(self, layout):
        """
        Remove todos os widgets de um layout (usado antes de recriar os campos).
        """
        if layout is None:
            return

        while layout.count():
            item = layout.takeAt(0)
            w = item.widget()
            child_layout = item.layout()

            if w is not None:
                w.deleteLater()
            elif child_layout is not None:
                self._clear_layout(child_layout)

    def _draw_canal_triangular(self):
        """
        Desenha o esquema do canal triangular ocupando a área do graphicsViewTipo,
        com lâmina d'água dentro dos taludes, taludes mais espessos, textos maiores
        e triângulo retângulo indicando o z no talude direito.
        """
        scene = self.sceneTipo

        # Tamanho disponível do gráfico
        vw = self.graphicsViewTipo.viewport().width()
        vh = self.graphicsViewTipo.viewport().height()
        if vw <= 0:
            vw = 260
        if vh <= 0:
            vh = 120

        margin_x = 15
        margin_top = 12
        margin_bottom = 18

        width = float(vw)
        height = float(vh)
        scene.setSceneRect(0, 0, width, height)

        cx = width / 2.0
        top_y = margin_top
        bottom_y = height - margin_bottom

        # boca do canal
        half_top = (width / 2.0) - margin_x

        left_top  = QPointF(cx - half_top, top_y)
        right_top = QPointF(cx + half_top, top_y)
        bottom    = QPointF(cx, bottom_y)

        # Taludes mais espessos
        pen_wall = QPen(Qt.GlobalColor.gray, 4)
        scene.addLine(left_top.x(), left_top.y(),  bottom.x(),    bottom.y(), pen_wall)
        scene.addLine(bottom.x(),   bottom.y(),    right_top.x(), right_top.y(), pen_wall)

        # Pequeno trecho horizontal como continuação do talude
        border_len = 18  # comprimento da borda em cada lado

        # usa o mesmo pen dos taludes, parece uma continuação
        border_pen = pen_wall  

        # lado esquerdo: continua para a esquerda, na mesma altura do topo
        scene.addLine(left_top.x() - border_len, left_top.y(), left_top.x(), left_top.y(), border_pen)

        # lado direito: continua para a direita, na mesma altura do topo
        scene.addLine(right_top.x(), right_top.y(), right_top.x() + border_len, right_top.y(), border_pen)

        # Linha de terreno
        pen_ground = QPen(Qt.GlobalColor.black, 1, Qt.PenStyle.DashLine)
        scene.addLine(left_top.x() - 5, top_y, right_top.x() + 5, top_y, pen_ground)

        # Lâmina d'água (reta azul) dentro do canal
        total_depth = bottom_y - top_y
        water_frac = 0.65 # fração da profundidade

        water_y = bottom_y - total_depth * water_frac

        # largura da seção molhada naquele nível (interseção com os taludes)
        rel = (bottom_y - water_y) / total_depth
        water_half = half_top * rel - 3       # margem interna
        if water_half < 5:
            water_half = 5

        water_height = 6
        water_rect = QRectF(cx - water_half, water_y - water_height / 2.0, 2 * water_half, water_height)

        scene.addRect(water_rect, QPen(Qt.PenStyle.NoPen), QBrush(QColor(0, 80, 200)))

        # Textos e setas (maiores)
        font = QFont()
        font.setPointSize(10)
        pen_red = QPen(Qt.GlobalColor.red, 1)

        # B (largura na lâmina d'água)
        scene.addLine(cx - water_half, water_y - 10, cx + water_half, water_y - 10, pen_red)
        scene.addLine(cx - water_half, water_y - 12, cx - water_half, water_y - 8, pen_red)
        scene.addLine(cx + water_half, water_y - 12, cx + water_half, water_y - 8, pen_red)

        txtB = scene.addText("B", font)
        txtB.setDefaultTextColor(Qt.GlobalColor.red)
        txtB_rect = txtB.boundingRect()
        txtB.setPos(cx - txtB_rect.width()/2.0,  water_y - 26)

        # Yn (profundidade normal)
        scene.addLine(cx, water_y, cx, bottom_y, pen_red)
        txtYn = scene.addText("Yn", font)
        txtYn.setDefaultTextColor(Qt.GlobalColor.red)
        yn_rect = txtYn.boundingRect()
        txtYn.setPos(cx + 4, (water_y + bottom_y)/2.0 - yn_rect.height()/2.0)

        # f (folga) à direita
        x_f = right_top.x() + 6
        scene.addLine(x_f, water_y, x_f, top_y, pen_red)
        scene.addLine(x_f - 3, water_y, x_f + 3, water_y, pen_red)
        scene.addLine(x_f - 3, top_y,    x_f + 3, top_y,    pen_red)

        txtF = scene.addText("f", font)
        txtF.setDefaultTextColor(Qt.GlobalColor.red)
        f_rect = txtF.boundingRect()
        txtF.setPos(x_f + 3, (water_y + top_y)/2.0 - f_rect.height()/2.0)

        # Dimensão z – do lado direito do talude, com canto
        red_pen = QPen(Qt.GlobalColor.red, 1.4)
        font = QFont("Arial", 8)

        # ponto aproximadamente no meio do talude direito
        t_z = 0.50  # 0 = fundo, 1 = crista
        slope_mid = QPointF(bottom.x() + t_z * (right_top.x() - bottom.x()), bottom.y() + t_z * (right_top.y() - bottom.y()))

        # base da marca de z: um pouco abaixo do talude e TODA à direita dele
        z_base_y = slope_mid.y() + 2
        z_left_x = slope_mid.x() + 2      # começa logo à direita do talude
        z_right_x = z_left_x + 15         # vai mais para a direita

        # linha horizontal da dimensão z
        scene.addLine(z_left_x, z_base_y, z_right_x, z_base_y, red_pen)

        # "L" invertido na extremidade direita (cantinho de 90°)
        scene.addLine(z_right_x, z_base_y, z_right_x, z_base_y - 10, red_pen)

        # texto "z" centralizado sob a linha
        text_z = scene.addText("z", font)
        text_z.setDefaultTextColor(Qt.GlobalColor.red)
        br_z = text_z.boundingRect()
        text_z.setPos((z_left_x + z_right_x) / 2 - br_z.width() / 2, z_base_y + 2)

    def _add_spin_field(self, container, layout, *, attr_name: str, label: str, decimals: int, vmin: float, vmax: float, step: float, suffix: str = ""):
        """
        Cria um QDoubleSpinBox padronizado, adiciona ao layout,
        e guarda em self.attr_name.
        """
        spin = QDoubleSpinBox(container)
        spin.setDecimals(decimals)
        spin.setRange(vmin, vmax)
        spin.setSingleStep(step)
        if suffix:
            spin.setSuffix(suffix)

        layout.addRow(QLabel(label, container), spin)
        setattr(self, attr_name, spin)
        return spin

    def _update_graphics_tipo(self, tipo_codigo: str):
        """
        Atualiza o graphicsViewTipo de acordo com o tipo de canal selecionado.
        Aqui desenhamos tudo em código (sem imagem externa).
        """
        if not hasattr(self, "graphicsViewTipo"):
            return

        # Garante que a cena exista
        if not hasattr(self, "sceneTipo") or self.sceneTipo is None:
            self.sceneTipo = QGraphicsScene(self)
            self.graphicsViewTipo.setScene(self.sceneTipo)

        # Preview do tipo de canal: sem barras de rolagem (fica “limpo”)
        try:
            gv = self.graphicsViewTipo
            gv.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
            gv.setVerticalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
            gv.setFrameShape(QFrame.Shape.NoFrame) # opcional: remove a borda
            gv.setAlignment(Qt.AlignmentFlag.AlignCenter) # mantém o desenho centrado
        except Exception:
            pass  # nosec B110

        # Limpa o desenho atual
        self.sceneTipo.clear()

        if tipo_codigo == "triangular":
            self._draw_canal_triangular()
        elif tipo_codigo == "trapezoidal":
            self._draw_canal_trapezoidal()
        elif tipo_codigo == "retangular":
            self._draw_canal_retangular()
        elif tipo_codigo == "circular":
            self._draw_canal_circular()

        # Ajusta o zoom só quando o view estiver realmente "medido"
        try:
            vp = self.graphicsViewTipo.viewport()
            if (vp is not None) and self.graphicsViewTipo.isVisible() and (vp.width() > 10) and (vp.height() > 10):
                # reset evita ficar preso numa transformação ruim de quando estava oculto
                try:
                    self.graphicsViewTipo.resetTransform()
                except Exception:
                    pass  # nosec B110

                rect = self.sceneTipo.itemsBoundingRect()
                if rect.isNull():
                    rect = self.sceneTipo.sceneRect()

                if not rect.isNull():
                    self.graphicsViewTipo.fitInView(rect, Qt.AspectRatioMode.KeepAspectRatio)
        except Exception:
            pass  # nosec B110

    def _draw_canal_trapezoidal(self):
        """
        Desenha o esquema de um canal trapezoidal no graphicsViewTipo,
        com taludes espessos, base horizontal, lâmina d'água e cotas
        B, Yn, f, 1, b e z, em estilo semelhante ao canal triangular.
        """
        scene = self.sceneTipo

        # Tamanho disponível do gráfico
        vw = self.graphicsViewTipo.viewport().width()
        vh = self.graphicsViewTipo.viewport().height()
        if vw <= 0:
            vw = 260
        if vh <= 0:
            vh = 120

        margin_x = 15
        margin_top = 12
        margin_bottom = 24  # um pouco maior por causa da cota "b"

        width = float(vw)
        height = float(vh)
        scene.setSceneRect(0, 0, width, height)

        cx = width / 2.0
        top_y = margin_top
        bottom_y = height - margin_bottom

        # Largura no topo e na base
        half_top = (width / 2.0) - margin_x
        half_base = half_top * 0.45  # base mais estreita

        # Pontos principais
        left_top   = QPointF(cx - half_top,  top_y)
        right_top  = QPointF(cx + half_top,  top_y)
        left_base  = QPointF(cx - half_base, bottom_y)
        right_base = QPointF(cx + half_base, bottom_y)

        # Taludes e base (cinza, mais espessos)
        pen_wall = QPen(Qt.GlobalColor.gray, 4)
        scene.addLine(left_top.x(),  left_top.y(),  left_base.x(),  left_base.y(),  pen_wall)
        scene.addLine(right_base.x(), right_base.y(), right_top.x(), right_top.y(), pen_wall)
        scene.addLine(left_base.x(), left_base.y(), right_base.x(), right_base.y(), pen_wall)

        # Pequeno trecho horizontal como continuação do talude
        border_len = 18
        border_pen = pen_wall
        scene.addLine(left_top.x() - border_len,  left_top.y(), left_top.x(), left_top.y(),  border_pen)
        scene.addLine(right_top.x(), right_top.y(), right_top.x() + border_len, right_top.y(), border_pen)

        # Linha de terreno (tracejada)
        pen_ground = QPen(Qt.GlobalColor.black, 1, Qt.PenStyle.DashLine)
        scene.addLine(left_top.x() - 5, top_y, right_top.x() + 5, top_y, pen_ground)

        # Lâmina d’água
        total_depth = bottom_y - top_y
        water_frac = 0.60
        water_y = bottom_y - total_depth * water_frac

        # Interseção da lâmina com os taludes
        t_w = (water_y - top_y) / (bottom_y - top_y)
        xw_left  = left_top.x()  + t_w * (left_base.x()  - left_top.x())
        xw_right = right_top.x() + t_w * (right_base.x() - right_top.x())

        inset = 3
        water_left  = xw_left  + inset
        water_right = xw_right - inset
        water_height = 6

        water_rect = QRectF(water_left, water_y - water_height / 2.0, water_right - water_left, water_height)
        scene.addRect(water_rect, QPen(Qt.PenStyle.NoPen), QBrush(QColor(0, 80, 200)))

        # Textos e setas em vermelho
        font_main = QFont()
        font_main.setPointSize(10)
        pen_red = QPen(Qt.GlobalColor.red, 1)

        # B (largura na lâmina d’água)
        yB = water_y - 10
        scene.addLine(water_left,  yB, water_right, yB, pen_red)
        scene.addLine(water_left,  yB - 2, water_left,  yB + 2, pen_red)
        scene.addLine(water_right, yB - 2, water_right, yB + 2, pen_red)

        txtB = scene.addText("B", font_main)
        txtB.setDefaultTextColor(Qt.GlobalColor.red)
        brB = txtB.boundingRect()
        txtB.setPos((water_left + water_right) / 2.0 - brB.width() / 2.0, yB - brB.height() - 2)

        # Yn (profundidade normal) – centro do canal
        scene.addLine(cx, water_y, cx, bottom_y, pen_red)
        txtYn = scene.addText("Yn", font_main)
        txtYn.setDefaultTextColor(Qt.GlobalColor.red)
        brYn = txtYn.boundingRect()
        txtYn.setPos(cx + 4, (water_y + bottom_y) / 2.0 - brYn.height() / 2.0)

        # f e 1 – folga e altura medida no talude direito (vertical)
        x_f = right_top.x() + 8
        scene.addLine(x_f, water_y, x_f, top_y, pen_red)
        scene.addLine(x_f - 3, water_y, x_f + 3, water_y, pen_red)
        scene.addLine(x_f - 3, top_y,    x_f + 3, top_y,    pen_red)

        # texto "f" (parte de cima)
        txtF = scene.addText("f", font_main)
        txtF.setDefaultTextColor(Qt.GlobalColor.red)
        brF = txtF.boundingRect()
        txtF.setPos(x_f + 3, top_y + 2)

        # b – largura da base
        yb = bottom_y + 10
        scene.addLine(left_base.x(),  yb, right_base.x(), yb, pen_red)
        scene.addLine(left_base.x(),  yb - 2, left_base.x(),  yb + 2, pen_red)
        scene.addLine(right_base.x(), yb - 2, right_base.x(), yb + 2, pen_red)

        txtb = scene.addText("b", font_main)
        txtb.setDefaultTextColor(Qt.GlobalColor.red)
        brb = txtb.boundingRect()
        txtb.setPos((left_base.x() + right_base.x()) / 2.0 - brb.width() / 2.0, yb + 2)

        # z – indicação na face do talude direito, com "L" de referência
        red_pen = QPen(Qt.GlobalColor.red, 1.4)
        font_z = QFont("Arial", 8)

        t_z = 0.45  # ponto intermediário do talude direito
        slope_mid = QPointF(right_base.x() + t_z * (right_top.x() - right_base.x()), right_base.y() + t_z * (right_top.y() - right_base.y()))

        z_base_y = slope_mid.y() + 2
        z_left_x = slope_mid.x() + 2
        z_right_x = z_left_x + 15

        scene.addLine(z_left_x, z_base_y, z_right_x, z_base_y, red_pen)             # horizontal
        scene.addLine(z_right_x, z_base_y, z_right_x, z_base_y - 10, red_pen)       # perninha do "L"

        text_z = scene.addText("z", font_z)
        text_z.setDefaultTextColor(Qt.GlobalColor.red)
        brz = text_z.boundingRect()
        text_z.setPos((z_left_x + z_right_x) / 2.0 - brz.width() / 2.0, z_base_y + 2)

    def _draw_canal_retangular(self):
        """
        Desenha o esquema do canal retangular ocupando a área do graphicsViewTipo,
        com lâmina d'água, paredes verticais, textos B, f, Yn e b.
        """
        scene = self.sceneTipo

        # Tamanho disponível do gráfico
        vw = self.graphicsViewTipo.viewport().width()
        vh = self.graphicsViewTipo.viewport().height()
        if vw <= 0:
            vw = 260
        if vh <= 0:
            vh = 120

        margin_x = 25
        margin_top = 12
        margin_bottom = 18

        width = float(vw)
        height = float(vh)
        scene.setSceneRect(0, 0, width, height)

        cx = width / 2.0
        top_y = margin_top + 10         # topo das paredes
        bottom_y = height - margin_bottom

        # largura interna do canal
        half_inner = (width / 2.0) - margin_x
        if half_inner < 30:
            half_inner = 30

        left_inner  = cx - half_inner
        right_inner = cx + half_inner

        # Paredes e fundo (cinza mais espesso)
        pen_wall = QPen(Qt.GlobalColor.gray, 4)
        scene.addLine(left_inner,  top_y, left_inner,  bottom_y, pen_wall)   # parede esquerda
        scene.addLine(right_inner, top_y, right_inner, bottom_y, pen_wall)   # parede direita
        scene.addLine(left_inner,  bottom_y, right_inner, bottom_y, pen_wall)  # fundo

        # Continuação horizontal das paredes (borda)
        border_len = 18
        scene.addLine(left_inner - border_len, top_y, left_inner, top_y, pen_wall)
        scene.addLine(right_inner, top_y, right_inner + border_len, top_y, pen_wall)

        # Linha de terreno (tracejada) um pouco acima do topo
        pen_ground = QPen(Qt.GlobalColor.black, 1, Qt.PenStyle.DashLine)
        scene.addLine(left_inner - border_len * 0.5, top_y - 4, right_inner + border_len * 0.5, top_y - 4, pen_ground)

        # Lâmina d'água
        total_depth = bottom_y - top_y
        water_frac = 0.6

        water_y = bottom_y - total_depth * water_frac
        water_height = 6

        water_rect = QRectF(left_inner + 3, water_y - water_height / 2.0, (right_inner - left_inner) - 6, water_height)
        scene.addRect(water_rect, QPen(Qt.PenStyle.NoPen), QBrush(QColor(0, 80, 200)))

        # Textos e setas (vermelho)
        font = QFont()
        font.setPointSize(10)
        pen_red = QPen(Qt.GlobalColor.red, 1)

        # B (largura na lâmina d'água)
        scene.addLine(left_inner, water_y - 10, right_inner, water_y - 10, pen_red)
        scene.addLine(left_inner,  water_y - 12, left_inner,  water_y - 8, pen_red)
        scene.addLine(right_inner, water_y - 12, right_inner, water_y - 8, pen_red)

        txtB = scene.addText("B", font)
        txtB.setDefaultTextColor(Qt.GlobalColor.red)
        brB = txtB.boundingRect()
        txtB.setPos(cx - brB.width() / 2.0, water_y - 26)

        # Yn (profundidade normal)
        x_yn = (left_inner + right_inner) / 2.0
        scene.addLine(x_yn, water_y, x_yn, bottom_y, pen_red)
        scene.addLine(x_yn - 3, water_y,   x_yn + 3, water_y,   pen_red)
        scene.addLine(x_yn - 3, bottom_y,  x_yn + 3, bottom_y,  pen_red)

        txtYn = scene.addText("Yn", font)
        txtYn.setDefaultTextColor(Qt.GlobalColor.red)
        brYn = txtYn.boundingRect()
        txtYn.setPos(x_yn + 4, (water_y + bottom_y) / 2.0 - brYn.height() / 2.0)

        # f (folga) na parede direita
        x_f = right_inner + 6
        scene.addLine(x_f, water_y, x_f, top_y, pen_red)
        scene.addLine(x_f - 3, water_y, x_f + 3, water_y, pen_red)
        scene.addLine(x_f - 3, top_y,    x_f + 3, top_y,    pen_red)

        txtF = scene.addText("f", font)
        txtF.setDefaultTextColor(Qt.GlobalColor.red)
        brF = txtF.boundingRect()
        txtF.setPos(x_f + 3, (water_y + top_y) / 2.0 - brF.height() / 2.0)

        # b (largura da base)
        base_dim_y = bottom_y + 8
        scene.addLine(left_inner, base_dim_y, right_inner, base_dim_y, pen_red)
        scene.addLine(left_inner,  base_dim_y, left_inner,  base_dim_y - 6, pen_red)
        scene.addLine(right_inner, base_dim_y, right_inner, base_dim_y - 6, pen_red)

        txtb = scene.addText("b", font)
        txtb.setDefaultTextColor(Qt.GlobalColor.red)
        brb = txtb.boundingRect()
        txtb.setPos(cx - brb.width() / 2.0, base_dim_y + 2)

    def _draw_canal_circular(self):
        """
        Desenha o esquema do canal circular com:
        - D à esquerda
        - Yn à direita, medido da lâmina até o fundo
        - corda da lâmina em azul
        - raios até as extremidades da corda, formando θ
        """

        scene = self.sceneTipo

        vw = self.graphicsViewTipo.viewport().width()
        vh = self.graphicsViewTipo.viewport().height()
        if vw <= 0:
            vw = 260
        if vh <= 0:
            vh = 120

        width = float(vw)
        height = float(vh)
        scene.setSceneRect(0, 0, width, height)

        margin_left = 42
        margin_right = 42
        margin_top = 14
        margin_bottom = 14

        cx = width / 2.0
        cy = height / 2.0

        radius = min((width - margin_left - margin_right) / 2.0,
            (height - margin_top - margin_bottom) / 2.0)
        if radius <= 0:
            radius = 30.0

        left_x = cx - radius
        right_x = cx + radius
        top_y = cy - radius
        bottom_y = cy + radius

        pen_circle = QPen(Qt.GlobalColor.gray, 3)
        pen_red = QPen(Qt.GlobalColor.red, 1)
        pen_blue = QPen(QColor(0, 80, 220), 3)

        font = QFont()
        font.setPointSize(10)

        # Lê D real
        D_real = 1.0
        if hasattr(self, "spinDiametro") and self.spinDiametro is not None:
            try:
                D_real = float(self.spinDiametro.value())
            except Exception:
                D_real = 1.0
        if D_real <= 0.0:
            D_real = 1.0

        # Lê Yn real
        yn_real = None
        if hasattr(self, "spinYn") and self.spinYn is not None:
            try:
                yn_real = float(self.spinYn.value())
            except Exception:
                yn_real = None

        # Preview simbólico quando Yn ainda estiver zerado ou inválido
        if yn_real is None or yn_real <= 0.0:
            yn_real = 0.35 * D_real

        yn_real = max(0.0, min(yn_real, D_real))

        # Fração real
        frac_real = yn_real / D_real

        # Fração visual protegida para o preview não ficar degenerado
        frac_draw = max(0.12, min(0.88, frac_real))

        # y da lâmina: Yn é medido do fundo até a lâmina
        water_y = bottom_y - frac_draw * (2.0 * radius)

        # Corda da lâmina
        dy = water_y - cy
        semi_chord = math.sqrt(max(0.0, radius * radius - dy * dy))
        x_left_water = cx - semi_chord
        x_right_water = cx + semi_chord

        # Círculo
        circle_rect = QRectF(left_x, top_y, 2.0 * radius, 2.0 * radius)
        scene.addEllipse(circle_rect, pen_circle)

        # Lâmina
        scene.addLine(x_left_water, water_y, x_right_water, water_y, pen_blue)

        # Raios até as extremidades da corda
        scene.addLine(cx, cy, x_left_water, water_y, pen_red)
        scene.addLine(cx, cy, x_right_water, water_y, pen_red)

        # Texto θ um pouco abaixo da corda, mas sem colar no fundo
        txt_theta = scene.addText("θ", font)
        txt_theta.setDefaultTextColor(Qt.GlobalColor.red)
        br_theta = txt_theta.boundingRect()

        theta_y = min(cy + radius * 0.30, water_y + 10)
        theta_y = min(theta_y, bottom_y - br_theta.height() - 4)
        txt_theta.setPos(cx - br_theta.width() / 2.0, theta_y)

        # D à esquerda
        x_d = left_x - 16
        scene.addLine(x_d, top_y, x_d, bottom_y, pen_red)
        scene.addLine(x_d - 3, top_y, x_d + 3, top_y, pen_red)
        scene.addLine(x_d - 3, bottom_y, x_d + 3, bottom_y, pen_red)

        txt_d = scene.addText("D", font)
        txt_d.setDefaultTextColor(Qt.GlobalColor.red)
        br_d = txt_d.boundingRect()
        txt_d.setPos(x_d - br_d.width() - 4, cy - br_d.height() / 2.0)

        # Yn à direita: da lâmina até o fundo
        x_yn = right_x + 16
        scene.addLine(x_yn, water_y, x_yn, bottom_y, pen_red)
        scene.addLine(x_yn - 3, water_y, x_yn + 3, water_y, pen_red)
        scene.addLine(x_yn - 3, bottom_y, x_yn + 3, bottom_y, pen_red)

        txt_yn = scene.addText("Yn", font)
        txt_yn.setDefaultTextColor(Qt.GlobalColor.red)
        br_yn = txt_yn.boundingRect()
        txt_yn.setPos(x_yn + 4, (water_y + bottom_y) / 2.0 - br_yn.height() / 2.0)
#////////////////////////////////////////////
    def _refresh_graphics_tipo_when_visible(self):
        """Refaz o desenho do preview quando o graphicsViewTipo estiver com tamanho válido."""
        v = getattr(self, "graphicsViewTipo", None)
        if v is None:
            return

        vp = v.viewport()
        if (vp is None) or (not v.isVisible()) or (vp.width() < 10) or (vp.height() < 10):
            # ainda não está pronto (aba oculta / layout não calculado)
            QTimer.singleShot(80, self._refresh_graphics_tipo_when_visible)
            return

        # pega o tipo atual e redesenha
        tipo = None
        try:
            tipo = self.comboBoxCanais.currentData()
        except Exception:
            pass  # nosec B110
        if not tipo:
            tipo = "triangular"

        try:
            self._update_graphics_tipo(tipo)
        except Exception:
            pass  # nosec B110

    def eventFilter(self, obj, event):
        # Quando a aba “CANAIS” é ativada, o viewport do QGraphicsView recebe Show/Resize.
        try:
            if hasattr(self, "graphicsViewTipo") and obj is self.graphicsViewTipo.viewport():
                if event.type() in (QEvent.Type.Show, QEvent.Type.Resize):
                    QTimer.singleShot(0, self._refresh_graphics_tipo_when_visible)
        except Exception:
            pass  # nosec B110

        return super().eventFilter(obj, event)

    def _init_pushButtonLista(self):
        """
        Configura o pushButtonLista para abrir um menu com as opções.
        Não altera o texto do botão, apenas guarda a seleção.
        """
        if not hasattr(self, "pushButtonLista"):
            return

        self.menuLista = QMenu(self.pushButtonLista)

        itens = [
            (self.tr("Condutos Circulares"), "condutos_circulares"),
            (self.tr("Canais Revestidos"), "canais_revestidos"),
            ("---", None),
            (self.tr("Cursos D'Água Dragados ou Escavados"), "cursos_dragados"),
            (self.tr("Cursos D'Água Naturais Menores"), "cursos_naturais_menores"),
            (self.tr("Enchentes"), "enchentes"),
            (self.tr("Cursos D'Água Naturais Maiores"), "naturais_maiores")]

        group = QActionGroup(self.menuLista)
        group.setExclusive(True)

        self._lista_actions = []
        first_action = None

        for texto, codigo in itens:
            if texto == "---":
                self.menuLista.addSeparator()
                continue

            ac = QAction(texto, self.menuLista)
            ac.setCheckable(True)
            ac.setData(codigo)
            group.addAction(ac)
            self.menuLista.addAction(ac)
            self._lista_actions.append(ac)

            ac.triggered.connect(lambda checked, a=ac: self._on_lista_item_selected(a))

            if first_action is None:
                first_action = ac

        # Seleciona a primeira opção por padrão (se quiser)
        if first_action is not None:
            first_action.setChecked(True)
            self._on_lista_item_selected(first_action)

        self.pushButtonLista.setMenu(self.menuLista)

    def _on_lista_item_selected(self, action: QAction):
        """
        Guarda apenas o código do item selecionado.
        Não altera o texto do botão definido no Qt Designer.
        """
        if not action or not action.isChecked():
            return

        texto = action.text()
        codigo = action.data()

        # guarda o código selecionado para uso posterior
        self.lista_tipo_codigo = codigo

        # opcional: só tooltip (não mexe no texto visível do botão)
        self.pushButtonLista.setToolTip(self.tr("Tipo selecionado: {text}").format(text=texto))

    def _init_lista_menu(self):
        """
        Cria o menu do pushButtonLista e conecta as ações.
        """
        self.menuLista = QMenu(self)
        self.pushButtonLista.setMenu(self.menuLista)

        group = QActionGroup(self.menuLista)
        group.setExclusive(True)
        self._lista_action_group = group

        def add_item(texto: str, code: str):
            act = QAction(texto, self.menuLista)
            act.setCheckable(True)
            act.setData(code)  # código interno, não traduzir
            self.menuLista.addAction(act)
            group.addAction(act)
            return act

        add_item(self.tr("Condutos Circulares"), "condutos_circulares")
        add_item(self.tr("Canais Revestidos"), "canais_revestidos")
        add_item(self.tr("Cursos D'Água Dragados ou Escavados"), "cursos_dragados")
        add_item(self.tr("Cursos D'Água Naturais Menores"), "cursos_naturais_menores")
        add_item(self.tr("Enchentes"), "enchentes")
        add_item(self.tr("Cursos D'Água Naturais Maiores"), "naturais_maiores")

        group.triggered.connect(self._on_lista_action_triggered)

    def _on_lista_action_triggered(self, action: QAction):
        tipo_tabela = action.data()

        if not tipo_tabela:
            return

        self.pushButtonLista.setToolTip(
            self.tr("Tipo selecionado: {text}").format(text=action.text()))

        dlg = TabelaRugosidadeCondutosDialog(self, tipo_tabela=tipo_tabela)
        dlg.exec()
#////////////////////////////////////////////
    def _init_pushButtonCamada(self):
        """
        Conecta o pushButtonCamada ao slot que cria a camada
        de canais com o mesmo SRC do raster selecionado.
        """
        if hasattr(self, "pushButtonCamada"):
            self.pushButtonCamada.clicked.connect(self._on_pushButtonCamada_clicked)

    def _get_selected_raster_from_combo(self):
        """
        Tenta obter o QgsRasterLayer atualmente selecionado
        no comboBoxRaster.
        """
        if not hasattr(self, "comboBoxRaster"):
            return None

        data = self.comboBoxRaster.currentData()
        # Caso você esteja guardando o layer diretamente
        from qgis.core import QgsRasterLayer, QgsProject

        if isinstance(data, QgsRasterLayer):
            return data

        # Caso esteja guardando o ID da camada
        if isinstance(data, str):
            lyr = QgsProject.instance().mapLayer(data)
            if isinstance(lyr, QgsRasterLayer):
                return lyr

        # Fallback: procurar por nome
        name = self.comboBoxRaster.currentText().strip()
        if not name:
            return None

        for lyr in QgsProject.instance().mapLayers().values():
            if isinstance(lyr, QgsRasterLayer) and lyr.name() == name:
                return lyr

        return None

    def _next_canal_layer_name(self, base_name: str) -> str:
        """
        Gera um nome de camada que não exista no projeto.
        Se já existir 'base_name', cria 'base_name_1', depois _2, etc.
        """
        base_name = (base_name or self.tr("CN_Canal")).strip()
        project = QgsProject.instance()
        existing_names = {lyr.name() for lyr in project.mapLayers().values()}

        if base_name not in existing_names:
            return base_name

        suffix = 1
        while f"{base_name}_{suffix}" in existing_names:
            suffix += 1

        return f"{base_name}_{suffix}"

    def _get_canal_base_name(self) -> str:
        """
        Retorna o nome traduzido da camada conforme o tipo selecionado
        em comboBoxCanais.
        """
        if not hasattr(self, "comboBoxCanais"):
            return self.tr("CN_Canal")

        tipo = self.comboBoxCanais.currentData()

        nomes = {
            "triangular": self.tr("CN_Triangular"),
            "trapezoidal": self.tr("CN_Trapezoidal"),
            "retangular": self.tr("CN_Retangular"),
            "circular": self.tr("CN_Circular")}

        return nomes.get(tipo, self.tr("CN_Canal"))

    def _on_pushButtonCamada_clicked(self):
        """
        Cria uma nova camada de canais (linhas) com o SRC do raster
        selecionado em comboBoxRaster, usando o tipo de canal do
        comboBoxCanais como base para o nome: CN_Triangular, CN_Trapezoidal, CN_Retangular, CN_Circular.
        Adiciona a camada ao projeto e ao tableViewCamada.
        Se o raster estiver em coordenadas geográficas, apenas avisa.
        """
        # 1) Verifica raster
        raster = self._get_selected_raster_from_combo()
        if raster is None:
            self.mostrar_mensagem(self.tr("Selecione um raster no comboBoxRaster antes de criar a camada de canais."), "Aviso")
            return

        crs = raster.crs()
        if not crs.isValid():
            self.mostrar_mensagem(self.tr("O SRC do raster selecionado é inválido."), "Aviso")
            return

        # 2) Se SRC for geográfico, apenas avisa
        if crs.isGeographic():
            self.mostrar_mensagem(self.tr("O raster selecionado está em coordenadas geográficas.\nUse um raster em projeção plana para criar a camada de canais."), "Aviso")
            return

        # 3) Nome base conforme o tipo de canal (CN_Triangular, CN_Trapezoidal, CN_Retangular, CN_Circular)
        base_name = self._get_canal_base_name()
        layer_name = self._next_canal_layer_name(base_name)

        # 4) Cria camada de linhas em memória com o mesmo CRS do raster
        authid = crs.authid()  # ex.: "EPSG:31983"
        if authid:
            uri = f"LineString?crs={authid}"
        else:
            uri = "LineString"

        vlayer = QgsVectorLayer(uri, layer_name, "memory")
        if not vlayer.isValid():
            self.mostrar_mensagem(self.tr("Não foi possível criar a camada de canais."), "Erro")
            return

        # Guarda o tipo de canal na camada (triangular, trapezoidal, retangular, circular)
        if hasattr(self, "comboBoxCanais"):
            tipo_canal = self.comboBoxCanais.currentData()
            if tipo_canal:
                vlayer.setCustomProperty("rd_tipo_canal", tipo_canal)

        # Oculta o formulário de atributos automático
        cfg = vlayer.editFormConfig()
        cfg.setSuppress(QgsEditFormConfig.FeatureFormSuppress.SuppressOn)
        vlayer.setEditFormConfig(cfg)

        vlayer.updateFields()

        # Garante campos de atributos básicos + específicos do tipo
        tipo_canal = ""
        if hasattr(self, "comboBoxCanais"):
            tipo_canal = self.comboBoxCanais.currentData() or ""
            if tipo_canal:
                vlayer.setCustomProperty("rd_tipo_canal", tipo_canal)

        self._ensure_campos_canal_for_layer(vlayer, tipo_canal)

        # Aplica simbologia de seta com cor baseada na Declividade(I)
        self.apply_arrow_symbology(vlayer)
        # Aplica rótulo do CN com cor baseada na Declividade(I)
        self.apply_cn_labeling(vlayer)

        # 5) Adiciona ao projeto DENTRO do grupo 'CANAIS'
        project = QgsProject.instance()
        group = self._ensure_canais_group()

        # Não deixar o QGIS colocar em raiz automaticamente
        project.addMapLayer(vlayer, False)
        group.addLayer(vlayer)

        # Garante um número de camada (1,2,3,...) para esta camada nova
        self._ensure_cn_layer_index(vlayer)

        # 6) Recarrega o tableViewCamada a partir do grupo
        if hasattr(self, "_camadas_model"):
            self._reload_tableViewCamada_from_group()
            # Seleciona a camada recém-criada como camada corrente
            self._select_camada_row_by_layer_id(vlayer.id())

        # registra sinais para preenchimento automático do CN
        self._register_cn_layer(vlayer)

        self.mostrar_mensagem(self.tr("Camada '{layer_name}' criada com SRC {authid} e adicionada ao projeto.").format(layer_name=layer_name, authid=crs.authid()), "Info")

        # Já entra em edição com Adicionar Linha ativo (ferramenta nativa)
        vlayer.startEditing()
        self.iface.setActiveLayer(vlayer)
        try:
            self.iface.actionAddFeature().trigger()
        except AttributeError:
            pass  # nosec B110

    def _get_canais_group(self) -> QgsLayerTreeGroup | None:
        """
        Retorna o grupo 'CANAIS' se existir, senão None.
        """
        root = QgsProject.instance().layerTreeRoot()
        return root.findGroup(self.tr("CANAIS"))

    def _init_tableViewCamada(self):
        """
        Inicializa o model do tableViewCamada e recarrega do grupo 'CANAIS'.
        Também conecta a mudança de seleção para atualizar o tableViewFeicao.
        """
        if not hasattr(self, "tableViewCamada"):
            return

        model = QStandardItemModel(self.tableViewCamada)
        model.setHorizontalHeaderLabels([self.tr("CAMADAS")])
        self.tableViewCamada.setModel(model)
        self._camadas_model = model

        header = self.tableViewCamada.horizontalHeader()
        header.setDefaultAlignment(Qt.AlignmentFlag.AlignCenter)
        header.setSectionResizeMode(0, QHeaderView.ResizeMode.Stretch)

        # Delegate com botão de deletar à esquerda da camada
        self._camada_delete_delegate = CanalDeleteButtonDelegate(self.tableViewCamada, self, mode="camada")
        self.tableViewCamada.setItemDelegateForColumn(0, self._camada_delete_delegate)

        # carrega camadas do grupo CANAIS
        self._reload_tableViewCamada_from_group()

        # conecta seleção -> atualiza feições
        sel_model = self.tableViewCamada.selectionModel()
        if sel_model:
            sel_model.currentRowChanged.connect(self._on_camada_row_changed)

        # Reage à seleção “de verdade” (clique, teclado, etc.)
        try:
            sel_model.selectionChanged.connect(lambda *_: self._update_pushButtonCamadaDXF_state())
        except Exception:
            pass  # nosec B110

        # dispara uma vez, se já tiver algo selecionado
        idx = self.tableViewCamada.currentIndex()
        if idx.isValid():
            self._on_camada_row_changed(idx, QModelIndex())

        if hasattr(self, "_update_pushButtonCamadaDXF_state"):
            self._update_pushButtonCamadaDXF_state()

        if hasattr(self, "_update_pushButtonSalvar_state"):
            self._update_pushButtonSalvar_state()

    def _init_tableViewFeicao(self):
        """
        Inicializa o model do tableViewFeicao (lista de feições da camada selecionada).
        """
        if not hasattr(self, "tableViewFeicao"):
            return

        model = QStandardItemModel(self.tableViewFeicao)
        model.setHorizontalHeaderLabels([self.tr("CANALETAS")])
        self.tableViewFeicao.setModel(model)
        self._feicao_model = model

        header = self.tableViewFeicao.horizontalHeader()
        header.setDefaultAlignment(Qt.AlignmentFlag.AlignCenter)
        header.setSectionResizeMode(0, QHeaderView.ResizeMode.Stretch)

        # Delegate com botão de deletar à esquerda do CN
        self._feicao_delete_delegate = CanalDeleteButtonDelegate(self.tableViewFeicao, self, mode="feicao")
        self.tableViewFeicao.setItemDelegateForColumn(0, self._feicao_delete_delegate)

        # quando mudar a linha selecionada, atualiza o scrollAreaDados
        sel_model = self.tableViewFeicao.selectionModel()
        if sel_model:
            sel_model.currentRowChanged.connect(self._on_feicao_row_changed)

    def _reload_tableViewFeicao_from_layer(self, layer):
        """
        Recria o conteúdo do tableViewFeicao com as feições da camada informada.
        Mostra apenas o valor do atributo CN em cada linha.
        """
        if not hasattr(self, "tableViewFeicao") or self._feicao_model is None:
            return

        model = self._feicao_model
        model.removeRows(0, model.rowCount())

        # se não há camada, apenas limpa a tabela
        if layer is None:
            return

        if not isinstance(layer, QgsVectorLayer):
            return

        idx_cn = layer.fields().indexOf("CN")

        for feat in layer.getFeatures():
            cn_val = feat.attribute(idx_cn) if idx_cn >= 0 else ""
            cn_str = "" if cn_val is None else str(cn_val)

            item_cn = QStandardItem("     " + cn_str)
            item_cn.setEditable(False)

            # guarda o fid “escondido” se precisar depois
            item_cn.setData(feat.id(), Qt.ItemDataRole.UserRole)

            model.appendRow([item_cn])

        # Atualiza estado dos botões após recarregar a tabela
        if hasattr(self, "_update_pushButtonCalcular_state"):
            self._update_pushButtonCalcular_state()
        if hasattr(self, "_update_pushButtonInverter_state"):
            self._update_pushButtonInverter_state()

    def _on_canal_features_deleted(self, fids):
        """
        Reage à remoção de feições em qualquer camada de canais.

        - Se for a camada atualmente selecionada, recarrega o tableViewFeicao
          e ajusta a seleção para manter o gráfico (scrollAreaGrafico) em sincronia.
        - Se não restarem feições, limpa o gráfico.
        """
        layer = self.sender()
        if not isinstance(layer, QgsVectorLayer):
            return

        if hasattr(self, "_current_canal_layer") and layer == self._current_canal_layer:
            # guarda o fid atualmente selecionado (se houver)
            current_fid = None
            try:
                if hasattr(self, "tableViewFeicao") and self.tableViewFeicao is not None:
                    sm = self.tableViewFeicao.selectionModel()
                    if sm is not None:
                        idx = sm.currentIndex()
                        if idx.isValid():
                            current_fid = idx.data(Qt.ItemDataRole.UserRole)
            except Exception:
                current_fid = None

            # recarrega a lista de feições (já excluindo as removidas)
            self._reload_tableViewFeicao_from_layer(layer)

            # tenta manter o fid selecionado; se não existir mais, seleciona a primeira linha
            try:
                model = getattr(self, "_feicao_model", None)
                if hasattr(self, "tableViewFeicao") and self.tableViewFeicao is not None and model is not None and model.rowCount() > 0:
                    target_row = 0

                    if current_fid is not None:
                        for row in range(model.rowCount()):
                            idx = model.index(row, 0)
                            if idx.data(Qt.ItemDataRole.UserRole) == current_fid:
                                target_row = row
                                break

                    sel_idx = model.index(target_row, 0)
                    self.tableViewFeicao.setCurrentIndex(sel_idx)
                    # _on_feicao_row_changed será disparado e atualizará o gráfico
                else:
                    # sem feições -> limpa gráfico e crosshair
                    if hasattr(self, "_clear_grafico_canal_terreno"):
                        self._clear_grafico_canal_terreno()
                    if hasattr(self, "_hide_grafico_crosshair"):
                        self._hide_grafico_crosshair()
            except Exception:
                # se algo falhar, pelo menos tenta atualizar/limpar o gráfico
                if hasattr(self, "_update_grafico_from_selection"):
                    try:
                        self._update_grafico_from_selection()
                    except Exception:
                        pass  # nosec B110

        # Atualiza a aba PROJETO (lista + gráfico)
        if hasattr(self, "_refresh_projeto_views"):
            self._refresh_projeto_views(layer)

        # Atualiza estados de botões que dependem de seleção/itens
        if hasattr(self, "_update_pushButtonCamadaDXF_state"):
            self._update_pushButtonCamadaDXF_state()

    def _on_layer_will_be_removed(self, layer_id: str):
        """
        Remove do tableViewCamada qualquer linha cujo ID de camada
        corresponda ao layer_id que está sendo removido do projeto.

        Também limpa o tableViewFeicao e o gráfico (scrollAreaGrafico)
        se essa era a camada selecionada.
        """
        removed_current = False

        # remove a linha do tableViewCamada (se existir)
        if hasattr(self, "tableViewCamada"):
            model = self.tableViewCamada.model()
            if model is not None:
                rows_to_remove = []
                for row in range(model.rowCount()):
                    idx = model.index(row, 0)
                    lid = idx.data(Qt.ItemDataRole.UserRole)
                    if lid == layer_id:
                        rows_to_remove.append(row)

                for row in reversed(rows_to_remove):
                    model.removeRow(row)

        # tira da lista de camadas rastreadas para CN
        if hasattr(self, "_CN_Trapezoidalcked_layers") and layer_id in self._CN_Trapezoidalcked_layers:
            self._CN_Trapezoidalcked_layers.discard(layer_id)

        # Remove o número de camada e a sequência da camada removida
        if hasattr(self, "_cn_layer_order"):
            self._cn_layer_order.pop(layer_id, None)
        if hasattr(self, "_cn_layer_seq"):
            self._cn_layer_seq.pop(layer_id, None)

        # se era a camada atualmente selecionada, limpa o tableViewFeicao e o gráfico
        if hasattr(self, "_current_canal_layer") and self._current_canal_layer is not None:
            try:
                if self._current_canal_layer.id() == layer_id:
                    removed_current = True
                    self._current_canal_layer = None
                    self._reload_tableViewFeicao_from_layer(None)
            except RuntimeError:
                removed_current = True
                self._current_canal_layer = None
                self._reload_tableViewFeicao_from_layer(None)

        if removed_current:
            if hasattr(self, "_clear_grafico_canal_terreno"):
                try:
                    self._clear_grafico_canal_terreno()
                except Exception:
                    pass  # nosec B110
            if hasattr(self, "_hide_grafico_crosshair"):
                try:
                    self._hide_grafico_crosshair()
                except Exception:
                    pass  # nosec B110

        # Mesmo que não seja a camada corrente, a seleção pode ter mudado ao remover a linha do model.
        if hasattr(self, "_update_grafico_from_selection"):
            try:
                self._update_grafico_from_selection()
            except Exception:
                pass  # nosec B110

        # Atualiza estado do checkBoxMapTool
        if hasattr(self, "_update_checkBoxMapTool_state"):
            self._update_checkBoxMapTool_state()

        # Atualiza estados dos botões depois de qualquer remoção de camada
        if hasattr(self, "_update_pushButtonCalcular_state"):
            self._update_pushButtonCalcular_state()
        if hasattr(self, "_update_pushButtonInverter_state"):
            self._update_pushButtonInverter_state()
        if hasattr(self, "_update_pushButtonCamadaDXF_state"):
            self._update_pushButtonCamadaDXF_state()
        if hasattr(self, "_update_pushButtonSalvar_state"):
            self._update_pushButtonSalvar_state()
        if hasattr(self, "_update_pushButtonGraficoDXF_state"):
            self._update_pushButtonGraficoDXF_state()

        if hasattr(self, "_reload_tableViewListaCanais_from_group"):
            try:
                self._reload_tableViewListaCanais_from_group()
            except Exception:
                pass  # nosec B110

    def _ensure_cn_layer_index(self, layer: QgsVectorLayer) -> int:
        """
        Garante que a camada tenha um número de camada (1,2,3,...)
        e devolve esse número.

        A lógica SEMPRE usa o menor inteiro positivo que ainda
        não está sendo usado por nenhuma outra camada CN.
        """
        if not isinstance(layer, QgsVectorLayer):
            return 0

        layer_id = layer.id()

        # Se já tem número de camada, só devolve
        if layer_id in self._cn_layer_order:
            return self._cn_layer_order[layer_id]

        # Calcula o menor inteiro positivo livre
        usados = set(self._cn_layer_order.values())
        idx = 1
        while idx in usados:
            idx += 1

        # Guarda o índice e inicia a sequência dessa camada (se ainda não existir)
        self._cn_layer_order[layer_id] = idx
        self._cn_layer_seq.setdefault(layer_id, 0)

        return idx

    def _reload_tableViewCamada_from_group(self):
        """
        Limpa e preenche o tableViewCamada com as camadas
        que estão dentro do grupo 'CANAIS'.
        """
        if not hasattr(self, "tableViewCamada"):
            return
        if not hasattr(self, "_camadas_model"):
            return

        model = self._camadas_model
        model.removeRows(0, model.rowCount())

        group = self._get_canais_group()
        if group is None:
            return

        for node in group.children():
            if isinstance(node, QgsLayerTreeLayer):
                lyr = node.layer()
                if lyr is None:
                    continue

                # Mostra apenas camadas de LINHA (canais)
                if not isinstance(lyr, QgsVectorLayer):
                    continue
                try:
                    if lyr.geometryType() != QgsWkbTypes.GeometryType.LineGeometry:
                        continue
                except Exception:
                    try:
                        if QgsWkbTypes.geometryType(lyr.wkbType()) != QgsWkbTypes.GeometryType.LineGeometry:
                            continue
                    except Exception:  # nosec B112
                        continue

                # Garante que essa camada tenha um número de camada (1,2,3,...)
                self._ensure_cn_layer_index(lyr)

                item = QStandardItem("    " + lyr.name())
                item.setEditable(False)
                item.setData(lyr.id(), Qt.ItemDataRole.UserRole)
                model.appendRow(item)

        # Seleciona a primeira linha se houver
        if model.rowCount() > 0:
            idx = model.index(0, 0)
            self.tableViewCamada.setCurrentIndex(idx)

        # Atualiza estado do checkBoxMapTool
        if hasattr(self, "_update_checkBoxMapTool_state"):
            self._update_checkBoxMapTool_state()

        # no fim do _reload_tableViewCamada_from_group()
        if hasattr(self, "_update_pushButtonCamadaDXF_state"):
            self._update_pushButtonCamadaDXF_state()

        if hasattr(self, "_update_pushButtonSalvar_state"):
            self._update_pushButtonSalvar_state()

        if hasattr(self, "_reload_tableViewListaCanais_from_group"):
            self._reload_tableViewListaCanais_from_group()

    def _on_canal_feature_added(self, fid: int):
        """
        Sempre que uma nova feição é criada em qualquer camada de canais,
        preenche automaticamente o campo CN, evitando buracos na numeração.
        """
        layer = self.sender()
        if not isinstance(layer, QgsVectorLayer):
            return

        layer_id = layer.id()

        # Garante que a camada tenha um índice fixo (1, 2, 3, ...)
        camada_idx = self._ensure_cn_layer_index(layer)

        # Obtém o índice do campo CN (cria se não existir)
        idx_cn = layer.fields().indexOf("CN")
        if idx_cn < 0:
            prov = layer.dataProvider()
            prov.addAttributes([QgsField("CN", QMetaType.Type.QString, "string", 50)])
            layer.updateFields()
            idx_cn = layer.fields().indexOf("CN")
            if idx_cn < 0:
                return

        # Localiza o menor número de sequência livre dentro desta camada
        existentes = set()
        for feat in layer.getFeatures():
            val = feat.attribute(idx_cn)
            if val and isinstance(val, str) and val.startswith(f"CN.{camada_idx}."):
                try:
                    seq_str = val.split(".")[2]
                    existentes.add(int(seq_str))
                except (IndexError, ValueError):
                    pass  # nosec B110

        seq = 1
        while seq in existentes:
            seq += 1

        cn_value = f"CN.{camada_idx}.{seq}"

        # Aplica o valor ao atributo CN da nova feição
        layer.changeAttributeValue(fid, idx_cn, cn_value)

        # Atualiza Compr_Canal e Declividade(I) automaticamente
        self._update_canal_medidas(layer, fid)

        # Atualiza controle de sequência local (mantém o maior usado)
        self._cn_layer_seq[layer_id] = max(self._cn_layer_seq.get(layer_id, 0), seq)

        # Atualiza tabela se esta camada estiver selecionada
        if hasattr(self, "_current_canal_layer") and layer == self._current_canal_layer:
            self._reload_tableViewFeicao_from_layer(layer)
            # Seleciona a nova feição no tableViewFeicao
            self._select_feicao_row_by_fid(fid)

        # Atualiza a aba PROJETO (lista + gráfico)
        if hasattr(self, "_refresh_projeto_views"):
            self._refresh_projeto_views(layer)

        if hasattr(self, "_update_pushButtonCamadaDXF_state"):
            self._update_pushButtonCamadaDXF_state()

    def _register_cn_layer(self, layer: QgsVectorLayer):
        """
        Conecta sinais de adição/remoção de feições para preencher CN
        e atualizar o tableViewFeicao. Evita registrar a mesma camada duas vezes.
        """
        if not isinstance(layer, QgsVectorLayer):
            return

        if layer.id() in self._CN_Trapezoidalcked_layers:
            return

        if layer.geometryType() != QgsWkbTypes.GeometryType.LineGeometry:
            return

        layer.featureAdded.connect(self._on_canal_feature_added)
        layer.geometryChanged.connect(self._on_canal_geometry_changed)
        layer.featuresDeleted.connect(self._on_canal_features_deleted)

        self._CN_Trapezoidalcked_layers.add(layer.id())

    def _update_canais_dados(self):
        """
        Atualiza os campos dentro do scrollAreaDados de acordo
        com o tipo selecionado em comboBoxCanais.
        """
        if not hasattr(self, "scrollAreaDados"):
            return

        container = self.scrollAreaDados.widget()
        if container is None:
            return

        layout = container.layout()
        if layout is None:
            layout = QFormLayout(container)
            container.setLayout(layout)

        # Limpa qualquer coisa que já estiver no layout
        self._clear_layout(layout)

        # Limpa referências antigas de spins para evitar apontar para widgets já deletados
        spin_attrs = [
            "spinYn",
            "spinDeclividade",
            "spinFolga",
            "spinCompCanal",
            "spinTaludeZ",
            "spinBaseB",
            "spinDiametro",
            "spinDiametroExt",
            "spinFolgaLat",
            "spinBercoEsp",
            "spinCobertura",
            "spinTaludeVala"]

        for name in spin_attrs:
            if hasattr(self, name):
                delattr(self, name)

        # Tipo de canal selecionado no combo
        tipo = self.comboBoxCanais.currentData() if hasattr(self, "comboBoxCanais") else None

        # Definição base de campos (config comum)
        campos_base = [
            {"attr_name": "spinYn",
                "label": self.tr("Profundidade Normal (Yn):"),
                "decimals": 3,
                "vmin": 0.0,
                "vmax": 1000.0,
                "step": 0.01,
                "suffix": self.tr(" m")},
            {"attr_name": "spinDeclividade",
                "label": self.tr("Declividade (I):"),
                "decimals": 3,
                "vmin": -100.0,
                "vmax": 100.0,
                "step": 0.001,
                "suffix": self.tr(" %")}]

        campos_folga = [
            {"attr_name": "spinFolga",
                "label": self.tr("Folga (f):"),
                "decimals": 3,
                "vmin": 0.0,
                "vmax": 10.0,
                "step": 0.01,
                "suffix": self.tr(" m")}]

        campos_comp = [
            {"attr_name": "spinCompCanal",
                "label": self.tr("Comprimento do Canal:"),
                "decimals": 3,
                "vmin": 0.0,
                "vmax": 100000.0,
                "step": 0.1,
                "suffix": self.tr(" m")}]

        # Campos extras por tipo
        if tipo == "triangular":
            campos_tipo = (
                campos_base
                + campos_folga
                + campos_comp
                + [{"attr_name": "spinTaludeZ",
                        "label": self.tr("Inclinação do Talude do canal (z):"),
                        "decimals": 3,
                        "vmin": 0.0,
                        "vmax": 10.0,
                        "step": 0.01,
                        "suffix": ""}])

        elif tipo == "trapezoidal":
            campos_tipo = (
                campos_base
                + campos_folga
                + campos_comp
                + [{"attr_name": "spinTaludeZ",
                        "label": self.tr("Inclinação do Talude (z):"),
                        "decimals": 3,
                        "vmin": 0.0,
                        "vmax": 10.0,
                        "step": 0.01,
                        "suffix": ""},
                    {"attr_name": "spinBaseB",
                        "label": self.tr("Largura da Base (b):"),
                        "decimals": 3,
                        "vmin": 0.0,
                        "vmax": 1000.0,
                        "step": 0.01,
                        "suffix": self.tr(" m")}])

        elif tipo == "retangular":
            campos_tipo = (
                campos_base
                + campos_folga
                + campos_comp
                + [{"attr_name": "spinBaseB",
                        "label": self.tr("Largura da Base (b):"),
                        "decimals": 3,
                        "vmin": 0.0,
                        "vmax": 1000.0,
                        "step": 0.01,
                        "suffix": self.tr(" m")}])

        elif tipo == "circular":
            campos_tipo = (
                campos_base
                + campos_comp
                + [
                    {"attr_name": "spinDiametro",
                        "label": self.tr("Diâmetro interno (D):"),
                        "decimals": 3,
                        "vmin": 0.0,
                        "vmax": 10.0,
                        "step": 0.01,
                        "suffix": self.tr(" m")},

                    {"attr_name": "spinDiametroExt",
                        "label": self.tr("Diâmetro externo:"),
                        "decimals": 3,
                        "vmin": 0.0,
                        "vmax": 10.0,
                        "step": 0.01,
                        "suffix": self.tr(" m")},

                    {"attr_name": "spinFolgaLat",
                        "label": self.tr("Folga lateral:"),
                        "decimals": 3,
                        "vmin": 0.0,
                        "vmax": 5.0,
                        "step": 0.01,
                        "suffix": self.tr(" m")},

                    {"attr_name": "spinBercoEsp",
                        "label": self.tr("Espessura do berço:"),
                        "decimals": 3,
                        "vmin": 0.0,
                        "vmax": 5.0,
                        "step": 0.01,
                        "suffix": self.tr(" m")},

                    {"attr_name": "spinCobertura",
                        "label": self.tr("Cobertura acima do tubo:"),
                        "decimals": 3,
                        "vmin": 0.0,
                        "vmax": 20.0,
                        "step": 0.01,
                        "suffix": self.tr(" m")},

                    {"attr_name": "spinTaludeVala",
                        "label": self.tr("Talude da vala (z):"),
                        "decimals": 3,
                        "vmin": 0.0,
                        "vmax": 10.0,
                        "step": 0.01,
                        "suffix": ""}])
        else:
            layout.addRow(QLabel(self.tr("Configure os parâmetros para o tipo de canal selecionado."), container))
            self._update_graphics_tipo(tipo)
            return

        # Cria os campos definidos para o tipo selecionado
        for cfg in campos_tipo:
            spin = self._add_spin_field(container, layout, **cfg)

            # Declividade e Comprimento do Canal são calculados -> somente leitura
            if cfg["attr_name"] in ("spinDeclividade", "spinCompCanal"):
                spin.setReadOnly(True)
                spin.setButtonSymbols(QAbstractSpinBox.ButtonSymbols.NoButtons)
                spin.setFocusPolicy(Qt.FocusPolicy.NoFocus)

            # Talude Z com valor padrão 1.0
            if cfg["attr_name"] == "spinTaludeZ":
                spin.blockSignals(True)
                spin.setValue(1.0)
                spin.blockSignals(False)

            if cfg["attr_name"] == "spinFolgaLat":
                spin.blockSignals(True)
                spin.setValue(0.15)
                spin.blockSignals(False)

            if cfg["attr_name"] == "spinBercoEsp":
                spin.blockSignals(True)
                spin.setValue(0.10)
                spin.blockSignals(False)

            if cfg["attr_name"] == "spinCobertura":
                spin.blockSignals(True)
                spin.setValue(0.30)
                spin.blockSignals(False)

            if cfg["attr_name"] == "spinTaludeVala":
                spin.blockSignals(True)
                spin.setValue(0.0)
                spin.blockSignals(False)

            if cfg["attr_name"] in ("spinYn", "spinDiametro"):
                try:
                    spin.valueChanged.disconnect(self._redraw_tipo_canal_preview)
                except Exception:
                    pass  # nosec B110
                spin.valueChanged.connect(self._redraw_tipo_canal_preview)

            if cfg["attr_name"] in (
                "spinYn",
                "spinDiametro",
                "spinDiametroExt",
                "spinFolgaLat",
                "spinBercoEsp",
                "spinCobertura",
                "spinTaludeVala"):
                try:
                    spin.valueChanged.disconnect(self._on_circular_inputs_changed)
                except Exception:
                    pass  # nosec B110
                spin.valueChanged.connect(self._on_circular_inputs_changed)

            if cfg["attr_name"] == "spinDiametro":
                spin.blockSignals(True)
                if spin.value() <= 0.0:
                    spin.setValue(1.0)
                spin.blockSignals(False)

            if cfg["attr_name"] == "spinDiametroExt":
                spin.blockSignals(True)
                if spin.value() <= 0.0:
                    spin.setValue(1.0)
                spin.blockSignals(False)

        # Depois de recriar os campos, sincroniza com a feição selecionada
        fid_sel = None
        if hasattr(self, "tableViewFeicao"):
            idx_sel = self.tableViewFeicao.currentIndex()
            if idx_sel.isValid():
                fid_sel = idx_sel.data(Qt.ItemDataRole.UserRole)

        if hasattr(self, "_populate_canais_medidas_from_layer"):
            self._populate_canais_medidas_from_layer(fid=fid_sel)

        # Conecta atualização de cor do spinDeclividade
        if hasattr(self, "spinDeclividade"):
            try:
                self.spinDeclividade.valueChanged.disconnect(self._on_spinDeclividade_value_changed)
            except Exception:
                pass  # nosec B110
            self.spinDeclividade.valueChanged.connect(self._on_spinDeclividade_value_changed)

        # Atualiza o desenho do graphicsViewTipo
        self._update_graphics_tipo(tipo)

        if tipo == "circular":
            self._apply_circular_constraints_ui()

    def _redraw_tipo_canal_preview(self, *args):
        tipo = ""
        if hasattr(self, "comboBoxCanais") and self.comboBoxCanais is not None:
            try:
                tipo = self.comboBoxCanais.currentData() or ""
            except Exception:
                tipo = ""
        self._update_graphics_tipo(tipo)

    def _get_spin_float(self, name: str, default=None):
        w = getattr(self, name, None)
        if w is None:
            return default
        try:
            return float(w.value())
        except Exception:
            return default

    def _validate_circular_inputs(self):
        """
        Valida coerência dos campos do tipo circular.
        Retorna: (ok: bool, msg: str)
        """
        D = self._get_spin_float("spinDiametro", 0.0)
        y = self._get_spin_float("spinYn", 0.0)
        Dext = self._get_spin_float("spinDiametroExt", 0.0)
        flat = self._get_spin_float("spinFolgaLat", 0.0)
        berco = self._get_spin_float("spinBercoEsp", 0.0)
        cob = self._get_spin_float("spinCobertura", 0.0)
        zvala = self._get_spin_float("spinTaludeVala", 0.0)

        n_val = None
        if hasattr(self, "lineEditRugosidade") and self.lineEditRugosidade is not None:
            txt = self.lineEditRugosidade.text().strip().replace(",", ".")
            if txt:
                try:
                    n_val = float(txt)
                except Exception:
                    n_val = None

        if D is None or D <= 0.0:
            return False, self.tr("O diâmetro interno (D) deve ser maior que zero.")

        if y is None or y < 0.0:
            return False, self.tr("A profundidade normal (Yn) não pode ser negativa.")

        if y > D:
            return False, self.tr("A profundidade normal (Yn) não pode ser maior que o diâmetro interno (D).")

        if Dext is None or Dext <= 0.0:
            return False, self.tr("O diâmetro externo deve ser maior que zero.")

        if Dext < D:
            return False, self.tr("O diâmetro externo deve ser maior ou igual ao diâmetro interno.")

        if flat is not None and flat < 0.0:
            return False, self.tr("A folga lateral não pode ser negativa.")

        if berco is not None and berco < 0.0:
            return False, self.tr("A espessura do berço não pode ser negativa.")

        if cob is not None and cob < 0.0:
            return False, self.tr("A cobertura acima do tubo não pode ser negativa.")

        if zvala is not None and zvala < 0.0:
            return False, self.tr("O talude da vala (z) não pode ser negativo.")

        if n_val is None or n_val <= 0.0:
            return False, self.tr("O coeficiente de rugosidade (n) deve ser maior que zero.")

        return True, ""

    def _apply_circular_constraints_ui(self):
        """
        Ajusta apenas dicas visuais do tipo circular,
        sem alterar silenciosamente os valores digitados.
        """
        if not hasattr(self, "spinDiametro") or not hasattr(self, "spinYn"):
            return

        ok, msg = self._validate_circular_inputs()

        # tooltip informativo, sem travar o fluxo
        try:
            if ok:
                self.spinYn.setToolTip("")
                if hasattr(self, "spinDiametroExt") and self.spinDiametroExt is not None:
                    self.spinDiametroExt.setToolTip("")
            else:
                self.spinYn.setToolTip(msg)
                if hasattr(self, "spinDiametroExt") and self.spinDiametroExt is not None:
                    self.spinDiametroExt.setToolTip(msg)
        except Exception:
            pass  # nosec B110

    def _on_circular_inputs_changed(self, *args):
        """
        Reaplica restrições e atualiza o estado do botão calcular.
        """
        self._apply_circular_constraints_ui()
        if hasattr(self, "_update_pushButtonCalcular_state"):
            self._update_pushButtonCalcular_state()

    def _blink_invalid_circular_inputs(self):
        """
        Pisca os widgets do tipo circular que estiverem incoerentes.
        """
        D = self._get_spin_float("spinDiametro", 0.0)
        y = self._get_spin_float("spinYn", 0.0)
        Dext = self._get_spin_float("spinDiametroExt", 0.0)
        flat = self._get_spin_float("spinFolgaLat", 0.0)
        berco = self._get_spin_float("spinBercoEsp", 0.0)
        cob = self._get_spin_float("spinCobertura", 0.0)
        zvala = self._get_spin_float("spinTaludeVala", 0.0)

        n_val = None
        line_n = getattr(self, "lineEditRugosidade", None)
        if line_n is not None:
            txt = line_n.text().strip().replace(",", ".")
            if txt:
                try:
                    n_val = float(txt)
                except Exception:
                    n_val = None

        if D is None or D <= 0.0:
            if hasattr(self, "spinDiametro"):
                self._blink_widget_red(self.spinDiametro)

        if y is None or y < 0.0:
            if hasattr(self, "spinYn"):
                self._blink_widget_red(self.spinYn)

        if y is not None and D is not None and y > D:
            if hasattr(self, "spinYn"):
                self._blink_widget_red(self.spinYn)
            if hasattr(self, "spinDiametro"):
                self._blink_widget_red(self.spinDiametro)

        if Dext is None or Dext <= 0.0:
            if hasattr(self, "spinDiametroExt"):
                self._blink_widget_red(self.spinDiametroExt)

        if Dext is not None and D is not None and Dext < D:
            if hasattr(self, "spinDiametroExt"):
                self._blink_widget_red(self.spinDiametroExt)
            if hasattr(self, "spinDiametro"):
                self._blink_widget_red(self.spinDiametro)

        if flat is not None and flat < 0.0:
            if hasattr(self, "spinFolgaLat"):
                self._blink_widget_red(self.spinFolgaLat)

        if berco is not None and berco < 0.0:
            if hasattr(self, "spinBercoEsp"):
                self._blink_widget_red(self.spinBercoEsp)

        if cob is not None and cob < 0.0:
            if hasattr(self, "spinCobertura"):
                self._blink_widget_red(self.spinCobertura)

        if zvala is not None and zvala < 0.0:
            if hasattr(self, "spinTaludeVala"):
                self._blink_widget_red(self.spinTaludeVala)

        if n_val is None or n_val <= 0.0:
            if hasattr(self, "lineEditRugosidade") and self.lineEditRugosidade is not None:
                self._blink_widget_red(self.lineEditRugosidade)

    def _get_canal_tipo_for_layer(self, layer) -> str:
        """
        Retorna o tipo de canal ('triangular', 'trapezoidal',
        'retangular', 'circular') associado à camada.
        Primeiro tenta uma propriedade customizada; se não existir,
        tenta inferir pelo prefixo do nome da camada (CN_Triangular, CN_Trapezoidal, etc.).
        """
        if not isinstance(layer, QgsVectorLayer):
            return ""

        # 1) Propriedade customizada (mais confiável)
        tipo = layer.customProperty("rd_tipo_canal", "")
        if tipo:
            return str(tipo)

        # 2) Fallback: inferir pelo nome
        name = layer.name()
        if name.startswith("CN_Triangular"):
            return "triangular"
        if name.startswith("CN_Trapezoidal"):
            return "trapezoidal"
        if name.startswith("CN_Retangular"):
            return "retangular"
        if name.startswith("CN_Circular"):
            return "circular"

        return ""

    def _reset_canais_dados_fields(self):
        """
        Reseta os campos do scrollAreaDados para o estado inicial
        (usado quando não há feição selecionada ou tipo não bate).
        """
        if hasattr(self, "spinCompCanal"):
            self.spinCompCanal.blockSignals(True)
            self.spinCompCanal.setValue(0.0)
            self.spinCompCanal.blockSignals(False)

        if hasattr(self, "spinDeclividade"):
            self.spinDeclividade.blockSignals(True)
            self.spinDeclividade.setValue(0.0)
            self.spinDeclividade.blockSignals(False)
            self._on_spinDeclividade_value_changed(0.0) # Volta a cor padrão (0.0 é não-negativo)

        for name in (
            "spinDiametroExt",
            "spinFolgaLat",
            "spinBercoEsp",
            "spinCobertura",
            "spinTaludeVala"):
            w = getattr(self, name, None)
            if w is not None:
                try:
                    w.blockSignals(True)
                    w.setValue(0.0)
                    w.blockSignals(False)
                except Exception:
                    pass  # nosec B110

    def _select_feicao_row_by_fid(self, fid: int):
        """
        Seleciona no tableViewFeicao a linha correspondente ao fid informado.
        Usado após criar uma nova feição, desde que a camada esteja selecionada
        no tableViewCamada.
        """
        if not hasattr(self, "tableViewFeicao"):
            return
        if not hasattr(self, "_feicao_model") or self._feicao_model is None:
            return

        model = self._feicao_model
        sel_model = self.tableViewFeicao.selectionModel()
        if sel_model is None:
            return

        for row in range(model.rowCount()):
            idx = model.index(row, 0)
            fid_row = idx.data(Qt.ItemDataRole.UserRole)
            if fid_row == fid:
                # Define a linha como selecionada e corrente
                self.tableViewFeicao.setCurrentIndex(idx)
                self.tableViewFeicao.selectRow(row)
                self.tableViewFeicao.scrollTo(idx)
                break

    def _select_camada_row_by_layer_id(self, layer_id: str):
        """
        Seleciona no tableViewCamada a linha que representa a camada
        com o ID informado e atualiza a camada corrente.
        Também espelha a seleção no tableViewListaCanais.
        """
        if not hasattr(self, "tableViewCamada") or not hasattr(self, "_camadas_model"):
            return

        model = self._camadas_model
        sel_model = self.tableViewCamada.selectionModel()
        if sel_model is None:
            return

        for row in range(model.rowCount()):
            idx = model.index(row, 0)
            lid = idx.data(Qt.ItemDataRole.UserRole)
            if lid == layer_id:
                self.tableViewCamada.setCurrentIndex(idx)
                self.tableViewCamada.selectRow(row)
                self.tableViewCamada.scrollTo(idx)
                break

        if hasattr(self, "_sync_tableViewListaCanais_with_layer_id"):
            self._sync_tableViewListaCanais_with_layer_id(layer_id)

    def _update_canal_medidas(self, layer, fid: int, geom=None):
        """
        Atualiza automaticamente:
          - Compr_Canal: comprimento da linha (unidades do SRC)
          - Declividade(I): ((Z_início - Z_fim) / comprimento) * 100  [%]

        Usa o raster atualmente selecionado no comboBoxRaster.
        Se a linha (ou parte) estiver fora da extensão do raster,
        Declividade(I) = 0.
        """
        if not isinstance(layer, QgsVectorLayer):
            return

        # Garante geometria atual
        if geom is None:
            try:
                feat = layer.getFeature(fid)
            except Exception:
                return
            if not feat.isValid():
                return
            geom = feat.geometry()

        if geom is None or geom.isEmpty():
            return

        # Garante que os campos existam
        prov = layer.dataProvider()
        fields = layer.fields()
        novos_campos = []

        if fields.indexOf("Compr_Canal") == -1:
            novos_campos.append(QgsField("Compr_Canal", QMetaType.Type.Double, "double", 20, 3))
        if fields.indexOf("Declividade(I)") == -1:
            novos_campos.append(QgsField("Declividade(I)", QMetaType.Type.Double, "double", 20, 3))

        if novos_campos:
            prov.addAttributes(novos_campos)
            layer.updateFields()
            fields = layer.fields()

        idx_len = fields.indexOf("Compr_Canal")
        idx_decl = fields.indexOf("Declividade(I)")
        if idx_len < 0 and idx_decl < 0:
            return

        # Comprimento
        length = geom.length() or 0.0
        if idx_len >= 0:
            layer.changeAttributeValue(fid, idx_len, round(length, 3))

        # Declividade em %
        declividade = 0.0

        raster = self._get_selected_raster_from_combo()
        if (
            raster is not None
            and raster.isValid()
            and length > 0
            and geom.type() == QgsWkbTypes.GeometryType.LineGeometry):
            rprov = raster.dataProvider()
            extent = raster.extent()
            bbox = geom.boundingBox()

            if extent.contains(bbox):
                # Pega primeira e última coordenada da linha
                if geom.isMultipart():
                    linhas = geom.asMultiPolyline()
                    linha = linhas[0] if linhas else []
                else:
                    linha = geom.asPolyline()

                if len(linha) >= 2:
                    p1 = linha[0]
                    p2 = linha[-1]

                    # sample() pode retornar float ou (valor, ok) dependendo da versão do QGIS
                    res1 = rprov.sample(QgsPointXY(p1.x(), p1.y()), 1)
                    res2 = rprov.sample(QgsPointXY(p2.x(), p2.y()), 1)

                    if isinstance(res1, tuple):
                        z1, ok1 = res1
                    else:
                        z1, ok1 = res1, (res1 is not None)

                    if isinstance(res2, tuple):
                        z2, ok2 = res2
                    else:
                        z2, ok2 = res2, (res2 is not None)

                    if ok1 and ok2 and z1 is not None and z2 is not None:
                        # se quiser sempre positiva, troque por: abs((z1 - z2) / length) * 100.0
                        declividade = ((z1 - z2) / length) * 100.0

        if idx_decl >= 0:
            layer.changeAttributeValue(fid, idx_decl, round(declividade, 3))

    def _on_canal_geometry_changed(self, fid, geom):
        """
        Atualiza medidas quando a geometria de uma feição é editada.
        Se a feição estava selecionada no tableViewFeicao, mantém
        a seleção e atualiza o painel de dados.
        """
        layer = self.sender()
        if not isinstance(layer, QgsVectorLayer):
            return

        # Recalcula comprimento e declividade
        self._update_canal_medidas(layer, fid, geom)

        # Atualiza gráfico de perfil para esta feição
        try:
            self._update_grafico_canal_terreno(layer=layer, fid=fid)
        except Exception:
            pass  # nosec B110

        if hasattr(self, "_current_canal_layer") and layer == self._current_canal_layer:
            keep_selected = False

            # Verifica se essa feição estava selecionada ANTES do reload
            if hasattr(self, "tableViewFeicao"):
                sel = self.tableViewFeicao.selectionModel()
                if sel:
                    current = sel.currentIndex()
                    if current.isValid() and current.data(Qt.ItemDataRole.UserRole) == fid:
                        keep_selected = True

            # Recarrega a tabela de feições
            self._reload_tableViewFeicao_from_layer(layer)

        # Atualiza também a aba PROJETO
        if hasattr(self, "_refresh_projeto_views"):
            self._refresh_projeto_views(layer)

            # Se ela estava selecionada, reseleciona e atualiza painel
            if keep_selected:
                self._select_feicao_row_by_fid(fid)
                self._populate_canais_medidas_from_layer(fid=fid)

    def _init_scrollAreaResultado(self):
        """
        Configura o scrollAreaResultado com os campos de resultados hidráulicos,
        usando QLineEdit e as unidades em labels à direita.
        """
        if not hasattr(self, "scrollAreaResultado"):
            return

        container = self.scrollAreaResultado.widget()
        if container is None:
            container = QWidget(self.scrollAreaResultado)
            self.scrollAreaResultado.setWidget(container)

        layout = container.layout()
        if layout is None or not isinstance(layout, QFormLayout):
            layout = QFormLayout(container)
            container.setLayout(layout)

        # ajustes de alinhamento/espacamento
        layout.setLabelAlignment(Qt.AlignmentFlag.AlignRight | Qt.AlignmentFlag.AlignVCenter)
        layout.setFormAlignment(Qt.AlignmentFlag.AlignLeft | Qt.AlignmentFlag.AlignTop)
        layout.setContentsMargins(4, 4, 4, 4)
        layout.setHorizontalSpacing(8)
        layout.setVerticalSpacing(4)

        # limpa o layout
        self._clear_layout(layout)

        # (attr_name, label à esquerda, unidade à direita)
        campos = [
            ("lineAreaA", self.tr("Área (A):"), self.tr("m²")),
            ("lineVazaoQ", self.tr("Vazão (Q):"), self.tr("m³/s")),
            ("linePerimetroP", self.tr("Perímetro Molhado (P):"), self.tr("m")),
            ("lineLarguraB", self.tr("Largura da Superfície (B):"), self.tr("m")),
            ("lineProfCriticaYc", self.tr("Profundidade Crítica (Yc):"), self.tr("m")),
            ("lineFroudeFr", self.tr("Número de Froude (Fr):"), ""),
            ("lineRegimeEscoamento", self.tr("Regime de Escoamento:"), ""),
            ("lineVelocidadeV", self.tr("Velocidade (V):"), self.tr("m/s")),
            ("lineEnergiaE", self.tr("Energia Específica (E):"), self.tr("m")),
            ("lineMovTerra", self.tr("Movimentação de Terra:"), self.tr("m³"))]

        # largura fixa para todos os lineEdits (ajuste se quiser mais largo/estreito)
        fixed_width = 80

        for attr_name, label_txt, unidade in campos:
            # line edit (só leitura – resultado calculado)
            line = QLineEdit(container)
            line.setObjectName(attr_name)
            line.setReadOnly(True)
            line.setAlignment(Qt.AlignmentFlag.AlignRight | Qt.AlignmentFlag.AlignVCenter)
            line.setFixedWidth(fixed_width)          # <<< todos com a mesma largura

            # guarda como atributo da classe (self.lineAreaA, etc.)
            setattr(self, attr_name, line)

            # widget da direita com lineedit + unidade
            row_widget = QWidget(container)
            h = QHBoxLayout(row_widget)
            h.setContentsMargins(0, 0, 0, 0)
            h.setSpacing(4)
            h.setAlignment(Qt.AlignmentFlag.AlignLeft | Qt.AlignmentFlag.AlignVCenter)
            h.addWidget(line)
            if unidade:
                lbl_unit = QLabel(unidade, row_widget)
                h.addWidget(lbl_unit)

            # label à esquerda
            lbl = QLabel(label_txt, container)
            lbl.setAlignment(Qt.AlignmentFlag.AlignRight | Qt.AlignmentFlag.AlignVCenter)

            layout.addRow(lbl, row_widget)

    def _ensure_canais_group(self) -> QgsLayerTreeGroup:
        """
        Garante que o grupo 'CANAIS' exista.
        Quando criado, ele é inserido no topo da árvore de camadas.
        """
        root = QgsProject.instance().layerTreeRoot()
        group = root.findGroup(self.tr("CANAIS"))
        if group is None:
            # cria o grupo na posição 0 (topo)
            group = root.insertGroup(0, self.tr("CANAIS"))
        return group

    def _sync_combo_canais_with_layer(self, layer):
        """
        Sincroniza o comboBoxCanais com o tipo da camada informada
        (triangular, trapezoidal, retangular, circular).

        Não faz nada se o combo não existir ou se o tipo da camada
        não puder ser determinado.
        """
        if not hasattr(self, "comboBoxCanais") or self.comboBoxCanais is None:
            return
        if layer is None:
            return

        tipo_layer = self._get_canal_tipo_for_layer(layer)
        if not tipo_layer:
            return

        # Procura no combo a opção cujo .itemData(i) == tipo_layer
        for i in range(self.comboBoxCanais.count()):
            if self.comboBoxCanais.itemData(i) == tipo_layer:
                if self.comboBoxCanais.currentIndex() != i:
                    # mudar o índice dispara o currentIndexChanged,
                    # atualizando o scrollAreaDados normalmente
                    self.comboBoxCanais.setCurrentIndex(i)
                break

    def _on_camada_row_changed(self, current: QModelIndex, previous: QModelIndex):
        """
        Quando o usuário troca a linha no tableViewCamada,
        mudamos a camada corrente, recarregamos o tableViewFeicao
        e sincronizamos com o painel de Camadas do QGIS.
        """
        if not current.isValid():
            self._current_canal_layer = None
            self._reload_tableViewFeicao_from_layer(None)
            return

        layer_id = current.data(Qt.ItemDataRole.UserRole)
        if not layer_id:
            self._current_canal_layer = None
            self._reload_tableViewFeicao_from_layer(None)
            return

        lyr = QgsProject.instance().mapLayer(layer_id)
        if not isinstance(lyr, QgsVectorLayer):
            self._current_canal_layer = None
            self._reload_tableViewFeicao_from_layer(None)
            return

        # Evita recursão com o handler do currentLayerChanged
        self._syncing_layer_selection = True
        try:
            # Define camada corrente interna
            self._current_canal_layer = lyr

            # Garante que o painel de Camadas use a mesma camada
            try:
                self.iface.setActiveLayer(lyr)
            except Exception:
                pass  # nosec B110

            # Recarrega tabela de feições dessa camada
            self._reload_tableViewFeicao_from_layer(lyr)

            # Sincroniza comboBoxCanais com o tipo desta camada
            self._sync_combo_canais_with_layer(lyr)
        finally:
            self._syncing_layer_selection = False

        # Tenta atualizar o gráfico para a feição atualmente selecionada
        if hasattr(self, "_update_grafico_from_selection"):
            self._update_grafico_from_selection()
        if hasattr(self, "_update_pushButtonCamadaDXF_state"):
            self._update_pushButtonCamadaDXF_state()

        if hasattr(self, "_update_grafico_projeto_from_current_layer"):
            self._update_grafico_projeto_from_current_layer()

        # Atualiza também a aba PROJETO
        if hasattr(self, "_refresh_projeto_views"):
            self._refresh_projeto_views(lyr)

        if hasattr(self, "_sync_tableViewListaCanais_with_layer_id"):
            try:
                self._sync_tableViewListaCanais_with_layer_id(lyr.id())
            except Exception:
                pass  # nosec B110

    def _connect_layer_sync(self):
        """
        Conecta o sinal currentLayerChanged do QGIS para manter
        o tableViewCamada em sincronia com o painel de Camadas.
        """
        if getattr(self, "_layer_sync_connected", False):
            return

        try:
            self.iface.currentLayerChanged.connect(self._on_qgis_current_layer_changed)
            self._layer_sync_connected = True
        except Exception:
            self._layer_sync_connected = False

    def _disconnect_layer_sync(self):
        """
        Desconecta a sincronização com o painel de Camadas.
        Chamado quando o dock é fechado.
        """
        if not getattr(self, "_layer_sync_connected", False):
            return

        try:
            self.iface.currentLayerChanged.disconnect(self._on_qgis_current_layer_changed)
        except Exception:
            pass  # nosec B110

        self._layer_sync_connected = False

    def _init_pushButtonCalcular(self):
        if hasattr(self, "pushButtonCalcular") and self.pushButtonCalcular is not None:
            self.pushButtonCalcular.clicked.connect(self._on_pushButtonCalcular_clicked)

    def _calc_area_perimetro_canal(self, tipo: str, y: float, z: float, b: float, D: float):
        """
        Calcula:
          - A: área molhada [m²]
          - P: perímetro molhado [m]
          - B: largura da superfície livre (topo) [m]

        em função do tipo de canal e da profundidade y.

        tipo: 'triangular', 'trapezoidal', 'retangular', 'circular'
        y   : profundidade [m]
        z   : inclinação do talude (horizontal:vertical)
        b   : largura da base [m]
        D   : diâmetro [m] (canal circular)
        """
        A = 0.0
        P = 0.0
        B = 0.0

        y = max(0.0, float(y))
        z = max(0.0, float(z))
        b = max(0.0, float(b))
        D = max(0.0, float(D))

        # Triangular (b = 0, taludes z:1)
        if tipo == "triangular":
            if y > 0.0 and z > 0.0:
                A = z * y * y                       # A = z y²
                P = 2.0 * y * math.hypot(1.0, z)   # 2 y √(1+z²)
                B = 2.0 * z * y                    # largura da superfície

        # Trapezoidal
        elif tipo == "trapezoidal":
            if y > 0.0:
                A = (b + z * y) * y                # A = (b + z y) y
                P = b + 2.0 * y * math.hypot(1.0, z)
                B = b + 2.0 * z * y

        # Retangular
        elif tipo == "retangular":
            if y > 0.0 and b > 0.0:
                A = b * y
                P = b + 2.0 * y
                B = b

        # Circular (aberto, profundidade y a partir do fundo)
        elif tipo == "circular":
            if D > 0.0 and y > 0.0:
                R = D / 2.0
                # profundidade não pode passar do diâmetro
                y = min(y, 2.0 * R)

                # ângulo central θ (rad) do trecho molhado
                cos_arg = (R - y) / R
                cos_arg = max(-1.0, min(1.0, cos_arg))
                theta = 2.0 * math.acos(cos_arg)

                # área do segmento circular
                A = 0.5 * R * R * (theta - math.sin(theta))
                # perímetro molhado
                P = R * theta
                # largura da superfície livre (corda)
                B = 2.0 * R * math.sin(theta / 2.0)

        return A, P, B

    def _calc_critical_depth(self, tipo: str, Q: float, z: float, b: float, D: float, y_ref: float = 1.0) -> float:
        """
        Calcula profundidade crítica (Yc) por iteração, a partir da
        condição geral de escoamento crítico:

            Q² * T / (g * A³) = 1

        onde T = B (largura da superfície), A = área molhada.

        Usa método da bisseção com base na geometria do canal.
        """
        g = 9.81
        if Q <= 0.0:
            return 0.0

        # função F(y) = Q² T / (g A³) - 1
        def f(y):
            A, _, B = self._calc_area_perimetro_canal(tipo, y, z, b, D)
            if A <= 0.0 or B <= 0.0:
                return -1.0
            return (Q * Q * B) / (g * A * A * A) - 1.0

        # limites de busca
        y_min = 1e-4
        y_max = max(2.0 * y_ref, 0.5)

        # limite físico para canal circular
        if tipo == "circular" and D > 0.0:
            y_max = min(y_max, D)

        f_min = f(y_min)
        f_max = f(y_max)

        # se não há troca de sinal, tenta expandir y_max algumas vezes
        it = 0
        while f_min * f_max > 0.0 and it < 15:
            y_max *= 2.0
            if tipo == "circular" and D > 0.0:
                y_max = min(y_max, D)
            f_max = f(y_max)
            it += 1

        # ainda sem troca de sinal → desiste
        if f_min * f_max > 0.0:
            return 0.0

        # bisseção
        for _ in range(30):
            y_mid = 0.5 * (y_min + y_max)
            f_mid = f(y_mid)

            if f_min * f_mid <= 0.0:
                y_max = y_mid
                f_max = f_mid
            else:
                y_min = y_mid
                f_min = f_mid

        return 0.5 * (y_min + y_max)

    def _on_pushButtonCalcular_clicked(self):
        """
        Lê dados em scrollAreaDados + lineEditRugosidade,
        calcula resultados hidráulicos básicos:

          - Área (A)
          - Perímetro Molhado (P)
          - Largura da Superfície (B)
          - Vazão (Q)   [Manning]
          - Profundidade Crítica (Yc)
          - Velocidade (V)
          - Número de Froude (Fr)
          - Regime de Escoamento
          - Energia Específica (E)
          - Movimentação de Terra (volume)

        e preenche os lineEdits em scrollAreaResultado.
        """
        # Garante que há feição selecionada no tableViewFeicao
        if hasattr(self, "tableViewFeicao"):
            sel_model = self.tableViewFeicao.selectionModel()
            model = getattr(self, "_feicao_model", None)
            has_rows = model is not None and model.rowCount() > 0
            has_sel = sel_model is not None and sel_model.currentIndex().isValid()
            if not (has_rows and has_sel):
                self.mostrar_mensagem(self.tr("Selecione uma feição na tabela para calcular."), "Aviso", duracao=3)
                self._update_pushButtonCalcular_state()
                return

        # Tipo de canal selecionado
        tipo = None
        if hasattr(self, "comboBoxCanais") and self.comboBoxCanais is not None:
            tipo = self.comboBoxCanais.currentData()
        if not tipo:
            return

        # Confere se o tipo da camada selecionada bate com o tipo do comboBoxCanais
        layer = getattr(self, "_current_canal_layer", None)
        if isinstance(layer, QgsVectorLayer):
            tipo_layer = self._get_canal_tipo_for_layer(layer)
            if tipo_layer and str(tipo_layer) != str(tipo):
                # Pisca o botão e o combo em vermelho
                if hasattr(self, "pushButtonCalcular"):
                    self._blink_widget_red(self.pushButtonCalcular)
                if hasattr(self, "comboBoxCanais") and self.comboBoxCanais is not None:
                    self._blink_widget_red(self.comboBoxCanais)

                self.mostrar_mensagem(self.tr("O tipo selecionado em 'Tipo de Canal' não corresponde ao tipo da camada selecionada."), "Aviso")
                return

        if tipo == "circular":
            ok, msg = self._validate_circular_inputs()
            if not ok:
                self._blink_invalid_circular_inputs()
                self.mostrar_mensagem(msg, "Aviso", duracao=3)
                return

        # Valida profundidade Yn
        spin_yn = getattr(self, "spinYn", None)
        if spin_yn is None or spin_yn.value() <= 0.0:
            if spin_yn is not None:
                self._blink_widget_red(spin_yn)
            self.mostrar_mensagem(self.tr("Informe uma profundidade normal (Yn) maior que zero."), "Aviso")
            return
        y = float(spin_yn.value())

        # Declividade em %, convertida para S (m/m)
        I_perc = self.spinDeclividade.value() if hasattr(self, "spinDeclividade") else 0.0
        S = abs(float(I_perc)) / 100.0

        # Outros parâmetros geométricos
        folga = self.spinFolga.value() if hasattr(self, "spinFolga") else 0.0
        comp_canal = self.spinCompCanal.value() if hasattr(self, "spinCompCanal") else 0.0
        z = self.spinTaludeZ.value() if hasattr(self, "spinTaludeZ") else 0.0
        b = self.spinBaseB.value() if hasattr(self, "spinBaseB") else 0.0
        D = self.spinDiametro.value() if hasattr(self, "spinDiametro") else 0.0

        # Rugosidade de Manning (n)
        line_n = getattr(self, "lineEditRugosidade", None)
        if line_n is None:
            self.mostrar_mensagem(self.tr("Informe a rugosidade de Manning (n)."), "Aviso")
            return

        txt_n = line_n.text().strip().replace(",", ".")
        if not txt_n:
            self._blink_widget_red(line_n)
            self.mostrar_mensagem(self.tr("Informe a rugosidade de Manning (n)."), "Aviso")
            return

        try:
            n = float(txt_n)
        except ValueError:
            self._blink_widget_red(line_n)
            self.mostrar_mensagem(self.tr("Informe a rugosidade de Manning (n)."), "Aviso")
            return

        if n <= 0.0:
            self._blink_widget_red(line_n)
            self.mostrar_mensagem(self.tr("A rugosidade (n) deve ser maior que zero."), "Aviso")
            return

        # Grava os dados atuais do scrollAreaDados na feição selecionada
        self._update_atributos_canal_from_scroll_dados()

        # Geometria: Área (A), Perímetro (P) e Largura de Superfície (B)
        A, P, B = self._calc_area_perimetro_canal(tipo, y, z, b, D)

        # Se a geometria não permitir calcular, avisa
        if A <= 0.0 or P <= 0.0 or B <= 0.0:
            for attr in [
                "lineAreaA",
                "lineVazaoQ",
                "linePerimetroP",
                "lineLarguraB",
                "lineProfCriticaYc",
                "lineVelocidadeV",
                "lineFroudeFr",
                "lineRegimeEscoamento",
                "lineEnergiaE",
                "lineMovimentacaoTerra"]:
                if hasattr(self, attr) and getattr(self, attr) is not None:
                    getattr(self, attr).clear()

            self.mostrar_mensagem(self.tr("Verifique os parâmetros geométricos do canal (Yn, z, b ou D)."), "Aviso")
            return

        # Preenche Área (A)
        if hasattr(self, "lineAreaA") and self.lineAreaA is not None:
            self.lineAreaA.setText(f"{A:.4f}")

        # Preenche Perímetro Molhado (P)
        if hasattr(self, "linePerimetroP") and self.linePerimetroP is not None:
            self.linePerimetroP.setText(f"{P:.4f}")

        # Preenche Largura da Superfície (B)
        if hasattr(self, "lineLarguraB") and self.lineLarguraB is not None:
            self.lineLarguraB.setText(f"{B:.4f}")

        # Vazão (Q) com Manning: Q = (1/n) * A * R^(2/3) * S^(1/2)
        Q = 0.0
        if S <= 0.0 or n <= 0.0:
            for attr in [
                "lineVazaoQ",
                "lineVelocidadeV",
                "lineFroudeFr",
                "lineRegimeEscoamento",
                "lineProfCriticaYc",
                "lineEnergiaE"]:
                if hasattr(self, attr) and getattr(self, attr) is not None:
                    getattr(self, attr).clear()

            self.mostrar_mensagem(self.tr("Informe uma declividade (I) diferente de zero e um coeficiente de rugosidade (n) maior que zero para calcular a vazão."), "Aviso")

            # mesmo assim, podemos calcular volume de terra mais abaixo
            Q = 0.0
        else:
            R = A / P
            Q = (1.0 / n) * A * (R ** (2.0 / 3.0)) * (S ** 0.5)
            if hasattr(self, "lineVazaoQ") and self.lineVazaoQ is not None:
                self.lineVazaoQ.setText(f"{Q:.4f}")

        # Profundidade Crítica (Yc), se tivermos Q > 0
        yc = 0.0
        if Q > 0.0:
            yc = self._calc_critical_depth(tipo, Q, z, b, D, y_ref=y)

        if hasattr(self, "lineProfCriticaYc") and self.lineProfCriticaYc is not None:
            if yc > 0.0:
                self.lineProfCriticaYc.setText(f"{yc:.4f}")
            else:
                self.lineProfCriticaYc.clear()

        #  Velocidade (V), Número de Froude (Fr) e regime
        V = 0.0
        Fr = 0.0
        regime = ""

        if Q > 0.0 and A > 0.0:
            V = Q / A  # [m/s]

        if V > 0.0 and B > 0.0:
            # Profundidade hidráulica D_h = A / B
            D_h = A / B
            if D_h > 0.0:
                Fr = V / math.sqrt(9.81 * D_h)

        # Classificação de regime
        if Fr > 0.0:
            eps = 0.05  # tolerância
            if abs(Fr - 1.0) <= eps:
                regime = self.tr("Crítico")
            elif Fr < 1.0:
                regime = self.tr("Subcrítico")
            else:
                regime = self.tr("Supercrítico")

        # Preenche campos de velocidade / Froude / regime
        if hasattr(self, "lineVelocidadeV") and self.lineVelocidadeV is not None:
            if V > 0.0:
                self.lineVelocidadeV.setText(f"{V:.4f}")
            else:
                self.lineVelocidadeV.clear()

        if hasattr(self, "lineFroudeFr") and self.lineFroudeFr is not None:
            if Fr > 0.0:
                self.lineFroudeFr.setText(f"{Fr:.4f}")
            else:
                self.lineFroudeFr.clear()

        if hasattr(self, "lineRegimeEscoamento") and self.lineRegimeEscoamento is not None:
            self.lineRegimeEscoamento.setText(regime if regime else "")

        #  Energia Específica (E) = y + V²/(2g)
        E = 0.0
        if V > 0.0:
            g = 9.81
            E = y + (V * V) / (2.0 * g)

        if hasattr(self, "lineEnergiaE") and self.lineEnergiaE is not None:
            if E > 0.0:
                self.lineEnergiaE.setText(f"{E:.4f}")
            else:
                self.lineEnergiaE.clear()

        #  Movimentação de Terra (volume)
        #  Para circular, considera escavação bruta de vala/tubo enterrado.
        V_terra = 0.0
        if comp_canal > 0.0:
            area_terr = 0.0

            if tipo == "circular":
                _, feat_sel = self._get_selected_canal_feature_context()
                area_terr = self._calc_circular_trench_area(D, feat_sel)
            else:
                area_terr = self._calc_earthwork_area(tipo, y, folga, z, b, D)

            if area_terr > 0.0:
                V_terra = area_terr * comp_canal

        # Descobre o QLineEdit correto (depende do objectName no .ui)
        line_mov_terra = None
        if hasattr(self, "lineMovimentacaoTerra"):
            line_mov_terra = self.lineMovimentacaoTerra
        elif hasattr(self, "lineMovTerra"):
            line_mov_terra = self.lineMovTerra

        if line_mov_terra is not None:
            if V_terra > 0.0:
                line_mov_terra.setText(f"{V_terra:.3f}")
            else:
                line_mov_terra.clear()

        # Grava os resultados calculados nos atributos da feição
        self._update_resultados_canal_from_scroll_resultado()

        # Atualiza o gráfico da feição selecionada
        try:
            self._update_grafico_from_selection()
        except Exception:
            pass  # nosec B110

        # Atualiza a aba PROJETO (lista + gráfico global)
        try:
            self._refresh_projeto_views(layer)
        except Exception:
            pass  # nosec B110

    def _get_selected_canal_feature_context(self):
        """
        Retorna (layer, feat) da feição atualmente selecionada em tableViewFeicao.
        """
        layer = getattr(self, "_current_canal_layer", None)
        if not isinstance(layer, QgsVectorLayer):
            return None, None

        fid = None
        if hasattr(self, "tableViewFeicao"):
            sel_model = self.tableViewFeicao.selectionModel()
            if sel_model is not None:
                idx = sel_model.currentIndex()
                if idx.isValid():
                    fid = idx.data(Qt.ItemDataRole.UserRole)

        if fid is None:
            return layer, None

        try:
            feat = layer.getFeature(fid)
        except Exception:
            feat = None

        if feat is None or not feat.isValid():
            return layer, None

        return layer, feat

    @staticmethod
    def _feat_attr_float(feat: QgsFeature | None, field_name: str, default=None):
        """
        Lê um atributo numérico da feição; se não existir ou estiver inválido, retorna default.
        """
        if feat is None or not feat.isValid():
            return default

        try:
            val = feat.attribute(field_name)
        except Exception:
            return default

        if val in (None, ""):
            return default

        try:
            return float(val)
        except Exception:
            return default

    def _get_circular_trench_params(self, feat: QgsFeature | None, D: float) -> dict:
        """
        Resolve parâmetros da vala do canal circular.

        Prioridade:
        1) usa atributos da feição, se existirem e forem válidos
        2) fallback para defaults práticos
        """
        D = max(0.0, float(D))

        diam_ext = self._feat_attr_float(feat, "Diametro_Ext", None)
        if diam_ext is None or diam_ext <= 0.0:
            diam_ext = max(D, D * 1.10 if D > 0.0 else 0.0)

        folga_lat = self._feat_attr_float(feat, "Folga_Lat", None)
        if folga_lat is None or folga_lat < 0.0:
            folga_lat = max(0.15, 0.15 * diam_ext)

        berco_esp = self._feat_attr_float(feat, "Berco_Esp", None)
        if berco_esp is None or berco_esp < 0.0:
            berco_esp = 0.10

        cobertura = self._feat_attr_float(feat, "Cobertura_C", None)
        if cobertura is None or cobertura < 0.0:
            cobertura = 0.30

        talude_vala = self._feat_attr_float(feat, "Talude_Vala", None)
        if talude_vala is None or talude_vala < 0.0:
            talude_vala = 0.0

        return {
            "Diametro_Ext": diam_ext,
            "Folga_Lat": folga_lat,
            "Berco_Esp": berco_esp,
            "Cobertura_C": cobertura,
            "Talude_Vala": talude_vala}

    def _calc_circular_trench_area(self, D: float, feat: QgsFeature | None = None) -> float:
        """
        Área aproximada de escavação da vala para canal/tubo circular enterrado.

        Mov_Terra passa a representar ESCAVAÇÃO BRUTA da vala:
          - H_vala = Dext + berço + cobertura
          - B_fundo = Dext + 2*folga lateral
          - A = (B_fundo + z*H_vala) * H_vala
        onde z é o talude horizontal por 1 vertical, por lado.
        """
        D = max(0.0, float(D))
        if D <= 0.0:
            return 0.0

        p = self._get_circular_trench_params(feat, D)

        Dext = max(0.0, float(p["Diametro_Ext"]))
        folga_lat = max(0.0, float(p["Folga_Lat"]))
        berco = max(0.0, float(p["Berco_Esp"]))
        cobertura = max(0.0, float(p["Cobertura_C"]))
        z_vala = max(0.0, float(p["Talude_Vala"]))

        if Dext <= 0.0:
            return 0.0

        H_vala = Dext + berco + cobertura
        B_fundo = Dext + 2.0 * folga_lat

        if H_vala <= 0.0 or B_fundo <= 0.0:
            return 0.0

        # seção trapezoidal simétrica de vala
        return (B_fundo + z_vala * H_vala) * H_vala

    def _calc_earthwork_area(self, tipo: str, y: float, f: float, z: float, b: float, D: float) -> float:
        """
        Área aproximada da seção de escavação (m²),
        usando profundidade total h = y + f, para canais abertos.

        Observação:
        - triangular, trapezoidal e retangular são tratados aqui;
        - circular enterrado é tratado separadamente por
          _calc_circular_trench_area(...).
        """
        h = max(0.0, float(y) + float(f))
        z = max(0.0, float(z))
        b = max(0.0, float(b))
        D = max(0.0, float(D))

        if h <= 0.0:
            return 0.0

        if tipo == "triangular":
            # seção triangular, taludes z:1
            return z * h * h

        elif tipo == "trapezoidal":
            # seção trapezoidal
            return (b + z * h) * h

        elif tipo == "retangular":
            # seção retangular
            return b * h

        elif tipo == "circular":
            # deixar 0 por enquanto; podemos refinar depois
            return 0.0

        return 0.0

    def _update_pushButtonCalcular_state(self):
        """
        Habilita o pushButtonCalcular somente se:
        - existir pelo menos uma feição no tableViewFeicao, e
        - houver uma linha selecionada.
        """
        if not hasattr(self, "pushButtonCalcular"):
            return

        enabled = False

        if hasattr(self, "tableViewFeicao") and hasattr(self, "_feicao_model") and self._feicao_model is not None:
            model = self._feicao_model
            if model.rowCount() > 0:
                sel_model = self.tableViewFeicao.selectionModel()
                if sel_model and sel_model.currentIndex().isValid():
                    enabled = True

        self.pushButtonCalcular.setEnabled(enabled)

        try:
            self.pushButtonCalcular.setToolTip("")
        except Exception:
            pass  # nosec B110

    def _blink_widget_red(self, widget, times: int = 2, interval_ms: int = 150):
        """
        Faz o widget "piscar" em vermelho algumas vezes para chamar atenção.
        """
        if widget is None:
            return

        base_style = widget.styleSheet() or ""
        blink_style = (base_style + ";background-color: rgba(255, 0, 0, 120);"
            if base_style else
            "background-color: rgba(255, 0, 0, 120);")

        total_steps = max(1, times) * 2
        state = {"count": 0}

        def toggle():
            if state["count"] % 2 == 0:
                widget.setStyleSheet(blink_style)
            else:
                widget.setStyleSheet(base_style)

            state["count"] += 1
            if state["count"] >= total_steps:
                timer.stop()
                widget.setStyleSheet(base_style)

        timer = QTimer(widget)
        timer.timeout.connect(toggle)
        timer.start(interval_ms)

    def _ensure_campos_canal_for_layer(self, layer: QgsVectorLayer, tipo: str):
        """
        Garante que a camada de canais tenha todos os campos necessários,
        de acordo com o tipo de canal ('triangular', 'trapezoidal',
        'retangular', 'circular').

        Não grava valores, só cria campos se estiverem faltando.
        """
        if not isinstance(layer, QgsVectorLayer):
            return

        prov = layer.dataProvider()
        fields = layer.fields()
        novos_campos: list[QgsField] = []

        def add_if_missing(name, qvariant_type=QMetaType.Type.Double, length=20, prec=3):
            if fields.indexOf(name) == -1:
                if qvariant_type == QMetaType.Type.Double:
                    novos_campos.append(QgsField(name, qvariant_type, "double", length, prec))
                else:
                    novos_campos.append(QgsField(name, qvariant_type, "string", length))

        # Campos básicos (sempre)
        add_if_missing("CN", QMetaType.Type.QString, 50, 0)
        add_if_missing("Compr_Canal", QMetaType.Type.Double, 20, 3)
        add_if_missing("Declividade(I)", QMetaType.Type.Double, 20, 3)
        add_if_missing("Tipo_Canal", QMetaType.Type.QString, 20, 0)

        tipo = str(tipo or "")

        if tipo == "triangular":
            add_if_missing("Yn")
            add_if_missing("Folga")
            add_if_missing("Talude_Z")
            add_if_missing("n_Manning", QMetaType.Type.Double, 20, 4)

        elif tipo == "trapezoidal":
            add_if_missing("Yn")
            add_if_missing("Folga")
            add_if_missing("Talude_Z")
            add_if_missing("Base_B")
            add_if_missing("n_Manning", QMetaType.Type.Double, 20, 4)

        elif tipo == "retangular":
            add_if_missing("Yn")
            add_if_missing("Folga")
            add_if_missing("Base_B")
            add_if_missing("n_Manning", QMetaType.Type.Double, 20, 4)

        elif tipo == "circular":
            add_if_missing("Yn")
            add_if_missing("Diametro_D")
            add_if_missing("Diametro_Ext")
            add_if_missing("Folga_Lat")
            add_if_missing("Berco_Esp")
            add_if_missing("Cobertura_C")
            add_if_missing("Talude_Vala")
            add_if_missing("n_Manning", QMetaType.Type.Double, 20, 4)

        else:
            # tipo desconhecido: grava só Yn e n_Manning se existirem
            add_if_missing("Yn")
            add_if_missing("n_Manning", QMetaType.Type.Double, 20, 4)

        # Campos de resultados hidráulicos (sempre)
        # Área (A), Vazão (Q), Perímetro Molhado (P),
        # Largura da Superfície (B), Profundidade Crítica (Yc),
        # Número de Froude (Fr), Regime, Velocidade (V),
        # Energia Específica (E), Movimentação de Terra
        add_if_missing("Area_A",       QMetaType.Type.Double, 20, 4)
        add_if_missing("Vazao_Q",      QMetaType.Type.Double, 20, 4)
        add_if_missing("Perimetro_P",  QMetaType.Type.Double, 20, 4)
        add_if_missing("Largura_B",    QMetaType.Type.Double, 20, 4)
        add_if_missing("ProfCrit_Yc",  QMetaType.Type.Double, 20, 4)
        add_if_missing("Froude_Fr",    QMetaType.Type.Double, 20, 4)
        add_if_missing("Regime_Esco",  QMetaType.Type.QString, 30, 0)
        add_if_missing("Velocidade_V", QMetaType.Type.Double, 20, 4)
        add_if_missing("Energia_E",    QMetaType.Type.Double, 20, 4)
        add_if_missing("Mov_Terra",    QMetaType.Type.Double, 20, 4)

        if novos_campos:
            prov.addAttributes(novos_campos)
            layer.updateFields()

    def _update_atributos_canal_from_scroll_dados(self):
        """
        Copia os valores do scrollAreaDados + lineEditRugosidade
        para a feição atualmente selecionada na camada de canais.

        Os campos já devem existir na camada (criados por
        _ensure_campos_canal_for_layer).
        """
        layer = getattr(self, "_current_canal_layer", None)
        if not isinstance(layer, QgsVectorLayer):
            return

        # fid selecionado no tableViewFeicao
        fid = None
        if hasattr(self, "tableViewFeicao"):
            sel_model = self.tableViewFeicao.selectionModel()
            if sel_model is not None:
                idx = sel_model.currentIndex()
                if idx.isValid():
                    fid = idx.data(Qt.ItemDataRole.UserRole)

        if fid is None:
            return

        try:
            feat = layer.getFeature(fid)
        except Exception:
            return

        if not feat.isValid():
            return

        # Tipo de canal
        tipo = self._get_canal_tipo_for_layer(layer)
        if (not tipo) and hasattr(self, "comboBoxCanais") and self.comboBoxCanais is not None:
            tipo = self.comboBoxCanais.currentData() or ""
        tipo = str(tipo or "")

        # Lê valores da interface

        def _get_spin_value(name):
            w = getattr(self, name, None)
            if w is None:
                return None
            try:
                return float(w.value())
            except Exception:
                return None

        y     = _get_spin_value("spinYn")
        folga = _get_spin_value("spinFolga")
        z     = _get_spin_value("spinTaludeZ")
        b     = _get_spin_value("spinBaseB")
        D     = _get_spin_value("spinDiametro")
        Dext      = _get_spin_value("spinDiametroExt")
        folga_lat = _get_spin_value("spinFolgaLat")
        berco_esp = _get_spin_value("spinBercoEsp")
        cobertura = _get_spin_value("spinCobertura")
        z_vala    = _get_spin_value("spinTaludeVala")

        n_val = None
        line_n = getattr(self, "lineEditRugosidade", None)
        if line_n is not None:
            txt = line_n.text().strip().replace(",", ".")
            if txt:
                try:
                    n_val = float(txt)
                except ValueError:
                    n_val = None

        # Garante edição
        if not layer.isEditable():
            layer.startEditing()

        # Garante campos (para camadas antigas criadas antes do ajuste)
        self._ensure_campos_canal_for_layer(layer, tipo)

        fields = layer.fields()

        idx_tipo = fields.indexOf("Tipo_Canal")
        idx_Yn   = fields.indexOf("Yn")
        idx_F    = fields.indexOf("Folga")
        idx_Z    = fields.indexOf("Talude_Z")
        idx_B    = fields.indexOf("Base_B")
        idx_Diam = fields.indexOf("Diametro_D")
        idx_n    = fields.indexOf("n_Manning")
        idx_Dext = fields.indexOf("Diametro_Ext")
        idx_FLat = fields.indexOf("Folga_Lat")
        idx_Berc = fields.indexOf("Berco_Esp")
        idx_Cob  = fields.indexOf("Cobertura_C")
        idx_ZVal = fields.indexOf("Talude_Vala")

        def set_attr(idx, valor):
            if idx >= 0:
                layer.changeAttributeValue(fid, idx, valor)

        # Tipo textual
        if tipo:
            set_attr(idx_tipo, tipo)

        # Comuns
        if y is not None:
            set_attr(idx_Yn, y)
        if n_val is not None:
            set_attr(idx_n, n_val)

        # Específicos por tipo
        if tipo == "triangular":
            if folga is not None:
                set_attr(idx_F, folga)
            if z is not None:
                set_attr(idx_Z, z)

        elif tipo == "trapezoidal":
            if folga is not None:
                set_attr(idx_F, folga)
            if z is not None:
                set_attr(idx_Z, z)
            if b is not None:
                set_attr(idx_B, b)

        elif tipo == "retangular":
            if folga is not None:
                set_attr(idx_F, folga)
            if b is not None:
                set_attr(idx_B, b)

        elif tipo == "circular":
            if D is not None:
                set_attr(idx_Diam, D)
            if Dext is not None:
                set_attr(idx_Dext, Dext)
            if folga_lat is not None:
                set_attr(idx_FLat, folga_lat)
            if berco_esp is not None:
                set_attr(idx_Berc, berco_esp)
            if cobertura is not None:
                set_attr(idx_Cob, cobertura)
            if z_vala is not None:
                set_attr(idx_ZVal, z_vala)

        # agora que os atributos foram gravados
        self._populate_canais_medidas_from_layer(fid=fid)

    def _populate_canais_medidas_from_layer(self, fid=None):
        """
        Preenche os campos do scrollAreaDados a partir da feição atual
        da camada de canais:

        - Comprimento do Canal   (spinCompCanal  <- Compr_Canal)
        - Declividade (I)        (spinDeclividade <- Declividade(I))
        - Yn                     (spinYn         <- Yn)
        - Folga                  (spinFolga      <- Folga)
        - Talude_Z               (spinTaludeZ    <- Talude_Z)
        - Base_B                 (spinBaseB      <- Base_B)
        - Diametro_D             (spinDiametro   <- Diametro_D)
        - n de Manning           (lineEditRugosidade <- n_Manning)

        Só atualiza os widgets se:
        - houver camada corrente,
        - houver feição válida,
        - o tipo da camada bater com o tipo do comboBoxCanais.
        Caso não haja feição/tipo compatível, reseta apenas Comp/Declividade.
        """
        has_comp    = hasattr(self, "spinCompCanal")
        has_decl    = hasattr(self, "spinDeclividade")
        has_yn      = hasattr(self, "spinYn")
        has_folga   = hasattr(self, "spinFolga")
        has_talude  = hasattr(self, "spinTaludeZ")
        has_baseb   = hasattr(self, "spinBaseB")
        has_diam    = hasattr(self, "spinDiametro")
        has_diam_ex = hasattr(self, "spinDiametroExt")
        has_flat    = hasattr(self, "spinFolgaLat")
        has_berco   = hasattr(self, "spinBercoEsp")
        has_cob     = hasattr(self, "spinCobertura")
        has_zvala   = hasattr(self, "spinTaludeVala")
        has_n       = hasattr(self, "lineEditRugosidade")

        if not (has_comp or has_decl or has_yn or has_folga or has_talude or has_baseb
            or has_diam or has_diam_ex or has_flat or has_berco or has_cob or has_zvala or has_n):
            return

        layer = getattr(self, "_current_canal_layer", None)
        if not isinstance(layer, QgsVectorLayer):
            self._reset_canais_dados_fields()
            return

        # Confere tipo da camada x tipo selecionado no comboBoxCanais
        tipo_ui = None
        if hasattr(self, "comboBoxCanais") and self.comboBoxCanais is not None:
            tipo_ui = self.comboBoxCanais.currentData()

        tipo_layer = self._get_canal_tipo_for_layer(layer)

        # Se souber o tipo da camada e do combo, e forem diferentes -> não mostra nada
        if tipo_ui and tipo_layer and (str(tipo_ui) != str(tipo_layer)):
            self._reset_canais_dados_fields()
            return

        # Determina qual feição usar
        try:
            if fid is None:
                sel_ids = list(layer.selectedFeatureIds())
                if sel_ids:
                    fid = sel_ids[0]
                elif layer.featureCount() == 1:
                    for f in layer.getFeatures():
                        fid = f.id()
                        break

            if fid is None:
                self._reset_canais_dados_fields()
                return

            feat = layer.getFeature(fid)
            if not feat.isValid():
                self._reset_canais_dados_fields()
                return
        except Exception:
            self._reset_canais_dados_fields()
            return

        fields = layer.fields()
        idx_len   = fields.indexOf("Compr_Canal")
        idx_decl  = fields.indexOf("Declividade(I)")
        idx_yn    = fields.indexOf("Yn")
        idx_folga = fields.indexOf("Folga")
        idx_z     = fields.indexOf("Talude_Z")
        idx_b     = fields.indexOf("Base_B")
        idx_d     = fields.indexOf("Diametro_D")
        idx_n     = fields.indexOf("n_Manning")
        idx_dext  = fields.indexOf("Diametro_Ext")
        idx_flat  = fields.indexOf("Folga_Lat")
        idx_berco = fields.indexOf("Berco_Esp")
        idx_cob   = fields.indexOf("Cobertura_C")
        idx_zvala = fields.indexOf("Talude_Vala")

        def _set_spin(widget_name, idx):
            if idx < 0:
                return
            w = getattr(self, widget_name, None)
            if w is None:
                return
            val = feat.attribute(idx)
            if val is None:
                return
            try:
                v = float(val)
            except (TypeError, ValueError):
                return
            w.blockSignals(True)
            w.setValue(v)
            w.blockSignals(False)

        if has_diam_ex:
            _set_spin("spinDiametroExt", idx_dext)

        if has_flat:
            _set_spin("spinFolgaLat", idx_flat)

        if has_berco:
            _set_spin("spinBercoEsp", idx_berco)

        if has_cob:
            _set_spin("spinCobertura", idx_cob)

        if has_zvala:
            _set_spin("spinTaludeVala", idx_zvala)

        # Comprimento do Canal
        if has_comp:
            _set_spin("spinCompCanal", idx_len)

        # Declividade (I) em %
        if has_decl and idx_decl >= 0:
            val = feat.attribute(idx_decl)
            try:
                if val is not None:
                    v = float(val)
                    self.spinDeclividade.blockSignals(True)
                    self.spinDeclividade.setValue(v)
                    self.spinDeclividade.blockSignals(False)
                    # Atualiza a cor conforme o sinal
                    self._on_spinDeclividade_value_changed(v)
            except (TypeError, ValueError):
                pass  # nosec B110

        # Yn, Folga, Talude_Z, Base_B, Diametro_D
        if has_yn:
            _set_spin("spinYn", idx_yn)

        if has_folga:
            _set_spin("spinFolga", idx_folga)

        if has_talude:
            _set_spin("spinTaludeZ", idx_z)

        if has_baseb:
            _set_spin("spinBaseB", idx_b)

        if has_diam:
            _set_spin("spinDiametro", idx_d)

        # n de Manning no lineEditRugosidade
        if has_n and idx_n >= 0:
            val = feat.attribute(idx_n)
            if val is not None:
                txt = str(val)
                self.lineEditRugosidade.blockSignals(True)
                self.lineEditRugosidade.setText(txt)
                self.lineEditRugosidade.blockSignals(False)

        # Atualiza também o gráfico de perfil (terreno x canal)
        try:
            self._update_grafico_canal_terreno(layer=layer, fid=fid)
        except Exception:
            # não quebra o fluxo por causa do gráfico
            pass  # nosec B110

    def _on_spinDeclividade_value_changed(self, value: float):
        """
        Deixa o texto do spinDeclividade em vermelho se o valor
        for negativo; volta ao padrão caso contrário.
        """
        if not hasattr(self, "spinDeclividade"):
            return

        try:
            if value < 0:
                self.spinDeclividade.setStyleSheet("QDoubleSpinBox { color: red; }")
            else:
                self.spinDeclividade.setStyleSheet("")
        except RuntimeError:
            # Caso o widget já tenha sido destruído ao trocar de tipo
            pass  # nosec B110

    def _init_pushButtonInverter(self):
        """
        Configura o pushButtonInverter:
        - começa desabilitado
        - conecta ao slot de inversão (se quiser usar depois)
        """
        if hasattr(self, "pushButtonInverter") and self.pushButtonInverter is not None:
            self.pushButtonInverter.setEnabled(False)
            self.pushButtonInverter.clicked.connect(self._on_pushButtonInverter_clicked)

    def _update_pushButtonInverter_state(self):
        """
        Habilita o pushButtonInverter somente se:
        - existir uma feição selecionada no tableViewFeicao, e
        - o valor de Declividade(I) dessa feição for negativo.
        """
        if not hasattr(self, "pushButtonInverter"):
            return

        enabled = False

        layer = getattr(self, "_current_canal_layer", None)
        if (
            isinstance(layer, QgsVectorLayer)
            and hasattr(self, "tableViewFeicao")
            and hasattr(self, "_feicao_model")
            and self._feicao_model is not None):
            model = self._feicao_model
            if model.rowCount() > 0:
                sel_model = self.tableViewFeicao.selectionModel()
                if sel_model:
                    idx = sel_model.currentIndex()
                    if idx.isValid():
                        fid = idx.data(Qt.ItemDataRole.UserRole)
                        if fid is not None:
                            try:
                                feat = layer.getFeature(fid)
                            except Exception:
                                feat = None

                            if feat is not None and feat.isValid():
                                fields = layer.fields()
                                idx_decl = fields.indexOf("Declividade(I)")
                                if idx_decl >= 0:
                                    val = feat.attribute(idx_decl)
                                    try:
                                        enabled = float(val) < 0.0
                                    except (TypeError, ValueError):
                                        enabled = False

        self.pushButtonInverter.setEnabled(enabled)

    def _on_pushButtonInverter_clicked(self):
        """
        Inverte a geometria da feição selecionada (ordem dos vértices da linha).
        Isso faz com que, ao recalcular, a Declividade(I) troque o sinal,
        pois o ponto inicial e final são invertidos no cálculo com o raster.
        """
        layer = getattr(self, "_current_canal_layer", None)
        if not isinstance(layer, QgsVectorLayer):
            return

        if layer.geometryType() != QgsWkbTypes.GeometryType.LineGeometry:
            return

        if not hasattr(self, "tableViewFeicao"):
            return

        sel_model = self.tableViewFeicao.selectionModel()
        if not sel_model:
            return

        idx = sel_model.currentIndex()
        if not idx.isValid():
            return

        fid = idx.data(Qt.ItemDataRole.UserRole)
        if fid is None:
            return

        try:
            feat = layer.getFeature(fid)
        except Exception:
            return

        if not feat.isValid():
            return

        geom = feat.geometry()
        if geom is None or geom.isEmpty():
            return

        new_geom = None

        # Multi-linha
        if geom.isMultipart():
            linhas = geom.asMultiPolyline()
            if not linhas:
                return

            novas_linhas = []
            for ln in linhas:
                if not ln:
                    novas_linhas.append([])
                    continue
                # inverte a ordem dos pontos
                rev_ln = [QgsPointXY(p.x(), p.y()) for p in reversed(ln)]
                novas_linhas.append(rev_ln)

            new_geom = QgsGeometry.fromMultiPolylineXY(novas_linhas)

        # Linha simples
        else:
            linha = geom.asPolyline()
            if len(linha) < 2:
                return

            rev_linha = [QgsPointXY(p.x(), p.y()) for p in reversed(linha)]
            new_geom = QgsGeometry.fromPolylineXY(rev_linha)

        if new_geom is None or new_geom.isEmpty():
            return

        # Garante edição
        if not layer.isEditable():
            layer.startEditing()

        # Grava a nova geometria (dispara geometryChanged)
        layer.changeGeometry(fid, new_geom)

        # Opcional: atualiza visualmente o mapa
        try:
            self.iface.mapCanvas().refresh()
        except Exception:
            pass  # nosec B110

        # Atualiza estado do botão (agora a Declividade deve ficar >= 0)
        self._update_pushButtonInverter_state()

        # Aplica simbologia de seta com cor baseada na Declividade(I)
        self.apply_arrow_symbology(layer)
        # Aplica rótulo do CN com cor baseada na Declividade(I)
        self.apply_cn_labeling(layer)

    def _update_resultados_canal_from_scroll_resultado(self):
        """
        Copia os valores dos lineEdits de scrollAreaResultado
        para os campos de resultados da feição atualmente selecionada:

        lineAreaA          -> Area_A
        lineVazaoQ         -> Vazao_Q
        linePerimetroP     -> Perimetro_P
        lineLarguraB       -> Largura_B
        lineProfCriticaYc  -> ProfCrit_Yc
        lineFroudeFr       -> Froude_Fr
        lineRegimeEscoamento -> Regime_Esco
        lineVelocidadeV    -> Velocidade_V
        lineEnergiaE       -> Energia_E
        lineMovTerra/lineMovimentacaoTerra -> Mov_Terra
        """
        layer = getattr(self, "_current_canal_layer", None)
        if not isinstance(layer, QgsVectorLayer):
            return

        # fid selecionado no tableViewFeicao
        fid = None
        if hasattr(self, "tableViewFeicao"):
            sel_model = self.tableViewFeicao.selectionModel()
            if sel_model is not None:
                idx = sel_model.currentIndex()
                if idx.isValid():
                    fid = idx.data(Qt.ItemDataRole.UserRole)

        if fid is None:
            return

        try:
            feat = layer.getFeature(fid)
        except Exception:
            return

        if not feat.isValid():
            return

        # Garante que os campos existem (para camadas antigas)
        tipo = self._get_canal_tipo_for_layer(layer)
        if (not tipo) and hasattr(self, "comboBoxCanais") and self.comboBoxCanais is not None:
            tipo = self.comboBoxCanais.currentData() or ""
        tipo = str(tipo or "")

        self._ensure_campos_canal_for_layer(layer, tipo)

        fields = layer.fields()
        idx_A      = fields.indexOf("Area_A")
        idx_Q      = fields.indexOf("Vazao_Q")
        idx_P      = fields.indexOf("Perimetro_P")
        idx_B      = fields.indexOf("Largura_B")
        idx_Yc     = fields.indexOf("ProfCrit_Yc")
        idx_Fr     = fields.indexOf("Froude_Fr")
        idx_Reg    = fields.indexOf("Regime_Esco")
        idx_V      = fields.indexOf("Velocidade_V")
        idx_E      = fields.indexOf("Energia_E")
        idx_Vterra = fields.indexOf("Mov_Terra")

        def _get_line_float(name):
            w = getattr(self, name, None)
            if w is None:
                return None
            txt = w.text().strip()
            if not txt:
                return None
            txt = txt.replace(",", ".")
            try:
                return float(txt)
            except ValueError:
                return None

        def _get_line_str(name):
            w = getattr(self, name, None)
            if w is None:
                return None
            txt = w.text().strip()
            return txt if txt else None

        A_val   = _get_line_float("lineAreaA")
        Q_val   = _get_line_float("lineVazaoQ")
        P_val   = _get_line_float("linePerimetroP")
        B_val   = _get_line_float("lineLarguraB")
        Yc_val  = _get_line_float("lineProfCriticaYc")
        Fr_val  = _get_line_float("lineFroudeFr")
        V_val   = _get_line_float("lineVelocidadeV")
        E_val   = _get_line_float("lineEnergiaE")
        Reg_val = _get_line_str("lineRegimeEscoamento")

        Vterra_val = None
        if hasattr(self, "lineMovimentacaoTerra"):
            Vterra_val = _get_line_float("lineMovimentacaoTerra")
        elif hasattr(self, "lineMovTerra"):
            Vterra_val = _get_line_float("lineMovTerra")

        # Garante edição
        if not layer.isEditable():
            layer.startEditing()

        def set_attr(idx, valor):
            if idx >= 0:
                layer.changeAttributeValue(fid, idx, valor)

        set_attr(idx_A,      A_val)
        set_attr(idx_Q,      Q_val)
        set_attr(idx_P,      P_val)
        set_attr(idx_B,      B_val)
        set_attr(idx_Yc,     Yc_val)
        set_attr(idx_Fr,     Fr_val)
        set_attr(idx_V,      V_val)
        set_attr(idx_E,      E_val)
        set_attr(idx_Reg,    Reg_val)
        set_attr(idx_Vterra, Vterra_val)

    def _reset_canais_resultado_fields(self):
        """
        Reseta os campos do scrollAreaResultado (resultados hidráulicos).
        """
        for name in [
            "lineAreaA",
            "lineVazaoQ",
            "linePerimetroP",
            "lineLarguraB",
            "lineProfCriticaYc",
            "lineFroudeFr",
            "lineRegimeEscoamento",
            "lineVelocidadeV",
            "lineEnergiaE",
            "lineMovTerra",
            "lineMovimentacaoTerra"]:  # caso exista com esse nome em algum .ui
        
            if hasattr(self, name):
                w = getattr(self, name)
                if w is not None:
                    w.clear()

    def _populate_canais_resultados_from_layer(self, fid=None):
        """
        Preenche os campos do scrollAreaResultado a partir da feição atual,
        usando os campos de resultados gravados na tabela de atributos:

        Area_A      -> lineAreaA
        Vazao_Q     -> lineVazaoQ
        Perimetro_P -> linePerimetroP
        Largura_B   -> lineLarguraB
        ProfCrit_Yc -> lineProfCriticaYc
        Froude_Fr   -> lineFroudeFr
        Regime_Esco -> lineRegimeEscoamento
        Velocidade_V-> lineVelocidadeV
        Energia_E   -> lineEnergiaE
        Mov_Terra   -> lineMovTerra / lineMovimentacaoTerra
        """
        # Garante que os lineEdits existem
        has_any = any(
            hasattr(self, name)
            for name in [
                "lineAreaA",
                "lineVazaoQ",
                "linePerimetroP",
                "lineLarguraB",
                "lineProfCriticaYc",
                "lineFroudeFr",
                "lineRegimeEscoamento",
                "lineVelocidadeV",
                "lineEnergiaE",
                "lineMovTerra",
                "lineMovimentacaoTerra"])
        if not has_any:
            return

        layer = getattr(self, "_current_canal_layer", None)
        if not isinstance(layer, QgsVectorLayer):
            self._reset_canais_resultado_fields()
            return

        # Confere tipo da camada x tipo selecionado no comboBoxCanais (igual ao _populate_canais_medidas_from_layer)
        tipo_ui = None
        if hasattr(self, "comboBoxCanais") and self.comboBoxCanais is not None:
            tipo_ui = self.comboBoxCanais.currentData()

        tipo_layer = self._get_canal_tipo_for_layer(layer)

        if tipo_ui and tipo_layer and (str(tipo_ui) != str(tipo_layer)):
            self._reset_canais_resultado_fields()
            return

        # Determina qual feição usar (mesma lógica do _populate_canais_medidas_from_layer)
        try:
            if fid is None:
                sel_ids = list(layer.selectedFeatureIds())
                if sel_ids:
                    fid = sel_ids[0]
                elif layer.featureCount() == 1:
                    for f in layer.getFeatures():
                        fid = f.id()
                        break

            if fid is None:
                self._reset_canais_resultado_fields()
                return

            feat = layer.getFeature(fid)
            if not feat.isValid():
                self._reset_canais_resultado_fields()
                return
        except Exception:
            self._reset_canais_resultado_fields()
            return

        fields = layer.fields()
        idx_A      = fields.indexOf("Area_A")
        idx_Q      = fields.indexOf("Vazao_Q")
        idx_P      = fields.indexOf("Perimetro_P")
        idx_B      = fields.indexOf("Largura_B")
        idx_Yc     = fields.indexOf("ProfCrit_Yc")
        idx_Fr     = fields.indexOf("Froude_Fr")
        idx_Reg    = fields.indexOf("Regime_Esco")
        idx_V      = fields.indexOf("Velocidade_V")
        idx_E      = fields.indexOf("Energia_E")
        idx_Vterra = fields.indexOf("Mov_Terra")

        def _set_line_float(widget_name, idx, fmt="{:.4f}"):
            if idx < 0:
                return
            w = getattr(self, widget_name, None)
            if w is None:
                return
            val = feat.attribute(idx)
            if val is None:
                w.clear()
                return
            try:
                v = float(val)
            except (TypeError, ValueError):
                w.clear()
                return
            w.setText(fmt.format(v))

        def _set_line_str(widget_name, idx):
            if idx < 0:
                return
            w = getattr(self, widget_name, None)
            if w is None:
                return
            val = feat.attribute(idx)
            if val is None:
                w.clear()
                return
            w.setText(str(val))

        # Área, Vazão, Perímetro, Largura, Profundidade Crítica
        _set_line_float("lineAreaA",          idx_A,      "{:.4f}")
        _set_line_float("lineVazaoQ",         idx_Q,      "{:.4f}")
        _set_line_float("linePerimetroP",     idx_P,      "{:.4f}")
        _set_line_float("lineLarguraB",       idx_B,      "{:.4f}")
        _set_line_float("lineProfCriticaYc",  idx_Yc,     "{:.4f}")

        # Froude e Velocidade, Energia
        _set_line_float("lineFroudeFr",       idx_Fr,     "{:.4f}")
        _set_line_float("lineVelocidadeV",    idx_V,      "{:.4f}")
        _set_line_float("lineEnergiaE",       idx_E,      "{:.4f}")

        # Regime de Escoamento (texto)
        _set_line_str("lineRegimeEscoamento", idx_Reg)

        # Movimentação de Terra (3 casas, igual ao cálculo)
        if hasattr(self, "lineMovimentacaoTerra"):
            _set_line_float("lineMovimentacaoTerra", idx_Vterra, "{:.3f}")
        elif hasattr(self, "lineMovTerra"):
            _set_line_float("lineMovTerra",          idx_Vterra, "{:.3f}")

    def _on_feicao_row_changed(self, current: QModelIndex, previous: QModelIndex):
        """
        Quando o usuário seleciona uma feição no tableViewFeicao,
        preenche o scrollAreaDados com Compr_Canal e Declividade(I)
        e o scrollAreaResultado com os resultados gravados.
        Se não houver seleção, reseta os campos.
        """
        if not current.isValid():
            self._reset_canais_dados_fields()
            self._reset_canais_resultado_fields()   # <<< NOVO
            self._update_pushButtonCalcular_state()
            # se tiver o botão inverter, pode atualizar aqui também
            # self._update_pushButtonInverter_state()
            return

        fid = current.data(Qt.ItemDataRole.UserRole)
        if fid is None:
            self._reset_canais_dados_fields()
            self._reset_canais_resultado_fields()   # <<< NOVO
            self._update_pushButtonCalcular_state()
            # self._update_pushButtonInverter_state()
            return

        # Garante que o comboBoxCanais esteja alinhado com o tipo da camada atualmente selecionada
        layer = getattr(self, "_current_canal_layer", None)
        if layer is not None:
            self._sync_combo_canais_with_layer(layer)

        # Entrada (scrollAreaDados)
        self._populate_canais_medidas_from_layer(fid=fid)

        # Atualiza o gráfico para essa feição
        if hasattr(self, "_update_grafico_from_selection"):
            self._update_grafico_from_selection()

        # Resultados (scrollAreaResultado)
        self._populate_canais_resultados_from_layer(fid=fid)

        # Atualiza estados dos botões
        if hasattr(self, "_update_pushButtonCalcular_state"):
            self._update_pushButtonCalcular_state()
        if hasattr(self, "_update_pushButtonInverter_state"):
            self._update_pushButtonInverter_state()
#////////////////////////////////////////////
    def apply_arrow_symbology(self, layer: QgsVectorLayer):
        """
        Aplica simbologia de seta na camada de linhas:

          - preenchimento azul (#0066CC) se Declividade(I) >= 0
          - preenchimento vermelho (#CC0000) se Declividade(I) < 0

        Sem traço de linha (apenas a seta).
        """
        if not isinstance(layer, QgsVectorLayer):
            return

        if layer.geometryType() != QgsWkbTypes.GeometryType.LineGeometry:
            return

        field_name = 'Declividade(I)'

        # expressão para cor baseada na Declividade(I)
        # < 0  -> vermelho
        # >= 0 -> azul
        color_expr = (
            f'CASE '
            f'WHEN "{field_name}" < 0 THEN color_rgb(255, 0, 0) '      # vermelho
            f'ELSE color_rgb(0, 0, 255) END') # azul

        # camada de seta
        arrow_layer = QgsArrowSymbolLayer()
        arrow_layer.setHeadType(QgsArrowSymbolLayer.HeadType.HeadSingle)
        arrow_layer.setHeadLength(4)
        arrow_layer.setHeadThickness(1.2)
        arrow_layer.setArrowStartWidth(0.6)
        arrow_layer.setArrowWidth(0.6)
        arrow_layer.setColor(QColor('#000000'))  # será sobrescrita por data-defined

        # aplica cor data-defined no sub-símbolo (preenchimento)
        sub_symbol: QgsFillSymbol = arrow_layer.subSymbol()
        if sub_symbol:
            for sl in sub_symbol.symbolLayers():
                # preenchimento controlado pela expressão
                sl.setDataDefinedProperty(
                    QgsSymbolLayer.Property.PropertyFillColor,
                    QgsProperty.fromExpression(color_expr))
                # sem borda
                if hasattr(sl, "setStrokeStyle"):
                    sl.setStrokeStyle(Qt.PenStyle.NoPen)
                if hasattr(sl, "setStrokeWidth"):
                    sl.setStrokeWidth(0.0)
                if hasattr(sl, "setStrokeColor"):
                    sl.setStrokeColor(QColor(0, 0, 0, 0))  # totalmente transparente

        # símbolo de linha sem layers-base (sem traço)
        line_symbol = QgsLineSymbol()
        while line_symbol.symbolLayerCount() > 0:
            line_symbol.deleteSymbolLayer(0)

        # adiciona somente a seta
        line_symbol.appendSymbolLayer(arrow_layer)

        # aplica na camada
        if layer.renderer():
            layer.renderer().setSymbol(line_symbol)
        else:
            layer.setRenderer(QgsSingleSymbolRenderer(line_symbol))

        layer.triggerRepaint()

    def _init_lineEditRugosidade(self):
        """
        Configura o lineEditRugosidade para aceitar apenas números,
        usando vírgula como separador decimal. O usuário pode digitar
        ponto ou vírgula; ponto é convertido automaticamente para vírgula.
        """
        if not hasattr(self, "lineEditRugosidade") or self.lineEditRugosidade is None:
            return

        le = self.lineEditRugosidade

        # Validador numérico com separador decimal da localidade PT-BR (vírgula)
        validator = QDoubleValidator(0.0, 1000.0, 6, le)  # ajuste range/decimais se quiser
        validator.setNotation(QDoubleValidator.Notation.StandardNotation)

        locale = QLocale(QLocale.Language.Portuguese, QLocale.Country.Brazil)
        validator.setLocale(locale)
        le.setValidator(validator)

        # Quando o usuário edita o texto, trocamos ponto por vírgula
        le.textEdited.connect(self._on_rugosidade_text_edited)

    def _on_rugosidade_text_edited(self, text: str):
        """
        Substitui ponto por vírgula enquanto o usuário digita.
        Mantém a posição do cursor o mais próximo possível.
        """
        if not hasattr(self, "lineEditRugosidade") or self.lineEditRugosidade is None:
            return

        new_text = text.replace(".", ",")
        if new_text == text:
            # nada a fazer
            return

        le = self.lineEditRugosidade
        cursor_pos = le.cursorPosition()

        le.blockSignals(True)
        le.setText(new_text)
        # Ajusta levemente a posição do cursor (caso tenha trocado caractere)
        le.setCursorPosition(min(cursor_pos, len(new_text)))
        le.blockSignals(False)

    def apply_cn_labeling(self, layer: QgsVectorLayer):
        """
        Configura rótulos para a camada de canais:

        - Texto = campo "CN"
        - Cor azul se Declividade(I) >= 0
        - Cor vermelha se Declividade(I) < 0
        """
        if not isinstance(layer, QgsVectorLayer):
            return
        if layer.geometryType() != QgsWkbTypes.GeometryType.LineGeometry:
            return

        # 1) Expressão de COR baseada em Declividade(I)
        color_expression = """
            CASE
                WHEN "Declividade(I)" < 0
                    THEN color_rgb(255, 0, 0)      -- vermelho
                ELSE
                    color_rgb(0, 102, 204)         -- azul
            END
        """

        # 2) Configurar estilo do texto
        text_format = QgsTextFormat()
        text_format.setFont(QFont("Arial", 9))
        text_format.setSize(9)
        # Cor padrão (vai ser sobrescrita pelo data-defined)
        text_format.setColor(QColor(0, 102, 204))

        # 3) Configurar PalLayerSettings
        pal_settings = QgsPalLayerSettings()
        pal_settings.enabled = True
        pal_settings.isExpression = False
        pal_settings.fieldName = "CN"   # rótulo = campo CN
        pal_settings.format = text_format

        # Para linhas, usar colocação ao longo da linha
        pal_settings.placement = QgsPalLayerSettings.Placement.Line

        # 4) Propriedades definidas por dados: cor do texto
        ddp = pal_settings.dataDefinedProperties()
        ddp.setProperty(
            QgsPalLayerSettings.Property.Color,
            QgsProperty.fromExpression(color_expression)
        )
        pal_settings.setDataDefinedProperties(ddp)

        # 5) Aplicar a rotulagem na camada
        layer.setLabelsEnabled(True)
        layer.setLabeling(QgsVectorLayerSimpleLabeling(pal_settings))
        layer.triggerRepaint()

        # Opcional: refrescar canvas
        try:
            self.iface.mapCanvas().refresh()
        except Exception:
            pass  # nosec B110
#////////////////////////////////////////////
    def _layer_is_in_canais_group(self, layer: QgsVectorLayer) -> bool:
        """
        Verifica se a camada está dentro do grupo 'CANAIS'.
        """
        if not isinstance(layer, QgsVectorLayer):
            return False

        group = self._get_canais_group()
        if group is None:
            return False

        for node in group.children():
            if isinstance(node, QgsLayerTreeLayer) and node.layerId() == layer.id():
                return True

        return False

    def _on_qgis_current_layer_changed(self, layer):
        """
        Quando o usuário troca a camada ativa no painel de Camadas
        do QGIS, sincronizamos o tableViewCamada se a camada fizer
        parte do grupo 'CANAIS'.
        """
        # Se estamos no meio de uma sincronização iniciada pelo plugin, ignora
        if self._syncing_layer_selection:
            return

        if layer is None or not isinstance(layer, QgsVectorLayer):
            return

        # Só reage para camadas dentro do grupo CANAIS
        if not self._layer_is_in_canais_group(layer):
            return

        # Atualiza camada corrente interna
        self._current_canal_layer = layer

        # Atualiza seleção no tableViewCamada (dispara _on_camada_row_changed)
        self._select_camada_row_by_layer_id(layer.id())

    def _get_cad_dock(self):
        """
        Retorna o dock nativo de Vetorização Avançada do QGIS.
        """
        try:
            return self.iface.cadDockWidget()
        except Exception:
            return None

    def _is_cad_enabled(self) -> bool:
        """
        Retorna True se as ferramentas avançadas de vetorização
        estiverem realmente ATIVAS, não apenas visíveis.
        """
        cad = self._get_cad_dock()
        if cad is None:
            return False

        try:
            return bool(cad.cadEnabled())
        except Exception:
            pass  # nosec B110

        try:
            act = cad.enableAction()
            return bool(act is not None and act.isChecked())
        except Exception:
            return False

    def _set_cad_floater_defaults(self):
        """
        Marca automaticamente no CAD dock:
        - Show Floater
        - Show Distance
        - Show Angle

        Também grava em QSettings para persistir entre sessões.
        """
        try:
            s = QSettings()
            s.setValue("/Cad/Floater", True)
            s.setValue("/Cad/DistanceShowInFloater", True)
            s.setValue("/Cad/AngleShowInFloater", True)
            s.sync()
        except Exception:
            pass  # nosec B110

        cad = self._get_cad_dock()
        if cad is None:
            return

        def _apply_actions():
            try:
                actions = cad.findChildren(QAction)
            except Exception:
                actions = []

            wanted = {"Show Floater", "Show Distance", "Show Angle"}

            for act in actions:
                try:
                    txt = (act.text() or "").strip()
                except Exception:  # nosec B112
                    continue

                if txt in wanted and act.isCheckable() and not act.isChecked():
                    try:
                        act.setChecked(True)
                    except Exception:
                        pass  # nosec B110

        # roda logo após o dock estar pronto/visível
        QTimer.singleShot(0, _apply_actions)

    def _update_checkBoxMapTool_state(self):
        """
        Habilita/desabilita o checkbox conforme existam camadas
        e sincroniza o check com o estado REAL do CAD nativo.
        """
        if not hasattr(self, "checkBoxMapTool") or self.checkBoxMapTool is None:
            return

        has_layers = False
        if hasattr(self, "_camadas_model") and self._camadas_model is not None:
            try:
                has_layers = self._camadas_model.rowCount() > 0
            except Exception:
                has_layers = False

        self.checkBoxMapTool.blockSignals(True)
        self.checkBoxMapTool.setEnabled(has_layers)

        if not has_layers:
            self.checkBoxMapTool.setChecked(False)
        else:
            self.checkBoxMapTool.setChecked(self._is_cad_enabled())

        self.checkBoxMapTool.blockSignals(False)

    def _init_checkBoxMapTool(self):
        """
        Faz o checkBoxMapTool controlar o CAD nativo do QGIS.
        """
        if not hasattr(self, "checkBoxMapTool") or self.checkBoxMapTool is None:
            return

        try:
            self.checkBoxMapTool.toggled.disconnect(self._on_checkBoxMapTool_toggled)
        except Exception:
            pass  # nosec B110

        self.checkBoxMapTool.toggled.connect(self._on_checkBoxMapTool_toggled)
        self._update_checkBoxMapTool_state()

    def _on_cad_enable_action_toggled(self, checked: bool):
        """
        Sincroniza o checkbox quando o usuário liga/desliga o CAD
        pelo próprio QGIS.
        """
        if not hasattr(self, "checkBoxMapTool") or self.checkBoxMapTool is None:
            return

        self.checkBoxMapTool.blockSignals(True)
        self.checkBoxMapTool.setChecked(bool(checked))
        self.checkBoxMapTool.blockSignals(False)

    def _on_cad_dock_visibility_changed(self, visible: bool):
        """
        Se o usuário fechar o painel CAD, o CAD pode continuar desligado.
        Então recalculamos pelo estado real.
        """
        try:
            self._update_checkBoxMapTool_state()
        except Exception:
            pass  # nosec B110

    def _on_checkBoxMapTool_toggled(self, checked: bool):
        """
        O checkbox controla:
        1) ativar/desativar "Ativar ferramentas avançadas de vetorização"
        2) garantir que o painel CAD esteja visível
        3) aplicar preferências do flutuador

        A desativação do CAD ao desmarcar só acontece se este diálogo
        estiver realmente aberto/visível.
        """
        cad = self._get_cad_dock()
        if cad is None:
            return

        try:
            act = cad.enableAction()
        except Exception:
            act = None

        if checked:
            # mostra o painel CAD
            try:
                cad.show()
                cad.raise_()
            except Exception:
                try:
                    cad.setVisible(True)
                except Exception:
                    pass  # nosec B110

            # ativa o CAD nativo
            try:
                if act is not None and not act.isChecked():
                    act.trigger()
            except Exception:
                pass  # nosec B110

            # aplica e marca as opções do flutuador
            self._set_cad_floater_defaults()

        else:
            # só desativa o CAD se o diálogo do plugin estiver aberto/visível
            dialog_open = False
            try:
                dialog_open = self.isVisible()
            except Exception:
                dialog_open = False

            if dialog_open:
                try:
                    if act is not None and act.isChecked():
                        act.trigger()
                except Exception:
                    pass  # nosec B110

        # depois aplica e marca as opções do floater
        self._update_checkBoxMapTool_state()
#////////////////////////////////////////////
    def _init_scrollAreaGrafico(self):
        """
        Inicializa o gráfico de Canal x Terreno em pyqtgraph
        com melhor qualidade visual e crosshair interativo.
        """
        if not hasattr(self, "scrollAreaGrafico"):
            return

        container = self.scrollAreaGrafico.widget()
        if container is None:
            container = QWidget(self.scrollAreaGrafico)
            self.scrollAreaGrafico.setWidget(container)

        layout = container.layout()
        if layout is None:
            layout = QVBoxLayout(container)
            layout.setContentsMargins(0, 0, 0, 0)
            layout.setSpacing(0)
            container.setLayout(layout)

        pg.setConfigOptions(antialias=True)

        # remove plot antigo, se existir
        if hasattr(self, "_grafico_plot_widget") and self._grafico_plot_widget is not None:
            try:
                layout.removeWidget(self._grafico_plot_widget)
                self._grafico_plot_widget.deleteLater()
            except Exception:
                pass  # nosec B110

        self._grafico_plot_widget = pg.PlotWidget(parent=container, background=(15, 15, 15))
        layout.addWidget(self._grafico_plot_widget)

        plot_item = self._grafico_plot_widget.getPlotItem()
        plot_item.showGrid(x=True, y=True, alpha=0.25)
        plot_item.setLabel("bottom", self.tr("Comprimento (m)"))
        plot_item.setLabel("left", self.tr("Cota (m)"))

        vb = plot_item.getViewBox()
        vb.setDefaultPadding(0.08)

        axis_font = QFont()
        axis_font.setPointSize(9)
        axis_pen = pg.mkPen(220, 220, 220)

        for name in ("bottom", "left"):
            axis = plot_item.getAxis(name)
            axis.setTickFont(axis_font)
            axis.setTextPen(axis_pen)
            axis.setPen(axis_pen)

        # legenda
        self._grafico_legend = plot_item.addLegend(offset=(10, 10))
        try:
            self._grafico_legend.layout.setContentsMargins(4, 4, 4, 4)
        except Exception:
            pass  # nosec B110

        # curvas
        canal_pen = pg.mkPen(QColor(0, 170, 255), width=2)
        terreno_pen = pg.mkPen(QColor(255, 0, 255), width=1)

        self._grafico_canal_curve = plot_item.plot([], [], pen=canal_pen, name=self.tr("Canal"))
        self._grafico_terreno_curve = plot_item.plot([], [], pen=terreno_pen, name=self.tr("Terreno"))

        # amostras extras da legenda (quadradinhos)
        # usar ScatterPlotItem funciona melhor do que PlotDataItem para esse caso
        self._grafico_leg_abaixo_solo = pg.ScatterPlotItem(
            [0], [0],
            symbol="s",
            size=10,
            brush=pg.mkBrush(0, 120, 255, 140),
            pen=pg.mkPen(0, 120, 255))
        self._grafico_legend.addItem(self._grafico_leg_abaixo_solo, self.tr("Abaixo do Solo"))

        self._grafico_leg_acima_solo = pg.ScatterPlotItem(
            [0], [0],
            symbol="s",
            size=10,
            brush=pg.mkBrush(255, 60, 60, 140),
            pen=pg.mkPen(255, 60, 60))
        self._grafico_legend.addItem(self._grafico_leg_acima_solo, self.tr("Acima do Solo"))

        # lista de preenchimentos (acima/abaixo)
        self._grafico_fill_items = []

        # Crosshair / texto / ponto sincronizado
        # linhas infinita vertical/horizontal
        self._grafico_vline = pg.InfiniteLine(angle=90, movable=False, pen=pg.mkPen(200, 200, 200, 140))
        self._grafico_hline = pg.InfiniteLine(angle=0, movable=False, pen=pg.mkPen(200, 200, 200, 140))
        plot_item.addItem(self._grafico_vline, ignoreBounds=True)
        plot_item.addItem(self._grafico_hline, ignoreBounds=True)
        self._grafico_vline.hide()
        self._grafico_hline.hide()

        # texto com cotas / distância
        self._grafico_coord_text = pg.TextItem("", anchor=(0, 1))
        plot_item.addItem(self._grafico_coord_text)
        self._grafico_coord_text.hide()

        # ponto amarelo no local da leitura
        self._grafico_sync_point = plot_item.plot(
            [], [], pen=None,
            symbol="o", symbolSize=6,
            symbolBrush=pg.mkBrush(255, 255, 0),
            symbolPen=None)

        # proxy para limitar a taxa de eventos do mouse
        if hasattr(self, "_grafico_mouse_proxy") and self._grafico_mouse_proxy is not None:
            self._grafico_mouse_proxy = None

        self._grafico_mouse_proxy = pg.SignalProxy(
            self._grafico_plot_widget.scene().sigMouseMoved,
            rateLimit=60,
            slot=self._on_grafico_mouse_moved)

    def _clear_grafico_fill_between(self):
        """
        Remove todos os itens de preenchimento (FillBetween + curvas auxiliares)
        do gráfico.
        """
        plot = getattr(self, "_grafico_plot_widget", None)
        items = getattr(self, "_grafico_fill_items", None)
        if plot is None or items is None:
            return

        for it in items:
            try:
                plot.removeItem(it)
            except Exception:
                pass  # nosec B110

        self._grafico_fill_items = []

    def _update_grafico_fill_between(self):
        """
        Cria preenchimentos entre as curvas Canal x Terreno,
        colorindo por trechos:

        - Terreno acima do Canal  -> azul
        - Terreno abaixo do Canal -> vermelho

        Garante que nas interseções (onde as curvas se cruzam)
        o preenchimento vá até o ponto de cruzamento.
        """
        plot = getattr(self, "_grafico_plot_widget", None)
        canal_curve = getattr(self, "_grafico_canal_curve", None)
        terreno_curve = getattr(self, "_grafico_terreno_curve", None)

        if plot is None or canal_curve is None or terreno_curve is None:
            return

        # remove preenchimentos antigos
        self._clear_grafico_fill_between()

        # se o checkbox não estiver marcado, sai
        if not (
            hasattr(self, "checkBoxAcima_Abaixo")
            and self.checkBoxAcima_Abaixo is not None
            and self.checkBoxAcima_Abaixo.isChecked()):
            return

        xs_t, ys_t = terreno_curve.getData()
        xs_c, ys_c = canal_curve.getData()

        if xs_t is None or ys_t is None or xs_c is None or ys_c is None:
            return

        xs_t = list(xs_t)
        ys_t = list(ys_t)
        xs_c = list(xs_c)
        ys_c = list(ys_c)

        n = min(len(xs_t), len(xs_c), len(ys_t), len(ys_c))
        if n < 2:
            return

        xs_t = xs_t[:n]
        ys_t = ys_t[:n]
        ys_c = ys_c[:n]

        def sign(v, eps=1e-9):
            if v > eps:
                return 1
            if v < -eps:
                return -1
            return 0

        # 1) Insere ponto de interseção sempre que o sinal muda
        xs2 = [xs_t[0]]
        ys_t2 = [ys_t[0]]
        ys_c2 = [ys_c[0]]

        for i in range(n - 1):
            x0 = xs_t[i]
            x1 = xs_t[i + 1]
            yt0 = ys_t[i]
            yt1 = ys_t[i + 1]
            yc0 = ys_c[i]
            yc1 = ys_c[i + 1]

            d0 = yt0 - yc0
            d1 = yt1 - yc1

            # se há mudança de sinal entre i e i+1
            if d0 * d1 < 0.0:
                t = d0 / (d0 - d1)  # fração ao longo do segmento
                x_int = x0 + t * (x1 - x0)
                yt_int = yt0 + t * (yt1 - yt0)
                yc_int = yc0 + t * (yc1 - yc0)

                # força as duas curvas a terem exatamente o mesmo valor na interseção
                y_int = (yt_int + yc_int) * 0.5

                xs2.append(x_int)
                ys_t2.append(y_int)
                ys_c2.append(y_int)

            xs2.append(x1)
            ys_t2.append(yt1)
            ys_c2.append(yc1)

        # 2) Recalcula diff com os pontos de interseção
        diff2 = [ys_t2[i] - ys_c2[i] for i in range(len(xs2))]
        signs2 = [sign(d) for d in diff2]

        import pyqtgraph as pg

        self._grafico_fill_items = []

        m = len(xs2)
        i = 0
        while i < m:
            s = signs2[i]
            # pula pontos neutros isolados
            if s == 0:
                i += 1
                continue

            start = i
            i += 1
            # inclui também pontos onde o sinal é 0 (interseções) dentro do trecho
            while i < m and (signs2[i] == s or signs2[i] == 0):
                i += 1
            end = i - 1

            if end <= start:
                continue

            # <<< NOVO: se antes do início houver um 0, inclui esse ponto
            if start > 0 and signs2[start - 1] == 0:
                start -= 1
            # e se depois do fim houver um 0, inclui também
            if end < m - 1 and signs2[end + 1] == 0:
                end += 1

            seg_x = xs2[start:end + 1]
            seg_terr = ys_t2[start:end + 1]
            seg_canal = ys_c2[start:end + 1]

            # Quem está por cima / por baixo e cor da área
            if s > 0:
                # Terreno acima -> azul
                upper_y = seg_terr
                lower_y = seg_canal
                brush = pg.mkBrush(0, 120, 255, 90)
            else:
                # Terreno abaixo -> vermelho
                upper_y = seg_canal
                lower_y = seg_terr
                brush = pg.mkBrush(255, 60, 60, 90)

            upper_item = pg.PlotCurveItem(seg_x, upper_y, pen=None)
            lower_item = pg.PlotCurveItem(seg_x, lower_y, pen=None)

            plot.addItem(upper_item)
            plot.addItem(lower_item)

            fill = pg.FillBetweenItem(curve1=upper_item, curve2=lower_item, brush=brush)
            plot.addItem(fill)

            self._grafico_fill_items.extend([upper_item, lower_item, fill])

    def _update_grafico_canal_terreno(self, layer: QgsVectorLayer | None = None, fid: int | None = None):
        """
        Atualiza o gráfico no scrollAreaGrafico para a feição informada
        (ou feição selecionada da camada corrente).

        Terreno:
            - amostrado no DEM ao longo de uma linha densificada.
        Canal:
            - reta de projeto, usando:
                * cota inicial = terreno_inicial - Yn
                * declividade constante = 'Declividade(I)' (%)
        """
        plot = getattr(self, "_grafico_plot_widget", None)
        canal_curve = getattr(self, "_grafico_canal_curve", None)
        terreno_curve = getattr(self, "_grafico_terreno_curve", None)

        if plot is None or canal_curve is None or terreno_curve is None:
            return

        def _clear():
            canal_curve.setData([], [])
            terreno_curve.setData([], [])

        # Camada alvo
        if layer is None:
            layer = getattr(self, "_current_canal_layer", None)
        if not isinstance(layer, QgsVectorLayer):
            _clear()
            return

        # Determina o fid se não foi informado
        if fid is None:
            try:
                sel_ids = list(layer.selectedFeatureIds())
                if sel_ids:
                    fid = sel_ids[0]
            except Exception:
                fid = None

        if fid is None:
            _clear()
            return

        # Feição e geometria
        try:
            feat = layer.getFeature(fid)
        except Exception:
            _clear()
            return

        geom = feat.geometry()
        if geom is None or geom.isEmpty() or geom.type() != QgsWkbTypes.GeometryType.LineGeometry:
            _clear()
            return

        # Garante polyline simples
        if geom.isMultipart():
            linhas = geom.asMultiPolyline()
            if not linhas:
                _clear()
                return
            geom = QgsGeometry.fromPolylineXY(linhas[0])

        total_len = geom.length() or 0.0
        if total_len <= 0.0:
            _clear()
            return

        # Raster selecionado (DEM)
        raster = self._get_selected_raster_from_combo()
        if raster is None or not raster.isValid():
            _clear()
            return

        rprov = raster.dataProvider()

        # Densifica a linha para pegar vários pontos ao longo do canal
        alvo_amostras = 150
        passo = total_len / alvo_amostras
        passo = max(passo, 1.0)  # pelo menos 1 m

        geom_dens = geom.densifyByDistance(passo)

        if geom_dens.isMultipart():
            linhas = geom_dens.asMultiPolyline()
            pts = linhas[0] if linhas else []
        else:
            pts = geom_dens.asPolyline()

        if len(pts) < 2:
            _clear()
            return

        xs: list[float] = []
        zs_terreno: list[float] = []

        dist_acum = 0.0
        prev_pt = None

        def _extract_z(res):
            if isinstance(res, tuple):
                val, ok = res
                return float(val) if ok and val is not None else None
            return float(res) if res is not None else None

        for pt in pts:
            if prev_pt is not None:
                dx = pt.x() - prev_pt.x()
                dy = pt.y() - prev_pt.y()
                dist_acum += math.hypot(dx, dy)

            res = rprov.sample(QgsPointXY(pt.x(), pt.y()), 1)
            z = _extract_z(res)
            if z is not None:
                xs.append(dist_acum)
                zs_terreno.append(z)

            prev_pt = pt

        # precisa de pelo menos 2 pontos válidos
        if len(xs) < 2 or len(zs_terreno) < 2:
            _clear()
            return

        # Profundidade normal Yn (para deslocar o canal para baixo)
        depth = 0.0
        try:
            idx_yn = layer.fields().indexOf("Yn")
            if idx_yn >= 0:
                val = feat.attribute(idx_yn)
                if val is not None:
                    depth = float(val)
        except Exception:
            depth = 0.0

        # Declividade(I) em %
        decl_perc = 0.0
        try:
            idx_decl = layer.fields().indexOf("Declividade(I)")
            if idx_decl >= 0:
                val = feat.attribute(idx_decl)
                if val is not None:
                    decl_perc = float(val)
        except Exception:
            decl_perc = 0.0

        # Converte declividade para m/m (pode ser negativa)
        S = decl_perc / 100.0

        # PERFIL DO TERRENO
        terreno = zs_terreno

        # PERFIL DO CANAL: reta
        # cota inicial = terreno_inicial - Yn
        if depth > 0.0:
            z_canal_0 = terreno[0] - depth
        else:
            # se ainda não tiver Yn, desenha canal colado ao terreno, só pra não ficar vazio
            z_canal_0 = terreno[0]

        canal = [z_canal_0 - S * x for x in xs]

        terreno_curve.setData(xs, terreno)
        canal_curve.setData(xs, canal)

        # Ajusta ranges com folga
        xmin, xmax = min(xs), max(xs)
        ymin = min(min(terreno), min(canal))
        ymax = max(max(terreno), max(canal))
        pad_y = 1.0 if ymax == ymin else (ymax - ymin) * 0.1

        plot.setXRange(xmin, xmax)
        plot.setYRange(ymin - pad_y, ymax + pad_y)

        # Atualiza o sombreamento entre as curvas (se habilitado)
        try:
            self._update_grafico_fill_between()
        except Exception:
            pass  # nosec B110

        # Ajusta a visão com um pouco de padding vertical
        plot = getattr(self, "_grafico_plot_widget", None)
        if plot is not None:
            vb = plot.getPlotItem().getViewBox()
            vb.enableAutoRange(axis=pg.ViewBox.YAxis, enable=True)
            vb.enableAutoRange(axis=pg.ViewBox.XAxis, enable=True)

        self._update_pushButtonGraficoDXF_state() # Habilita para Exportar

    def _on_checkBoxAcima_Abaixo_toggled(self, checked: bool):
        self._update_grafico_fill_between()

    def _init_checkBoxAcima_Abaixo(self):
        """
        Conecta o checkBoxAcima_Abaixo para controlar o
        preenchimento entre as curvas Canal x Terreno.
        """
        if hasattr(self, "checkBoxAcima_Abaixo") and self.checkBoxAcima_Abaixo is not None:
            self.checkBoxAcima_Abaixo.toggled.connect(self._on_checkBoxAcima_Abaixo_toggled)

    def _update_grafico_from_selection(self):
        """
        Atualiza o gráfico Canal x Terreno (scrollAreaGrafico) com base em:
        - camada corrente (_current_canal_layer)
        - feição selecionada no tableViewFeicao (ou seleção da camada no QGIS)

        Se não houver feição/camada/raster válidos, o gráfico é limpo.
        """
        # garante que o gráfico existe
        if not hasattr(self, "_grafico_canal_curve") or self._grafico_canal_curve is None:
            return
        if not hasattr(self, "_grafico_terreno_curve") or self._grafico_terreno_curve is None:
            return

        layer = getattr(self, "_current_canal_layer", None)
        if not isinstance(layer, QgsVectorLayer):
            self._clear_grafico_canal_terreno()
            return

        # Descobre o fid selecionado
        fid = None

        # prioridade: seleção no tableViewFeicao
        if hasattr(self, "tableViewFeicao"):
            sel_model = self.tableViewFeicao.selectionModel()
            if sel_model is not None:
                idx = sel_model.currentIndex()
                if idx.isValid():
                    fid = idx.data(Qt.ItemDataRole.UserRole)

        # fallback: seleção da camada no QGIS
        if fid is None:
            sel_ids = list(layer.selectedFeatureIds())
            if sel_ids:
                fid = sel_ids[0]

        # fallback 2: se só tiver uma feição, usa ela
        if fid is None:
            try:
                if layer.featureCount() == 1:
                    for f in layer.getFeatures():
                        fid = f.id()
                        break
            except Exception:
                pass  # nosec B110

        if fid is None:
            self._clear_grafico_canal_terreno()
            return

        # Pega a feição / geometria
        try:
            feat = layer.getFeature(fid)
        except Exception:
            self._clear_grafico_canal_terreno()
            return

        geom = feat.geometry() if feat is not None else None
        if geom is None or geom.isEmpty():
            self._clear_grafico_canal_terreno()
            return

        if geom.type() != QgsWkbTypes.GeometryType.LineGeometry:
            self._clear_grafico_canal_terreno()
            return

        # guarda a geometria do perfil (para exportação da tabela com X/Y)
        try:
            self._grafico_profile_geom = QgsGeometry(geom)  # cópia segura
        except Exception:
            self._grafico_profile_geom = None

        # Raster para amostrar o terreno
        raster = self._get_selected_raster_from_combo()
        if raster is None or not raster.isValid():
            self._clear_grafico_canal_terreno()
            return

        rprov = raster.dataProvider()
        length = geom.length() or 0.0
        if length <= 0.0:
            self._clear_grafico_canal_terreno()
            return

        # Gera amostras ao longo da linha
        # no máx. ~150 pontos para não pesar
        target_spacing = max(1.0, length / 100.0)   # tentativa de ~100 amostras
        num_samples = max(2, int(length / target_spacing) + 1)

        xs = []
        z_terreno = []

        for i in range(num_samples):
            d = (length * i) / (num_samples - 1)
            try:
                pt = geom.interpolate(d).asPoint()
            except Exception:   # nosec B112
                continue

            res = rprov.sample(QgsPointXY(pt.x(), pt.y()), 1)
            if isinstance(res, tuple):
                z, ok = res
                if not ok or z is None:
                    continue
            else:
                z = res
                if z is None:
                    continue

            xs.append(float(d))
            z_terreno.append(float(z))

        if len(xs) < 2 or len(z_terreno) < 2:
            self._clear_grafico_canal_terreno()
            return

        # Gera linha do canal (reta)
        fields = layer.fields()
        idx_decl = fields.indexOf("Declividade(I)")
        idx_yn   = fields.indexOf("Yn")

        decl = 0.0
        yn   = 0.0

        try:
            if idx_decl >= 0:
                val = feat.attribute(idx_decl)
                if val is not None:
                    decl = float(val)
        except (TypeError, ValueError):
            decl = 0.0

        try:
            if idx_yn >= 0:
                val = feat.attribute(idx_yn)
                if val is not None:
                    yn = float(val)
        except (TypeError, ValueError):
            yn = 0.0

        # profundidade para posicionar canal abaixo do terreno
        if yn <= 0.0:
            yn = 0.0  # fallback: 0,0 m abaixo do terreno

        # declividade em m/m
        S = float(decl) / 100.0

        x0 = xs[0]
        z0_terreno = z_terreno[0]
        z0_canal = z0_terreno - yn

        z_canal = []
        for x in xs:
            # canal reto: z = z0_canal - S*(x - x0)
            zc = z0_canal - S * (x - x0)
            z_canal.append(zc)

        # Atualiza curvas
        self._grafico_canal_curve.setData(xs, z_canal)
        self._grafico_terreno_curve.setData(xs, z_terreno)

        # Atualiza preenchimentos (acima/abaixo)
        if hasattr(self, "_update_grafico_fill_between"):
            self._update_grafico_fill_between()

        # autoscale
        if hasattr(self, "_grafico_plot_widget") and self._grafico_plot_widget is not None:
            try:
                self._grafico_plot_widget.getPlotItem().getViewBox().autoRange()
            except Exception:
                pass  # nosec B110

    def _hide_grafico_crosshair(self):
        """
        Esconde crosshair, texto e ponto do gráfico Canal x Terreno.
        """
        if hasattr(self, "_grafico_vline") and self._grafico_vline is not None:
            self._grafico_vline.hide()
        if hasattr(self, "_grafico_hline") and self._grafico_hline is not None:
            self._grafico_hline.hide()
        if hasattr(self, "_grafico_coord_text") and self._grafico_coord_text is not None:
            self._grafico_coord_text.hide()
        if hasattr(self, "_grafico_sync_point") and self._grafico_sync_point is not None:
            # esvaziar dados já esconde o ponto
            self._grafico_sync_point.setData([], [])

    def _clear_grafico_canal_terreno(self):
        """
        Limpa o gráfico Canal x Terreno (curvas e preenchimentos).
        """
        if hasattr(self, "_grafico_canal_curve") and self._grafico_canal_curve is not None:
            self._grafico_canal_curve.setData([], [])

        if hasattr(self, "_grafico_terreno_curve") and self._grafico_terreno_curve is not None:
            self._grafico_terreno_curve.setData([], [])

        if hasattr(self, "_grafico_fill_items") and self._grafico_fill_items is not None:
            for item in self._grafico_fill_items:
                try:
                    self._grafico_plot_widget.removeItem(item)
                except Exception:
                    pass  # nosec B110
            self._grafico_fill_items = []

        # esconde crosshair / texto / ponto
        self._hide_grafico_crosshair()

        if hasattr(self, "_grafico_plot_widget") and self._grafico_plot_widget is not None:
            try:
                self._grafico_plot_widget.getPlotItem().getViewBox().autoRange()
            except Exception:
                pass  # nosec B110

    def _on_grafico_mouse_moved(self, evt):
        """
        Evento chamado quando o mouse é movido sobre o gráfico Canal x Terreno.
        Mostra crosshair, texto com distâncias/cotas e um ponto no gráfico,
        usando interpolação para ficar fluido mesmo com zoom.
        """
        # garante que temos gráfico e curvas
        if not hasattr(self, "_grafico_plot_widget") or self._grafico_plot_widget is None:
            return
        if not hasattr(self, "_grafico_canal_curve") or self._grafico_canal_curve is None:
            return
        if not hasattr(self, "_grafico_terreno_curve") or self._grafico_terreno_curve is None:
            return

        plot_item = self._grafico_plot_widget.getPlotItem()

        # evt vem da SignalProxy: normalmente (pos,) 
        if isinstance(evt, (list, tuple)):
            pos = evt[0]
        else:
            pos = evt

        if not isinstance(pos, QPointF):
            return

        # verifica se o mouse está dentro da área do gráfico
        if not plot_item.sceneBoundingRect().contains(pos):
            self._hide_grafico_crosshair()
            return

        # coordenadas do mouse no sistema do gráfico
        mouse_point = plot_item.vb.mapSceneToView(pos)
        x = mouse_point.x()
        y_mouse = mouse_point.y()  # usado só pra saber de qual curva chegar mais perto

        xs_c, ys_c = self._grafico_canal_curve.getData()
        xs_t, ys_t = self._grafico_terreno_curve.getData()

        if xs_c is None or ys_c is None or xs_t is None or ys_t is None:
            self._hide_grafico_crosshair()
            return

        xs_c = list(xs_c)
        ys_c = list(ys_c)
        xs_t = list(xs_t)
        ys_t = list(ys_t)

        if not xs_c or not xs_t:
            self._hide_grafico_crosshair()
            return

        # assumimos que Canal e Terreno compartilham o mesmo eixo X (como montamos no update)
        xs = xs_c if len(xs_c) <= len(xs_t) else xs_t

        # garante que xs esteja em ordem crescente (por segurança)
        if xs[0] > xs[-1]:
            xs = xs[::-1]
            ys_c = ys_c[::-1]
            ys_t = ys_t[::-1]

        x_min, x_max = xs[0], xs[-1]
        if x < x_min or x > x_max:
            self._hide_grafico_crosshair()
            return

        # Interpolação linear nos dois conjuntos (Canal e Terreno)
        i = bisect.bisect_left(xs, x)

        # escolhe o segmento [i-1, i] ou bordas
        if i <= 0:
            x0, x1 = xs[0], xs[1]
            yc0, yc1 = ys_c[0], ys_c[1]
            yt0, yt1 = ys_t[0], ys_t[1]
        elif i >= len(xs):
            x0, x1 = xs[-2], xs[-1]
            yc0, yc1 = ys_c[-2], ys_c[-1]
            yt0, yt1 = ys_t[-2], ys_t[-1]
        else:
            x0, x1 = xs[i-1], xs[i]
            yc0, yc1 = ys_c[i-1], ys_c[i]
            yt0, yt1 = ys_t[i-1], ys_t[i]

        if x1 == x0:
            t = 0.0
        else:
            t = (x - x0) / (x1 - x0)

        # y interpolado para Canal e Terreno
        y_canal = float(yc0 + t * (yc1 - yc0))
        y_terreno = float(yt0 + t * (yt1 - yt0))

        # decide em qual curva ancorar a linha horizontal (mais próxima do mouse)
        if abs(y_mouse - y_canal) <= abs(y_mouse - y_terreno):
            y_val = y_canal
        else:
            y_val = y_terreno

        x_val = x  # aqui é contínuo, não travado no ponto da série

        # Atualiza crosshair
        if hasattr(self, "_grafico_vline") and self._grafico_vline is not None:
            self._grafico_vline.setPos(x_val)
            self._grafico_vline.show()

        if hasattr(self, "_grafico_hline") and self._grafico_hline is not None:
            self._grafico_hline.setPos(y_val)
            self._grafico_hline.show()

        # Texto com distâncias / cotas
        if hasattr(self, "_grafico_coord_text") and self._grafico_coord_text is not None:
            html = (
                "<div style='color:white;'>"
                + self.tr("<b>Distância:</b> {x_val:.2f} m<br>").format(x_val=x_val)
                + self.tr("<span style='color:#00AAFF;'><b>Canal:</b> {y_canal:.2f} m</span><br>").format(y_canal=y_canal)
                + self.tr("<span style='color:#FF64FF;'><b>Terreno:</b> {y_terreno:.2f} m</span>").format(y_terreno=y_terreno)
                + "</div>")
            self._grafico_coord_text.setHtml(html)
            self._grafico_coord_text.setPos(x_val, y_val)
            self._grafico_coord_text.show()

        # Ponto amarelo na posição
        if hasattr(self, "_grafico_sync_point") and self._grafico_sync_point is not None:
            self._grafico_sync_point.setData([x_val], [y_val])
#////////////////////////////////////////////
    def _init_pushButtonCamadaDXF(self):
        """
        Conecta o pushButtonCamadaDXF ao exportador DXF.
        """
        btn = getattr(self, "pushButtonCamadaDXF", None)
        if btn is None:
            return

        # garante que não duplica conexões
        try:
            btn.clicked.disconnect()
        except Exception:
            pass  # nosec B110

        # Conecta o botão
        btn.clicked.connect(self._on_pushButtonCamadaDXF_clicked)

        # (opcional, mas recomendado) já atualiza o enabled conforme seleção/feições
        try:
            self._update_pushButtonCamadaDXF_state()
        except Exception:
            pass  # nosec B110

    def escolher_local_para_salvar(self, nome_padrao, tipo_arquivo):
        """
        Permite ao usuário escolher um local e um nome de arquivo para salvar uma camada,
        lembrando o último diretório e evitando sobreposição.

        :param nome_padrao: ex: "MinhaCamada.dxf"
        :param tipo_arquivo: ex: "Arquivos DXF (*.dxf)"
        :return: caminho completo ou None se cancelado
        """
        settings = QSettings()

        # Use uma chave "sua" (melhor do que "lastDir" genérico)
        lastDir = settings.value("tempo_salvo_tools/lastDir", "", type=str)
        if not lastDir or not os.path.isdir(lastDir):
            lastDir = os.path.expanduser("~")

        base_nome_padrao, extensao = os.path.splitext(nome_padrao)
        if not extensao:
            # fallback simples: tenta extrair extensão do filtro
            # exemplo "Arquivos DXF (*.dxf)" -> ".dxf"
            ext_guess = ".dxf" if ".dxf" in tipo_arquivo.lower() else ""
            extensao = ext_guess

        numero = 1
        nome_proposto = base_nome_padrao

        while os.path.exists(os.path.join(lastDir, nome_proposto + extensao)):
            nome_proposto = f"{base_nome_padrao}_{numero}"
            numero += 1

        nome_completo_proposto = os.path.join(lastDir, nome_proposto + extensao)

        options = QFileDialog.Options()
        parent = getattr(self, "dlg", self)  # funciona tanto se você tiver self.dlg quanto não

        fileName, _ = QFileDialog.getSaveFileName(
            parent, self.tr("Salvar Camada"), nome_completo_proposto, tipo_arquivo, options=options)

        if fileName:
            settings.setValue("tempo_salvo_tools/lastDir", os.path.dirname(fileName))

            if extensao and not fileName.lower().endswith(extensao.lower()):
                fileName += extensao

            return fileName

        return None

    def calcular_angulo_entre_pontos(self, p1: QgsPointXY, p2: QgsPointXY) -> float:
        """
        Ângulo (graus) do segmento p1->p2, baseado em atan2(dy, dx).
        Ajusta para manter texto "em pé" (evita ficar de cabeça pra baixo).
        """
        dx = p2.x() - p1.x()
        dy = p2.y() - p1.y()
        ang = math.degrees(math.atan2(dy, dx))  # -180..180

        # Mantém texto legível (evita upside-down)
        if ang > 90:
            ang -= 180
        elif ang < -90:
            ang += 180
        return ang

    def calcular_rotulo_centralizado(self, geometry: QgsGeometry):
        """
        Identifica o segmento mais longo de uma geometria e retorna:
        (ângulo_em_graus, ponto_central_QgsPointXY).
        """
        if geometry is None or geometry.isEmpty():
            return 0.0, None

        # Curvas -> linhas (segurança)
        try:
            if hasattr(geometry, "wkbType"):
                from qgis.core import QgsWkbTypes
                if QgsWkbTypes.isCurvedType(geometry.wkbType()):
                    geometry = geometry.curveToLine()
        except Exception:
            pass  # nosec B110

        max_length = -1.0
        best_center = None
        best_angle = 0.0

        # Multipart ou single
        if geometry.isMultipart():
            lines = geometry.asMultiPolyline()
        else:
            lines = [geometry.asPolyline()]

        for line in lines:
            if not line or len(line) < 2:
                continue

            for i in range(len(line) - 1):
                a = QgsPointXY(line[i])
                b = QgsPointXY(line[i + 1])
                seg_len = a.distance(b)

                if seg_len > max_length:
                    max_length = seg_len
                    best_center = QgsPointXY((a.x() + b.x()) / 2.0, (a.y() + b.y()) / 2.0)
                    best_angle = self.calcular_angulo_entre_pontos(a, b)

        return best_angle, best_center

    def _on_pushButtonCamadaDXF_clicked(self):
        """
        Ao clicar, abre um diálogo:
        - DXF2D: exporta com linetype SETAS (>>)
        - DXF3D: exporta 3D normal (usa a sua função 3D já existente)
        """
        layer = self._get_selected_layer_from_tableViewCamada()
        if not isinstance(layer, QgsVectorLayer) or not layer.isValid():
            QMessageBox.warning(getattr(self, "dlg", self), "DXF", self.tr("Nenhuma camada válida selecionada no tableViewCamada."))
            return

        mode = self._ask_dxf_export_mode_dialog()
        if mode is None:
            return  # cancelado

        if mode == "2D":
            out_path = self.escolher_local_para_salvar(layer.name() + "_2D.dxf", self.tr("Arquivos DXF (*.dxf)"))
            if not out_path:
                return
            ok, err = self._export_layer_to_dxf_2d_setas_com_rotulos(layer, out_path)
        else:
            out_path = self.escolher_local_para_salvar(layer.name() + "_3D.dxf", self.tr("Arquivos DXF (*.dxf)"))
            if not out_path:
                return
            # Reaproveita a sua exportação 3D normal (já definida)
            ok, err = self._export_layer_to_dxf_3d_com_rotulos(layer, out_path)

        # 6) Mensagens finais (SEM QMessageBox)
        if ok:
            self.mostrar_mensagem(self.tr("DXF exportado com sucesso: {file_name}").format(file_name=os.path.basename(out_path)), "Sucesso", duracao=2, caminho_pasta=os.path.dirname(out_path), caminho_arquivo=out_path, forcar=True)
        else:
            self.mostrar_mensagem(self.tr("Falha ao exportar DXF: {error}").format(error=err or self.tr("erro desconhecido.")), "Erro", duracao=2, forcar=True)

    def _ask_dxf_export_mode_dialog(self):
        """
        Retorna "2D", "3D" ou None (cancelado).
        """
        parent = getattr(self, "dlg", self)
        dlg = QDialog(parent)
        dlg.setWindowTitle(self.tr("Exportar DXF"))
        dlg.setModal(True)

        lay = QVBoxLayout(dlg)
        lay.addWidget(QLabel(self.tr("Selecione o modo de exportação:")))

        rb2d = QRadioButton(self.tr("DXF2D (linetype SETAS >>)"))
        rb3d = QRadioButton(self.tr("DXF3D (linha normal 3D)"))
        rb2d.setChecked(True)

        bg = QButtonGroup(dlg)
        bg.addButton(rb2d)
        bg.addButton(rb3d)

        lay.addWidget(rb2d)
        lay.addWidget(rb3d)

        buttons = QDialogButtonBox(QDialogButtonBox.StandardButton.Ok | QDialogButtonBox.StandardButton.Cancel)

        buttons.accepted.connect(dlg.accept)
        buttons.rejected.connect(dlg.reject)
        lay.addWidget(buttons)

        if dlg.exec() != QDialog.DialogCode.Accepted:
            return None

        return self.tr("2D") if rb2d.isChecked() else ("3D")

    def _dxf_add_linetype_setas(self, doc, linetype_name="SETAS", scale_factor=1.0):
        """
        Mesma lógica do UiManager (linetype complexo com texto ">>").
        scale_factor fixo em 1.0 (ou o valor que você passar).
        """
        # Ajuste da escala dos componentes do padrão
        scale_symbol = 0.5 * float(scale_factor)
        long_dash = 0.3 * float(scale_factor)
        short_dash = 0.5 * float(scale_factor)
        space_between_dashes = 0.1 * float(scale_factor)

        # texto ">>" centralizado na linha (X/Y ajustados)
        shape_code = f"[\">>\",STANDARD,S={scale_symbol},R=0.0,X=-0.25,Y=-0.25]"

        single_pattern_length = long_dash + short_dash + space_between_dashes + scale_symbol
        pattern_str = (
            f"A,{long_dash},{-space_between_dashes},{short_dash},{-space_between_dashes},"
            f"{shape_code},{-space_between_dashes},{short_dash},{-space_between_dashes},{long_dash}")

        if linetype_name not in doc.linetypes:
            doc.linetypes.add(
                name=linetype_name,
                pattern=pattern_str,
                description=self.tr("Linha com setas ---->>---->>---->>"),
                length=single_pattern_length)

    def _export_layer_to_dxf_2d_setas_com_rotulos(self, layer, out_path: str):
        """
        DXF2D:
        - linhas: LWPOLYLINE (2D) com linetype SETAS
        - cores da linha: por Declividade (campo "I")
        - rótulos: TEXT rotacionado (calcular_rotulo_centralizado)
        - cor do rótulo: definida aqui (ajuste em _get_dxf_rotulo_rgb)
        """
        def iter_parts_as_xy(geom):
            if geom is None or geom.isEmpty():
                return []
            try:
                if QgsWkbTypes.isCurvedType(geom.wkbType()):
                    geom = geom.curveToLine()
            except Exception:
                pass  # nosec B110

            parts = []
            if geom.isMultipart():
                for g in geom.asGeometryCollection():
                    pts = [(float(p.x()), float(p.y())) for p in g.vertices()]
                    if len(pts) >= 2:
                        parts.append(pts)
            else:
                pts = [(float(p.x()), float(p.y())) for p in geom.vertices()]
                if len(pts) >= 2:
                    parts.append(pts)
            return parts

        def safe_float(v):
            try:
                f = float(v)
                if not math.isnan(f):
                    return f
            except Exception:
                pass  # nosec B110
            return None

        def _get_dxf_rotulo_rgb():
            # AJUSTE AQUI a cor do rótulo (RGB)
            # Exemplo: amarelo suave
            return (255, 230, 120)

        def _ramp_rgb(t):
            """
            Ramp simples p/ declividade:
            t=0 (baixa) -> azul
            t=1 (alta)  -> vermelho
            """
            t = max(0.0, min(1.0, float(t)))
            r1, g1, b1 = (0, 170, 255)
            r2, g2, b2 = (255, 80, 0)
            r = int(r1 + (r2 - r1) * t)
            g = int(g1 + (g2 - g1) * t)
            b = int(b1 + (b2 - b1) * t)
            return (r, g, b)

        # Cria DXF
        doc = ezdxf.new("R2010")
        msp = doc.modelspace()

        # ajuda o viewer a mostrar linetype
        try:
            doc.header["$LTSCALE"] = 1.0
            doc.header["$CELTSCALE"] = 1.0
        except Exception:
            pass  # nosec B110

        # Layers DXF
        dxf_layer_lines = layer.name()[:255]
        dxf_layer_text = (layer.name() + "_ROTULOS")[:255]
        try:
            if dxf_layer_lines not in doc.layers:
                doc.layers.new(dxf_layer_lines)
            if dxf_layer_text not in doc.layers:
                doc.layers.new(dxf_layer_text)
        except Exception:
            dxf_layer_lines = "0"
            dxf_layer_text = "0"

        # Linetype SETAS (scale_factor = 1)
        try:
            self._dxf_add_linetype_setas(doc, linetype_name="SETAS", scale_factor=1.0)
        except Exception:
            pass  # nosec B110

        # Campo CN e Declividade (I)
        fields = layer.fields()
        idx_cn = fields.indexOf("CN") if fields is not None else -1
        idx_i = fields.indexOf("I") if fields is not None else -1

        # min/max de I para normalizar
        i_vals = []
        if idx_i >= 0:
            for ft in layer.getFeatures():
                fv = safe_float(ft.attribute(idx_i))
                if fv is not None:
                    i_vals.append(fv)
        i_min = min(i_vals) if i_vals else 0.0
        i_max = max(i_vals) if i_vals else 1.0
        denom = (i_max - i_min) if (i_max - i_min) != 0 else 1.0

        text_height = 2.5
        rotulo_rgb = _get_dxf_rotulo_rgb()
        rotulo_true = ezdxf.colors.rgb2int(rotulo_rgb)

        # Exporta feições
        for feat in layer.getFeatures():
            geom = feat.geometry()
            if geom is None or geom.isEmpty():
                continue

            # cor por declividade
            if idx_i >= 0:
                fv = safe_float(feat.attribute(idx_i))
                if fv is None:
                    t = 0.0
                else:
                    t = (fv - i_min) / denom
            else:
                t = 0.0

            line_rgb = _ramp_rgb(t)
            line_true = ezdxf.colors.rgb2int(line_rgb)

            # Linhas 2D com SETAS
            for pts_xy in iter_parts_as_xy(geom):
                if len(pts_xy) < 2:
                    continue
                try:
                    msp.add_lwpolyline(
                        pts_xy,
                        dxfattribs={"layer": dxf_layer_lines, "true_color": line_true, "linetype": "SETAS", "ltscale": 1.0})
                except Exception:
                    pass  # nosec B110

            # Rótulo (centralizado no segmento mais longo)
            try:
                ang, center = self.calcular_rotulo_centralizado(geom)
                if center is None:
                    continue

                x = float(center.x())
                y = float(center.y())

                if idx_cn >= 0:
                    txt = str(feat.attribute(idx_cn) or "").strip()
                else:
                    txt = ""
                if not txt:
                    txt = str(feat.id())

                t_ent = msp.add_text(
                    txt,
                    dxfattribs={"layer": dxf_layer_text, "height": float(text_height), "rotation": float(ang), "true_color": rotulo_true})
                t_ent.dxf.insert = (x, y)

                try:
                    t_ent.set_placement((x, y), align="MIDDLE_CENTER")
                except Exception:
                    try:
                        t_ent.set_pos((x, y), align="MIDDLE_CENTER")
                    except Exception:
                        pass  # nosec B110

            except Exception:
                pass  # nosec B110

        try:
            doc.saveas(out_path)
        except Exception as e:
            return False, self.tr("Erro ao salvar DXF: {error}").format(error=str(e))

        return True, None

    def _export_layer_to_dxf_3d_com_rotulos(self, layer: QgsVectorLayer, out_path: str):
        """
        Exporta TODAS as feições da camada para DXF usando ezdxf:
        - Geometrias: Polyline3D (3D)
        - Rótulos: TEXT rotacionado (usa calcular_rotulo_centralizado)
        - Cores: definidas por Declividade(I) (mesma lógica do apply_cn_labeling)
        """
        # Raster opcional: se a geometria não tiver Z, tentamos amostrar Z do raster selecionado
        raster = None
        try:
            raster = self._get_selected_raster_from_combo()
            if raster is not None and not raster.isValid():
                raster = None
        except Exception:
            raster = None

        def sample_z(x: float, y: float):
            if raster is None:
                return None
            try:
                if not raster.extent().contains(QgsPointXY(x, y)):
                    return None
                val, ok = raster.dataProvider().sample(QgsPointXY(x, y), 1)
                if ok:
                    z = float(val)
                    if not math.isnan(z):
                        return z
            except Exception:
                pass  # nosec B110
            return None

        def point_z_from_qgspoint(pt):
            try:
                z = float(pt.z())
                if not math.isnan(z):
                    return z
            except Exception:
                pass  # nosec B110
            return None

        def iter_parts_as_points(geom: QgsGeometry):
            """
            Retorna lista de partes, cada parte = lista de QgsPoint (com Z se existir).
            """
            if geom is None or geom.isEmpty():
                return []

            # Curvas -> linhas
            try:
                if QgsWkbTypes.isCurvedType(geom.wkbType()):
                    geom = geom.curveToLine()
            except Exception:
                pass  # nosec B110

            parts = []
            if geom.isMultipart():
                for g in geom.asGeometryCollection():
                    pts = [p for p in g.vertices()]
                    if len(pts) >= 2:
                        parts.append(pts)
            else:
                pts = [p for p in geom.vertices()]
                if len(pts) >= 2:
                    parts.append(pts)
            return parts

        def rgb_to_truecolor(r: int, g: int, b: int) -> int:
            return (int(r) << 16) + (int(g) << 8) + int(b)

        # >>> CORES (mesma lógica do seu apply_cn_labeling)
        # Declividade(I) < 0  -> vermelho (255,0,0)
        # Declividade(I) >= 0 -> azul (0,102,204)  #0066CC
        field_decl = "Declividade(I)"
        idx_decl = layer.fields().indexOf(field_decl) if layer.fields() is not None else -1

        def truecolor_from_declividade(feat: QgsFeature) -> int:
            v = None
            try:
                if idx_decl >= 0:
                    v = feat.attribute(idx_decl)
                else:
                    # se por algum motivo o index falhar, tenta por nome
                    v = feat[field_decl]
            except Exception:
                v = None

            try:
                fv = float(v)
            except Exception:
                fv = 0.0  # fallback: trata como >=0 (azul)

            if fv < 0.0:
                return rgb_to_truecolor(255, 0, 0)       # vermelho
            return rgb_to_truecolor(0, 0, 255)         # azul #0066CC

        # Cria DXF
        doc = ezdxf.new("R2010")
        msp = doc.modelspace()

        # Layers DXF (um pra linhas, outro pra rótulos)
        dxf_layer_lines = layer.name()[:255]
        dxf_layer_text = (layer.name() + "_ROTULOS")[:255]
        try:
            if dxf_layer_lines not in doc.layers:
                doc.layers.new(dxf_layer_lines)
            if dxf_layer_text not in doc.layers:
                doc.layers.new(dxf_layer_text)
        except Exception:
            dxf_layer_lines = "0"
            dxf_layer_text = "0"

        # Parâmetros simples de texto (em unidades do desenho)
        text_height = 2.5

        # Campo do rótulo (se existir)
        fields = layer.fields()
        idx_cn = fields.indexOf("CN") if fields is not None else -1

        # Exporta feições
        for feat in layer.getFeatures():
            geom = feat.geometry()
            if geom is None or geom.isEmpty():
                continue

            # Cor por feição baseada na Declividade(I)
            ent_truecolor = truecolor_from_declividade(feat)

            # Linhas 3D
            for pts in iter_parts_as_points(geom):
                poly3d = []
                for p in pts:
                    x = float(p.x())
                    y = float(p.y())

                    z = point_z_from_qgspoint(p)
                    if z is None:
                        z = sample_z(x, y)
                    if z is None:
                        z = 0.0

                    poly3d.append((x, y, float(z)))

                if len(poly3d) >= 2:
                    try:
                        msp.add_polyline3d(
                            poly3d,
                            dxfattribs={"layer": dxf_layer_lines, "true_color": int(ent_truecolor)})
                    except Exception:
                        pass  # nosec B110

            # Rótulo
            try:
                ang, center = self.calcular_rotulo_centralizado(geom)
                if center is None:
                    continue

                x = float(center.x())
                y = float(center.y())

                z = sample_z(x, y)
                if z is None:
                    zs = []
                    for pts in iter_parts_as_points(geom):
                        for p in pts:
                            zz = point_z_from_qgspoint(p)
                            if zz is not None:
                                zs.append(float(zz))
                    z = (sum(zs) / len(zs)) if zs else 0.0

                # texto do rótulo
                if idx_cn >= 0:
                    txt = str(feat.attribute(idx_cn) or "").strip()
                else:
                    txt = ""
                if not txt:
                    txt = str(feat.id())

                t = msp.add_text(
                    txt,
                    dxfattribs={
                        "layer": dxf_layer_text,
                        "height": text_height,
                        "rotation": float(ang),
                        "true_color": int(ent_truecolor)})  # mesma cor do critério

                t.dxf.insert = (x, y, float(z))

                try:
                    t.set_placement((x, y, float(z)), align="MIDDLE_CENTER")
                except Exception:
                    try:
                        t.set_pos((x, y, float(z)), align="MIDDLE_CENTER")
                    except Exception:
                        pass  # nosec B110

            except Exception:
                pass  # nosec B110

        try:
            doc.saveas(out_path)
        except Exception as e:
            return False, self.tr("Erro ao salvar DXF: {error}").format(error=str(e))

        return True, None

    def _qcolor_to_truecolor(self, qc):
        """
        Converte QColor -> true_color (0xRRGGBB) usado pelo ezdxf.
        DXF não suporta alpha; ignoramos transparência.
        """
        try:
            return (int(qc.red()) << 16) + (int(qc.green()) << 8) + int(qc.blue())
        except Exception:
            return None

    def _get_symbol_qcolor_for_feature(self, layer: QgsVectorLayer, feat: QgsFeature):
        """
        Tenta obter a cor (QColor) do símbolo aplicado à feição via renderer.
        """
        try:
            ctx = QgsRenderContext.fromMapSettings(self.iface.mapCanvas().mapSettings())
            # melhora avaliação de expressões do renderer (categorizado/regras)
            try:
                ctx.expressionContext().appendScopes(
                    QgsExpressionContextUtils.globalProjectLayerScopes(layer))
            except Exception:
                pass  # nosec B110

            renderer = layer.renderer()
            if renderer is None:
                return None

            sym = renderer.symbolForFeature(feat, ctx)
            if sym is None:
                return None

            # QColor principal do símbolo
            return sym.color()
        except Exception:
            return None

    def _get_label_qcolor_for_layer(self, layer: QgsVectorLayer):
        """
        Tenta obter a cor do rótulo (QColor) do labeling (quando for SimpleLabeling).
        Se não der, retorna None.
        """
        try:
            if not layer.labelsEnabled():
                return None

            labeling = layer.labeling()
            if labeling is None:
                return None

            # Em muitos casos (SimpleLabeling), existe .settings()
            if not hasattr(labeling, "settings"):
                return None

            pal = labeling.settings()  # QgsPalLayerSettings
            fmt = pal.format()         # QgsTextFormat
            return fmt.color()         # QColor
        except Exception:
            return None

    def _get_selected_layer_from_tableViewCamada(self) -> QgsVectorLayer | None:
        """
        Retorna a camada selecionada no tableViewCamada (grupo CANAIS),
        ou None se não houver seleção válida.
        """
        if not hasattr(self, "tableViewCamada") or self.tableViewCamada is None:
            return None

        sel_model = self.tableViewCamada.selectionModel()
        if sel_model is None or not sel_model.hasSelection():
            return None

        # Preferir selectedRows (seleção real), fallback para currentIndex
        rows = sel_model.selectedRows(0)
        idx = rows[0] if rows else self.tableViewCamada.currentIndex()
        if not idx.isValid():
            return None

        layer_id = idx.data(Qt.ItemDataRole.UserRole)
        if not layer_id:
            return None

        try:
            lyr = QgsProject.instance().mapLayer(layer_id)
        except Exception:
            return None

        return lyr if isinstance(lyr, QgsVectorLayer) else None

    def _layer_has_any_feature(self, layer: QgsVectorLayer) -> bool:
        """
        True se a camada tiver pelo menos 1 feição (robusto mesmo com providers
        onde featureCount pode ser impreciso/atrasado).
        """
        if not isinstance(layer, QgsVectorLayer):
            return False

        try:
            if layer.featureCount() > 0:
                return True
        except Exception:
            pass  # nosec B110

        # Fallback: tenta buscar 1 feição
        try:
            from qgis.core import QgsFeatureRequest
            it = layer.getFeatures(QgsFeatureRequest().setLimit(1))
            for _ in it:
                return True
        except Exception:
            pass  # nosec B110

        return False

    def _update_pushButtonCamadaDXF_state(self):
        """
        Habilita o pushButtonCamadaDXF somente se:
        - houver linha selecionada no tableViewCamada
        - e a camada selecionada tiver feições
        """
        if not hasattr(self, "pushButtonCamadaDXF") or self.pushButtonCamadaDXF is None:
            return

        layer = self._get_selected_layer_from_tableViewCamada()
        ok = False

        if isinstance(layer, QgsVectorLayer):
            # opcional: garantir que é linha
            try:
                ok_geom = (layer.geometryType() == QgsWkbTypes.GeometryType.LineGeometry)
            except Exception:
                ok_geom = True

            if ok_geom and self._layer_has_any_feature(layer):
                ok = True

        self.pushButtonCamadaDXF.setEnabled(ok)
#////////////////////////////////////////////
    def _init_pushButtonGraficoDXF(self):
        """Conecta e inicializa o botão de exportação do gráfico para DXF."""
        btn = getattr(self, "pushButtonGraficoDXF", None)
        if btn is None:
            return

        try:
            btn.clicked.disconnect()
        except Exception:
            pass  # nosec B110

        btn.clicked.connect(self._on_pushButtonGraficoDXF_clicked)
        self._update_pushButtonGraficoDXF_state()

    def _update_pushButtonGraficoDXF_state(self) -> bool:
        """
        Habilita o pushButtonGraficoDXF somente se:
        - existir curva de Canal e Terreno
        - ambas tiverem >= 2 pontos válidos
        """
        btn = getattr(self, "pushButtonGraficoDXF", None)
        if btn is None:
            return False

        xs_t, ys_t = self._grafico_get_curve_xy(getattr(self, "_grafico_terreno_curve", None))
        xs_c, ys_c = self._grafico_get_curve_xy(getattr(self, "_grafico_canal_curve", None))

        ok = (len(xs_t) >= 2 and len(xs_c) >= 2 and len(ys_t) >= 2 and len(ys_c) >= 2)
        btn.setEnabled(ok)
        return ok

    def _grafico_get_curve_xy(self, curve):
        """Extrai (xs, ys) do PlotDataItem do pyqtgraph, filtrando NaN/None."""
        if curve is None:
            return [], []
        try:
            xs, ys = curve.getData()
        except Exception:
            return [], []

        if xs is None or ys is None:
            return [], []

        out_x, out_y = [], []
        import math
        n = min(len(xs), len(ys))
        for i in range(n):
            try:
                x = float(xs[i])
                y = float(ys[i])
                if math.isnan(x) or math.isnan(y):
                    continue
                out_x.append(x)
                out_y.append(y)
            except Exception:  # nosec B112
                continue
        return out_x, out_y

    def _on_pushButtonGraficoDXF_clicked(self):
        """Handler do botão: escolhe caminho, exporta e mostra mensagem via mostrar_mensagem()."""
        if not self._update_pushButtonGraficoDXF_state():
            self.mostrar_mensagem(self.tr("Nada para exportar: gere/atualize o gráfico antes."), "Info")
            return

        # Usa sua função (você já tem/usa esse padrão no plugin)
        if not hasattr(self, "escolher_local_para_salvar"):
            self.mostrar_mensagem(self.tr("Função escolher_local_para_salvar não encontrada no plugin."), "Erro")
            return

        out_path = self.escolher_local_para_salvar(self.tr("Grafico_Perfil.dxf"), self.tr("Arquivos DXF (*.dxf)"))
        if not out_path:
            return

        include_hatch = bool(
            hasattr(self, "checkBoxAcima_Abaixo")
            and self.checkBoxAcima_Abaixo is not None
            and self.checkBoxAcima_Abaixo.isChecked())

        include_table = bool(
            hasattr(self, "checkBoxTabela")
            and self.checkBoxTabela is not None
            and self.checkBoxTabela.isChecked())

        ok, err = self._export_grafico_perfil_to_dxf(out_path, include_hatch=include_hatch, include_table=include_table)
        if not ok:
            self.mostrar_mensagem(err or self.tr("Falha ao exportar gráfico para DXF."), "Erro")
            return

        self.mostrar_mensagem(self.tr("Gráfico exportado para DXF com sucesso."), "Sucesso", caminho_pasta=os.path.dirname(out_path), caminho_arquivo=out_path)

    def _export_grafico_perfil_to_dxf(self, out_path: str, *, include_hatch: bool = True, include_table: bool = True):
        """
        Exporta o gráfico Canal x Terreno para DXF:
        - 2 polylines (Terreno e Canal)
        - HACHURA sólida + transparência 60% entre as curvas (opcional)
        - Eixos/moldura e caixas de cota (usa suas funções auxiliares)
        """
        # Dados do gráfico (curvas)
        xs_t, ys_t = self._grafico_get_curve_xy(getattr(self, "_grafico_terreno_curve", None))
        xs_c, ys_c = self._grafico_get_curve_xy(getattr(self, "_grafico_canal_curve", None))
        if len(xs_t) < 2 or len(xs_c) < 2:
            return False, self.tr("Curvas insuficientes para exportação.")

        # Para hatch: alinhar canal/terreno no mesmo X
        def interp_y(xs_src, ys_src, xq):
            if not xs_src:
                return None
            if xq <= xs_src[0]:
                return ys_src[0]
            if xq >= xs_src[-1]:
                return ys_src[-1]
            lo, hi = 0, len(xs_src) - 1
            while hi - lo > 1:
                mid = (lo + hi) // 2
                if xs_src[mid] <= xq:
                    lo = mid
                else:
                    hi = mid
            xa, xb = xs_src[lo], xs_src[hi]
            ya, yb = ys_src[lo], ys_src[hi]
            if abs(xb - xa) < 1e-12:
                return ya
            t = (xq - xa) / (xb - xa)
            return ya + t * (yb - ya)

        # DXF setup
        doc = ezdxf.new("R2010")
        msp = doc.modelspace()

        # Layers
        L_TERR = "GRAFICO_TERRENO"
        L_CAN  = "GRAFICO_CANAL"
        L_HA   = "GRAFICO_HACHURA_ACIMA"
        L_HB   = "GRAFICO_HACHURA_ABAIXO"

        for lname in (L_TERR, L_CAN, L_HA, L_HB):
            try:
                if lname not in doc.layers:
                    doc.layers.new(lname)
            except Exception:
                pass  # nosec B110

        # Cores (iguais ao gráfico/fill)
        rgb_canal   = (0, 170, 255)
        rgb_terreno = (255, 100, 255)
        rgb_above   = (0, 120, 255)
        rgb_below   = (255, 60, 60)

        # HACHURA (primeiro), para as linhas ficarem por cima
        if include_hatch:
            xs = xs_t[:]
            yterr = ys_t[:]
            ycan = [interp_y(xs_c, ys_c, xq) for xq in xs]

            xs_f, yt_f, yc_f = [], [], []
            for xq, yt, yc in zip(xs, yterr, ycan):
                if yt is None or yc is None:
                    continue
                try:
                    if math.isnan(float(xq)) or math.isnan(float(yt)) or math.isnan(float(yc)):
                        continue
                except Exception:  # nosec B112
                    continue
                xs_f.append(float(xq))
                yt_f.append(float(yt))
                yc_f.append(float(yc))

            if len(xs_f) >= 2:
                def sign(v, eps=1e-9):
                    if v > eps:
                        return 1
                    if v < -eps:
                        return -1
                    return 0

                n = len(xs_f)
                xs2 = [xs_f[0]]
                yt2 = [yt_f[0]]
                yc2 = [yc_f[0]]

                for i in range(n - 1):
                    x0_, x1_ = xs_f[i], xs_f[i + 1]
                    yt0, yt1 = yt_f[i], yt_f[i + 1]
                    yc0, yc1 = yc_f[i], yc_f[i + 1]
                    d0 = yt0 - yc0
                    d1 = yt1 - yc1

                    if d0 * d1 < 0.0:
                        t = d0 / (d0 - d1)
                        x_int = x0_ + t * (x1_ - x0_)
                        yt_int = yt0 + t * (yt1 - yt0)
                        yc_int = yc0 + t * (yc1 - yc0)
                        y_int = (yt_int + yc_int) * 0.5
                        xs2.append(x_int)
                        yt2.append(y_int)
                        yc2.append(y_int)

                    xs2.append(x1_)
                    yt2.append(yt1)
                    yc2.append(yc1)

                diff2 = [yt2[i] - yc2[i] for i in range(len(xs2))]
                signs2 = [sign(d) for d in diff2]

                def add_hatch_polygon(points, rgb, layer_name):
                    if len(points) < 3:
                        return
                    try:
                        hatch = msp.add_hatch(dxfattribs={"layer": layer_name})

                        # caminho (contorno)
                        hatch.paths.add_polyline_path(points, is_closed=True)

                        # SOLID + cor
                        try:
                            hatch.set_solid_fill(rgb=rgb)
                        except Exception:
                            hatch.set_solid_fill()
                            try:
                                hatch.dxf.true_color = rgb2int(rgb)
                            except Exception:
                                pass  # nosec B110

                        # transparência 60% (0=opaco, 1=transparente)
                        try:
                            hatch.transparency = 0.60
                        except Exception:
                            pass  # nosec B110
                    except Exception:
                        pass  # nosec B110

                m = len(xs2)
                i = 0
                while i < m:
                    s = signs2[i]
                    if s == 0:
                        i += 1
                        continue

                    start = i
                    i += 1
                    while i < m and (signs2[i] == s or signs2[i] == 0):
                        i += 1
                    end = i - 1
                    if end <= start:
                        continue

                    if start > 0 and signs2[start - 1] == 0:
                        start -= 1
                    if end < m - 1 and signs2[end + 1] == 0:
                        end += 1

                    seg_x = xs2[start:end + 1]
                    seg_t = yt2[start:end + 1]
                    seg_c = yc2[start:end + 1]
                    if len(seg_x) < 2:
                        continue

                    poly = [(seg_x[k], seg_t[k]) for k in range(len(seg_x))] + \
                           [(seg_x[k], seg_c[k]) for k in range(len(seg_x) - 1, -1, -1)]

                    if s > 0:
                        add_hatch_polygon(poly, rgb_above, L_HA)
                    else:
                        add_hatch_polygon(poly, rgb_below, L_HB)

        # LINHAS (depois), para ficarem por cima da hachura
        try:
            msp.add_lwpolyline(list(zip(xs_t, ys_t)), dxfattribs={"layer": L_TERR, "true_color": rgb2int(rgb_terreno)})
        except Exception:
            try:
                pl = msp.add_polyline2d(list(zip(xs_t, ys_t)), dxfattribs={"layer": L_TERR})
                pl.dxf.true_color = rgb2int(rgb_terreno)
            except Exception:
                pass  # nosec B110

        try:
            msp.add_lwpolyline(list(zip(xs_c, ys_c)), dxfattribs={"layer": L_CAN, "true_color": rgb2int(rgb_canal)})
        except Exception:
            try:
                pl = msp.add_polyline2d(list(zip(xs_c, ys_c)), dxfattribs={"layer": L_CAN})
                pl.dxf.true_color = rgb2int(rgb_canal)
            except Exception:
                pass  # nosec B110

        # Eixos/moldura + caixas de cota (sempre, com ou sem hachura)
        bbox = self._dxf_bbox_from_series(xs_t, [ys_t, ys_c], pad_ratio=0.10)
        if not bbox:
            return False, self.tr("Não foi possível calcular a extensão do gráfico (bbox).")

        x_data_start = min(min(xs_t), min(xs_c))
        x_data_end   = max(max(xs_t), max(xs_c))

        x0b, y0b, x1b, y1b = bbox
        # Adiciona a Legenda
        self._dxf_add_legend_tracinhos(msp, x0=x0b, y0=y0b, x1=x1b, y1=y1b, rgb_terreno=rgb_terreno, rgb_projeto=rgb_canal, label_terreno=self.tr("Terreno"), label_projeto=self.tr("Projeto"))

        # GRID HORIZONTAL POR TRÁS DO GRÁFICO
        self._dxf_add_y_gridlines(msp, x0=x0b, y0=y0b, x1=x1b, y1=y1b, y_ticks_count=5, layer="GRAFICO_GRID_Y", rgb=(200, 200, 200), transparency=0.50)

        x_data_start = min(min(xs_t), min(xs_c))
        x_data_end   = max(max(xs_t), max(xs_c))

        self._dxf_add_x_gridlines(msp, x0=x0b, y0=y0b, x1=x1b, y1=y1b, x_tick_step=10.0, x_ticks_start=x_data_start, x_ticks_end=x_data_end, layer="GRAFICO_GRID_X", rgb=(200, 200, 200), transparency=0.60)

        self._dxf_add_axes_and_frame(msp, x0=x0b, y0=y0b, x1=x1b, y1=y1b, layer_axes="GRAFICO_EIXOS", layer_frame="GRAFICO_MOLDURA", layer_text="GRAFICO_TEXTOS", add_ticks=True, add_labels=True, y_label=self.tr("Cota (m)"), x_tick_step=10.0, x_ticks_start=x_data_start, x_ticks_end=x_data_end)

        # use o que você já tiver armazenado quando gera o gráfico:
        y_bottom_cotas = self._dxf_add_cota_boxes(msp, x0=x0b, y0=y0b, x1=x1b, y1=y1b, xs_terreno=xs_t, ys_terreno=ys_t, xs_projeto=xs_c, ys_projeto=ys_c, x_tick_step=10.0)

        if include_table:
            self._dxf_add_tabela_estacas_xyz(msp, x0=x0b, y0=y0b, x1=x1b, y1=y1b, xs_terreno=xs_t, ys_terreno=ys_t, xs_projeto=xs_c, ys_projeto=ys_c, profile_geom=getattr(self, "_grafico_profile_geom", None), x_tick_step=10.0, y_anchor=y_bottom_cotas)

        # Salvar
        try:
            doc.saveas(out_path)
        except Exception as e:
            return False, self.tr("Erro ao salvar DXF: {error}").format(error=str(e))

        return True, None

    def _dxf_bbox_from_series(self, xs, ys_list, pad_ratio=0.08):
        """
        Calcula bounding box do gráfico a partir de X e múltiplas séries Y.
        Aplica um padding percentual.
        """
        xs = list(xs or [])
        if not xs:
            return None

        all_y = []
        for ys in (ys_list or []):
            if ys is None:
                continue
            all_y.extend(list(ys))

        if not all_y:
            return None

        x0, x1 = float(min(xs)), float(max(xs))
        y0, y1 = float(min(all_y)), float(max(all_y))

        span_x = max(1e-9, x1 - x0)
        span_y = max(1e-9, y1 - y0)

        pad_x = span_x * float(pad_ratio)
        pad_y = span_y * float(pad_ratio)

        return (x0 - pad_x, y0 - pad_y, x1 + pad_x, y1 + pad_y)

    def _dxf_add_axes_and_frame(self, msp, *, x0, y0, x1, y1, layer_axes="GRAFICO_EIXOS", layer_frame="GRAFICO_MOLDURA", layer_text="GRAFICO_TEXTOS", add_ticks=True, add_labels=True, x_label=None, y_label=None, x_tick_step=10.0, label_x_ticks=True, label_y_ticks=True, y_ticks_count=5, x_ticks_start=None, x_ticks_end=None):
        """
        - Moldura
        - Eixos X/Y
        - Ticks X de 10 em 10 + rótulos (abaixo da caixa)
        - Ticks Y (divisões) + rótulos (à esquerda)
        - Texto Y (Cota) mais à esquerda do que os rótulos do Y
        """
        if y_label is None:
            y_label = self.tr("Cota (m)")

        try:
            from ezdxf.enums import TextEntityAlignment
        except Exception:
            TextEntityAlignment = None

        if x1 <= x0:
            x1 = x0 + 1.0
        if y1 <= y0:
            y1 = y0 + 1.0

        span_x = float(x1 - x0)
        span_y = float(y1 - y0)

        text_h = max(1.5, span_y * 0.03)
        tick_len = max(0.8, span_y * 0.02)
        off_txt = max(1.0, span_y * 0.04)

        # X tick labels mais abaixo da caixa
        x_tick_label_drop = off_txt * 1.4

        # Y tick labels e título mais à esquerda
        y_tick_label_left = off_txt * 4     # onde ficam os VALORES do eixo Y
        y_title_left = off_txt * 5          # onde fica o texto "Cota (m)" (mais à esquerda que os valores)

        # Moldura
        frame_pts = [(x0, y0), (x1, y0), (x1, y1), (x0, y1), (x0, y0)]
        try:
            msp.add_lwpolyline(frame_pts, dxfattribs={"layer": layer_frame, "closed": True})
        except Exception:
            for a, b in zip(frame_pts[:-1], frame_pts[1:]):
                msp.add_line(a, b, dxfattribs={"layer": layer_frame})

        # Eixos
        msp.add_line((x0, y0), (x1, y0), dxfattribs={"layer": layer_axes})
        msp.add_line((x0, y0), (x0, y1), dxfattribs={"layer": layer_axes})

        if add_ticks:
            # Ticks eixo X: 10 em 10, incluindo x1
            step = float(x_tick_step) if x_tick_step else 10.0
            if step <= 0:
                step = 10.0

            x_start_tick = float(x_ticks_start) if x_ticks_start is not None else float(x0)
            x_end_tick   = float(x_ticks_end)   if x_ticks_end   is not None else float(x1)

            start = math.ceil(x_start_tick / step) * step
            ticks_x = []
            t = start
            tol = step * 1e-9 + 1e-9

            while t <= x_end_tick + tol:
                if t >= x_start_tick - tol:
                    ticks_x.append(float(t))
                t += step

            # garante o tick do FINAL REAL do gráfico (x_end_tick)
            if not ticks_x or abs(ticks_x[-1] - x_end_tick) > (step * 1e-6 + 1e-6):
                ticks_x.append(float(x_end_tick))

            for tx in ticks_x:
                msp.add_line((tx, y0), (tx, y0 + tick_len), dxfattribs={"layer": layer_axes})

                if label_x_ticks:
                    try:
                        lbl = msp.add_text(f"{tx:.0f} m", dxfattribs={"layer": layer_text, "height": text_h * 0.50})
                        pos = (tx, y0 - x_tick_label_drop, 0.0)
                        lbl.dxf.insert = pos
                        try:
                            lbl.set_placement(pos, align=TextEntityAlignment.MIDDLE_RIGHT)
                        except Exception:
                            pass  # nosec B110
                    except Exception:
                        pass  # nosec B110

            # Ticks eixo Y: divisões + valores
            n_ticks_y = int(y_ticks_count) if y_ticks_count else 5
            n_ticks_y = max(1, n_ticks_y)

            for i in range(n_ticks_y + 1):
                ty = y0 + (span_y * i / n_ticks_y)

                # tick horizontal
                msp.add_line((x0, ty), (x0 + tick_len, ty), dxfattribs={"layer": layer_axes})

                # VALOR do eixo Y (mais à esquerda)
                if label_y_ticks:
                    try:
                        txt = f"{ty:.2f}"
                        lbl = msp.add_text(txt, dxfattribs={"layer": layer_text, "height": text_h * 0.50})
                        pos = (x0 - y_tick_label_left, ty, 0.0)
                        lbl.dxf.insert = pos
                        # alinha à direita (encostando “perto” do eixo)
                        try:
                            lbl.set_placement(pos, align=TextEntityAlignment.MIDDLE_RIGHT)
                        except Exception:
                            pass  # nosec B110
                    except Exception:
                        pass  # nosec B110

        # Título do eixo Y (mais à esquerda que os valores)
        if add_labels:
            try:
                t = msp.add_text(y_label, dxfattribs={"layer": layer_text, "height": text_h, "rotation": 90.0})
                pos = (x0 - y_title_left, y0 + span_y * 0.5, 0.0)
                t.dxf.insert = pos
                try:
                    t.set_placement(pos, align=TextEntityAlignment.MIDDLE_CENTER)
                except Exception:
                    pass  # nosec B110
            except Exception:
                pass  # nosec B110

    def _dxf_add_y_gridlines(self, msp, *, x0, y0, x1, y1, y_ticks_count=5, layer="GRAFICO_GRID_Y", rgb=(200, 200, 200), transparency=0.70):
        """
        Linhas horizontais partindo dos ticks do eixo Y até o lado oposto do retângulo.
        Desenha em cinza claro e transparente.
        """
        # cria layer
        try:
            doc = msp.doc
            if layer not in doc.layers:
                doc.layers.new(layer)
        except Exception:
            pass  # nosec B110

        span_y = float(y1 - y0)
        tick_len = max(0.8, span_y * 0.02)  # mesmo “tick_len” usado nos eixos

        n = max(1, int(y_ticks_count))
        for i in range(n + 1):
            ty = y0 + (span_y * i / n)

            # normalmente não precisa desenhar nas bordas (já tem moldura)
            if i == 0 or i == n:
                continue

            ln = msp.add_line((x0 + tick_len, ty), (x1, ty), dxfattribs={"layer": layer})

            # cor cinza claro
            try:
                if rgb2int is not None:
                    ln.dxf.true_color = rgb2int(rgb)
            except Exception:
                pass  # nosec B110

            # transparência (0=opaco, 1=transparente)
            try:
                ln.transparency = float(transparency)
            except Exception:
                pass  # nosec B110

    def _dxf_add_legend_tracinhos(self, msp, *, x0, y0, x1, y1, rgb_terreno=(255, 100, 255), rgb_projeto=(0, 170, 255), label_terreno=None, label_projeto=None, layer_lines="GRAFICO_LEGENDA", layer_text="GRAFICO_LEGENDA_TXT"):
        """
        Adiciona uma legenda simples no DXF (estilo “tracinhos”) para identificar
        as duas linhas do gráfico: Terreno e Projeto.

        A legenda é posicionada logo acima da moldura do gráfico (y1) e desenha:
          - um pequeno segmento de linha colorido (dash) + texto ao lado
          - repete para as duas entradas (terreno/projeto)
        O tamanho do texto e dos tracinhos é proporcional ao tamanho da moldura.

        Parâmetros:
          - msp: modelspace do ezdxf
          - (x0, y0, x1, y1): caixa do gráfico (moldura)
          - rgb_*: cor TrueColor (R,G,B) para cada item da legenda
          - label_*: rótulos mostrados ao lado do tracinho
          - layer_lines/layer_text: layers onde serão criadas as entidades
        """
        if label_terreno is None:
            label_terreno = self.tr("Terreno")

        if label_projeto is None:
            label_projeto = self.tr("Projeto")

        # cria layers (se possível) para separar linhas e textos da legenda
        try:
            doc = msp.doc
            if layer_lines not in doc.layers:
                doc.layers.new(layer_lines)  # layer dos “tracinhos”
            if layer_text not in doc.layers:
                doc.layers.new(layer_text)  # layer dos textos
        except Exception:
            pass  # nosec B110 | se falhar (doc/layers indisponível), desenha mesmo assim sem criar layer

        span_x = float(x1 - x0)  # largura da moldura
        span_y = float(y1 - y0)  # altura da moldura

        # dimensões relativas ao tamanho do quadro (mantém proporção em diferentes escalas)
        text_h = max(1.3, span_y * 0.03)     # altura do texto
        off_txt = max(1.0, span_y * 0.04)    # offset vertical/espacamentos

        # posição base: um pouco acima da moldura do gráfico
        y_leg = y1 + off_txt * 0.6

        # tamanho do “tracinho” e espaçamento geral
        dash_len = max(4.0, span_x * 0.05)   # comprimento do segmento de linha
        gap = off_txt * 0.6                  # espaçamento entre itens

        # começa perto do canto esquerdo da moldura
        x_start = x0 + off_txt * 0.8

        def add_dash_and_text(xi, rgb, label):
            """Desenha um tracinho colorido + texto ao lado e retorna o próximo X disponível."""
            # 1) tracinho (linha) da legenda
            ln = msp.add_line((xi, y_leg), (xi + dash_len, y_leg), dxfattribs={"layer": layer_lines})
            try:
                if rgb2int is not None:
                    ln.dxf.true_color = rgb2int(rgb)  # aplica TrueColor (RGB)
            except Exception:
                pass  # nosec B110

            # 2) texto ao lado do tracinho (alinhado ao meio vertical)
            t = msp.add_text(label, dxfattribs={"layer": layer_text, "height": text_h})
            t_pos = (xi + dash_len + off_txt * 0.35, y_leg, 0.0)
            try:
                from ezdxf.enums import TextEntityAlignment
                t.set_placement(t_pos, align=TextEntityAlignment.MIDDLE_LEFT)  # texto “colado” no tracinho
            except Exception:
                t.dxf.insert = t_pos  # fallback simples caso set_placement não exista

            # 3) calcula um X aproximado para o próximo item (não mede bbox real, só estima)
            approx = len(label) * (text_h * 0.6)  # heurística simples de largura do texto
            return xi + dash_len + off_txt * 0.35 + approx + gap

        # Item 1: Terreno
        x_next = add_dash_and_text(x_start, rgb_terreno, label_terreno)

        # separa o Item 2 para não ficar “colado” no primeiro
        x_next += max(off_txt * 2.5, dash_len * 0.8)

        # Item 2: Projeto
        add_dash_and_text(x_next, rgb_projeto, label_projeto)

    def _dxf_add_cota_boxes(self, msp, *, x0, y0, x1, y1, xs_terreno, ys_terreno, xs_projeto, ys_projeto, x_tick_step=10.0, layer_box="GRAFICO_COTAS_BOX", layer_text="GRAFICO_COTAS_TEXT", label_terreno=None, label_projeto=None, label_escavacao=None):
        """
        Três caixas (Terreno/Projeto/Escavação) abaixo do gráfico.
        - Rótulos ficam DENTRO do retângulo, encostados à esquerda e justificados à esquerda.
        - Valores: a cada 10m e no final (x_end).
        - Valores NÃO ficam em cima das linhas verticais: ficam levemente deslocados para dentro da célula.
        - No último tick (x_end), o valor fica à direita do separador e é garantido dentro do retângulo.
        - Escavação = Terreno - Projeto (por tick).
        """
        if label_terreno is None:
            label_terreno = self.tr("Terreno")

        if label_projeto is None:
            label_projeto = self.tr("Projeto")

        if label_escavacao is None:
            label_escavacao = self.tr("Escavação")

        # Alinhamentos (ezdxf)
        try:
            from ezdxf.enums import TextEntityAlignment as _ALIGN
        except Exception:
            _ALIGN = None

        # Normaliza séries (float + ordena por X) para garantir interp
        def _normalize_xy(xs, ys):
            pairs = []
            if xs is None or ys is None:
                return [], []
            n = min(len(xs), len(ys))
            for i in range(n):
                try:
                    fx = float(xs[i])
                    fy = float(ys[i])
                    if math.isnan(fx) or math.isnan(fy):
                        continue
                    pairs.append((fx, fy))
                except Exception:  # nosec B112
                    continue
            pairs.sort(key=lambda p: p[0])
            return [p[0] for p in pairs], [p[1] for p in pairs]

        xs_terreno, ys_terreno = _normalize_xy(xs_terreno, ys_terreno)
        xs_projeto, ys_projeto = _normalize_xy(xs_projeto, ys_projeto)

        if len(xs_terreno) < 2 or len(ys_terreno) < 2:
            return None

        # Interpolação linear (xs monotônico)
        def interp_y(xs_src, ys_src, xq):
            if not xs_src:
                return None
            if xq <= xs_src[0]:
                return ys_src[0]
            if xq >= xs_src[-1]:
                return ys_src[-1]
            lo, hi = 0, len(xs_src) - 1
            while hi - lo > 1:
                mid = (lo + hi) // 2
                if xs_src[mid] <= xq:
                    lo = mid
                else:
                    hi = mid
            xA, xB = xs_src[lo], xs_src[hi]
            yA, yB = ys_src[lo], ys_src[hi]
            dx = (xB - xA)
            if abs(dx) < 1e-12:
                return yA
            t = (xq - xA) / dx
            return yA + t * (yB - yA)

        # Helper para texto
        def add_text(text, pos, height, rotation=0.0, align=None):
            if text is None:
                return
            text = str(text)
            if not text.strip():
                return
            t = msp.add_text(text, dxfattribs={"layer": layer_text, "height": float(height), "rotation": float(rotation)})
            try:
                if _ALIGN is not None and align is not None:
                    t.set_placement(pos, align=align)
                else:
                    t.dxf.insert = pos
            except Exception:
                t.dxf.insert = pos

        # Sizing
        span_y = float(y1 - y0)
        text_h = max(1.0, span_y * 0.03)
        off_txt = max(1.0, span_y * 0.04)

        x_tick_label_drop = off_txt * 1.4
        row_h = max(text_h * 1.8, span_y * 0.10)
        gap = off_txt * 0.7

        # 3 linhas: Terreno / Projeto / Escavação
        row1_top = y0 - x_tick_label_drop - gap
        row1_bot = row1_top - row_h
        row2_top = row1_bot
        row2_bot = row2_top - row_h
        row3_top = row2_bot
        row3_bot = row3_top - row_h

        y_mid1 = (row1_top + row1_bot) * 0.5
        y_mid2 = (row2_top + row2_bot) * 0.5
        y_mid3 = (row3_top + row3_bot) * 0.5

        # Layers
        try:
            doc = msp.doc
            if layer_box not in doc.layers:
                doc.layers.new(layer_box)
            if layer_text not in doc.layers:
                doc.layers.new(layer_text)
        except Exception:
            pass  # nosec B110

        # Eixo X do perfil (usa o terreno como referência)
        x_start = float(xs_terreno[0])
        x_end = float(xs_terreno[-1])

        step = float(x_tick_step) if x_tick_step else 10.0
        if step <= 0:
            step = 10.0

        # ticks a cada 10 + final
        start_tick = math.ceil(x_start / step) * step
        ticks = []
        t = start_tick
        tol = step * 1e-9 + 1e-9
        while t <= x_end + tol:
            if t >= x_start - tol:
                ticks.append(float(t))
            t += step
        if not ticks or abs(ticks[-1] - x_end) > (step * 1e-6 + 1e-6):
            ticks.append(float(x_end))

        # Largura mínima da coluna do rótulo (pra nunca cortar)
        label_h = text_h * 0.50
        approx_char_w = label_h * 0.60
        longest = max(len(label_terreno or ""), len(label_projeto or ""), len(label_escavacao or ""))
        min_label_col_w = (longest * approx_char_w) + off_txt * 1.2

        col_right = ticks[0] if ticks else x_start

        x0_tbl = float(x0)
        if (col_right - x0_tbl) < min_label_col_w:
            x0_tbl = col_right - min_label_col_w

        x1_tbl = float(x1)

        # Retângulos
        def rect(xa, ya, xb, yb):
            pts = [(xa, ya), (xb, ya), (xb, yb), (xa, yb), (xa, ya)]
            try:
                msp.add_lwpolyline(pts, dxfattribs={"layer": layer_box, "closed": True})
            except Exception:
                for A, B in zip(pts[:-1], pts[1:]):
                    msp.add_line(A, B, dxfattribs={"layer": layer_box})

        rect(x0_tbl, row1_bot, x1_tbl, row1_top)  # Terreno
        rect(x0_tbl, row2_bot, x1_tbl, row2_top)  # Projeto
        rect(x0_tbl, row3_bot, x1_tbl, row3_top)  # Escavação

        # Separadores verticais (toda a altura das 3 linhas)
        for tx in ticks:
            try:
                msp.add_line((tx, row3_bot), (tx, row1_top), dxfattribs={"layer": layer_box})
            except Exception:
                pass  # nosec B110

        # Rótulos: dentro, encostado no lado esquerdo, justificado à esquerda
        label_pad = off_txt * 0.40
        label_x = x0_tbl + label_pad

        if _ALIGN is not None:
            add_text(label_terreno,   (label_x, y_mid1, 0.0), height=label_h, align=_ALIGN.MIDDLE_LEFT)
            add_text(label_projeto,   (label_x, y_mid2, 0.0), height=label_h, align=_ALIGN.MIDDLE_LEFT)
            add_text(label_escavacao, (label_x, y_mid3, 0.0), height=label_h, align=_ALIGN.MIDDLE_LEFT)
        else:
            add_text(label_terreno,   (label_x, y_mid1, 0.0), height=label_h)
            add_text(label_projeto,   (label_x, y_mid2, 0.0), height=label_h)
            add_text(label_escavacao, (label_x, y_mid3, 0.0), height=label_h)

        # Valores
        val_h = text_h * 0.50
        inset = off_txt * 0.35
        last_tx = ticks[-1] if ticks else x_end
        last_tol = step * 1e-6 + 1e-6

        def _approx_text_w(txt: str) -> float:
            return max(0.0, len(txt) * (val_h * 0.60))

        def _add_value_cell(tx, ymid, txt):
            if txt is None:
                return
            txt = str(txt).strip()
            if not txt:
                return

            is_last = abs(tx - last_tx) <= last_tol

            if not is_last:
                # mantém comportamento normal: logo após o separador (tx), alinhado à esquerda
                if _ALIGN is not None:
                    add_text(txt, (tx + inset, ymid, 0.0), height=val_h, align=_ALIGN.MIDDLE_LEFT)
                else:
                    add_text(txt, (tx + inset, ymid, 0.0), height=val_h)
                return

            # ÚLTIMO tick: fica à direita do separador, mas garantido dentro do retângulo
            w = _approx_text_w(txt)

            if _ALIGN is not None:
                if (tx + inset + w) <= (x1_tbl - inset):
                    add_text(txt, (tx + inset, ymid, 0.0), height=val_h, align=_ALIGN.MIDDLE_LEFT)
                else:
                    add_text(txt, (x1_tbl - inset, ymid, 0.0), height=val_h, align=_ALIGN.MIDDLE_RIGHT)
            else:
                px = tx + inset
                if (px + w) > (x1_tbl - inset):
                    px = (x1_tbl - inset) - w
                add_text(txt, (px, ymid, 0.0), height=val_h)

        for tx in ticks:
            yt = interp_y(xs_terreno, ys_terreno, tx)
            yp = interp_y(xs_projeto, ys_projeto, tx) if len(xs_projeto) >= 2 else None

            # Terreno
            if yt is not None:
                _add_value_cell(tx, y_mid1, f"{float(yt):.2f}")

            # Projeto
            if yp is not None:
                _add_value_cell(tx, y_mid2, f"{float(yp):.2f}")

            # Escavação = Terreno - Projeto
            if yt is not None and yp is not None:
                esc = float(yt) - float(yp)
                _add_value_cell(tx, y_mid3, f"{esc:.2f}")

        return row3_bot

    def _dxf_add_x_gridlines(self, msp, *, x0, y0, x1, y1, x_tick_step=10.0, x_ticks_start=None, x_ticks_end=None, layer="GRAFICO_GRID_X", rgb=(200, 200, 200), transparency=0.70, skip_frame=True):
        """
        Linhas verticais partindo dos ticks do eixo X (base y0) até o topo (y1),
        em cinza claro e transparente.

        IMPORTANTE:
        - Se x_ticks_start/x_ticks_end forem informados, as linhas seguem esses ticks,
          garantindo casar com o último valor do eixo X (fim real do gráfico).
        """
        # cria layer
        try:
            doc = msp.doc
            if layer not in doc.layers:
                doc.layers.new(layer)
        except Exception:
            pass  # nosec B110

        span_y = float(y1 - y0)
        tick_len = max(0.8, span_y * 0.02)  # igual ao eixo

        step = float(x_tick_step) if x_tick_step else 10.0
        if step <= 0:
            step = 10.0

        # usa ticks do eixo (fim real), não o bbox
        x_start_tick = float(x_ticks_start) if x_ticks_start is not None else float(x0)
        x_end_tick   = float(x_ticks_end)   if x_ticks_end   is not None else float(x1)

        # gera ticks de step em step dentro do range real
        start = math.ceil(x_start_tick / step) * step
        ticks_x = []
        t = start
        tol = step * 1e-9 + 1e-9
        while t <= x_end_tick + tol:
            if t >= x_start_tick - tol:
                ticks_x.append(float(t))
            t += step

        # garante o tick final REAL (ex.: 97m)
        if not ticks_x or abs(ticks_x[-1] - x_end_tick) > (step * 1e-6 + 1e-6):
            ticks_x.append(float(x_end_tick))

        # desenha gridlines
        for tx in ticks_x:
            if skip_frame:
                # evita duplicar a moldura só quando COINCIDIR com a borda
                if abs(tx - x0) <= (step * 1e-6 + 1e-6):
                    continue
                if abs(tx - x1) <= (step * 1e-6 + 1e-6):
                    continue

            ln = msp.add_line((tx, y0 + tick_len), (tx, y1), dxfattribs={"layer": layer})

            # cor cinza claro
            try:
                if rgb2int is not None:
                    ln.dxf.true_color = rgb2int(rgb)
            except Exception:
                pass  # nosec B110

            # transparência (0=opaco, 1=transparente)
            try:
                ln.transparency = float(transparency)
            except Exception:
                pass  # nosec B110

    def _dxf_add_tabela_estacas_xyz(self, msp, *, x0, y0, x1, y1, xs_terreno, ys_terreno, y_anchor=None, xs_projeto, ys_projeto, profile_geom=None, x_tick_step=10.0, layer_box="GRAFICO_TABELA_BOX", layer_text="GRAFICO_TABELA_TEXT"):
        """
        Tabela abaixo do gráfico com colunas:
        ESTACAS, X, Y, TERRENO, PROJETO, ESCAVAÇÃO (=Terreno-Projeto)

        - X/Y extraídos da geometria do perfil via geom.interpolate(dist)
        - dist é o X do gráfico (0..length), em metros
        - Textos SEMPRE dentro das células:
            * ESTACAS centralizado
            * Demais colunas: encostado à esquerda (com pad interno)
        """
        # alinhamentos (ezdxf)
        try:
            from ezdxf.enums import TextEntityAlignment as _ALIGN
        except Exception:
            _ALIGN = None

        # cria layers
        doc = msp.doc
        style_name = "ARIAL"

        try:
            if style_name not in doc.styles:
                doc.styles.new(style_name, dxfattribs={"font": "arial.ttf"})
        except Exception:
            # fallback: se não conseguir criar (ambiente sem a fonte), usa o padrão
            style_name = "Standard"

        # normaliza séries (float + ordena por X) para interp
        def _normalize_xy(xs, ys):
            pairs = []
            if xs is None or ys is None:
                return [], []
            n = min(len(xs), len(ys))
            for i in range(n):
                try:
                    fx = float(xs[i])
                    fy = float(ys[i])
                    if math.isnan(fx) or math.isnan(fy):
                        continue
                    pairs.append((fx, fy))
                except Exception:  # nosec B112
                    continue
            pairs.sort(key=lambda p: p[0])
            return [p[0] for p in pairs], [p[1] for p in pairs]

        xs_terreno, ys_terreno = _normalize_xy(xs_terreno, ys_terreno)
        xs_projeto, ys_projeto = _normalize_xy(xs_projeto, ys_projeto)

        if len(xs_terreno) < 2 or len(ys_terreno) < 2:
            return

        # interp linear (xs monotônico)
        def interp_y(xs_src, ys_src, xq):
            if not xs_src:
                return None
            if xq <= xs_src[0]:
                return ys_src[0]
            if xq >= xs_src[-1]:
                return ys_src[-1]
            lo, hi = 0, len(xs_src) - 1
            while hi - lo > 1:
                mid = (lo + hi) // 2
                if xs_src[mid] <= xq:
                    lo = mid
                else:
                    hi = mid
            xA, xB = xs_src[lo], xs_src[hi]
            yA, yB = ys_src[lo], ys_src[hi]
            dx = (xB - xA)
            if abs(dx) < 1e-12:
                return yA
            t = (xq - xA) / dx
            return yA + t * (yB - yA)

        def _add_text(text, pos, height, align=None):
            if text is None:
                return
            s = str(text)
            if not s.strip():
                return
            ent = msp.add_text(s, dxfattribs={"layer": layer_text, "height": float(height), "style": "ARIAL"})

            try:
                if _ALIGN is not None and align is not None:
                    ent.set_placement(pos, align=align)
                else:
                    ent.dxf.insert = pos
            except Exception:
                ent.dxf.insert = pos

        # ticks (a cada 10m + final do comprimento)
        x_start = float(xs_terreno[0])
        x_end = float(xs_terreno[-1])

        step = float(x_tick_step) if x_tick_step else 10.0
        if step <= 0:
            step = 10.0

        start_tick = math.ceil(x_start / step) * step
        ticks = []
        t = start_tick
        tol = step * 1e-9 + 1e-9
        while t <= x_end + tol:
            if t >= x_start - tol:
                ticks.append(float(t))
            t += step
        if not ticks or abs(ticks[-1] - x_end) > (step * 1e-6 + 1e-6):
            ticks.append(float(x_end))

        # sizing baseado no bbox do gráfico
        span_y = float(y1 - y0)
        span_x = float(x1 - x0)  # comprimento do gráfico no eixo X

        text_h_y   = max(1.0, span_y * 0.03)
        text_h_len = max(0.8, min(4.0, span_x * 0.01))  # ajuste fino

        text_h = min(text_h_y, text_h_len)
        off_txt = max(1.0, span_y * 0.04)

        x_tick_label_drop = off_txt * 1.4

        gap = off_txt * 1.2

        #Controle da altura e lagura das células da tabela
        header_h = max(text_h * 1.6, span_y * 0.07)
        row_h = max(text_h * 1.5, span_y * 0.09)

        # y_anchor: deve ser o "fundo do bloco anterior" (ex: fundo das caixas de cota)
        if y_anchor is None:
            # fallback mais “para baixo” para não colidir com eixo/labels
            anchor = y0 - x_tick_label_drop - gap - (off_txt * 4.0)
        else:
            try:
                anchor = float(y_anchor)
            except Exception:
                anchor = y0 - x_tick_label_drop - gap - (off_txt * 4.0)

        table_top = anchor - off_txt * 1.0  # respiro extra
        n_rows = len(ticks)
        table_bot = table_top - header_h - n_rows * row_h

        # largura total igual ao gráfico
        tbl_x0 = float(x0)
        tbl_x1 = float(x1)

        # colunas (pesos)
        headers = [self.tr("ESTACAS"), self.tr("X"), self.tr("Y"), self.tr("TERRENO"), self.tr("PROJETO"), self.tr("ESCAVAÇÃO")]
        weights = [0.10, 0.15, 0.15, 0.17, 0.17, 0.26]  # soma ~ 1.0

        # calcula limites das colunas
        col_edges = [tbl_x0]
        acc = tbl_x0
        wtot = (tbl_x1 - tbl_x0)
        for w in weights:
            acc += wtot * w
            col_edges.append(acc)

        # desenha moldura externa
        def rect(xa, ya, xb, yb):
            pts = [(xa, ya), (xb, ya), (xb, yb), (xa, yb), (xa, ya)]
            try:
                msp.add_lwpolyline(pts, dxfattribs={"layer": layer_box, "closed": True})
            except Exception:
                for A, B in zip(pts[:-1], pts[1:]):
                    msp.add_line(A, B, dxfattribs={"layer": layer_box})

        rect(tbl_x0, table_bot, tbl_x1, table_top)

        # linhas verticais (colunas)
        for xe in col_edges[1:-1]:
            try:
                msp.add_line((xe, table_bot), (xe, table_top), dxfattribs={"layer": layer_box})
            except Exception:
                pass  # nosec B110

        # linha separando header
        y_header_bot = table_top - header_h
        try:
            msp.add_line((tbl_x0, y_header_bot), (tbl_x1, y_header_bot), dxfattribs={"layer": layer_box})
        except Exception:
            pass  # nosec B110

        # linhas horizontais (linhas da tabela)
        y = y_header_bot
        for _ in range(n_rows):
            y -= row_h
            try:
                msp.add_line((tbl_x0, y), (tbl_x1, y), dxfattribs={"layer": layer_box})
            except Exception:
                pass  # nosec B110

        # helper: texto dentro da célula (com pad)
        def cell_text(col_i, row_i, text, *, mode="center"):
            xL = col_edges[col_i]
            xR = col_edges[col_i + 1]

            if row_i == -1:
                yT = table_top
                yB = y_header_bot
                h = text_h * 0.85
            else:
                yT = y_header_bot - row_i * row_h
                yB = yT - row_h
                h = text_h * 0.65

            pad = max(off_txt * 0.20, (xR - xL) * 0.04)

            # centros
            xMid = (xL + xR) * 0.5
            yMid = (yT + yB) * 0.5

            # desce um pouco APENAS o texto do cabeçalho
            if row_i == -1:
                yMid -= text_h * 0.50

                # puxa o cabeçalho para a esquerda (alinhado à esquerda)
                mode = "left"
                xMid = xL + pad * 2   # ajuste fino: 0.6 .. 1.2

            if mode == "left":
                pos = (xL + pad, yMid, 0.0)
                al = _ALIGN.MIDDLE_LEFT if _ALIGN is not None else None
            elif mode == "right":
                pos = (xR - pad, yMid, 0.0)
                al = _ALIGN.MIDDLE_RIGHT if _ALIGN is not None else None
            else:
                pos = ((xL + xR) * 0.5, yMid, 0.0)
                al = _ALIGN.MIDDLE_CENTER if _ALIGN is not None else None

            _add_text(text, pos, height=h, align=al)

        # header (centralizado)
        for ci, head in enumerate(headers):
            cell_text(ci, -1, head, mode="center")

        # X/Y via geometria do perfil
        def get_xy_at_dist(dist):
            if profile_geom is None:
                return None, None
            try:
                if profile_geom.isEmpty():
                    return None, None
            except Exception:
                pass  # nosec B110

            try:
                d = float(dist)
            except Exception:
                return None, None

            # clamp para evitar dist negativa ou maior que o comprimento
            try:
                L = float(profile_geom.length())
                if math.isnan(L) or L <= 0:
                    return None, None
                d = max(0.0, min(d, L))
            except Exception:
                d = max(0.0, d)

            try:
                ptg = profile_geom.interpolate(d)
                if ptg is None or ptg.isEmpty():
                    return None, None
                p = ptg.asPoint()
                return float(p.x()), float(p.y())
            except Exception:
                return None, None

        # linhas (ESTACAS central, demais à esquerda dentro da célula)
        for ri, dist in enumerate(ticks):
            yt = interp_y(xs_terreno, ys_terreno, dist)
            if yt is None:
                continue

            yp = interp_y(xs_projeto, ys_projeto, dist) if len(xs_projeto) >= 2 else None
            if yp is None:
                yp = yt

            esc = float(yt) - float(yp)
            Xv, Yv = get_xy_at_dist(dist)

            cell_text(0, ri, f"{ri + 1}", mode="center")  # ESTACAS

            # agora tudo “encostado à esquerda” dentro da célula (como você pediu)
            cell_text(1, ri, (f"{Xv:.3f}" if Xv is not None else ""), mode="left")
            cell_text(2, ri, (f"{Yv:.3f}" if Yv is not None else ""), mode="left")
            cell_text(3, ri, f"{float(yt):.2f}", mode="left")
            cell_text(4, ri, f"{float(yp):.2f}", mode="left")
            cell_text(5, ri, f"{float(esc):.2f}", mode="left")
#////////////////////////////////////////////
    def _init_pushButtonSalvar(self):
        """Conecta o pushButtonSalvar para exportar todas as camadas do grupo CANAIS (listadas no tableViewCamada) para GPKG."""
        btn = getattr(self, "pushButtonSalvar", None)
        if btn is None:
            return

        try:
            btn.clicked.disconnect()
        except Exception:
            pass  # nosec B110

        btn.clicked.connect(self._on_pushButtonSalvar_clicked)
        self._update_pushButtonSalvar_state()

    def _update_pushButtonSalvar_state(self) -> bool:
        """
        Habilita o pushButtonSalvar somente se existir ao menos 1 camada válida
        listada no tableViewCamada (e presente no grupo CANAIS).
        """
        btn = getattr(self, "pushButtonSalvar", None)
        if btn is None:
            return False

        ok = False
        for lyr in self._iter_canais_layers_from_tableView():
            # se você quiser exigir “tem feição”, descomente:
            # if hasattr(self, "_layer_has_any_feature") and not self._layer_has_any_feature(lyr):
            #     continue
            ok = True
            break

        btn.setEnabled(ok)
        return ok

    def _iter_canais_layers_from_tableView(self):
        """Itera QgsVectorLayer listadas no tableViewCamada e que estão dentro do grupo 'CANAIS'."""
        view = getattr(self, "tableViewCamada", None)
        model = getattr(self, "_camadas_model", None) or (view.model() if view is not None else None)
        if model is None:
            return

        prj = QgsProject.instance()
        root = prj.layerTreeRoot()
        grp = root.findGroup(self.tr("CANAIS"))
        if grp is None:
            return

        # layer_id fica no Qt.UserRole na coluna 0 (seu padrão na tabela)
        for row in range(model.rowCount()):
            try:
                idx0 = model.index(row, 0)
                layer_id = idx0.data(Qt.ItemDataRole.UserRole)
                if not layer_id:
                    continue

                lyr = prj.mapLayer(layer_id)
                if not isinstance(lyr, QgsVectorLayer):
                    continue

                # garante que está no grupo CANAIS
                if grp.findLayer(lyr.id()) is None:
                    continue

                yield lyr
            except Exception:  # nosec B112
                continue

    def _sanitize_gpkg_layer_name(self, name: str, used: set[str]) -> str:
        """Gera um nome seguro de tabela no GPKG e garante unicidade."""
        base = (name or "").strip()
        base = re.sub(r"[^0-9a-zA-Z_]+", "_", base).strip("_")
        if not base:
            base = self.tr("CANAIS")
        if base[0].isdigit():
            base = "L_" + base

        out = base
        i = 1
        while out in used:
            i += 1
            out = f"{base}_{i}"
        used.add(out)
        return out

    def _on_pushButtonSalvar_clicked(self):
        """
        Salva todas as camadas do grupo 'CANAIS' (que estão listadas no tableViewCamada) em um GeoPackage.
        """
        layers = list(self._iter_canais_layers_from_tableView())
        if not layers:
            self.mostrar_mensagem(self.tr("Nenhuma camada do grupo 'CANAIS' está listada para salvar."), "Info")
            self._update_pushButtonSalvar_state()
            return

        # Usa sua função que já lembra pasta e evita sobrescrever
        if not hasattr(self, "escolher_local_para_salvar"):
            self.mostrar_mensagem(self.tr("Função escolher_local_para_salvar não encontrada no plugin."), "Erro")
            return

        out_path = self.escolher_local_para_salvar(self.tr("CANAIS.gpkg"), "GeoPackage (*.gpkg)")
        if not out_path:
            return
        if not out_path.lower().endswith(".gpkg"):
            out_path += ".gpkg"

        # Exporta cada camada como uma sub-layer/tabela dentro do mesmo .gpkg
        used_names: set[str] = set()
        errors: list[str] = []
        written: list[tuple[str, str]] = []  # (nome_display, nome_gpkg)

        ctx = QgsProject.instance().transformContext()

        first = True
        for lyr in layers:
            gpkg_layer_name = self._sanitize_gpkg_layer_name(lyr.name(), used_names)

            try:
                opts = QgsVectorFileWriter.SaveVectorOptions()
                opts.driverName = "GPKG"
                opts.fileEncoding = "UTF-8"
                opts.layerName = gpkg_layer_name

                # 1ª escrita: cria/overwrite arquivo; próximas: cria/overwrite layer
                if hasattr(opts, "actionOnExistingFile"):
                    if first and hasattr(QgsVectorFileWriter, "CreateOrOverwriteFile"):
                        opts.actionOnExistingFile = QgsVectorFileWriter.ActionOnExistingFile.CreateOrOverwriteFile
                    elif hasattr(QgsVectorFileWriter, "CreateOrOverwriteLayer"):
                        opts.actionOnExistingFile = QgsVectorFileWriter.ActionOnExistingFile.CreateOrOverwriteLayer
                first = False

                if hasattr(QgsVectorFileWriter, "writeAsVectorFormatV3"):
                    res = QgsVectorFileWriter.writeAsVectorFormatV3(lyr, out_path, ctx, opts)
                    err = res[0] if isinstance(res, (tuple, list)) else res
                    msg = res[1] if isinstance(res, (tuple, list)) and len(res) > 1 else ""
                else:
                    # fallback bem simples (pode não suportar múltiplas layers no mesmo gpkg em versões antigas)
                    err, msg = QgsVectorFileWriter.writeAsVectorFormat(lyr, out_path, "UTF-8", lyr.crs(), "GPKG")

                if err != QgsVectorFileWriter.WriterError.NoError:
                    errors.append(f"{lyr.name()}: {msg or 'erro ao escrever'}")
                    continue

                written.append((lyr.name(), gpkg_layer_name))

            except Exception as e:
                errors.append(f"{lyr.name()}: {e}")

        if not written:
            self.mostrar_mensagem(self.tr("Falha ao salvar GeoPackage (nenhuma camada foi gravada)."), "Erro")
            return

        # Mensagem final (com botão abrir pasta/arquivo, no seu padrão)
        pasta = os.path.dirname(out_path)
        if errors:
            resumo = "\n".join(errors[:8])
            if len(errors) > 8:
                resumo += f"\n... (+{len(errors) - 8} falhas)"
            self.mostrar_mensagem(self.tr("GeoPackage salvo: {file_name}\nCamadas gravadas: {layer_count}\nFalhas:\n{summary}").format(file_name=os.path.basename(out_path), layer_count=len(written), summary=resumo), "Aviso", caminho_pasta=pasta, caminho_arquivo=out_path, forcar=True)
        else:
            self.mostrar_mensagem(self.tr("GeoPackage salvo com sucesso: {file_name}\nCamadas gravadas: {layer_count}").format(file_name=os.path.basename(out_path), layer_count=len(written)), "Sucesso", caminho_pasta=pasta, caminho_arquivo=out_path)

        self._update_pushButtonSalvar_state()
#////////////////////////////////////////////
    def _init_pushButtonAbrir(self):
        """
        Inicializa o botão 'Abrir' conectando o clique ao handler correspondente.

        - Localiza o widget (pushButtonAbrir) se existir no UI
        - Remove conexões anteriores (evita múltiplos disparos ao reabrir/reinicializar o dock)
        - Conecta o sinal clicked ao método _on_pushButtonAbrir_clicked
        """
        btn = getattr(self, "pushButtonAbrir", None)
        if btn is None:
            return  # UI sem o botão (ou nome diferente), nada a fazer

        try:
            btn.clicked.disconnect()  # evita conexão duplicada
        except Exception:
            pass  # nosec B110

        btn.clicked.connect(self._on_pushButtonAbrir_clicked)  # handler do botão "Abrir"

    def _on_pushButtonAbrir_clicked(self):
        """
        Handler do botão "Abrir".

        - Abre um QFileDialog para o usuário selecionar um arquivo (vetor/raster)
        - Chama _abrir_arquivo(path) para carregar no projeto
        - Mostra feedback amigável via mostrar_mensagem (inclui o caminho do arquivo)
        """
        # Filtros do diálogo: prioriza formatos comuns de GIS e deixa opção "Todos"
        filtros = (
            self.tr("GeoPackage (*.gpkg)") + ";;"
            + self.tr("Vetores (*.shp *.gpkg *.geojson *.kml *.gpx *.dxf)") + ";;"
            + self.tr("Rasters (*.tif *.tiff *.asc *.img)") + ";;"
            + self.tr("Todos (*.*)"))

        # Abre o seletor de arquivo
        path, _ = QFileDialog.getOpenFileName(self, self.tr("Abrir arquivo"), "", filtros)
        if not path:
            return

        # Tenta carregar o arquivo no projeto
        ok, err = self._abrir_arquivo(path)
        if not ok:
            self.mostrar_mensagem(err or self.tr("Falha ao abrir arquivo."), "Erro", duracao=4, caminho_arquivo=path, forcar=True)
        else:
            self.mostrar_mensagem(self.tr("Arquivo carregado no projeto."), "Sucesso", duracao=2, caminho_arquivo=path)

    def _abrir_arquivo(self, path: str) -> tuple[bool, str | None]:
        """
        Abre um arquivo no projeto, escolhendo a rotina adequada conforme a extensão.

        - Se for .gpkg, delega para _abrir_geopackage (pode listar camadas internas e tratar melhor)
        - Caso contrário, usa _abrir_generico para tentar carregar diretamente como vetor/raster

        Retorno:
          (ok, erro) onde:
            - ok = True se conseguiu carregar
            - erro = mensagem de erro (ou None em caso de sucesso)
        """
        ext = os.path.splitext(path)[1].lower().strip()

        if ext == ".gpkg":
            return self._abrir_geopackage(path)

        # “arquivo qualquer”: tenta abrir direto (vetor/raster) sem lógica adicional
        return self._abrir_generico(path)

    def _abrir_generico(self, path: str) -> tuple[bool, str | None]:
        """
        Tenta abrir um arquivo “genérico” no QGIS, primeiro como vetor e depois como raster.

        Estratégia:
          1) Cria um nome base a partir do nome do arquivo (sem extensão)
          2) Tenta carregar como QgsVectorLayer (provider OGR)
          3) Se falhar, tenta carregar como QgsRasterLayer
          4) Se ambos falharem, retorna erro

        Retorno:
          (ok, erro) onde:
            - ok = True se conseguiu adicionar a camada ao projeto
            - erro = mensagem curta em caso de falha (None em sucesso)
        """
        base = os.path.splitext(os.path.basename(path))[0] or "Camada"  # nome amigável para a layer

        # 1) tenta vetor (OGR cobre a maior parte dos formatos vetoriais)
        v = QgsVectorLayer(path, base, "ogr")
        if v.isValid():
            QgsProject.instance().addMapLayer(v, True)  # adiciona na raiz do projeto (visível no painel)
            return True, None

        # 2) tenta raster (GDAL por baixo do QgsRasterLayer)
        r = QgsRasterLayer(path, base)
        if r.isValid():
            QgsProject.instance().addMapLayer(r, True)  # adiciona na raiz do projeto
            return True, None

        # 3) fallback: não reconheceu como vetor nem raster
        return False, self.tr("Arquivo inválido ou formato não suportado pelo QGIS.")

    def _abrir_geopackage(self, gpkg_path: str) -> tuple[bool, str | None]:
        """
        Abre um GeoPackage (.gpkg) e adiciona as camadas vetoriais ao projeto.

        Comportamento:
          - Lê o gpkg via SQLite para listar tabelas em gpkg_contents com data_type='features'
          - Para cada sublayer (tabela), tenta abrir como QgsVectorLayer
          - Evita duplicação comparando a URI (source) com camadas já carregadas no projeto
          - Se a camada for de LINHA (canais), adiciona dentro do grupo 'CANAIS' e tenta:
              1) restaurar estilo salvo no próprio GPKG (layer_styles/default)
              2) fallback: reaplicar simbologia e rotulagem do plugin (se existirem campos)
              3) registrar novamente auto-preenchimento de CN
          - Camadas que não são linha são adicionadas normalmente na árvore do projeto

        Retorno:
          (ok, erro) onde:
            - ok = True se pelo menos uma camada de linha foi adicionada ao grupo CANAIS
            - erro = mensagem curta em caso de falha (None em sucesso)
        """
        if not os.path.exists(gpkg_path):
            return False, self.tr("Arquivo não encontrado.")

        # lista sublayers via SQL (robusto p/ GPKG)
        try:
            con = sqlite3.connect(gpkg_path)
            cur = con.cursor()
            cur.execute("SELECT table_name FROM gpkg_contents WHERE data_type='features'")
            layer_names = [r[0] for r in cur.fetchall()]
            con.close()
        except Exception as e:
            return False, self.tr("Falha ao ler o GeoPackage: {error}").format(error=str(e))

        if not layer_names:
            return False, self.tr("GeoPackage sem camadas vetoriais (features).")

        group = self._ensure_canais_group()  # grupo CANAIS
        project = QgsProject.instance()

        added_any = False

        # evita duplicar
        existing_sources = set()
        for lyr in project.mapLayers().values():
            try:
                existing_sources.add(lyr.source())
            except Exception:
                pass  # nosec B110

        for lname in layer_names:
            uri = f"{gpkg_path}|layername={lname}"
            if uri in existing_sources:
                continue

            vlayer = QgsVectorLayer(uri, lname, "ogr")
            if not vlayer.isValid():
                continue

            # detecta se é linha (canal)
            try:
                is_line = (vlayer.geometryType() == QgsWkbTypes.GeometryType.LineGeometry)
            except Exception:
                is_line = True  # fallback

            if is_line:
                # linhas: adiciona sem ir pra raiz e coloca no grupo CANAIS
                project.addMapLayer(vlayer, False)
                group.addLayer(vlayer)

                restored = self._try_restore_saved_style(vlayer)

                if not restored:
                    try:
                        if vlayer.fields().indexOf("Declividade(I)") != -1:
                            self.apply_arrow_symbology(vlayer)
                    except Exception:
                        pass  # nosec B110
                    try:
                        if vlayer.fields().indexOf("CN") != -1:
                            self.apply_cn_labeling(vlayer)
                    except Exception:
                        pass  # nosec B110

                try:
                    self._register_cn_layer(vlayer)
                except Exception:
                    pass  # nosec B110

                added_any = True
            else:
                # não é canal: adiciona UMA vez na árvore normal (raiz)
                project.addMapLayer(vlayer, True)

        if not added_any:
            return False, self.tr("Nenhuma camada de linha válida foi adicionada ao grupo CANAIS.")

        # atualiza lista do tableViewCamada a partir do grupo CANAIS
        try:
            self._reload_tableViewCamada_from_group()
        except Exception:
            pass  # nosec B110

        # estado dos botões (DXF etc.)
        try:
            self._update_pushButtonCamadaDXF_state()
        except Exception:
            pass  # nosec B110

        return True, None

    def _try_restore_saved_style(self, layer) -> bool:
        """
        Tenta aplicar o estilo salvo no provider (ex: GeoPackage layer_styles com default).
        Retorna True se conseguiu.
        """
        ok = False

        # 1) default style (provider)
        try:
            res = layer.loadDefaultStyle()
            if isinstance(res, tuple):
                ok = bool(res[0])
            else:
                ok = bool(res)
        except Exception:
            ok = False

        if ok:
            try:
                layer.triggerRepaint()
            except Exception:
                pass  # nosec B110
            try:
                self.iface.mapCanvas().refresh()
            except Exception:
                pass  # nosec B110
            return True

        return False
#////////////////////////////////////////////
    def _sim2_ensure_init(self):
        """Garante que o estado da simulação existe (idempotente)."""

        if getattr(self, "_sim2_inited", False):
            return
        self._sim2_inited = True

        # Estado
        self._sim2_levels = []
        self._sim2_idx = 0
        self._sim2_depth_layer_id = None

        self._sim2_original_transparency = None
        self._sim2_waiting_depth = False
        self._sim2_layers_before = set()

        # Timer
        self._sim2_timer = QTimer(self)
        self._sim2_timer.timeout.connect(self._sim2_on_tick)

        # Sinais (conecta só uma vez)
        if not getattr(self, "_sim2_signals_connected", False):
            self._sim2_signals_connected = True

            if hasattr(self, "pushButtonGerar"):
                self.pushButtonGerar.clicked.connect(self.on_pushButtonGerar_clicked)

            if hasattr(self, "doubleSpinBoxTempo"):
                self.doubleSpinBoxTempo.valueChanged.connect(self._sim2_on_tempo_changed)

            if hasattr(self, "horizontalSlider"):
                self.horizontalSlider.setEnabled(False)  # slider = relógio
                self.horizontalSlider.setMinimum(0)
                self.horizontalSlider.setMaximum(0)
                self.horizontalSlider.valueChanged.connect(self._sim2_on_slider_changed)

    def on_pushButtonGerar_clicked(self):
        """
        Gera 'frames' (thresholds) e inicia a simulação.
        Independente do botão de profundidade: se não achar raster de profundidade,
        dispara on_pushButtonPronfundidade_clicked() e espera surgir.
        """
        self._sim2_ensure_init()
        # toggle: se já está tocando, para
        if hasattr(self, "_sim2_timer") and self._sim2_timer.isActive():
            self._sim2_stop(restore=True)
            return

        # lê parâmetros
        vmin = float(self.doubleSpinBoxMinimo.value()) if hasattr(self, "doubleSpinBoxMinimo") else 0.0
        vmax = float(self.doubleSpinBoxMaximo.value()) if hasattr(self, "doubleSpinBoxMaximo") else vmin
        nframes = int(self.spinBoxPasso.value()) if hasattr(self, "spinBoxPasso") else 1
        nframes = max(1, nframes)

        # monta frames (thresholds)
        self._sim2_levels = self._sim2_build_levels(vmin, vmax, nframes)
        self._sim2_idx = 0

        # prepara slider (relógio)
        if hasattr(self, "horizontalSlider"):
            self.horizontalSlider.blockSignals(True)
            self.horizontalSlider.setEnabled(False)
            self.horizontalSlider.setRange(0, max(0, len(self._sim2_levels) - 1))
            self.horizontalSlider.setValue(0)
            self.horizontalSlider.blockSignals(False)

        # resolve raster de profundidade
        depth_layer = self._sim2_resolve_depth_layer()
        if depth_layer is None:
            # não existe (ou não foi capturado): dispara profundidade e espera
            self._sim2_request_depth_and_wait()
            return

        self._sim2_start(depth_layer)

    def _sim2_build_levels(self, vmin: float, vmax: float, nframes: int) -> list[float]:
        """Retorna lista de thresholds igualmente espaçados (N frames)."""
        if nframes <= 1:
            return [float(vmin)]
        vmin = float(vmin)
        vmax = float(vmax)
        step = (vmax - vmin) / float(nframes - 1)
        return [vmin + i * step for i in range(nframes)]

    def _sim2_resolve_depth_layer(self) -> QgsRasterLayer | None:
        """
        Tenta achar o raster base de profundidade:
        1) se você já guarda algum id (ex.: self._sim_base_depth_layer_id), usa.
        2) senão, tenta heurística por nome (Profundidade/Depth).
        """
        project = QgsProject.instance()

        # 1) id guardado pelo seu fluxo (se existir)
        for attr in ("_sim2_depth_layer_id", "_sim_base_depth_layer_id"):
            if hasattr(self, attr):
                lid = getattr(self, attr, None)
                lyr = project.mapLayer(lid) if lid else None
                if isinstance(lyr, QgsRasterLayer) and lyr.isValid():
                    self._sim2_depth_layer_id = lyr.id()
                    return lyr

        # 2) heurística por nome (fallback)
        candidates: list[QgsRasterLayer] = []
        for lyr in project.mapLayers().values():
            if isinstance(lyr, QgsRasterLayer) and lyr.isValid():
                nm = (lyr.name() or "").lower()
                if ("profund" in nm) or ("depth" in nm):
                    candidates.append(lyr)

        if not candidates:
            return None

        # pega o “último” candidato (ordem do dict geralmente reflete inserção recente)
        depth_layer = candidates[-1]
        self._sim2_depth_layer_id = depth_layer.id()
        return depth_layer

    def _sim2_request_depth_and_wait(self):
        """
        Dispara o cálculo de profundidade e espera surgir um raster de profundidade.

        Patch (Opção B):
        - quando a simulação (T. Real) precisar gerar profundidade automaticamente,
          usa um h_min "seguro" baseado em min(vmin, vmax) para não “matar” o raster
          quando o usuário coloca Minimo > Maximo (para inverter a animação).
        """
        self._sim2_ensure_init()
        if self._sim2_waiting_depth:
            return

        self._sim2_waiting_depth = True
        self._sim2_layers_before = set(QgsProject.instance().mapLayers().keys())

        # conecta um listener temporário
        QgsProject.instance().layerWasAdded.connect(self._sim2_on_layer_added)

        # calcula h_min seguro baseado na faixa da simulação
        vmin = float(self.doubleSpinBoxMinimo.value()) if hasattr(self, "doubleSpinBoxMinimo") else 0.0
        vmax = float(self.doubleSpinBoxMaximo.value()) if hasattr(self, "doubleSpinBoxMaximo") else vmin
        h_min_safe = min(vmin, vmax)
        if h_min_safe < 0.0:
            h_min_safe = 0.0

        # dispara seu fluxo de profundidade (pode ser async)
        if hasattr(self, "on_pushButtonPronfundidade_clicked"):
            try:
                self.on_pushButtonPronfundidade_clicked(gerar_vetor=False, h_min_override=h_min_safe)
            except Exception:
                self._sim2_release_depth_wait()
                raise
        else:
            self._sim2_release_depth_wait()
            self.mostrar_mensagem(self.tr("Não encontrei on_pushButtonPronfundidade_clicked para gerar profundidade."), "Erro")

    def _sim2_release_depth_wait(self):
        """Desconecta o listener temporário de camada adicionada."""
        if self._sim2_waiting_depth:
            try:
                QgsProject.instance().layerWasAdded.disconnect(self._sim2_on_layer_added)
            except Exception:
                pass  # nosec B110
        self._sim2_waiting_depth = False

    def _sim2_on_layer_added(self, layer):
        """
        Listener: quando uma camada nova entra no projeto, tenta capturar a profundidade.
        """
        try:
            if not layer:
                return

            # só novas
            if layer.id() in self._sim2_layers_before:
                return

            if isinstance(layer, QgsRasterLayer) and layer.isValid():
                nm = (layer.name() or "").lower()
                if ("profund" in nm) or ("depth" in nm):
                    self._sim2_depth_layer_id = layer.id()
                    self._sim2_release_depth_wait()
                    self._sim2_start(layer)
        except Exception:
            # em caso de exceção, não deixa listener preso
            self._sim2_release_depth_wait()

    def _sim2_start(self, depth_layer: QgsRasterLayer):
        """Inicia a simulação: guarda transparência original, aplica frame 0 e liga timer."""
        if not isinstance(depth_layer, QgsRasterLayer) or not depth_layer.isValid():
            self.mostrar_mensagem(self.tr("Raster de profundidade inválido para simulação."), "Erro")
            return

        # guarda transparência original (para restaurar ao parar)
        self._sim2_store_original_transparency(depth_layer)

        # aplica frame inicial
        self._sim2_apply_frame(0)

        # liga timer com tempo atual
        self._sim2_timer.setInterval(self._sim2_get_interval_ms())
        self._sim2_timer.start()

        # opcional: muda texto do botão para indicar “parar”
        if hasattr(self, "pushButtonGerar"):
            self.pushButtonGerar.setText(self.tr("Parar simulação"))

        try:
            self._update_action_buttons_state()
        except Exception:
            pass  # nosec B110

    def _sim2_stop(self, restore: bool = True):
        """Para o timer e restaura transparência original (opcional)."""
        if hasattr(self, "_sim2_timer") and self._sim2_timer.isActive():
            self._sim2_timer.stop()

        depth_layer = QgsProject.instance().mapLayer(self._sim2_depth_layer_id) if self._sim2_depth_layer_id else None
        if restore and isinstance(depth_layer, QgsRasterLayer) and depth_layer.isValid():
            self._sim2_restore_original_transparency(depth_layer)
            depth_layer.triggerRepaint()

        if hasattr(self, "pushButtonGerar"):
            self.pushButtonGerar.setText(self.tr("Pocas (T. Real)"))

        try:
            self._update_action_buttons_state()
        except Exception:
            pass  # nosec B110

    def _sim2_get_interval_ms(self) -> int:
        """Tempo por frame em ms, baseado no doubleSpinBoxTempo (segundos)."""
        tempo_s = float(self.doubleSpinBoxTempo.value()) if hasattr(self, "doubleSpinBoxTempo") else 1.0
        tempo_s = max(0.05, tempo_s)  # evita 0
        return int(tempo_s * 1000.0)

    def _sim2_on_tempo_changed(self, *_):
        """Atualiza velocidade enquanto estiver tocando."""
        if hasattr(self, "_sim2_timer") and self._sim2_timer.isActive():
            self._sim2_timer.setInterval(self._sim2_get_interval_ms())

    def _sim2_on_tick(self):
        """Avança o 'relógio' (slider) e aplica o frame correspondente."""
        if not self._sim2_levels:
            self._sim2_stop(restore=True)
            return

        self._sim2_idx += 1
        if self._sim2_idx >= len(self._sim2_levels):
            self._sim2_idx = 0  # loop infinito; se quiser parar no fim, troca aqui

        self._sim2_apply_frame(self._sim2_idx)

    def _sim2_on_slider_changed(self, idx: int):
        """
        Só faz sentido se o slider estiver habilitado para 'scrub'.
        Como o slider é o "relógio", isso normalmente só dispara via setValue().
        """
        # Se a inundação estiver rodando, ignora mudanças do slider (ele está sendo usado por ela)
        if getattr(self, "_inun_running", False):
            return

        self._sim2_apply_frame(int(idx))

    def _sim2_apply_frame(self, idx: int):
        """Aplica threshold do frame idx no raster base e atualiza o slider."""
        if not self._sim2_levels:
            return

        idx = max(0, min(int(idx), len(self._sim2_levels) - 1))
        threshold = float(self._sim2_levels[idx])

        depth_layer = QgsProject.instance().mapLayer(self._sim2_depth_layer_id) if self._sim2_depth_layer_id else None
        if not isinstance(depth_layer, QgsRasterLayer) or not depth_layer.isValid():
            # self.mostrar_mensagem("Raster de profundidade não está mais disponível no projeto.", "Erro")
            self._sim2_stop(restore=False)
            return

        self._sim2_apply_threshold(depth_layer, threshold)

        if hasattr(self, "horizontalSlider"):
            self.horizontalSlider.blockSignals(True)
            self.horizontalSlider.setValue(idx)
            self.horizontalSlider.blockSignals(False)

    def _sim2_store_original_transparency(self, depth_layer: QgsRasterLayer):
        """Salva a lista atual de transparência do renderer para restaurar depois."""
        self._sim2_original_transparency = None
        ren = depth_layer.renderer()
        if ren is None:
            return

        rt = ren.rasterTransparency()
        if rt is None:
            self._sim2_original_transparency = []
            return

        items = []
        try:
            for p in rt.transparentSingleValuePixelList() or []:
                items.append((float(p.min), float(p.max), float(p.percentTransparent)))
        except Exception:
            items = []

        self._sim2_original_transparency = items

    def _sim2_restore_original_transparency(self, depth_layer: QgsRasterLayer):
        """Restaura a transparência original salva."""
        ren = depth_layer.renderer()
        if ren is None:
            return

        orig = self._sim2_original_transparency
        if orig is None:
            return

        rt = QgsRasterTransparency()
        px_list = []
        for mn, mx, pct in orig:
            px = QgsRasterTransparency.TransparentSingleValuePixel()
            px.min = mn
            px.max = mx
            px.percentTransparent = pct
            px_list.append(px)

        rt.setTransparentSingleValuePixelList(px_list)
        ren.setRasterTransparency(rt)

    def _sim2_apply_threshold(self, depth_layer: QgsRasterLayer, threshold: float):
        """
        Esconde tudo que for < threshold via transparência por faixa.
        Isso preserva o estilo (rampa de cores) que você já aplicou no raster.
        """
        ren = depth_layer.renderer()
        if ren is None:
            return

        # começa com a transparência original (se houver)
        base_items = self._sim2_original_transparency or []
        px_list = []

        # reconstroi itens originais
        for mn, mx, pct in base_items:
            px = QgsRasterTransparency.TransparentSingleValuePixel()
            px.min = float(mn)
            px.max = float(mx)
            px.percentTransparent = float(pct)
            px_list.append(px)

        # adiciona nossa faixa: (-inf .. threshold-eps) => 100% transparente
        eps = 1e-9
        px_th = QgsRasterTransparency.TransparentSingleValuePixel()
        px_th.min = -1e20
        px_th.max = float(threshold) - eps
        px_th.percentTransparent = 100.0
        px_list.append(px_th)

        rt = QgsRasterTransparency()
        rt.setTransparentSingleValuePixelList(px_list)
        ren.setRasterTransparency(rt)

        depth_layer.triggerRepaint()
#////////////////////////////////////////////
    def _can_run_taudem_inundacao(self) -> bool:
        """Retorna True se os rasters necessários do TauDEM (FEL, P e SRC) existem e são válidos para o DEM atual."""
        layer_id = self.comboBoxRaster.currentData()  # id do DEM selecionado no combo
        dem_layer = QgsProject.instance().mapLayer(layer_id)  # resolve para QgsRasterLayer
        if not isinstance(dem_layer, QgsRasterLayer):
            return False  # nada selecionado ou não é raster

        fel = self._find_taudem_raster_for_dem(dem_layer, "FEL")  # DEM preenchido (fill)
        p   = self._find_taudem_raster_for_dem(dem_layer, "D8 FlowDir (P)")  # direção D8 (P)
        src = self._find_taudem_raster_for_dem(dem_layer, self.tr("Canais (SRC"))  # raster de canais (streams)

        # só libera se todos existem e estão válidos no projeto
        return bool(fel and p and src and fel.isValid() and p.isValid() and src.isValid())

    def _add_taudem_raster_to_subgroup(self, layer: QgsRasterLayer, *, subgroup_name: str, short_code: str):
        """
        Adiciona raster dentro de: TauDEM - Drenagem / <subgroup_name>
        (fica excluído do comboBoxRaster pelo seu filtro de grupos).
        """
        log_prefix = "TauDEM - Tempo Salvo Tools"

        if not isinstance(layer, QgsRasterLayer) or not layer.isValid():
            QgsMessageLog.logMessage(self.tr("[{short_code}] Raster inválido, não será adicionado.").format(short_code=short_code), log_prefix, level=Qgis.MessageLevel.Warning)
            return

        project = QgsProject.instance()
        project.addMapLayer(layer, addToLegend=False)

        root = project.layerTreeRoot()
        gmain = root.findGroup(self.tr("TauDEM - Drenagem"))
        if gmain is None:
            gmain = root.addGroup(self.tr("TauDEM - Drenagem"))

        gsub = gmain.findGroup(subgroup_name)
        if gsub is None:
            gsub = gmain.addGroup(subgroup_name)

        gsub.addLayer(layer)

        # mantém organizado
        gmain.setExpanded(True)
        gsub.setExpanded(True)
        node = root.findLayer(layer.id())
        if node:
            node.setExpanded(False)

    def _find_taudem_layer_by_exact_name(self, layer_name: str) -> QgsRasterLayer | None:
        project = QgsProject.instance()
        root = project.layerTreeRoot()
        g = root.findGroup(self.tr("TauDEM - Drenagem"))
        if g is None:
            return None

        for node in g.findLayers():
            lyr = node.layer()
            if isinstance(lyr, QgsRasterLayer) and lyr.name() == layer_name and lyr.isValid():
                return lyr
        return None

    def _get_taudem_products_for_dem(self, dem_layer: QgsRasterLayer) -> tuple[QgsRasterLayer | None, QgsRasterLayer | None, QgsRasterLayer | None]:
        """
        Retorna os produtos FEL, P e SRC associados ao MDT.
        """
        if (not isinstance(dem_layer, QgsRasterLayer)
            or not dem_layer.isValid()):
            return None, None, None

        dem_name = dem_layer.name()

        fel = self._find_taudem_layer_by_exact_name(self.tr("{dem_name} - FEL (TauDEM)").format(dem_name=dem_name))

        p = self._find_taudem_layer_by_exact_name(self.tr("{dem_name} - D8 FlowDir (P)").format(dem_name=dem_name))

        src = self._find_taudem_layer_by_exact_name(self.tr("{dem_name} - Canais (SRC TauDEM)").format(dem_name=dem_name))

        return fel, p, src
#////////////////////////////////////////////
    def _inun_get_interval_ms(self) -> int:
        """Tempo por frame (ms) com base no doubleSpinBoxTempo (segundos)."""
        tempo_s = float(self.doubleSpinBoxTempo.value()) if hasattr(self, "doubleSpinBoxTempo") else 1.0
        tempo_s = max(0.05, tempo_s)
        return int(tempo_s * 1000.0)

    def _inun_build_levels(self, vmin: float, vmax: float, nframes: int) -> list[float]:
        """Lista de níveis igualmente espaçados."""
        nframes = max(1, int(nframes))
        vmin = float(vmin)
        vmax = float(vmax)
        if nframes <= 1:
            return [vmin]
        step = (vmax - vmin) / float(nframes - 1)
        return [vmin + i * step for i in range(nframes)]

    def _inun_apply_level(self, raster_layer: QgsRasterLayer, level: float):
        """
        Mostra apenas (0 .. level] e esconde:
          - <= 0 (seco)
          - > level (ainda não inundou)
        Mantém o estilo azul existente, só mexe na transparência.
        """
        ren = raster_layer.renderer()
        if ren is None:
            return

        prov = raster_layer.dataProvider()
        if prov is None:
            return

        # pega máximo para saber até onde esconder
        try:
            stats = prov.bandStatistics(1, QgsRasterBandStats.Stats.All, raster_layer.extent(), 0)
            max_val = float(stats.maximumValue)
        except Exception:
            max_val = None

        rt = QgsRasterTransparency()
        px_list = []

        # 1) esconde tudo <= 0
        p0 = QgsRasterTransparency.TransparentSingleValuePixel()
        p0.min = -1e20
        p0.max = 0.0
        p0.percentTransparent = 100.0
        px_list.append(p0)

        # 2) esconde tudo > level
        # (se level <= 0, isso basicamente esconde tudo)
        if max_val is not None:
            eps = 1e-12
            p1 = QgsRasterTransparency.TransparentSingleValuePixel()
            p1.min = float(level) + eps
            p1.max = max_val
            p1.percentTransparent = 100.0
            px_list.append(p1)

        # Se você quiser o comportamento inverso (mostrar >= level),
        # troque o bloco (2) por este:
        #   p1.min = -1e20
        #   p1.max = float(level) - eps

        rt.setTransparentSingleValuePixelList(px_list)
        ren.setRasterTransparency(rt)
        raster_layer.triggerRepaint()

    def _inun_ensure_init(self):
        """Inicializa estruturas da simulação de inundação (uma vez só)."""
        if getattr(self, "_inun_inited", False):
            return

        self._inun_inited = True
        self._inun_timer = QTimer(self)
        self._inun_timer.timeout.connect(self._inun_on_tick)

        self._inun_running = False
        self._inun_waiting_layer = False
        self._inun_layer_id = None

        self._inun_levels = []
        self._inun_idx = 0

        self._inun_expected_dem_prefix = None
        self._inun_expected_tag = None  # "taudem" | "whitebox" | "saga"
        self._inun_stage_ref = None     # STAGE usado para gerar o raster base

        # backup transparência original (por layer id)
        # dict: layer_id -> list[(min,max,percent)]
        self._inun_original_transparency = {}

        # Slider da simulação
        self._inun_slider_dragging = False
        self._inun_slider_block = False

        if not getattr(self, "_inun_slider_connected", False):
            self._inun_slider_connected = True

            if hasattr(self, "horizontalSlider"):
                try:
                    self.horizontalSlider.setEnabled(False)
                    self.horizontalSlider.setMinimum(0)
                    self.horizontalSlider.setMaximum(0)
                    self.horizontalSlider.setValue(0)

                    # evita múltiplas conexões
                    try:
                        self.horizontalSlider.valueChanged.disconnect(self._inun_on_slider_changed)
                    except Exception:
                        pass  # nosec B110
                    self.horizontalSlider.valueChanged.connect(self._inun_on_slider_changed)

                    # pause enquanto arrasta
                    try:
                        self.horizontalSlider.sliderPressed.disconnect(self._inun_on_slider_pressed)
                    except Exception:
                        pass  # nosec B110
                    try:
                        self.horizontalSlider.sliderReleased.disconnect(self._inun_on_slider_released)
                    except Exception:
                        pass  # nosec B110

                    self.horizontalSlider.sliderPressed.connect(self._inun_on_slider_pressed)
                    self.horizontalSlider.sliderReleased.connect(self._inun_on_slider_released)

                except Exception:
                    pass  # nosec B110

    def _inun_on_slider_pressed(self):
        """Pausa a animação enquanto o usuário arrasta o slider da inundação."""
        self._inun_slider_dragging = True  # marca que o usuário está interagindo
        try:
            if hasattr(self, "_inun_timer") and self._inun_timer.isActive():
                self._inun_timer.stop()  # evita o timer “brigar” com o arraste
        except Exception:
            pass  # nosec B110

    def _inun_on_slider_released(self):
        """Retoma a animação após soltar o slider, se a simulação estiver ativa."""
        self._inun_slider_dragging = False  # fim do arraste
        # volta a animar se a simulação ainda estiver "rodando"
        try:
            if getattr(self, "_inun_running", False) and hasattr(self, "_inun_timer"):
                self._inun_timer.setInterval(self._inun_get_interval_ms())  # aplica velocidade atual
                self._inun_timer.start()
        except Exception:
            pass  # nosec B110

    def _inun_on_slider_changed(self, v):
        """Atualiza o frame da inundação quando o slider muda (manual ou programático)."""
        if getattr(self, "_inun_slider_block", False):
            return  # ignora alterações feitas internamente (ex.: setValue durante animação)
        if not getattr(self, "_inun_levels", None):
            return  # não há níveis/frames calculados

        try:
            idx = int(v)  # valor do slider vira índice de frame
        except Exception:
            return

        # garante que o índice sempre fique dentro do intervalo válido
        idx = max(0, min(idx, len(self._inun_levels) - 1))
        self._inun_idx = idx  # atualiza índice corrente
        self._inun_apply_frame()  # aplica o frame (atualiza raster/visual)

    def _inun_parse_stage_from_name(self, layer_name: str | None) -> float | None:
        """Extrai STAGE do nome (ex.: 'STAGE=1.25')."""
        if not layer_name:
            return None
        try:
            m = re.search(r"STAGE\s*=\s*([0-9]+(?:\.[0-9]+)?)", layer_name, flags=re.IGNORECASE)
            return float(m.group(1)) if m else None
        except Exception:
            return None

    def _inun_on_tempo_changed(self, *_args):
        """Se estiver rodando, atualiza intervalo do timer."""
        if getattr(self, "_inun_running", False) and hasattr(self, "_inun_timer"):
            try:
                self._inun_timer.setInterval(self._inun_get_interval_ms())
            except Exception:
                pass  # nosec B110

    def _inun_resolve_base_layer(self, dem_layer: QgsRasterLayer | None) -> QgsRasterLayer | None:
        """
        Encontra a camada de INUNDAÇÃO (depth) do DEM selecionado e do motor atual.
        Nunca retorna HAND.
        """
        if not isinstance(dem_layer, QgsRasterLayer) or not dem_layer.isValid():
            return None

        dem_prefix = (dem_layer.name() or "") + " - "

        motor_taudem = hasattr(self, "radioButtonTauDem") and self.radioButtonTauDem.isChecked()
        motor_wbt = hasattr(self, "radioButtonTools") and self.radioButtonTools.isChecked()
        motor_saga = hasattr(self, "radioButtonSAGA") and self.radioButtonSAGA.isChecked()

        tag = None
        if motor_taudem:
            tag = "taudem"
        elif motor_wbt:
            tag = "whitebox"
        elif motor_saga:
            tag = "saga"

        project = QgsProject.instance()
        candidates = []
        for lyr in project.mapLayers().values():
            if not isinstance(lyr, QgsRasterLayer) or not lyr.isValid():
                continue
            nm = lyr.name() or ""
            nl = nm.lower()

            if dem_prefix and (not nm.startswith(dem_prefix)):
                continue

            # não pode ser HAND
            if "hand" in nl:
                continue

            # precisa “parecer” inundação
            if not (("inund" in nl) or ("alag" in nl) or ("flood" in nl) or ("depth" in nl)):
                continue

            # se souber o motor, filtra pelo tag no nome
            if tag and (tag not in nl):
                continue

            candidates.append(lyr)

        # se tiver várias (vários STAGE), pega a “mais nova” (última inserida costuma ficar por último)
        return candidates[-1] if candidates else None

    def _inun_store_original_transparency(self, raster_layer: QgsRasterLayer):
        """Guarda a transparência original para restaurar no stop."""
        try:
            ren = raster_layer.renderer()
            if ren is None:
                return
            rt = ren.rasterTransparency()
            if rt is None:
                self._inun_original_transparency[raster_layer.id()] = []
                return
            px = rt.transparentSingleValuePixelList() or []
            backup = [(float(p.min), float(p.max), float(p.percentTransparent)) for p in px]
            self._inun_original_transparency[raster_layer.id()] = backup
        except Exception:
            self._inun_original_transparency[raster_layer.id()] = []

    def _inun_restore_original_transparency(self, raster_layer: QgsRasterLayer):
        """Restaura a transparência original."""
        try:
            backup = self._inun_original_transparency.get(raster_layer.id(), None)
            if backup is None:
                return

            ren = raster_layer.renderer()
            if ren is None:
                return

            rt = QgsRasterTransparency()
            px_list = []
            for mn, mx, pct in backup:
                p = QgsRasterTransparency.TransparentSingleValuePixel()
                p.min = mn
                p.max = mx
                p.percentTransparent = pct
                px_list.append(p)

            rt.setTransparentSingleValuePixelList(px_list)
            ren.setRasterTransparency(rt)
            raster_layer.triggerRepaint()
        except Exception:
            pass  # nosec B110

    def _inun_apply_stage(self, raster_layer: QgsRasterLayer, stage_level: float):
        """
        Aplica “frame” na camada de INUNDAÇÃO (depth) ajustando transparência.

        Raster base foi calculado com stage_ref (normalmente o Max):
          depth_ref = max(stage_ref - HAND, 0)

        Para simular stage_level:
          células inundadas satisfazem HAND <= stage_level
          como HAND = stage_ref - depth_ref (nas células inundadas),
          equivale a depth_ref >= (stage_ref - stage_level)

        Então a gente mostra apenas depth_ref >= threshold e >0.
        """
        ren = raster_layer.renderer()
        if ren is None:
            return

        stage_ref = getattr(self, "_inun_stage_ref", None)
        if stage_ref is None:
            stage_ref = self._inun_parse_stage_from_name(raster_layer.name())
        if stage_ref is None:
            try:
                stage_ref = float(self.doubleSpinBoxMaximo.value()) if hasattr(self, "doubleSpinBoxMaximo") else None
            except Exception:
                stage_ref = None

        try:
            stage_ref = float(stage_ref) if stage_ref is not None else None
        except Exception:
            stage_ref = None

        try:
            stage_level = float(stage_level)
        except Exception:
            stage_level = 0.0

        # threshold em termos de DEPTH no raster base
        threshold = max(0.0, (stage_ref - stage_level)) if stage_ref is not None else max(0.0, stage_level)

        rt = QgsRasterTransparency()
        px_list = []

        # esconde tudo <= 0 (seco)
        p0 = QgsRasterTransparency.TransparentSingleValuePixel()
        p0.min = -1e20
        p0.max = 0.0
        p0.percentTransparent = 100.0
        px_list.append(p0)

        # esconde profundidades abaixo do threshold para “crescer” a área com o stage
        eps = 1e-12
        if threshold > eps:
            p1 = QgsRasterTransparency.TransparentSingleValuePixel()
            p1.min = 0.0 + eps
            p1.max = float(threshold) - eps
            p1.percentTransparent = 100.0
            px_list.append(p1)

        rt.setTransparentSingleValuePixelList(px_list)
        ren.setRasterTransparency(rt)
        raster_layer.triggerRepaint()

    def _inun_on_layer_added(self, layer: QgsMapLayer):
        """Se estivermos esperando o raster de inundação ser criado, captura e inicia a simulação."""
        if not getattr(self, "_inun_waiting_layer", False):
            return
        if not isinstance(layer, QgsRasterLayer) or not layer.isValid():
            return

        nm = layer.name() or ""
        nl = nm.lower()

        # ignora HAND
        if "hand" in nl:
            return

        # precisa “parecer” inundação
        if not (("inund" in nl) or ("alag" in nl) or ("flood" in nl) or ("depth" in nl)):
            return

        # filtra pelo DEM selecionado no momento da solicitação
        pref = getattr(self, "_inun_expected_dem_prefix", None)
        if pref and (not nm.startswith(pref)):
            return

        # filtra pelo motor esperado (se definido)
        tag = getattr(self, "_inun_expected_tag", None)
        if tag and (tag not in nl):
            return

        # achou: para de esperar e inicia
        try:
            QgsProject.instance().layerWasAdded.disconnect(self._inun_on_layer_added)
        except Exception:
            pass  # nosec B110

        self._inun_waiting_layer = False
        self._inun_layer_id = layer.id()

        self._inun_start(layer)

    def _inun_request_layer_and_wait(self, dem_layer: QgsRasterLayer):
        """Chama o pushButtonInundacao e espera a camada de inundação aparecer para iniciar a simulação."""
        if self._inun_waiting_layer:
            return

        motor_taudem = hasattr(self, "radioButtonTauDem") and self.radioButtonTauDem.isChecked()
        motor_wbt = hasattr(self, "radioButtonTools") and self.radioButtonTools.isChecked()
        motor_saga = hasattr(self, "radioButtonSAGA") and self.radioButtonSAGA.isChecked()

        tag = None
        if motor_taudem:
            tag = "taudem"
        elif motor_wbt:
            tag = "whitebox"
        elif motor_saga:
            tag = "saga"

        self._inun_expected_tag = tag
        self._inun_expected_dem_prefix = (dem_layer.name() or "") + " - "
        self._inun_waiting_layer = True

        try:
            QgsProject.instance().layerWasAdded.disconnect(self._inun_on_layer_added)
        except Exception:
            pass  # nosec B110
        QgsProject.instance().layerWasAdded.connect(self._inun_on_layer_added)

        # dispara a geração normal (assíncrona nos seus tasks)
        self.on_pushButtonInundacao_clicked()

    def _inun_start(self, raster_layer: QgsRasterLayer):
        """Inicia timer e aplica o primeiro frame."""
        self._inun_running = True

        # captura stage_ref (se existir no nome)
        self._inun_stage_ref = self._inun_parse_stage_from_name(raster_layer.name())
        if self._inun_stage_ref is None:
            try:
                self._inun_stage_ref = float(self.doubleSpinBoxMaximo.value()) if hasattr(self, "doubleSpinBoxMaximo") else None
            except Exception:
                self._inun_stage_ref = None

        self._inun_store_original_transparency(raster_layer)

        # botão vira “stop”
        if hasattr(self, "pushButtonInundacaoTreal"):
            try:
                self.pushButtonInundacaoTreal.setText(self.tr("Parar Inundação"))
            except Exception:
                pass  # nosec B110

        self._inun_idx = 0
        self._inun_timer.setInterval(self._inun_get_interval_ms())
        self._inun_timer.start()

        # Configura slider para acompanhar os frames
        if hasattr(self, "horizontalSlider"):
            try:
                self.horizontalSlider.setEnabled(True)
                self.horizontalSlider.setMinimum(0)
                self.horizontalSlider.setMaximum(max(0, len(self._inun_levels) - 1))
                self._inun_slider_block = True
                self.horizontalSlider.blockSignals(True)
                self.horizontalSlider.setValue(self._inun_idx)
                self.horizontalSlider.blockSignals(False)
            finally:
                self._inun_slider_block = False

        # aplica primeiro frame já
        self._inun_apply_frame()

        try:
            self._update_action_buttons_state()
        except Exception:
            pass  # nosec B110

    def _inun_stop(self, restore: bool = True):
        """Para a simulação de inundação e (opcional) restaura a transparência original."""
        self._inun_waiting_layer = False  # não está mais aguardando a camada aparecer
        self._inun_running = False        # marca simulação como parada

        try:
            self._inun_timer.stop()  # interrompe animação/atualizações
        except Exception:
            pass  # nosec B110

        try:
            QgsProject.instance().layerWasAdded.disconnect(self._inun_on_layer_added)  # evita callback pendente
        except Exception:
            pass  # nosec B110

        # Restaura a transparência original do raster usado na simulação (se existir)
        if restore and self._inun_layer_id:
            lyr = QgsProject.instance().mapLayer(self._inun_layer_id)
            if isinstance(lyr, QgsRasterLayer) and lyr.isValid():
                self._inun_restore_original_transparency(lyr)

        # Volta o texto do botão de tempo real para o padrão
        if hasattr(self, "pushButtonInundacaoTreal"):
            try:
                self.pushButtonInundacaoTreal.setText(self.tr("Inundação (Sim)"))
            except Exception:
                pass  # nosec B110

        # Desliga e “zera” o slider para não ficar interativo fora da simulação
        if hasattr(self, "horizontalSlider"):
            try:
                self._inun_slider_block = True      # bloqueia handler do slider durante reset
                self.horizontalSlider.setEnabled(False)
                self.horizontalSlider.setMinimum(0)
                self.horizontalSlider.setMaximum(0)
                self.horizontalSlider.setValue(0)
            finally:
                self._inun_slider_block = False

        # Atualiza botões/ações conforme novo estado (habilita/desabilita)
        try:
            self._update_action_buttons_state()
        except Exception:
            pass  # nosec B110

    def _inun_apply_frame(self):
        """Aplica o frame atual na camada base."""
        if not self._inun_layer_id:
            return
        lyr = QgsProject.instance().mapLayer(self._inun_layer_id)
        if not isinstance(lyr, QgsRasterLayer) or not lyr.isValid():
            self._inun_stop(restore=False)
            return
        if not self._inun_levels:
            return

        lvl = self._inun_levels[self._inun_idx]
        self._inun_apply_stage(lyr, lvl)

    def _inun_on_tick(self):
        """Avança frames."""
        if not self._inun_running:
            return
        if not self._inun_levels:
            return

        self._inun_idx += 1
        if self._inun_idx >= len(self._inun_levels):
            self._inun_idx = 0

        if hasattr(self, "horizontalSlider") and not getattr(self, "_inun_slider_dragging", False):
            try:
                self._inun_slider_block = True
                self.horizontalSlider.blockSignals(True)
                self.horizontalSlider.setValue(self._inun_idx)
                self.horizontalSlider.blockSignals(False)

            finally:
                self._inun_slider_block = False

        self._inun_apply_frame()

    def on_pushButtonInundacaoTreal_clicked(self):
        """
        Play/Stop da simulação.
        Usa:
          - doubleSpinBoxMinimo (stage inicial)
          - doubleSpinBoxMaximo (stage final)
          - spinBoxPasso (qtd de frames)
          - doubleSpinBoxTempo (intervalo s)
        """
        self._inun_ensure_init()

        # toggle stop
        if self._inun_running or self._inun_waiting_layer:
            self._inun_stop(restore=True)
            return

        # DEM selecionado
        layer_id = self.comboBoxRaster.currentData() if hasattr(self, "comboBoxRaster") else None
        dem_layer = QgsProject.instance().mapLayer(layer_id) if layer_id else None
        if not isinstance(dem_layer, QgsRasterLayer) or not dem_layer.isValid():
            self.mostrar_mensagem(self.tr("Selecione um MDT válido no combo antes de simular inundação."), "Erro")
            return

        # níveis
        try:
            vmin = float(self.doubleSpinBoxMinimo.value()) if hasattr(self, "doubleSpinBoxMinimo") else 0.0
        except Exception:
            vmin = 0.0
        try:
            vmax = float(self.doubleSpinBoxMaximo.value()) if hasattr(self, "doubleSpinBoxMaximo") else vmin
        except Exception:
            vmax = vmin

        if vmax < vmin:
            vmin, vmax = vmax, vmin

        try:
            frames = int(self.spinBoxPasso.value()) if hasattr(self, "spinBoxPasso") else 30
        except Exception:
            frames = 30
        frames = max(frames, 2)

        if abs(vmax - vmin) < 1e-12:
            self.mostrar_mensagem(self.tr("Defina um intervalo (Min < Max) para simular inundação."), "Erro")
            return

        self._inun_levels = [vmin + (vmax - vmin) * (i / (frames - 1)) for i in range(frames)]

        # tenta achar camada já existente do motor atual
        base = self._inun_resolve_base_layer(dem_layer)
        if base is None:
            self.mostrar_mensagem(self.tr("Não encontrei a camada de inundação desse motor. Vou gerar e iniciar a simulação automaticamente…"), "Info")
            self._inun_request_layer_and_wait(dem_layer)
            return

        self._inun_layer_id = base.id()
        self._inun_start(base)

    def _set_layer_visibility(self, layer: QgsMapLayer, visible: bool):
        """Mostra/oculta uma camada no painel de camadas (Layer Tree) do QGIS."""
        try:
            root = QgsProject.instance().layerTreeRoot()  # raiz da árvore de camadas do projeto
            node = root.findLayer(layer.id()) if (root and layer) else None  # nó correspondente à layer
            if node is not None:
                node.setItemVisibilityChecked(bool(visible))  # liga/desliga o “olhinho”
        except Exception:
            pass  # nosec B110
#////////////////////////////////////////////
    def _executar_inundacao_taudem(self, dem_layer: QgsRasterLayer | None = None):
        """
        Inundação fluvial (TauDEM) usando HAND:
          - Reusa FEL, P e SRC já criados pelo pushButtonExecutar
          - Usa SOMENTE doubleSpinBoxMaximo como STAGE (m)
          - NÃO gera vetores
        """
        # DEM selecionado
        if dem_layer is None:
            layer_id = self.comboBoxRaster.currentData()
            dem_layer = QgsProject.instance().mapLayer(layer_id)

        if not isinstance(dem_layer, QgsRasterLayer) or not dem_layer.isValid():
            self.mostrar_mensagem(self.tr("Selecione um MDT raster válido no combo."), "Erro")
            return

        # STAGE (m) = doubleSpinBoxMaximo
        stage_m = float(self.doubleSpinBoxMaximo.value()) if hasattr(self, "doubleSpinBoxMaximo") else 0.0
        if stage_m <= 0.0:
            self.mostrar_mensagem(self.tr("Defina um nível d'água (doubleSpinBoxMaximo) maior que 0."), "Erro")
            return

        # acha FEL, P, SRC
        fel_layer, p_layer, src_layer = self._get_taudem_products_for_dem(dem_layer)
        if not (fel_layer and p_layer and src_layer):
            self.mostrar_mensagem(self.tr("Não encontrei FEL / P / SRC do TauDEM para este MDT.\nRode primeiro o pushButtonExecutar com TauDEM."), "Erro")
            return

        # evita rodar duas vezes ao mesmo tempo
        if getattr(self, "_taudem_inund_task", None) is not None:
            self.mostrar_mensagem(self.tr("Já existe um cálculo de inundação em execução."), "Info")
            return

        workspace = self._create_safe_workspace(prefix="ts_taudem_inund_")

        fel_path = fel_layer.source().split(" |", 1)[0]
        p_path   = p_layer.source().split(" |", 1)[0]
        src_path = src_layer.source().split(" |", 1)[0]

        task = TauDEMInundacaoTask(plugin=self, dem_layer=dem_layer, fel_path=fel_path, p_path=p_path, src_path=src_path, stage_m=stage_m, workspace=workspace)
        self._taudem_inund_task = task

        def _finish(success: bool):
            self._taudem_inund_task = None

            if not success:
                err = getattr(task, "error_message", None)
                if err:
                    self.mostrar_mensagem(err, "Erro", forcar=True)
                elif task.isCanceled():
                    self.mostrar_mensagem(self.tr("Inundação cancelada pelo usuário."), "Erro", forcar=True)
                else:
                    self.mostrar_mensagem(self.tr("Falha no cálculo de inundação (HAND)."), "Erro", forcar=True)
                return

            dem_crs = dem_layer.crs()

            # HAND (inicia desmarcado/oculto)
            self._add_taudem_raster(path=task.hand_path, name=self.tr("{dem_name} - HAND (TauDEM)").format(dem_name=dem_layer.name()), dem_crs=dem_crs, short_code="HAND", visible=False)

            # Inundação (1 camada só)
            inund_layer = None
            if task.depth_path and os.path.exists(task.depth_path):
                inund_layer = self._add_taudem_raster(path=task.depth_path, name=self.tr("{dem_name} - Inundação (m) STAGE={stage_m:.3f} (TauDEM)").format(dem_name=dem_layer.name(), stage_m=stage_m), dem_crs=dem_crs, short_code="INUND")

            # estilo azul (se existir)
            if inund_layer and hasattr(self, "_apply_depth_raster_style"):
                try:
                    self._apply_depth_raster_style(inund_layer)
                except Exception:
                    pass  # nosec B110

            self.mostrar_mensagem(self.tr("Inundação (HAND) concluída. STAGE={stage_m:.3f} m").format(stage_m=stage_m), "Sucesso", forcar=True, caminho_pasta=workspace)

            # garante que os botões reflitam o novo estado
            try:
                self._update_action_buttons_state()
            except Exception:
                pass  # nosec B110

        task.taskCompleted.connect(lambda: _finish(True))
        task.taskTerminated.connect(lambda: _finish(False))

        QgsApplication.taskManager().addTask(task)
        self.mostrar_mensagem(self.tr("Cálculo de inundação (HAND/TauDEM) iniciado em segundo plano..."), "Info")

    def _executar_inundacao_saga(self, dem_layer: QgsRasterLayer):
        """
        Pipeline SAGA (sem vetores):
          1) rasteriza canais (vector) -> channels_grid.tif (NoData fora)
          2) SAGA: Vertical Distance to Channel Network -> HAND.tif
          3) RasterCalc -> inundação (depth) = max(stage - hand, 0)
        """
        if not isinstance(dem_layer, QgsRasterLayer) or not dem_layer.isValid():
            self.mostrar_mensagem(self.tr("Selecione um MDT válido no combo antes de executar inundação (SAGA)."), "Erro")
            return

        filled_layer = self._find_saga_filled_layer(dem_layer)
        if not isinstance(filled_layer, QgsRasterLayer) or not filled_layer.isValid():
            self.mostrar_mensagem(self.tr("Não encontrei o DEM preenchido do SAGA.\nExecute primeiro o pushButtonExecutar com o motor SAGA."), "Erro")
            return

        canais_layer = self._find_saga_canais_vector_layer(dem_layer)
        if not isinstance(canais_layer, QgsVectorLayer) or not canais_layer.isValid():
            self.mostrar_mensagem(self.tr("Não encontrei o vetor de canais do SAGA.\nExecute primeiro o pushButtonExecutar com o motor SAGA."), "Erro")
            return

        stage = float(self.doubleSpinBoxMaximo.value()) if hasattr(self, "doubleSpinBoxMaximo") else 0.0
        if stage <= 0:
            self.mostrar_mensagem(self.tr("Defina um nível (doubleSpinBoxMaximo) > 0 para calcular inundação (SAGA)."), "Erro")
            return

        workspace = self._create_safe_workspace(prefix="ts_saga_inund_")

        # guarda referência para não ser coletado e permitir cancelamento depois (se você quiser)
        self._saga_inund_runner = SagaInundacaoRunner(plugin=self, dem_layer=dem_layer, filled_layer=filled_layer, canais_layer=canais_layer, stage=stage, workspace=workspace)
        self._saga_inund_runner.start()

    def _executar_inundacao_whitebox(self, dem_layer: QgsRasterLayer):
        """
        Calcula HAND + Inundação (depth) usando rasters já gerados pelo Whitebox no pushButtonExecutar:
          - D8 pointer (Whitebox)
          - Canais (raster Whitebox)
        Stage = doubleSpinBoxMaximo
        """
        if not isinstance(dem_layer, QgsRasterLayer):
            self.mostrar_mensagem(self.tr("Selecione um MDT válido no combo antes de calcular inundação (Whitebox)."), "Erro")
            return

        pntr_layer = self._find_whitebox_d8_pointer_layer(dem_layer)
        streams_layer = self._find_whitebox_streams_raster_layer(dem_layer)

        if pntr_layer is None or streams_layer is None:
            self.mostrar_mensagem(self.tr("Não encontrei os rasters do Whitebox necessários (D8 pointer e canais raster).\nExecute primeiro o processamento com o motor WhiteboxTools."), "Erro")
            return

        # Stage pela UI
        stage = float(self.doubleSpinBoxMaximo.value()) if hasattr(self, "doubleSpinBoxMaximo") else 0.0
        if stage <= 0:
            self.mostrar_mensagem(self.tr("Defina um nível (doubleSpinBoxMaximo) > 0 para calcular inundação."), "Erro")
            return

        # DEM seguro (caminho sem acentos) para garantir arquivo físico acessível
        safe_dem_layer = self._get_safe_dem_layer(dem_layer)
        if not safe_dem_layer or not safe_dem_layer.isValid():
            self.mostrar_mensagem(self.tr("Falha ao obter DEM em caminho seguro para inundação (Whitebox)."), "Erro")
            return

        workspace = self._create_safe_workspace(prefix="ts_wbt_inund_")

        task = WhiteboxInundacaoTask(plugin=self, dem_layer=dem_layer, safe_dem_layer=safe_dem_layer, pntr_layer=pntr_layer, streams_layer=streams_layer, stage=stage, workspace=workspace)

        self._wbt_inund_task = task  # Seta guard ANTES de enfileirar

        task.taskCompleted.connect(lambda: self._on_whitebox_inund_task_finished(task, True))
        task.taskTerminated.connect(lambda: self._on_whitebox_inund_task_finished(task, False))

        QgsApplication.taskManager().addTask(task)
        self.mostrar_mensagem(self.tr("Inundação (Whitebox): calculando HAND e profundidade…"), "Info")

    def _update_action_buttons_state(self):
        """
        Controla a habilitação dos botões:
          - Executar
          - Profundidade
          - Inundação

        Regras:
          - Executar: MDT válido + motor selecionado
          - Profundidade:
              * Whitebox: só precisa do MDT
              * SAGA: precisa do DEM preenchido SAGA
              * TauDEM: precisa do FEL TauDEM
          - Inundação:
              * TauDEM: precisa (FEL, P, SRC) do TauDEM
              * Whitebox: precisa do raster de canais/streams do Whitebox
              * SAGA: (a implementar) -> desabilitado por enquanto
        """
        project = QgsProject.instance()

        # Verifica raster selecionado
        layer_id = self.comboBoxRaster.currentData() if hasattr(self, "comboBoxRaster") else None
        dem_layer = project.mapLayer(layer_id) if layer_id else None
        has_raster = isinstance(dem_layer, QgsRasterLayer) and dem_layer.isValid()

        # Verifica motor selecionado
        motor_saga = hasattr(self, "radioButtonSAGA") and self.radioButtonSAGA.isChecked()
        motor_taudem = hasattr(self, "radioButtonTauDem") and self.radioButtonTauDem.isChecked()
        motor_wbt = hasattr(self, "radioButtonTools") and self.radioButtonTools.isChecked()
        motor_selected = motor_saga or motor_taudem or motor_wbt

        # pushButtonExecutar
        can_run = has_raster and motor_selected

        # pushButtonPronfundidade
        can_depth = False
        if can_run and dem_layer is not None:
            if motor_wbt:
                can_depth = True
            elif motor_saga:
                saga_filled = self._find_saga_filled_layer(dem_layer)
                can_depth = saga_filled is not None
            elif motor_taudem:
                fel_layer = self._find_taudem_fel_layer(dem_layer)
                can_depth = fel_layer is not None

        # pushButtonInundacao
        can_inund = False
        if can_run and dem_layer is not None:
            if motor_taudem:
                # precisa FEL + P + SRC
                try:
                    fel, p, src = self._get_taudem_products_for_dem(dem_layer)
                    can_inund = (fel is not None) and (p is not None) and (src is not None)
                except Exception:
                    can_inund = False
            elif motor_wbt:
                # precisa do raster de canais/streams
                try:
                    src_wbt = self._find_whitebox_streams_layer(dem_layer)
                    can_inund = (src_wbt is not None)
                except Exception:
                    can_inund = False
            elif motor_saga:
                try:
                    saga_filled = self._find_saga_filled_layer(dem_layer)
                    saga_canais = self._find_saga_channels_vector_layer(dem_layer)

                    stage_ok = True
                    if hasattr(self, "doubleSpinBoxMaximo"):
                        stage_ok = float(self.doubleSpinBoxMaximo.value()) > 0.0

                    can_inund = (saga_filled is not None) and (saga_canais is not None) and stage_ok
                except Exception:
                    can_inund = False

        if hasattr(self, "pushButtonExecutar"):
            self.pushButtonExecutar.setEnabled(can_run)
        if hasattr(self, "pushButtonPronfundidade"):
            self.pushButtonPronfundidade.setEnabled(can_depth)
        if hasattr(self, "pushButtonInundacao"):
            self.pushButtonInundacao.setEnabled(can_inund)

        # pushButtonGerar (simulação de poças / frames)
        # Regras:
        #   - Se já está rodando, mantém habilitado (serve como STOP)
        #   - Se não está rodando: precisa de DEM+motor e (depth já existe OU dá pra calcular depth)
        if hasattr(self, "pushButtonGerar"):
            sim2_running = bool(getattr(self, "_sim2_timer", None) and self._sim2_timer.isActive())

            if sim2_running:
                can_gerar = True
            else:
                depth_exists = False
                try:
                    depth_exists = (self._sim2_resolve_depth_layer() is not None)
                except Exception:
                    depth_exists = False

                can_gerar = bool(has_raster and motor_selected and (depth_exists or can_depth))

            self.pushButtonGerar.setEnabled(can_gerar)

        # pushButtonInundacaoTreal (simulação de inundação em tempo real)
        # Regras:
        #   - Se já está rodando/esperando layer, mantém habilitado (serve como STOP)
        #   - Se não: precisa de DEM+motor, intervalo válido (Min < Max) e
        #         (já existe layer base de inundação do motor atual OU dá pra gerar inundação)
        if hasattr(self, "pushButtonInundacaoTreal"):
            inun_running = bool(getattr(self, "_inun_running", False) or getattr(self, "_inun_waiting_layer", False))

            if inun_running:
                can_inun_treal = True
            else:
                # intervalo Min/Max válido
                stage_ok = True
                try:
                    vmin = float(self.doubleSpinBoxMinimo.value()) if hasattr(self, "doubleSpinBoxMinimo") else 0.0
                    vmax = float(self.doubleSpinBoxMaximo.value()) if hasattr(self, "doubleSpinBoxMaximo") else vmin
                    stage_ok = (vmax > vmin + 1e-12)
                except Exception:
                    stage_ok = False

                # já existe a camada base do motor atual?
                base_ok = False
                try:
                    base_ok = (self._inun_resolve_base_layer(dem_layer) is not None)
                except Exception:
                    base_ok = False

                can_inun_treal = bool(has_raster and motor_selected and stage_ok and (base_ok or can_inund))

            self.pushButtonInundacaoTreal.setEnabled(can_inun_treal)

    def _find_whitebox_streams_raster_layer(self, dem_layer: QgsRasterLayer) -> QgsRasterLayer | None:
        """Procura: '<DEM> - Canais (raster Whitebox)' dentro do grupo WhiteboxTools - Drenagem."""
        if not isinstance(dem_layer, QgsRasterLayer):
            return None
        dem_name = dem_layer.name()

        root = QgsProject.instance().layerTreeRoot()
        grupo = root.findGroup(self.tr("WhiteboxTools - Drenagem"))
        if not grupo:
            return None

        for node in grupo.findLayers():
            lyr = node.layer()
            if isinstance(lyr, QgsRasterLayer) and lyr.isValid():
                nm = (lyr.name() or "")
                if nm.startswith(self.tr("{dem_name} - Canais").format(dem_name=dem_name)):
                    return lyr
        return None

    def _find_whitebox_layer_by_exact_name(self, layer_name: str) -> QgsRasterLayer | None:
        """Procura um raster no grupo 'WhiteboxTools - Drenagem' pelo nome exato (case-sensitive)."""
        project = QgsProject.instance()
        root = project.layerTreeRoot()
        g = root.findGroup(self.tr("WhiteboxTools - Drenagem"))  # grupo onde o plugin coloca saídas do Whitebox
        if g is None:
            return None

        # percorre apenas as layers dentro do grupo e retorna o primeiro match válido
        for node in g.findLayers():
            lyr = node.layer()
            if isinstance(lyr, QgsRasterLayer) and lyr.name() == layer_name and lyr.isValid():
                return lyr

        return None

    def _find_whitebox_streams_layer(self, dem_layer: QgsRasterLayer) -> QgsRasterLayer | None:
        """
        Procura o raster de canais/streams gerado pelo WhiteboxTools para este MDT.
        Tenta por nome exato (mais confiável) e depois por heurística (nome contém palavras-chave).
        """
        if not isinstance(dem_layer, QgsRasterLayer) or not dem_layer.isValid():
            return None

        dem_name = dem_layer.name()
        # 1) Tentativas por nomes "padrão" (ajuste se você usa outro padrão)
        exact_candidates = [
            self.tr("{dem_name} - Canais (SRC Whitebox)").format(dem_name=dem_name),
            self.tr("{dem_name} - Canais (SRC WhiteboxTools)").format(dem_name=dem_name),
            self.tr("{dem_name} - Streams (Whitebox)").format(dem_name=dem_name),
            self.tr("{dem_name} - Stream Network (Whitebox)").format(dem_name=dem_name)]
        for nm in exact_candidates:
            lyr = self._find_whitebox_layer_by_exact_name(nm)
            if lyr is not None:
                return lyr

        # 2) Heurística: varre o grupo e pega o último que “parece” ser streams desse MDT
        project = QgsProject.instance()
        root = project.layerTreeRoot()
        g = root.findGroup(self.tr("WhiteboxTools - Drenagem"))
        if g is None:
            return None

        dn = (dem_name or "").lower()
        keys = ("src", "canais", "streams", "stream")
        matches: list[QgsRasterLayer] = []
        for node in g.findLayers():
            lyr = node.layer()
            if isinstance(lyr, QgsRasterLayer) and lyr.isValid():
                nm = (lyr.name() or "").lower()
                if dn and dn in nm and any(k in nm for k in keys):
                    matches.append(lyr)

        return matches[-1] if matches else None

    def _find_whitebox_d8_pointer_layer(self, dem_layer: QgsRasterLayer) -> QgsRasterLayer | None:
        """Procura: '<DEM> - D8 pointer (Whitebox)' dentro do grupo WhiteboxTools - Drenagem."""
        if not isinstance(dem_layer, QgsRasterLayer):
            return None
        dem_name = dem_layer.name()

        root = QgsProject.instance().layerTreeRoot()
        grupo = root.findGroup(self.tr("WhiteboxTools - Drenagem"))
        if not grupo:
            return None

        for node in grupo.findLayers():
            lyr = node.layer()
            if isinstance(lyr, QgsRasterLayer) and lyr.isValid():
                nm = lyr.name() or ""
                if nm.startswith(self.tr("{dem_name} - D8 pointer").format(dem_name=dem_name)):
                    return lyr
        return None

    def on_pushButtonInundacao_clicked(self):
        """
        Executa a simulação de inundação usando o motor selecionado (TauDEM, WhiteboxTools ou SAGA).

        - Valida se há um MDT/DEM raster selecionado no combo
        - Encaminha para a função de inundação do motor marcado nos radioButtons
        - Mostra mensagens de erro caso falte DEM ou motor selecionado
        """
        layer_id = self.comboBoxRaster.currentData()  # id da camada selecionada no combo
        dem_layer = QgsProject.instance().mapLayer(layer_id)  # resolve para QgsMapLayer

        if not isinstance(dem_layer, QgsRasterLayer):
            self.mostrar_mensagem(self.tr("Selecione um MDT válido no combo antes de executar inundação."), "Erro")
            return

        # Roteia para o motor escolhido
        if self.radioButtonTauDem.isChecked():
            self._executar_inundacao_taudem(dem_layer)  # inundação via TauDEM
        elif self.radioButtonTools.isChecked():
            self._executar_inundacao_whitebox(dem_layer)  # inundação via WhiteboxTools
        elif self.radioButtonSAGA.isChecked():
            self._executar_inundacao_saga(dem_layer)  # inundação via SAGA
        else:
            self.mostrar_mensagem(self.tr("Selecione um motor (SAGA, TauDEM ou WhiteboxTools)."), "Erro")

    def _find_existing_raster_by_path(self, path: str):
        """Procura no projeto um QgsRasterLayer válido cuja source (arquivo) seja exatamente o caminho informado."""
        if not path:
            return None

        want = os.path.normcase(os.path.normpath(path))  # normaliza p/ comparar (Windows: case-insensitive)
        project = QgsProject.instance()

        for lyr in project.mapLayers().values():
            if isinstance(lyr, QgsRasterLayer) and lyr.isValid():
                # source pode vir com sufixos tipo "|layername=..." etc. (pega só o arquivo)
                src = (lyr.source() or "").split("|")[0].strip()
                if not src:
                    continue

                got = os.path.normcase(os.path.normpath(src))  # normaliza o caminho da camada
                if got == want:
                    return lyr  # achou raster já carregado no projeto

        return None  # não encontrou

    def _add_whitebox_raster(self, path: str, name: str, dem_crs, short_code: str, *, visible: bool = True, group_name: str = None):
        """Adiciona (ou reutiliza) um raster do Whitebox no grupo do projeto, evitando duplicação por caminho."""
        if group_name is None:
            group_name = self.tr("WhiteboxTools - Drenagem")
            
        log_prefix = "WhiteboxTools - Tempo Salvo Tools"

        # valida arquivo de saída (evita criar layer inválida e poluir o log)
        if not path or not os.path.exists(path):
            QgsMessageLog.logMessage(self.tr("[{short_code}] Arquivo raster não encontrado: {path}").format(short_code=short_code, path=path), log_prefix, level=Qgis.MessageLevel.Warning)
            return None

        project = QgsProject.instance()
        root = project.layerTreeRoot()

        # garante grupo de destino (onde o plugin organiza as saídas do Whitebox)
        group = root.findGroup(group_name)
        if group is None:
            group = root.addGroup(group_name)

        # 1) Reusa layer existente pelo MESMO arquivo (path) para não duplicar no projeto
        existing = self._find_existing_raster_by_path(path)
        if isinstance(existing, QgsRasterLayer) and existing.isValid():
            # garante que o CRS do raster “case” com o DEM, quando informado
            if dem_crs and dem_crs.isValid():
                try:
                    existing.setCrs(dem_crs)
                except Exception:
                    pass  # nosec B110

            node = root.findLayer(existing.id())
            if node:
                # se estiver fora do grupo correto, move o nó para o grupo do Whitebox
                try:
                    if node.parent() != group:
                        clone = node.clone()            # cria um nó idêntico
                        group.addChildNode(clone)       # insere no grupo certo
                        node.parent().removeChildNode(node)  # remove do grupo anterior
                        node = clone
                except Exception:
                    pass  # nosec B110

                # ajusta visibilidade/expansão do item na árvore
                try:
                    node.setExpanded(False)
                    node.setItemVisibilityChecked(bool(visible))
                except Exception:
                    pass  # nosec B110

            group.setExpanded(True)
            return existing

        # 2) Se não existe, cria e adiciona uma única vez ao grupo
        layer = QgsRasterLayer(path, name, "gdal")
        if not layer.isValid():
            QgsMessageLog.logMessage(self.tr("[{short_code}] Falha ao carregar raster: {path}").format(short_code=short_code, path=path), log_prefix, level=Qgis.MessageLevel.Warning)
            return None

        # aplica CRS do DEM quando fornecido (evita interpretação errada do raster no projeto)
        if dem_crs and dem_crs.isValid():
            layer.setCrs(dem_crs)

        # adiciona no projeto sem inserir na raiz e coloca diretamente no grupo do Whitebox
        project.addMapLayer(layer, False)
        group.addLayer(layer)

        group.setExpanded(True)
        node = root.findLayer(layer.id())
        if node:
            node.setExpanded(False)
            try:
                node.setItemVisibilityChecked(bool(visible))  # “olhinho” ligado/desligado
            except Exception:
                pass  # nosec B110

        return layer

    def _on_whitebox_inund_task_finished(self, task, success: bool):
        """Callback final da task de inundação (Whitebox): adiciona rasters ao projeto, aplica estilo e atualiza UI."""
        log_prefix = "WhiteboxTools - Tempo Salvo Tools"

        # Libera guard no final, dê certo ou errado
        try:
            if not success:
                err = getattr(task, "error_message", None)
                if err:
                    self.mostrar_mensagem(err, self.tr("Erro"), forcar=True)
                elif task.isCanceled():
                    self.mostrar_mensagem(self.tr("Inundação (Whitebox) cancelada."), "Aviso")
                else:
                    self.mostrar_mensagem(self.tr("Falha na inundação (Whitebox)."), "Erro", forcar=True)
                return

            dem_layer = getattr(task, "dem_layer", None)
            if not isinstance(dem_layer, QgsRasterLayer):
                self.mostrar_mensagem(self.tr("Inundação (Whitebox) finalizou, mas não encontrei o DEM original."), "Erro")
                return

            dem_crs = dem_layer.crs()
            dem_name = dem_layer.name()

            # HAND (desmarcado)
            hand_layer = self._add_whitebox_raster(task.hand_path, self.tr("{dem_name} - HAND (Whitebox)").format(dem_name=dem_name), dem_crs, "HAND", visible=False, group_name=self.tr("WhiteboxTools - Drenagem"))

            # Inundação (azul)
            stage_txt = f"{task.stage:.3f}".rstrip("0").rstrip(".")
            inund_layer = self._add_whitebox_raster(task.depth_path, self.tr("{dem_name} - Inundação (m) STAGE={stage_txt} (Whitebox)").format(dem_name=dem_name, stage_txt=stage_txt), dem_crs, "INUND", visible=True, group_name=self.tr("WhiteboxTools - Drenagem"))

            # Aplica estilo “azul”/profundidade, se existir o helper de estilo
            if inund_layer is not None:
                try:
                    if hasattr(self, "_apply_depth_raster_style"):
                        self._apply_depth_raster_style(inund_layer)
                except Exception as e:
                    QgsMessageLog.logMessage(self.tr("Falha ao aplicar estilo azul na inundação: {error}").format(error=str(e)), log_prefix, level=Qgis.MessageLevel.Warning)

            self.mostrar_mensagem(self.tr("Inundação (Whitebox) concluída ✅"), "Info")
            try:
                self._update_action_buttons_state()
            except Exception:
                pass  # nosec B110

        finally:
            # Libera referência da task atual (evita “travar” novas execuções)
            if getattr(self, "_wbt_inund_task", None) is task:
                self._wbt_inund_task = None
#////////////////////////////////////////////
    def _init_textBrowserInfo(self):
        """Configura o QTextBrowser de ajuda (HTML): modo leitura, links/âncoras e conteúdo inicial."""
        w = getattr(self, "textBrowserInfo", None)
        if w is None:
            return  # UI não possui o widget (ou objectName diferente)

        # Segurança/UX: evita edição do conteúdo de ajuda
        w.setReadOnly(True)

        # Controla abertura de links (internos vs externos) via callback
        try:
            w.setOpenExternalLinks(False)  # não abre automaticamente no navegador
            w.setOpenLinks(False)          # não navega automaticamente (vamos tratar no slot)
        except Exception:
            pass  # nosec B110

        # Evita múltiplas conexões (reabrir dock/recarregar UI pode duplicar sinais)
        if hasattr(w, "anchorClicked"):
            try:
                w.anchorClicked.disconnect()  # remove conexão anterior, se houver
            except Exception:
                pass  # nosec B110
            w.anchorClicked.connect(self._on_info_anchor_clicked)  # trata âncoras e links externos

        w.setHtml(self._build_info_html())  # injeta o HTML do manual/ajuda

    def _on_info_anchor_clicked(self, url):
        """Trata cliques no HTML do QTextBrowser: âncoras internas (#secao) ou links externos (navegador)."""
        w = getattr(self, "textBrowserInfo", None)
        if w is None:
            return  # widget não existe/foi renomeado

        frag = url.fragment()  # parte depois do '#'
        if frag:
            # Link interno: navega para a âncora (seção) dentro do próprio QTextBrowser
            try:
                w.scrollToAnchor(frag)
            except Exception:
                pass  # nosec B110
            return

        # Link externo: abre no navegador padrão do sistema
        QDesktopServices.openUrl(url)

    def _build_info_html(self) -> str:
        return """
        <html>
        <head>
          <meta charset="utf-8">
          <style>
            body { font-family: Segoe UI, Arial; font-size: 10pt; line-height: 1.35; }
            h2 { margin: 6px 0 10px 0; }
            h3 { margin: 18px 0 6px 0; }
            h4 { margin: 12px 0 6px 0; }
            .toc { background:#f4f7fb; border:1px solid #d7e0ea; padding:10px; border-radius:10px; }
            .toc a { text-decoration:none; }
            .toc a:hover { text-decoration:underline; }
            .mono { font-family: Consolas, monospace; }
            .note { background:#fff7e6; border:1px solid #f2d39a; padding:8px 10px; border-radius:10px; }
            .ok { background:#ecfff2; border:1px solid #b7e6c5; padding:8px 10px; border-radius:10px; }
            .warn { background:#fff1f2; border:1px solid #f4b4be; padding:8px 10px; border-radius:10px; }
            .step { margin: 6px 0; }
            .small { color:#444; font-size: 9pt; }
            .top { float:right; font-size:9pt; }
            .kbd { font-family: Consolas, monospace; background:#eef2f7; border:1px solid #dde3ea; padding:1px 6px; border-radius:6px; }
            hr { border:none; border-top:1px solid #e4e8ee; margin: 14px 0; }
            ul { margin: 6px 0 10px 18px; }
          </style>
        </head>

        <body>

        <a name="top" id="top"></a>
        <h2>""" + self.tr("Configuração de Uso do Plugin") + """</h2>

        <div class="toc">
          <b>""" + self.tr("Menu") + """</b><br>
          • <a href="#saga">""" + self.tr("SAGA: obter, instalar e configurar") + """</a><br>
          • <a href="#saga_uso">""" + self.tr("Como usar o motor SAGA") + """</a><br>
          <br>
          • <a href="#taudem">""" + self.tr("TauDEM: obter, instalar e configurar") + """</a><br>
          • <a href="#taudem_uso">""" + self.tr("Como usar o motor TauDEM") + """</a><br>
          <br>
          • <a href="#whitebox">""" + self.tr("WhiteboxTools: obter e instalar") + """</a><br>
          • <a href="#whitebox_uso">""" + self.tr("Como usar o motor WhiteboxTools") + """</a><br>
          <br>
          • <a href="#pocas">""" + self.tr("Como usar: Poças (Simulação 2)") + """</a><br>
          • <a href="#inundacao">""" + self.tr("Como usar: Inundação (Simulação 1)") + """</a><br>
          • <a href="#inundacao_rt">""" + self.tr("Como usar: Inundação em Tempo Real") + """</a><br>
          <br>
          • <a href="#qgis">""" + self.tr("Ativar/validar providers no QGIS") + """</a><br>
          • <a href="#diag">""" + self.tr("Diagnóstico rápido") + """</a><br>
        </div>

        <hr>

        <a name="saga" id="saga"></a>
        <h3>SAGA <span class="top"><a href="#top">voltar ao topo</a></span></h3>

        <div class="note">
          <b>Versão recomendada (Windows): SAGA GIS 9.11.0</b><br>
          <span class="small">Se você usar o provider “SAGA NextGen”, ele pede SAGA 9.2+.</span>
        </div>

        <div class="step"><b>Download (oficial):</b></div>
        <ul>
          <li><a href="https://sourceforge.net/projects/saga-gis/files/">SourceForge (arquivos/versões)</a></li>
          <li><span class="small">Procure o zip do Windows (ex.: <span class="mono">saga-9.11.0_msw.zip</span>).</span></li>
        </ul>

        <div class="step"><b>Instalação:</b></div>
        <ul>
          <li>Extraia o ZIP para uma pasta fixa (ex.: <span class="mono">C:\\SIG\\SAGA\\</span>).</li>
          <li>No QGIS: <b>Processamento → Opções → Provedores → SAGA</b> (ou “SAGA NextGen”) e aponte para o executável/pasta do SAGA.</li>
          <li>Teste na Caixa de Ferramentas procurando <span class="mono">saga:</span>.</li>
        </ul>

        <a name="saga_uso" id="saga_uso"></a>
        <h3>Como usar o motor SAGA <span class="top"><a href="#top">voltar ao topo</a></span></h3>

        <div class="ok">
          <b>Fluxo típico:</b> DEM → (ajustes/threshold) → Executar → Rede (vetor) + Bacias (vetor/raster) + produtos auxiliares.
        </div>

        <ul>
          <li><b>1) Selecione o DEM</b> no combo do plugin (<span class="kbd">MDT/DEM</span>).</li>
          <li><b>2) Escolha o motor</b> como <b>SAGA</b>.</li>
          <li><b>3) Ajuste o threshold</b>: valores maiores geram menos canais; menores geram mais detalhes (e mais ruído).</li>
          <li><b>4) Execute</b>. O plugin cria um grupo do SAGA e adiciona camadas de rede/bacias e auxiliares.</li>
          <li><b>5) Conferência rápida:</b> valide se a rede segue os talvegues e se as bacias fecham corretamente.</li>
        </ul>

        <hr>

        <a name="taudem" id="taudem"></a>
        <h3>TauDEM <span class="top"><a href="#top">voltar ao topo</a></span></h3>

        <div class="ok">
          <b>Boa notícia:</b> basta o TauDEM estar instalado no computador. O plugin tenta localizar e usar automaticamente.
          <br><span class="small">Se não localizar (ou se você quiser apontar manualmente), informe a pasta do TauDEM e o <span class="mono">mpiexec</span>.</span>
        </div>

        <div class="step"><b>Download (oficial):</b></div>
        <ul>
          <li><a href="https://hydrology.usu.edu/taudem/taudem5/downloads.html">TauDEM (USU) downloads</a></li>
          <li><a href="https://github.com/dtarb/TauDEM/releases">TauDEM releases (GitHub)</a></li>
        </ul>

        <div class="step"><b>Instalação (Windows, caminho mais fácil):</b></div>
        <ul>
          <li>Use o “Complete Windows installer” quando disponível.</li>
          <li>Depois de instalado, você não precisa “ativar” nada: o plugin detecta e executa.</li>
        </ul>

        <a name="taudem_uso" id="taudem_uso"></a>
        <h3>Como usar o motor TauDEM <span class="top"><a href="#top">voltar ao topo</a></span></h3>

        <div class="ok">
          <b>Fluxo típico:</b> DEM → D8/PitRemove → acumulação → streams → NET (vetor) + ORD (raster).
        </div>

        <ul>
          <li><b>1) Selecione o DEM</b> no plugin.</li>
          <li><b>2) Escolha o motor</b> como <b>TauDEM</b>.</li>
          <li><b>3) Ajuste o threshold</b>: controla a densidade da rede.</li>
          <li><b>4) Execute</b> para gerar NET/ORD e bacias conforme a opção.</li>
        </ul>

        <hr>

        <a name="whitebox" id="whitebox"></a>
        <h3>WhiteboxTools <span class="top"><a href="#top">voltar ao topo</a></span></h3>

        <div class="note">
          <b>Importante:</b> o plugin/provider do QGIS geralmente <u>não</u> inclui o binário do WhiteboxTools.
          Você precisa instalar o WhiteboxTools primeiro e depois apontar o caminho no QGIS.
        </div>

        <div class="step"><b>Download (oficial):</b></div>
        <ul>
          <li><a href="https://www.whiteboxgeo.com/download-whiteboxtools/">WhiteboxTools (Whitebox Geospatial)</a></li>
          <li><span class="small">Escolha Windows e baixe a versão correspondente (ex.: v2.3).</span></li>
        </ul>

        <div class="step"><b>Instalação (passo a passo):</b></div>
        <ul>
          <li>Baixe e extraia o WhiteboxTools para uma pasta fixa (ex.: <span class="mono">C:\\SIG\\WhiteboxTools\\</span>).</li>
          <li>No QGIS, habilite o provider/plugin de WhiteboxTools (se disponível).</li>
          <li>Em <b>Processamento → Opções → Provedores → WhiteboxTools</b>, configure o caminho do executável.</li>
          <li>Teste na Caixa de Ferramentas procurando <span class="mono">wbt:</span>.</li>
        </ul>

        <a name="whitebox_uso" id="whitebox_uso"></a>
        <h3>Como usar o motor WhiteboxTools <span class="top"><a href="#top">voltar ao topo</a></span></h3>

        <div class="ok">
          <b>Fluxo típico:</b> DEM → D8Pointer → acumulação → ExtractStreams → (ordem Strahler) → rede vetorial + bacias.
        </div>

        <ul>
          <li><b>1) Selecione o DEM</b> no plugin.</li>
          <li><b>2) Escolha o motor</b> como <b>WhiteboxTools</b>.</li>
          <li><b>3) Ajuste o threshold</b> do <span class="mono">ExtractStreams</span>.</li>
          <li><b>4) Execute</b> para gerar rede vetorial e bacias (e ordem, quando habilitada).</li>
        </ul>

        <hr>

        <a name="pocas" id="pocas"></a>
        <h3>Como usar: Poças (Simulação 2) <span class="top"><a href="#top">voltar ao topo</a></span></h3>

        <div class="ok">
          <b>Objetivo:</b> identificar e visualizar “poças” (depressões) e sua profundidade/volume a partir de um DEM.
        </div>

        <ul>
          <li><b>Pré-requisitos:</b>
            <ul>
              <li>Selecione um <b>DEM</b> válido no combo <span class="kbd">MDT/DEM</span>.</li>
              <li>Gere/tenha um raster de <b>Profundidade</b> (DepthInSink/Depth in sinks), quando o motor suportar.</li>
            </ul>
          </li>

          <li><b>Passo a passo:</b>
            <ul>
              <li>1) Clique em <span class="kbd">Calcular Poças</span> (se estiver disponível).</li>
              <li>2) Ajuste o <b>h_min</b> (profundidade mínima): filtra poças rasas e remove ruído.</li>
              <li>3) Clique em <span class="kbd">Gerar</span> para criar a visualização/resultado das poças.</li>
            </ul>
          </li>

          <li><b>Saídas esperadas:</b>
            <ul>
              <li>Raster de profundidade.</li>
              <li>Camada vetorial de poças (polígonos) com métricas (área/volume quando habilitado).</li>
            </ul>
          </li>

          <li class="small"><b>Dica:</b> se aparecerem muitas poças pequenas, aumente <b>h_min</b> e/ou use um DEM pré-processado.</li>
        </ul>

        <hr>

        <a name="inundacao" id="inundacao"></a>
        <h3>Como usar: Inundação (Simulação 1) <span class="top"><a href="#top">voltar ao topo</a></span></h3>

        <div class="ok">
          <b>Objetivo:</b> simular lâmina d’água sobre o terreno usando um raster base (inundação/flood) e parâmetros de estágio.
        </div>

        <ul>
          <li><b>Pré-requisitos:</b>
            <ul>
              <li>Ter um <b>raster base</b> compatível (ex.: inundação/flood gerado por algum motor ou camada de profundidade/resultado).</li>
              <li>Definir o intervalo de estágio (mínimo/máximo) e o passo.</li>
            </ul>
          </li>

          <li><b>Passo a passo:</b>
            <ul>
              <li>1) Selecione o DEM e o motor.</li>
              <li>2) Defina <b>Mínimo</b> e <b>Máximo</b> (ex.: nível/altura) e um <b>Passo</b>.</li>
              <li>3) Clique em <span class="kbd">Inundação</span> para gerar os resultados (frames/camadas conforme seu fluxo).</li>
            </ul>
          </li>

          <li><b>Saídas esperadas:</b>
            <ul>
              <li>Uma camada/raster resultante para cada estágio (dependendo de como você configurou o pipeline).</li>
              <li>Visualização incremental do avanço da inundação.</li>
            </ul>
          </li>

          <li class="small"><b>Dica:</b> se o processamento ficar pesado, aumente o passo (menos estágios) e refaça com mais detalhe só no fim.</li>
        </ul>

        <hr>

        <a name="inundacao_rt" id="inundacao_rt"></a>
        <h3>Como usar: Inundação em Tempo Real <span class="top"><a href="#top">voltar ao topo</a></span></h3>

        <div class="note">
          <b>Tempo real</b> significa que a camada é atualizada automaticamente com um timer, variando o estágio ao longo do intervalo.
        </div>

        <ul>
          <li><b>Pré-requisitos:</b>
            <ul>
              <li>Intervalo válido: <b>Mínimo &lt; Máximo</b>.</li>
              <li>Um raster base de inundação compatível (ou possibilidade de gerar no motor atual).</li>
            </ul>
          </li>

          <li><b>Passo a passo:</b>
            <ul>
              <li>1) Configure <b>Mínimo</b>, <b>Máximo</b> e <b>Passo</b>.</li>
              <li>2) Ajuste o <b>Tempo</b> (intervalo do timer) para controlar a velocidade da animação.</li>
              <li>3) Clique em <span class="kbd">Inundação (Tempo Real)</span> para iniciar.</li>
              <li>4) Clique novamente para <b>parar</b> (o botão funciona como Start/Stop).</li>
            </ul>
          </li>

          <li><b>Quando usar:</b>
            <ul>
              <li>Apresentações rápidas e análise visual do avanço da inundação.</li>
              <li>Testar sensibilidade de estágio sem gerar dezenas de arquivos/frames.</li>
            </ul>
          </li>

          <div class="warn">
            <b>Atenção:</b> Em áreas grandes ou com raster pesado, tempo real pode ficar lento.
            Se isso acontecer, aumente o <b>Tempo</b> do timer ou o <b>Passo</b>.
          </div>
        </ul>

        <hr>

        <a name="qgis" id="qgis"></a>
        <h3>Ativar/validar providers no QGIS <span class="top"><a href="#top">voltar ao topo</a></span></h3>
        <ul>
          <li>Vá em <b>Processamento → Opções → Provedores</b> e habilite os providers instalados.</li>
          <li>Se um provider não aparece, normalmente falta instalar o software (SAGA/TauDEM/Whitebox) ou o plugin/provider correspondente.</li>
        </ul>

        <hr>

        <a name="diag" id="diag"></a>
        <h3>Diagnóstico rápido <span class="top"><a href="#top">voltar ao topo</a></span></h3>
        <ul>
          <li>Abra <b>Processamento → Caixa de Ferramentas</b></li>
          <li>Pesquise: <span class="mono">saga:</span>, <span class="mono">taudem</span>, <span class="mono">wbt:</span></li>
          <li>Se não aparecer: volte em <b>Processamento → Opções → Provedores</b> e confira caminhos.</li>
        </ul>

        </body>
        </html>
        """
#////////////////////////////////////////////
    def _init_tableViewListaCanais(self):
        """
        Inicializa o tableViewListaCanais como um espelho navegável
        do tableViewCamada, para uso na aba PROJETO.
        """
        if not hasattr(self, "tableViewListaCanais"):
            return

        model = QStandardItemModel(self.tableViewListaCanais)
        model.setHorizontalHeaderLabels([self.tr("CANAIS")])
        self.tableViewListaCanais.setModel(model)
        self._lista_canais_model = model

        header = self.tableViewListaCanais.horizontalHeader()
        header.setDefaultAlignment(Qt.AlignmentFlag.AlignCenter)
        header.setSectionResizeMode(0, QHeaderView.ResizeMode.Stretch)

        self._reload_tableViewListaCanais_from_group()

        sel_model = self.tableViewListaCanais.selectionModel()
        if sel_model:
            sel_model.currentRowChanged.connect(self._on_lista_canais_row_changed)

    def _reload_tableViewListaCanais_from_group(self):
        """
        Recarrega o tableViewListaCanais com as mesmas camadas lineares
        do grupo CANAIS, sem criar fluxo paralelo de seleção.
        """
        if not hasattr(self, "tableViewListaCanais"):
            return
        if not hasattr(self, "_lista_canais_model") or self._lista_canais_model is None:
            return

        model = self._lista_canais_model
        model.removeRows(0, model.rowCount())

        group = self._get_canais_group()
        if group is None:
            return

        for node in group.children():
            if not isinstance(node, QgsLayerTreeLayer):
                continue

            lyr = node.layer()
            if lyr is None or not isinstance(lyr, QgsVectorLayer):
                continue

            try:
                if lyr.geometryType() != QgsWkbTypes.GeometryType.LineGeometry:
                    continue
            except Exception:
                try:
                    if QgsWkbTypes.geometryType(lyr.wkbType()) != QgsWkbTypes.GeometryType.LineGeometry:
                        continue
                except Exception:  # nosec B112
                    continue

            # # resumo da camada para exibir na aba PROJETO
            n_trechos = 0
            comp_total = 0.0
            try:
                for f in lyr.getFeatures():
                    g = f.geometry()
                    if g is not None and not g.isEmpty():
                        n_trechos += 1
                        comp_total += float(g.length())
            except Exception:
                n_trechos = 0
                comp_total = 0.0

            try:
                for f in lyr.getFeatures():
                    g = f.geometry()
                    if g is not None and not g.isEmpty():
                        comp_total += float(g.length())
            except Exception:
                comp_total = 0.0

            trecho_txt = self.tr("trecho") if n_trechos == 1 else self.tr("trechos")
            txt = self.tr("    {layer_name}  ({count} {segment_text} • {length:.2f} m)").format(layer_name=lyr.name(), count=n_trechos, segment_text=trecho_txt, length=comp_total)

            item = QStandardItem(txt)
            item.setEditable(False)
            item.setData(lyr.id(), Qt.ItemDataRole.UserRole)

            # tooltip mais detalhado
            item.setToolTip(self.tr("Camada: {layer_name}\nTrechos: {count}\nComprimento total: {length:.2f} m").format(layer_name=lyr.name(), count=n_trechos, length=comp_total))

            model.appendRow(item)

        # Mantém a lista do projeto espelhando a camada atual
        try:
            lyr = getattr(self, "_current_canal_layer", None)
            if isinstance(lyr, QgsVectorLayer):
                self._sync_tableViewListaCanais_with_layer_id(lyr.id())
            elif model.rowCount() > 0:
                idx = model.index(0, 0)
                self.tableViewListaCanais.setCurrentIndex(idx)
        except Exception:
            pass  # nosec B110

    def _sync_tableViewListaCanais_with_layer_id(self, layer_id: str):
        """
        Espelha no tableViewListaCanais a camada atualmente selecionada
        no tableViewCamada/QGIS, sem disparar loop.
        """
        if not hasattr(self, "tableViewListaCanais"):
            return
        if not hasattr(self, "_lista_canais_model") or self._lista_canais_model is None:
            return
        if not layer_id:
            return

        model = self._lista_canais_model

        self._syncing_lista_canais_selection = True
        try:
            for row in range(model.rowCount()):
                idx = model.index(row, 0)
                lid = idx.data(Qt.ItemDataRole.UserRole)
                if lid == layer_id:
                    self.tableViewListaCanais.setCurrentIndex(idx)
                    self.tableViewListaCanais.selectRow(row)
                    self.tableViewListaCanais.scrollTo(idx)
                    break
        finally:
            self._syncing_lista_canais_selection = False

    def _on_lista_canais_row_changed(self, current: QModelIndex, previous: QModelIndex):
        """
        Quando o usuário troca a linha no tableViewListaCanais,
        apenas delega a seleção real para o tableViewCamada.
        """
        if self._syncing_lista_canais_selection:
            return

        if not current.isValid():
            return

        layer_id = current.data(Qt.ItemDataRole.UserRole)
        if not layer_id:
            return

        # tableViewCamada continua sendo a fonte oficial da seleção
        if hasattr(self, "_select_camada_row_by_layer_id"):
            self._select_camada_row_by_layer_id(layer_id)

    def _update_grafico_projeto_from_current_layer(self):
        layer = getattr(self, "_current_canal_layer", None)
        self._update_grafico_projeto(layer)

    def _project_graph_sort_key(self, feat, idx_cn: int):
        try:
            if idx_cn >= 0:
                cn = feat.attribute(idx_cn)
                s = "" if cn is None else str(cn)
                nums = re.findall(r"\d+", s)
                if nums:
                    return tuple(int(n) for n in nums)
        except Exception:
            pass  # nosec B110

        try:
            return (int(feat.id()),)
        except Exception:
            return (999999999,)

    def _sample_profile_from_geom(self, geom: QgsGeometry, rprov, *, target_samples: int = 120):
        if geom is None or geom.isEmpty() or geom.type() != QgsWkbTypes.GeometryType.LineGeometry:
            return [], []

        if geom.isMultipart():
            linhas = geom.asMultiPolyline()
            if not linhas:
                return [], []
            geom = QgsGeometry.fromPolylineXY(linhas[0])

        total_len = geom.length() or 0.0
        if total_len <= 0.0:
            return [], []

        passo = max(total_len / target_samples, 1.0)
        geom_dens = geom.densifyByDistance(passo)

        if geom_dens.isMultipart():
            linhas = geom_dens.asMultiPolyline()
            pts = linhas[0] if linhas else []
        else:
            pts = geom_dens.asPolyline()

        if len(pts) < 2:
            return [], []

        xs = []
        zs = []

        dist_acum = 0.0
        prev_pt = None

        def _extract_z(res):
            if isinstance(res, tuple):
                val, ok = res
                return float(val) if ok and val is not None else None
            return float(res) if res is not None else None

        for pt in pts:
            if prev_pt is not None:
                dx = pt.x() - prev_pt.x()
                dy = pt.y() - prev_pt.y()
                dist_acum += math.hypot(dx, dy)

            res = rprov.sample(QgsPointXY(pt.x(), pt.y()), 1)
            z = _extract_z(res)
            if z is not None:
                xs.append(dist_acum)
                zs.append(z)

            prev_pt = pt

        return xs, zs

    def _refresh_projeto_views(self, layer: QgsVectorLayer | None = None):
        """
        Recarrega a lista da aba PROJETO e o gráfico global.
        """
        try:
            if hasattr(self, "_reload_tableViewListaCanais_from_group"):
                self._reload_tableViewListaCanais_from_group()
        except Exception:
            pass  # nosec B110

        try:
            if layer is None:
                layer = getattr(self, "_current_canal_layer", None)
            self._update_grafico_projeto(layer)
        except Exception:
            pass  # nosec B110
#////////////////////////////////////////////
    def _init_checkBoxHachura(self):
        """
        Conecta o checkBoxHachura para controlar a hachura
        do gráfico global da aba PROJETO.
        """
        if hasattr(self, "checkBoxHachura") and self.checkBoxHachura is not None:
            try:
                self.checkBoxHachura.toggled.disconnect(self._on_checkBoxHachura_toggled)
            except Exception:
                pass  # nosec B110
            self.checkBoxHachura.toggled.connect(self._on_checkBoxHachura_toggled)

    def _on_checkBoxHachura_toggled(self, checked: bool):
        self._update_grafico_projeto_fill_between()

    def _clear_grafico_projeto_fill_between(self):
        """
        Remove todos os itens de preenchimento (FillBetween + curvas auxiliares)
        do gráfico global da aba PROJETO.
        """
        plot = getattr(self, "_grafico_projeto_plot_widget", None)
        items = getattr(self, "_grafico_projeto_fill_items", None)

        if plot is None or items is None:
            return

        for it in items:
            try:
                plot.removeItem(it)
            except Exception:
                pass  # nosec B110

        self._grafico_projeto_fill_items = []

    def _update_grafico_projeto_fill_between(self):
        """
        Cria preenchimentos entre as curvas Canal x Terreno
        no gráfico global da aba PROJETO, por trechos:

        - Terreno acima do Canal  -> azul
        - Terreno abaixo do Canal -> vermelho

        Respeita o checkBoxHachura.
        """
        plot = getattr(self, "_grafico_projeto_plot_widget", None)
        canal_curve = getattr(self, "_grafico_projeto_canal_curve", None)
        terreno_curve = getattr(self, "_grafico_projeto_terreno_curve", None)

        if plot is None or canal_curve is None or terreno_curve is None:
            return

        # limpa preenchimentos antigos
        self._clear_grafico_projeto_fill_between()

        # respeita checkbox
        if not (
            hasattr(self, "checkBoxHachura")
            and self.checkBoxHachura is not None
            and self.checkBoxHachura.isChecked()):
            return

        xs_t, ys_t = terreno_curve.getData()
        xs_c, ys_c = canal_curve.getData()

        if xs_t is None or ys_t is None or xs_c is None or ys_c is None:
            return

        xs_t = list(xs_t)
        ys_t = list(ys_t)
        xs_c = list(xs_c)
        ys_c = list(ys_c)

        n = min(len(xs_t), len(xs_c), len(ys_t), len(ys_c))
        if n < 2:
            return

        xs_t = xs_t[:n]
        ys_t = ys_t[:n]
        ys_c = ys_c[:n]

        def sign(v, eps=1e-9):
            if v > eps:
                return 1
            if v < -eps:
                return -1
            return 0

        # 1) insere interseções
        xs2 = [xs_t[0]]
        ys_t2 = [ys_t[0]]
        ys_c2 = [ys_c[0]]

        for i in range(n - 1):
            x0 = xs_t[i]
            x1 = xs_t[i + 1]
            yt0 = ys_t[i]
            yt1 = ys_t[i + 1]
            yc0 = ys_c[i]
            yc1 = ys_c[i + 1]

            # ignora quebras entre trechos
            try:
                if (
                    math.isnan(float(x0)) or math.isnan(float(x1)) or
                    math.isnan(float(yt0)) or math.isnan(float(yt1)) or
                    math.isnan(float(yc0)) or math.isnan(float(yc1))):
                    xs2.append(x1)
                    ys_t2.append(yt1)
                    ys_c2.append(yc1)
                    continue
            except Exception:
                xs2.append(x1)
                ys_t2.append(yt1)
                ys_c2.append(yc1)
                continue

            d0 = yt0 - yc0
            d1 = yt1 - yc1

            if d0 * d1 < 0.0:
                t = d0 / (d0 - d1)
                x_int = x0 + t * (x1 - x0)
                yt_int = yt0 + t * (yt1 - yt0)
                yc_int = yc0 + t * (yc1 - yc0)
                y_int = (yt_int + yc_int) * 0.5

                xs2.append(x_int)
                ys_t2.append(y_int)
                ys_c2.append(y_int)

            xs2.append(x1)
            ys_t2.append(yt1)
            ys_c2.append(yc1)

        m = len(xs2)
        if m < 2:
            return

        # 2) segmenta trechos contínuos com mesmo sinal
        i = 0
        while i < m - 1:
            try:
                if (
                    math.isnan(float(xs2[i])) or math.isnan(float(xs2[i + 1])) or
                    math.isnan(float(ys_t2[i])) or math.isnan(float(ys_t2[i + 1])) or
                    math.isnan(float(ys_c2[i])) or math.isnan(float(ys_c2[i + 1]))):
                    i += 1
                    continue
            except Exception:
                i += 1
                continue

            d = ys_t2[i] - ys_c2[i]
            s = sign(d)

            if s == 0:
                i += 1
                continue

            start = i
            end = i

            j = i + 1
            while j < m:
                try:
                    if (math.isnan(float(xs2[j])) or
                        math.isnan(float(ys_t2[j])) or
                        math.isnan(float(ys_c2[j]))):
                        break
                except Exception:
                    break

                sj = sign(ys_t2[j] - ys_c2[j])
                if sj != 0 and sj != s:
                    break

                end = j
                j += 1

            if start > 0 and sign(ys_t2[start - 1] - ys_c2[start - 1]) == 0:
                start -= 1
            if end < m - 1 and sign(ys_t2[end + 1] - ys_c2[end + 1]) == 0:
                end += 1

            seg_x = xs2[start:end + 1]
            seg_terr = ys_t2[start:end + 1]
            seg_canal = ys_c2[start:end + 1]

            if len(seg_x) >= 2:
                if s > 0:
                    upper_y = seg_terr
                    lower_y = seg_canal
                    brush = pg.mkBrush(0, 120, 255, 90)
                else:
                    upper_y = seg_canal
                    lower_y = seg_terr
                    brush = pg.mkBrush(255, 60, 60, 90)

                upper_item = pg.PlotCurveItem(seg_x, upper_y, pen=None)
                lower_item = pg.PlotCurveItem(seg_x, lower_y, pen=None)

                plot.addItem(upper_item)
                plot.addItem(lower_item)

                fill = pg.FillBetweenItem(curve1=upper_item, curve2=lower_item, brush=brush)
                plot.addItem(fill)

                self._grafico_projeto_fill_items.extend([upper_item, lower_item, fill])

            i = max(j, i + 1)
#////////////////////////////////////////////
    def _init_checkBoxAltimetria(self):
        """
        Conecta o checkBoxAltimetria para habilitar/desabilitar
        o cursor de leitura do gráfico da aba PROJETO.
        """
        if hasattr(self, "checkBoxAltimetria") and self.checkBoxAltimetria is not None:
            try:
                self.checkBoxAltimetria.toggled.disconnect(self._on_checkBoxAltimetria_toggled)
            except Exception:
                pass  # nosec B110
            self.checkBoxAltimetria.toggled.connect(self._on_checkBoxAltimetria_toggled)

    def _on_checkBoxAltimetria_toggled(self, checked: bool):
        if not checked:
            self._hide_grafico_projeto_crosshair()

    def _init_scrollAreaProjetoGrafico(self):
        """
        Cria o gráfico global exclusivamente dentro do scrollAreaProjeto.
        Não usa textBrowserInfo e não toca na aba REDES.
        """
        sa = getattr(self, "scrollAreaProjeto", None)
        if sa is None:
            return

        container = sa.widget()
        if container is None:
            container = QWidget(sa)
            sa.setWidget(container)

        layout = container.layout()
        if layout is None:
            layout = QVBoxLayout(container)
            layout.setContentsMargins(0, 0, 0, 0)
            layout.setSpacing(0)
            container.setLayout(layout)

        # remove o gráfico anterior, se existir
        if self._grafico_projeto_plot_widget is not None:
            try:
                layout.removeWidget(self._grafico_projeto_plot_widget)
                self._grafico_projeto_plot_widget.deleteLater()
            except Exception:
                pass  # nosec B110

        pg.setConfigOptions(antialias=True)

        self._grafico_projeto_plot_widget = pg.PlotWidget(parent=container, background=(15, 15, 15))
        layout.addWidget(self._grafico_projeto_plot_widget)

        plot_item = self._grafico_projeto_plot_widget.getPlotItem()
        plot_item.showGrid(x=True, y=True, alpha=0.20)
        plot_item.setLabel("bottom", self.tr("Comprimento acumulado (m)"))
        plot_item.setLabel("left", self.tr("Cota (m)"))
        plot_item.setTitle(self.tr("Perfil do Projeto"))

        vb = plot_item.getViewBox()
        vb.setDefaultPadding(0.08)

        axis_font = QFont()
        axis_font.setPointSize(9)
        axis_pen = pg.mkPen(220, 220, 220)

        for name in ("bottom", "left"):
            axis = plot_item.getAxis(name)
            axis.setTickFont(axis_font)
            axis.setTextPen(axis_pen)
            axis.setPen(axis_pen)

        self._grafico_projeto_legend = plot_item.addLegend(offset=(10, 10))
        try:
            self._grafico_projeto_legend.layout.setContentsMargins(4, 4, 4, 4)
        except Exception:
            pass  # nosec B110

        canal_pen = pg.mkPen(QColor(0, 170, 255), width=2)
        terreno_pen = pg.mkPen(QColor(255, 0, 255), width=1)

        self._grafico_projeto_canal_curve = plot_item.plot([], [], pen=canal_pen, name=self.tr("Canal"))
        self._grafico_projeto_terreno_curve = plot_item.plot([], [], pen=terreno_pen, name=self.tr("Terreno"))

        # Crosshair / texto / ponto sincronizado
        self._grafico_projeto_vline = pg.InfiniteLine(angle=90, movable=False, pen=pg.mkPen(200, 200, 200, 140))
        self._grafico_projeto_hline = pg.InfiniteLine(angle=0, movable=False, pen=pg.mkPen(200, 200, 200, 140))
        plot_item.addItem(self._grafico_projeto_vline, ignoreBounds=True)
        plot_item.addItem(self._grafico_projeto_hline, ignoreBounds=True)
        self._grafico_projeto_vline.hide()
        self._grafico_projeto_hline.hide()

        self._grafico_projeto_coord_text = pg.TextItem("", anchor=(0, 1))
        plot_item.addItem(self._grafico_projeto_coord_text)
        self._grafico_projeto_coord_text.hide()

        self._grafico_projeto_sync_point = plot_item.plot(
            [], [], pen=None,
            symbol="o", symbolSize=6,
            symbolBrush=pg.mkBrush(255, 255, 0),
            symbolPen=None)

        # destaque do trecho selecionado
        self._grafico_projeto_trecho_item = plot_item.plot([], [], pen=pg.mkPen(255, 255, 0, width=4))
        self._grafico_projeto_trecho_item.hide()

        self._grafico_projeto_trecho_text = pg.TextItem("", anchor=(0.5, 1))
        plot_item.addItem(self._grafico_projeto_trecho_text)
        self._grafico_projeto_trecho_text.hide()

        if hasattr(self, "_grafico_projeto_mouse_proxy") and self._grafico_projeto_mouse_proxy is not None:
            self._grafico_projeto_mouse_proxy = None

        self._grafico_projeto_mouse_proxy = pg.SignalProxy(
            self._grafico_projeto_plot_widget.scene().sigMouseMoved,
            rateLimit=60,
            slot=self._on_grafico_projeto_mouse_moved)

    def _hide_grafico_projeto_crosshair(self):
        """
        Esconde crosshair, texto e ponto do gráfico da aba PROJETO.
        """
        if hasattr(self, "_grafico_projeto_vline") and self._grafico_projeto_vline is not None:
            self._grafico_projeto_vline.hide()
        if hasattr(self, "_grafico_projeto_hline") and self._grafico_projeto_hline is not None:
            self._grafico_projeto_hline.hide()
        if hasattr(self, "_grafico_projeto_coord_text") and self._grafico_projeto_coord_text is not None:
            self._grafico_projeto_coord_text.hide()
        if hasattr(self, "_grafico_projeto_sync_point") and self._grafico_projeto_sync_point is not None:
            self._grafico_projeto_sync_point.setData([], [])

    def _split_project_graph_segments(self, xs, ys_c, ys_t):
        """
        Divide as séries do gráfico do Projeto em segmentos contínuos,
        quebrando em np.nan para respeitar os trechos.
        """
        segments = []
        cur_x = []
        cur_c = []
        cur_t = []

        n = min(len(xs), len(ys_c), len(ys_t))
        for i in range(n):
            xv = xs[i]
            yc = ys_c[i]
            yt = ys_t[i]

            try:
                invalid = (
                    xv is None or yc is None or yt is None or
                    math.isnan(float(xv)) or
                    math.isnan(float(yc)) or
                    math.isnan(float(yt)))
            except Exception:
                invalid = True

            if invalid:
                if len(cur_x) >= 2:
                    segments.append((cur_x, cur_c, cur_t))
                cur_x, cur_c, cur_t = [], [], []
                continue

            cur_x.append(float(xv))
            cur_c.append(float(yc))
            cur_t.append(float(yt))

        if len(cur_x) >= 2:
            segments.append((cur_x, cur_c, cur_t))

        return segments
#////////////////////////////////////////////
    def _init_checkBoxTrecho(self):
        """
        Conecta o checkBoxTrecho para destacar o trecho do gráfico do Projeto
        sob o mouse e mostrar sua inclinação.
        """
        if hasattr(self, "checkBoxTrecho") and self.checkBoxTrecho is not None:
            try:
                self.checkBoxTrecho.toggled.disconnect(self._on_checkBoxTrecho_toggled)
            except Exception:
                pass  # nosec B110
            self.checkBoxTrecho.toggled.connect(self._on_checkBoxTrecho_toggled)

    def _hide_grafico_projeto_trecho(self):
        """
        Esconde o destaque amarelo e o texto de inclinação do trecho.
        """
        if hasattr(self, "_grafico_projeto_trecho_item") and self._grafico_projeto_trecho_item is not None:
            try:
                self._grafico_projeto_trecho_item.setData([], [])
                self._grafico_projeto_trecho_item.hide()
            except Exception:
                pass  # nosec B110

        if hasattr(self, "_grafico_projeto_trecho_text") and self._grafico_projeto_trecho_text is not None:
            try:
                self._grafico_projeto_trecho_text.hide()
            except Exception:
                pass  # nosec B110

    def _interp_project_segment(self, seg: dict, x: float):
        """
        Interpola Canal e Terreno dentro de um trecho específico do gráfico do Projeto.
        """
        xs = list(seg.get("xs") or [])
        ys_c = list(seg.get("ys_canal") or [])
        ys_t = list(seg.get("ys_terr") or [])

        n = min(len(xs), len(ys_c), len(ys_t))
        if n < 2:
            return None, None

        xs = xs[:n]
        ys_c = ys_c[:n]
        ys_t = ys_t[:n]

        if x < xs[0] or x > xs[-1]:
            return None, None

        i = bisect.bisect_left(xs, x)

        if i <= 0:
            x0, x1 = xs[0], xs[1]
            yc0, yc1 = ys_c[0], ys_c[1]
            yt0, yt1 = ys_t[0], ys_t[1]
        elif i >= len(xs):
            x0, x1 = xs[-2], xs[-1]
            yc0, yc1 = ys_c[-2], ys_c[-1]
            yt0, yt1 = ys_t[-2], ys_t[-1]
        else:
            x0, x1 = xs[i - 1], xs[i]
            yc0, yc1 = ys_c[i - 1], ys_c[i]
            yt0, yt1 = ys_t[i - 1], ys_t[i]

        if x1 == x0:
            t = 0.0
        else:
            t = (x - x0) / (x1 - x0)

        y_canal = float(yc0 + t * (yc1 - yc0))
        y_terreno = float(yt0 + t * (yt1 - yt0))
        return y_canal, y_terreno

    def _pick_grafico_projeto_segment(self, x: float, y_mouse: float):
        """
        Escolhe o trecho do gráfico do Projeto que está sob o mouse.
        Resolve também a ambiguidade nas junções entre trechos.
        """
        segments = getattr(self, "_grafico_projeto_segments", None) or []
        if not segments:
            return None, None, None, None

        candidates = []

        for seg in segments:
            try:
                x0 = float(seg.get("x_start"))
                x1 = float(seg.get("x_end"))
            except Exception:  # nosec B112
                continue

            if x < x0 or x > x1:
                continue

            y_canal, y_terreno = self._interp_project_segment(seg, x)
            if y_canal is None or y_terreno is None:
                continue

            if abs(y_mouse - y_canal) <= abs(y_mouse - y_terreno):
                y_anchor = y_canal
            else:
                y_anchor = y_terreno

            candidates.append((abs(y_mouse - y_anchor), seg, y_canal, y_terreno, y_anchor))

        if not candidates:
            return None, None, None, None

        _, seg, y_canal, y_terreno, y_anchor = min(candidates, key=lambda it: it[0])
        return seg, y_canal, y_terreno, y_anchor

    def _segment_declividade_percent(self, seg: dict) -> float:
        """
        Retorna a inclinação (%) do trecho.
        Prioriza o campo Declividade(I) da feição; se não houver, calcula pela reta do canal.
        """
        try:
            val = seg.get("decl_perc")
            if val is not None:
                return float(val)
        except Exception:
            pass  # nosec B110

        xs = list(seg.get("xs") or [])
        ys = list(seg.get("ys_canal") or [])
        if len(xs) < 2 or len(ys) < 2:
            return 0.0

        dx = float(xs[-1]) - float(xs[0])
        if abs(dx) < 1e-12:
            return 0.0

        return ((float(ys[0]) - float(ys[-1])) / dx) * 100.0

    def _update_grafico_projeto_trecho_highlight(self, seg: dict | None):
        """
        Destaca em amarelo o trecho selecionado e mostra a inclinação.
        """
        if seg is None:
            self._hide_grafico_projeto_trecho()
            return

        item = getattr(self, "_grafico_projeto_trecho_item", None)
        txt = getattr(self, "_grafico_projeto_trecho_text", None)

        if item is None or txt is None:
            return

        xs = list(seg.get("xs") or [])
        ys_canal = list(seg.get("ys_canal") or [])
        ys_terr = list(seg.get("ys_terr") or [])

        n = min(len(xs), len(ys_canal))
        if n < 2:
            self._hide_grafico_projeto_trecho()
            return

        xs = xs[:n]
        ys_canal = ys_canal[:n]

        item.setData(xs, ys_canal)
        item.show()

        decl = self._segment_declividade_percent(seg)

        cn = seg.get("cn")
        fid = seg.get("fid")

        if cn not in (None, ""):
            trecho_label = f"{cn}"
        else:
            trecho_label = f"FID {fid}"

        x_mid = 0.5 * (xs[0] + xs[-1])

        try:
            y_top = max(max(ys_canal), max(ys_terr)) if ys_terr else max(ys_canal)
        except Exception:
            y_top = max(ys_canal)

        html = (
            "<div style='color:#FFFF66;'>"
            + self.tr("<b>Trecho:</b> {trecho_label}<br>").format(trecho_label=trecho_label)
            + self.tr("<b>Inclinação:</b> {decl:.3f}%").format(decl=decl)
            + "</div>")
        txt.setHtml(html)
        txt.setPos(x_mid, y_top)
        txt.show()

        # sincroniza seleção do trecho no QGIS
        try:
            self._set_grafico_projeto_hover_selection(seg.get("fid"))
        except Exception:
            pass  # nosec B110

    def _update_grafico_projeto(self, layer: QgsVectorLayer | None = None):
        """
        Monta o gráfico global da aba PROJETO, preservando também os metadados
        de cada trecho para interação por mouse.
        """
        plot = self._grafico_projeto_plot_widget
        canal_curve = self._grafico_projeto_canal_curve
        terreno_curve = self._grafico_projeto_terreno_curve

        if plot is None or canal_curve is None or terreno_curve is None:
            return

        if not isinstance(layer, QgsVectorLayer):
            self._clear_grafico_projeto()
            return

        raster = self._get_selected_raster_from_combo()
        if raster is None or not raster.isValid():
            self._clear_grafico_projeto()
            return

        rprov = raster.dataProvider()

        idx_cn = layer.fields().indexOf("CN")
        idx_yn = layer.fields().indexOf("Yn")
        idx_decl = layer.fields().indexOf("Declividade(I)")

        feats = list(layer.getFeatures())
        if not feats:
            self._clear_grafico_projeto()
            return

        feats.sort(key=lambda f: self._project_graph_sort_key(f, idx_cn))

        xs_terr_all = []
        zs_terr_all = []
        xs_can_all = []
        zs_can_all = []

        self._grafico_projeto_segments = []

        x_offset = 0.0
        n_validos = 0

        for feat in feats:
            geom = feat.geometry()
            xs_local, zs_terr = self._sample_profile_from_geom(geom, rprov, target_samples=100)

            if len(xs_local) < 2 or len(zs_terr) < 2:
                continue

            try:
                depth = float(feat.attribute(idx_yn)) if idx_yn >= 0 and feat.attribute(idx_yn) is not None else 0.0
            except Exception:
                depth = 0.0

            try:
                decl_perc = float(feat.attribute(idx_decl)) if idx_decl >= 0 and feat.attribute(idx_decl) is not None else 0.0
            except Exception:
                decl_perc = 0.0

            try:
                cn_val = feat.attribute(idx_cn) if idx_cn >= 0 else None
            except Exception:
                cn_val = None

            S = decl_perc / 100.0
            z0_canal = zs_terr[0] - depth if depth > 0.0 else zs_terr[0]
            zs_canal = [z0_canal - S * x for x in xs_local]
            xs_global = [x_offset + x for x in xs_local]

            if xs_terr_all:
                xs_terr_all.append(np.nan)
                zs_terr_all.append(np.nan)
                xs_can_all.append(np.nan)
                zs_can_all.append(np.nan)

            xs_terr_all.extend(xs_global)
            zs_terr_all.extend(zs_terr)
            xs_can_all.extend(xs_global)
            zs_can_all.extend(zs_canal)

            self._grafico_projeto_segments.append({
                "fid": feat.id(),
                "cn": cn_val,
                "x_start": xs_global[0],
                "x_end": xs_global[-1],
                "xs": list(xs_global),
                "ys_canal": list(zs_canal),
                "ys_terr": list(zs_terr),
                "decl_perc": decl_perc})

            x_offset = xs_global[-1]
            n_validos += 1

        if n_validos == 0:
            self._clear_grafico_projeto()
            try:
                plot.getPlotItem().setTitle(self.tr("Perfil do Projeto - {layer_name} (sem trechos válidos)").format(layer_name=layer.name()))
            except Exception:
                pass  # nosec B110
            return

        terreno_curve.setData(xs_terr_all, zs_terr_all)
        canal_curve.setData(xs_can_all, zs_can_all)

        try:
            self._hide_grafico_projeto_crosshair()
        except Exception:
            pass  # nosec B110

        try:
            self._hide_grafico_projeto_trecho()
        except Exception:
            pass  # nosec B110

        try:
            self._update_grafico_projeto_fill_between()
        except Exception:
            pass  # nosec B110

        try:
            plot.getPlotItem().setTitle(self.tr("Perfil do Projeto - {layer_name} ({count} trecho(s))").format(layer_name=layer.name(), count=n_validos))
            plot.getPlotItem().getViewBox().autoRange()
        except Exception:
            pass  # nosec B110

    def _set_grafico_projeto_hover_selection(self, fid: int | None):
        """
        Seleciona temporariamente, no QGIS, a feição correspondente ao trecho
        sob o mouse no gráfico da aba PROJETO.
        """
        layer = getattr(self, "_current_canal_layer", None)
        if not isinstance(layer, QgsVectorLayer):
            return

        if fid is None:
            self._clear_grafico_projeto_hover_selection()
            return

        # evita re-selecionar a mesma feição o tempo todo
        if (
            getattr(self, "_grafico_projeto_hover_selected_fid", None) == fid
            and getattr(self, "_grafico_projeto_hover_selected_layer_id", None) == layer.id()):
            return

        try:
            layer.selectByIds([int(fid)])
            self._grafico_projeto_hover_selected_fid = int(fid)
            self._grafico_projeto_hover_selected_layer_id = layer.id()
        except Exception:
            pass  # nosec B110

    def _clear_grafico_projeto_hover_selection(self, force: bool = False):
        """
        Limpa a seleção temporária criada pelo hover no gráfico da aba PROJETO.
        Usa rastreamento próprio para não deixar resquícios.
        """
        layer = getattr(self, "_current_canal_layer", None)

        sel_fid = getattr(self, "_grafico_projeto_hover_selected_fid", None)
        sel_layer_id = getattr(self, "_grafico_projeto_hover_selected_layer_id", None)

        if sel_fid is None and not force:
            return

        try:
            if isinstance(layer, QgsVectorLayer) and (force or layer.id() == sel_layer_id):
                layer.removeSelection()
        except Exception:
            pass  # nosec B110

        self._grafico_projeto_hover_selected_fid = None
        self._grafico_projeto_hover_selected_layer_id = None

    def _on_checkBoxTrecho_toggled(self, checked: bool):
        if not checked:
            self._hide_grafico_projeto_trecho()
            self._clear_grafico_projeto_hover_selection()

    def _on_grafico_projeto_mouse_moved(self, evt):
        """
        Mouse move no gráfico da aba PROJETO:
        - checkBoxAltimetria: mostra crosshair + distância + cotas
        - checkBoxTrecho: destaca o trecho em amarelo, mostra a inclinação
          e seleciona a mesma feição no QGIS
        """
        alt_enabled = (
            hasattr(self, "checkBoxAltimetria")
            and self.checkBoxAltimetria is not None
            and self.checkBoxAltimetria.isChecked())

        trecho_enabled = (
            hasattr(self, "checkBoxTrecho")
            and self.checkBoxTrecho is not None
            and self.checkBoxTrecho.isChecked())

        if not alt_enabled and not trecho_enabled:
            self._hide_grafico_projeto_crosshair()
            self._hide_grafico_projeto_trecho()
            return

        if not hasattr(self, "_grafico_projeto_plot_widget") or self._grafico_projeto_plot_widget is None:
            self._hide_grafico_projeto_trecho()
            return

        plot_item = self._grafico_projeto_plot_widget.getPlotItem()

        if isinstance(evt, (list, tuple)):
            pos = evt[0]
        else:
            pos = evt

        if not isinstance(pos, QPointF):
            self._hide_grafico_projeto_trecho()
            return

        # mouse saiu da área do gráfico -> limpa tudo
        if not plot_item.sceneBoundingRect().contains(pos):
            self._hide_grafico_projeto_crosshair()
            self._hide_grafico_projeto_trecho()
            return

        mouse_point = plot_item.vb.mapSceneToView(pos)
        x = mouse_point.x()
        y_mouse = mouse_point.y()

        seg, y_canal, y_terreno, y_val = self._pick_grafico_projeto_segment(x, y_mouse)

        # mouse está no gráfico, mas fora de um trecho válido -> limpa seleção temporária
        if seg is None or y_canal is None or y_terreno is None or y_val is None:
            self._hide_grafico_projeto_crosshair()
            self._hide_grafico_projeto_trecho()
            return

        if trecho_enabled:
            self._update_grafico_projeto_trecho_highlight(seg)
        else:
            self._hide_grafico_projeto_trecho()

        if not alt_enabled:
            self._hide_grafico_projeto_crosshair()
            return

        x_val = x

        if hasattr(self, "_grafico_projeto_vline") and self._grafico_projeto_vline is not None:
            self._grafico_projeto_vline.setPos(x_val)
            self._grafico_projeto_vline.show()

        if hasattr(self, "_grafico_projeto_hline") and self._grafico_projeto_hline is not None:
            self._grafico_projeto_hline.setPos(y_val)
            self._grafico_projeto_hline.show()

        if hasattr(self, "_grafico_projeto_coord_text") and self._grafico_projeto_coord_text is not None:
            html = (
                "<div style='color:white;'>"
                + self.tr("<b>Distância:</b> {x_val:.2f} m<br>").format(x_val=x_val)
                + self.tr("<span style='color:#00AAFF;'><b>Canal:</b> {y_canal:.2f} m</span><br>").format(y_canal=y_canal)
                + self.tr("<span style='color:#FF64FF;'><b>Terreno:</b> {y_terreno:.2f} m</span>").format(y_terreno=y_terreno)
                + "</div>")
            self._grafico_projeto_coord_text.setHtml(html)
            self._grafico_projeto_coord_text.setPos(x_val, y_val)
            self._grafico_projeto_coord_text.show()

        if hasattr(self, "_grafico_projeto_sync_point") and self._grafico_projeto_sync_point is not None:
            self._grafico_projeto_sync_point.setData([x_val], [y_val])

    def _clear_grafico_projeto(self):
        if self._grafico_projeto_canal_curve is not None:
            self._grafico_projeto_canal_curve.setData([], [])
        if self._grafico_projeto_terreno_curve is not None:
            self._grafico_projeto_terreno_curve.setData([], [])

        self._grafico_projeto_segments = []

        try:
            self._hide_grafico_projeto_crosshair()
        except Exception:
            pass  # nosec B110

        try:
            self._hide_grafico_projeto_trecho()
        except Exception:
            pass  # nosec B110

        try:
            self._clear_grafico_projeto_hover_selection(force=True)
        except Exception:
            pass  # nosec B110

        if hasattr(self, "_clear_grafico_projeto_fill_between"):
            try:
                self._clear_grafico_projeto_fill_between()
            except Exception:
                pass  # nosec B110

    def _reset_grafico_projeto(self):
        """
        Reseta completamente o gráfico da aba PROJETO.
        """
        self._clear_grafico_projeto()

        try:
            self._clear_grafico_projeto_hover_selection(force=True)
        except Exception:
            pass  # nosec B110

        plot = getattr(self, "_grafico_projeto_plot_widget", None)
        if plot is None:
            return

        try:
            plot.getPlotItem().setTitle(self.tr("Perfil do Projeto"))
        except Exception:
            pass  # nosec B110

        try:
            vb = plot.getPlotItem().getViewBox()
            vb.enableAutoRange(axis=pg.ViewBox.XAxis, enable=True)
            vb.enableAutoRange(axis=pg.ViewBox.YAxis, enable=True)
            vb.autoRange()
        except Exception:
            pass  # nosec B110

class SagaInundacaoRunner:
    """
    Pipeline (assíncrono):
      1) gdal:rasterize canais (vector) -> channels_grid.tif (NoData fora, 1 nos canais)
      2) sagang:verticaldistancetochannelnetwork -> HAND.tif
      3) _RasterCalcTask -> depth.tif (max(stage - hand, 0))
    """
    def __init__(self, plugin, dem_layer: QgsRasterLayer, filled_layer: QgsRasterLayer, canais_layer: QgsVectorLayer, stage: float, workspace: str):
        self.plugin = plugin
        self.dem_layer = dem_layer
        self.filled_layer = filled_layer
        self.canais_layer = canais_layer
        self.stage = float(stage)
        self.workspace = workspace

        base_ascii = plugin._make_ascii_filename(dem_layer.source())
        root, _ext = os.path.splitext(base_ascii)

        self.channels_grid_path = os.path.join(self.workspace, f"saga_channels_{root}.tif")
        self.hand_path = os.path.join(self.workspace, f"saga_hand_{root}.tif")
        self.depth_path = os.path.join(self.workspace, f"saga_inund_{root}_stage_{self.stage:.3f}.tif")

        self.context = QgsProcessingContext()
        self.context.setProject(QgsProject.instance())

        self.feedback_rasterize = QgsProcessingFeedback()
        self.feedback_hand = QgsProcessingFeedback()

        self.task_rasterize = None
        self.task_hand = None
        self.task_depth = None

    def start(self):
        self.plugin.mostrar_mensagem(self.plugin.tr("Inundação (SAGA): iniciando (etapa 1/3: rasterizar canais)..."), "Info")
        self._start_rasterize_channels()

    def _count_channel_pixels(self, tif_path: str) -> int:
        try:
            from osgeo import gdal
            import numpy as np

            ds = gdal.Open(tif_path, gdal.GA_ReadOnly)
            if ds is None:
                return 0
            band = ds.GetRasterBand(1)
            arr = band.ReadAsArray()
            nodata = band.GetNoDataValue()
            if nodata is None:
                nodata = -9999.0

            valid = (arr != nodata)
            return int(np.count_nonzero(valid & (arr > 0)))
        except Exception:
            return 0

    def _start_rasterize_channels(self):
        """
        IMPORTANTÍSSIMO:
        Rasteriza usando a GRADE DO filled_layer (DEM preenchido), para bater 1:1
        com o ELEVATION usado no HAND.
        """
        alg = QgsApplication.processingRegistry().algorithmById("gdal:rasterize")
        if alg is None:
            self.plugin.mostrar_mensagem(self.plugin.tr("Algoritmo 'gdal:rasterize' não encontrado no Processing."), "Erro")
            return

        base = self.filled_layer if (isinstance(self.filled_layer, QgsRasterLayer) and self.filled_layer.isValid()) else self.dem_layer

        params = {
            "INPUT": self.canais_layer,
            "FIELD": None,
            "BURN": 1.0,
            "USE_Z": False,

            # UNITS=0 => WIDTH/HEIGHT = número de pixels
            "UNITS": 0,
            "WIDTH": int(base.width()),
            "HEIGHT": int(base.height()),
            "EXTENT": base.extent(),

            # fora dos canais vira NoData, e só canal vira 1
            "NODATA": -9999.0,
            "INIT": -9999.0,

            # Int16 evita “meio valor” e ajuda o SAGA a não “perder” canal
            "DATA_TYPE": 1,   # Int16

            "OPTIONS": "",
            "INVERT": False,
            "EXTRA": "",
            "OUTPUT": self.channels_grid_path}

        self.task_rasterize = QgsProcessingAlgRunnerTask(alg, params, self.context, self.feedback_rasterize)
        self.task_rasterize.executed.connect(self._on_rasterize_finished)
        QgsApplication.taskManager().addTask(self.task_rasterize)

    def _on_rasterize_finished(self, successful: bool, results: dict):
        if (not successful) or (not os.path.exists(self.channels_grid_path)):
            self.plugin.mostrar_mensagem(self.plugin.tr("Falha ao rasterizar canais (SAGA inundação)."), "Erro", forcar=True)
            return

        # Sanidade: sem pixels de canal => o SAGA sempre vai dar “Channel Network”
        nchan = self._count_channel_pixels(self.channels_grid_path)
        if nchan <= 0:
            self.plugin.mostrar_mensagem(self.plugin.tr("Raster de canais ficou vazio (0 pixels > 0).\nIsso causa o erro 'Channel Network' no SAGA.\nVerifique CRS/extent do vetor de canais vs DEM preenchido."), "Erro", forcar=True)
            return

        self.plugin.mostrar_mensagem(self.plugin.tr("Inundação (SAGA): etapa 1/3 concluída. (etapa 2/3: calculando HAND)..."), "Info")
        self._start_hand()

    def _start_hand(self):
        alg_id = "sagang:verticaldistancetochannelnetwork"
        alg = QgsApplication.processingRegistry().algorithmById(alg_id)
        if alg is None:
            alg_id = "saga:verticaldistancetochannelnetwork"
            alg = QgsApplication.processingRegistry().algorithmById(alg_id)

        if alg is None:
            self.plugin.mostrar_mensagem(self.plugin.tr("Não encontrei o algoritmo SAGA: Vertical Distance to Channel Network."), "Erro")
            return

        params_hand = {
            "ELEVATION": self.filled_layer,          # usa o DEM preenchido (grade do SAGA)
            "CHANNELS": self.channels_grid_path,     # raster binário (NoData fora, 1 nos canais)
            "DISTANCE": self.hand_path,              # GeoTIFF de saída
            "BASELEVEL": QgsProcessing.TEMPORARY_OUTPUT,
            "THRESHOLD": 1.0,
            "MAXITER": 0,
            "NOUNDERGROUND": True}

        self.task_hand = QgsProcessingAlgRunnerTask(alg, params_hand, self.context, self.feedback_hand)
        self.task_hand.executed.connect(self._on_hand_finished)
        QgsApplication.taskManager().addTask(self.task_hand)

    def _on_hand_finished(self, successful: bool, results: dict):
        log_prefix = "Tempo Salvo Tools"

        # o Processing às vezes marca successful=True mesmo com erro interno,
        # então a verdade final é: o arquivo existe?
        if (not successful) or (not os.path.exists(self.hand_path)):
            try:
                QgsMessageLog.logMessage(self.plugin.tr("[SAGA HAND] successful={successful} results={results}").format(successful=successful, results=results), log_prefix, level=Qgis.MessageLevel.Warning)
            except Exception:
                pass  # nosec B110

            self.plugin.mostrar_mensagem(self.plugin.tr("Falha ao calcular HAND (SAGA inundação).\nSe aparecer 'Channel Network', o raster de canais ainda não está válido."), "Erro", forcar=True)
            return

        hand_layer = QgsRasterLayer(self.hand_path, self.plugin.tr("{dem_name} - HAND (SAGA)").format(dem_name=self.dem_layer.name()), "gdal")
        if not hand_layer.isValid():
            self.plugin.mostrar_mensagem(self.plugin.tr("HAND foi gerado, mas falhou ao carregar no QGIS."), "Erro", forcar=True)
            return

        try:
            hand_layer.setCrs(self.dem_layer.crs())
        except Exception:
            pass  # nosec B110

        self.plugin._add_saga_raster(hand_layer, short_code="HAND")

        # HAND desmarcado
        try:
            node = QgsProject.instance().layerTreeRoot().findLayer(hand_layer.id())
            if node:
                node.setItemVisibilityChecked(False)
        except Exception:
            pass  # nosec B110

        self.plugin.mostrar_mensagem(self.plugin.tr("Inundação (SAGA): etapa 2/3 concluída. (etapa 3/3: calculando profundidade)..."), "Info")
        self._start_depth(hand_layer)

    def _start_depth(self, hand_layer: QgsRasterLayer):
        e = QgsRasterCalculatorEntry()
        e.ref = "hand@1"
        e.raster = hand_layer
        e.bandNumber = 1

        stage = float(self.stage)
        expr = f"(({stage} - hand@1) * (({stage} - hand@1) > 0))"

        base = self.filled_layer if (isinstance(self.filled_layer, QgsRasterLayer) and self.filled_layer.isValid()) else self.dem_layer

        self.task_depth = _RasterCalcTask(
            self.plugin.tr("Inundação (SAGA): calculando profundidade"),
            expr=expr,
            out_path=self.depth_path,
            extent=base.extent(),
            width=base.width(),
            height=base.height(),
            entries=[e])
        self.task_depth.taskCompleted.connect(self._on_depth_finished)
        self.task_depth.taskTerminated.connect(self._on_depth_terminated)
        QgsApplication.taskManager().addTask(self.task_depth)

    def _on_depth_terminated(self):
        self.plugin.mostrar_mensagem(self.plugin.tr("Inundação (SAGA) cancelada."), "Aviso")

    def _on_depth_finished(self):
        if not os.path.exists(self.depth_path):
            self.plugin.mostrar_mensagem(self.plugin.tr("Falha ao gerar raster de inundação (SAGA)."), "Erro", forcar=True)
            return

        stage_txt = f"{self.stage:.3f}".rstrip("0").rstrip(".")
        depth_layer = QgsRasterLayer(self.depth_path, self.plugin.tr("{dem_name} - Inundação (m) STAGE={stage_txt} (SAGA)").format(dem_name=self.dem_layer.name(), stage_txt=stage_txt), "gdal")
        if depth_layer.isValid():
            try:
                depth_layer.setCrs(self.dem_layer.crs())
            except Exception:
                pass  # nosec B110

            self.plugin._add_saga_raster(depth_layer, short_code="INUND")

            try:
                if hasattr(self.plugin, "_apply_depth_raster_style"):
                    self.plugin._apply_depth_raster_style(depth_layer)
            except Exception:
                pass  # nosec B110

        self.plugin.mostrar_mensagem(self.plugin.tr("Inundação (SAGA) concluída ✅"), "Info")
        try:
            self.plugin._update_action_buttons_state()
        except Exception:
            pass  # nosec B110

class WhiteboxInundacaoTask(QgsTask):
    """
    Calcula HAND (Height Above Nearest Drainage) e profundidade de inundação (stage - HAND)
    usando rasters já gerados pelo WhiteboxTools:
      - D8 pointer
      - streams raster (canais) com valores > 0

    Não gera vetores.
    """
    def __init__(self, plugin, dem_layer, safe_dem_layer, pntr_layer, streams_layer, stage: float, workspace: str):
        super().__init__(plugin.tr("Inundação Whitebox (Tempo Salvo Tools)"), QgsTask.Flag.CanCancel)
        self.plugin = plugin
        self.dem_layer = dem_layer
        self.safe_dem_layer = safe_dem_layer
        self.pntr_layer = pntr_layer
        self.streams_layer = streams_layer
        self.stage = float(stage)
        self.workspace = workspace

        # saídas
        base_ascii = plugin._make_ascii_filename(dem_layer.source())
        root, _ext = os.path.splitext(base_ascii)
        self.hand_path = os.path.join(self.workspace, f"hand_{root}.tif")
        self.depth_path = os.path.join(self.workspace, f"inund_{root}_stage_{self.stage:.3f}.tif")

        self.error_message = None

    @staticmethod
    def _src_path(layer: QgsRasterLayer) -> str:
        p = layer.source() or ""
        # remove “|layername=” etc
        return p.split("|")[0].strip()

    def run(self):
        try:
            if self.isCanceled():
                return False

            dem_path = self._src_path(self.safe_dem_layer if self.safe_dem_layer else self.dem_layer)
            pntr_path = self._src_path(self.pntr_layer)
            streams_path = self._src_path(self.streams_layer)

            if not os.path.exists(dem_path):
                self.error_message = self.plugin.tr("DEM não encontrado: {path}").format(path=dem_path)
                return False
            if not os.path.exists(pntr_path):
                self.error_message = self.plugin.tr("D8 pointer não encontrado: {path}").format(path=pntr_path)
                return False
            if not os.path.exists(streams_path):
                self.error_message = self.plugin.tr("Streams raster não encontrado: {path}").format(path=streams_path)
                return False

            dem_ds = gdal.Open(dem_path, gdal.GA_ReadOnly)
            pntr_ds = gdal.Open(pntr_path, gdal.GA_ReadOnly)
            str_ds = gdal.Open(streams_path, gdal.GA_ReadOnly)

            if dem_ds is None or pntr_ds is None or str_ds is None:
                self.error_message = self.plugin.tr("Falha ao abrir rasters (DEM/pointer/streams).")
                return False

            dem = dem_ds.GetRasterBand(1).ReadAsArray().astype(np.float32, copy=False)
            pntr_band = pntr_ds.GetRasterBand(1)
            pntr = pntr_band.ReadAsArray()
            streams = str_ds.GetRasterBand(1).ReadAsArray()

            nrows, ncols = dem.shape
            if pntr.shape != dem.shape or streams.shape != dem.shape:
                self.error_message = self.plugin.tr("Rasters com dimensões diferentes.\nDEM={dem_shape}, D8={pntr_shape}, Streams={streams_shape}\nDica: garanta que os produtos Whitebox foram gerados a partir do mesmo DEM/grid.").format(dem_shape=dem.shape, pntr_shape=pntr.shape, streams_shape=streams.shape)
                return False

            dem_nodata = dem_ds.GetRasterBand(1).GetNoDataValue()
            pntr_nodata = pntr_band.GetNoDataValue()
            str_nodata = str_ds.GetRasterBand(1).GetNoDataValue()

            # Máscaras básicas
            valid = np.ones_like(dem, dtype=bool)
            if dem_nodata is not None:
                valid &= (dem != float(dem_nodata))
            if pntr_nodata is not None:
                valid &= (pntr != pntr_nodata)

            # streams: considera canal se >0 e não nodata
            stream_mask = (streams > 0)
            if str_nodata is not None:
                stream_mask &= (streams != str_nodata)
            stream_mask &= valid

            if not np.any(stream_mask):
                self.error_message = self.plugin.tr("Streams raster não contém células de canal (>0).")
                return False

            # Detecta esquema do D8 pointer
            pntr_valid = pntr[valid]
            pmax = float(np.nanmax(pntr_valid)) if pntr_valid.size else 0.0

            # Whitebox “base-2” típico: 1,2,4,8,16,32,64,128
            use_base2 = (pmax > 8.0)

            # Monta dest (índice linear do downstream)
            N = nrows * ncols
            idx = np.arange(N, dtype=np.int32)
            r = idx // ncols
            c = idx - r * ncols

            p = pntr.reshape(-1)
            vmask = valid.reshape(-1)

            dest = np.full(N, -1, dtype=np.int32)

            # mapeamento: (dr, dc, code)
            if use_base2:
                # E, SE, S, SW, W, NW, N, NE  (padrão base-2)
                dirs = [
                    (0, 1, 1),
                    (1, 1, 2),
                    (1, 0, 4),
                    (1, -1, 8),
                    (0, -1, 16),
                    (-1, -1, 32),
                    (-1, 0, 64),
                    (-1, 1, 128)]
            else:
                # esquema 1..8 (se você gerar ESRI convertido etc)
                # assumindo: 1=E,2=NE,3=N,4=NW,5=W,6=SW,7=S,8=SE
                dirs = [
                    (0, 1, 1),
                    (-1, 1, 2),
                    (-1, 0, 3),
                    (-1, -1, 4),
                    (0, -1, 5),
                    (1, -1, 6),
                    (1, 0, 7),
                    (1, 1, 8)]

            for dr, dc, code in dirs:
                if self.isCanceled():
                    return False

                m = vmask & (p == code)

                if dr == -1:
                    m &= (r > 0)
                elif dr == 1:
                    m &= (r < (nrows - 1))

                if dc == -1:
                    m &= (c > 0)
                elif dc == 1:
                    m &= (c < (ncols - 1))

                dest[m] = idx[m] + (dr * ncols + dc)

            # Constrói lista de adjacência inversa via linked list (head/next)
            head = np.full(N, -1, dtype=np.int32)
            next_in = np.full(N, -1, dtype=np.int32)

            src_cells = np.where(dest >= 0)[0].astype(np.int32, copy=False)
            for u in src_cells:
                if self.isCanceled():
                    return False
                v = int(dest[u])
                next_in[u] = head[v]
                head[v] = u

            # BFS a partir dos canais: base_elev
            dem_flat = dem.reshape(-1)
            stream_flat = stream_mask.reshape(-1)

            base = np.full(N, np.nan, dtype=np.float32)
            q = deque()

            stream_idx = np.where(stream_flat)[0].astype(np.int32, copy=False)
            base[stream_idx] = dem_flat[stream_idx]
            for s in stream_idx:
                q.append(int(s))

            while q:
                if self.isCanceled():
                    return False

                v = q.popleft()
                u = int(head[v])
                while u != -1:
                    if np.isnan(base[u]):
                        # se por algum motivo u também é stream, base = DEM
                        base[u] = dem_flat[u] if stream_flat[u] else base[v]
                        q.append(u)
                    u = int(next_in[u])

            # HAND
            hand = dem_flat - base
            # onde base não existe, vira nodata
            hand[np.isnan(base)] = np.nan
            hand = np.where(np.isnan(hand), np.nan, np.maximum(hand, 0.0)).astype(np.float32, copy=False)

            # Depth por stage
            depth = self.stage - hand
            depth = np.where(np.isnan(hand), np.nan, np.maximum(depth, 0.0)).astype(np.float32, copy=False)

            # Escreve GeoTIFFs
            gt = dem_ds.GetGeoTransform()
            prj = dem_ds.GetProjection()

            drv = gdal.GetDriverByName("GTiff")
            if drv is None:
                self.error_message = self.plugin.tr("Driver GTiff não disponível (GDAL).")
                return False

            def write_tif(out_path: str, arr_flat: np.ndarray, nodata_val: float):
                ds = drv.Create(out_path, ncols, nrows, 1, gdal.GDT_Float32, options=["COMPRESS=LZW", "TILED=YES"])
                ds.SetGeoTransform(gt)
                ds.SetProjection(prj)
                b = ds.GetRasterBand(1)
                b.SetNoDataValue(float(nodata_val))
                out = arr_flat.reshape((nrows, ncols))
                # troca nan por nodata
                out2 = np.where(np.isnan(out), float(nodata_val), out).astype(np.float32, copy=False)
                b.WriteArray(out2)
                b.FlushCache()
                ds.FlushCache()
                ds = None

            write_tif(self.hand_path, hand, nodata_val=-9999.0)
            write_tif(self.depth_path, depth, nodata_val=-9999.0)

            return True

        except Exception as e:
            self.error_message = self.plugin.tr("Erro na inundação (Whitebox): {error}").format(error=str(e))
            return False

class TauDEMFloodSimTask(QgsTask):
    """
    Task que:
    1) Lê FEL, P (D8) e SRC (canais) já gerados pelo TauDEM
    2) Calcula HAND (altura acima do canal mais próximo a jusante)
    3) Gera rasters depth = max(0, stage - HAND) para cada frame (stage)
    """
    def __init__(self, plugin, *, dem_layer, fel_layer, p_layer, src_layer, stages, workspace, dem_name):
        super().__init__(plugin.tr("TauDEM: Simulação de Inundação ({dem_name})").format(dem_name=dem_name), QgsTask.Flag.CanCancel)
        self.plugin = plugin
        self.dem_layer = dem_layer
        self.dem_name = dem_name

        self.fel_layer = fel_layer
        self.p_layer = p_layer
        self.src_layer = src_layer

        self.stages = [float(x) for x in stages]
        self.workspace = workspace

        self.depth_paths = []
        self.hand_path = None
        self.error_message = None

    @staticmethod
    def _clean_raster_path(uri: str) -> str:
        if not uri:
            return uri
        if " |" in uri:
            return uri.split(" |", 1)[0]
        return uri

    def run(self) -> bool:
        try:
            gdal.UseExceptions()

            fel_path = self._clean_raster_path(self.fel_layer.source())
            p_path = self._clean_raster_path(self.p_layer.source())
            src_path = self._clean_raster_path(self.src_layer.source())

            ds_fel = gdal.Open(fel_path, gdal.GA_ReadOnly)
            ds_p = gdal.Open(p_path, gdal.GA_ReadOnly)
            ds_src = gdal.Open(src_path, gdal.GA_ReadOnly)

            if ds_fel is None or ds_p is None or ds_src is None:
                raise RuntimeError(self.plugin.tr("Falha ao abrir FEL/P/SRC com GDAL."))

            rows = ds_fel.RasterYSize
            cols = ds_fel.RasterXSize

            if ds_p.RasterXSize != cols or ds_p.RasterYSize != rows or ds_src.RasterXSize != cols or ds_src.RasterYSize != rows:
                raise RuntimeError(self.plugin.tr("FEL, P e SRC não possuem as mesmas dimensões (lin/col)."))

            band_fel = ds_fel.GetRasterBand(1)
            band_p = ds_p.GetRasterBand(1)
            band_src = ds_src.GetRasterBand(1)

            nodata_fel = band_fel.GetNoDataValue()
            nodata_p = band_p.GetNoDataValue()
            nodata_src = band_src.GetNoDataValue()

            fel = band_fel.ReadAsArray().astype(np.float32, copy=False)
            p = band_p.ReadAsArray()
            src = band_src.ReadAsArray()

            # máscara válida
            valid = np.ones((rows, cols), dtype=bool)
            if nodata_fel is not None:
                valid &= (fel != nodata_fel)
            if nodata_p is not None:
                valid &= (p != nodata_p)
            if nodata_src is not None:
                valid &= (src != nodata_src)

            # canais: SRC > 0
            channel = valid & (src > 0)

            # LUT D8: tenta detectar se é 1..8 (TauDEM comum) ou powers-of-two (1,2,4,...,128)
            p_int = p.astype(np.int32, copy=False)
            pmax = int(np.nanmax(p_int[valid])) if np.any(valid) else 0

            # dr, dc lookup
            if pmax <= 8:
                # TauDEM (1..8): 1=E,2=NE,3=N,4=NW,5=W,6=SW,7=S,8=SE
                dr_lut = np.zeros(9, dtype=np.int16)
                dc_lut = np.zeros(9, dtype=np.int16)
                dr_lut[1], dc_lut[1] = 0,  1
                dr_lut[2], dc_lut[2] = -1, 1
                dr_lut[3], dc_lut[3] = -1, 0
                dr_lut[4], dc_lut[4] = -1,-1
                dr_lut[5], dc_lut[5] = 0, -1
                dr_lut[6], dc_lut[6] = 1, -1
                dr_lut[7], dc_lut[7] = 1,  0
                dr_lut[8], dc_lut[8] = 1,  1
                dr = dr_lut[np.clip(p_int, 0, 8)]
                dc = dc_lut[np.clip(p_int, 0, 8)]
                has_flow = valid & (p_int >= 1) & (p_int <= 8)
            else:
                # Powers-of-two (ESRI-like): 1=E,2=SE,4=S,8=SW,16=W,32=NW,64=N,128=NE
                dr_lut = np.zeros(129, dtype=np.int16)
                dc_lut = np.zeros(129, dtype=np.int16)
                dr_lut[1],   dc_lut[1]   = 0,  1
                dr_lut[2],   dc_lut[2]   = 1,  1
                dr_lut[4],   dc_lut[4]   = 1,  0
                dr_lut[8],   dc_lut[8]   = 1, -1
                dr_lut[16],  dc_lut[16]  = 0, -1
                dr_lut[32],  dc_lut[32]  = -1,-1
                dr_lut[64],  dc_lut[64]  = -1, 0
                dr_lut[128], dc_lut[128] = -1, 1
                p_clip = np.clip(p_int, 0, 128)
                dr = dr_lut[p_clip]
                dc = dc_lut[p_clip]
                has_flow = valid & (p_int > 0)

            # downstream index (flatten)
            N = rows * cols
            idx = np.arange(N, dtype=np.int32)
            rr = (idx // cols).astype(np.int32, copy=False)
            cc = (idx % cols).astype(np.int32, copy=False)

            drf = dr.reshape(-1).astype(np.int32, copy=False)
            dcf = dc.reshape(-1).astype(np.int32, copy=False)
            flowf = has_flow.reshape(-1)

            r2 = rr + drf
            c2 = cc + dcf

            inside = (r2 >= 0) & (r2 < rows) & (c2 >= 0) & (c2 < cols) & flowf
            dest = np.full(N, -1, dtype=np.int32)
            dest[inside] = (r2[inside] * cols + c2[inside]).astype(np.int32, copy=False)

            # construir lista "upstream" via sort (CSR)
            valid_src_idx = np.where(dest >= 0)[0]
            valid_dest_idx = dest[valid_src_idx]
            order = np.argsort(valid_dest_idx, kind="mergesort")
            valid_dest_sorted = valid_dest_idx[order]
            adj = valid_src_idx[order]  # upstream cells packed

            counts = np.bincount(valid_dest_sorted, minlength=N)
            offsets = np.zeros(N + 1, dtype=np.int64)
            offsets[1:] = np.cumsum(counts)

            # base elevation: FEL do canal mais próximo a jusante
            fel_f = fel.reshape(-1)
            channel_f = channel.reshape(-1)

            base = np.full(N, np.nan, dtype=np.float32)
            base[channel_f] = fel_f[channel_f]

            # BFS/propagação a montante
            queue = adj  # reaproveita array? não, melhor iniciar com canais
            q = list(np.where(channel_f)[0])
            head = 0

            # progresso: 0..60% aqui
            step_check = 50000

            while head < len(q):
                if self.isCanceled():
                    return False

                j = q[head]
                head += 1

                bj = base[j]
                if np.isnan(bj):
                    continue

                a0 = int(offsets[j])
                a1 = int(offsets[j + 1])
                if a1 <= a0:
                    continue

                ups = adj[a0:a1]
                if ups.size == 0:
                    continue

                unset = np.isnan(base[ups])
                if not np.any(unset):
                    continue

                ups2 = ups[unset]
                ch2 = channel_f[ups2]

                # se for canal, ele mesmo é a referência
                if np.any(ch2):
                    ups_ch = ups2[ch2]
                    base[ups_ch] = fel_f[ups_ch]
                    q.extend(ups_ch.tolist())

                # se não for canal, herda a cota do downstream
                if np.any(~ch2):
                    ups_nc = ups2[~ch2]
                    base[ups_nc] = bj
                    q.extend(ups_nc.tolist())

                if head % step_check == 0:
                    prog = min(60.0, 60.0 * (head / max(1.0, float(N))))
                    self.setProgress(prog)

            # HAND
            hand = (fel_f - base).astype(np.float32, copy=False)
            hand[np.isnan(base)] = np.nan

            # grava HAND (opcional, mas ajuda debug e reuso)
            gt = ds_fel.GetGeoTransform()
            prj = ds_fel.GetProjection()

            nodata_out = -9999.0
            hand2d = hand.reshape(rows, cols)
            hand2d_out = np.where(np.isfinite(hand2d), hand2d, nodata_out).astype(np.float32, copy=False)

            self.hand_path = os.path.join(self.workspace, f"{self.dem_name}_HAND.tif")
            drv = gdal.GetDriverByName("GTiff")
            ds_out = drv.Create(self.hand_path, cols, rows, 1, gdal.GDT_Float32, options=["COMPRESS=LZW"])
            ds_out.SetGeoTransform(gt)
            ds_out.SetProjection(prj)
            b = ds_out.GetRasterBand(1)
            b.SetNoDataValue(nodata_out)
            b.WriteArray(hand2d_out)
            b.FlushCache()
            ds_out = None

            # Depth frames
            n = len(self.stages)
            if n == 0:
                raise RuntimeError(self.plugin.tr("Lista de níveis vazia."))

            for i, stage in enumerate(self.stages):
                if self.isCanceled():
                    return False

                depth = (stage - hand).astype(np.float32, copy=False)
                depth = np.where(np.isfinite(depth) & (depth > 0), depth, 0.0).astype(np.float32, copy=False)

                depth2d = depth.reshape(rows, cols)
                out = np.where(np.isfinite(depth2d), depth2d, 0.0).astype(np.float32, copy=False)

                out_path = os.path.join(self.workspace, f"{self.dem_name}_INUND_{i:03d}_h{stage:.3f}.tif")
                ds_d = drv.Create(out_path, cols, rows, 1, gdal.GDT_Float32, options=["COMPRESS=LZW"])
                ds_d.SetGeoTransform(gt)
                ds_d.SetProjection(prj)
                bd = ds_d.GetRasterBand(1)
                bd.SetNoDataValue(0.0)
                bd.WriteArray(out)
                bd.FlushCache()
                ds_d = None

                self.depth_paths.append(out_path)

                # progresso: 60..100%
                self.setProgress(60.0 + 40.0 * ((i + 1) / float(n)))

            return True

        except Exception as e:
            self.error_message = self.plugin.tr("Erro na simulação de inundação (TauDEM): {error}").format(error=str(e))
            return False

class TauDEMInundacaoTask(QgsTask):
    """
    Calcula HAND e inundação usando apenas produtos já existentes do TauDEM:
      - FEL (DEM preenchido)
      - P   (D8 flow direction, codificação TauDEM 1..8)
      - SRC (raster de canais)

    Saídas:
      - hand.tif
      - inund_depth_stage_<stage>.tif
    """
    def __init__(self, *, plugin, dem_layer: QgsRasterLayer, fel_path: str, p_path: str, src_path: str, stage_m: float, workspace: str):
        super().__init__(plugin.tr("TauDEM: Inundação (HAND)"), QgsTask.Flag.CanCancel)
        self.plugin = plugin
        self.dem_layer = dem_layer
        self.dem_name = dem_layer.name()

        self.fel_path = fel_path
        self.p_path = p_path
        self.src_path = src_path

        self.stage_m = float(stage_m)
        self.workspace = workspace
        self.error_message = None

        self.hand_path = os.path.join(workspace, "hand.tif")
        self.depth_path = None

    def _open_band(self, path: str):
        ds = gdal.Open(path, gdal.GA_ReadOnly)
        if ds is None:
            raise RuntimeError(self.plugin.tr("Não foi possível abrir raster: {path}").format(path=path))

        band = ds.GetRasterBand(1)
        if band is None:
            raise RuntimeError(self.plugin.tr("Raster sem banda 1: {path}").format(path=path))

        return ds, band

    def _write_geotiff(self, path: str, arr2d: np.ndarray, *, gt, proj_wkt, nodata, gdal_dtype):
        driver = gdal.GetDriverByName("GTiff")
        if driver is None:
            raise RuntimeError(self.plugin.tr("Driver GTiff não disponível (GDAL)."))

        rows, cols = arr2d.shape
        ds_out = driver.Create(path, cols, rows, 1, gdal_dtype, options=["COMPRESS=DEFLATE", "TILED=YES"])
        if ds_out is None:
            raise RuntimeError(self.plugin.tr("Falha ao criar GeoTIFF: {path}").format(path=path))

        ds_out.SetGeoTransform(gt)
        ds_out.SetProjection(proj_wkt)

        band = ds_out.GetRasterBand(1)
        if nodata is not None:
            band.SetNoDataValue(float(nodata))

        band.WriteArray(arr2d)
        band.FlushCache()
        ds_out.FlushCache()
        ds_out = None

    @staticmethod
    def _stage_to_fname(stage_m: float) -> str:
        s = f"{stage_m:.3f}".rstrip("0").rstrip(".")
        return s.replace(".", "p")

    def run(self) -> bool:
        log_prefix = "TauDEM - Inundação"

        try:
            if self.stage_m <= 0.0:
                raise RuntimeError(self.plugin.tr("STAGE deve ser > 0."))

            ds_fel, b_fel = self._open_band(self.fel_path)
            ds_p,   b_p   = self._open_band(self.p_path)
            ds_src, b_src = self._open_band(self.src_path)

            rows = ds_fel.RasterYSize
            cols = ds_fel.RasterXSize

            if ds_p.RasterXSize != cols or ds_p.RasterYSize != rows:
                raise RuntimeError(self.plugin.tr("P (D8) não tem o mesmo tamanho do FEL."))
            if ds_src.RasterXSize != cols or ds_src.RasterYSize != rows:
                raise RuntimeError(self.plugin.tr("SRC não tem o mesmo tamanho do FEL."))

            gt = ds_fel.GetGeoTransform()
            proj = ds_fel.GetProjection()

            fel = b_fel.ReadAsArray().astype(np.float32, copy=False)
            p   = b_p.ReadAsArray().astype(np.int16, copy=False)
            src = b_src.ReadAsArray()

            fel_nd = b_fel.GetNoDataValue()
            p_nd   = b_p.GetNoDataValue()
            src_nd = b_src.GetNoDataValue()

            valid = np.ones((rows, cols), dtype=bool)
            if fel_nd is not None:
                valid &= (fel != np.float32(fel_nd))
            if p_nd is not None:
                valid &= (p != np.int16(p_nd))
            if src_nd is not None:
                valid &= (src != src_nd)

            stream_mask = valid & (src > 0)
            n_stream = int(stream_mask.sum())
            if n_stream == 0:
                raise RuntimeError(self.plugin.tr("SRC não contém canais (nenhuma célula > 0). Ajuste o THRESHOLD e rode TauDEM novamente."))

            n = rows * cols
            fel_f    = fel.reshape(n)
            p_f      = p.reshape(n)
            valid_f  = valid.reshape(n)
            stream_f = stream_mask.reshape(n)

            assigned = np.zeros(n, dtype=bool)
            stream_elev = np.full(n, np.nan, dtype=np.float32)

            idx0 = np.flatnonzero(stream_f)
            assigned[idx0] = True
            stream_elev[idx0] = fel_f[idx0]
            q = deque(idx0.tolist())

            processed = 0
            step_report = max(50000, n // 200)

            # TauDEM D8 coding:
            # 1=E,2=NE,3=N,4=NW,5=W,6=SW,7=S,8=SE
            while q:
                if self.isCanceled():
                    return False

                idx = q.popleft()
                se = stream_elev[idx]
                r = idx // cols
                c = idx - r * cols

                if c > 0:
                    j = idx - 1
                    if (not assigned[j]) and valid_f[j] and (p_f[j] == 1):
                        assigned[j] = True; stream_elev[j] = se; q.append(j)

                if r < rows - 1 and c > 0:
                    j = idx + cols - 1
                    if (not assigned[j]) and valid_f[j] and (p_f[j] == 2):
                        assigned[j] = True; stream_elev[j] = se; q.append(j)

                if r < rows - 1:
                    j = idx + cols
                    if (not assigned[j]) and valid_f[j] and (p_f[j] == 3):
                        assigned[j] = True; stream_elev[j] = se; q.append(j)

                if r < rows - 1 and c < cols - 1:
                    j = idx + cols + 1
                    if (not assigned[j]) and valid_f[j] and (p_f[j] == 4):
                        assigned[j] = True; stream_elev[j] = se; q.append(j)

                if c < cols - 1:
                    j = idx + 1
                    if (not assigned[j]) and valid_f[j] and (p_f[j] == 5):
                        assigned[j] = True; stream_elev[j] = se; q.append(j)

                if r > 0 and c < cols - 1:
                    j = idx - cols + 1
                    if (not assigned[j]) and valid_f[j] and (p_f[j] == 6):
                        assigned[j] = True; stream_elev[j] = se; q.append(j)

                if r > 0:
                    j = idx - cols
                    if (not assigned[j]) and valid_f[j] and (p_f[j] == 7):
                        assigned[j] = True; stream_elev[j] = se; q.append(j)

                if r > 0 and c > 0:
                    j = idx - cols - 1
                    if (not assigned[j]) and valid_f[j] and (p_f[j] == 8):
                        assigned[j] = True; stream_elev[j] = se; q.append(j)

                processed += 1
                if processed % step_report == 0:
                    pct = 100.0 * float(assigned.sum()) / float(n)
                    self.setProgress(min(99.0, pct))

            out_nodata = -9999.0

            # HAND
            hand = np.full(n, out_nodata, dtype=np.float32)
            hand[assigned] = fel_f[assigned] - stream_elev[assigned]
            hand = np.maximum(hand, 0.0)

            self._write_geotiff(
                self.hand_path,
                hand.reshape((rows, cols)),
                gt=gt,
                proj_wkt=proj,
                nodata=out_nodata,
                gdal_dtype=gdal.GDT_Float32)

            # Depth (1 cenário só)
            depth = np.full(n, out_nodata, dtype=np.float32)
            val = self.stage_m - hand[assigned]
            val = np.where(val > 0.0, val, 0.0).astype(np.float32, copy=False)
            depth[assigned] = val

            stage_tag = self._stage_to_fname(self.stage_m)
            self.depth_path = os.path.join(self.workspace, f"inund_depth_stage_{stage_tag}m.tif")

            self._write_geotiff(
                self.depth_path,
                depth.reshape((rows, cols)),
                gt=gt,
                proj_wkt=proj,
                nodata=out_nodata,
                gdal_dtype=gdal.GDT_Float32)

            self.setProgress(100.0)
            QgsMessageLog.logMessage(self.plugin.tr("Inundação OK. canais={n_stream}; stage={stage_m}m").format(n_stream=n_stream, stage_m=self.stage_m), log_prefix, level=Qgis.MessageLevel.Info)
            return True

        except Exception as e:
            self.error_message = self.plugin.tr("Erro na inundação (HAND): {error}").format(error=str(e))
            QgsMessageLog.logMessage(self.error_message, log_prefix, level=Qgis.MessageLevel.Critical)
            return False

class _RasterCalcTask(QgsTask):
    """
    Executa um QgsRasterCalculator em segundo plano (thread do QgsTask).
    Usado para gerar rasters derivados (profundidade e máscara).
    """
    def __init__(self, title: str, *, expr: str, out_path: str, extent, width: int, height: int, entries: list[QgsRasterCalculatorEntry]):
        super().__init__(title, QgsTask.Flag.CanCancel)
        self.expr = expr
        self.out_path = out_path
        self.extent = extent
        self.width = int(width)
        self.height = int(height)
        self.entries = entries
        self.error_message = ""

    def run(self) -> bool:
        try:
            if self.isCanceled():
                return False

            self.setProgress(0)

            calc = QgsRasterCalculator(self.expr, self.out_path, "GTiff", self.extent, self.width, self.height, self.entries)

            res = calc.processCalculation()
            if res != 0:
                self.error_message = QCoreApplication.translate("_RasterCalcTask", "QgsRasterCalculator retornou código {code}.").format(code=res)
                return False

            self.setProgress(100)
            return True
        except Exception as e:
            self.error_message = str(e)
            return False

class _PocasPostProcessTask(QgsTask):
    """
    Pós-processa o resultado do polygonize (poças):
    - filtra ID > 0
    - calcula área e volume (a partir de profundidade média via QgsZonalStatistics)
    - salva em GPKG (out_vec_path)

    Obs.: Tudo roda em segundo plano; a adição ao projeto é feita no callback do Runner.
    """
    def __init__(self, title: str, *, poly_path: str, depth_path: str, out_vec_path: str, crs_authid: str, nome_vec: str):
        super().__init__(title, QgsTask.Flag.CanCancel)
        self.poly_path = poly_path
        self.depth_path = depth_path
        self.out_vec_path = out_vec_path
        self.crs_authid = crs_authid
        self.nome_vec = nome_vec
        self.error_message = ""

    def run(self) -> bool:
        try:
            if self.isCanceled():
                return False

            # Carrega polygonize
            poly_tmp_layer = QgsVectorLayer(self.poly_path, "pocas_poly_tmp", "ogr")
            if not poly_tmp_layer.isValid():
                self.error_message = QCoreApplication.translate("_PocasPostProcessTask", "Falha ao carregar camada vetorial temporária (polygonize).")
                return False

            # Raster de profundidade (arquivo físico)
            depth_rlayer = QgsRasterLayer(self.depth_path, "depth_tmp")
            if not depth_rlayer.isValid():
                self.error_message = QCoreApplication.translate("_PocasPostProcessTask", "Raster de profundidade inválido: {depth_path}").format(depth_path=self.depth_path)
                return False

            # Cria camada de saída (memória) com poças (ID > 0)
            pocas_layer = QgsVectorLayer(f"Polygon?crs={self.crs_authid}", self.nome_vec, "memory")
            prov = pocas_layer.dataProvider()
            prov.addAttributes([
                QgsField("id", QMetaType.Type.Int),
                QgsField("area_m2", QMetaType.Type.Double),
                QgsField("vol_m3", QMetaType.Type.Double)])
            pocas_layer.updateFields()

            id_field_name = "ID"
            if poly_tmp_layer.fields().indexFromName("ID") < 0:
                id_field_name = "DN"  # fallback padrão do gdal:polygonize

            features_out = []
            idx = 1

            # OBS: aqui assume CRS métrico (como já era no código original)
            for f in poly_tmp_layer.getFeatures():
                if self.isCanceled():
                    return False

                try:
                    val = float(f[id_field_name])
                except Exception:
                    val = 0.0

                if val <= 0.0:
                    continue

                geom = f.geometry()
                if geom is None or geom.isEmpty():
                    continue

                new_f = QgsFeature(pocas_layer.fields())
                new_f.setGeometry(geom)

                area = geom.area()
                new_f["id"] = idx
                new_f["area_m2"] = area
                new_f["vol_m3"] = 0.0

                features_out.append(new_f)
                idx += 1

            if not features_out:
                self.error_message = QCoreApplication.translate("_PocasPostProcessTask", "Nenhuma poça encontrada para vetorizar (todas profundidades = 0).")
                return False

            prov.addFeatures(features_out)
            pocas_layer.updateExtents()

            # ZonalStatistics (profundidade média por poça)
            zs = QgsZonalStatistics(pocas_layer, depth_rlayer, "DEP_", 1, QgsZonalStatistics.Statistic.Mean)
            zs.calculateStatistics(None)

            fields = pocas_layer.fields()
            idx_dep = -1
            for i, fld in enumerate(fields):
                if fld.name().upper().startswith("DEP_"):
                    idx_dep = i
                    break

            if idx_dep == -1:
                self.error_message = QCoreApplication.translate("_PocasPostProcessTask"," Campo DEP_* não encontrado após ZonalStatistics.")
                return False

            idx_vol = fields.indexFromName("vol_m3")

            pocas_layer.startEditing()
            for f in pocas_layer.getFeatures():
                if self.isCanceled():
                    pocas_layer.rollBack()
                    return False

                try:
                    mean_depth = float(f[idx_dep])
                except Exception:
                    mean_depth = 0.0

                try:
                    area = float(f["area_m2"])
                except Exception:
                    area = 0.0

                vol = area * mean_depth
                pocas_layer.changeAttributeValue(f.id(), idx_vol, vol)
            pocas_layer.commitChanges()

            # Salvar GPKG
            res = QgsVectorFileWriter.writeAsVectorFormat(pocas_layer, self.out_vec_path, "utf-8", pocas_layer.crs(), "GPKG")
            if isinstance(res, tuple):
                err, _ = res
            else:
                err = res

            if err != QgsVectorFileWriter.WriterError.NoError:
                self.error_message = QCoreApplication.translate("_PocasPostProcessTask", "Erro ao salvar camada vetorial de poças (código {error_code}).").format(error_code=err)
                return False

            return True

        except Exception as e:
            self.error_message = str(e)
            return False

class DepthPocasRunner:
    """
    Pipeline assíncrono (sem travar o QGIS) para:
      1) gerar raster de profundidade (filled/FEL - DEM) via QgsRasterCalculator (QgsTask)
      2) gerar máscara (depth > 0) via QgsRasterCalculator (QgsTask)
      3) polygonize (gdal:polygonize) via QgsProcessingAlgRunnerTask
      4) pós-processar (área + volume) e salvar GPKG via QgsTask
      5) adicionar raster e vetor no grupo do motor

    motor ∈ {"saga", "taudem"}
    """
    def __init__(self, plugin, *, motor: str, dem_layer: QgsRasterLayer, base_layer: QgsRasterLayer, h_min: float, gerar_vetor: bool = True):
        self.plugin = plugin
        self.motor = (motor or "").lower().strip()
        self.dem_layer = dem_layer
        self.base_layer = base_layer
        self.h_min = float(h_min)

        self.group_name = self.plugin.tr("SAGA - Drenagem") if self.motor == "saga" else self.plugin.tr("TauDEM - Drenagem")
        self.log_prefix = "Profundidade - Tempo Salvo Tools"

        # Contextos/feedbacks para tarefas do Processing
        self.context = QgsProcessingContext()
        self.context.setProject(QgsProject.instance())

        self.feedback_poly = QgsProcessingFeedback()

        # Referências às tasks (evitar GC)
        self.task_depth = None
        self.task_mask = None
        self.task_poly = None
        self.task_post = None

        # Paths (preenchidos em start)
        self.workspace = None
        self.depth_path = None
        self.mask_path = None
        self.poly_tmp_path = None
        self.out_vec_path = None

        # Objetos resultantes
        self.depth_layer = None
        self.gerar_vetor = bool(gerar_vetor)

    def start(self):
        # bloqueia botão enquanto roda
        try:
            if hasattr(self.plugin, "pushButtonPronfundidade"):
                self.plugin.pushButtonPronfundidade.setEnabled(False)
        except Exception:
            pass  # nosec B110

        # Workspace e nomes
        prefix = "ts_saga_depth_" if self.motor == "saga" else "ts_taudem_depth_"
        self.workspace = self.plugin._create_safe_workspace(prefix=prefix)

        out_name = self.plugin._make_ascii_filename(self.dem_layer.source(), prefix="depth")
        if not out_name.lower().endswith(".tif"):
            out_name += ".tif"
        self.depth_path = os.path.join(self.workspace, out_name)

        ascii_base = self.plugin._make_ascii_filename(self.depth_path, prefix="pocas")
        base = ascii_base[:-4] if ascii_base.lower().endswith(".tif") else ascii_base

        self.mask_path = os.path.join(self.workspace, f"{base}_mask.tif")
        self.poly_tmp_path = os.path.join(self.workspace, f"{base}_poly_tmp.gpkg")
        self.out_vec_path = os.path.join(self.workspace, f"{base}_pocas.gpkg")

        self.plugin.mostrar_mensagem(self.plugin.tr("Profundidade ({motor}): calculando raster em segundo plano...").format(motor=self.motor.upper()), "Info")
        self._start_depth_raster()

    def _start_depth_raster(self):
        # Entradas do RasterCalculator
        entries: list[QgsRasterCalculatorEntry] = []

        e_dem = QgsRasterCalculatorEntry()
        e_dem.ref = "dem@1"
        e_dem.raster = self.dem_layer
        e_dem.bandNumber = 1
        entries.append(e_dem)

        if self.motor == "saga":
            base_ref = "filled@1"
        else:
            base_ref = "fel@1"

        e_base = QgsRasterCalculatorEntry()
        e_base.ref = base_ref
        e_base.raster = self.base_layer
        e_base.bandNumber = 1
        entries.append(e_base)

        base_expr = f"{base_ref} - dem@1"

        if self.h_min <= 0.0:
            expr = f"({base_expr}) * (({base_expr}) > 0)"
        else:
            expr = f"({base_expr}) * (({base_expr}) >= {self.h_min})"

        title = self.plugin.tr("Profundidade ({motor}) - Raster").format(motor=self.motor.upper())
        grid_layer = self.base_layer if isinstance(self.base_layer, QgsRasterLayer) and self.base_layer.isValid() else self.dem_layer

        self.task_depth = _RasterCalcTask(
            title,
            expr=expr,
            out_path=self.depth_path,
            extent=grid_layer.extent(),
            width=grid_layer.width(),
            height=grid_layer.height(),
            entries=[e_dem, e_base])

        self.task_depth.taskCompleted.connect(self._on_depth_finished)
        self.task_depth.taskTerminated.connect(self._on_depth_terminated)

        QgsApplication.taskManager().addTask(self.task_depth)

    def _on_depth_terminated(self):
        self._finish_with_error(self.plugin.tr("Cálculo de profundidade cancelado."))

    def _on_depth_finished(self):
        if not self.task_depth or self.task_depth.status() != QgsTask.TaskStatus.Complete:
            msg = getattr(self.task_depth, "error_message", "") if self.task_depth else ""
            self._finish_with_error(self.plugin.tr("Falha ao calcular raster de profundidade. {message}").format(message=msg).strip())
            return

        # Carrega camada raster no thread principal
        titulo = self.plugin.tr("{dem_name} - Profundidade mínima").format(dem_name=self.dem_layer.name())
        if self.motor == "taudem":
            titulo += " (TauDEM)"
        if self.h_min > 0.0:
            titulo += f" ≥ {self.h_min:.2f} m"

        self.depth_layer = QgsRasterLayer(self.depth_path, titulo, "gdal")
        if not self.depth_layer.isValid():
            self._finish_with_error(self.plugin.tr("Raster de profundidade gerado, mas falhou ao ser carregado."))
            return

        # Aplica estilo e adiciona ao grupo
        try:
            self.plugin._apply_depth_raster_style(self.depth_layer)
        except Exception:
            pass  # nosec B110

        self._add_raster_to_group(self.depth_layer)

        if not self.gerar_vetor:
            self._finish_with_success(self.plugin.tr("Raster de profundidade gerado (sem vetorização)."))
            return

        self.plugin.mostrar_mensagem(self.plugin.tr("Raster de profundidade gerado. Vetorizando poças (em segundo plano)."), "Info")
        self._start_mask_raster()

    def _start_mask_raster(self):
        # máscara depth > 0
        entries: list[QgsRasterCalculatorEntry] = []
        e_depth = QgsRasterCalculatorEntry()
        e_depth.ref = "depth@1"
        e_depth.raster = self.depth_layer
        e_depth.bandNumber = 1
        entries.append(e_depth)

        expr = "depth@1 > 0"

        self.task_mask = _RasterCalcTask(
            self.plugin.tr("Poças - Máscara (depth>0)"),
            expr=expr,
            out_path=self.mask_path,
            extent=self.depth_layer.extent(),
            width=self.depth_layer.width(),
            height=self.depth_layer.height(),
            entries=entries)
        self.task_mask.taskCompleted.connect(self._on_mask_finished)
        self.task_mask.taskTerminated.connect(self._on_mask_terminated)

        QgsApplication.taskManager().addTask(self.task_mask)

    def _on_mask_terminated(self):
        self._finish_with_error(self.plugin.tr("Cálculo da máscara (depth>0) cancelado."))

    def _on_mask_finished(self):
        if not self.task_mask or self.task_mask.status() != QgsTask.TaskStatus.Complete:
            msg = getattr(self.task_mask, "error_message", "") if self.task_mask else ""
            self._finish_with_error(self.plugin.tr("Falha ao criar raster máscara (depth>0). {message}").format(message=msg).strip())
            return

        # Polygonize (Processing task)
        alg = QgsApplication.processingRegistry().algorithmById("gdal:polygonize")
        if alg is None:
            self._finish_with_error(self.plugin.tr("Algoritmo 'gdal:polygonize' não encontrado no Processing."))
            return

        params = {
            "INPUT": self.mask_path,
            "BAND": 1,
            "FIELD": "ID",
            "EIGHT_CONNECTEDNESS": False,
            "OUTPUT": self.poly_tmp_path}

        self.task_poly = QgsProcessingAlgRunnerTask(alg, params, self.context, self.feedback_poly)
        self.task_poly.executed.connect(self._on_polygonize_finished)
        QgsApplication.taskManager().addTask(self.task_poly)

    def _on_polygonize_finished(self, successful: bool, results: dict):
        if not successful:
            self._finish_with_error(self.plugin.tr("Erro ao vetorizar poças (gdal:polygonize)."))
            return

        poly_path = results.get("OUTPUT") or self.poly_tmp_path

        # Nome do vetor (mesma lógica do método síncrono)
        dem_name = self.dem_layer.name() if self.dem_layer else ""
        depth_name = self.depth_layer.name() if self.depth_layer else ""

        if dem_name and depth_name.startswith(dem_name):
            suffix = depth_name[len(dem_name):]
            nome_vec = self.plugin.tr("{dem_name} - Poças{suffix}").format(dem_name=dem_name, suffix=suffix)
        elif dem_name:
            nome_vec = self.plugin.tr("{dem_name} - Poças").format(dem_name=dem_name)
        else:
            nome_vec = self.plugin.tr("Poças")

        crs = self.dem_layer.crs() if self.dem_layer and self.dem_layer.isValid() else self.depth_layer.crs()

        self.task_post = _PocasPostProcessTask(
            self.plugin.tr("Poças - Área e Volume"),
            poly_path=poly_path,
            depth_path=self.depth_path,
            out_vec_path=self.out_vec_path,
            crs_authid=crs.authid(),
            nome_vec=nome_vec)
        self.task_post.taskCompleted.connect(self._on_post_finished)
        self.task_post.taskTerminated.connect(self._on_post_terminated)

        QgsApplication.taskManager().addTask(self.task_post)

    def _on_post_terminated(self):
        self._finish_with_error(self.plugin.tr("Pós-processamento de poças cancelado."))

    def _on_post_finished(self):
        if not self.task_post or self.task_post.status() != QgsTask.TaskStatus.Complete:
            msg = getattr(self.task_post, "error_message", "") if self.task_post else ""
            # Se for "Nenhuma poça...", repassa como info (não erro)
            if msg and self.plugin.tr("Nenhuma poça") in msg:
                self._finish_with_info(msg)
            else:
                self._finish_with_error(self.plugin.tr("Falha ao gerar poças (área/volume). {message}").format(message=msg).strip())
            return

        # Adiciona camada final ao projeto
        nome_vec = getattr(self.task_post, "nome_vec", self.plugin.tr("Poças"))
        final_layer = QgsVectorLayer(self.out_vec_path, nome_vec, "ogr")
        if not final_layer.isValid():
            self._finish_with_error(self.plugin.tr("Poças geradas, mas falhou ao carregar o vetor no QGIS."))
            return

        self._add_vector_to_group(final_layer, nome_vec)

        self._finish_with_success(self.plugin.tr("Poças geradas com sucesso (área e volume)."))

    def _add_raster_to_group(self, layer: QgsRasterLayer):
        project = QgsProject.instance()
        root = project.layerTreeRoot()
        group = root.findGroup(self.group_name)
        if group is None:
            group = root.addGroup(self.group_name)

        # Remove anteriores com mesmo nome
        for node in list(group.findLayers()):
            lyr = node.layer()
            if isinstance(lyr, QgsRasterLayer) and lyr.name() == layer.name():
                group.removeChildNode(node)
                project.removeMapLayer(lyr.id())

        project.addMapLayer(layer, addToLegend=False)
        group.addLayer(layer)
        group.setExpanded(True)

        node = root.findLayer(layer.id())
        if node:
            node.setExpanded(False)

    def _add_vector_to_group(self, layer: QgsVectorLayer, layer_name: str):
        project = QgsProject.instance()
        root = project.layerTreeRoot()
        group = root.findGroup(self.group_name)
        if group is None:
            group = root.addGroup(self.group_name)

        for node in list(group.findLayers()):
            lyr = node.layer()
            if lyr and lyr.name() == layer_name:
                group.removeChildNode(node)
                project.removeMapLayer(lyr.id())

        project.addMapLayer(layer, addToLegend=False)
        group.addLayer(layer)
        group.setExpanded(True)

        node = root.findLayer(layer.id())
        if node:
            node.setExpanded(False)

    def _finish_with_success(self, msg: str):
        self._unlock_ui()
        self.plugin.mostrar_mensagem(msg, "Sucesso")
        if getattr(self.plugin, "_depth_runner", None) is self:
            self.plugin._depth_runner = None

    def _finish_with_info(self, msg: str):
        self._unlock_ui()
        self.plugin.mostrar_mensagem(msg, "Info")
        if getattr(self.plugin, "_depth_runner", None) is self:
            self.plugin._depth_runner = None

    def _finish_with_error(self, msg: str):
        self._unlock_ui()
        self.plugin.mostrar_mensagem(msg, "Erro")
        QgsMessageLog.logMessage(msg, self.log_prefix, level=Qgis.MessageLevel.Warning)
        if getattr(self.plugin, "_depth_runner", None) is self:
            self.plugin._depth_runner = None

    def _unlock_ui(self):
        try:
            if hasattr(self.plugin, "pushButtonPronfundidade"):
                self.plugin.pushButtonPronfundidade.setEnabled(True)
        except Exception:
            pass  # nosec B110

class CanalDeleteButtonDelegate(QStyledItemDelegate):
    """
    Delegate que desenha um botão de deletar à ESQUERDA do texto
    e, ao clicar, exibe uma confirmação e executa a remoção.

    mode = "camada" -> tableViewCamada (remove camada do projeto)
    mode = "feicao" -> tableViewFeicao (remove feição da camada corrente)
    """
    def __init__(self, view, plugin, mode: str = "camada"):
        super().__init__(view)
        self.view = view          # tableViewCamada ou tableViewFeicao
        self.plugin = plugin      # instância de RedesDrenagem
        self.mode = mode          # "camada" ou "feicao"

    def paint(self, painter, option, index):
        # desenha normalmente (texto, seleção, etc.)
        super().paint(painter, option, index)

        if not index.isValid():
            return

        rect = option.rect
        size = 10
        # Ícone à ESQUERDA, centralizado verticalmente
        icon_rect = QRect(rect.left() + 4, rect.center().y() - size // 2, size, size)

        painter.save()
        painter.setRenderHint(QPainter.RenderHint.Antialiasing)

        # quadradinho vermelho com borda azul
        painter.setPen(QPen(QColor(0, 170, 0), 1.5))
        painter.setBrush(QBrush(QColor(255, 0, 127, 200)))
        radius = 2
        painter.drawRoundedRect(icon_rect, radius, radius)

        # "X" branco
        painter.setPen(QPen(QColor(255, 255, 255), 2))
        painter.drawLine(
            icon_rect.topLeft() + QPoint(2, 2),
            icon_rect.bottomRight() - QPoint(2, 2))
        painter.drawLine(
            icon_rect.topRight() + QPoint(-2, 2),
            icon_rect.bottomLeft() + QPoint(2, -2))

        painter.restore()

    def editorEvent(self, event, model, option, index):
        if (event.type() == QEvent.Type.MouseButtonRelease
            and event.button() == Qt.MouseButton.LeftButton
            and index.isValid()):
            rect = option.rect
            size = 10
            icon_rect = QRect(rect.left() + 4, rect.center().y() - size // 2, size, size)

            if icon_rect.contains(event.pos()):
                # Clique no ícone -> confirmar e remover
                if self.mode == "camada":
                    self._confirm_and_delete_layer(index)
                else:
                    self._confirm_and_delete_feature(index)
                return True  # evento tratado

        return super().editorEvent(event, model, option, index)

    def _confirm_and_delete_layer(self, index):
        layer_id = index.data(Qt.ItemDataRole.UserRole)
        if not layer_id:
            return

        proj = QgsProject.instance()
        layer = proj.mapLayer(layer_id)
        if layer is None:
            return

        # Conta feições (se for vetor)
        feat_count = -1
        if isinstance(layer, QgsVectorLayer):
            try:
                feat_count = layer.featureCount()
            except Exception:
                feat_count = -1

        # Se tiver feições (ou não der pra saber), confirma remoção
        # (antes você removia direto quando feat_count == 0)
        if not (isinstance(layer, QgsVectorLayer) and feat_count == 0):
            resp = QMessageBox.question(self.view, self.plugin.tr("Remover camada de canais"), self.plugin.tr("Deseja realmente remover esta camada de canais e todas as suas feições?"), QMessageBox.StandardButton.Yes | QMessageBox.StandardButton.No, QMessageBox.StandardButton.No)
            if resp != QMessageBox.StandardButton.Yes:
                return

        # Se a camada estiver em edição, resolve SALVAR/DESCARTAR antes de remover
        if isinstance(layer, QgsVectorLayer) and layer.isEditable():
            if layer.isModified():
                msg = QMessageBox(self.view)
                msg.setWindowTitle(self.plugin.tr("Parar Edição"))
                msg.setIcon(QMessageBox.Icon.Question)
                msg.setText(self.plugin.tr("Deseja salvar as alterações para a camada '{layer_name}'?").format(layer_name=layer.name()))
                msg.setStandardButtons(QMessageBox.StandardButton.Save | QMessageBox.StandardButton.Discard | QMessageBox.StandardButton.Cancel)
                msg.setDefaultButton(QMessageBox.StandardButton.Discard)

                btn_save = msg.button(QMessageBox.StandardButton.Save)
                if btn_save is not None:
                    btn_save.setEnabled(False)   # <-- Salvar fica inativo

                msg.exec()
                r = msg.standardButton(msg.clickedButton())

                if r == QMessageBox.StandardButton.Cancel:
                    return

                if r == QMessageBox.StandardButton.Discard:
                    try:
                        layer.rollBack()  # descarta e sai do modo edição
                    except Exception:
                        pass  # nosec B110
                    # segue para remover a camada
                else:
                    # "Salvar" está desativado por enquanto.
                    # Se por algum motivo cair aqui (atalho/bug), trate como cancelamento:
                    return

                if r == QMessageBox.StandardButton.Cancel:
                    return

                if r == QMessageBox.StandardButton.Save:
                    ok = False
                    try:
                        ok = layer.commitChanges()  # salva e sai do modo edição
                    except Exception:
                        ok = False

                    if not ok:
                        QMessageBox.critical(self.view, self.plugin.tr("Erro"), self.plugin.tr("Falha ao salvar a camada. A remoção foi cancelada."))
                        return
                else:
                    # Discard
                    try:
                        layer.rollBack()  # descarta e sai do modo edição
                    except Exception:
                        pass  # nosec B110
            else:
                # Está em edição mas sem mudanças: só sai do modo edição p/ não disparar prompt do QGIS
                try:
                    layer.commitChanges()
                except Exception:
                    try:
                        layer.rollBack()
                    except Exception:
                        pass  # nosec B110

        # Agora sim: remove do projeto (sem aparecer o 2º diálogo do QGIS)
        proj.removeMapLayer(layer_id)

        # Agora sim: remove do projeto (sem aparecer o 2º diálogo do QGIS)
        proj.removeMapLayer(layer_id)

        # Se esta era a última camada listada no tableViewCamada, remove também o grupo "CANAIS"
        try:
            QTimer.singleShot(0, self._maybe_remove_canais_group)
        except Exception:
            # fallback: tenta imediato
            self._maybe_remove_canais_group()

    def _maybe_remove_canais_group(self):
        """
        Se não restar nenhuma camada no tableViewCamada, remove também o grupo 'CANAIS'
        na árvore de camadas do QGIS.

        Obs.: usamos QTimer.singleShot(0, ...) ao chamar para garantir que os sinais de remoção
        (layerWillBeRemoved) já tenham atualizado o model/árvore.
        """
        tries = getattr(self, "_canais_cleanup_tries", 0)

        # 1) critério principal: tableViewCamada ficou vazio
        try:
            view = getattr(self.plugin, "tableViewCamada", None)
            model = getattr(self.plugin, "_camadas_model", None) or (view.model() if view is not None else None)
            if model is not None and model.rowCount() > 0:
                self._canais_cleanup_tries = 0
                return
        except Exception:
            # se não conseguimos inspecionar o model, seguimos para checar o grupo direto
            pass  # nosec B110

        prj = QgsProject.instance()
        root = prj.layerTreeRoot()
        if root is None:
            return

        grp = root.findGroup(self.plugin.tr("CANAIS"))
        if grp is None:
            return

        # 2) segurança: só remove se o grupo estiver realmente vazio
        try:
            child_count = grp.childCount() if hasattr(grp, "childCount") else len(grp.children())
        except Exception:
            child_count = 0

        if child_count > 0:
            # Em alguns casos, o nó do layer ainda não saiu da árvore no mesmo tick.
            if tries < 3:
                self._canais_cleanup_tries = tries + 1
                try:
                    QTimer.singleShot(0, self._maybe_remove_canais_group)
                except Exception:
                    pass  # nosec B110
            return

        self._canais_cleanup_tries = 0

        # Remove o grupo vazio
        try:
            parent = grp.parent() or root
            parent.removeChildNode(grp)
        except Exception:
            try:
                root.removeChildNode(grp)
            except Exception:
                pass  # nosec B110

    def _confirm_and_delete_feature(self, index):
        """Feição"""
        fid = index.data(Qt.ItemDataRole.UserRole)
        if fid is None:
            return

        layer = getattr(self.plugin, "_current_canal_layer", None)
        if not isinstance(layer, QgsVectorLayer):
            return

        resp = QMessageBox.question(self.view, self.plugin.tr("Remover camada de canais"), self.plugin.tr("Deseja realmente remover esta camada de canais e todas as suas feições?"), QMessageBox.StandardButton.Yes | QMessageBox.StandardButton.No, QMessageBox.StandardButton.No)
        
        if resp != QMessageBox.StandardButton.Yes:
            return

        try:
            fid_int = int(fid)
        except Exception:
            fid_int = fid

        if not layer.isEditable():
            layer.startEditing()

        # deleteFeatures dispara o sinal featuresDeleted,
        # que já está conectado a _on_canal_features_deleted.
        layer.deleteFeatures([fid_int])
        layer.triggerRepaint()

        # Atualiza estado do botão Calcular, se existir
        if hasattr(self.plugin, "_update_pushButtonCalcular_state"):
            self.plugin._update_pushButtonCalcular_state()
        if hasattr(self.plugin, "_update_pushButtonInverter_state"):
            try:
                self.plugin._update_pushButtonInverter_state()
            except Exception:
                pass  # nosec B110

class TabelaRugosidadeCondutosDialog(QDialog):
    """
    Diálogo de Tabelas de Rugosidade.
    Pode mostrar:
      - 'condutos_circulares'
      - 'canais_revestidos'
    """
    def __init__(self, parent=None, tipo_tabela="condutos_circulares"):
        super().__init__(parent)

        # guarda o dock/manager, para acessar lineEditRugosidade
        self.parent_manager = parent
        self.tipo_tabela = tipo_tabela

        if self.tipo_tabela == "canais_revestidos":
            self.setWindowTitle(self.tr("Tabela de Rugosidade para Canais Revestidos"))

        elif self.tipo_tabela == "cursos_dragados":
            self.setWindowTitle(self.tr("Tabela de Rugosidade para Cursos D'Água Dragados ou Escavados"))

        elif self.tipo_tabela == "cursos_naturais_menores":
            self.setWindowTitle(self.tr("Tabela de Rugosidade para Cursos D'Água Naturais Menores"))

        elif self.tipo_tabela == "enchentes":
            self.setWindowTitle(self.tr("Tabela de Rugosidade para Enchentes"))

        elif self.tipo_tabela == "naturais_maiores":
            self.setWindowTitle(self.tr("Tabela de Rugosidade para Cursos D'Água Naturais Maiores"))

        else:
            self.setWindowTitle(self.tr("Tabela de Rugosidade para Condutos Circulares"))

        self.resize(700, 350)

        layout = QVBoxLayout(self)

        lbl = QLabel(self.tr("Tabela de Materiais e seus respectivos coeficientes:"))
        layout.addWidget(lbl)

        self.tableView = QTableView(self)
        layout.addWidget(self.tableView)

        btn_box = QDialogButtonBox(QDialogButtonBox.StandardButton.Close, self)
        btn_box.rejected.connect(self.reject)
        layout.addWidget(btn_box)

        # MODEL
        self.model = QStandardItemModel(self)
        self.model.setHorizontalHeaderLabels([self.tr("Descrição"), self.tr("Mínimo"), self.tr("Normal"), self.tr("Máximo")])
        self._preencher_dados_model()

        self.tableView.setModel(self.model)
        self.tableView.setSelectionBehavior(QAbstractItemView.SelectionBehavior.SelectRows)
        self.tableView.setSelectionMode(QAbstractItemView.SelectionMode.SingleSelection)
        self.tableView.horizontalHeader().setStretchLastSection(True)
        self.tableView.horizontalHeader().setDefaultAlignment(Qt.AlignmentFlag.AlignLeft)
        self.tableView.resizeColumnsToContents()

        # duplo clique na linha
        self.tableView.doubleClicked.connect(self._on_row_double_clicked)

    def _preencher_dados_model(self):
        """Preenche a tabela com os dados conforme o tipo selecionado."""

        if self.tipo_tabela == "canais_revestidos":
            # CANAIS REVESTIDOS
            dados = [
                (self.tr("Superfície em aço polido não revestido com pintura"), "0,011", "0,012", "0,014"),
                (self.tr("Superfície em aço polido revestido com pintura"), "0,012", "0,013", "0,017"),
                (self.tr("Aço corrugado"), "0,021", "0,025", "0,030"),
                (self.tr("Nata de cimento puro"), "0,010", "0,011", "0,013"),
                (self.tr("Argamassa"), "0,011", "0,013", "0,015"),
                (self.tr("Madeira aplainada, não tratada"), "0,011", "0,012", "0,015"),
                (self.tr("Madeira aplainada, tratada com creosoto"), "0,011", "0,012", "0,015"),
                (self.tr("Madeira não aplainada"), "0,011", "0,013", "0,016"),
                (self.tr("Pranchões de madeira com travessas"), "0,012", "0,015", "0,018"),
                (self.tr("Madeira revestida com papel próprio"), "0,010", "0,014", "0,017"),
                (self.tr("Concreto acabado a colher"), "0,011", "0,013", "0,015"),
                (self.tr("Concreto acabado a desempenadeira"), "0,013", "0,015", "0,017"),
                (self.tr("Concreto acabado com cascalho rolando no fundo"), "0,015", "0,017", "0,020"),
                (self.tr("Concreto sobre rocha bem escavada"), "0,017", "0,020", "0,022"),
                (self.tr("Concreto sobre rocha irregular"), "0,022", "0,027", "0,030"),
                (self.tr("Concreto com fundo acabado e laterais revestidas com pedra arrumada argamassada"), "0,015", "0,017", "0,020"),
                (self.tr("Concreto com fundo acabado e laterais com pedra argamassada, não arrumada"), "0,017", "0,020", "0,024"),
                (self.tr("Concreto com fundo e laterais de alvenaria de pedra grosseira argamassada"), "0,016", "0,020", "0,025"),
                (self.tr("Concreto com fundo e laterais de alvenaria de pedra grosseira"), "0,018", "0,020", "0,025"),
                (self.tr("Concreto com fundo acabado e laterais de pedra seca ou riprap"), "0,020", "0,030", "0,035"),
                (self.tr("Fundo em cascalho rolado e laterais de concreto moldado em formas"), "0,015", "0,018", "0,020"),
                (self.tr("Fundo em cascalho rolado e laterais com pedra argamassada não arrumada"), "0,023", "0,030", "0,033"),
                (self.tr("Fundo em cascalho rolado e laterais de pedra seca ou riprap"), "0,023", "0,030", "0,033"),
                (self.tr("Tijolos com argamassa de cimento"), "0,014", "0,015", "0,017"),
                (self.tr("Tijolos com requimados vitrificados"), "0,013", "0,014", "0,015"),
                (self.tr("Alvenaria de pedra grosseira cimentada"), "0,017", "0,025", "0,030"),
                (self.tr("Alvenaria de pedra seca"), "0,025", "0,030", "0,035"),
                (self.tr("Pedra de cantaria revestida"), "0,012", "0,013", "0,015"),
                (self.tr("Asfalto liso"), "0,010", "0,011", "0,013"),
                (self.tr("Asfalto rugoso"), "0,013", "0,015", "0,016"),
                (self.tr("Revestidos por vegetação"), "0,030", "0,050", "0,060")]

        elif self.tipo_tabela == "cursos_dragados":
            dados = [
                (self.tr("Em terra, retilíneos, uniformes, regulares e recentemente concluídos"), "0,016", "0,018", "0,020"),
                (self.tr("Em terra, retilíneos, uniformes, regulares e após sofrer influência de intempéries"), "0,018", "0,022", "0,025"),
                (self.tr("Em terra, retilíneos e uniformes com secção uniforme em cascalho regular"), "0,022", "0,027", "0,033"),
                (self.tr("Em terra, retilíneos e uniformes com grama curta e poucas ervas"), "0,022", "0,027", "0,033"),
                (self.tr("Em terra, com meandros e lentos sem vegetação"), "0,023", "0,025", "0,030"),
                (self.tr("Em terra, com meandros e lentos com grama e algumas ervas"), "0,025", "0,030", "0,033"),
                (self.tr("Em terra, com meandros e lentos com densas ervas ou plantas aquáticas no fundo do canal"), "0,030", "0,035", "0,040"),
                (self.tr("Em terra, com meandros e lentos com fundo em terra e laterais em pedra grosseira"), "0,028", "0,030", "0,035"),
                (self.tr("Em terra, com meandros e lentos com fundo rochoso e taludes com ervas"), "0,025", "0,035", "0,040"),
                (self.tr("Em terra, com meandros e lentos com pedras arredondadas no fundo e laterais regulares"), "0,030", "0,040", "0,050"),
                (self.tr("Canais dragados por máquinas ( tipo Drag-lines ) - sem vegetação"), "0,025", "0,035", "0,040"),
                (self.tr("Canais dragados por máquinas ( tipo Drag-lines ) - mata rala nos taludes"), "0,035", "0,050", "0,060"),
                (self.tr("Rochas cortadas lisas e uniformes"), "0,025", "0,035", "0,040"),
                (self.tr("Rochas cortadas pontudas e irregulares"), "0,035", "0,040", "0,050"),
                (self.tr("Canais sem manutenção, ervas e galhos sem cortar - com densas ervas, mais altas que a profundidade da água"), "0,050", "0,080", "0,120"),
                (self.tr("Canais sem manutenção, ervas e galhos sem cortar - com fundo regular, galhos e ramos nas laterais"), "0,040", "0,050", "0,080"),
                (self.tr("Canais sem manutenção, ervas e galhos sem cortar - com fundo regular, galhos e ramos nas laterais (na fase de cheias)"), "0,045", "0,070", "0,110"),
                (self.tr("Canais sem manutenção, ervas e galhos sem cortar - com densa ramagem na fase de cheias"), "0,080", "0,100", "0,140")]

        elif self.tipo_tabela == "cursos_naturais_menores":
            dados = [
                (self.tr("Cursos na planície - regulares, retilíneos, completamente cheios, sem poços ou remansos"), "0,025", "0,030", "0,033"),
                (self.tr("Cursos na planície - regulares, retilíneos, completamente cheios, sem poços ou remansos, e com pedras nas margens"), "0,030", "0,035", "0,040"),
                (self.tr("Cursos na planície - regulares, sinuosos, alguns poços e baixios (águas rasas)"), "0,033", "0,040", "0,045"),
                (self.tr("Cursos na planície - regulares, sinuosos, alguns poços e baixios (águas rasas) e com pedras e ervas nas margens"), "0,035", "0,045", "0,050"),
                (self.tr("Cursos na planície - regulares, sinuosos, alguns poços e baixios (águas rasas) e com pedras e ervas na calha"), "0,040", "0,048", "0,055"),
                (self.tr("Cursos na planície - regulares, sinuosos, alguns poços e baixios (águas rasas) e com pedras e ervas, mais vegetação nas margens"), "0,045", "0,050", "0,060"),
                (self.tr("Cursos na planície - lentos em toda extensão, cheios de ervas e poços"), "0,050", "0,070", "0,080"),
                (self.tr("Cursos na planície - completamente cheios de ervas em toda extensão, com poços ou transportando material em suspensão"), "0,075", "0,100", "0,150"),
                (self.tr("Cursos de montanhas - sem vegetação, taludes usualmente escarpados, árvores e galhos submersos nas margens"), "0,030", "0,040", "0,050"),
                (self.tr("Cursos de montanhas - sem vegetação, taludes usualmente escarpados, árvores e galhos submersos nas margens, condições mais rugosas"), "0,040", "0,050", "0,070")]

        elif self.tipo_tabela == "enchentes":
            dados = [
                (self.tr("Pastagem, sem mata mas com relva"), "0,025", "0,030", "0,035"),
                (self.tr("Pastagem, sem mata mas com relva alta"), "0,030", "0,035", "0,050"),
                (self.tr("Áreas cultivadas sem safra"), "0,030", "0,035", "0,045"),
                (self.tr("Áreas cultivadas com a safra amadurecida, plantada em fileiras"), "0,035", "0,040", "0,050"),
                (self.tr("Áreas cultivadas com a safra amadurecida, plantada em campinas"), "0,030", "0,040", "0,050"),
                (self.tr("Matagal esparso com densas ervas"), "0,035", "0,050", "0,070"),
                (self.tr("Matagal ralo com árvores"), "0,040", "0,060", "0,080"),
                (self.tr("Médio para denso matagal"), "0,070", "0,110", "0,160"),
                (self.tr("Denso arvoredo plantado em fileiras"), "0,110", "0,150", "0,200"),
                (self.tr("Terreno desmatado com tocos de árvores, sem brotos"), "0,030", "0,040", "0,050"),
                (self.tr("Terreno desmatado com tocos de árvores com denso crescimento de brotos"), "0,050", "0,060", "0,080"),
                (self.tr("Denso crescimento de floresta, com pequenas árvores, pouca vegetação — rasteira e enchente máxima superficial"), "0,080", "0,100", "0,120"),
                (self.tr("Denso crescimento de floresta, com pequenas árvores, pouca vegetação — rasteira e enchente máxima subterrânea"), "0,100", "0,120", "0,160")]

        elif self.tipo_tabela == "naturais_maiores":
            dados = [
                (self.tr("Seção regular sem matacões ou galhos (largura superficial na máxima enchente superior a 30 m)"), "0,025", "0,025", "0,060"),
                (self.tr("Irregular e seção rugosa (largura superficial na máxima enchente superior a 30 m)"), "0,035", "0,035", "0,100")]

        else:
            # CONDUTOS CIRCULARES
            dados = [
                (self.tr("Aço com junta Lockbar e soldada"), "0,010", "0,012", "0,014"),
                (self.tr("Aço rebitado e em espiral"), "0,013", "0,016", "0,017"),
                (self.tr("Ferro fundido revestido (piche ou cimentado)"), "0,010", "0,013", "0,014"),
                (self.tr("Ferro fundido não revestido"), "0,011", "0,014", "0,016"),
                (self.tr("Ferro forjado preto"), "0,012", "0,014", "0,015"),
                (self.tr("Ferro forjado galvanizado"), "0,013", "0,016", "0,017"),
                (self.tr("Metal corrugado (ARMCO) para dreno subterrâneo"), "0,017", "0,019", "0,210"),
                (self.tr("Metal corrugado (ARMCO) para dreno para água pluvial (bueiro)"), "0,021", "0,024", "0,030"),
                (self.tr("Acrílico - tipo perglass (vidro plástico)"), "0,008", "0,009", "0,010"),
                (self.tr("Latão ou bronze polido (muito liso)"), "0,009", "0,010", "0,013"),
                (self.tr("Nata de cimento puro"), "0,010", "0,011", "0,013"),
                (self.tr("Cimento argamassa"), "0,011", "0,013", "0,015"),
                (self.tr("Concreto - galerias retilíneas livres de escombros ou entulhos"), "0,010", "0,011", "0,013"),
                (self.tr("Condutos de concreto com curvas, conexões e alguns escombros ou entulhos"), "0,011", "0,013", "0,014"),
                (self.tr("Concreto acabado"), "0,011", "0,012", "0,014"),
                (self.tr("Concreto - coletor de esgotos, retilíneo, com inspeções e entradas domiciliares"), "0,013", "0,015", "0,017"),
                (self.tr("Galerias concretadas com formas metálicas"), "0,012", "0,013", "0,014"),
                (self.tr("Galerias concretadas com formas de madeira lisas"), "0,012", "0,014", "0,016"),
                (self.tr("Galerias concretadas com formas de madeira irregular"), "0,015", "0,017", "0,020"),
                (self.tr("Madeira em aduelas"), "0,010", "0,012", "0,014"),
                (self.tr("Madeira tratada e laminada"), "0,015", "0,017", "0,020"),
                (self.tr("Tubos comuns de cerâmica - água pluvial"), "0,011", "0,013", "0,017"),
                (self.tr("Cerâmica vitrificada para esgotos"), "0,011", "0,014", "0,017"),
                (self.tr("Cerâmica vitrificada para esgotos com inspeções e entrada de ramais domiciliares"), "0,013", "0,015", "0,017"),
                (self.tr("Cerâmica vitrificada para dreno com junta seca"), "0,014", "0,016", "0,018"),
                (self.tr("Galerias em alvenarias de tijolos requemados - vidrado"), "0,011", "0,013", "0,015"),
                (self.tr("Galerias em alvenaria de tijolos e revestidas com argamassa"), "0,012", "0,015", "0,017"),
                (self.tr("Coletoras de esgoto revestidos com tinta betuminosa, com película de limo com curvas e conexões"), "0,012", "0,013", "0,016"),
                (self.tr("Alvenaria argamassa com pedras irregulares"), "0,018", "0,025", "0,030"),
                (self.tr("Vidro"), "0,009", "0,010", "0,013")]

        for desc, nmin, nmed, nmax in dados:
            itens = [
                QStandardItem(desc),
                QStandardItem(nmin),
                QStandardItem(nmed),
                QStandardItem(nmax)]
            for it in itens:
                it.setEditable(False)
            self.model.appendRow(itens)

    def _on_row_double_clicked(self, index: QModelIndex):
        """
        Duplo clique -> pega o valor 'Normal' da linha, joga no
        lineEditRugosidade do diálogo principal e fecha.
        """
        if not index.isValid():
            return

        row = index.row()
        COL_NORMAL = 2  # 0=Desc; 1=Mín; 2=Normal; 3=Máx

        idx_normal = self.model.index(row, COL_NORMAL)
        valor_normal = self.model.data(idx_normal, Qt.ItemDataRole.DisplayRole)

        if not valor_normal:
            return

        if self.parent_manager is not None and hasattr(self.parent_manager, "lineEditRugosidade"):
            self.parent_manager.lineEditRugosidade.setText(str(valor_normal))

        self.accept()

class WhiteboxDrenagemRunner:
    """
    Orquestra a drenagem via WhiteboxTools em 4 etapas usando QgsProcessingAlgRunnerTask:
    1) D8 pointer
    2) D8 flow accumulation
    3) Stream definition by threshold
    4) Watershed (bacias)
    OBS: usa o provider do WhiteboxTools já instalado na Caixa de Ferramentas do QGIS.
    """
    def __init__(self, plugin, dem_layer, safe_dem_layer, threshold: float):
        self.plugin = plugin
        self.dem_layer = dem_layer
        self.safe_dem_layer = safe_dem_layer
        self.dem_name = dem_layer.name()
        self.threshold = float(threshold)

        # Workspace para arquivos temporários desta execução
        self.workspace = plugin._create_safe_workspace(prefix="ts_wbt_")
        self.original_dem_path = dem_layer.source()

        # Nomes ASCII baseados no DEM original
        base_ascii = plugin._make_ascii_filename(self.original_dem_path)
        root, ext = os.path.splitext(base_ascii)

        self.pntr_path = os.path.join(self.workspace, f"pntr_{root}.tif")
        self.accum_path = os.path.join(self.workspace, f"accum_{root}.tif")
        self.streams_path = os.path.join(self.workspace, f"streams_{root}.tif")
        self.order_path = os.path.join(self.workspace, f"order_{root}.tif")
        self.basins_path = os.path.join(self.workspace, f"basins_{root}.tif")
        self.basins_vec_path = os.path.join(self.workspace, f"basins_vec_{root}.gpkg")
        self.streams_vec_path = os.path.join(self.workspace, f"streams_vec_{root}.shp")

        # Contexto e feedback do Processing (devem viver enquanto as tasks existirem)
        self.context = QgsProcessingContext()
        self.context.setProject(QgsProject.instance())

        self.feedback_pointer = QgsProcessingFeedback()
        self.feedback_accum = QgsProcessingFeedback()
        self.feedback_streams = QgsProcessingFeedback()
        self.feedback_order = QgsProcessingFeedback()
        self.feedback_basins = QgsProcessingFeedback()
        self.feedback_basins_vec = QgsProcessingFeedback()
        self.feedback_streams_vec = QgsProcessingFeedback()

        # Referência às tasks
        self.task_pointer = None
        self.task_accum = None
        self.task_streams = None
        self.task_streams_vec = None
        self.task_order = None
        self.task_basins_vec = None
        self.task_basins = None

        # Provider WhiteboxTools (id deve ser 'wbt')
        self._provider = None

    def _start_stream_order(self):
        """Etapa 3b: Strahler stream order (gera raster de ordem)."""
        alg = self._get_algorithm("StrahlerStreamOrder", self.plugin.tr("Strahler stream order"))
        if alg is None:
            alg = self._get_algorithm(self.plugin.tr("strahler_stream_order"), self.plugin.tr("Strahler stream order"))

        if alg is None:
            QgsMessageLog.logMessage(self.plugin.tr("StrahlerStreamOrder não encontrado. Continuando sem ORDER no vetor."), "WhiteboxTools - Tempo Salvo Tools", level=Qgis.MessageLevel.Warning)
            self._start_streams_vector()
            return

        # monta params de forma robusta (nomes variam entre wrappers)
        out_name = None
        pntr_name = None
        streams_name = None

        for p in alg.parameterDefinitions():
            n = (p.name() or "").lower().replace("_", "")
            if p.isDestination() and out_name is None:
                out_name = p.name()
            elif pntr_name is None and ("d8" in n or "pntr" in n or "pointer" in n):
                pntr_name = p.name()
            elif streams_name is None and ("stream" in n):
                streams_name = p.name()

        if not out_name:
            out_name = "output"
        if not pntr_name:
            pntr_name = "d8_pntr"
        if not streams_name:
            streams_name = "streams"

        params = {
            pntr_name: self.pntr_path,
            streams_name: self.streams_path,
            out_name: self.order_path}

        self.task_order = QgsProcessingAlgRunnerTask(alg, params, self.context, self.feedback_order)
        self.task_order.executed.connect(self._on_stream_order_finished)
        QgsApplication.taskManager().addTask(self.task_order)

    def _on_stream_order_finished(self, successful: bool, results: dict):
        if not successful:
            QgsMessageLog.logMessage(self.plugin.tr("Strahler stream order falhou. results={results}. Continuando sem ORDER.").format(results=results), "WhiteboxTools - Tempo Salvo Tools", level=Qgis.MessageLevel.Warning)
            self._start_streams_vector()
            return

        # (opcional, mas útil para debug)
        self.plugin._add_whitebox_raster(path=self.order_path, name=self.plugin.tr("{dem_name} - Ordem (Strahler Whitebox)").format(dem_name=self.dem_name), dem_crs=self.dem_layer.crs(), short_code="ORD")

        self._start_streams_vector()

    def _get_provider(self):
        """
        Helpers internos
        Usa o helper do dock (RedesDrenagem) para descobrir o provider do WhiteboxTools.
        Geralmente o id é 'wbt'.
        """
        if self._provider is not None:
            return self._provider

        self._provider = self.plugin._get_wbt_provider()
        return self._provider

    def _get_algorithm(self, tool_name: str, human_name: str):
        """
        Resolve o algoritmo do WhiteboxTools a partir do nome da ferramenta.

        tool_name: nome lógico (ex.: 'D8Pointer', 'D8FlowAccumulation', 'ExtractStreams', 'Basins').
        human_name: nome amigável para mensagens de erro.
        """
        log_prefix = "WhiteboxTools - Tempo Salvo Tools"

        reg = QgsApplication.processingRegistry()
        provider = self._get_provider()  # usa o helper que consulta o provider 'wbt'

        if provider is None:
            self.plugin.mostrar_mensagem(self.plugin.tr("Provider 'WhiteboxTools' (wbt) não está disponível no Processing. Verifique se o plugin 'WhiteboxTools for Processing' está instalado e habilitado."), "Erro")
            return None

        prov_id = provider.id()  # deve ser 'wbt'

        # 1) Tentativa direta: 'wbt:ToolName'
        alg_id_direct = f"{prov_id}:{tool_name}"
        alg = reg.algorithmById(alg_id_direct)
        if alg is not None:
            QgsMessageLog.logMessage(self.plugin.tr("Algoritmo resolvido diretamente: '{alg_id_direct}'").format(alg_id_direct=alg_id_direct), log_prefix, level=Qgis.MessageLevel.Info)
            return alg

        # 2) Igualdade ignorando maiúsculas/minúsculas e underscores
        norm_tool = tool_name.lower().replace("_", "")
        exact_match = None
        partial_match = None

        for a in provider.algorithms():
            aid = a.id()  # ex.: 'wbt:D8Pointer'
            base = aid.split(":")[1] if ":" in aid else aid
            norm_base = base.lower().replace("_", "")

            if norm_base == norm_tool:
                exact_match = a
                break

            if partial_match is None and (norm_tool in norm_base or norm_base in norm_tool):
                partial_match = a

        if exact_match is not None:
            QgsMessageLog.logMessage(self.plugin.tr("Resolvendo '{tool_name}' para algoritmo '{algorithm_id}' (WhiteboxTools).").format(tool_name=tool_name, algorithm_id=exact_match.id()), log_prefix, level=Qgis.MessageLevel.Info)
            return exact_match

        if partial_match is not None:
            QgsMessageLog.logMessage(self.plugin.tr("Resolvendo '{tool_name}' (match parcial) para algoritmo '{algorithm_id}' (WhiteboxTools).").format(tool_name=tool_name, algorithm_id=partial_match.id()), log_prefix, level=Qgis.MessageLevel.Info)
            return partial_match

        # 3) Não achou nada → log com alguns ids disponíveis
        try:
            all_ids = [a.id() for a in provider.algorithms()]
            sample_ids = ", ".join(sorted(all_ids)[:20])
        except Exception:
            sample_ids = self.plugin.tr("Não foi possível obter a lista de algoritmos.")

        QgsMessageLog.logMessage(self.plugin.tr("Algoritmo '{tool_name}' não encontrado no provider '{prov_id}'. Alguns ids disponíveis: {sample_ids}").format(tool_name=tool_name, prov_id=prov_id, sample_ids=sample_ids), log_prefix, level=Qgis.MessageLevel.Warning)

        self.plugin.mostrar_mensagem(self.plugin.tr("Algoritmo WhiteboxTools '{human_name}' não encontrado (id esperado parecido com '{prov_id}:{tool_name}').").format(human_name=human_name, prov_id=prov_id, tool_name=tool_name), "Erro")
        return None

    def _build_simple_in_out_params(self, alg, input_path: str, output_path: str, tool_desc: str):
        """
        Para ferramentas simples (1 raster de entrada, 1 raster de saída),
        descobre o primeiro parâmetro NÃO-destino como entrada e o primeiro
        parâmetro destino como saída.
        """
        log_prefix = "WhiteboxTools - Tempo Salvo Tools"

        in_name = None
        out_name = None

        for p in alg.parameterDefinitions():
            # Destino → saída
            if p.isDestination():
                if out_name is None:
                    out_name = p.name()
                continue

            # Primeiro parâmetro "normal" → entrada principal
            if in_name is None:
                in_name = p.name()

        QgsMessageLog.logMessage(self.plugin.tr("{tool_desc}: parâmetro de entrada='{in_name}', saída='{out_name}'").format(tool_desc=tool_desc, in_name=in_name, out_name=out_name), log_prefix, level=Qgis.MessageLevel.Info)

        if not in_name or not out_name:
            QgsMessageLog.logMessage(self.plugin.tr("{tool_desc}: não conseguiu identificar parâmetros de entrada/saída.").format(tool_desc=tool_desc), log_prefix, level=Qgis.MessageLevel.Critical)

            self.plugin.mostrar_mensagem(self.plugin.tr("Não foi possível identificar parâmetros de entrada/saída para '{tool_desc}' no WhiteboxTools (veja o Registro de Mensagens).").format(tool_desc=tool_desc), "Erro")
            return None

        # Para os algoritmos do WhiteboxTools, é seguro passar caminhos de arquivo
        return {in_name: input_path, out_name: output_path}

    @staticmethod
    def _clean_src(path: str) -> str:
        """
        Remove parâmetros extras de fonte QGIS, como '|layername=...',
        deixando apenas o caminho físico do arquivo.
        """
        return (path or "").split("|", 1)[0].strip()

    @staticmethod
    def _norm_param_name(name: str) -> str:
        return (name or "").lower().replace("_", "").replace("-", "")

    def _log_algorithm_params(self, alg, tool_desc: str):
        """
        Loga os parâmetros reais do algoritmo Whitebox carregado no QGIS.
        Isso ajuda muito quando o provider muda nomes entre versões.
        """
        try:
            partes = []
            for p in alg.parameterDefinitions():
                try:
                    dest = " destino" if p.isDestination() else ""
                except Exception:
                    dest = ""

                try:
                    tipo = p.type()
                except Exception:
                    tipo = "?"

                partes.append(f"{p.name()} [{tipo}{dest}]")

            QgsMessageLog.logMessage(self.plugin.tr("{tool_desc}: parâmetros disponíveis = {params}").format(tool_desc=tool_desc, params=", ".join(partes)), "WhiteboxTools - Tempo Salvo Tools", level=Qgis.MessageLevel.Info)
        except Exception as e:
            QgsMessageLog.logMessage(self.plugin.tr("{tool_desc}: não foi possível listar parâmetros: {error}").format(tool_desc=tool_desc, error=str(e)), "WhiteboxTools - Tempo Salvo Tools", level=Qgis.MessageLevel.Warning)

    def _find_param(self, alg, aliases, include_dest=False):
        """
        Encontra um parâmetro por lista de nomes possíveis.
        Ex.: ['input', 'raster', 'dem'].
        """
        aliases_norm = [self._norm_param_name(a) for a in aliases]

        for p in alg.parameterDefinitions():
            try:
                if p.isDestination() and not include_dest:
                    continue
            except Exception:
                pass  # nosec B110

            n = self._norm_param_name(p.name())
            if n in aliases_norm:
                return p.name()

        # Segunda tentativa: match parcial, útil em wrappers novos
        for p in alg.parameterDefinitions():
            try:
                if p.isDestination() and not include_dest:
                    continue
            except Exception:
                pass  # nosec B110

            n = self._norm_param_name(p.name())
            if any(a in n or n in a for a in aliases_norm):
                return p.name()

        return None

    def _find_output_param(self, alg, aliases=("output", "out", "destination")):
        """
        Encontra o parâmetro de saída.
        Prioriza parâmetros destino do QGIS Processing.
        """
        aliases_norm = [self._norm_param_name(a) for a in aliases]

        for p in alg.parameterDefinitions():
            try:
                if p.isDestination():
                    return p.name()
            except Exception:
                pass  # nosec B110

        for p in alg.parameterDefinitions():
            n = self._norm_param_name(p.name())
            if n in aliases_norm:
                return p.name()

        return None

    def _has_param(self, alg, aliases):
        return self._find_param(alg, aliases, include_dest=True) is not None

    def _enum_value(self, alg, param_name: str, wanted: str, fallback=None):
        """
        Retorna o valor adequado para parâmetro enum.
        Se o parâmetro tiver options(), retorna o índice da opção.
        Se não tiver, retorna o texto.
        """
        wanted_norm = self._norm_param_name(wanted)

        for p in alg.parameterDefinitions():
            if p.name() != param_name:
                continue

            if hasattr(p, "options"):
                try:
                    options = list(p.options())
                    for i, opt in enumerate(options):
                        opt_norm = self._norm_param_name(str(opt))
                        if wanted_norm in opt_norm or opt_norm in wanted_norm:
                            return i
                except Exception:
                    pass  # nosec B110

        return fallback if fallback is not None else wanted

    def _extract_output_path_from_results(self, results: dict, preferred_path: str = "", possible_keys=("output", "out", "out_type", "OUTPUT")) -> str:
        """
        Tenta descobrir o caminho real de saída retornado pelo Processing.
        Alguns providers retornam a saída com nome diferente do parâmetro usado.
        """
        if isinstance(results, dict):
            for key in possible_keys:
                val = results.get(key)
                if isinstance(val, str) and val.strip():
                    clean = val.split("|", 1)[0].strip()
                    if clean:
                        return clean

            # Fallback: procura qualquer string que pareça arquivo raster
            for val in results.values():
                if isinstance(val, str):
                    clean = val.split("|", 1)[0].strip()
                    if clean.lower().endswith((".tif", ".tiff", ".vrt", ".sdat")):
                        return clean

        return preferred_path

    def _create_accum_from_pointer_fallback(self, pointer_path: str, output_path: str, esri_pointer: bool = False) -> bool:
        """
        Cria raster de acumulação D8 a partir do raster D8 pointer.

        Usado como fallback quando o Whitebox Workflows atualizado não gera
        o raster de acumulação, especialmente quando o parâmetro de destino
        aparece como 'out_type'.
        """
        log_prefix = "WhiteboxTools - Tempo Salvo Tools"

        try:
            pointer_path = (pointer_path or "").split("|", 1)[0].strip()
            output_path = (output_path or "").split("|", 1)[0].strip()

            if not pointer_path or not os.path.exists(pointer_path):
                QgsMessageLog.logMessage(self.plugin.tr("Fallback ACC: pointer não encontrado: {pointer_path}").format(pointer_path=pointer_path), log_prefix, level=Qgis.MessageLevel.Critical)
                return False

            ds = gdal.Open(pointer_path)
            if ds is None:
                QgsMessageLog.logMessage(self.plugin.tr("Fallback ACC: GDAL não abriu o pointer: {pointer_path}").format(pointer_path=pointer_path), log_prefix, level=Qgis.MessageLevel.Critical)
                return False

            band = ds.GetRasterBand(1)
            pntr = band.ReadAsArray().astype(np.int32)
            nodata = band.GetNoDataValue()

            nrows, ncols = pntr.shape
            total = nrows * ncols

            valid = pntr > 0
            if nodata is not None:
                valid &= pntr != int(nodata)

            # WhiteboxTools default:
            # 64 128 1
            # 32  0  2
            # 16  8  4
            #
            # ESRI:
            # 32 64 128
            # 16  0   1
            #  8  4   2
            if esri_pointer:
                dirs = {
                    1:   (0, 1),     # E
                    2:   (1, 1),     # SE
                    4:   (1, 0),     # S
                    8:   (1, -1),    # SW
                    16:  (0, -1),    # W
                    32:  (-1, -1),   # NW
                    64:  (-1, 0),    # N
                    128: (-1, 1),    # NE
                }
            else:
                dirs = {
                    1:   (-1, 1),    # NE
                    2:   (0, 1),     # E
                    4:   (1, 1),     # SE
                    8:   (1, 0),     # S
                    16:  (1, -1),    # SW
                    32:  (0, -1),    # W
                    64:  (-1, -1),   # NW
                    128: (-1, 0)}    # N
                

            dest = np.full(total, -1, dtype=np.int64)
            indeg = np.zeros(total, dtype=np.int32)

            flat_valid = valid.reshape(-1)
            rows = np.arange(total, dtype=np.int64) // ncols
            cols = np.arange(total, dtype=np.int64) % ncols
            flat_pntr = pntr.reshape(-1)

            for code, (dr, dc) in dirs.items():
                mask = flat_valid & (flat_pntr == code)

                rr = rows + dr
                cc = cols + dc

                in_bounds = (
                    mask &
                    (rr >= 0) & (rr < nrows) &
                    (cc >= 0) & (cc < ncols))

                src_idx = np.where(in_bounds)[0]
                dst_idx = (rr[src_idx] * ncols + cc[src_idx]).astype(np.int64)

                # Só aponta para célula válida
                ok_dst = flat_valid[dst_idx]
                src_idx = src_idx[ok_dst]
                dst_idx = dst_idx[ok_dst]

                dest[src_idx] = dst_idx
                np.add.at(indeg, dst_idx, 1)

            accum = np.zeros(total, dtype=np.float64)
            accum[flat_valid] = 1.0

            q = deque(np.where(flat_valid & (indeg == 0))[0].astype(np.int64).tolist())

            solved = 0
            while q:
                u = q.popleft()
                solved += 1

                v = dest[u]
                if v >= 0:
                    accum[v] += accum[u]
                    indeg[v] -= 1
                    if indeg[v] == 0:
                        q.append(v)

            remaining = int(np.sum(flat_valid & (indeg > 0)))
            if remaining > 0:
                QgsMessageLog.logMessage(self.plugin.tr("Fallback ACC: {remaining} células ficaram com dependência circular/pendente. O raster será salvo mesmo assim.").format(remaining=remaining), log_prefix, level=Qgis.MessageLevel.Warning)

            out_arr = accum.reshape((nrows, ncols)).astype(np.float32)
            out_nodata = -9999.0
            out_arr[~valid] = out_nodata

            out_dir = os.path.dirname(output_path)
            if out_dir:
                os.makedirs(out_dir, exist_ok=True)

            driver = gdal.GetDriverByName("GTiff")
            out_ds = driver.Create(
                output_path,
                ncols,
                nrows,
                1,
                gdal.GDT_Float32,
                options=["COMPRESS=LZW", "TILED=YES"])

            if out_ds is None:
                QgsMessageLog.logMessage(self.plugin.tr("Fallback ACC: não foi possível criar o raster: {output_path}").format(output_path=output_path), log_prefix, level=Qgis.MessageLevel.Critical)
                return False

            out_ds.SetGeoTransform(ds.GetGeoTransform())
            out_ds.SetProjection(ds.GetProjection())

            out_band = out_ds.GetRasterBand(1)
            out_band.WriteArray(out_arr)
            out_band.SetNoDataValue(out_nodata)
            out_band.FlushCache()

            out_ds.FlushCache()
            out_ds = None
            ds = None

            return os.path.exists(output_path)

        except Exception as e:
            QgsMessageLog.logMessage(self.plugin.tr("Fallback ACC: erro inesperado: {error}\n{traceback_info}").format(error=str(e), traceback_info=traceback.format_exc()), log_prefix, level=Qgis.MessageLevel.Critical)
            return False

    def start(self):
        """Pipeline público"""
        self.plugin.mostrar_mensagem(self.plugin.tr("Processamento de drenagem com WhiteboxTools iniciado em segundo plano "
            "(etapa 1/4: D8 pointer)..."), "Info")
        self._start_pointer()

    def _start_pointer(self):
        """Etapa 1: D8 pointer"""
        alg = self._get_algorithm("D8Pointer", "D8 pointer")
        if alg is None:
            return

        dem_path = self.safe_dem_layer.source()

        # Na interface de Processing o D8Pointer usa 'dem' (entrada) e 'output' (saída)
        QgsMessageLog.logMessage(self.plugin.tr("D8 pointer: parâmetro de entrada='{in_name}', saída='{out_name}'").format(in_name="dem", out_name="output"), "WhiteboxTools - Tempo Salvo Tools", level=Qgis.MessageLevel.Info)

        params = {"dem": dem_path, "output": self.pntr_path}

        self.task_pointer = QgsProcessingAlgRunnerTask(alg, params, self.context, self.feedback_pointer)
        self.task_pointer.executed.connect(self._on_pointer_finished)

        QgsApplication.taskManager().addTask(self.task_pointer)

    def _on_pointer_finished(self, successful: bool, results: dict):
        log_prefix = "WhiteboxTools - Tempo Salvo Tools"

        if not successful:
            QgsMessageLog.logMessage(self.plugin.tr("D8 pointer terminou com falha. results={results}").format(results=results), log_prefix, level=Qgis.MessageLevel.Critical)

            self.plugin.mostrar_mensagem(self.plugin.tr("Erro ao executar 'D8 pointer' (WhiteboxTools). Verifique o painel 'Registro de Mensagens' para detalhes."), "Erro")
            return

        # Adiciona o pointer como raster opcional
        self.plugin._add_whitebox_raster(path=self.pntr_path, name=self.plugin.tr("{dem_name} - D8 pointer (Whitebox)").format(dem_name=self.dem_name), dem_crs=self.dem_layer.crs(), short_code="PNTR")

        self.plugin.mostrar_mensagem(self.plugin.tr("Executando WhiteboxTools: D8 flow accumulation..."), "Info")
        self._start_accum()

    def _start_accum(self):
        """Etapa 2: D8 flow accumulation"""
        alg = self._get_algorithm("D8FlowAccumulation", "D8 flow accumulation")
        if alg is None:
            alg = self._get_algorithm("d8_flow_accum", "D8 flow accumulation")

        if alg is None:
            return

        log_prefix = "WhiteboxTools - Tempo Salvo Tools"
        self._log_algorithm_params(alg, "D8 flow accumulation")

        dem_path = self._clean_src(self.safe_dem_layer.source())

        in_name = self._find_param(alg, ["raster", "input", "dem"])
        out_name = self._find_output_param(alg)

        if not in_name or not out_name:
            QgsMessageLog.logMessage(self.plugin.tr("D8 flow accumulation: não encontrou parâmetros de entrada/saída. in_name={in_name}, out_name={out_name}").format(in_name=in_name, out_name=out_name), log_prefix, level=Qgis.MessageLevel.Critical)

            self.plugin.mostrar_mensagem(self.plugin.tr("Não foi possível identificar os parâmetros do D8 flow accumulation no WhiteboxTools atualizado. Veja o Registro de Mensagens."), "Erro")
            return

        params = {
            in_name: dem_path,
            out_name: self.accum_path}

        # Muito importante:
        # Para o threshold do ExtractStreams funcionar como número de células,
        # a acumulação deve sair em 'cells'.
        out_type_name = self._find_param(alg, ["out_type", "outtype", "output_type", "outputtype"])
        if out_type_name:
            params[out_type_name] = self._enum_value(alg, out_type_name, "cells", fallback="cells")

        log_name = self._find_param(alg, ["log_transform", "logtransform", "log"])
        if log_name:
            params[log_name] = False

        clip_name = self._find_param(alg, ["clip"])
        if clip_name:
            params[clip_name] = False

        input_is_pointer_name = self._find_param(alg, ["input_is_pointer", "inputispointer", "pntr", "pointer"])
        if input_is_pointer_name:
            params[input_is_pointer_name] = False

        esri_name = self._find_param(alg, ["esri_pntr", "esri_pointer", "esripntr", "esripointer"])
        if esri_name:
            params[esri_name] = False

        QgsMessageLog.logMessage(self.plugin.tr("D8 flow accumulation: usando parâmetros={params}").format(params=params), log_prefix, level=Qgis.MessageLevel.Info)

        self.task_accum = QgsProcessingAlgRunnerTask(
            alg,
            params,
            self.context,
            self.feedback_accum)
        self.task_accum.executed.connect(self._on_accum_finished)

        QgsApplication.taskManager().addTask(self.task_accum)

    def _on_accum_finished(self, successful: bool, results: dict):
        log_prefix = "WhiteboxTools - Tempo Salvo Tools"

        QgsMessageLog.logMessage(self.plugin.tr("D8 flow accumulation finalizou. successful={successful}, results={results}").format(successful=successful, results=results), log_prefix, level=Qgis.MessageLevel.Info)

        # Tenta descobrir se o Processing retornou outro caminho de saída
        if isinstance(results, dict):
            for key in ("output", "out", "out_type", "OUTPUT"):
                val = results.get(key)
                if isinstance(val, str) and val.strip():
                    candidate = val.split("|", 1)[0].strip()
                    if os.path.exists(candidate):
                        self.accum_path = candidate
                        break

        # Se o Whitebox disse que executou, mas não criou o raster, NÃO pode seguir direto
        if not os.path.exists(self.accum_path):
            QgsMessageLog.logMessage(self.plugin.tr("D8 flow accumulation não gerou o raster esperado: {accum_path}").format(accum_path=self.accum_path), log_prefix, level=Qgis.MessageLevel.Warning)

            # Tenta fallback interno, se você já adicionou a função
            if hasattr(self, "_create_accum_from_pointer_fallback"):
                QgsMessageLog.logMessage(self.plugin.tr("Tentando gerar ACC pelo fallback interno a partir do D8 pointer..."), log_prefix, level=Qgis.MessageLevel.Info)

                ok = self._create_accum_from_pointer_fallback(
                    pointer_path=self.pntr_path,
                    output_path=self.accum_path,
                    esri_pointer=False)

                if not ok or not os.path.exists(self.accum_path):
                    QgsMessageLog.logMessage(self.plugin.tr("Fallback interno também não gerou o ACC: {accum_path}").format(accum_path=self.accum_path), log_prefix, level=Qgis.MessageLevel.Critical)

                    self.plugin.mostrar_mensagem(self.plugin.tr("Erro ao gerar a acumulação D8. O WhiteboxTools não criou o raster ACC e o fallback interno também falhou."), "Erro")
                    return
            else:
                self.plugin.mostrar_mensagem(self.plugin.tr("Erro ao gerar a acumulação D8. O WhiteboxTools não criou o raster ACC."), "Erro")
                return

        # Só adiciona e continua se o ACC realmente existir
        self.plugin._add_whitebox_raster(
            path=self.accum_path,
            name=self.plugin.tr("{dem_name} - Acumulação (Whitebox)").format(dem_name=self.dem_name),
            dem_crs=self.dem_layer.crs(),
            short_code="ACC")

        self.plugin.mostrar_mensagem(self.plugin.tr("Executando WhiteboxTools: Stream definition by threshold."), "Info")
        self._start_streams()

    def _start_streams(self):
        """Etapa 3: Stream definition by threshold"""
        alg = self._get_algorithm("ExtractStreams", "Extract streams")
        if alg is None:
            alg = self._get_algorithm("extract_streams", "Extract streams")

        if alg is None:
            return

        log_prefix = "WhiteboxTools - Tempo Salvo Tools"
        self._log_algorithm_params(alg, "Extract streams")

        flow_name = self._find_param(alg, [
            "flow_accumulation",
            "flow_accum",
            "flowaccum",
            "input",
            "raster"])

        threshold_name = self._find_param(alg, ["threshold"])
        out_name = self._find_output_param(alg)

        if not flow_name or not threshold_name or not out_name:
            QgsMessageLog.logMessage(self.plugin.tr("Extract streams: não encontrou parâmetros necessários. flow={flow_name}, threshold={threshold_name}, output={out_name}").format(flow_name=flow_name, threshold_name=threshold_name, out_name=out_name), log_prefix, level=Qgis.MessageLevel.Critical)

            self.plugin.mostrar_mensagem(self.plugin.tr("Não foi possível identificar os parâmetros do Extract streams no WhiteboxTools atualizado. Veja o Registro de Mensagens."), "Erro")
            return

        params = {
            flow_name: self.accum_path,
            threshold_name: self.threshold,
            out_name: self.streams_path}

        zero_name = self._find_param(alg, ["zero_background", "zerobackground"])
        if zero_name:
            params[zero_name] = False

        QgsMessageLog.logMessage(self.plugin.tr("Extract streams: usando parâmetros={params}").format(params=params), log_prefix, level=Qgis.MessageLevel.Info)

        self.task_streams = QgsProcessingAlgRunnerTask(
            alg,
            params,
            self.context,
            self.feedback_streams)

        self.task_streams.executed.connect(self._on_streams_finished)

        QgsApplication.taskManager().addTask(self.task_streams)

    def _start_streams_vector(self):
        """
        Etapa 3b: Raster streams -> vetor
        """
        alg = self._get_algorithm("raster_streams_to_vector", "Raster streams to vector")
        if alg is None:
            alg = self._get_algorithm("RasterStreamsToVector", "Raster streams to vector")

        if alg is None:
            return

        log_prefix = "WhiteboxTools - Tempo Salvo Tools"
        self._log_algorithm_params(alg, "Raster streams to vector")

        streams_name = self._find_param(alg, ["streams", "streams_raster", "streamsraster"])
        pntr_name = self._find_param(alg, ["d8_pointer", "d8_pntr", "d8pntr", "pointer"])
        out_name = self._find_output_param(alg)

        if not streams_name or not pntr_name or not out_name:
            QgsMessageLog.logMessage(self.plugin.tr("Raster streams to vector: não encontrou parâmetros necessários. streams={streams_name}, pntr={pntr_name}, output={out_name}").format(streams_name=streams_name, pntr_name=pntr_name, out_name=out_name), log_prefix, level=Qgis.MessageLevel.Critical)

            self.plugin.mostrar_mensagem(self.plugin.tr("Não foi possível identificar os parâmetros do Raster streams to vector no WhiteboxTools atualizado. Veja o Registro de Mensagens."), "Erro")
            return

        params = {
            streams_name: self.streams_path,
            pntr_name: self.pntr_path,
            out_name: self.streams_vec_path}

        esri_name = self._find_param(alg, ["esri_pntr", "esri_pointer", "esripntr", "esripointer"])
        if esri_name:
            params[esri_name] = False

        all_vertices_name = self._find_param(alg, ["all_vertices", "allvertices"])
        if all_vertices_name:
            params[all_vertices_name] = False

        QgsMessageLog.logMessage(self.plugin.tr("Raster streams to vector: usando parâmetros={params}").format(params=params), log_prefix, level=Qgis.MessageLevel.Info)

        self.task_streams_vec = QgsProcessingAlgRunnerTask(
            alg,
            params,
            self.context,
            self.feedback_streams_vec)

        self.task_streams_vec.executed.connect(self._on_streams_vector_finished)

        QgsApplication.taskManager().addTask(self.task_streams_vec)

    def _on_streams_vector_finished(self, successful: bool, results: dict):
        if not successful:
            self.plugin.mostrar_mensagem(self.plugin.tr("Erro ao executar 'Raster streams to vector' (WhiteboxTools)."), "Erro")
            return

        # Adiciona a rede vetorial de drenagem
        self.plugin._add_whitebox_vector(path=self.streams_vec_path, name=self.plugin.tr("{dem_name} - Rede de drenagem (vetor Whitebox)").format(dem_name=self.dem_name), dem_crs=self.dem_layer.crs(), short_code="NET")

        # Agora que o vetor de canais já foi criado e o contexto de Processing está "livre",
        self.plugin.mostrar_mensagem(self.plugin.tr("Executando WhiteboxTools: Watershed (bacias)..."), "Info")
        self._start_basins()

    def _on_streams_finished(self, successful: bool, results: dict):
        if not successful:
            self.plugin.mostrar_mensagem(self.plugin.tr("Erro ao executar 'Stream definition by threshold' (WhiteboxTools)."), "Erro")
            return

        # Adiciona o raster de canais
        self.plugin._add_whitebox_raster(path=self.streams_path, name=self.plugin.tr("{dem_name} - Canais (raster Whitebox)").format(dem_name=self.dem_name), dem_crs=self.dem_layer.crs(), short_code="SRC")

        # Para não termos duas tasks de Processing mexendo com GDAL ao mesmo tempo.
        self.plugin.mostrar_mensagem(self.plugin.tr("Executando WhiteboxTools: Strahler stream order (ordem de canais)..."), "Info")
        self._start_stream_order()

    def _start_basins(self):
        """
        Etapa 4: Watershed (bacias)
        Gera bacias pelo WhiteboxTools, escolhendo entre:
        - Basins (bacias simples a partir do D8 pointer), ou
        - Subbasins (sub-bacias dependentes da rede de canais / THRESHOLD).
        """
        log_prefix = "WhiteboxTools - Tempo Salvo Tools"

        # Lê a escolha feita na interface (dock)
        use_subbasins = (
            getattr(self.plugin, "radioWbtSubbasins", None)
            and self.plugin.radioWbtSubbasins.isChecked())
        use_basins_simple = (
            getattr(self.plugin, "radioWbtBasins", None)
            and self.plugin.radioWbtBasins.isChecked())

        # Default: se nada estiver marcado por algum motivo,
        # assume Subbasins (comportamento mais útil para drenagem)
        if not use_subbasins and not use_basins_simple:
            use_subbasins = True

        # Escolhe algoritmo e parâmetros conforme a opção
        if use_subbasins:
            # Sub-bacias dependentes da rede de canais (usa streams + d8_pntr)
            alg = self._get_algorithm("Subbasins", "Subbasins")
            if alg is None:
                return

            QgsMessageLog.logMessage(self.plugin.tr("Subbasins: entrada='{d8_pntr}' + '{streams}', saída='{output}'").format(d8_pntr="d8_pntr", streams="streams", output="output"), log_prefix, level=Qgis.MessageLevel.Info)

            params = {"d8_pntr": self.pntr_path, "streams": self.streams_path,  # raster de canais gerado com o THRESHOLD
                "output":  self.basins_path}

        else:
            # Bacias simples, só a partir do D8 pointer (ignora THRESHOLD)
            alg = self._get_algorithm("Basins", "Basins")
            if alg is None:
                return

            QgsMessageLog.logMessage(self.plugin.tr("Basins: entrada='{d8_pntr}', saída='{output}'").format(d8_pntr="d8_pntr", output="output"), log_prefix, level=Qgis.MessageLevel.Info)

            params = {"d8_pntr": self.pntr_path, "output":  self.basins_path}

        # Cria a task e conecta o callback
        self.task_basins = QgsProcessingAlgRunnerTask(alg, params, self.context, self.feedback_basins)
        self.task_basins.executed.connect(self._on_basins_finished)

        QgsApplication.taskManager().addTask(self.task_basins)

    def _on_basins_vec_finished(self, successful: bool, results: dict):
        """
        Callback da task 'gdal:polygonize' (vetorização das bacias).
        """
        if not successful:
            self.plugin.mostrar_mensagem(self.plugin.tr("Erro ao vetorizar bacias (gdal:polygonize)."), "Erro")
            return

        # Caminho de saída (pelo resultado ou pelo path padrão)
        vec_path = results.get("OUTPUT") or self.basins_vec_path

        # Adiciona campos de área em m² e hectares
        self._add_area_fields_to_basins_layer(vec_path)

        # Adiciona a camada vetorial de bacias ao projeto
        self.plugin._add_whitebox_vector(path=vec_path, name=self.plugin.tr("{dem_name} - Bacias (Whitebox, vetor)").format(dem_name=self.dem_name), dem_crs=self.dem_layer.crs(), short_code="BASINS_VEC")

        self.plugin.mostrar_mensagem(self.plugin.tr("Processamento de drenagem com WhiteboxTools concluído (incluindo bacias vetorizadas)."), "Sucesso")

        # libera referência no plugin (opcional)
        if getattr(self.plugin, "_whitebox_runner", None) is self:
            self.plugin._whitebox_runner = None

    def _add_area_fields_to_basins_layer(self, vec_path: str):
        """
        Abre o vetor de bacias gerado (vec_path) e adiciona
        campos area_m2 e area_ha preenchidos a partir da geometria.
        """
        log_prefix = "WhiteboxTools - Tempo Salvo Tools"

        layer = QgsVectorLayer(vec_path, "basins_tmp", "ogr")
        if not layer.isValid():
            QgsMessageLog.logMessage(self.plugin.tr("Camada de bacias inválida para cálculo de área: {vec_path}").format(vec_path=vec_path), log_prefix, level=Qgis.MessageLevel.Warning)
            return

        pr = layer.dataProvider()

        # Cria campos se ainda não existirem
        fields_to_add = []
        if layer.fields().indexFromName("area_m2") < 0:
            fields_to_add.append(QgsField("area_m2", QMetaType.Type.Double))
        if layer.fields().indexFromName("area_ha") < 0:
            fields_to_add.append(QgsField("area_ha", QMetaType.Type.Double))

        if fields_to_add:
            pr.addAttributes(fields_to_add)
            layer.updateFields()

        idx_area_m2 = layer.fields().indexFromName("area_m2")
        idx_area_ha = layer.fields().indexFromName("area_ha")

        if idx_area_m2 < 0 or idx_area_ha < 0:
            QgsMessageLog.logMessage(self.plugin.tr("Não foi possível localizar campos area_m2/area_ha após adicioná-los."), log_prefix, level=Qgis.MessageLevel.Warning)
            return

        # Usa QgsDistanceArea para garantir área em m²
        dist = QgsDistanceArea()
        dist.setSourceCrs(layer.crs(), QgsProject.instance().transformContext())
        dist.setEllipsoid(QgsProject.instance().ellipsoid())

        layer.startEditing()
        for f in layer.getFeatures():
            geom = f.geometry()
            if geom is None or geom.isEmpty():
                continue

            area_m2 = dist.measureArea(geom)
            area_ha = area_m2 / 10000.0

            layer.changeAttributeValue(f.id(), idx_area_m2, area_m2)
            layer.changeAttributeValue(f.id(), idx_area_ha, area_ha)
        layer.commitChanges()

    def _on_basins_finished(self, successful: bool, results: dict):
        if not successful:
            self.plugin.mostrar_mensagem(self.plugin.tr("Erro ao executar 'Watershed' (WhiteboxTools)."), "Erro")
            return

        # Adiciona o raster de bacias
        self.plugin._add_whitebox_raster(path=self.basins_path, name=self.plugin.tr("{dem_name} - Bacias (Whitebox)").format(dem_name=self.dem_name), dem_crs=self.dem_layer.crs(), short_code="BASINS")

        # Agora dispara a vetorização (raster -> vetor)
        self.plugin.mostrar_mensagem(self.plugin.tr("Vetorizar bacias (gdal:polygonize)..."), "Info")
        self._start_basins_vector()

    def _start_basins_vector(self):
        """
        Vetoriza o raster de bacias (self.basins_path) usando
        o algoritmo 'gdal:polygonize' (raster → vetor).
        """
        log_prefix = "WhiteboxTools - Tempo Salvo Tools"

        # Garante que o raster de bacias existe
        if not os.path.exists(self.basins_path):
            QgsMessageLog.logMessage(self.plugin.tr("Raster de bacias não encontrado para vetorizar: {basins_path}").format(basins_path=self.basins_path), log_prefix, level=Qgis.MessageLevel.Warning)

            self.plugin.mostrar_mensagem(self.plugin.tr("Raster de bacias não encontrado para vetorizar (WhiteboxTools)."), "Erro")
            return

        reg = QgsApplication.processingRegistry()
        alg = reg.algorithmById("gdal:polygonize")
        if alg is None:
            self.plugin.mostrar_mensagem(self.plugin.tr("Algoritmo 'gdal:polygonize' (Polygonize raster to vector) "
                "não foi encontrado no Processing."), "Erro")
            return

        # Parâmetros conforme o algoritmo GDAL Polygonize
        params = {
            "INPUT": self.basins_path,  # raster de bacias
            "BAND": 1,                  # primeira banda
            "FIELD": "BASIN_ID",        # nome do campo de atributo
            "EIGHT_CONNECTEDNESS": False,
            "OUTPUT": self.basins_vec_path}

        # Task para vetorizar bacias
        self.task_basins_vec = QgsProcessingAlgRunnerTask(alg, params, self.context, self.feedback_basins_vec)
        self.task_basins_vec.executed.connect(self._on_basins_vec_finished)

        QgsApplication.taskManager().addTask(self.task_basins_vec)

class TauDEMDrenagemTask(QgsTask):
    """
    Tarefa em segundo plano para processar drenagem com TauDEM:
    1) pitremove   -> FEL
    2) d8flowdir   -> P, SD8
    3) aread8      -> AD8
    4) threshold   -> SRC (raster de canais), usando máscara do DEM
    5) streamnet   -> NET (canais vetoriais) e W (bacias)
    """
    def __init__(self, plugin, dem_layer, safe_dem_layer, workspace, threshold: float):
        super().__init__(plugin.tr("Drenagem TauDEM (Tempo Salvo Tools)"), QgsTask.Flag.CanCancel)

        self.plugin = plugin
        self.dem_layer = dem_layer
        self.safe_dem_layer = safe_dem_layer
        self.workspace = workspace
        self.dem_name = dem_layer.name()
        self.threshold = float(threshold)

        original_dem_path = dem_layer.source()

        # nomes ASCII baseados no DEM original
        ascii_name = self.plugin._make_ascii_filename(original_dem_path)
        root, ext = os.path.splitext(ascii_name)

        # Saídas básicas
        self.fel_path  = os.path.join(self.workspace, f"fel_{root}.tif")
        self.p_path    = os.path.join(self.workspace, f"p_{root}.tif")
        self.sd8_path  = os.path.join(self.workspace, f"sd8_{root}.tif")
        self.ad8_path  = os.path.join(self.workspace, f"ad8_{root}.tif")

        # Saídas de canais e bacias
        self.src_path   = os.path.join(self.workspace, f"src_{root}.tif")
        self.ord_path   = os.path.join(self.workspace, f"ord_{root}.tif")
        self.tree_path  = os.path.join(self.workspace, f"tree_{root}.txt")
        self.coord_path = os.path.join(self.workspace, f"coord_{root}.txt")
        self.net_path   = os.path.join(self.workspace, f"net_{root}.shp")
        self.w_path     = os.path.join(self.workspace, f"w_{root}.tif")

        self.error_message = None

    def run(self):
        """
        Executado em thread de background.
        Não chamar GUI aqui.
        """
        log_prefix = "TauDEM - Tempo Salvo Tools"
        QgsMessageLog.logMessage(self.plugin.tr("Iniciando tarefa de drenagem TauDEM..."), log_prefix, level=Qgis.MessageLevel.Info)

        try:
            # caminho do DEM seguro (vai ser usado também como máscara)
            dem_path = self.safe_dem_layer.source()
            QgsMessageLog.logMessage(self.plugin.tr("DEM seguro usado: {dem_path}").format(dem_path=dem_path), log_prefix, level=Qgis.MessageLevel.Info)

            # 1) PitRemove
            if self.isCanceled():
                return False

            ok, out = TAUDEM_CONFIG.run_taudem_command("pitremove.exe", ["-z", dem_path, "-fel", self.fel_path], log_prefix=log_prefix)
            if not ok:
                self.error_message = self.plugin.tr("Erro na etapa PitRemove: {output}").format(output=out)
                return False

            # 2) D8FlowDir
            if self.isCanceled():
                return False

            ok, out = TAUDEM_CONFIG.run_taudem_command("d8flowdir.exe", ["-fel", self.fel_path, "-p", self.p_path, "-sd8", self.sd8_path], log_prefix=log_prefix)
            if not ok:
                self.error_message = self.plugin.tr("Erro na etapa D8 FlowDir: {output}").format(output=out)
                return False

            # 3) AreaD8
            if self.isCanceled():
                return False

            ok, out = TAUDEM_CONFIG.run_taudem_command("aread8.exe", ["-p", self.p_path, "-ad8", self.ad8_path], log_prefix=log_prefix)
            if not ok:
                self.error_message = self.plugin.tr("Erro na etapa Área de Contribuição (aread8): {output}").format(output=out)
                return False

            # 4) Threshold (Stream Definition by Threshold) com máscara do DEM
            if self.isCanceled():
                return False

            ok, out = TAUDEM_CONFIG.run_taudem_command("threshold.exe", ["-ssa", self.ad8_path, "-src", self.src_path, "-thresh", str(int(self.threshold)), "-mask", dem_path], log_prefix=log_prefix)
            if not ok:
                self.error_message = self.plugin.tr("Erro na etapa Stream Definition (threshold): {output}").format(output=out)
                return False

            # 5) StreamNet (rede de drenagem e bacias)
            if self.isCanceled():
                return False

            ok, out = TAUDEM_CONFIG.run_taudem_command("streamnet.exe", ["-fel", self.fel_path, "-p", self.p_path, "-ad8", self.ad8_path, "-src", self.src_path, "-ord", self.ord_path, "-tree", self.tree_path, "-coord", self.coord_path, "-net", self.net_path, "-w", self.w_path], log_prefix=log_prefix)
            if not ok:
                self.error_message = self.plugin.tr("Erro na etapa StreamNet (canais/bacias): {output}").format(output=out)
                return False

            return True

        except Exception as e:
            tb = traceback.format_exc()
            self.error_message = self.plugin.tr("Erro inesperado na tarefa TauDEM: {error}").format(error=str(e))
            QgsMessageLog.logMessage(tb, log_prefix, level=Qgis.MessageLevel.Critical)
            return False

    def cancel(self):
        QgsMessageLog.logMessage(self.plugin.tr("Tarefa TauDEM cancelada."), "TauDEM - Tempo Salvo Tools", level=Qgis.MessageLevel.Info)
        super().cancel()

class SagaDrenagemRunner:
    """
    Orquestra as 3 etapas SAGA em segundo plano usando QgsProcessingAlgRunnerTask:
    1) Fill sinks (Wang & Liu)
    2) Flow accumulation (one step)
    3) Channel network and drainage basins
    """
    def __init__(self, plugin, dem_layer, safe_dem_layer, minslope: float, strahler_threshold: int):
        self.plugin = plugin                    # instância de RedesDrenagem
        self.dem_layer = dem_layer
        self.safe_dem_layer = safe_dem_layer
        self.dem_name = dem_layer.name()
        self.minslope = float(minslope)
        self.strahler_threshold = int(strahler_threshold)

        # Workspace para arquivos temporários desta execução
        self.workspace = plugin._create_safe_workspace()
        self.original_dem_path = dem_layer.source()

        # Contexto e feedback do Processing
        # IMPORTANTES: precisam viver enquanto as tasks existirem
        self.context = QgsProcessingContext()
        self.context.setProject(QgsProject.instance())

        self.feedback_fill = QgsProcessingFeedback()
        self.feedback_flow = QgsProcessingFeedback()
        self.feedback_channel = QgsProcessingFeedback()

        # Referências às tasks (para não serem coletadas)
        self.task_fill = None
        self.task_flow = None
        self.task_channel = None

        # Caminho do DEM preenchido
        self.filled_safe_path = None
        self.filled_layer = None

    # API pública
    def start(self):
        self.plugin.mostrar_mensagem(self.plugin.tr("Processamento de drenagem com SAGA iniciado em segundo plano (etapa 1/3: preenchimento de depressões)..."), "Info")
        self._start_fill()

    # Etapa 1: Fill Sinks
    def _start_fill(self):
        filled_safe_name = self.plugin._make_ascii_filename(
            self.original_dem_path,
            prefix="dem_filled")
        self.filled_safe_path = os.path.join(self.workspace, filled_safe_name)

        params_fill = {
            "ELEV": self.safe_dem_layer,                # DEM "seguro" (camada)
            "MINSLOPE": self.minslope,
            "FDIR": QgsProcessing.TEMPORARY_OUTPUT,
            "FILLED": self.filled_safe_path,           # caminho explícito
            "WSHED": QgsProcessing.TEMPORARY_OUTPUT}

        alg = QgsApplication.processingRegistry().algorithmById("sagang:fillsinkswangliu")
        if alg is None:
            self.plugin.mostrar_mensagem(self.plugin.tr("Algoritmo 'sagang:fillsinkswangliu' não encontrado."), "Erro")
            return

        self.task_fill = QgsProcessingAlgRunnerTask(alg, params_fill, self.context, self.feedback_fill)
        # Sinal executed: (successful: bool, results: dict)
        self.task_fill.executed.connect(self._on_fill_finished)

        QgsApplication.taskManager().addTask(self.task_fill)

    def _on_fill_finished(self, successful: bool, results: dict):
        if not successful:
            self.plugin.mostrar_mensagem(self.plugin.tr("Erro ao executar 'Fill sinks (Wang & Liu)' com SAGA."), "Erro")
            return

        # Cria camada do DEM preenchido e adiciona ao projeto
        filled_layer_name = f"{self.dem_name} - DEM preenchido"
        self.filled_layer = QgsRasterLayer(self.filled_safe_path, filled_layer_name)

        if not self.filled_layer.isValid():
            self.plugin.mostrar_mensagem(self.plugin.tr("Falha ao carregar o DEM preenchido gerado pelo SAGA."), "Erro")
            return

        # Adiciona em grupo 'SAGA - Drenagem'
        self.plugin._add_saga_raster(self.filled_layer, short_code="DEM_FILLED")

        # Próxima etapa
        self.plugin.mostrar_mensagem(self.plugin.tr("Executando SAGA: Flow accumulation (one step)..."), "Info")
        self._start_flow()

    # Etapa 2: Flow Accumulation
    def _start_flow(self):
        params_flow = {
            "DEM": self.filled_layer,                   # usa DEM preenchido
            "TCA": QgsProcessing.TEMPORARY_OUTPUT,
            "SCA": QgsProcessing.TEMPORARY_OUTPUT,
            "PREPROCESSING": 1}                         # já fizemos o fill

        alg = QgsApplication.processingRegistry().algorithmById("sagang:flowaccumulationonestep")
        if alg is None:
            self.plugin.mostrar_mensagem(self.plugin.tr("Algoritmo 'sagang:flowaccumulationonestep' não encontrado."), "Erro" )
            return

        self.task_flow = QgsProcessingAlgRunnerTask(alg, params_flow, self.context,  self.feedback_flow)
        self.task_flow.executed.connect(self._on_flow_finished)

        QgsApplication.taskManager().addTask(self.task_flow)

    def _on_flow_finished(self, successful: bool, results: dict):
        if not successful:
            self.plugin.mostrar_mensagem(self.plugin.tr("Erro ao executar 'Flow accumulation (one step)'."), "Erro")
            # Se quiser ainda assim tentar canais, poderia chamar _start_channel() aqui
            return

        tca_path = results.get("TCA")
        sca_path = results.get("SCA")

        # TCA
        if tca_path:
            tca_layer = QgsRasterLayer(tca_path, self.plugin.tr("{dem_name} - Acumulação (TCA)").format(dem_name=self.dem_name))
            if tca_layer.isValid():
                self.plugin._add_saga_raster(tca_layer, short_code="TCA")
            else:
                self.plugin.mostrar_mensagem(self.plugin.tr("Falha ao carregar o raster de acumulação (TCA)."), "Erro")

        # SCA
        if sca_path:
            sca_layer = QgsRasterLayer(sca_path, self.plugin.tr("{dem_name} - Área específica (SCA)").format(dem_name=self.dem_name))
            if sca_layer.isValid():
                self.plugin._add_saga_raster(sca_layer, short_code="SCA")
            else:
                self.plugin.mostrar_mensagem(self.plugin.tr("Falha ao carregar o raster de área específica (SCA)."), "Erro")

        # Próxima etapa
        self.plugin.mostrar_mensagem(self.plugin.tr("Executando SAGA: Channel network and drainage basins..."), "Info")
        self._start_channel()

    # Etapa 3: Channel Network
    def _start_channel(self):
        params_channel = {
            "DEM": self.filled_layer,
            "DIRECTION": QgsProcessing.TEMPORARY_OUTPUT,
            "CONNECTION": QgsProcessing.TEMPORARY_OUTPUT,
            "ORDER": QgsProcessing.TEMPORARY_OUTPUT,
            "BASIN": QgsProcessing.TEMPORARY_OUTPUT,
            "SEGMENTS": QgsProcessing.TEMPORARY_OUTPUT,
            "BASINS": QgsProcessing.TEMPORARY_OUTPUT,
            "NODES": QgsProcessing.TEMPORARY_OUTPUT,
            "THRESHOLD": self.strahler_threshold,
            "SUBBASINS": True}

        alg = QgsApplication.processingRegistry().algorithmById("sagang:channelnetworkanddrainagebasins")
        if alg is None:
            self.plugin.mostrar_mensagem(self.plugin.tr("Algoritmo 'sagang:channelnetworkanddrainagebasins' não encontrado."), "Erro")
            return

        self.task_channel = QgsProcessingAlgRunnerTask(alg, params_channel, self.context, self.feedback_channel)
        self.task_channel.executed.connect(self._on_channel_finished)

        QgsApplication.taskManager().addTask(self.task_channel)

    def _on_channel_finished(self, successful: bool, results: dict):
        if not successful:
            self.plugin.mostrar_mensagem(self.plugin.tr("Erro ao executar 'Channel network and drainage basins'."), "Erro")
            return

        log_prefix = "SAGA - Tempo Salvo Tools"

        # (opcional) ajuda a diagnosticar nomes de outputs em versões diferentes
        try:
            QgsMessageLog.logMessage(self.plugin.tr("[SAGA] Outputs: {outputs}").format(outputs=list(results.keys())), log_prefix, level=Qgis.MessageLevel.Info)
        except Exception:
            pass  # nosec B110

        seg_path = results.get("SEGMENTS")
        basins_path = results.get("BASINS")

        # >>> NOVO: raster/grid de bacias
        basin_grid_path = (
            results.get("BASIN")
            or results.get("Basin")
            or results.get("BASIN_GRID")
            or results.get("BASINRASTER"))

        # Canais (vetor)
        if seg_path:
            canais_layer = QgsVectorLayer(seg_path, self.plugin.tr("{dem_name} - Canais SAGA").format(dem_name=self.dem_name), "ogr")
            if canais_layer.isValid():
                self.plugin._add_saga_vector(canais_layer, short_code="SEGMENTS")
            else:
                self.plugin.mostrar_mensagem(self.plugin.tr("Falha ao carregar a camada de canais gerada pelo SAGA."), "Erro")

        # Bacias (raster/grid)
        if basin_grid_path:
            basin_name = self.plugin.tr("{dem_name} - Bacias (Raster) SAGA").format(dem_name=self.dem_name)

            if isinstance(basin_grid_path, QgsRasterLayer):
                basin_raster = basin_grid_path
                basin_raster.setName(basin_name)
            else:
                basin_raster = QgsRasterLayer(str(basin_grid_path), basin_name, "gdal")

            if basin_raster.isValid():
                self.plugin._add_saga_raster(basin_raster, short_code="BASIN")
            else:
                self.plugin.mostrar_mensagem(self.plugin.tr("Falha ao carregar o raster de bacias (BASIN) gerado pelo SAGA."), "Erro")

        # Bacias (polígono)
        if basins_path:
            bacias_layer = QgsVectorLayer(basins_path, self.plugin.tr("{dem_name} - Bacias SAGA").format(dem_name=self.dem_name), "ogr")
            if bacias_layer.isValid():
                self.plugin._add_saga_vector(bacias_layer, short_code="BASINS")

                # simbologia por ORDER (se existir)
                try:
                    self.plugin.aplicar_simbologia_bacias_por_order(bacias_layer)
                except Exception:
                    pass  # nosec B110
            else:
                self.plugin.mostrar_mensagem(self.plugin.tr("Falha ao carregar a camada de bacias gerada pelo SAGA."), "Erro")

        # opcional: libera referência no plugin
        if getattr(self.plugin, "_saga_runner", None) is self:
            self.plugin._saga_runner = None

class TauDEMConfig(object):
    def __init__(self):
        self.taudem_dir = None   # pasta onde estão pitremove.exe, d8flowdir.exe, etc.
        self.mpiexec = None      # caminho do mpiexec.exe
        # Número de processos MPI = nº de CPUs (ou 4 se der None)
        self.nproc = max(1, os.cpu_count() or 4)

    def _find_file_in_path(self, filename: str):
        """Procura um executável no PATH do sistema."""
        for p in os.environ.get("PATH", "").split(os.pathsep):
            cand = os.path.join(p, filename)
            if os.path.isfile(cand):
                return cand
        return None

    def _find_taudem_dir(self):
        """
        Tenta localizar a pasta do TauDEM automaticamente.
        - Usa variável de ambiente TAUDEM_DIR (se existir)
        - Testa caminhos comuns no Windows
        - Se não achar, pede para o usuário escolher a pasta (contendo pitremove.exe)
        """
        candidates = []

        # 1) variável de ambiente
        env_dir = os.environ.get("TAUDEM_DIR")
        if env_dir:
            candidates.append(env_dir)

        # 2) caminhos padrão típicos de instalação TauDEM 5.x no Windows
        candidates.extend([
            r"C:\Program Files\TauDEM\TauDEM5Exe",
            r"C:\Program Files (x86)\TauDEM\TauDEM5Exe",
            r"C:\TauDEM5Exe"])

        for c in candidates:
            if c and os.path.isdir(c) and os.path.isfile(os.path.join(c, "pitremove.exe")):
                return c

        # 3) pede pro usuário escolher a pasta
        folder = QFileDialog.getExistingDirectory(
            iface.mainWindow(),
            QCoreApplication.translate("TauDEMConfig", "Selecione a pasta onde está instalado o TauDEM (contendo pitremove.exe)"))

        if folder and os.path.isfile(os.path.join(folder, "pitremove.exe")):
            return folder

        return None

    def _find_mpiexec(self):
        """
        Tenta localizar o mpiexec.exe (Microsoft MPI)
        - Testa caminhos comuns
        - Tenta achar no PATH
        - Se não achar, pede para o usuário escolher o executável
        """
        candidates = [
            r"C:\Program Files\Microsoft MPI\Bin\mpiexec.exe",
            r"C:\Program Files (x86)\Microsoft MPI\Bin\mpiexec.exe"]

        for c in candidates:
            if os.path.isfile(c):
                return c

        from_path = self._find_file_in_path("mpiexec.exe")
        if from_path:
            return from_path

        exe_path, _ = QFileDialog.getOpenFileName(iface.mainWindow(),  QCoreApplication.translate("TauDEMConfig", "Selecione o executável mpiexec.exe"), "", QCoreApplication.translate("TauDEMConfig", "Executáveis (*.exe)"))

        if exe_path and os.path.isfile(exe_path):
            return exe_path

        return None

    def setup_taudem_config(self) -> bool:
        """
        Inicializa a configuração do TauDEM (se ainda não estiver inicializada).
        Retorna True se tudo estiver OK, False se algo estiver faltando.
        """
        # Já configurado anteriormente
        if self.taudem_dir and self.mpiexec:
            return True

        taudem_dir = self._find_taudem_dir()
        if not taudem_dir:
            QMessageBox.warning(
                iface.mainWindow(),
                QCoreApplication.translate("TauDEMConfig", "TauDEM não localizado"),
                QCoreApplication.translate("TauDEMConfig", "Não foi possível localizar a pasta do TauDEM.\n\nVerifique se o TauDEM está instalado e tente novamente."))
            return False

        mpiexec_path = self._find_mpiexec()
        if not mpiexec_path:
            QMessageBox.warning(
                iface.mainWindow(),
                QCoreApplication.translate("TauDEMConfig", "mpiexec.exe não localizado"),
                QCoreApplication.translate("TauDEMConfig", "Não foi possível localizar o mpiexec.exe (Microsoft MPI).\n\nInstale o Microsoft MPI e tente novamente."))
            return False

        self.taudem_dir = taudem_dir
        self.mpiexec = mpiexec_path

        QMessageBox.information(
            iface.mainWindow(),
            QCoreApplication.translate("TauDEMConfig", "TauDEM configurado"),
            QCoreApplication.translate(
                "TauDEMConfig",
                "TauDEM configurado com sucesso!\n\nPasta TauDEM: {taudem_dir}\nmpiexec: {mpiexec_path}\nNúcleos (processos MPI): {nproc}"
            ).format(taudem_dir=taudem_dir, mpiexec_path=mpiexec_path, nproc=self.nproc))

        return True

    def is_configured(self) -> bool:
        """Retorna True se a configuração básica já foi feita."""
        return bool(self.taudem_dir and self.mpiexec)

    def run_taudem_command(self, exe_name: str, args: list, log_prefix: str = "TauDEM - Tempo Salvo Tools"):
        """
        Executa um comando TauDEM via mpiexec (Microsoft MPI) garantindo um PATH consistente.

        - Prioriza TauDEM5Exe + MPI Bin + GDAL (gdal201.dll) + Windows System32
        - Remove qualquer referência a CHCNAV/CHC do PATH (nunca usar)
        - Passa o PATH também via `mpiexec -env PATH ...` para os ranks
        - Loga saída compacta para não "explodir" o log
        """
        if not self.is_configured():
            msg = QCoreApplication.translate("TauDEMConfig", "TauDEM não está configurado. Chame TAUDEM_CONFIG.setup_taudem_config() no thread principal antes.")
            QgsMessageLog.logMessage(msg, log_prefix, level=Qgis.MessageLevel.Critical)
            return False, msg

        taudem_dir = os.path.realpath(os.path.abspath(str(self.taudem_dir)))

        mpiexec_path = os.path.realpath(os.path.abspath(str(self.mpiexec)))

        # Impede que exe_name contenha pastas ou sequências como "../"
        exe_name = os.path.basename(str(exe_name))

        exe_path = os.path.realpath(os.path.join(taudem_dir, exe_name))

        try:
            caminho_comum = os.path.commonpath([taudem_dir, exe_path])

            executavel_dentro_taudem = (os.path.normcase(caminho_comum) == os.path.normcase(taudem_dir))

        except ValueError:
            executavel_dentro_taudem = False

        if not os.path.isfile(mpiexec_path):
            msg = QCoreApplication.translate("TauDEMConfig", "O executável mpiexec.exe não foi encontrado:\n{path}").format(path=mpiexec_path)

            QgsMessageLog.logMessage(msg, log_prefix, level=Qgis.MessageLevel.Critical)

            return False, msg

        if (not executavel_dentro_taudem
            or not os.path.isfile(exe_path)):
            msg = QCoreApplication.translate("TauDEMConfig", "{exe_name} não encontrado ou inválido na pasta TauDEM:\n"
                "{taudem_dir}").format(exe_name=exe_name, taudem_dir=taudem_dir)

            QgsMessageLog.logMessage(msg, log_prefix, level=Qgis.MessageLevel.Critical)

            return False, msg

        # args -> strings
        args = [str(a) for a in (args or [])]

        # garante diretórios das saídas (evita "No such file or directory")
        def _is_abs_windows_path(s: str) -> bool:
            return isinstance(s, str) and len(s) > 2 and s[1] == ":" and (s[2] in ("\\", "/"))

        for a in args:
            if _is_abs_windows_path(a):
                parent = os.path.dirname(a)
                if parent and not os.path.isdir(parent):
                    try:
                        os.makedirs(parent, exist_ok=True)
                    except Exception as e:
                        QgsMessageLog.logMessage(QCoreApplication.translate("TauDEMConfig", "Aviso: não foi possível criar diretório '{parent}': {error}").format(parent=parent, error=str(e)), log_prefix, level=Qgis.MessageLevel.Warning)

        # Compactador de stdout (para não lotar o log)
        def _compact_stdout(full_text: str, max_lines: int = 220) -> str:
            if not full_text:
                return ""
            lines = [ln.rstrip("\r\n") for ln in full_text.splitlines()]

            dll_counts = Counter()
            warn_counts = Counter()
            kept: list[str] = []

            i = 0
            while i < len(lines):
                ln = lines[i].strip()

                # ERROR 1: Can't load requested DLL: <path>
                m = re.search(r"Can't load requested DLL:\s*(.+)$", ln, flags=re.IGNORECASE)
                if m:
                    dll_path = m.group(1).strip().strip('"')
                    dll_counts[os.path.basename(dll_path)] += 1
                    # frequentemente vem seguido de "127: ..."
                    if i + 1 < len(lines) and lines[i + 1].strip().startswith("127:"):
                        i += 2
                    else:
                        i += 1
                    continue

                # Warning 1: Cannot find xxx.csv
                if ln.lower().startswith("warning") and "cannot find" in ln.lower():
                    mm = re.search(r"Cannot find\s+(.+)$", ln, flags=re.IGNORECASE)
                    key = (mm.group(1).strip() if mm else ln)
                    warn_counts[key] += 1
                    i += 1
                    continue

                kept.append(lines[i])
                i += 1

            out: list[str] = []
            if warn_counts:
                out.append(QCoreApplication.translate("TauDEMConfig", "[GDAL] Avisos compactados (arquivos não encontrados):"))
                for k, c in warn_counts.most_common(12):
                    out.append(f"  - {k}  (x{c})")
                if len(warn_counts) > 12:
                    out.append(f"  - ... (+{len(warn_counts) - 12} tipos)")
                out.append("")

            if dll_counts:
                out.append(QCoreApplication.translate("TauDEMConfig", "[GDAL] Plugins que falharam ao carregar (compactado):"))
                for k, c in dll_counts.most_common(12):
                    out.append(f"  - {k}  (x{c})")
                if len(dll_counts) > 12:
                    out.append(f"  - ... (+{len(dll_counts) - 12} DLLs)")
                out.append("")

            out.extend(kept)

            if len(out) > max_lines:
                head = out[:140]
                tail = out[-60:]
                mid_omit = len(out) - (len(head) + len(tail))
                out = head + [QCoreApplication.translate("TauDEMConfig", "... ({mid_omit} linhas omitidas) ...").format(mid_omit=mid_omit)] + tail

            return "\n".join(out)

        # ENV robusto e SEM CHCNAV
        env = os.environ.copy()

        # remove variáveis do QGIS que geram spam de plugins/dados
        for k in ("GDAL_DRIVER_PATH", "GDAL_DATA", "PROJ_LIB", "PROJ_DATA"):
            env.pop(k, None)

        systemroot = env.get("SystemRoot") or r"C:\Windows"
        sys_paths = [
            os.path.join(systemroot, "System32"),
            systemroot,
            os.path.join(systemroot, "System32", "Wbem"),
            os.path.join(systemroot, "System32", "WindowsPowerShell", "v1.0")]

        mpi_bin = os.path.dirname(mpiexec_path)
        taudem_bin = taudem_dir

        # GDAL fixo (e nunca CHCNAV)
        gdal_dir = r"C:\Program Files\GDAL"
        if not os.path.isfile(os.path.join(gdal_dir, "gdal201.dll")):
            gdal_dir = ""

        def _split_paths(p: str):
            return [x for x in (p or "").split(os.pathsep) if x]

        def _uniq_keep_order(paths):
            seen = set()
            out = []
            for p in paths:
                p = (p or "").strip()
                if not p:
                    continue
                key = p.lower()

                # NUNCA usar CHCNAV/CHC
                if ("chcnav" in key) or ("chc geomatics office" in key) or ("chc" in key and "geomatics" in key):
                    continue

                if key not in seen:
                    seen.add(key)
                    out.append(p)
            return out

        # monta PATH prioritário
        base = _uniq_keep_order(
            [taudem_bin, mpi_bin] +
            ([gdal_dir] if gdal_dir else []) +
            sys_paths +
            _split_paths(env.get("PATH", "")))
        env["PATH"] = os.pathsep.join(base)

        # Comando: força PATH nos ranks
        cmd = [mpiexec_path, "-n", str(self.nproc), "-env", "PATH", env["PATH"], "-wdir", taudem_dir, exe_path] + args

        QgsMessageLog.logMessage(QCoreApplication.translate("TauDEMConfig", "Executando TauDEM:"), log_prefix, level=Qgis.MessageLevel.Info)
        try:
            QgsMessageLog.logMessage(subprocess.list2cmdline(cmd), log_prefix, level=Qgis.MessageLevel.Info)
        except Exception:
            QgsMessageLog.logMessage(" ".join(cmd), log_prefix, level=Qgis.MessageLevel.Info)

        startupinfo = None
        creationflags = 0
        if os.name == "nt":
            startupinfo = subprocess.STARTUPINFO()
            startupinfo.dwFlags |= subprocess.STARTF_USESHOWWINDOW
            creationflags = subprocess.CREATE_NO_WINDOW

        try:
            proc = subprocess.run(  # nosec B603
                cmd,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                text=True,
                encoding="utf-8",
                errors="replace",
                cwd=taudem_dir,
                env=env,
                startupinfo=startupinfo,
                creationflags=creationflags,
                shell=False,
                check=False)

        except Exception as e:
            tb = traceback.format_exc()
            QgsMessageLog.logMessage(tb, log_prefix, level=Qgis.MessageLevel.Critical)
            return False, QCoreApplication.translate("TauDEMConfig", "Erro ao executar o TauDEM: {error}").format(error=str(e))

        full_out = proc.stdout or ""
        compact_out = _compact_stdout(full_out)

        QgsMessageLog.logMessage(QCoreApplication.translate("TauDEMConfig", "\n--- Saída TauDEM (compacta) ---\n{compact_out}").format(compact_out=compact_out), log_prefix, level=Qgis.MessageLevel.Info)

        if proc.returncode != 0:
            rc = proc.returncode
            hint = ""
            if rc == 3221225781:
                hint = " (0xC0000135: DLL não encontrada)"
            msg = QCoreApplication.translate("TauDEMConfig", "TauDEM retornou código de erro {rc}{hint}.\nVerifique os caminhos, permissões e o log acima.").format(rc=rc, hint=hint)
            QgsMessageLog.logMessage(msg, log_prefix, level=Qgis.MessageLevel.Critical)
            return False, full_out

        return True, full_out
# Instância global de configuração
TAUDEM_CONFIG = TauDEMConfig()