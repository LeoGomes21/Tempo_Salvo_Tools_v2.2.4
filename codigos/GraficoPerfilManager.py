from qgis.core import QgsProject, QgsRasterLayer, QgsPointXY, QgsWkbTypes, QgsFeature, Qgis, QgsGeometry, QgsCoordinateTransform, QgsDistanceArea, QgsVectorLayer, QgsTextFormat, QgsMapRendererParallelJob, QgsMapSettings, QgsField, QgsPalLayerSettings, QgsVectorLayerSimpleLabeling, QgsMapRendererCustomPainterJob
from qgis.PyQt.QtWidgets import QDockWidget, QListWidgetItem, QColorDialog, QStyledItemDelegate, QTableWidgetItem, QToolTip, QLabel, QListView, QFileDialog, QPushButton, QGraphicsTextItem, QAbstractItemView
from qgis.gui import QgsMapToolEmitPoint, QgsRubberBand, QgsVertexMarker, QgsMapToolIdentifyFeature
from qgis.PyQt.QtCore import Qt, QRect, QPoint, QSize, QEvent, QSettings, QBuffer, QMetaType, QIODevice, QCoreApplication, QUrl
from qgis.PyQt.QtGui import QIcon, QColor, QImage, QPixmap, QPainter, QFont, QDesktopServices
from matplotlib.backends.backend_pdf import PdfPages
from pyqtgraph import SignalProxy
import matplotlib.pyplot as plt
from qgis.utils import iface
import pyqtgraph.exporters
from qgis.PyQt import uic
from qgis.PyQt import QtCore
import pyqtgraph as pg
from pyqtgraph.graphicsItems.PlotDataItem import PlotDataItem
if "paint" not in PlotDataItem.__dict__:
    def _plotdataitem_paint_noop(self, *args):
        pass
    PlotDataItem.paint = _plotdataitem_paint_noop
import numpy as np
import random
import base64
import ezdxf
import math
import os
import re

# SIP (Qt5/Qt6)
try:
    # Preferido em plugins QGIS (funciona em vários ambientes)
    from qgis.PyQt import sip  # type: ignore
except Exception:
    try:
        # Qt6 / PyQt6 (muito comum no QGISQt6)
        from PyQt6 import sip  # type: ignore
    except Exception:
        try:
            # fallback (alguns ambientes ainda expõem top-level)
            import sip  # type: ignore
        except Exception:
            # último recurso: não quebra o plugin, só desativa isdeleted
            class _SipStub:
                @staticmethod
                def isdeleted(_obj) -> bool:
                    return False
            sip = _SipStub()

FORM_CLASS, _ = uic.loadUiType(os.path.join(
    os.path.dirname(__file__), 'Grafico_perfil.ui'))

class PerfilManager(QDockWidget, FORM_CLASS):

    def __init__(self, parent=None):
        """Constructor."""
        super(PerfilManager, self).__init__(parent)
        self.setupUi(self)

        self.setWindowTitle(self.tr("Gráficos de Perfis de MDT's"))

        # Armazena a referência da interface QGIS
        self.iface = iface

        # Adiciona o dock widget à interface QGIS na parte inferior
        iface.addDockWidget(Qt.DockWidgetArea.BottomDockWidgetArea, self)

        # Ativa o antialiasing globalmente
        pg.setConfigOptions(antialias=True)

        # Inicializa o dicionário de mapeamento camada-item
        self.layer_item_map = {}

        # Preenche o listWidgetRaster com camadas Raster
        self.populate_raster_list()

        # Cria o widget do pyqtgraph e adiciona ao scrollAreaGrafico
        self.plot_widget = pg.PlotWidget(enableMenu=False)
        self.scrollAreaGrafico.setWidget(self.plot_widget)

        # Ativa o uso do OpenGL para melhorar a renderização
        self.plot_widget.useOpenGL(True)

        # Inicializa o fundo como preto e ajusta a cor dos textos
        self.plot_widget.setBackground('k')
        self.update_axis_labels(color='white')  # Define o texto dos rótulos como branco

        # Variáveis auxiliares
        self.selected_raster_layers = []  # Lista de camadas raster selecionadas
        self.selected_raster_layer = None  # Mantém uma única camada selecionada para compatibilidade

        self.line_tool = None
        self.rubber_band = None
        # Marcador para indicar a posição na linha temporária
        self.map_marker = None

        self.selected_raster_item = None

        # Inicializa as variáveis do gráfico
        self.current_x_values = []  # Lista vazia para os valores x
        self.current_y_values = []  # Lista vazia para os valores y
        self.all_profiles = []      # Perfis carregados no gráfico principal
        self.checkBoxHachura.setChecked(False)
        self.checkBoxHachura.setEnabled(False)

        # Inicializa o checkBoxLinha como selecionado
        self.checkBoxLinha.setChecked(True)

        # Inicializa a variável z_value_annotation como None
        self.z_value_annotation = None

        # Conecta os sinais aos slots
        self.connect_signals()

        self.update_checkboxes_state()

        self.configure_raster_list_dragdrop()

        self.setup_raster_tooltips()

        self.setup_second_graph() #Inicializa o segundo gráfico
        self.update_export_button_state()
        self.update_create_button_state()
        self.update_3d_button_state()
        self.update_create_line_button_state()

        # Conecta os sinais de mudança de nome das camadas
        self.connect_name_changed_signals()

        # Variável para armazenar a rubber band do segmento destacado no mapa
        self.highlighted_map_segment = None
        self.inclination_map_text = None

        self.inclination_tooltip = None  # Adicionado para o tooltip de inclinação

        # Camada/feição de linha usadas quando o perfil vem do checkBoxLinha2
        self.current_line_layer = None
        self.current_line_feature = None

        # controla se já mostramos o aviso "Desenhe ou selecione uma linha..."
        self._perfil_msg_sem_linha_mostrada = False

        # Widget de mensagem de sucesso
        self._widget_msg_sucesso = None

    def tr(self, message):
        return QtCore.QCoreApplication.translate("PerfilManager", message)

    def connect_signals(self):
        # Conecta a seleção de camada raster
        self.listWidgetRaster.itemChanged.connect(self.on_raster_layer_selected)
        self.listWidgetRaster.itemChanged.connect(self.update_checkboxes_state)  # Atualiza checkboxes

        # Monitorar mudança no sistema de coordenadas
        iface.mapCanvas().destinationCrsChanged.connect(self.update_checkboxes_state)

        # Conecta o checkbox para selecionar a linha
        self.checkBoxLinha.checkStateChanged.connect(self.on_select_line_state_changed)

        # Conecta o checkbox para selecionar uma linha de uma camada vetorial
        self.checkBoxLinha2.checkStateChanged.connect(self.on_select_line_layer_state_changed)

        # Conecta sinais do projeto para monitorar alterações de camadas
        QgsProject.instance().layerWasAdded.connect(self.on_layer_added)
        QgsProject.instance().layerWillBeRemoved.connect(self.on_layer_removed)

        # Conecta o sinal do checkBox_PB para alternar o fundo do gráfico
        self.checkBox_PB.checkStateChanged.connect(self.toggle_background_color)

        # Conecta o sinal do checkBox_Cotas para exibir o valor da cota do MDT
        self.checkBox_Cotas.checkStateChanged.connect(self.on_checkBox_Cotas_state_changed)

        # Conecta o sinal currentIndexChanged do comboBoxListaRaster ao novo método
        self.comboBoxListaRaster.currentIndexChanged.connect(self.on_combobox_layer_changed)

        #Conecte o sinal valueChanged do doubleSpinBox_espaco para que ele acione a atualização do tableWidget_Dados ao ser alterado
        self.doubleSpinBox_espaco.valueChanged.connect(self.update_table_on_spacing_change)

        # Sincronização ao Alterar o comboBoxListaRaster
        self.comboBoxListaRaster.currentIndexChanged.connect(self.update_second_graph)

        # Conecta o estado do checkBox_Inclina
        self.checkBox_Inclina.checkStateChanged.connect(self.on_checkBox_Inclina_state_changed)

        # Conecta a criação da camada de pontos
        self.pushButtonCriar.clicked.connect(self.create_points_layer_from_table)

        # Conecte os sinais para verificar o estado do botão exportar
        self.comboBoxTipo.currentIndexChanged.connect(self.update_export_button_state)
        self.comboBoxTipo_2.currentIndexChanged.connect(self.update_export_button_state)

        # Conectar o botão pushButtonExportar à função export_plot
        self.pushButtonExportar.clicked.connect(self.export_plot)

        # Conectar o botão pushButtonExportar_2 ao método de exportação
        self.pushButtonExportar_2.clicked.connect(self.export_second_graph)

        # self.spinBoxPontos.valueChanged.connect(self.on_spinBoxPontos_changed)
        self.spinBoxPontos.valueChanged.connect(lambda _: self.on_spinBoxPontos_changed(self.spinBoxPontos.value()))

        # Quando o valor muda, ajustamos o “singleStep” dinamicamente
        self.spinBoxPontos.valueChanged.connect(self.update_spinbox_pontos_step)

        # Conecta a exibição de hachura/preenchimento abaixo do perfil
        self.checkBoxHachura.checkStateChanged.connect(self.on_checkBoxHachura_state_changed)

        # Armazenar os valores padrão do doubleSpinBox_espaco
        self.default_doubleSpinBox_espaco_value = self.doubleSpinBox_espaco.value()
        self.default_doubleSpinBox_espaco_max = self.doubleSpinBox_espaco.maximum()

        # Armazenar o valor padrão do spinBoxPontos
        self.default_spinBoxPontos_value = self.spinBoxPontos.value()

        # Botões auxiliares
        self.pushButtonSelecionar.clicked.connect(self.select_all_rasters)
        self.pushButtonResetar.clicked.connect(self.reset_profile_view)

        self.pushButtonCamada3D.clicked.connect(self.create_3d_profile_lines_layer)

        self.pushButtonCriaLinha.clicked.connect(self.create_second_graph_3d_line_layer)

    def connect_name_changed_signals(self):
        """Conecta o sinal de mudança de nome de todas as camadas raster existentes no projeto QGIS."""
        for layer in QgsProject.instance().mapLayers().values():
            if isinstance(layer, QgsRasterLayer):
                layer.nameChanged.connect(self.on_layer_name_changed)

    def on_layer_added(self, layer):
        """Atualiza o listWidgetRaster ao adicionar uma nova camada raster."""
        if isinstance(layer, QgsRasterLayer):  # Verifica se é uma camada raster
            # Conecta o sinal de mudança de nome para a camada recém-adicionada
            layer.nameChanged.connect(self.on_layer_name_changed)
            # Adiciona a nova camada ao listWidgetRaster
            self.add_raster_layer_to_list(layer)

            self.update_checkboxes_state() #Atualiza o checkboxes 

    def on_layer_removed(self, layer_id):
        """Remove da lista o raster correspondente ao ID removido."""
        layer_to_remove = None
        role_layer_id = int(Qt.ItemDataRole.UserRole) + 1

        for i in range(self.listWidgetRaster.count()):
            item = self.listWidgetRaster.item(i)

            if not item:
                continue

            if item.data(role_layer_id) == layer_id:
                layer_to_remove = next((layer
                        for layer in self.selected_raster_layers
                        if layer is not None
                        and not sip.isdeleted(layer)
                        and layer.id() == layer_id),
                    None)

                self.listWidgetRaster.takeItem(i)
                break

        self.selected_raster_layers = [
            layer
            for layer in self.selected_raster_layers
            if (layer is not None
                and not sip.isdeleted(layer)
                and layer.id() != layer_id)]

        self.all_profiles = [profile
            for profile in getattr(self, "all_profiles", [])
            if (profile.get("layer") is not None
                and not sip.isdeleted(profile.get("layer"))
                and profile["layer"].id() != layer_id)]

        if self.selected_raster_layers and (
            (self.line_tool and self.line_tool.points)
            or getattr(self, "line_points", None)):
            points = (self.line_tool.points
                if self.line_tool and self.line_tool.points
                else self.line_points)

            self.extract_profile(points)
        else:
            self.plot_widget.clear()

        self.update_combobox_raster_list()
        self.update_checkboxes_state()
        self.update_raster_action_buttons_state()

    def showEvent(self, event):
        """Ativado quando o diálogo é exibido."""
        super(PerfilManager, self).showEvent(event)

        # Certifique-se de que plot_widget está inicializado
        if not hasattr(self, 'plot_widget') or not self.plot_widget:
            self.plot_widget = pg.PlotWidget(enableMenu=False)
            self.scrollAreaGrafico.setWidget(self.plot_widget)
            self.plot_widget.setBackground('k')
            self.update_axis_labels(color='white')

        # Guarda as camadas raster já selecionadas antes de recriar a lista
        selected_layer_ids = {
            layer.id()
            for layer in getattr(self, "selected_raster_layers", [])
            if layer is not None}

        # Recria a lista restaurando os checkboxes marcados
        self.populate_raster_list(selected_layer_ids=selected_layer_ids)

        # Ativa a ferramenta de linha se o checkBoxLinha estiver selecionado
        if self.checkBoxLinha.isChecked():
            self.activate_line_tool()

        # Verifica se há camadas raster selecionadas
        if not self.selected_raster_layers:
            self.checkBoxLinha.setChecked(False)
            self.checkBoxLinha.setEnabled(False)
            self.checkBoxLinha2.setChecked(False)
            self.checkBoxLinha2.setEnabled(False)
        else:
            self.checkBoxLinha.setEnabled(True)
            self.checkBoxLinha2.setEnabled(True)

            if self.checkBoxLinha.isChecked():
                self.activate_line_tool()
            elif self.checkBoxLinha2.isChecked():
                self.activate_line_layer_tool()

        self.setup_raster_tooltips()
        self.setup_comboboxes()
        self.update_export_button_state()
        self._perfil_msg_sem_linha_mostrada = False

    def populate_raster_list(self, selected_layer_ids=None):
        """Lista todas as camadas Raster no listWidgetRaster com checkbox, cor e nome."""
        if selected_layer_ids is None:
            selected_layer_ids = set()
        else:
            selected_layer_ids = set(selected_layer_ids)

        LAYER_ID_ROLE = int(Qt.ItemDataRole.UserRole) + 1

        # Evita disparos de itemChanged durante a reconstrução da lista
        self.listWidgetRaster.blockSignals(True)
        self.listWidgetRaster.clear()

        # Reconstroi a lista interna de camadas selecionadas
        self.selected_raster_layers = []

        # Cabeçalho
        self.listWidgetRaster.addItem(self._create_raster_header_item())

        initial_colors = [
            QColor(0, 0, 255),    # Azul
            QColor(255, 0, 0),    # Vermelho
            QColor(0, 255, 0),    # Verde
            QColor(255, 0, 255),  # Magenta
            QColor(0, 255, 255),  # Ciano
            QColor(255, 255, 0)]   # Amarelo

        raster_index = 0
        layers = list(QgsProject.instance().mapLayers().values())
        for layer in layers:
            if isinstance(layer, QgsRasterLayer):
                if raster_index < len(initial_colors):
                    color = initial_colors[raster_index]
                else:
                    color = QColor(
                        random.randint(0, 255), # nosec B311
                        random.randint(0, 255), # nosec B311
                        random.randint(0, 255)) # nosec B311

                pixmap = QPixmap(5, 5)
                pixmap.fill(color)
                icon = QIcon(pixmap)

                list_item = QListWidgetItem(layer.name())
                list_item.setIcon(icon)
                list_item.setFlags(list_item.flags() | Qt.ItemFlag.ItemIsUserCheckable)

                # Guarda cor e layer_id
                list_item.setData(Qt.ItemDataRole.UserRole, color)
                list_item.setData(LAYER_ID_ROLE, layer.id())

                # Restaura o estado marcado/desmarcado
                if layer.id() in selected_layer_ids:
                    list_item.setCheckState(Qt.CheckState.Checked)
                    self.selected_raster_layers.append(layer)
                else:
                    list_item.setCheckState(Qt.CheckState.Unchecked)

                self.listWidgetRaster.addItem(list_item)
                raster_index += 1

        self.listWidgetRaster.blockSignals(False)

        self.color_delegate = ColorItemDelegate(self.listWidgetRaster, self)
        self.listWidgetRaster.setItemDelegate(self.color_delegate)

        # Atualiza o estado dos checkboxes dependentes
        self.update_checkboxes_state()
        self.update_raster_action_buttons_state()

    def add_raster_layer_to_list(self, layer):
        """Adiciona uma camada raster ao listWidgetRaster."""
        LAYER_ID_ROLE = int(Qt.ItemDataRole.UserRole) + 1

        initial_colors = [
            QColor(0, 0, 255), QColor(255, 0, 0), QColor(0, 255, 0),
            QColor(255, 0, 255), QColor(0, 255, 255), QColor(255, 255, 0)]

        index = self.listWidgetRaster.count() - 1  # Ignora cabeçalho
        if index < len(initial_colors):
            color = initial_colors[index]
        else:
            # Cor aleatória usada somente para diferenciar visualmente os perfis.
            color = QColor(
                random.randint(0, 255),  # nosec B311
                random.randint(0, 255),  # nosec B311
                random.randint(0, 255))  # nosec B311

        pixmap = QPixmap(5, 5)
        pixmap.fill(color)
        icon = QIcon(pixmap)

        list_item = QListWidgetItem(layer.name())
        list_item.setIcon(icon)
        list_item.setFlags(list_item.flags() | Qt.ItemFlag.ItemIsUserCheckable)
        list_item.setCheckState(Qt.CheckState.Unchecked)
        list_item.setData(Qt.ItemDataRole.UserRole, color)
        list_item.setData(LAYER_ID_ROLE, layer.id())

        self.listWidgetRaster.addItem(list_item)
        self._ensure_raster_header_first()
        self.update_raster_action_buttons_state()

    def clear_inclination_text_on_map(self):
        """Remove o texto de inclinação desenhado no canvas."""
        if hasattr(self, 'inclination_map_text') and self.inclination_map_text:
            try:
                iface.mapCanvas().scene().removeItem(self.inclination_map_text)
            except Exception:
                pass  # nosec B110
            self.inclination_map_text = None

    def clear_inclination_text_on_graph2(self):
        """Remove o texto de inclinação desenhado no segundo gráfico."""
        if hasattr(self, 'inclination_text') and self.inclination_text:
            try:
                self.plot_widget2.scene().removeItem(self.inclination_text)
            except Exception:
                pass  # nosec B110
            self.inclination_text = None

    def show_inclination_text_on_graph2(self, text, x0, y0, x1, y1):
        """
        Desenha o texto da inclinação no segundo gráfico, realmente paralelo
        ao segmento destacado, usando coordenadas de tela.
        """
        self.clear_inclination_text_on_graph2()

        vb = self.plot_widget2.plotItem.vb

        # Converte os extremos do segmento para coordenadas de cena
        p0_scene = vb.mapViewToScene(QtCore.QPointF(x0, y0))
        p1_scene = vb.mapViewToScene(QtCore.QPointF(x1, y1))

        dx = p1_scene.x() - p0_scene.x()
        dy = p1_scene.y() - p0_scene.y()

        seg_len = math.hypot(dx, dy)
        if seg_len == 0:
            return

        midpoint_x = (p0_scene.x() + p1_scene.x()) / 2.0
        midpoint_y = (p0_scene.y() + p1_scene.y()) / 2.0

        angle_deg = math.degrees(math.atan2(dy, dx))
        if angle_deg < -90 or angle_deg > 90:
            angle_deg += 180

        angle_rad = math.radians(angle_deg)

        # Normais possíveis
        n1x, n1y = -math.sin(angle_rad),  math.cos(angle_rad)
        n2x, n2y =  math.sin(angle_rad), -math.cos(angle_rad)

        # Escolhe a normal que aponta para cima na tela
        if n1y < n2y:
            nx, ny = n1x, n1y
        else:
            nx, ny = n2x, n2y

        offset_px = 10

        text_item = QGraphicsTextItem(text)
        text_item.setDefaultTextColor(QColor(Qt.GlobalColor.white))
        text_item.setFont(QFont("Arial", 10, QFont.Weight.Bold))

        rect = text_item.boundingRect()
        text_item.setTransformOriginPoint(rect.center())

        text_item.setPos(
            midpoint_x - rect.width() / 2 + nx * offset_px,
            midpoint_y - rect.height() / 2 + ny * offset_px)
        text_item.setRotation(angle_deg)

        self.plot_widget2.scene().addItem(text_item)
        self.inclination_text = text_item

    def show_inclination_text_on_map(self, text, point1, point2):
        """
        Desenha o texto da inclinação no mapa, alinhado com o segmento destacado
        e sempre acima da linha na tela.
        """
        self.clear_inclination_text_on_map()

        canvas = iface.mapCanvas()
        map_to_pixel = canvas.mapSettings().mapToPixel()

        p1_px = map_to_pixel.transform(point1)
        p2_px = map_to_pixel.transform(point2)

        dx = p2_px.x() - p1_px.x()
        dy = p2_px.y() - p1_px.y()

        seg_len = math.hypot(dx, dy)
        if seg_len == 0:
            return

        midpoint_x = (p1_px.x() + p2_px.x()) / 2.0
        midpoint_y = (p1_px.y() + p2_px.y()) / 2.0

        angle_deg = math.degrees(math.atan2(dy, dx))
        if angle_deg < -90 or angle_deg > 90:
            angle_deg += 180

        # direção "visual" do texto
        angle_rad = math.radians(angle_deg)
        ux = math.cos(angle_rad)
        uy = math.sin(angle_rad)

        # duas normais possíveis
        n1x, n1y = -uy, ux
        n2x, n2y = uy, -ux

        # escolhe a normal que aponta para cima na tela
        if n1y < n2y:
            nx, ny = n1x, n1y
        else:
            nx, ny = n2x, n2y

        offset_px = 12

        text_item = QGraphicsTextItem(text)
        text_item.setDefaultTextColor(QColor(Qt.GlobalColor.yellow))
        text_item.setFont(QFont("Arial", 10, QFont.Weight.Bold))

        rect = text_item.boundingRect()
        text_item.setTransformOriginPoint(rect.center())

        text_item.setPos(
            midpoint_x - rect.width() / 2 + nx * offset_px,
            midpoint_y - rect.height() / 2 + ny * offset_px)
        text_item.setRotation(angle_deg)

        canvas.scene().addItem(text_item)
        self.inclination_map_text = text_item

    def closeEvent(self, event):
        """Ativado quando o diálogo é fechado."""
        super(PerfilManager, self).closeEvent(event)

        # Remove o marcador do mapa
        self.remove_map_marker()

        # Remove a linha temporária ao fechar o diálogo
        if self.rubber_band:
            self.rubber_band.reset(Qgis.GeometryType.Line)
            self.rubber_band = None

        # Reseta o checkBox_PB para desmarcado
        self.checkBox_PB.setChecked(False)

        # Reseta o checkBoxLinha para desmarcado
        self.checkBoxLinha.setChecked(False)

        # Reseta o checkBoxLinha2 para desmarcado
        self.checkBoxLinha2.setChecked(False)
        
         # Reseta o checkBox_Cotas para desmarcado
        self.checkBox_Cotas.setChecked(False)

        # Reseta o conteúdo do scrollAreaGrafico
        if hasattr(self, 'plot_widget') and self.plot_widget is not None:
            self.plot_widget.clear()  # Limpa o gráfico se estiver presente
            self.scrollAreaGrafico.takeWidget()  # Remove o widget do scroll area
            self.plot_widget = None  # Redefine para None

        # Restaura o estado inicial do scrollAreaGrafico
        self.plot_widget = pg.PlotWidget(enableMenu=False)
        self.scrollAreaGrafico.setWidget(self.plot_widget)
        self.plot_widget.setBackground('k')  # Fundo preto como padrão
        self.update_axis_labels(color='white')  # Texto branco como padrão

        # Reseta as variáveis de perfil
        self.line_points = []
        self.line_distances = []
        self.current_x_values = []
        self.current_y_values = []
        self.all_profiles = []
        self.selected_raster_layers = []

        # Esconde e redefine o tooltip_widget
        if hasattr(self, 'tooltip_widget') and self.tooltip_widget:
            self.tooltip_widget.hide()
            self.tooltip_widget = None

        # Reseta o comboBoxListaRaster
        self.comboBoxListaRaster.clear()
        self.comboBoxListaRaster.addItem(self.tr("Nenhuma camada exibida"))

        # Reseta o tableWidget_Dados e o gráfico no scrollAreaGrafico2
        self.reset_table_and_graph()
        self.clear_inclination_text_on_graph2()

        # Remover o destaque do segmento no mapa
        if self.highlighted_map_segment:
            iface.mapCanvas().scene().removeItem(self.highlighted_map_segment)
            self.highlighted_map_segment = None

        # Remove o texto de inclinação desenhado no canvas
        self.clear_inclination_text_on_map()

        # Esconde e redefine o inclination_tooltip
        if hasattr(self, 'inclination_tooltip') and self.inclination_tooltip:
            self.inclination_tooltip.hide()
            self.inclination_tooltip = None

        # Reseta os comboBoxes para o estado inicial
        self.reset_comboboxes()
 
        # evita disparar extração antes de tudo estar pronto
        self.spinBoxPontos.blockSignals(True)
        self.spinBoxPontos.setValue(self.default_spinBoxPontos_value)
        self.spinBoxPontos.blockSignals(False)
        self.update_spinbox_pontos_step(self.spinBoxPontos.value())
        self.update_3d_button_state()
        self.update_create_line_button_state()
        self.update_export_button_state()        

    def hideEvent(self, event):
        super(PerfilManager, self).hideEvent(event)
        self.clear_inclination_text_on_map()
        self.clear_inclination_text_on_graph2()

    def activate_line_tool(self):
        """Ativa a ferramenta de desenho de linha e mantém a linha visível."""
        if not self.line_tool:
            self.line_tool = LineTool(iface.mapCanvas(), self)
        iface.mapCanvas().setMapTool(self.line_tool)

    def clear_rubber_band(self):
        """Limpa a linha temporária do mapa."""
        if self.rubber_band:
            self.rubber_band.reset(Qgis.GeometryType.Line)
            self.rubber_band = None

    def deactivate_line_tool(self):
        """Desativa a ferramenta de desenho de linha sem remover a linha temporária."""
        if self.line_tool:
            iface.mapCanvas().unsetMapTool(self.line_tool)
            # Não chama self.line_tool.clear_rubber_band()
            self.line_tool = None

    def remove_map_marker(self):
        """Remove o marcador do mapa."""
        if self.map_marker:
            iface.mapCanvas().scene().removeItem(self.map_marker)
            self.map_marker = None

    def update_graph_color(self, new_color, index):
        """Atualiza a cor da linha do gráfico."""
        # Atualiza a cor armazenada no item
        item = self.listWidgetRaster.item(index.row())
        if item:
            item.setData(Qt.ItemDataRole.UserRole, new_color)
            # Verifica se este item é o que está atualmente plotado
            if item == self.selected_raster_item:
                self.plot_profile(self.current_x_values, self.current_y_values)

    def extract_profile(self, points):
        """Extrai os perfis das camadas raster selecionadas ao longo da linha."""
        if not self.selected_raster_layers:
            self.mostrar_mensagem(self.tr("Nenhuma camada raster selecionada."), "Erro")
            return

        self.all_profiles = []  # Lista para armazenar todos os perfis

        # Calcula os pontos e distâncias apenas uma vez
        distances, line_points = self.calculate_distances_and_points(points)
        self.line_points = line_points
        self.line_distances = distances

        # Ajusta o valor máximo do doubleSpinBox_espaco
        if distances:
            total_length = distances[-1]
            self.doubleSpinBox_espaco.setMaximum(total_length)
            # Opcional: ajustar o valor atual se for maior que o máximo
            if self.doubleSpinBox_espaco.value() > total_length:
                self.doubleSpinBox_espaco.setValue(total_length)

        # Para cada camada selecionada, extrai os valores de elevação
        for layer in self.selected_raster_layers:
            profiles = []  # Lista para armazenar segmentos de dados válidos
            current_distances = []
            current_values = []

            # Obtém o CRS da camada raster e configura a transformação de coordenadas
            raster_crs = layer.crs()
            map_crs = iface.mapCanvas().mapSettings().destinationCrs()
            if raster_crs != map_crs:
                transform = QgsCoordinateTransform(map_crs, raster_crs, QgsProject.instance())
                transformed_points = [transform.transform(point) for point in line_points]
            else:
                transformed_points = line_points

            for i, point in enumerate(transformed_points):
                ident = layer.dataProvider().identify(point, Qgis.RasterIdentifyFormat.Value)
                if ident.isValid():
                    results = ident.results()
                    value = list(results.values())[0]
                    if value is not None and not np.isnan(value):
                        current_distances.append(distances[i])
                        current_values.append(value)
                    else:
                        if current_distances and current_values:
                            profiles.append({
                                'distances': current_distances,
                                'values': current_values})
                            current_distances = []
                            current_values = []
                else:
                    if current_distances and current_values:
                        profiles.append({
                            'distances': current_distances,
                            'values': current_values})
                        current_distances = []
                        current_values = []

            if current_distances and current_values:
                profiles.append({
                    'distances': current_distances,
                    'values': current_values})

            # Armazena os perfis segmentados junto com a camada
            self.all_profiles.append({
                'layer': layer,
                'profiles': profiles})

        # Plota todos os perfis
        self.plot_profiles()

    def calculate_distances_and_points(self, points):
        """
        Calcula as distâncias cumulativas e gera exatamente N pontos ao longo
        de toda a polilinha, quando estiver em modo linha fixa (checkBoxLinha2).
        Caso contrário, mantém o comportamento segment-by-segment.
        """
        # Se estamos no modo “linha fixa”:
        if self.checkBoxLinha2.isChecked():
            geom = QgsGeometry.fromPolylineXY(points)
            total_length = geom.length()
            n = max(2, self.spinBoxPontos.value())

            if total_length <= 0:
                return [0], [points[0]]

            distances = [i * total_length / (n - 1) for i in range(n)]
            if math.isclose(distances[-1], total_length):
                distances[-1] = max(0.0, total_length - 1e-6)

            sampled = []
            for d in distances:
                g = geom.interpolate(d)
                if not g or g.isEmpty():
                    g = geom.interpolate(max(0.0, d - 1e-6))
                sampled.append(QgsPointXY(g.asPoint()))

            return distances, sampled

        # Modo “linha temporária” (ou fallback): mantém o loop por segmento
        distances = []
        all_pts   = []
        total     = 0.0

        for j in range(len(points) - 1):
            start, end = points[j], points[j + 1]

            seg_dist, seg_pts = self.sample_points_along_line(start, end)

            # desloca as distâncias do segmento
            seg_dist = [d + total for d in seg_dist]

            if j == 0:
                # 1º segmento: entra tudo
                distances.extend(seg_dist)
                all_pts.extend(seg_pts)
            else:
                # Demais segmentos: descarta o 1º ponto/distância
                distances.extend(seg_dist[1:])
                all_pts.extend(seg_pts[1:])

            total = distances[-1]           # último valor já é o cumulativo

        return distances, all_pts

    def on_spinBoxPontos_changed(self, value):
        """
        Refaz o gráfico do perfil ao alterar a quantidade de amostras por segmento.
        """
        # Reexecuta a extração do perfil, se já houver linha desenhada e camadas raster selecionadas
        if (self.selected_raster_layers and
            (self.line_tool and self.line_tool.points or hasattr(self, 'line_points') and self.line_points)):
            self.extract_profile(self.line_tool.points if self.line_tool and self.line_tool.points else self.line_points)

    def sample_points_along_line(self, start_point, end_point, num_samples=None):
        """
        Gera pontos ao longo de um segmento de linha.
        O número de amostras é baseado no tamanho do pixel (em metros) quando possível.
        Distâncias acumuladas em METROS (corrige projeto geográfico).
        """
        # vetor do segmento (para interpolar os pontos em coordenadas do MAPA)
        dx = end_point.x() - start_point.x()
        dy = end_point.y() - start_point.y()

        # tamanho de pixel médio do primeiro raster selecionado (em metros, na prática)
        pixel_size = None
        if getattr(self, "selected_raster_layers", None):
            rlayer = self.selected_raster_layers[0]
            px = abs(rlayer.rasterUnitsPerPixelX())
            py = abs(rlayer.rasterUnitsPerPixelY())
            pixel_size = (px + py) / 2 if px and py else None

        # medidor geodésico em METROS no CRS do MAPA
        map_crs = iface.mapCanvas().mapSettings().destinationCrs()
        dist_calc = QgsDistanceArea()
        dist_calc.setSourceCrs(map_crs, QgsProject.instance().transformContext())
        try:
            dist_calc.setEllipsoid(QgsProject.instance().ellipsoid())
        except Exception:
            pass  # nosec B110

        # comprimento do segmento em METROS
        segment_length_m = dist_calc.measureLine(QgsPointXY(start_point), QgsPointXY(end_point))

        # passo alvo em METROS (fallback 1 m)
        step_m = pixel_size if (pixel_size and pixel_size > 0) else 1.0

        # nº de amostras
        max_samples = 1000
        if hasattr(self, "spinBoxPontos"):
            spin_value = self.spinBoxPontos.value()
            if spin_value and spin_value > 1:
                max_samples = spin_value

        auto_samples = max(2, min(int(segment_length_m / step_m) + 1, max_samples))
        num_samples = max(2, auto_samples) if num_samples is None else max(2, min(num_samples, max_samples))

        # gera os pontos por interpolação linear nas coordenadas do MAPA
        x_values = [start_point.x() + dx * i / (num_samples - 1) for i in range(num_samples)]
        y_values = [start_point.y() + dy * i / (num_samples - 1) for i in range(num_samples)]
        points = [QgsPointXY(x, y) for x, y in zip(x_values, y_values)]

        # distâncias ACUMULADAS em METROS
        distances = [0.0]
        for i in range(1, len(points)):
            d = dist_calc.measureLine(points[i-1], points[i])
            distances.append(distances[-1] + d)

        return distances, points

    def toggle_background_color(self, state):
        """Alterna a cor de fundo do gráfico e a cor dos textos dos rótulos dos eixos."""
        if state == Qt.CheckState.Checked:
            self.plot_widget.setBackground('w')  # Define o fundo como branco
            self.update_axis_labels(color='black')   # Define o texto dos rótulos como preto
        else:
            self.plot_widget.setBackground('k')  # Define o fundo como preto
            self.update_axis_labels(color='white')   # Define o texto dos rótulos como branco

    def update_axis_labels(self, color):
        """Atualiza a cor dos rótulos dos eixos."""
        self.plot_widget.setLabel('left', self.tr('Elevação (m)'), color=color, size='10pt')
        self.plot_widget.setLabel('bottom', self.tr('Distância (m)'), color=color, size='10pt')

    def get_list_item_by_layer_name(self, layer_name):
        """Retorna o QListWidgetItem correspondente ao nome da camada."""
        for index in range(self.listWidgetRaster.count()):
            item = self.listWidgetRaster.item(index)
            if item.text() == layer_name:
                return item
        return None

    def get_list_item_by_layer(self, layer):
        """Retorna o QListWidgetItem correspondente à camada raster, usando layer_id."""
        if layer is None:
            return None

        try:
            layer_id = layer.id()
        except Exception:
            return None

        LAYER_ID_ROLE = int(Qt.ItemDataRole.UserRole) + 1

        for index in range(self.listWidgetRaster.count()):
            item = self.listWidgetRaster.item(index)
            if not item:
                continue
            if not (item.flags() & Qt.ItemFlag.ItemIsUserCheckable):
                continue
            if item.data(LAYER_ID_ROLE) == layer_id:
                return item

        return None

    def _get_visible_profiles(self):
        """
        Retorna apenas os perfis cujas camadas estão atualmente marcadas
        no listWidgetRaster.
        """
        visible_profiles = []

        for profile_data in getattr(self, "all_profiles", []):
            layer = profile_data.get("layer")
            item = self.get_list_item_by_layer(layer)

            if item and item.checkState() == Qt.CheckState.Checked:
                visible_profiles.append(profile_data)

        return visible_profiles

    def _has_profile_cache_for_layer(self, layer):
        """Retorna True se já houver perfil calculado em cache para a camada."""
        if layer is None:
            return False

        for profile_data in getattr(self, "all_profiles", []):
            if profile_data.get("layer") == layer:
                return True

        return False

    def on_raster_layer_selected(self, item):
        """Callback quando um item do listWidgetRaster é alterado."""
        if not (item.flags() & Qt.ItemFlag.ItemIsUserCheckable):
            return

        LAYER_ID_ROLE = int(Qt.ItemDataRole.UserRole) + 1
        layer_id = item.data(LAYER_ID_ROLE)
        layer = QgsProject.instance().mapLayer(layer_id) if layer_id else None

        # Mantém a lista sincronizada com o estado visual dos checkboxes
        self.sync_selected_raster_layers_with_list_order()
        self.selected_raster_layer = (
            self.selected_raster_layers[0] if self.selected_raster_layers else None)

        # Se não houver nenhum raster marcado, só limpa a exibição.
        # NÃO apaga self.all_profiles, para permitir que a linha reapareça ao remarcar.
        if not self.selected_raster_layers:
            if hasattr(self, 'plot_widget') and self.plot_widget is not None:
                self.plot_widget.clear()

            self.current_x_values = []
            self.current_y_values = []

            self.update_combobox_raster_list()
            self.reset_table_and_graph()
            self.remove_map_marker()
            self.hide_tooltip()

            if hasattr(self, 'vLine'):
                self.vLine.hide()
            if hasattr(self, 'hLine'):
                self.hLine.hide()
            if hasattr(self, 'coord_text'):
                self.coord_text.hide()
            if hasattr(self, 'sync_point'):
                self.sync_point.hide()
            self.update_3d_button_state()

            return

        # Se ainda não há linha pronta, apenas limpa o gráfico principal
        has_line = bool(
            (self.line_tool and getattr(self.line_tool, "points", None)) or
            (hasattr(self, 'line_points') and self.line_points))

        if not has_line:
            if hasattr(self, 'plot_widget') and self.plot_widget is not None:
                self.plot_widget.clear()
            self.update_combobox_raster_list()
            self.update_3d_button_state()
            return

        # Se a camada acabou de ser marcada e ainda não existe cache para ela,
        # recalcula o perfil com os rasters atualmente marcados
        if item.checkState() == Qt.CheckState.Checked and not self._has_profile_cache_for_layer(layer):
            pontos = (
                self.line_tool.points
                if self.line_tool and getattr(self.line_tool, "points", None)
                else self.line_points)
            self.extract_profile(pontos)
            return

        # Se já houver cache, basta replotar respeitando os checkboxes
        self.sort_all_profiles_by_list_order()
        self.plot_profiles()
        self.update_combobox_raster_list()

        if self.comboBoxListaRaster.currentText() != self.tr("Nenhuma camada exibida"):
            self.log_xyz_every_100m()
        else:
            self.reset_table_and_graph()

    def update_combobox_raster_list(self):
        """
        Atualiza o comboBoxListaRaster apenas com as camadas raster
        atualmente visíveis no gráfico.
        """
        current_text = self.comboBoxListaRaster.currentText()
        visible_profiles = self._get_visible_profiles()

        self.comboBoxListaRaster.blockSignals(True)
        self.comboBoxListaRaster.clear()

        if visible_profiles:
            for profile_data in visible_profiles:
                self.comboBoxListaRaster.addItem(profile_data['layer'].name())

            index = self.comboBoxListaRaster.findText(current_text)
            if index >= 0:
                self.comboBoxListaRaster.setCurrentIndex(index)
            else:
                self.comboBoxListaRaster.setCurrentIndex(0)
        else:
            self.comboBoxListaRaster.addItem(self.tr("Nenhuma camada exibida"))

        self.comboBoxListaRaster.blockSignals(False)

        # Como o índice foi definido com os sinais bloqueados,
        # atualiza explicitamente a tabela e o Gráfico 2.
        if visible_profiles and self.comboBoxListaRaster.currentIndex() >= 0:
            self.on_combobox_layer_changed(self.comboBoxListaRaster.currentIndex())

    def plot_profiles(self):
        """Plota apenas os perfis das camadas raster atualmente marcadas."""

        # Limpa completamente o gráfico antes de redesenhar
        self.plot_widget.clear()

        # Obtém apenas os perfis cujas camadas estão marcadas no listWidgetRaster
        visible_profiles = self._get_visible_profiles()
        has_profiles = bool(visible_profiles)

        # Habilita ou desabilita o checkbox de hachura conforme existam perfis visíveis
        self.checkBoxHachura.setEnabled(has_profiles)

        # Se não houver perfis visíveis, limpa estados auxiliares e encerra
        if not has_profiles:
            # Se a hachura estava ligada, desmarca sem disparar sinais
            if self.checkBoxHachura.isChecked():
                self.checkBoxHachura.blockSignals(True)
                self.checkBoxHachura.setChecked(False)
                self.checkBoxHachura.blockSignals(False)

            # Limpa os vetores atuais usados por outras rotinas
            self.current_x_values = []
            self.current_y_values = []

            # Atualiza interface e botão de exportação
            self.update_combobox_raster_list()
            self.update_export_button_state()
            self.update_create_button_state()
            self.update_3d_button_state()
            return

        # Melhora visual da renderização do gráfico
        pg.setConfigOptions(antialias=True)
        self.plot_widget.useOpenGL(True)

        # Acumuladores globais para definir os limites finais do gráfico
        all_x_values = []
        all_y_values = []

        # Lista intermediária com os segmentos que serão plotados
        plot_segments = []

        # Percorre apenas os perfis visíveis
        for profile_data in visible_profiles:
            layer = profile_data['layer']
            profiles = profile_data['profiles']

            # Busca o item da lista para recuperar a cor associada à camada
            item = self.get_list_item_by_layer(layer)
            if item:
                base_color = QColor(item.data(Qt.ItemDataRole.UserRole))
            else:
                # Cor padrão caso não encontre o item da lista
                base_color = QColor(0, 0, 255)

            layer_name = layer.name()

            # Define a caneta da linha do perfil
            pen = pg.mkPen(color=base_color, width=1.3)

            # Cada camada pode possuir um ou mais segmentos de perfil
            for segment in profiles:
                distances = segment['distances']
                values = segment['values']

                # Ignora segmentos vazios
                if not distances or not values:
                    continue

                # Alimenta os acumuladores globais
                all_x_values.extend(distances)
                all_y_values.extend(values)

                # Guarda os dados do segmento para plotagem posterior
                plot_segments.append({
                    'layer_name': layer_name,
                    'distances': distances,
                    'values': values,
                    'pen': pen,
                    'base_color': base_color})

        # Se não sobrou nenhum dado válido para desenhar, limpa estados e encerra
        if not all_x_values or not all_y_values:
            self.current_x_values = []
            self.current_y_values = []
            self.update_combobox_raster_list()
            self.update_export_button_state()
            return

        # Nível base usado para preenchimento quando a hachura estiver ativa
        fill_level = min(all_y_values)

        # Plota todos os segmentos visíveis
        for seg in plot_segments:
            distances = seg['distances']
            values = seg['values']
            pen = seg['pen']
            layer_name = seg['layer_name']
            base_color = seg['base_color']

            # Se a hachura estiver ativa, desenha com preenchimento semitransparente
            if self.checkBoxHachura.isChecked():
                fill_color = QColor(base_color)
                fill_color.setAlpha(127)

                self.plot_widget.plot(
                    distances,
                    values,
                    pen=pen,
                    name=layer_name,
                    fillLevel=fill_level,
                    brush=pg.mkBrush(fill_color))
            else:
                # Caso contrário, desenha apenas a linha
                self.plot_widget.plot(
                    distances,
                    values,
                    pen=pen,
                    name=layer_name)

        # Usa o primeiro perfil visível como referência para rotinas auxiliares
        first_profile = None
        for profile_data in visible_profiles:
            if profile_data['profiles']:
                first_profile = profile_data['profiles'][0]
                break

        # Atualiza os vetores atuais com base no primeiro perfil disponível
        if first_profile:
            self.current_x_values = first_profile['distances']
            self.current_y_values = first_profile['values']
        else:
            self.current_x_values = []
            self.current_y_values = []

        # Define rótulos dos eixos e grade
        self.plot_widget.setLabel('left', self.tr('Elevação (m)'))
        self.plot_widget.setLabel('bottom', self.tr('Distância (m)'))
        self.plot_widget.showGrid(x=True, y=True, alpha=0.3)

        # Fixa os ranges manualmente com base em todos os dados visíveis
        self.plot_widget.enableAutoRange(axis='y', enable=False)
        self.plot_widget.enableAutoRange(axis='x', enable=False)
        self.plot_widget.setXRange(min(all_x_values), max(all_x_values), padding=0)
        self.plot_widget.setYRange(min(all_y_values), max(all_y_values), padding=0)

        # Cria as linhas-guia vertical e horizontal para o mouse
        self.vLine = pg.InfiniteLine(
            angle=90,
            pen=pg.mkPen(color='g', style=QtCore.Qt.PenStyle.DashLine))
        self.hLine = pg.InfiniteLine(
            angle=0,
            pen=pg.mkPen(color='g', style=QtCore.Qt.PenStyle.DashLine))

        self.plot_widget.addItem(self.vLine)
        self.plot_widget.addItem(self.hLine)
        self.vLine.hide()
        self.hLine.hide()

        # Texto que exibe coordenadas/elevação junto ao cursor
        self.coord_text = pg.TextItem(anchor=(0, 1))
        self.plot_widget.addItem(self.coord_text)
        self.coord_text.hide()

        # Ponto sincronizado que acompanha a posição do mouse no gráfico
        self.sync_point = pg.PlotDataItem(
            [],
            [],
            pen=None,
            symbol='o',
            symbolPen=None,
            symbolBrush=pg.mkBrush('r'),
            symbolSize=6)
        self.plot_widget.addItem(self.sync_point)
        self.sync_point.hide()

        # Conecta o movimento do mouse para atualizar linhas-guia, texto e ponto
        self.proxy = SignalProxy(
            self.plot_widget.scene().sigMouseMoved,
            rateLimit=60,
            slot=self.mouse_moved)

        # Atualiza elementos da interface relacionados ao gráfico atual
        self.update_combobox_raster_list()
        self.update_export_button_state()
        self.update_create_button_state()
        self.update_3d_button_state()

    def create_3d_profile_lines_layer(self):
        """
        Cria uma camada de linhas 3D com base nas linhas atualmente visíveis
        no gráfico principal (scrollAreaGrafico).

        Regra:
        - cada segmento de perfil visível no gráfico gera 1 feição LineStringZ
        - o número de feições da camada = número de linhas visíveis no gráfico
        """
        visible_profiles = self._get_visible_profiles()

        if not visible_profiles:
            self.mostrar_mensagem(self.tr("Não há linhas visíveis no gráfico para criar a camada 3D."), "Erro")
            return

        if not hasattr(self, 'line_points') or not hasattr(self, 'line_distances') or not self.line_points or not self.line_distances:
            self.mostrar_mensagem(self.tr("Não há linha base válida para reconstruir a geometria 3D."), "Erro")
            return

        # CRS do projeto
        crs = iface.mapCanvas().mapSettings().destinationCrs()

        # Nome base da camada
        base_layer_name = self.tr("Perfis_3D")

        existing_layer_names = [layer.name() for layer in QgsProject.instance().mapLayers().values()]
        layer_name = base_layer_name
        counter = 1
        while layer_name in existing_layer_names:
            layer_name = f"{base_layer_name}_{counter}"
            counter += 1

        # Camada de memória 3D
        layer = QgsVectorLayer(f"LineStringZ?crs={crs.authid()}", layer_name, "memory")
        if not layer.isValid():
            self.mostrar_mensagem(self.tr("Falha ao criar a camada 3D."), "Erro")
            return

        provider = layer.dataProvider()

        # Campos de atributos
        provider.addAttributes([
            QgsField("ID", QMetaType.Type.Int),
            QgsField("Raster", QMetaType.Type.QString),
            QgsField("Segmento", QMetaType.Type.Int),
            QgsField("Pontos", QMetaType.Type.Int),
            QgsField("Compr_lin", QMetaType.Type.Double),
            QgsField("Compr_3d", QMetaType.Type.Double),
            QgsField("Z_min", QMetaType.Type.Double),
            QgsField("Z_max", QMetaType.Type.Double)])
        layer.updateFields()

        features = []
        feat_id = 1

        for profile_data in visible_profiles:
            raster_layer = profile_data.get("layer")
            raster_name = raster_layer.name() if raster_layer else "Raster"

            profiles = profile_data.get("profiles", [])
            for seg_index, segment in enumerate(profiles, start=1):
                distances = segment.get("distances", [])
                values = segment.get("values", [])

                if not distances or not values:
                    continue

                coords_3d = []

                for dist_value, z_value in zip(distances, values):
                    if z_value is None or np.isnan(z_value):
                        continue

                    point_xy = self.get_point_at_distance(dist_value)
                    if point_xy is None:
                        continue

                    coords_3d.append((point_xy.x(), point_xy.y(), float(z_value)))

                # Uma LineString precisa de ao menos 2 vértices válidos
                if len(coords_3d) < 2:
                    continue

                wkt_coords = ", ".join(f"{x} {y} {z}" for x, y, z in coords_3d)
                geom = QgsGeometry.fromWkt(f"LineStringZ ({wkt_coords})")

                if geom is None or geom.isEmpty():
                    continue

                # Comprimento linear (XY)
                compr_lin = 0.0

                # Comprimento real 3D (XYZ)
                compr_3d = 0.0

                for i in range(1, len(coords_3d)):
                    x1, y1, z1 = coords_3d[i - 1]
                    x2, y2, z2 = coords_3d[i]

                    dx = x2 - x1
                    dy = y2 - y1
                    dz = z2 - z1

                    compr_lin += math.hypot(dx, dy)
                    compr_3d += math.sqrt(dx * dx + dy * dy + dz * dz)

                feat = QgsFeature(layer.fields())
                feat.setGeometry(geom)
                feat.setAttributes([
                    feat_id,
                    raster_name,
                    seg_index,
                    len(coords_3d),
                    compr_lin,
                    compr_3d,
                    min(z for _, _, z in coords_3d),
                    max(z for _, _, z in coords_3d)])
                features.append(feat)
                feat_id += 1

        if not features:
            self.mostrar_mensagem(self.tr("Nenhuma geometria 3D válida pôde ser criada a partir do gráfico."), "Erro")
            return

        provider.addFeatures(features)
        layer.updateExtents()
        QgsProject.instance().addMapLayer(layer)

        self.mostrar_mensagem(self.tr("Camada 3D criada com {count} linha(s), conforme as linhas visíveis no gráfico.").format(count=len(features)), "Sucesso")

    def on_select_line_state_changed(self, state):
        """Ativa ou desativa a ferramenta de desenho de linha."""
        if state == Qt.CheckState.Checked:
            # Desativa o checkBoxLinha2 (seleção de linha de camada) se estiver ativo
            self.checkBoxLinha2.setChecked(False)
            self.deactivate_line_layer_tool()

            # perfil passa a ser de linha temporária
            self.current_line_layer = None
            self.current_line_feature = None

            # Linha desenhada não está ligada a nenhuma camada vetorial
            self.current_line_layer = None

            # Ativa a ferramenta de desenho de linha se o diálogo estiver visível
            if self.isVisible():
                self.activate_line_tool()

        else:
            # Desativa a ferramenta de desenho de linha
            self.deactivate_line_tool()

    def on_select_line_layer_state_changed(self, state):
        """Ativa ou desativa a ferramenta de seleção de linha de camada."""
        if state == Qt.CheckState.Checked:
            # Desativa o checkBoxLinha (linha temporária) se estiver ativo
            self.checkBoxLinha.setChecked(False)
            self.deactivate_line_tool()
            # Ativa a ferramenta de seleção de linha de camada
            self.activate_line_layer_tool()

        else:
            # Desativa a ferramenta de seleção de linha de camada
            self.deactivate_line_layer_tool()

    def activate_line_layer_tool(self):
        """Ativa a ferramenta de seleção de linha de qualquer camada."""
        if not hasattr(self, 'line_layer_tool') or not self.line_layer_tool:
            self.line_layer_tool = SelectLineTool(iface.mapCanvas(), self)
        iface.mapCanvas().setMapTool(self.line_layer_tool)

    def deactivate_line_layer_tool(self):
        """Desativa a ferramenta de seleção de linha."""
        if hasattr(self, 'line_layer_tool') and self.line_layer_tool:
            iface.mapCanvas().unsetMapTool(self.line_layer_tool)
            self.line_layer_tool = None

    def draw_rubber_band(self, points, color=None):
        """
        Desenha a linha no mapa com uma cor fixa baseada na ação (checkBoxLinha ou checkBoxLinha2).
        :param points: Lista de pontos para formar a linha.
        :param color: Cor fixa opcional para a linha. Se None, usa a cor padrão do checkbox ativo.
        """
        if not self.rubber_band:
            self.rubber_band = QgsRubberBand(iface.mapCanvas(), Qgis.GeometryType.Line)
            self.rubber_band.setWidth(2)

        # Define a cor da linha: usa o parâmetro 'color' ou a cor padrão do checkbox ativo
        if color:
            self.rubber_band.setColor(color)
        elif self.checkBoxLinha.isChecked():
            self.rubber_band.setColor(Qt.GlobalColor.red)  # Vermelho para linha temporária
        elif self.checkBoxLinha2.isChecked():
            self.rubber_band.setColor(Qt.GlobalColor.magenta)  # Magenta para linha fixa

        # Redefine a geometria da linha
        if points:
            line_geometry = QgsGeometry.fromPolylineXY([QgsPointXY(point.x(), point.y()) for point in points])
            self.rubber_band.setToGeometry(line_geometry, None)

    def update_checkboxes_state(self):
        """Atualiza o estado dos checkboxes com base nas condições."""
        # Verifica se o sistema de coordenadas do projeto é geográfico
        map_crs = iface.mapCanvas().mapSettings().destinationCrs()
        is_geographic = map_crs.isGeographic()

        # Verifica se há camadas selecionadas no listWidgetRaster
        has_selected_rasters = any(
            self.listWidgetRaster.item(i).checkState() == Qt.CheckState.Checked
            for i in range(self.listWidgetRaster.count())
            if self.listWidgetRaster.item(i).flags() & Qt.ItemFlag.ItemIsUserCheckable)

        # Verifica se há camadas de linha com feições
        has_line_features = any(
            isinstance(layer, QgsVectorLayer) and 
            layer.geometryType() == Qgis.GeometryType.Line and 
            layer.featureCount() > 0
            for layer in QgsProject.instance().mapLayers().values())

        # Atualiza o estado do checkBoxLinha
        self.checkBoxLinha.setEnabled(has_selected_rasters)
        if not has_selected_rasters:
            self.checkBoxLinha.setChecked(False)  # Desmarca se não houver camadas raster selecionadas

        # Atualiza o estado do checkBoxLinha2
        self.checkBoxLinha2.setEnabled(
            has_selected_rasters and has_line_features and not is_geographic)
        if not has_selected_rasters or is_geographic or not has_line_features:
            self.checkBoxLinha2.setChecked(False)  # Desmarca se as condições não forem atendidas

    def update_map_marker(self, distance):
        """Atualiza a posição do marcador no mapa com base na distância percorrida."""
        if not hasattr(self, 'line_distances') or not hasattr(self, 'line_points') or not self.line_distances or not self.line_points:
            self.remove_map_marker()
            return

        # Verifica se a distância está dentro do intervalo permitido
        if distance < self.line_distances[0] or distance > self.line_distances[-1]:
            self.remove_map_marker()
            return

        # Encontra os índices dos pontos entre os quais a distância atual se encontra
        point = None
        for i in range(len(self.line_distances) - 1):
            if self.line_distances[i] <= distance <= self.line_distances[i + 1]:
                # Interpola entre os pontos line_points[i] e line_points[i + 1]
                ratio = (distance - self.line_distances[i]) / (self.line_distances[i + 1] - self.line_distances[i])
                x = self.line_points[i].x() + ratio * (self.line_points[i + 1].x() - self.line_points[i].x())
                y = self.line_points[i].y() + ratio * (self.line_points[i + 1].y() - self.line_points[i].y())
                point = QgsPointXY(x, y)
                break

        if not point:
            self.remove_map_marker()
            return

        # Se o marcador não existir, cria um novo
        if not self.map_marker:
            self.map_marker = QgsVertexMarker(iface.mapCanvas())
            self.map_marker.setIconSize(10)
            self.map_marker.setIconType(QgsVertexMarker.IconType.ICON_CIRCLE)
            self.map_marker.setPenWidth(2)

        # Atualiza a cor do marcador com base no estado dos checkboxes
        if self.checkBoxLinha.isChecked():
            self.map_marker.setColor(Qt.GlobalColor.red)  # Vermelho para checkBoxLinha
        elif self.checkBoxLinha2.isChecked():
            self.map_marker.setColor(Qt.GlobalColor.magenta)  # Magenta para checkBoxLinha2

        # Atualiza a posição do marcador
        self.map_marker.setCenter(point)

        # Armazena o ponto e a distância atuais para uso no tooltip
        self.current_point = point
        self.current_distance = distance

    def hide_tooltip(self):
        """Esconde o tooltip flutuante."""
        if hasattr(self, 'tooltip_widget') and self.tooltip_widget and self.tooltip_widget.isVisible():
            self.tooltip_widget.hide()

    def on_checkBox_Cotas_state_changed(self, state):
        if state == Qt.CheckState.Checked:
            # Atualiza o marcador do mapa para mostrar o valor de Z
            if hasattr(self, 'current_distance') and self.current_distance is not None:
                self.update_map_marker(self.current_distance)
        else:
            # Esconde o tooltip se desmarcado
            self.hide_tooltip()

    def mouse_moved(self, evt):
        """
        Atualiza a interação do mouse somente com os perfis
        atualmente marcados no listWidgetRaster.
        """
        visible_profiles = self._get_visible_profiles()

        if not visible_profiles:
            if hasattr(self, "vLine"):
                self.vLine.hide()

            if hasattr(self, "hLine"):
                self.hLine.hide()

            if hasattr(self, "coord_text"):
                self.coord_text.hide()

            if hasattr(self, "sync_point"):
                self.sync_point.hide()

            self.remove_map_marker()
            self.hide_tooltip()
            return

        pos = evt[0]

        if self.plot_widget.plotItem.sceneBoundingRect().contains(pos):
            mousePoint = self.plot_widget.plotItem.vb.mapSceneToView(pos)

            x = mousePoint.x()
            y = mousePoint.y()

            # Considera somente os perfis VISÍVEIS.
            all_x_values = [valor_x
                for profile_data in visible_profiles
                for segment in profile_data["profiles"]
                for valor_x in segment["distances"]]

            if not all_x_values:
                return

            if min(all_x_values) <= x <= max(all_x_values):
                min_diff = float("inf")
                closest_y_interp = None
                closest_profile_data = None

                # Procura exclusivamente entre as camadas marcadas.
                for profile_data in visible_profiles:
                    for segment in profile_data["profiles"]:
                        distances = segment["distances"]
                        values = segment["values"]

                        if not distances or not values:
                            continue

                        if distances[0] <= x <= distances[-1]:
                            y_interp = np.interp(x, distances, values)

                            diff = abs(y - y_interp)

                            if diff < min_diff:
                                min_diff = diff
                                closest_y_interp = y_interp
                                closest_profile_data = profile_data

                if closest_y_interp is not None:
                    self.vLine.setPos(x)
                    self.hLine.setPos(closest_y_interp)

                    self.vLine.show()
                    self.hLine.show()

                    text_color = ("black"
                        if self.checkBox_PB.isChecked()
                        else "white")

                    self.coord_text.setHtml(
                        '<div style="color:{text_color};">'
                        '<b>{elevacao_label}</b> {elevacao:.2f} m<br>'
                        '<b>{distancia_label}</b> {distancia:.2f} m</div>'
                        .format(
                            text_color=text_color,
                            elevacao_label=self.tr("Elevação:"),
                            elevacao=closest_y_interp,
                            distancia_label=self.tr("Distância:"),
                            distancia=x))

                    self.coord_text.setPos(x, closest_y_interp)
                    self.coord_text.show()

                    self.sync_point.setData([x], [closest_y_interp])
                    self.sync_point.show()

                    self.update_map_marker(x)

                    if closest_profile_data:
                        layer = closest_profile_data["layer"]
                        color = self.get_color_for_layer(layer)

                    else:
                        color = QColor("white")

                    if self.checkBox_Cotas.isChecked():
                        self.show_tooltip_on_map(closest_y_interp, color)

                    else:
                        self.hide_tooltip()

                else:
                    self.vLine.hide()
                    self.hLine.hide()
                    self.coord_text.hide()
                    self.sync_point.hide()
                    self.remove_map_marker()
                    self.hide_tooltip()

            else:
                self.vLine.hide()
                self.hLine.hide()
                self.coord_text.hide()
                self.sync_point.hide()
                self.remove_map_marker()
                self.hide_tooltip()

        else:
            if hasattr(self, "vLine"):
                self.vLine.hide()

            if hasattr(self, "hLine"):
                self.hLine.hide()

            if hasattr(self, "coord_text"):
                self.coord_text.hide()

            if hasattr(self, "sync_point"):
                self.sync_point.hide()

            self.remove_map_marker()
            self.hide_tooltip()

    def get_color_for_layer(self, layer):
        """
        Retorna a cor associada a uma camada raster.
        Protege contra layers já destruídos (deletados do projeto).
        """
        if layer is None:
            return QColor('white')

        # Se o objeto C++ já foi destruído, evita chamar .name()
        try:
            if sip.isdeleted(layer):
                return QColor('white')
            layer_name = layer.name()
        except RuntimeError:
            # Qualquer problema ao acessar o layer → usa cor padrão
            return QColor('white')

        item = self.get_list_item_by_layer_name(layer_name)
        if item:
            color = item.data(Qt.ItemDataRole.UserRole)
            return color
        else:
            return QColor('white')

    def show_tooltip_on_map(self, z_value, color):
        """Mostra um tooltip flutuante no mapa com o valor de Z e a cor especificada."""
        # Inicializar o tooltip_widget se ainda não existir
        if not hasattr(self, 'tooltip_widget') or self.tooltip_widget is None:
            self.tooltip_widget = FloatingTooltip(iface.mainWindow())

        if self.current_point:
            canvas = iface.mapCanvas()

            # Converter as coordenadas do ponto para posição na tela
            screen_pos = canvas.mapSettings().mapToPixel().transform(self.current_point)
            global_pos = canvas.mapToGlobal(QPoint(int(screen_pos.x()), int(screen_pos.y())))

            # Mostrar o tooltip com o valor de Z e a cor
            self.tooltip_widget.show_tooltip(f"{z_value:.2f} m", global_pos, color)

    def get_raster_thumbnail(self, layer, max_size=150):
        """Gera uma miniatura de uma camada raster, ajustando ao formato da imagem."""
        if not isinstance(layer, QgsRasterLayer):
            return None

        # Obtém a extensão do raster
        extent = layer.extent()
        width_extent = extent.width()
        height_extent = extent.height()

        # Calcula a proporção da imagem
        if width_extent > height_extent:
            width = max_size
            height = int((height_extent / width_extent) * max_size)
        else:
            height = max_size
            width = int((width_extent / height_extent) * max_size)

        # Configura as definições do mapa
        map_settings = QgsMapSettings()
        map_settings.setLayers([layer])
        map_settings.setBackgroundColor(QColor(255, 255, 255))  # Fundo branco
        map_settings.setOutputSize(QSize(width, height))
        map_settings.setExtent(extent)

        # Cria uma imagem para renderizar o raster
        image = QImage(width, height, QImage.Format.Format_ARGB32)
        image.fill(Qt.GlobalColor.transparent)

        # Configura o pintor e o trabalho de renderização
        painter = QPainter(image)
        render_job = QgsMapRendererCustomPainterJob(map_settings, painter)

        # Executa o trabalho de renderização
        render_job.start()
        render_job.waitForFinished()
        painter.end()

        # Converte a imagem para PNG em memória
        buffer = QBuffer()
        buffer.open(QIODevice.OpenModeFlag.WriteOnly)
        image.save(buffer, "PNG")
        buffer.close()

        # Codifica os dados da imagem em Base64
        img_base64 = base64.b64encode(buffer.data()).decode('utf-8')

        return img_base64

    def setup_raster_tooltips(self):
        """Conecta o sinal de movimento do mouse ao listWidgetRaster."""
        self.listWidgetRaster.viewport().installEventFilter(self)

    def eventFilter(self, obj, event):
        """Intercepta eventos de mouse no listWidgetRaster."""
        if obj == self.listWidgetRaster.viewport() and event.type() == QEvent.Type.ToolTip:
            # Obtém a posição do mouse
            item = self.listWidgetRaster.itemAt(event.pos())
            if item:
                # Obtém a camada correspondente ao item
                layer_name = item.text()
                layers = QgsProject.instance().mapLayersByName(layer_name)
                if layers:
                    layer = layers[0]
                    img_base64 = self.get_raster_thumbnail(layer)
                    if img_base64:
                        # Cria o HTML do tooltip com a imagem embutida
                        tooltip_html = f"<img src='data:image/png;base64,{img_base64}'>"
                        QToolTip.showText(event.globalPos(), tooltip_html, self.listWidgetRaster)
                        return True
            else:
                QToolTip.hideText()
        return super().eventFilter(obj, event)

    def get_point_at_distance(self, distance):
        """Retorna o ponto ao longo da linha na distância cumulativa especificada."""
        if not self.line_points or not self.line_distances:
            return None

        if distance < self.line_distances[0] or distance > self.line_distances[-1]:
            return None

        if len(self.line_points) != len(self.line_distances):
            # desalinhado → evita crash silenciosamente
            return None

        for i in range(len(self.line_distances) - 1):
            d0 = self.line_distances[i]
            d1 = self.line_distances[i + 1]
            if d0 <= distance <= d1:
                # Evita divisão por zero
                if d1 - d0 == 0:
                    ratio = 0
                else:
                    ratio = (distance - d0) / (d1 - d0)
                x = self.line_points[i].x() + ratio * (self.line_points[i + 1].x() - self.line_points[i].x())
                y = self.line_points[i].y() + ratio * (self.line_points[i + 1].y() - self.line_points[i].y())
                return QgsPointXY(x, y)
        # Se a distância for exatamente a última, retorna o último ponto
        if np.isclose(distance, self.line_distances[-1]):
            return self.line_points[-1]
        return None

    def get_z_values_at_point(self, point):
        """Retorna um dicionário de valores Z das camadas raster selecionadas no ponto dado."""
        z_values = {}
        for layer in self.selected_raster_layers:
            # Transforma o ponto para o CRS da camada raster, se necessário
            raster_crs = layer.crs()
            map_crs = iface.mapCanvas().mapSettings().destinationCrs()
            if raster_crs != map_crs:
                transform = QgsCoordinateTransform(map_crs, raster_crs, QgsProject.instance())
                point_in_raster_crs = transform.transform(point)
            else:
                point_in_raster_crs = point

            ident = layer.dataProvider().identify(point_in_raster_crs, Qgis.RasterIdentifyFormat.Value)
            if ident.isValid():
                results = ident.results()
                value = list(results.values())[0]
                if value is not None and not np.isnan(value):
                    z_values[layer.name()] = value
                else:
                    z_values[layer.name()] = float('nan')
            else:
                z_values[layer.name()] = float('nan')
        return z_values

    def on_profile_ready(self, all_profiles):
        """Callback chamado quando o perfil está pronto."""
        self.all_profiles = all_profiles
        self.plot_profiles()
        # Chama o método para registrar os valores
        self.log_xyz_every_100m()

    def on_layer_name_changed(self):
        """Atualiza os nomes preservando os rasters selecionados."""
        selected_layer_ids = {
            layer.id()
            for layer in self.selected_raster_layers
            if layer is not None and not sip.isdeleted(layer)}

        self.populate_raster_list(
            selected_layer_ids=selected_layer_ids)

        if self.all_profiles:
            self.update_combobox_raster_list()

    def on_combobox_layer_changed(self, index):
        """
        Atualiza a tabela de dados com base na camada raster selecionada no comboBoxListaRaster.
        """
        selected_layer_name = self.comboBoxListaRaster.currentText()

        # Se nenhuma camada válida estiver selecionada, limpa a tabela
        if selected_layer_name == self.tr("Nenhuma camada exibida"):
            self.tableWidget_Dados.clearContents()
            self.tableWidget_Dados.setRowCount(0)
            self.graph_x_data = []
            self.graph_y_data = []
            self.update_create_button_state()
            self.update_export_button_state()
            return

        # Gera os dados a partir do log_xyz_every_100m
        self.log_xyz_every_100m()

    def populate_table(self, data):
        """
        Preenche o tableWidget_Dados com os dados fornecidos e calcula a Inclinação.
        :param data: Lista de tuplas contendo (distância, x, y, z).
        """
        self.tableWidget_Dados.clearContents()
        self.tableWidget_Dados.setRowCount(len(data))
        self.tableWidget_Dados.setColumnCount(6)  # Agora temos 6 colunas
        self.tableWidget_Dados.setHorizontalHeaderLabels(["ID", "X", "Y", "Z", self.tr("Inclinação (%)"), self.tr("Distância (m)")])

        # Inicializa variáveis para calcular a inclinação
        prev_z = None
        prev_distance = None
        crs = iface.mapCanvas().mapSettings().destinationCrs()
        coord_decimals = 8 if crs.isGeographic() else 2

        for row_index, (distance, x, y, z) in enumerate(data):
            # Adiciona o ID (sequência)
            self.tableWidget_Dados.setItem(row_index, 0, QTableWidgetItem(str(row_index + 1)))

            # Adiciona X, Y, Z, e Distância
            self.tableWidget_Dados.setItem(row_index, 1, QTableWidgetItem(f"{x:.{coord_decimals}f}"))
            self.tableWidget_Dados.setItem(row_index, 2, QTableWidgetItem(f"{y:.{coord_decimals}f}"))
            self.tableWidget_Dados.setItem(row_index, 3, QTableWidgetItem(f"{z:.2f}" if not np.isnan(z) else "N/A"))
            self.tableWidget_Dados.setItem(row_index, 5, QTableWidgetItem(f"{distance:.2f}"))

            # Calcula a inclinação
            if row_index == 0:
                # Para o primeiro ponto, inclinação é sempre 0, exceto se Z for inválido
                inclination = 0 if not np.isnan(z) else None
            elif prev_z is None or prev_distance is None or np.isnan(z):
                # Reinicia a inclinação se Z for inválido
                inclination = None
            else:
                try:
                    # Inclinação em %: (ΔZ / ΔDistância) * 100
                    inclination = ((z - prev_z) / (distance - prev_distance)) * 100
                except ZeroDivisionError:
                    inclination = 0  # Previne divisão por zero

            # Formata inclinação como N/A se for inválida
            inclination_str = f"{inclination:.3f} %" if inclination is not None else "N/A"
            self.tableWidget_Dados.setItem(row_index, 4, QTableWidgetItem(inclination_str))

            # Atualiza valores anteriores se Z for válido
            if not np.isnan(z):
                prev_z = z
                prev_distance = distance

        # Ajusta automaticamente o tamanho das colunas
        self.tableWidget_Dados.resizeColumnsToContents()

        #  Para chamar update_second_graph após preencher a tabela
        self.update_second_graph()
        self.update_create_button_state()

    def log_xyz_every_100m(self):
        """Registra X, Y e Z a cada N metros, onde N é definido no doubleSpinBox_espaco."""
        if not hasattr(self, 'line_points') or not self.line_points:
            return

        self.tableWidget_Dados.clearContents()
        self.tableWidget_Dados.setRowCount(0)

        selected_layer_name = self.comboBoxListaRaster.currentText()
        if selected_layer_name == self.tr("Nenhuma camada exibida"):
            return

        selected_layer = next(
            (layer for layer in self.selected_raster_layers
             if layer.name() == selected_layer_name), None)
        if not selected_layer:
            return

        total_distance = self.line_distances[-1] if self.line_distances else 0
        spacing = self.doubleSpinBox_espaco.value()

        # Se a linha veio de uma camada vetorial em geográfico, barra aqui
        if getattr(self, "current_line_layer", None) is not None:
            line_layer = self.current_line_layer
            if line_layer.crs().isGeographic():
                self.mostrar_mensagem(self.tr("A linha selecionada está em coordenadas geográficas, não é possível amostrar (camada de linha em coordenadas geográficas)."), "Erro")
                return

        if total_distance == 0:
            self.mostrar_mensagem(self.tr("A linha desenhada tem comprimento zero."), "Aviso")
            return
        if spacing <= 0:
            return

        # Usa primeiro e último ponto com Z válido do raster selecionado
        first_valid_distance = None
        last_valid_distance = None

        if getattr(self, "all_profiles", None):
            for profile_data in self.all_profiles:
                if profile_data.get("layer") == selected_layer:
                    for seg in profile_data.get("profiles", []):
                        dists = seg.get("distances", [])
                        vals = seg.get("values", [])
                        for d, v in zip(dists, vals):
                            if v is not None and not np.isnan(v):
                                if first_valid_distance is None:
                                    first_valid_distance = d
                                last_valid_distance = d
                    break

        distances_to_sample = []

        if first_valid_distance is not None and last_valid_distance is not None:
            # garante ordem
            if last_valid_distance < first_valid_distance:
                first_valid_distance, last_valid_distance = last_valid_distance, first_valid_distance

            d = first_valid_distance
            tol = 1e-6
            while d < last_valid_distance - tol:
                distances_to_sample.append(d)
                d += spacing

            # garante inclusão do último ponto com dado válido,
            # mesmo que o trecho final seja menor que o espaçamento
            if not distances_to_sample or abs(distances_to_sample[-1] - last_valid_distance) > tol:
                distances_to_sample.append(last_valid_distance)
        else:
            # fallback antigo: usa toda a linha
            distances_to_sample = list(np.arange(0, total_distance, spacing))
            if total_distance not in distances_to_sample:
                distances_to_sample.append(total_distance)

        # remove duplicados mantendo a ordem (por segurança contra arredondamento)
        seen = set()
        unique_distances = []
        for d in distances_to_sample:
            key = round(d, 6)
            if key not in seen:
                seen.add(key)
                unique_distances.append(d)
        distances_to_sample = unique_distances

        table_data = []
        self.graph_line_points = []  # Armazena os pontos

        for distance in distances_to_sample:
            point = self.get_point_at_distance(distance)
            if point:
                x, y = point.x(), point.y()
                z_values = self.get_z_values_at_point(point)
                z_value = z_values.get(selected_layer_name, float('nan'))
                table_data.append((distance, x, y, z_value))
                self.graph_line_points.append(point)

        self.populate_table(table_data)

    def update_table_on_spacing_change(self):
        """
        Atualiza a tabela de dados ao alterar o valor do espaçamento no doubleSpinBox_espaco.
        """
        spacing = self.doubleSpinBox_espaco.value()
        if spacing <= 0:
            self.mostrar_mensagem(self.tr("O espaçamento não pode ser zero ou negativo. Ajuste o valor."), "Aviso")
            return
        # Se estiver tudo ok:
        self.log_xyz_every_100m()

    def mouse_moved_second_graph(self, evt):
        """
        Destaca o trecho do perfil de terreno sob o cursor, exibe sua
        inclinação e destaca o mesmo segmento no mapa.
        """
        pos = evt[0]  # Obter a posição do mouse do evento

        if not hasattr(self, 'graph_x_data') or not hasattr(self, 'graph_y_data'):
            return

        if not self.graph_x_data or not self.graph_y_data:
            if hasattr(self, 'highlighted_segment') and self.highlighted_segment:
                try:
                    self.plot_widget2.removeItem(self.highlighted_segment)
                except Exception:
                    pass  # nosec B110
                self.highlighted_segment = None
                self.highlighted_segment_index = None

            if hasattr(self, 'inclination_text') and self.inclination_text:
                try:
                    self.plot_widget2.removeItem(self.inclination_text)
                except Exception:
                    pass  # nosec B110
                self.inclination_text = None

            self.clear_inclination_text_on_map()
            return

        if self.plot_widget2.plotItem.sceneBoundingRect().contains(pos):
            mousePoint = self.plot_widget2.plotItem.vb.mapSceneToView(pos)
            x = mousePoint.x()
            y = mousePoint.y()

            # Obter os dados do gráfico
            x_data = self.graph_x_data  # Distâncias
            y_data = self.graph_y_data  # Z (Elevação)

            if not x_data or not y_data:
                return

            # Encontrar o segmento entre duas IDs onde x está entre x_data[i] e x_data[i+1]
            for i in range(len(x_data) - 1):
                # Não cria um segmento entre linhas não consecutivas da tabela.
                if (hasattr(self, "graph_row_indices")
                    and len(self.graph_row_indices) > i + 1
                    and self.graph_row_indices[i + 1]
                    != self.graph_row_indices[i] + 1):
                    continue

                x0, x1 = x_data[i], x_data[i + 1]
                y0, y1 = y_data[i], y_data[i + 1]

                # Verificar se os valores de Z são válidos
                if y0 is None or y1 is None or np.isnan(y0) or np.isnan(y1):
                    continue  # Ignora este segmento

                delta_x = x1 - x0
                delta_y = y1 - y0

                # Verificar se a inclinação pode ser calculada
                if delta_x == 0 or delta_x is None or np.isnan(delta_x):
                    continue  # Ignora este segmento

                # Verifica se a posição do mouse está dentro do segmento (x0->x1)
                if x0 <= x <= x1 or x1 <= x <= x0:

                    table_inclination_item = None
                    # Usa o índice real da linha da tabela correspondente ao ponto i+1
                    if hasattr(self, "graph_row_indices") and len(self.graph_row_indices) > (i + 1):
                        row_idx = self.graph_row_indices[i + 1]
                        table_inclination_item = self.tableWidget_Dados.item(row_idx, 4)  # coluna Inclinação

                    if table_inclination_item:
                        # Lê a string exata, ex: "10.943 %"
                        inclination_str = table_inclination_item.text()
                    else:
                        # Se não houver item (ou fora de range), faz um fallback local
                        inclination_value = (delta_y / delta_x) * 100
                        # Aqui você pode escolher quantas casas exibir, ou não arredondar:
                        inclination_str = f"{inclination_value} %"

                    # Mouse está sobre o segmento entre os pontos i e i+1
                    if hasattr(self, 'highlighted_segment_index') and self.highlighted_segment_index == i:
                        # Já está destacado, não precisa fazer nada
                        return
                    else:
                        # Remover destaque anterior (linhas, textos, etc.)
                        if self.highlighted_segment:
                            self.plot_widget2.removeItem(self.highlighted_segment)
                            self.highlighted_segment = None

                        self.clear_inclination_text_on_graph2()

                        if self.highlighted_map_segment:
                            iface.mapCanvas().scene().removeItem(self.highlighted_map_segment)
                            self.highlighted_map_segment = None
                            self.clear_inclination_text_on_map()

                        # Criar uma nova linha com traço mais grosso para destacar o segmento
                        pen = pg.mkPen(color='yellow', width=4)
                        x_segment = [x0, x1]
                        y_segment = [y0, y1]
                        self.highlighted_segment = pg.PlotCurveItem(x_segment, y_segment, pen=pen)
                        self.plot_widget2.addItem(self.highlighted_segment)

                        # Armazenar o índice do segmento destacado
                        self.highlighted_segment_index = i

                        # Adicionar o texto da inclinação ao gráfico
                        self.show_inclination_text_on_graph2(inclination_str, x0, y0, x1, y1)

                        # Destacar o segmento correspondente no mapa
                        self.highlight_segment_on_map(i)

                        # Mostrar o texto de inclinação no mapa se o checkbox estiver marcado
                        if self.checkBox_Inclina.isChecked():
                            if hasattr(self, 'current_segment_points'):
                                point1, point2 = self.current_segment_points
                                self.show_inclination_text_on_map(inclination_str, point1, point2)
                        else:
                            self.clear_inclination_text_on_map()

                        break  # Segmento encontrado e processado
            else:
                # Mouse está fora da área do gráfico
                if self.highlighted_segment:
                    self.plot_widget2.removeItem(self.highlighted_segment)
                    self.highlighted_segment = None
                    self.highlighted_segment_index = None

                self.clear_inclination_text_on_graph2()

                if self.highlighted_map_segment:
                    iface.mapCanvas().scene().removeItem(self.highlighted_map_segment)
                    self.highlighted_map_segment = None
                    self.clear_inclination_text_on_map()

                # Esconder o tooltip de inclinação
                if hasattr(self, 'inclination_tooltip') and self.inclination_tooltip:
                    self.inclination_tooltip.hide()

    def setup_second_graph(self):
        """
        Configura o gráfico do perfil de terreno amostrado conforme
        o espaçamento definido no doubleSpinBox_espaco.
        """
        self.plot_widget2 = pg.PlotWidget(enableMenu=False)
        self.scrollAreaGrafico2.setWidget(self.plot_widget2)

        self.plot_widget2.setBackground("k")

        self.plot_widget2.setLabel(
            "left",
            self.tr("Elevação (m)"),
            color="white",
            size="10pt")

        self.plot_widget2.setLabel(
            "bottom",
            self.tr("Distância Acumulada (m)"),
            color="white",
            size="10pt")

        self.plot_widget2.showGrid(
            x=True,
            y=True,
            alpha=0.3)

        self.graph_x_data = []
        self.graph_y_data = []
        self.graph_segments = []
        self.graph_row_indices = []
        self.graph_line_points_filtered = []

        self.proxy2 = pg.SignalProxy(
            self.plot_widget2.scene().sigMouseMoved,
            rateLimit=60,
            slot=self.mouse_moved_second_graph)

        self.highlighted_segment = None
        self.highlighted_segment_index = None

    def reset_table_and_graph(self):
        """
        Reseta o tableWidget_Dados e o gráfico no scrollAreaGrafico2.
        """
        # Reseta a tabela
        self.tableWidget_Dados.clearContents()
        self.tableWidget_Dados.setRowCount(0)
        self.tableWidget_Dados.setColumnCount(0)

        # Limpa explicitamente itens auxiliares do segundo gráfico
        if hasattr(self, 'plot_widget2') and self.plot_widget2 is not None:
            if hasattr(self, 'highlighted_segment') and self.highlighted_segment:
                try:
                    self.plot_widget2.removeItem(self.highlighted_segment)
                except Exception:
                    pass  # nosec B110
                self.highlighted_segment = None

            self.clear_inclination_text_on_graph2()

            self.plot_widget2.clear()

        self.highlighted_segment_index = None

        # Limpa completamente os dados-base do segundo gráfico
        self.graph_x_data = []
        self.graph_y_data = []
        self.graph_segments = []
        self.graph_row_indices = []
        self.graph_line_points_filtered = []
        self.current_segment_points = None

        # Limpa também reflexos no mapa
        if hasattr(self, 'highlighted_map_segment') and self.highlighted_map_segment:
            try:
                iface.mapCanvas().scene().removeItem(self.highlighted_map_segment)
            except Exception:
                pass  # nosec B110
            self.highlighted_map_segment = None

        self.clear_inclination_text_on_map()
        self.update_create_button_state()
        self.update_export_button_state()
        self.update_create_line_button_state()

    def update_second_graph(self):
        """
        Atualiza o segundo gráfico como um perfil de terreno amostrado.

        Eixo X:
            distância acumulada definida pelos pontos amostrados conforme
            o doubleSpinBox_espaco.

        Eixo Y:
            elevação Z do raster selecionado.

        A inclinação permanece disponível na tabela e no destaque dos trechos.
        """
        if not hasattr(self, "plot_widget2"):
            self.setup_second_graph()

        self.plot_widget2.clear()

        self.highlighted_segment = None
        self.highlighted_segment_index = None
        self.clear_inclination_text_on_graph2()

        selected_raster_name = self.comboBoxListaRaster.currentText()

        if (not selected_raster_name
            or selected_raster_name
            == self.tr("Nenhuma camada exibida")):
            self.graph_x_data = []
            self.graph_y_data = []
            self.graph_segments = []
            self.graph_row_indices = []
            self.graph_line_points_filtered = []
            self.update_export_button_state()
            self.update_create_line_button_state()
            return

        color = self.get_selected_raster_display_color()
        pen = pg.mkPen(color=color, width=2)

        x_data = []
        y_data = []
        valid_graph_line_points = []
        graph_row_indices = []
        graph_segments = []

        segment_x = []
        segment_y = []

        for row in range(self.tableWidget_Dados.rowCount()):
            distance_item = self.tableWidget_Dados.item(row, 5)
            z_item = self.tableWidget_Dados.item(row, 3)

            if not distance_item or not z_item:
                if len(segment_x) >= 2:
                    graph_segments.append(
                        (segment_x, segment_y))

                segment_x = []
                segment_y = []
                continue

            distance_text = distance_item.text().strip()
            z_text = z_item.text().strip()

            if z_text.upper() == "N/A":
                if len(segment_x) >= 2:
                    graph_segments.append(
                        (segment_x, segment_y))

                segment_x = []
                segment_y = []
                continue

            try:
                distance = float(distance_text)
                z_value = float(z_text)

            except ValueError:
                if len(segment_x) >= 2:
                    graph_segments.append(
                        (segment_x, segment_y))

                segment_x = []
                segment_y = []
                continue

            point = None

            if (hasattr(self, "graph_line_points")
                and row < len(self.graph_line_points)):
                point = self.graph_line_points[row]

            if point is None:
                if len(segment_x) >= 2:
                    graph_segments.append(
                        (segment_x, segment_y))

                segment_x = []
                segment_y = []
                continue

            x_data.append(distance)
            y_data.append(z_value)
            valid_graph_line_points.append(point)
            graph_row_indices.append(row)

            segment_x.append(distance)
            segment_y.append(z_value)

        if len(segment_x) >= 2:
            graph_segments.append(
                (segment_x, segment_y))

        self.graph_x_data = x_data
        self.graph_y_data = y_data
        self.graph_segments = graph_segments
        self.graph_line_points_filtered = valid_graph_line_points
        self.graph_row_indices = graph_row_indices

        self.plot_widget2.setLabel(
            "left",
            self.tr("Elevação (m)"),
            color="white",
            size="10pt")

        self.plot_widget2.setLabel(
            "bottom",
            self.tr("Distância Acumulada (m)"),
            color="white",
            size="10pt")

        for segment_distances, segment_elevations in graph_segments:
            self.plot_widget2.plot(
                segment_distances,
                segment_elevations,
                pen=pen)

        self.fit_second_graph_view(padding=0.03)
        self.update_export_button_state()
        self.update_create_line_button_state()

    def fit_second_graph_view(self, padding: float = 0.05):
        """Ajusta o enquadramento do plot_widget2 aos dados atuais, com uma margem (padding)."""
        if not getattr(self, "graph_x_data", None) or not getattr(self, "graph_y_data", None):
            return
        if not self.graph_x_data or not self.graph_y_data:
            return

        # Filtra Y válidos
        y_valid = [y for y in self.graph_y_data if y is not None and not np.isnan(y)]
        if not y_valid:
            return

        x_min, x_max = min(self.graph_x_data), max(self.graph_x_data)
        y_min, y_max = min(y_valid), max(y_valid)

        # Garante intervalos não nulos
        if math.isclose(x_min, x_max):
            dx = max(1.0, abs(x_min) * 0.01)
            x_min -= dx; x_max += dx
        if math.isclose(y_min, y_max):
            dy = max(1.0, abs(y_min) * 0.01)
            y_min -= dy; y_max += dy

        x_pad = (x_max - x_min) * padding
        y_pad = (y_max - y_min) * padding

        self.plot_widget2.enableAutoRange(axis='x', enable=False)
        self.plot_widget2.enableAutoRange(axis='y', enable=False)
        self.plot_widget2.setXRange(x_min - x_pad, x_max + x_pad, padding=0)
        self.plot_widget2.setYRange(y_min - y_pad, y_max + y_pad, padding=0)

    def on_checkBox_Inclina_state_changed(self, state):
        """Esconde o texto de inclinação se o checkbox for desmarcado."""
        if state != Qt.CheckState.Checked:
            if hasattr(self, 'inclination_tooltip') and self.inclination_tooltip:
                self.inclination_tooltip.hide()
            self.clear_inclination_text_on_map()

    def highlight_segment_on_map(self, segment_index):
        """
        Destaca o segmento correspondente na linha do mapa.
        :param segment_index: Índice do segmento na lista de pontos da linha.
        """
        # Remover o destaque anterior se existir
        if self.highlighted_map_segment:
            iface.mapCanvas().scene().removeItem(self.highlighted_map_segment)
            self.highlighted_map_segment = None

        # Verificar se os pontos do gráfico estão disponíveis
        if not hasattr(self, 'graph_line_points_filtered') or not self.graph_line_points_filtered:
            return

        # Verificar se o índice do segmento é válido
        if segment_index < len(self.graph_line_points_filtered) - 1:
            point1 = self.graph_line_points_filtered[segment_index]
            point2 = self.graph_line_points_filtered[segment_index + 1]

            # Garantir que ambos os pontos são válidos
            if not point1 or not point2:
                return

            # Criar uma rubber band para o segmento destacado
            self.highlighted_map_segment = QgsRubberBand(iface.mapCanvas(), Qgis.GeometryType.Line)
            self.highlighted_map_segment.setColor(Qt.GlobalColor.yellow)
            self.highlighted_map_segment.setWidth(4)
            self.highlighted_map_segment.setToGeometry(QgsGeometry.fromPolylineXY([point1, point2]), None)

            # Armazenar os pontos do segmento atual
            self.current_segment_points = (point1, point2)

    def update_spinBox_maximum(self):
        """Atualiza o valor máximo do doubleSpinBox_espaco para o comprimento da linha temporária."""
        if hasattr(self, 'line_distances') and self.line_distances:
            total_length = self.line_distances[-1]  # Comprimento total da linha
            self.doubleSpinBox_espaco.setMaximum(total_length)
        else:
            self.doubleSpinBox_espaco.setMaximum(0)  # Valor padrão quando não há linha

    def update_spinbox_pontos_step(self, value: int):
        """
        Ajusta o passo (singleStep) do spinBoxPontos:

            10   ≤ valor < 100   → passo 10
            100 ≤ valor < 1000   → passo 50
            1000 ≤ valor ≤ 3000  → passo 100
        """
        if value < 100:
            step = 10
        elif value < 1000:
            step = 50
        else:                      # value >= 1000
            step = 100

        if self.spinBoxPontos.singleStep() != step:
            self.spinBoxPontos.blockSignals(True)
            self.spinBoxPontos.setSingleStep(step)
            self.spinBoxPontos.blockSignals(False)

    def create_points_layer_from_table(self):
        """
        Cria uma camada de pontos a partir dos dados amostrados
        presentes no tableWidget_Dados.
        """
        row_count = self.tableWidget_Dados.rowCount()

        if row_count == 0:
            self.mostrar_mensagem(self.tr("Tabela de dados está vazia."), "Erro")
            return

        selected_raster_name = self.comboBoxListaRaster.currentText()

        if (not selected_raster_name
            or selected_raster_name == self.tr("Nenhuma camada exibida")):

            self.mostrar_mensagem(self.tr("Nenhuma camada raster selecionada."), "Erro")
            return

        base_layer_name = self.tr("{selected_raster_name}_Pontos").format(
            selected_raster_name=selected_raster_name)

        existing_layer_names = {layer.name()
            for layer in QgsProject.instance().mapLayers().values()}

        layer_name = base_layer_name
        counter = 1

        while layer_name in existing_layer_names:
            layer_name = f"{base_layer_name}_{counter}"
            counter += 1

        crs = iface.mapCanvas().mapSettings().destinationCrs()

        layer = QgsVectorLayer(f"Point?crs={crs.authid()}", layer_name, "memory")

        if not layer.isValid():
            self.mostrar_mensagem(self.tr("Falha ao criar a camada de pontos."), "Erro")
            return

        provider = layer.dataProvider()

        # Nomes internos estáveis, sem espaços ou caracteres especiais.
        provider.addAttributes([
            QgsField("ID", QMetaType.Type.QString),
            QgsField("X", QMetaType.Type.Double),
            QgsField("Y", QMetaType.Type.Double),
            QgsField("Z", QMetaType.Type.Double),
            QgsField("Incl_pct", QMetaType.Type.Double),
            QgsField("Dist_m", QMetaType.Type.Double)])

        layer.updateFields()

        # Exibe nomes amigáveis e traduzíveis na tabela de atributos.
        aliases = [
            self.tr("ID"),
            self.tr("X"),
            self.tr("Y"),
            self.tr("Z"),
            self.tr("Inclinação (%)"),
            self.tr("Distância (m)")]

        for field_index, alias in enumerate(aliases):
            layer.setFieldAlias(field_index, alias)

        stored_points = getattr(self, "graph_line_points", [])

        use_stored_points = (len(stored_points) == row_count)

        features = []

        def obter_numero(row, column):
            item = self.tableWidget_Dados.item(row, column)

            if not item:
                return None

            text = (
                item.text()
                .strip()
                .replace(" %", "")
                .replace("%", "")
                .replace(",", "."))

            if not text or text.upper() == "N/A":
                return None

            try:
                return float(text)
            except (TypeError, ValueError):
                return None

        for row in range(row_count):
            try:
                id_item = self.tableWidget_Dados.item(row, 0)

                id_value = (id_item.text()
                    if id_item
                    else str(row + 1))

                x = obter_numero(row, 1)
                y = obter_numero(row, 2)
                z = obter_numero(row, 3)
                inclination = obter_numero(row, 4)
                distance = obter_numero(row, 5)

                if use_stored_points:
                    point = QgsPointXY(
                        stored_points[row])

                    x = point.x()
                    y = point.y()

                elif x is not None and y is not None:
                    point = QgsPointXY(x, y)

                else:
                    continue

                feature = QgsFeature(layer.fields())

                feature.setGeometry(
                    QgsGeometry.fromPointXY(point))

                feature.setAttributes([id_value, x, y, z, inclination, distance])

                features.append(feature)

            except Exception as error:
                self.mostrar_mensagem(self.tr(
                        "Erro ao processar a linha {row}: "
                        "{error}").format(row=row + 1, error=str(error)), "Erro")

        if not features:
            self.mostrar_mensagem(self.tr(
                    "Nenhum ponto válido pôde ser criado "
                    "a partir da tabela."), "Aviso")
            return

        result = provider.addFeatures(features)

        if isinstance(result, tuple):
            success = bool(result[0])
        else:
            success = bool(result)

        if not success:
            self.mostrar_mensagem(self.tr(
                    "Falha ao adicionar as feições "
                    "à camada de pontos."), "Erro")
            return

        layer.updateExtents()
        QgsProject.instance().addMapLayer(layer)

        self.mostrar_mensagem( self.tr(
                "Camada '{layer_name}' criada com "
                "{count} ponto(s)!").format(layer_name=layer_name,  count=len(features)), "Sucesso")

    def _count_real_raster_items(self):
        """Conta apenas os itens de raster reais (ignora o cabeçalho)."""
        total = 0
        for i in range(self.listWidgetRaster.count()):
            item = self.listWidgetRaster.item(i)
            if item and (item.flags() & Qt.ItemFlag.ItemIsUserCheckable):
                total += 1
        return total

    def update_raster_action_buttons_state(self):
        """
        Habilita/Desabilita os botões auxiliares de raster
        conforme a existência de camadas reais no listWidgetRaster.
        """
        has_rasters = self._count_real_raster_items() > 0
        self.pushButtonSelecionar.setEnabled(has_rasters)
        self.pushButtonResetar.setEnabled(has_rasters)

    def update_3d_button_state(self):
        """
        Ativa o pushButtonCamada3D apenas quando houver linhas visíveis
        no gráfico principal (scrollAreaGrafico).
        """
        has_visible_graph = bool(self._get_visible_profiles())
        self.pushButtonCamada3D.setEnabled(has_visible_graph)

    def update_create_line_button_state(self):
        """
        Ativa o pushButtonCriaLinha apenas quando houver dados válidos
        no segundo gráfico (scrollAreaGrafico2).
        """
        has_graph2_data = (
            hasattr(self, 'graph_x_data') and
            hasattr(self, 'graph_y_data') and
            len(self.graph_x_data) >= 2 and
            len(self.graph_y_data) >= 2)

        has_table_rows = self.tableWidget_Dados.rowCount() >= 2

        selected_raster_name = self.comboBoxListaRaster.currentText()
        has_valid_raster = (
            selected_raster_name
            and selected_raster_name != self.tr("Nenhuma camada exibida"))

        enabled = bool(has_graph2_data and has_table_rows and has_valid_raster)

        self.pushButtonCriaLinha.setEnabled(enabled)

    def get_selected_raster_display_color(self):
        """
        Retorna a cor visual associada ao raster atualmente selecionado
        no comboBoxListaRaster / listWidgetRaster.
        """
        selected_raster_name = self.comboBoxListaRaster.currentText()

        for index in range(self.listWidgetRaster.count()):
            item = self.listWidgetRaster.item(index)
            if not item:
                continue
            if item.text() == selected_raster_name:
                color = item.data(Qt.ItemDataRole.UserRole)
                if isinstance(color, QColor):
                    return color
                return QColor(color)

        return QColor(255, 0, 0)  # fallback

    def build_unique_second_graph_line_layer_name(self):
        """
        Gera um nome único no padrão:
        <RasterSelecionado>_Linha
        <RasterSelecionado>_Linha_1
        <RasterSelecionado>_Linha_2
        ...
        """
        selected_raster_name = self.comboBoxListaRaster.currentText()

        if not selected_raster_name or selected_raster_name == self.tr("Nenhuma camada exibida"):
            selected_raster_name = self.tr("Perfil")

        base_name = self.tr("{selected_raster_name}_Perfil_Amostrado").format(selected_raster_name=selected_raster_name)

        existing_layer_names = {layer.name()
            for layer in QgsProject.instance().mapLayers().values()}

        if base_name not in existing_layer_names:
            return base_name

        counter = 1
        while f"{base_name}_{counter}" in existing_layer_names:
            counter += 1

        return f"{base_name}_{counter}"

    def create_second_graph_3d_line_layer(self):
        """
        Cria uma camada 3D de linhas a partir dos trechos representados
        no segundo gráfico (scrollAreaGrafico2).

        Regras:
        - 1 feição por trecho entre dois pontos consecutivos válidos
        - atributo com comprimento do trecho
        - atributo com inclinação (%)
        - nome da camada = <Raster>_Linha, com sufixo sequencial se necessário
        - cor da linha = mesma cor do raster no gráfico
        - rótulo = inclinação (%) em amarelo
        """
        selected_raster_name = self.comboBoxListaRaster.currentText()
        if selected_raster_name == self.tr("Nenhuma camada exibida"):
            self.mostrar_mensagem(self.tr("Nenhuma camada raster selecionada no comboBoxListaRaster."), "Erro")
            return

        row_count = self.tableWidget_Dados.rowCount()
        if row_count < 2:
            self.mostrar_mensagem(self.tr("Não há dados suficientes no segundo gráfico para criar linhas."), "Erro")
            return

        if not hasattr(self, 'graph_line_points') or not self.graph_line_points:
            self.mostrar_mensagem(self.tr("Não há pontos de linha associados ao segundo gráfico."), "Erro")
            return

        crs = iface.mapCanvas().mapSettings().destinationCrs()
        layer_name = self.build_unique_second_graph_line_layer_name()

        layer = QgsVectorLayer(f"LineStringZ?crs={crs.authid()}", layer_name, "memory")
        if not layer.isValid():
            self.mostrar_mensagem(self.tr("Falha ao criar a camada de linhas 3D do segundo gráfico."), "Erro")
            return

        provider = layer.dataProvider()
        provider.addAttributes([
            QgsField("ID", QMetaType.Type.Int),
            QgsField("Trecho_m", QMetaType.Type.Double),
            QgsField("Incl_pct", QMetaType.Type.Double),
            QgsField("Z_ini", QMetaType.Type.Double),
            QgsField("Z_fim", QMetaType.Type.Double)])
        layer.updateFields()

        features = []
        feat_id = 1

        # Colunas da tabela
        COL_Z = 3
        COL_INCL = 4
        COL_DIST = 5

        for row in range(row_count - 1):
            try:
                p1 = self.graph_line_points[row]
                p2 = self.graph_line_points[row + 1]

                if p1 is None or p2 is None:
                    continue

                z_ini_item = self.tableWidget_Dados.item(row, COL_Z)
                z_fim_item = self.tableWidget_Dados.item(row + 1, COL_Z)
                incl_item = self.tableWidget_Dados.item(row + 1, COL_INCL)
                dist_ini_item = self.tableWidget_Dados.item(row, COL_DIST)
                dist_fim_item = self.tableWidget_Dados.item(row + 1, COL_DIST)

                if not all([z_ini_item, z_fim_item, incl_item, dist_ini_item, dist_fim_item]):
                    continue

                z_ini_txt = z_ini_item.text().strip()
                z_fim_txt = z_fim_item.text().strip()
                incl_txt = incl_item.text().strip()
                dist_ini_txt = dist_ini_item.text().strip()
                dist_fim_txt = dist_fim_item.text().strip()

                if z_ini_txt.upper() == "N/A" or z_fim_txt.upper() == "N/A" or incl_txt.upper() == "N/A":
                    continue

                z_ini = float(z_ini_txt)
                z_fim = float(z_fim_txt)
                incl_pct = float(incl_txt.replace("%", "").replace(" ", ""))
                dist_ini = float(dist_ini_txt)
                dist_fim = float(dist_fim_txt)

                trecho_m = abs(dist_fim - dist_ini)

                geom = QgsGeometry.fromWkt(
                    f"LineStringZ ({p1.x()} {p1.y()} {z_ini}, {p2.x()} {p2.y()} {z_fim})")

                if geom is None or geom.isEmpty():
                    continue

                feat = QgsFeature(layer.fields())
                feat.setGeometry(geom)
                feat.setAttributes([feat_id, trecho_m, incl_pct, z_ini, z_fim])
                features.append(feat)
                feat_id += 1

            except Exception:  # nosec B112
                continue

        if not features:
            self.mostrar_mensagem(self.tr("Nenhum trecho válido pôde ser criado a partir do segundo gráfico."), "Erro")
            return

        provider.addFeatures(features)
        layer.updateExtents()
        QgsProject.instance().addMapLayer(layer)

        # Aplica a cor da linha igual à cor do gráfico/raster
        line_color = self.get_selected_raster_display_color()
        symbol = layer.renderer().symbol()
        if symbol is not None:
            symbol.setColor(line_color)
            symbol.setWidth(0.5)
        layer.triggerRepaint()

        # Configura rótulos com a inclinação em amarelo
        settings = QgsPalLayerSettings()
        settings.enabled = True
        settings.fieldName = "Incl_pct"

        text_format = QgsTextFormat()
        text_format.setColor(QColor(Qt.GlobalColor.yellow))
        text_format.setSize(10)

        settings.setFormat(text_format)
        settings.placement = Qgis.LabelPlacement.Curved
        settings.centroidWhole = False

        labeling = QgsVectorLayerSimpleLabeling(settings)
        layer.setLabeling(labeling)
        layer.setLabelsEnabled(True)
        layer.triggerRepaint()

        self.mostrar_mensagem(self.tr("Camada '{layer_name}' criada com {count} trecho(s) do segundo gráfico.").format( layer_name=layer_name, count=len(features)), "Sucesso")

    def update_create_button_state(self):
        """
        Habilita o pushButtonCriar quando houver:
        - uma camada raster válida selecionada;
        - pelo menos uma linha da tabela com coordenadas X e Y válidas.

        A criação da camada de pontos depende da tabela, não da
        visibilidade do gráfico principal.
        """
        selected_raster_name = self.comboBoxListaRaster.currentText()

        has_valid_raster = bool(
            selected_raster_name
            and selected_raster_name
            != self.tr("Nenhuma camada exibida"))

        has_valid_coordinates = False

        for row in range(self.tableWidget_Dados.rowCount()):
            x_item = self.tableWidget_Dados.item(row, 1)
            y_item = self.tableWidget_Dados.item(row, 2)

            if not x_item or not y_item:
                continue

            try:
                float(x_item.text().replace(",", "."))
                float(y_item.text().replace(",", "."))
                has_valid_coordinates = True
                break

            except (TypeError, ValueError):
                continue

        self.pushButtonCriar.setEnabled(has_valid_raster
            and has_valid_coordinates)

    def setup_comboboxes(self):
        """
        Configura os comboBoxTipo e comboBoxTipo_2 com os formatos de exportação,
        texto maior e barra de rolagem com 3 itens visíveis.
        """
        # Define os formatos disponíveis para exportação
        formats = [
            self.tr("Selecione:"),  # Primeira mensagem
            "*.png",       # Imagem raster
            "*.svg",       # Imagem vetorial
            "*.dxf",       # Formato CAD
            "*.pdf",       # Documento PDF
            "*.tiff",      # Imagem raster de alta qualidade
            "*.jpeg"]      # Imagem raster compactada

        # Configura o comboBoxTipo
        self.comboBoxTipo.clear()
        self.comboBoxTipo.addItems(formats)
        self.comboBoxTipo.setStyleSheet("""
            QComboBox {
                font-size: 12px;  /* Tamanho do texto no ComboBox */
                padding: 4px;     /* Espaçamento interno */
            }
            QComboBox QAbstractItemView {
                font-size: 12px;  /* Tamanho do texto na lista */
                background-color: white;  /* Fundo branco */
                selection-background-color: blue;  /* Fundo ao selecionar */
                border: 1px solid lightgray;  /* Borda */
                padding: 4px;     /* Espaçamento interno */
            }
        """)
        self.comboBoxTipo.setMaxVisibleItems(3)  # Limita a exibição a 3 itens visíveis
        self.comboBoxTipo.setView(QListView())  # Habilita barra de rolagem personalizada

        # Configura o comboBoxTipo_2
        self.comboBoxTipo_2.clear()
        self.comboBoxTipo_2.addItems(formats)
        self.comboBoxTipo_2.setStyleSheet("""
            QComboBox {
                font-size: 12px;  /* Tamanho do texto no ComboBox */
                padding: 4px;     /* Espaçamento interno */
            }
            QComboBox QAbstractItemView {
                font-size: 12px;  /* Tamanho do texto na lista */
                background-color: white;  /* Fundo branco */
                selection-background-color: blue;  /* Fundo ao selecionar */
                border: 1px solid lightgray;  /* Borda */
                padding: 4px;     /* Espaçamento interno */
            }
        """)
        self.comboBoxTipo_2.setMaxVisibleItems(3)  # Limita a exibição a 3 itens visíveis
        self.comboBoxTipo_2.setView(QListView())  # Habilita barra de rolagem personalizada

    def reset_comboboxes(self):
        """
        Reseta os comboBoxTipo e comboBoxTipo_2 ao estado inicial.
        """
        self.comboBoxTipo.setCurrentIndex(0)  # Reseta para "Selecione:"
        self.comboBoxTipo_2.setCurrentIndex(0)  # Reseta para "Selecione:"
        self.update_export_button_state()

    def _has_active_line_feature_context(self):
        """
        Retorna True se houver contexto suficiente para sugerir o uso do checkBoxLinha2.

        Regras:
        1) Se já existe uma feição de linha identificada pelo SelectLineTool, retorna True.
        2) Senão, basta existir no projeto ao menos uma camada vetorial de linha
           com pelo menos 1 feição.
        """
        # Caso já exista uma feição de linha armazenada pelo fluxo do checkBoxLinha2
        if getattr(self, "current_line_layer", None) is not None and getattr(self, "current_line_feature", None) is not None:
            return True

        # Caso exista alguma camada vetorial de linha com feições no projeto
        for layer in QgsProject.instance().mapLayers().values():
            if not isinstance(layer, QgsVectorLayer):
                continue

            if layer.geometryType() != Qgis.GeometryType.Line:
                continue

            try:
                if layer.featureCount() > 0:
                    return True
            except Exception:
                pass  # nosec B110

        return False

    def _blink_checkbox(self, checkbox, color_hex, cycles=2, interval_ms=120):
        """
        Faz o checkbox piscar rapidamente alterando apenas o indicador.
        Não altera o estado checked/unchecked nem o texto.
        """
        if not checkbox or sip.isdeleted(checkbox):
            return

        # Se o checkbox já estiver marcado, não pisca
        if checkbox.isChecked():
            return

        original_style = checkbox.styleSheet() or ""

        # Estiliza apenas o quadradinho do checkbox
        blink_style = f"""
        QCheckBox::indicator {{
            width: 10px;
            height: 10px;
        }}
        QCheckBox::indicator:unchecked {{
            border: 1px solid {color_hex};
            background-color: rgba(255, 255, 255, 70);
        }}
        QCheckBox::indicator:checked {{
            border: 1px solid {color_hex};
            background-color: {color_hex};
        }}
        """
        total_steps = cycles * 2  # liga/desliga por ciclo

        def _step(i=0):
            if sip.isdeleted(checkbox):
                return

            if i >= total_steps:
                checkbox.setStyleSheet(original_style)
                return

            if i % 2 == 0:
                checkbox.setStyleSheet(blink_style)
            else:
                checkbox.setStyleSheet(original_style)

            QtCore.QTimer.singleShot(interval_ms, lambda: _step(i + 1))

        _step()

    def _maybe_blink_line_checkboxes_after_select(self):
        """
        Pisca os checkboxes de linha após o pushButtonSelecionar,
        apenas como dica visual.
        Regra:
        - se checkBoxLinha ou checkBoxLinha2 já estiverem marcados, não pisca nada
        - checkBoxLinha pisca em vermelho
        - checkBoxLinha2 pisca em azul somente se houver contexto de linha ativa
        """
        # Se um dos modos de linha já estiver ativo, não pisca nada
        if self.checkBoxLinha.isChecked() or self.checkBoxLinha2.isChecked():
            return

        # Pisca o modo de linha temporária
        self._blink_checkbox(self.checkBoxLinha, "#ff3b30", cycles=2, interval_ms=120)

        # Pisca o modo de linha por camada apenas se houver feição/camada de linha ativa
        if self._has_active_line_feature_context():
            self._blink_checkbox(self.checkBoxLinha2, "#00ff00", cycles=2, interval_ms=120)

    def escolher_local_para_salvar(self, nome_padrao, tipo_arquivo):

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
        fileName, _ = QFileDialog.getSaveFileName(self, self.tr("Salvar Camada"), nome_completo_proposto, tipo_arquivo)

        # Verifica se um nome de arquivo foi escolhido
        if fileName:
            # Atualiza o último diretório usado nas configurações do QGIS
            settings.setValue("lastDir", os.path.dirname(fileName))

            # Assegura que o arquivo tenha a extensão correta
            if not fileName.endswith(extensao):
                fileName += extensao

        return fileName  # Retorna o caminho completo do arquivo escolhido ou None se cancelado

    def mostrar_mensagem(self, texto, tipo, duracao=2, caminho_pasta=None, caminho_arquivo=None):
        """
        Exibe mensagem na barra do QGIS.
        tipo: 'Erro', 'Aviso' ou 'Sucesso'
        """
        bar = self.iface.messageBar()

        # remove eventual widget anterior de sucesso
        if tipo == "Sucesso" and self._widget_msg_sucesso is not None:
            try:
                bar.popWidget(self._widget_msg_sucesso)
            except (RuntimeError, TypeError):
                pass  # nosec B110 | A mensagem pode já ter expirado.
            self._widget_msg_sucesso = None

        if tipo == "Erro":
            bar.pushMessage(self.tr("Erro"), texto, level=Qgis.MessageLevel.Critical, duration=duracao)

        elif tipo == "Aviso":
            # Aviso ESPECIAL: azul claro translúcido
            if texto == self.tr("Desenhe ou selecione uma linha para gerar o perfil."):
                msg = bar.createMessage("Aviso", texto)

                msg.setStyleSheet("""
                    QFrame {
                        background-color: rgba(0, 170, 255, 80%);
                        border-radius: 3px;
                    }
                    QLabel {color: black;}""")

                bar.pushWidget(msg, level=Qgis.MessageLevel.Info, duration=duracao)

            else:
                # Demais avisos continuam no amarelo padrão do QGIS
                bar.pushMessage(self.tr("Aviso"), texto, level=Qgis.MessageLevel.Warning, duration=duracao)

        elif tipo == "Sucesso":
            msg = bar.createMessage(self.tr("Sucesso"), texto)

            # botão para abrir pasta (opcional)
            if caminho_pasta:
                btn_pasta = QPushButton(self.tr("Abrir Pasta"))
                btn_pasta.clicked.connect(
                    lambda _checked=False, caminho=caminho_pasta:
                        QDesktopServices.openUrl(
                            QUrl.fromLocalFile(
                                os.path.abspath(os.fspath(caminho)))))
                msg.layout().insertWidget(1, btn_pasta)

            # botão para abrir arquivo (opcional)
            if caminho_arquivo:
                btn_exec = QPushButton(self.tr("Abrir Arquivo"))
                btn_exec.clicked.connect(
                    lambda _checked=False, caminho=caminho_arquivo:
                        QDesktopServices.openUrl(
                            QUrl.fromLocalFile(
                                os.path.abspath(os.fspath(caminho)))))
                msg.layout().insertWidget(2, btn_exec)

            # mostra o widget e guarda referência
            self._widget_msg_sucesso = bar.pushWidget(msg, level=Qgis.MessageLevel.Info, duration=duracao)

    def configure_raster_list_dragdrop(self):
        """Permite reordenar os rasters no listWidgetRaster com o mouse."""
        self.listWidgetRaster.setDragEnabled(True)
        self.listWidgetRaster.setAcceptDrops(True)
        self.listWidgetRaster.setDropIndicatorShown(True)
        self.listWidgetRaster.setDefaultDropAction(Qt.DropAction.MoveAction)
        self.listWidgetRaster.setDragDropMode(QAbstractItemView.DragDropMode.InternalMove)
        self.listWidgetRaster.setSelectionMode(QAbstractItemView.SelectionMode.SingleSelection)

        self.listWidgetRaster.model().rowsMoved.connect(self.on_raster_rows_moved)

    def sync_selected_raster_layers_with_list_order(self):
        """
        Recria self.selected_raster_layers seguindo a ordem visual do listWidgetRaster.
        Funciona bem se os nomes das camadas forem únicos.
        """
        ordered_layers = []

        for i in range(self.listWidgetRaster.count()):
            item = self.listWidgetRaster.item(i)

            # ignora cabeçalho ou itens não checkáveis
            if not (item.flags() & Qt.ItemFlag.ItemIsUserCheckable):
                continue

            if item.checkState() != Qt.CheckState.Checked:
                continue

            layers = QgsProject.instance().mapLayersByName(item.text())
            if layers:
                ordered_layers.append(layers[0])

        self.selected_raster_layers = ordered_layers

    def sort_all_profiles_by_list_order(self):
        """Reordena self.all_profiles para seguir a ordem visual do listWidgetRaster."""
        order_map = {}

        pos = 0
        for i in range(self.listWidgetRaster.count()):
            item = self.listWidgetRaster.item(i)

            if not (item.flags() & Qt.ItemFlag.ItemIsUserCheckable):
                continue

            order_map[item.text()] = pos
            pos += 1

        self.all_profiles.sort(
            key=lambda profile_data: order_map.get(profile_data['layer'].name(), 999999))

    def on_checkBoxHachura_state_changed(self, state):
        """Aplica/remove a hachura apenas se houver gráfico principal carregado."""
        if not hasattr(self, "plot_widget") or self.plot_widget is None:
            return

        if not getattr(self, "all_profiles", None):
            # Sem gráfico/perfil: não deixa o checkbox ficar ativo
            self.checkBoxHachura.blockSignals(True)
            self.checkBoxHachura.setChecked(False)
            self.checkBoxHachura.blockSignals(False)
            return

        self.plot_profiles()

    def _is_web_imagery_raster(self, layer):
        """
        Retorna True para rasters que aparentam ser basemap/imagem de provedor web
        (Google, Bing, Esri, XYZ/WMS/WMTS, etc.).
        """
        if not isinstance(layer, QgsRasterLayer):
            return False

        try:
            provider = (layer.providerType() or "").strip().lower()
            source = (layer.source() or "").strip().lower()
            name = (layer.name() or "").strip().lower()
        except Exception:
            return False

        combined = f"{name} | {source}"

        # nomes/fontes típicos de basemap/imagem
        imagery_tokens = (
            "google", "google earth", "bing",
            "esri", "arcgis", "world imagery",
            "satellite", "satelite", "imagery",
            "hybrid", "roadmap", "terrain",
            "mapbox", "cartodb", "openstreetmap", "osm",
            "basemap", "base map")

        if any(token in combined for token in imagery_tokens):
            return True

        # Em QGIS, camadas XYZ costumam vir como raster com provider "wms"
        if provider == "wms":
            service_tokens = (
                "type=xyz",
                "service=wms",
                "service=wmts",
                "tilematrixset",
                "contextualwmslegend=0",
                "url=http://",
                "url=https://")
            if any(token in combined for token in service_tokens):
                return True

        return False

    def _is_profile_eligible_raster(self, layer):
        """
        Retorna True apenas para rasters adequados ao botão 'Selecionar'
        do gráfico de perfil.
        """
        if not isinstance(layer, QgsRasterLayer):
            return False

        if self._is_web_imagery_raster(layer):
            return False

        return True

    def select_all_rasters(self):
        """
        Marca apenas rasters elegíveis para perfil e ignora
        basemaps/imagens de provedores web.
        """
        selected_layers = []
        LAYER_ID_ROLE = int(Qt.ItemDataRole.UserRole) + 1

        self.listWidgetRaster.blockSignals(True)
        try:
            for i in range(self.listWidgetRaster.count()):
                item = self.listWidgetRaster.item(i)
                if not item:
                    continue

                # ignora cabeçalho / itens não checkáveis
                if not (item.flags() & Qt.ItemFlag.ItemIsUserCheckable):
                    continue

                layer_id = item.data(LAYER_ID_ROLE)
                layer = QgsProject.instance().mapLayer(layer_id) if layer_id else None

                if self._is_profile_eligible_raster(layer):
                    item.setCheckState(Qt.CheckState.Checked)
                    selected_layers.append(layer)
                else:
                    item.setCheckState(Qt.CheckState.Unchecked)
        finally:
            self.listWidgetRaster.blockSignals(False)

        self.selected_raster_layers = selected_layers
        self.selected_raster_layer = selected_layers[0] if selected_layers else None

        self.update_checkboxes_state()
        # Pisca os checkboxes de linha apenas como dica visual
        self._maybe_blink_line_checkboxes_after_select()

        # Se já houver uma linha válida, recalcula o perfil com os rasters elegíveis
        if self.line_tool and getattr(self.line_tool, "points", None):
            self.extract_profile(self.line_tool.points)
        elif getattr(self, "line_points", None):
            self.extract_profile(self.line_points)

    def _create_raster_header_item(self):
        """Cria o item de cabeçalho fixo do listWidgetRaster."""
        header_item = QListWidgetItem(self.tr("Camadas Rasters"))
        header_item.setTextAlignment(Qt.AlignmentFlag.AlignCenter)
        header_item.setFlags(Qt.ItemFlag.NoItemFlags)
        header_item.setBackground(QColor(200, 200, 200))
        return header_item

    def _ensure_raster_header_first(self):
        """
        Garante que o cabeçalho 'Camadas Rasters' permaneça sempre na primeira linha.
        """
        if self.listWidgetRaster.count() == 0:
            self.listWidgetRaster.addItem(self._create_raster_header_item())
            return

        header_item = None

        for i in range(self.listWidgetRaster.count()):
            item = self.listWidgetRaster.item(i)
            if not item:
                continue

            # Cabeçalho = item não checkável com o texto esperado
            if (item.text() == self.tr("Camadas Rasters") and
                not (item.flags() & Qt.ItemFlag.ItemIsUserCheckable)):
                header_item = self.listWidgetRaster.takeItem(i)
                break

        if header_item is None:
            header_item = self._create_raster_header_item()

        # Reforça a configuração visual/funcional do cabeçalho
        header_item.setText(self.tr("Camadas Rasters"))
        header_item.setTextAlignment(Qt.AlignmentFlag.AlignCenter)
        header_item.setFlags(Qt.ItemFlag.NoItemFlags)
        header_item.setBackground(QColor(200, 200, 200))

        # Reinsere sempre o próprio cabeçalho na posição 0
        self.listWidgetRaster.insertItem(0, header_item)

        # Força atualização visual
        self.listWidgetRaster.viewport().update()

    def on_raster_rows_moved(self, parent, start, end, destination, row):
        """Atualiza a ordem interna após mover itens no listWidgetRaster."""
        self._ensure_raster_header_first()

        self.sync_selected_raster_layers_with_list_order()
        self.sort_all_profiles_by_list_order()

        if self.all_profiles:
            self.plot_profiles()

        self.update_combobox_raster_list()

    def reset_profile_view(self):
        """Limpa gráficos, linha temporária, destaques e seleções do listWidgetRaster."""
        # 1) Limpa seleção dos rasters
        self.listWidgetRaster.blockSignals(True)
        try:
            for i in range(self.listWidgetRaster.count()):
                item = self.listWidgetRaster.item(i)
                if not item:
                    continue
                if item.flags() & Qt.ItemFlag.ItemIsUserCheckable:
                    item.setCheckState(Qt.CheckState.Unchecked)
        finally:
            self.listWidgetRaster.blockSignals(False)

        self.selected_raster_layers = []
        self.selected_raster_layer = None

        # 2) Limpa o gráfico principal
        if hasattr(self, 'plot_widget') and self.plot_widget is not None:
            self.plot_widget.clear()

        # 3) Limpa tabela e segundo gráfico
        self.reset_table_and_graph()

        # 4) Remove marcador do mapa
        self.remove_map_marker()

        # 5) Remove linha temporária / rubber band do mapa
        if self.line_tool:
            try:
                if hasattr(self.line_tool, "points"):
                    self.line_tool.points = []
                if hasattr(self.line_tool, "is_drawing"):
                    self.line_tool.is_drawing = False
                if hasattr(self.line_tool, "rubber_band") and self.line_tool.rubber_band:
                    self.line_tool.rubber_band.reset(Qgis.GeometryType.Line)
            except Exception:
                pass  # nosec B110

        self.deactivate_line_tool()
        self.deactivate_line_layer_tool()
        self.clear_rubber_band()

        # 6) Limpa destaque do segmento no mapa
        if self.highlighted_map_segment:
            try:
                iface.mapCanvas().scene().removeItem(self.highlighted_map_segment)
            except Exception:
                pass  # nosec B110
            self.highlighted_map_segment = None

        # 7) Limpa texto de inclinação no mapa
        self.clear_inclination_text_on_map()

        # 8) Esconde tooltip de inclinação, se existir
        if hasattr(self, 'inclination_tooltip') and self.inclination_tooltip:
            self.inclination_tooltip.hide()

        # 9) Esconde tooltip de cotas, se existir
        self.hide_tooltip()

        # 10) Reseta estados internos do perfil
        self.line_points = []
        self.line_distances = []
        self.current_x_values = []
        self.current_y_values = []
        self.all_profiles = []

        self.current_line_layer = None
        self.current_line_feature = None

        # 11) Reseta combo/listas auxiliares
        self.update_combobox_raster_list()
        self.reset_comboboxes()

        # 12) Reseta alguns checkboxes ligados ao gráfico/perfil
        self.checkBoxLinha.setChecked(False)
        self.checkBoxLinha2.setChecked(False)
        self.checkBox_Cotas.setChecked(False)

        # 13) Reseta o spinBoxPontos para o valor padrão
        self.spinBoxPontos.blockSignals(True)
        self.spinBoxPontos.setValue(self.default_spinBoxPontos_value)
        self.spinBoxPontos.blockSignals(False)

        # Reaplica o passo correto do spin após o reset
        self.update_spinbox_pontos_step(self.spinBoxPontos.value())

        if hasattr(self, "checkBoxHachura"):
            self.checkBoxHachura.setChecked(False)

        # 14) Atualiza estado geral da interface
        self.update_checkboxes_state()
        self.update_export_button_state()
        self.update_create_button_state()
        self.update_3d_button_state()

        # Pode mostrar o aviso novamente
        self._perfil_msg_sem_linha_mostrada = False

    def build_default_profile_filename(self, file_extension: str) -> str:
        """
        Retorna o nome padrão do arquivo de exportação.
        - Se o perfil veio de uma camada de linha (checkBoxLinha2), usa:
            grafico_perfil_<nome_da_camada>_<ID>
          onde <ID> é o campo ID/id/Id, se existir, senão o ID interno da feição.
        - Se veio de linha temporária, usa apenas 'grafico_perfil'.
        """
        # Caso tenha camada e feição de linha armazenadas (linha de camada)
        if getattr(self, "current_line_layer", None) and getattr(self, "current_line_feature", None):
            layer_name = self.current_line_layer.name()
            feat = self.current_line_feature

            id_text = None
            field_names = feat.fields().names()

            # tenta achar um campo de ID explícito
            for fname in ("ID", "id", "Id"):
                if fname in field_names:
                    val = feat[fname]
                    if val not in (None, ""):
                        id_text = str(val)
                        break

            # se não achar, usa o ID interno da feição
            if id_text is None:
                id_text = str(feat.id())

            base = self.tr("Grafico_Perfil_{layer_name}_ID{id_text}").format(    layer_name=layer_name, id_text=id_text)
        else:
            # linha temporária
            base = "grafico_perfil"

        return base + file_extension

    def export_plot(self):
        """
        Exporta o gráfico gerado pelo plot_profiles no formato selecionado no comboBoxTipo.
        """
        if not hasattr(self, 'plot_widget') or self.plot_widget is None:
            self.mostrar_mensagem(self.tr("Nenhum gráfico para exportar."), "Erro")
            return

        selected_format = self.comboBoxTipo.currentText()

        if selected_format == self.tr("Selecione:"):
            self.mostrar_mensagem(self.tr("Por favor, selecione um formato para exportação."), "Erro")
            return

        format_mapping = {
            "*.png": ("PNG Image (*.png)", ".png"),
            "*.svg": ("SVG Image (*.svg)", ".svg"),
            "*.dxf": ("DXF Drawing (*.dxf)", ".dxf"),
            "*.tiff": ("TIFF Image (*.tiff)", ".tiff"),
            "*.jpeg": ("JPEG Image (*.jpeg *.jpg)", ".jpeg"),
            "*.pdf": ("PDF Document (*.pdf)", ".pdf")}

        file_filter, file_extension = format_mapping.get(selected_format, (self.tr("Todos os arquivos (*)"), ""))

        file_path = None

        try:
            nome_padrao = self.build_default_profile_filename(file_extension)
            file_path = self.escolher_local_para_salvar(nome_padrao, file_filter)

            if not file_path:
                return

            if file_extension and not file_path.endswith(file_extension):
                file_path += file_extension

            if selected_format == "*.png":
                self.export_plot_as_image(file_path, 'png')
            elif selected_format == "*.svg":
                self.export_plot_as_svg(file_path)
            elif selected_format == "*.tiff":
                self.export_plot_as_image(file_path, 'tiff')
            elif selected_format == "*.jpeg":
                self.export_plot_as_image(file_path, 'jpeg')
            elif selected_format == "*.pdf":
                self.export_plot_as_pdf(file_path)
            elif selected_format == "*.dxf":
                self.export_plot_as_dxf(file_path)
            else:
                self.mostrar_mensagem(self.tr("Formato de exportação não suportado."), "Erro")
                return

            self.mostrar_mensagem(self.tr("Gráfico exportado com sucesso!"), "Sucesso", caminho_pasta=os.path.dirname(file_path), caminho_arquivo=file_path)

        except Exception as e:
            self.mostrar_mensagem(self.tr("Falha ao exportar o gráfico: {error}").format(error=str(e)), "Erro")

    def exportar_eixos(self, msp, all_distances, all_values, layers_info):
        """
        Exporta os eixos (X/Y) do gráfico principal para DXF, incluindo:
        - Ticks do eixo X com unidade "m"
        - Ticks do eixo Y (tracinho vermelho)
        - Grade horizontal e vertical em cinza com 50% de transparência
        - Contorno da caixa do gráfico e legendas
        """
        # Nomes das layers do DXF traduzíveis
        layer_eixos = self.tr("Eixos")
        layer_grade_principal = self.tr("Grade_Principal")

        # Extremos do gráfico (dados)
        x_min, x_max = min(all_distances), max(all_distances)
        y_min, y_max = min(all_values), max(all_values)

        # Garante um intervalo mínimo no eixo Y para não “achatar” o desenho
        intervalo_minimo_y = 10
        intervalo_y_total = y_max - y_min
        if intervalo_y_total < intervalo_minimo_y:
            centro_y = (y_max + y_min) / 2
            y_min = centro_y - intervalo_minimo_y / 2
            y_max = centro_y + intervalo_minimo_y / 2

        # Margens em torno do gráfico (5% do tamanho do eixo, com mínimo)
        x_margin = (x_max - x_min) * 0.05
        y_margin = (y_max - y_min) * 0.05
        margem_minima = 1
        x_margin = max(x_margin, margem_minima)
        y_margin = max(y_margin, margem_minima)

        # Expande o “quadro” do gráfico
        x_min = max(0, x_min - x_margin)
        x_max += x_margin
        y_min -= y_margin
        y_max += y_margin

        # Arredonda para inteiros (DXF costuma ficar melhor “limpo” assim)
        x_min, x_max = int(x_min), int(x_max) + 1
        y_min, y_max = int(y_min), int(y_max) + 1

        # Layers base
        if layer_eixos not in msp.doc.layers:
            msp.doc.layers.new(name=layer_eixos, dxfattribs={'color': 7})  # branco/cinza claro

        # Layer da grade (principal)
        if layer_grade_principal not in msp.doc.layers:
            msp.doc.layers.new(name=layer_grade_principal, dxfattribs={'color': 8})  # cinza

        # Fonte
        if 'Arial' not in msp.doc.styles:
            msp.doc.styles.new('Arial', dxfattribs={'font': 'arial.ttf'})

        # Altura do texto baseada no tamanho do gráfico
        base_text_height = min((x_max - x_min), (y_max - y_min)) * 0.025
        if base_text_height < 0.1:
            base_text_height = 0.1

        # Cor cinza “real” (true_color) + transparência 50%
        cinza = (128 << 16) | (128 << 8) | 128  # 0x808080
        transparencia_50 = 0.5

        # EIXO X + GRADE VERTICAL
        intervalo_x = max(1, (x_max - x_min) // 10)
        x_ticks = list(range(x_min, x_max, intervalo_x))

        for x in x_ticks:
            # Tick do eixo X (pequena linha vertical no eixo)
            msp.add_line(
                (x, y_min - y_margin * 0.3),
                (x, y_min + y_margin * 0.3),
                dxfattribs={'layer': layer_eixos})

            # Grade vertical “saindo do eixo X” (de y_min até y_max)
            if x != x_min:
                vln = msp.add_line(
                    (x, y_min),
                    (x, y_max),
                    dxfattribs={'layer': layer_grade_principal, 'true_color': cinza}
                )
                try:
                    vln.transparency = transparencia_50
                except Exception:
                    vln.dxf.transparency = 0x02000080  # fallback raw (~50%)

            # Rótulo do eixo X com unidade
            msp.add_text(f"{x} m", dxfattribs={
                'height': base_text_height,
                'layer': layer_eixos,
                'insert': (x, y_min - y_margin * 1.5),
                'rotation': 0,
                'style': 'Arial'})

        # EIXO Y + GRADE HORIZONTAL
        intervalo_y_axis = max(1, (y_max - y_min) // 10)
        y_ticks = list(range(y_min, y_max, intervalo_y_axis))

        # Texto do Y à esquerda do tick vermelho
        margem_fixa_x = x_min - x_margin * 0.25

        # Linha horizontal deve iniciar na ponta direita do “tracinho vermelho”
        x_inicio_grade = x_min + x_margin * 0.075

        for y in y_ticks:
            # “Tracinho vermelho” do eixo Y
            msp.add_line(
                (x_min - x_margin * 0.075, y),
                (x_min + x_margin * 0.075, y),
                dxfattribs={'layer': layer_eixos, 'color': 1})

            # Rótulo do eixo Y
            msp.add_text(f"{y}", dxfattribs={
                'height': base_text_height,
                'layer': layer_eixos,
                'insert': (margem_fixa_x, y),
                'rotation': 0,
                'style': 'Arial'})

            # Grade horizontal: do fim do tick vermelho até o lado oposto da caixa (x_max)
            if y != y_min:
                hln = msp.add_line(
                    (x_inicio_grade, y),
                    (x_max, y),
                    dxfattribs={'layer': layer_grade_principal, 'true_color': cinza})
                try:
                    hln.transparency = transparencia_50
                except Exception:
                    hln.dxf.transparency = 0x02000080  # fallback raw (~50%)

        # Caixa do gráfico (retângulo)
        msp.add_lwpolyline([
            (x_min, y_min),
            (x_max, y_min),
            (x_max, y_max),
            (x_min, y_max),
            (x_min, y_min)
        ], dxfattribs={'layer': layer_eixos}, close=True)

        # Legendas das camadas
        self.adicionar_legendas_camadas(
            msp,
            layers_info,
            x_min,
            x_max,
            y_max,
            y_margin,
            base_text_height,
            layer_eixos)

        return x_min, y_min

    def export_plot_as_dxf(self, file_path):
        """
        Exporta o gráfico principal como DXF.
        """
        if not hasattr(self, 'plot_widget') or self.plot_widget is None:
            raise ValueError(self.tr("Nenhum gráfico disponível para exportar."))

        doc = ezdxf.new(dxfversion='R2010')
        msp = doc.modelspace()

        all_distances = []
        all_values = []
        layers_info = []
        plot_items = []
        hatch_items = []

        for item in self.plot_widget.plotItem.items:
            if not isinstance(item, pg.PlotDataItem):
                continue

            x_data = item.xData
            y_data = item.yData

            if x_data is None or y_data is None or len(x_data) == 0 or len(y_data) == 0:
                continue

            layer_name = item.name() or self.tr("Perfil")

            list_item = self.get_list_item_by_layer_name(layer_name)
            if list_item:
                color = QColor(list_item.data(Qt.ItemDataRole.UserRole))
            else:
                color = QColor(Qt.GlobalColor.blue)

            true_color = (color.red() << 16) | (color.green() << 8) | color.blue()

            safe_layer_name = re.sub(r'[<>/\\:";?*|=,]+', '_', str(layer_name)).strip() or self.tr("Perfil")
            safe_layer_name = safe_layer_name[:255]

            if safe_layer_name not in doc.layers:
                doc.layers.new(name=safe_layer_name, dxfattribs={'color': 7})

            points = [
                (float(x), float(y))
                for x, y in zip(x_data, y_data)
                if x is not None and y is not None and not np.isnan(float(y))]

            if len(points) < 2:
                continue

            msp.add_lwpolyline(
                points,
                dxfattribs={
                    'true_color': true_color,
                    'layer': safe_layer_name})

            all_distances.extend([p[0] for p in points])
            all_values.extend([p[1] for p in points])
            layers_info.append((layer_name, true_color))
            plot_items.append(points)
            hatch_items.append((points, safe_layer_name, color))

        if not plot_items or not all_distances or not all_values:
            raise ValueError(self.tr("Nenhum dado encontrado no gráfico para exportar."))

        # Exporta a hachura/preenchimento abaixo dos perfis, quando ativada
        if self.checkBoxHachura.isChecked():
            fill_level = min(all_values)

            for points, safe_layer_name, color in hatch_items:
                if len(points) < 2:
                    continue

                hatch_points = [(points[0][0], fill_level)]
                hatch_points.extend(points)
                hatch_points.append((points[-1][0], fill_level))

                hatch = msp.add_hatch(color=7, dxfattribs={'layer': safe_layer_name})
                hatch.set_solid_fill(color=7, rgb=(color.red(), color.green(), color.blue()))
                hatch.transparency = 0.5
                hatch.paths.add_polyline_path(hatch_points, is_closed=True)

        self.exportar_eixos(msp, all_distances, all_values, layers_info)

        doc.saveas(file_path)

    def adicionar_legendas_camadas(self, msp, layers_info, x_min, x_max, y_max, y_margin, base_text_height, layer_eixos, modo_segundo=False):
        # Mantém o comportamento original no gráfico principal
        if not modo_segundo:
            legend_y = y_max + y_margin
            x_pos = x_min
            spacing = (x_max - x_min) * 0.1 if (x_max - x_min) * 0.1 > 5 else 5
            line_length = (x_max - x_min) * 0.05 if (x_max - x_min) * 0.05 > 2 else 2

            for layer_name, true_color in layers_info:
                msp.add_line((x_pos, legend_y), (x_pos + line_length, legend_y), dxfattribs={'true_color': true_color, 'layer': layer_eixos})

                msp.add_text(layer_name, dxfattribs={
                    'height': base_text_height,
                    'layer': layer_eixos,
                    'insert': (x_pos + line_length + 1, legend_y),
                    'rotation': 0,
                    'style': 'Arial'})

                x_pos += line_length + len(layer_name) * 2 + spacing

            return

        # Gráfico 2: legenda compacta, próxima da moldura e alinhada à esquerda
        legend_y = y_max + max(y_margin * 0.25, base_text_height * 0.8)
        line_length = max(base_text_height * 4, 2)
        gap = base_text_height * 1.2
        left_margin = base_text_height * 2

        x_pos = x_min + left_margin

        for layer_name, true_color in layers_info:
            texto_legenda = self.tr("Perfil: {layer_name}").format(layer_name=layer_name)

            line_start_x = x_pos
            line_end_x = line_start_x + line_length
            text_x = line_end_x + gap

            msp.add_line(
                (line_start_x, legend_y),
                (line_end_x, legend_y),
                dxfattribs={
                    'true_color': true_color,
                    'layer': layer_eixos})

            msp.add_text(texto_legenda, dxfattribs={
                'height': base_text_height,
                'layer': layer_eixos,
                'insert': (text_x, legend_y),
                'rotation': 0,
                'style': 'Arial',
                'color': 7})

            x_pos = text_x + len(texto_legenda) * base_text_height * 0.65 + base_text_height * 3

    def export_plot_as_pdf(self, file_path):
        """
        Exporta o gráfico como um arquivo PDF com uma margem fixa de 2 metros nos eixos X e Y.
        Inclui a hachura abaixo do perfil quando checkBoxHachura estiver ativo.
        """
        if not hasattr(self, 'plot_widget') or not self.plot_widget:
            raise ValueError(self.tr("Nenhum gráfico disponível para exportar."))

        # Obtém todos os itens do gráfico para extrair os dados
        x_data_all = []
        y_data_all = []
        plot_items = []

        for item in self.plot_widget.plotItem.items:
            if isinstance(item, pg.PlotDataItem):
                x_data, y_data = item.xData, item.yData

                if x_data is None or y_data is None:
                    continue

                x_data_all.extend(x_data)
                y_data_all.extend(y_data)

                layer_name = item.name() or ""

                # Tenta obter a cor da camada a partir do listWidgetRaster
                list_item = self.get_list_item_by_layer_name(layer_name)
                if list_item:
                    qcolor = QColor(list_item.data(Qt.ItemDataRole.UserRole))
                else:
                    qcolor = QColor(0, 0, 255)

                mpl_color = (
                    qcolor.red() / 255.0,
                    qcolor.green() / 255.0,
                    qcolor.blue() / 255.0)

                plot_items.append((x_data, y_data, layer_name, mpl_color))

        if not x_data_all or not y_data_all:
            raise ValueError(self.tr("Nenhum dado encontrado no gráfico para exportar."))

        # Configura os limites dos eixos com margem fixa de 2 metros
        margin_fixed = 2
        x_min, x_max = min(x_data_all) - margin_fixed, max(x_data_all) + margin_fixed
        y_min_raw, y_max = min(y_data_all), max(y_data_all)
        y_min = y_min_raw - margin_fixed

        # Base da hachura igual ao gráfico principal
        fill_level = y_min_raw

        # Calcula a escala em metros
        x_range = x_max - x_min
        y_range = y_max - y_min
        scale_ratio = x_range / y_range if y_range != 0 else None
        scale_text = (
            self.tr(
                "Escala:\n"
                "1 unidade no eixo Y (Elevação) equivale a {scale_ratio:.2f} unidades no eixo X (Distância)"
            ).format(scale_ratio=scale_ratio)
            if scale_ratio is not None
            else self.tr("Escala: não aplicável"))

        # Cria o PDF
        with PdfPages(file_path) as pdf:
            fig, ax = plt.subplots(figsize=(12, 6))

            # Adiciona os dados ao gráfico
            for x_data, y_data, label, mpl_color in plot_items:
                # Hachura/preenchimento abaixo da curva, se ativa
                if self.checkBoxHachura.isChecked():
                    ax.fill_between(
                        x_data,
                        y_data,
                        fill_level,
                        color=mpl_color,
                        alpha=0.5)

                # Linha do perfil por cima da hachura
                ax.plot(
                    x_data,
                    y_data,
                    label=label,
                    linewidth=1.5,
                    color=mpl_color)

            # Configurações dos eixos com as margens fixas
            ax.set_xlim(x_min, x_max)
            ax.set_ylim(y_min, y_max + margin_fixed)
            ax.set_title(self.tr("Gráfico de Perfil"), fontsize=16, fontweight='bold')
            ax.set_xlabel(self.tr("Distância (m)"), fontsize=12)
            ax.set_ylabel(self.tr("Elevação (m)"), fontsize=12)

            # Grade e legenda
            ax.grid(True, linestyle='--', alpha=0.6)
            ax.legend(fontsize=10, loc="upper right")

            # Adiciona a escala no gráfico
            ax.text(
                0.98, 0.02, scale_text,
                fontsize=10, color='gray', ha='right', va='bottom',
                transform=ax.transAxes)

            pdf.savefig(fig, bbox_inches='tight')
            plt.close(fig)

    def export_plot_as_image(self, file_path, image_format):
        """
        Exporta o gráfico como uma imagem nos formatos PNG, TIFF ou JPEG.
        :param file_path: Caminho completo do arquivo para salvar.
        :param image_format: Formato da imagem ('png', 'tiff', 'jpeg').
        """
        exporter = pg.exporters.ImageExporter(self.plot_widget.plotItem)
        exporter.parameters()['width'] = 1920  # Ajusta a largura em pixels
        exporter.export(file_path)

    def export_plot_as_svg(self, file_path):
        """
        Exporta o gráfico como um arquivo SVG.
        :param file_path: Caminho completo do arquivo para salvar.
        """
        exporter = pg.exporters.SVGExporter(self.plot_widget.plotItem)
        exporter.export(file_path)

    def update_export_button_state(self):
        """
        Atualiza o estado (ativado/desativado) dos botões de exportação:
        - pushButtonExportar   -> gráfico 1
        - pushButtonExportar_2 -> gráfico 2
        """
        selected_format = self.comboBoxTipo.currentText()
        selected_format_2 = self.comboBoxTipo_2.currentText()

        # Gráfico 1: depende dos perfis carregados
        has_graph_1 = bool(getattr(self, 'all_profiles', None))

        # Gráfico 2: depende dos vetores de dados realmente montados
        has_graph_2 = (
            hasattr(self, 'graph_x_data') and
            hasattr(self, 'graph_y_data') and
            len(self.graph_x_data) >= 2 and
            len(self.graph_y_data) >= 2)

        enable_export_1 = has_graph_1 and selected_format != self.tr("Selecione:")
        enable_export_2 = has_graph_2 and selected_format_2 != self.tr("Selecione:")

        self.pushButtonExportar.setEnabled(bool(enable_export_1))
        self.pushButtonExportar_2.setEnabled(bool(enable_export_2))
    
    def on_export_button_clicked(self):
        """
        Executa a lógica de exportação ao clicar no botão Exportar.
        """
        try:
            self.exportar_grafico()
        except Exception as e:
            self.mostrar_mensagem(self.tr("Erro ao exportar gráfico: {error}").format(error=str(e)), "Erro")

    def export_second_graph(self):
        """
        Exporta o segundo gráfico no formato selecionado no comboBoxTipo_2.
        """
        # Verifica se o segundo gráfico existe
        if not hasattr(self, 'plot_widget2') or self.plot_widget2 is None:
            self.mostrar_mensagem(self.tr("Nenhum gráfico para exportar."), "Erro")
            return

        # Obtém o formato selecionado no comboBoxTipo_2
        selected_format = self.comboBoxTipo_2.currentText()

        # Verifica se um formato válido foi selecionado
        if selected_format == self.tr("Selecione:"):
            self.mostrar_mensagem(self.tr("Por favor, selecione um formato para exportação."), "Erro")
            return

        # Define o filtro de arquivo e a extensão com base no formato selecionado
        format_mapping = {
            "*.png": ("PNG Image (*.png)", ".png"),
            "*.svg": ("SVG Image (*.svg)", ".svg"),
            "*.tiff": ("TIFF Image (*.tiff)", ".tiff"),
            "*.jpeg": ("JPEG Image (*.jpeg *.jpg)", ".jpeg"),
            "*.pdf": ("PDF Document (*.pdf)", ".pdf"),
            "*.dxf": ("DXF Drawing (*.dxf)", ".dxf"),  # Adicionando o DXF
        }
        file_filter, file_extension = format_mapping.get(selected_format, (self.tr("Todos os arquivos (*)"), ""))

        # Gera um nome padrão para o arquivo
        nome_padrao = self.tr("grafico_perfil_2") + file_extension

        # Abre a caixa de diálogo para escolher onde salvar
        file_path = self.escolher_local_para_salvar(nome_padrao, file_filter)

        # Se o usuário cancelar a ação, `file_path` será None
        if not file_path:
            return

        # Garante que o arquivo seja salvo com a extensão correta
        if not file_path.endswith(file_extension):
            file_path += file_extension

        # Exporta o gráfico no formato selecionado
        try:
            if selected_format == "*.png":
                self.export_second_graph_as_image(file_path, 'png')
            elif selected_format == "*.svg":
                self.export_second_graph_as_svg(file_path)
            elif selected_format == "*.tiff":
                self.export_second_graph_as_image(file_path, 'tiff')
            elif selected_format == "*.jpeg":
                self.export_second_graph_as_image(file_path, 'jpeg')
            elif selected_format == "*.pdf":
                self.export_second_graph_as_pdf(file_path)
            elif selected_format == "*.dxf":
                self.export_second_graph_as_dxf(file_path)
            else:
                self.mostrar_mensagem(self.tr("Formato de exportação não suportado."), "Erro")
                return

            # Mostra uma mensagem de sucesso com o botão para abrir o arquivo ou a pasta
            self.mostrar_mensagem(self.tr("Gráfico exportado com sucesso!"), "Sucesso", caminho_pasta=os.path.dirname(file_path), caminho_arquivo=file_path)
        except Exception as e:
            self.mostrar_mensagem(self.tr("Falha ao exportar o gráfico: {error}").format(error=str(e)), "Erro")

    def export_second_graph_as_image(self, file_path, image_format):
        """
        Exporta o segundo gráfico como uma imagem nos formatos PNG, TIFF ou JPEG.
        :param file_path: Caminho completo do arquivo para salvar.
        :param image_format: Formato da imagem ('png', 'tiff', 'jpeg').
        """
        exporter = pg.exporters.ImageExporter(self.plot_widget2.plotItem)
        exporter.parameters()['width'] = 1920  # Ajusta a largura em pixels
        exporter.export(file_path)

    def export_second_graph_as_svg(self, file_path):
        """
        Exporta o segundo gráfico como um arquivo SVG.
        :param file_path: Caminho completo do arquivo para salvar.
        """
        exporter = pg.exporters.SVGExporter(self.plot_widget2.plotItem)
        exporter.export(file_path)

    def export_second_graph_as_pdf(self, file_path):
        """
        Exporta o segundo gráfico como um arquivo PDF.
        :param file_path: Caminho completo do arquivo para salvar.
        """
        if not hasattr(self, 'plot_widget2') or not self.plot_widget2:
            raise ValueError(self.tr("Nenhum gráfico disponível para exportar."))

        # Obtém todos os itens do gráfico para extrair os dados
        x_data_all = []
        y_data_all = []
        plot_items = []

        for item in self.plot_widget2.plotItem.items:
            if isinstance(item, pg.PlotDataItem):
                x_data, y_data = item.xData, item.yData
                x_data_all.extend(x_data)
                y_data_all.extend(y_data)
                plot_items.append((x_data, y_data, item.name()))

        if not x_data_all or not y_data_all:
            raise ValueError(self.tr("Nenhum dado encontrado no gráfico para exportar."))

        # Configura os limites dos eixos com margem fixa de 2 metros
        margin_fixed = 2  # Margem fixa em metros
        x_min, x_max = min(x_data_all) - margin_fixed, max(x_data_all) + margin_fixed
        y_min, y_max = min(y_data_all) - margin_fixed, max(y_data_all) + margin_fixed

        # Calcula a escala em metros
        x_range = x_max - x_min
        y_range = y_max - y_min
        scale_ratio = x_range / y_range if y_range != 0 else None
        scale_text = (
            self.tr(
                "Escala:\n"
                "1 unidade no eixo Y (Elevação) equivale a {scale_ratio:.2f} unidades no eixo X (Distância)"
            ).format(scale_ratio=scale_ratio)
            if scale_ratio is not None
            else self.tr("Escala: não aplicável"))

        # Cria o PDF
        with PdfPages(file_path) as pdf:
            # Cria uma nova figura do matplotlib com layout horizontal maior
            fig, ax = plt.subplots(figsize=(12, 6))  # Largura maior para layout estendido

            # Adiciona os dados ao gráfico
            for x_data, y_data, label in plot_items:
                ax.plot(x_data, y_data, label=label, linewidth=1.5)

            # Configurações dos eixos com as margens fixas
            ax.set_xlim(x_min, x_max)
            ax.set_ylim(y_min, y_max)
            ax.set_title(self.tr("Perfil de Terreno Amostrado"), fontsize=16, fontweight="bold")
            ax.set_xlabel(self.tr("Distância Acumulada (m)"), fontsize=12)
            ax.set_ylabel(self.tr("Elevação (m)"), fontsize=12)

            # Grade e legenda
            ax.grid(True, linestyle='--', alpha=0.6)
            ax.legend(fontsize=10, loc="upper right")

            # Adiciona a escala no gráfico
            ax.text(0.98, 0.02, scale_text, fontsize=10, color='gray', ha='right', va='bottom', transform=ax.transAxes)

            # Adiciona o gráfico ao PDF
            pdf.savefig(fig, bbox_inches='tight')
            plt.close(fig)

    def export_second_graph_as_dxf(self, file_path):
        """
        Exporta o segundo gráfico como um arquivo DXF.
        :param file_path: Caminho completo do arquivo para salvar.
        """
        if not self.graph_x_data or not self.graph_y_data:
            raise ValueError(self.tr("Nenhum dado disponível para exportar em DXF."))

        doc = ezdxf.new(dxfversion='R2010')
        msp = doc.modelspace()

        # Configurações de estilo e escala
        x_data = self.graph_x_data
        y_data = self.graph_y_data
        x_min, x_max = min(x_data), max(x_data)
        y_min, y_max = min(y_data), max(y_data)

        # Cor do gráfico
        color = QColor(Qt.GlobalColor.red)  # Cor padrão
        selected_raster_name = self.comboBoxListaRaster.currentText()
        if selected_raster_name != self.tr("Nenhuma camada exibida"):
            for i in range(self.listWidgetRaster.count()):
                item = self.listWidgetRaster.item(i)
                if item.text() == selected_raster_name:
                    color = item.data(Qt.ItemDataRole.UserRole)
                    break

        true_color = (color.red() << 16) | (color.green() << 8) | color.blue()

        # Criar camada no DXF para o gráfico
        layer_name = self.tr("Perfil_Terreno_Amostrado")
        if layer_name not in doc.layers:
            doc.layers.new(name=layer_name, dxfattribs={'color': 7})

        # Adicionar os pontos do gráfico como uma linha poligonal
        graph_segments = getattr(self, "graph_segments", [])

        if graph_segments:
            for segment_x, segment_y in graph_segments:
                points = [(float(x), float(y))
                    for x, y in zip(segment_x, segment_y)]

                if len(points) >= 2:
                    msp.add_lwpolyline(points, dxfattribs={"true_color": true_color, "layer": layer_name})
        else:
            points = [(float(x), float(y))
                for x, y in zip(x_data, y_data)]

            if len(points) >= 2:
                msp.add_lwpolyline(points, dxfattribs={"true_color": true_color, "layer": layer_name})

        # Exportar eixos e informações no gráfico
        layers_info = [(selected_raster_name, true_color)]
        self.exportar_eixos_segundo(msp, x_data, y_data, layers_info)

        # Salvar o arquivo DXF
        doc.saveas(file_path)

    def desenhar_retangulo_eixo_x(self, msp, x_min, x_max, y_min, y_margin, base_text_height):
        """
        Desenha um retângulo ao redor dos valores do eixo X com a mesma extensão do contorno do eixo
        e posiciona o texto "Distâncias" mais à esquerda do retângulo.
        :param msp: ModelSpace do DXF.
        :param x_min: Limite mínimo do eixo X.
        :param x_max: Limite máximo do eixo X.
        :param y_min: Valor mínimo do eixo Y (já com margens aplicadas).
        :param y_margin: Margem vertical calculada.
        :param base_text_height: Altura base do texto para escalonamento.
        """
        layer_eixos_segundo = self.tr("Eixos_Segundo")

        # Garante que a layer exista no DXF
        if layer_eixos_segundo not in msp.doc.layers:
            msp.doc.layers.new(name=layer_eixos_segundo, dxfattribs={'color': 7})

        # Garante que a fonte exista
        if 'Arial' not in msp.doc.styles:
            msp.doc.styles.new('Arial', dxfattribs={'font': 'arial.ttf'})

        # Define a altura do retângulo ao redor dos valores do eixo X
        rect_bottom = y_min - y_margin * 2
        rect_top = y_min - y_margin * 0.5

        # Desenha o retângulo com a mesma extensão do contorno do eixo
        msp.add_lwpolyline([
            (x_min, rect_bottom),
            (x_max, rect_bottom),
            (x_max, rect_top),
            (x_min, rect_top),
            (x_min, rect_bottom)
        ], dxfattribs={'layer': layer_eixos_segundo}, close=True)

        # Adiciona o texto "Distâncias" à esquerda do retângulo
        text_x = x_min - base_text_height * 10
        text_y = (rect_bottom + rect_top) / 2.0

        msp.add_text(self.tr("Distâncias (m)"), dxfattribs={
            'height': base_text_height,
            'layer': layer_eixos_segundo,
            'insert': (text_x, text_y),
            'rotation': 0,
            'style': 'Arial'})

    def exportar_eixos_segundo(self, msp, x_data, y_data, layers_info):
        """
        Adiciona os eixos X e Y ao gráfico secundário exportado para DXF, garantindo que a extensão do eixo X
        cubra toda a linha do gráfico com base em x_data, adicionando uma margem antes do 0, e ao final desenha
        um retângulo com o texto "Distâncias".
        """
        layer_eixos_segundo = self.tr("Eixos_Segundo")
        layer_grade_segundo = self.tr("Grade_Segundo")

        x_min_real, x_max_real = min(x_data), max(x_data)
        y_min, y_max = min(y_data), max(y_data)

        intervalo_minimo_y = 10
        intervalo_y = y_max - y_min
        if intervalo_y < intervalo_minimo_y:
            centro_y = (y_max + y_min) / 2
            y_min = centro_y - intervalo_minimo_y / 2
            y_max = centro_y + intervalo_minimo_y / 2

        x_margin = (x_max_real - x_min_real) * 0.05
        y_margin = (y_max - y_min) * 0.05
        margem_minima = 1
        x_margin = max(x_margin, margem_minima)
        y_margin = max(y_margin, margem_minima)

        extra_margin_x = 5
        x_min = max(-extra_margin_x, x_min_real - x_margin)
        x_max = x_max_real + x_margin
        y_min -= y_margin
        y_max += y_margin

        x_min, x_max = int(x_min), int(x_max) + 1
        y_min, y_max = int(y_min), int(y_max) + 1

        # Layers do DXF
        if layer_eixos_segundo not in msp.doc.layers:
            msp.doc.layers.new(name=layer_eixos_segundo, dxfattribs={'color': 7})

        if layer_grade_segundo not in msp.doc.layers:
            msp.doc.layers.new(name=layer_grade_segundo, dxfattribs={'color': 8})

        # Fonte
        if 'Arial' not in msp.doc.styles:
            msp.doc.styles.new('Arial', dxfattribs={'font': 'arial.ttf'})

        base_text_height = min((x_max - x_min), (y_max - y_min)) * 0.025
        if base_text_height < 0.1:
            base_text_height = 0.1

        x_spacing = int(self.doubleSpinBox_espaco.value())
        if x_spacing <= 0:
            x_spacing = int(max(1, (x_max_real - x_min_real) // 10))

        x_ticks = list(range(int(x_min_real), int(x_max_real), x_spacing))
        if x_max_real not in x_ticks:
            x_ticks.append(x_max_real)

        # Desenho dos ticks do eixo X e linhas verticais
        for x in x_ticks:
            # Linha vertical até a linha do gráfico, se existir ponto exato
            if x in x_data:
                y_value = y_data[x_data.index(x)]
                msp.add_line(
                    (x, y_min),
                    (x, y_value),
                    dxfattribs={
                        'color': 3,
                        'layer': layer_eixos_segundo})

            # Tick do eixo X
            msp.add_line(
                (x, y_min - y_margin * 0.3),
                (x, y_min + y_margin * 0.3),
                dxfattribs={'layer': layer_eixos_segundo})

            # Texto do eixo X
            msp.add_text(f"{x}", dxfattribs={
                'height': base_text_height,
                'layer': layer_eixos_segundo,
                'insert': (x, y_min - y_margin * 1.5),
                'rotation': 0,
                'style': 'Arial'})

        intervalo_y_axis = max(1, (y_max - y_min) // 10)
        y_ticks = list(range(y_min, y_max, intervalo_y_axis))

        cinza = (128 << 16) | (128 << 8) | 128  # 0x808080

        # Ajustes fixos visuais para eixo Y
        tick_half = max(base_text_height * 1.2, 0.8)
        label_gap = max(base_text_height * 3.2, 2.0)
        title_gap = max(base_text_height * 1.0, 1.0)

        tick_x1 = x_min - tick_half
        tick_x2 = x_min + tick_half
        x_inicio_grade = tick_x2
        margem_fixa_x = x_min - label_gap

        for y in y_ticks:
            # Tracinho vermelho do eixo Y com tamanho fixo
            msp.add_line(
                (tick_x1, y),
                (tick_x2, y),
                dxfattribs={
                    'layer': layer_eixos_segundo,
                    'color': 1})

            # Rótulo do eixo Y em posição visual mais fixa
            msp.add_text(f"{y}", dxfattribs={
                'height': base_text_height,
                'layer': layer_eixos_segundo,
                'insert': (margem_fixa_x, y - base_text_height * 0.35),
                'rotation': 0,
                'style': 'Arial',
                'color': 7})

            # Grade horizontal cinza
            if y != y_min:
                grade_ln = msp.add_line(
                    (x_inicio_grade, y),
                    (x_max, y),
                    dxfattribs={
                        'layer': layer_grade_segundo,
                        'true_color': cinza})

                try:
                    grade_ln.transparency = 0.5
                except Exception:
                    grade_ln.dxf.transparency = 0x02000080

        # Título vertical do eixo Y
        titulo_elev_x = margem_fixa_x - title_gap
        titulo_elev_y = (y_min + y_max) / 2.0

        msp.add_text(self.tr("Elevação (m)"), dxfattribs={
            'height': base_text_height,
            'layer': layer_eixos_segundo,
            'insert': (titulo_elev_x, titulo_elev_y),
            'rotation': 90,
            'style': 'Arial',
            'color': 7})

        # Caixa do gráfico
        msp.add_lwpolyline([
            (x_min, y_min),
            (x_max, y_min),
            (x_max, y_max),
            (x_min, y_max),
            (x_min, y_min)
        ], dxfattribs={'layer': layer_eixos_segundo}, close=True)

        self.adicionar_legendas_camadas(
            msp,
            layers_info,
            x_min,
            x_max,
            y_max,
            y_margin,
            base_text_height,
            layer_eixos_segundo,
            modo_segundo=True)

        # Retângulo envolvendo os valores do eixo X
        self.desenhar_retangulo_eixo_x(
            msp,
            x_min,
            x_max,
            y_min,
            y_margin,
            base_text_height)

        # Retângulo de Elevação
        self.desenhar_retangulo_elevacao(
            msp,
            x_min,
            x_max,
            y_min,
            y_margin,
            base_text_height)

        # Retângulo de Inclinação
        self.desenhar_retangulo_inclinacao(
            msp,
            x_min,
            x_max,
            y_min,
            y_margin,
            base_text_height)

        # Retângulo de Desnível
        self.desenhar_retangulo_desnivel(
            msp,
            x_min,
            x_max,
            y_min,
            y_margin,
            base_text_height)

    def desenhar_retangulo_elevacao(self, msp, x_min, x_max, y_min, y_margin, base_text_height):
        """
        Desenha um segundo retângulo abaixo do retângulo de 'Distâncias' para exibir valores de Z
        presentes no tableWidget_Dados, e adiciona o texto 'Elevação' mais próximo do retângulo.
        """
        layer_eixos_segundo = self.tr("Eixos_Segundo")

        if layer_eixos_segundo not in msp.doc.layers:
            msp.doc.layers.new(name=layer_eixos_segundo, dxfattribs={'color': 7})

        if 'Arial' not in msp.doc.styles:
            msp.doc.styles.new('Arial', dxfattribs={'font': 'arial.ttf'})

        rect_top_elev = y_min - y_margin * 2.0
        rect_bottom_elev = y_min - y_margin * 3.5

        msp.add_lwpolyline([
            (x_min, rect_bottom_elev),
            (x_max, rect_bottom_elev),
            (x_max, rect_top_elev),
            (x_min, rect_top_elev),
            (x_min, rect_bottom_elev)
        ], dxfattribs={'layer': layer_eixos_segundo}, close=True)

        ele_text_x = x_min - base_text_height * 10
        ele_text_y = (rect_bottom_elev + rect_top_elev) / 2.0

        msp.add_text(self.tr("Elevação"), dxfattribs={
            'height': base_text_height,
            'layer': layer_eixos_segundo,
            'insert': (ele_text_x, ele_text_y),
            'rotation': 0,
            'style': 'Arial'})

        row_count = self.tableWidget_Dados.rowCount()
        col_dist = 5
        col_z = 3

        z_text_y = (rect_bottom_elev + rect_top_elev) / 2.0

        for row in range(row_count):
            distance_item = self.tableWidget_Dados.item(row, col_dist)
            z_item = self.tableWidget_Dados.item(row, col_z)

            if distance_item and z_item:
                try:
                    dist_value = float(distance_item.text())
                    z_value_text = z_item.text().strip()

                    if z_value_text.upper() == "N/A":
                        continue

                    z_value_float = float(z_value_text)
                    z_formatted = f"{z_value_float:.2f}"

                    msp.add_text(z_formatted, dxfattribs={
                        'height': base_text_height,
                        'layer': layer_eixos_segundo,
                        'insert': (dist_value, z_text_y),
                        'rotation': 0,
                        'style': 'Arial',
                        'color': 3})

                except ValueError:
                    continue

    def desenhar_retangulo_desnivel(self, msp, x_min, x_max, y_min, y_margin, base_text_height):
        """
        Desenha um retângulo para exibir valores de Desnível abaixo do retângulo de Inclinação,
        e adiciona o texto 'Desnível' à esquerda do retângulo de forma proporcional ao seu comprimento.
        """
        layer_eixos_segundo = self.tr("Eixos_Segundo")

        # Garante que a layer exista no DXF
        if layer_eixos_segundo not in msp.doc.layers:
            msp.doc.layers.new(name=layer_eixos_segundo, dxfattribs={'color': 7})

        # Garante que a fonte exista
        if 'Arial' not in msp.doc.styles:
            msp.doc.styles.new('Arial', dxfattribs={'font': 'arial.ttf'})

        rect_top_desnivel = y_min - y_margin * 5.0
        rect_bottom_desnivel = y_min - y_margin * 6.5

        msp.add_lwpolyline([
            (x_min, rect_bottom_desnivel),
            (x_max, rect_bottom_desnivel),
            (x_max, rect_top_desnivel),
            (x_min, rect_top_desnivel),
            (x_min, rect_bottom_desnivel)
        ], dxfattribs={'layer': layer_eixos_segundo}, close=True)

        # Ajuste do texto "Desnível" proporcional ao comprimento do retângulo
        desnivel_text_x = x_min - base_text_height * 10
        desnivel_text_y = (rect_bottom_desnivel + rect_top_desnivel) / 2.0

        msp.add_text(self.tr("Desnível"), dxfattribs={
            'height': base_text_height,
            'layer': layer_eixos_segundo,
            'insert': (desnivel_text_x, desnivel_text_y),
            'rotation': 0,
            'style': 'Arial'})

        # Cálculo do Desnível
        row_count = self.tableWidget_Dados.rowCount()
        col_dist = 5  # Coluna "Distância (m)"
        col_z = 3     # Coluna "Z"

        previous_z = None

        for row in range(row_count):
            distance_item = self.tableWidget_Dados.item(row, col_dist)
            z_item = self.tableWidget_Dados.item(row, col_z)

            if distance_item and z_item:
                try:
                    dist_value = float(distance_item.text())
                    z_value_text = z_item.text().strip()

                    if z_value_text.upper() == "N/A":
                        desnivel_value = "N/A"
                        previous_z = None
                    else:
                        z_value_float = float(z_value_text)

                        if previous_z is None:
                            desnivel_value = 0.0
                        else:
                            desnivel_value = z_value_float - previous_z

                        previous_z = z_value_float

                    desnivel_formatted = (
                        f"{desnivel_value:.2f}"
                        if desnivel_value != "N/A"
                        else "N/A")

                    cor_desnivel = 7

                    if desnivel_value != "N/A":
                        if desnivel_value > 0:
                            cor_desnivel = 5
                        elif desnivel_value < 0:
                            cor_desnivel = 1

                    msp.add_text(desnivel_formatted, dxfattribs={
                        'height': base_text_height,
                        'layer': layer_eixos_segundo,
                        'insert': (dist_value, desnivel_text_y),
                        'rotation': 0,
                        'style': 'Arial',
                        'color': cor_desnivel})

                except ValueError:
                    continue

    def desenhar_retangulo_inclinacao(self, msp, x_min, x_max, y_min, y_margin, base_text_height):
        """
        Desenha um terceiro retângulo encostado abaixo do retângulo de 'Elevação' para exibir valores de Inclinação (%)
        presentes no tableWidget_Dados, com posicionamento dinâmico do texto 'Inclinação' mais próximo do retângulo.
        """
        layer_eixos_segundo = self.tr("Eixos_Segundo")

        # Garante que a layer exista no DXF
        if layer_eixos_segundo not in msp.doc.layers:
            msp.doc.layers.new(name=layer_eixos_segundo, dxfattribs={'color': 7})

        # Garante que a fonte exista
        if 'Arial' not in msp.doc.styles:
            msp.doc.styles.new('Arial', dxfattribs={'font': 'arial.ttf'})

        # Coordenadas do retângulo da Inclinação encostado ao retângulo de Elevação
        rect_top_incl = y_min - y_margin * 3.5
        rect_bottom_incl = y_min - y_margin * 5.0

        # Desenha o retângulo com a mesma largura do eixo X
        msp.add_lwpolyline([
            (x_min, rect_bottom_incl),
            (x_max, rect_bottom_incl),
            (x_max, rect_top_incl),
            (x_min, rect_top_incl),
            (x_min, rect_bottom_incl)
        ], dxfattribs={'layer': layer_eixos_segundo}, close=True)

        # Ajuste dinâmico da posição do texto "Inclinação"
        incl_text_x = x_min - base_text_height * 10
        incl_text_y = (rect_bottom_incl + rect_top_incl) / 2.0

        msp.add_text(self.tr("Inclinação"), dxfattribs={
            'height': base_text_height,
            'layer': layer_eixos_segundo,
            'insert': (incl_text_x, incl_text_y),
            'rotation': 0,
            'style': 'Arial'})

        # Obtém os valores de Inclinação e suas distâncias do tableWidget_Dados
        row_count = self.tableWidget_Dados.rowCount()
        col_dist = 5  # Coluna "Distância (m)"
        col_incl = 4  # Coluna "Inclinação (%)"

        for row in range(row_count):
            distance_item = self.tableWidget_Dados.item(row, col_dist)
            incl_item = self.tableWidget_Dados.item(row, col_incl)

            if distance_item and incl_item:
                try:
                    dist_value = float(distance_item.text())
                    incl_value_text = incl_item.text().strip()

                    if incl_value_text.upper() == "N/A":
                        continue

                    incl_value_float = float(incl_value_text.replace("%", ""))
                    incl_formatted = f"{incl_value_float:.2f} %"

                    cor_inclinacao = 7

                    if incl_value_float > 0:
                        cor_inclinacao = 5
                    elif incl_value_float < 0:
                        cor_inclinacao = 1

                    msp.add_text(incl_formatted, dxfattribs={
                        'height': base_text_height,
                        'layer': layer_eixos_segundo,
                        'insert': (dist_value, incl_text_y),
                        'rotation': 0,
                        'style': 'Arial',
                        'color': cor_inclinacao})

                except ValueError:
                    continue

class SelectLineTool(QgsMapToolIdentifyFeature):
    def __init__(self, canvas, parent):
        super().__init__(canvas)
        self.canvas = canvas
        self.parent = parent

    def canvasReleaseEvent(self, event):
        if event.button() == Qt.MouseButton.LeftButton:
            # Identifica todas as camadas vetoriais de linha no projeto
            layers = [
                layer for layer in QgsProject.instance().mapLayers().values()
                if isinstance(layer, QgsVectorLayer) and layer.geometryType() == Qgis.GeometryType.Line]

            if not layers:
                self.parent.mostrar_mensagem(QCoreApplication.translate("PerfilManager", "Nenhuma camada de linha encontrada no projeto."), "Erro")
                return

            # Identifica a feição clicada em qualquer camada de linha
            pixel_pt = event.originalPixelPoint()
            results = self.identify(int(pixel_pt.x()), int(pixel_pt.y()), layers, self.TopDownStopAtFirst)
            if results:
                res = results[0]
                feature = res.mFeature
                layer = res.mLayer

                # Guarda a camada e a feição usadas no perfil
                self.parent.current_line_layer = layer
                self.parent.current_line_feature = feature

                geometry = feature.geometry()

                if (geometry
                    and QgsWkbTypes.geometryType(geometry.wkbType())
                    == Qgis.GeometryType.Line):

                    # Extrai os vértices da linha selecionada
                    line_points = [QgsPointXY(pt) for pt in geometry.vertices()]

                    if len(line_points) < 2:
                        self.parent.mostrar_mensagem(QCoreApplication.translate("PerfilManager", "A feição selecionada não possui pontos suficientes para gerar o perfil."), "Erro")
                        return

                    # Armazena a linha selecionada
                    self.parent.line_points = line_points

                    # Gera o perfil
                    self.parent.extract_profile(line_points)

                    # Mantém a linha selecionada visível no mapa
                    self.parent.draw_rubber_band(line_points, color=Qt.GlobalColor.magenta)

                else:
                    self.parent.mostrar_mensagem(QCoreApplication.translate("PerfilManager", "A feição selecionada não é uma linha."), "Erro")

            else:
                self.parent.mostrar_mensagem(QCoreApplication.translate("PerfilManager", "Nenhuma feição encontrada no local clicado."), "Erro")

class ColorItemDelegate(QStyledItemDelegate):
    def __init__(self, parent=None, perfil_manager=None):
        super().__init__(parent)
        self.perfil_manager = perfil_manager

    def paint(self, painter, option, index):
        """Personaliza a renderização do item com um quadradinho de cor entre o checkbox e o nome."""
        # Desenha o item padrão (inclui o checkbox)
        super().paint(painter, option, index)

        # Recupera a cor armazenada no item
        color = index.data(Qt.ItemDataRole.UserRole)
        if color:
            # Configura o retângulo para o quadradinho de cor
            rect = option.rect
            size = 12  # Tamanho do quadradinho
            color_rect = QRect(rect.left() + 20, rect.top() + (rect.height() - size) // 2, size, size)

            # Desenha o quadradinho de cor com a cor atualizada
            painter.fillRect(color_rect, color)

    def editorEvent(self, event, model, option, index):
        # Código existente
        if event.type() == QtCore.QEvent.Type.MouseButtonPress:
            # Verificar se o clique foi no quadradinho de cor
            rect = option.rect
            size = 12
            color_rect = QtCore.QRect(rect.left() + 20, rect.top() + (rect.height() - size) // 2, size, size)
            if color_rect.contains(event.pos()):
                # Abrir o QColorDialog
                current_color = index.data(Qt.ItemDataRole.UserRole)
                titulo_cor = (QCoreApplication.translate("PerfilManager", "Selecione uma cor")
                    if self.perfil_manager
                    else QCoreApplication.translate("PerfilManager", "Selecione uma cor"))

                new_color = QColorDialog.getColor(
                    initial=current_color,
                    parent=None,
                    title=titulo_cor)
                if new_color.isValid():
                    # Atualizar a cor no modelo
                    model.setData(index, new_color, Qt.ItemDataRole.UserRole)
                    # Chamar update_graph_color no PerfilManager
                    if self.perfil_manager:
                        self.perfil_manager.update_graph_color(new_color, index)
                return True
        return super().editorEvent(event, model, option, index)

class LineTool(QgsMapToolEmitPoint):
    def __init__(self, canvas, parent):
        super().__init__(canvas)
        self.canvas = canvas
        self.parent = parent
        self.points = []
        self.rubber_band = QgsRubberBand(canvas, Qgis.GeometryType.Line)
        self.rubber_band.setColor(Qt.GlobalColor.red)
        self.rubber_band.setWidth(2)
        self.is_drawing = False

    def canvasPressEvent(self, event):
        if event.button() == Qt.MouseButton.LeftButton:
            # Adiciona ponto à linha
            if not self.parent.checkBoxLinha.isChecked():
                self.parent.mostrar_mensagem(QCoreApplication.translate("PerfilManager", "Ative o checkbox 'Desenhar Linha' para usar esta ferramenta."), "Aviso")
                return

            if not self.is_drawing:
                # Inicia um novo desenho
                self.points = []
                if self.parent.rubber_band:
                    self.parent.rubber_band.reset(Qgis.GeometryType.Line)

                # Linha temporária: não está associada a camada/feição >>>
                self.parent.current_line_layer = None
                self.parent.current_line_feature = None

                # Opcional, pra garantir
                self.parent.current_line_layer = None

            # Adiciona o ponto atual
            point = self.toMapCoordinates(event.pos())
            self.points.append(point)

            self.parent.draw_rubber_band(self.points, color=Qt.GlobalColor.red)  # Sempre vermelho

            self.update_rubber_band()
            self.is_drawing = True

        elif event.button() == Qt.MouseButton.RightButton and self.is_drawing:
            # Conclui o desenho ao clicar com o botão direito
            self.is_drawing = False
            self.parent.extract_profile(self.points)  # Extrai o perfil
            self.parent.log_xyz_every_100m()  # Registra os pontos a cada 100 metros

    def on_profile_ready(self, all_profiles):
        """Callback chamado quando o perfil está pronto."""
        self.all_profiles = all_profiles
        self.plot_profiles()
        self.log_xyz_every_100m()  # Registra os pontos a cada 100 metros

        # Chama o método para registrar os valores
        self.log_xyz_every_100m()

    def canvasMoveEvent(self, event):
        # Verifica se o checkBoxLinha está marcado antes de permitir desenhar
        if not self.parent.checkBoxLinha.isChecked():
            return

        if self.is_drawing:
            # Atualiza a linha temporária conforme o mouse se move
            point = self.toMapCoordinates(event.pos())
            if len(self.points) > 0:
                self.update_rubber_band(self.points + [point])
    
    def update_rubber_band(self, points=None):
        """Atualiza a linha temporária no mapa."""
        if points is None:
            points = self.points
        if self.parent.rubber_band is None:
            self.parent.rubber_band = QgsRubberBand(self.canvas, Qgis.GeometryType.Line)
            self.parent.rubber_band.setColor(Qt.GlobalColor.red)
            self.parent.rubber_band.setWidth(2)
        else:
            self.parent.rubber_band.reset(Qgis.GeometryType.Line)
        if points:
            line_geometry = QgsGeometry.fromPolylineXY([QgsPointXY(p.x(), p.y()) for p in points])
            self.parent.rubber_band.setToGeometry(line_geometry, None)

    def clear_rubber_band(self):
        """Limpa a linha temporária do mapa."""
        if self.rubber_band:
            self.rubber_band.reset(Qgis.GeometryType.Line)

    def deactivate(self):
        """Mantém a linha visível ao desativar a ferramenta."""
        pass  # Não faz nada para manter a linha visível

class FloatingTooltip(QLabel):
    def __init__(self, parent=None):
        super().__init__(parent)
        self.setStyleSheet("""
            QLabel {
                border: none;
                background-color: rgba(0, 0, 0, 0);  /* Fundo transparente */
                font: bold 12px;}
        """)
        # Alteramos aqui para usar Qt.WindowType.Tool em vez de Qt.WindowType.ToolTip
        self.setWindowFlags(Qt.WindowType.Tool | Qt.WindowType.FramelessWindowHint)
        self.setAttribute(Qt.WidgetAttribute.WA_TranslucentBackground)
        self.setAlignment(Qt.AlignmentFlag.AlignCenter)

    def show_tooltip(self, text, global_pos, color):
        # Define o texto com HTML para aplicar a cor
        color_name = color.name()  # Obtém a cor em formato hexadecimal
        self.setText(f'<span style="color:{color_name}">{text}</span>')
        self.setTextFormat(Qt.TextFormat.RichText)
        self.adjustSize()
        x = global_pos.x() - self.width() // 2 - 2
        y = global_pos.y() - self.height() - 5  # Ajuste conforme necessário
        self.move(x, y)
        self.show()

    def hide_tooltip(self):
        self.hide()
