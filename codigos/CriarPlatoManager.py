from qgis.core import QgsProject, QgsRasterLayer, QgsMapSettings, QgsMapRendererCustomPainterJob, Qgis, QgsMessageLog, QgsVectorLayer, QgsField, QgsFeature, QgsGeometry, QgsPointXY, QgsMarkerSymbol, QgsLineSymbol, QgsArrowSymbolLayer, QgsVectorLayerSimpleLabeling, QgsPalLayerSettings, QgsTextFormat, QgsProperty, QgsCoordinateTransform, QgsTextBackgroundSettings, QgsRuleBasedRenderer, QgsRectangle, QgsMeshLayer, QgsCoordinateReferenceSystem, QgsSymbolLayer, QgsFillSymbol, QgsSingleSymbolRenderer, QgsApplication, QgsVectorFileWriter, QgsVectorFileWriterTask, QgsProviderRegistry, QgsProviderSublayerDetails
from qgis.PyQt.QtWidgets import QDialog, QGraphicsScene, QGraphicsPixmapItem, QLabel, QLineEdit, QDoubleSpinBox, QVBoxLayout, QHBoxLayout, QListWidgetItem, QListWidget, QFileDialog, QStyledItemDelegate, QStyle, QAbstractSpinBox, QComboBox, QRadioButton, QPushButton, QFrame, QGridLayout, QProgressBar, QCheckBox, QTextBrowser
from qgis.PyQt.QtCore import Qt, QSize, QRect, QPoint, QEvent, QRegularExpression, QMetaType, QCoreApplication, QUrl
from qgis.PyQt.QtGui import QImage, QPainter, QPixmap, QColor, QFont, QPen, QBrush, QRegularExpressionValidator, QDesktopServices
from matplotlib.offsetbox import OffsetImage, AnnotationBbox
from qgis.gui import QgsProjectionSelectionDialog
from openpyxl.styles import Border, Side
from qgis.PyQt.QtXml import QDomDocument
from matplotlib.patches import Circle
from openpyxl import load_workbook
import matplotlib.patches as patches
import matplotlib.pyplot as plt
from qgis.utils import iface
from qgis.PyQt import uic
import pandas as pd
import numpy as np
import processing
import tempfile
import math
import re
import os

FORM_CLASS, _ = uic.loadUiType(os.path.join(
    os.path.dirname(__file__), 'platoMDT.ui'))

class PlatoManager(QDialog, FORM_CLASS):
    def __init__(self, parent=None):
        """Constructor."""
        super(PlatoManager, self).__init__(parent)
        # Configura a interface do usuário a partir do Designer.
        self.setupUi(self)

        self.iface = iface

        # Altera o título da janela
        self.setWindowTitle(self.tr("Gerar Platô sobre o MDT"))

        # Inicializa o sinalizador para controlar a execução do gráfico
        self.is_generating_graph = False

        # Cria uma cena gráfica para o QGraphicsView
        self.scene = QGraphicsScene()
        self.graphicsViewRaster.setScene(self.scene)

        self.scenePoligono = QGraphicsScene()
        self.graphicsViewPoligono.setScene(self.scenePoligono)

        # Inicializa o ComboBox de Raster
        self.init_combo_box_raster()
        self.init_combo_box_poligono()

        self.scroll_widgets = []  # Armazena os widgets da scrollArea

        # Cria uma instância do GraficoManager e passa a instância atual de PlatoManager
        self.grafico_manager = GraficoManager(self)

        # Inicializa o caminho do logotipo como None
        self.logo_path = None

        # Configurações iniciais
        self.check_logo_status()  # Verifica e ajusta o estado do botão de logo

        # Conecta os sinais aos slots
        self.connect_signals()

        self.update_pushButtonSalvar_state()

        # Configura a janela para permitir minimizar, maximizar e fechar
        # Mantém o diálogo associado ao QGIS, mas permite trabalhar no mapa
        # Janela independente visualmente, mas pertencente ao QGIS
        self.setWindowFlags(Qt.WindowType.Window
            | Qt.WindowType.WindowMinimizeButtonHint
            | Qt.WindowType.WindowMaximizeButtonHint
            | Qt.WindowType.WindowCloseButtonHint)

        self.setWindowModality(Qt.WindowModality.NonModal)

        # Ao passar o mouse (hover) com um azul claro
        style = """QListWidget::item:hover {background: #cceeff;}   /* Azul claro no hover */"""
        self.listWidgetSegmentos.setStyleSheet(style)
        self.listWidgetEstacas.setStyleSheet(style)
        self.listWidgetTalude.setStyleSheet(style)

    def connect_signals(self):
        # Conecta os sinais existentes
        self.comboBoxRaster.currentIndexChanged.connect(self.display_raster)
        self.comboBoxPoligono.currentIndexChanged.connect(self.display_polygon)  # Conexão para atualizar o graphicsViewPoligono
        QgsProject.instance().layersAdded.connect(self.handle_layers_added)

        # Conectar o novo método que lida com a remoção de camadas
        QgsProject.instance().layersRemoved.connect(self.handle_layers_removed)

        for layer in QgsProject.instance().mapLayers().values():
            layer.nameChanged.connect(self.update_combo_boxes)

        # Conectar sinais relacionados a outras verificações que podem afetar o botão
        for layer in QgsProject.instance().mapLayers().values():
            layer.nameChanged.connect(self.update_pushButtonVertices_state)

        # Conecta o botão pushButtonCalcular para atualizar as camadas
        self.pushButtonCalcular.clicked.connect(self.calculate_and_create_segment_layers)

        # Abre o diálogo para configuração da rampa
        self.pushButtonRampa.clicked.connect(self.abrir_dialogo_rampa)

        # Atualiza a lista de segmentos ao abrir o projeto ou ao carregar camadas
        QgsProject.instance().layersAdded.connect(self.update_list_widget_segmentos)
        QgsProject.instance().layerWillBeRemoved.connect(self.update_list_widget_segmentos)

        # Atualiza a lista de Estaqueamento ao abrir o projeto ou ao carregar camadas
        QgsProject.instance().layersAdded.connect(self.update_list_widget_estaqueamentos)
        QgsProject.instance().layerWillBeRemoved.connect(self.update_list_widget_estaqueamentos)

        # Atualiza a lista de Taludes ao abrir o projeto ou ao carregar camadas
        QgsProject.instance().layersAdded.connect(self.update_list_widget_talude)
        QgsProject.instance().layerWillBeRemoved.connect(self.update_list_widget_talude)

        # Conecta o botão para calcular e gerar os pontos intermediários
        self.pushButtonEstaqueamento.clicked.connect(self.calculate_intermediate_points)

        # Conecta o botão para calcular e gerar os Taludes
        self.pushButtonTalude.clicked.connect(self.calculate_talude)

        # Conecta a seleção de itens no listWidgetSegmentos
        self.listWidgetSegmentos.itemSelectionChanged.connect(self.check_estaqueamento_button_state)

        # Conecta o valor do doubleSpinBoxEquidistante para ativar/desativar o botão
        self.doubleSpinBoxEquidistante.valueChanged.connect(self.check_estaqueamento_button_state)

        # Conectar o sinal do doubleSpinBoxEquidistante para atualizar o toolTip
        self.doubleSpinBoxEquidistante.valueChanged.connect(self.calculate_and_update_tooltip)

        # Conectar o sinal de seleção do listWidgetSegmentos para recalcular o toolTip
        self.listWidgetSegmentos.currentItemChanged.connect(self.calculate_and_update_tooltip)

        # Conectar o sinal de seleção do listWidgetSegmentos para recalcular o toolTip e ajustar o estado do doubleSpinBox
        self.listWidgetSegmentos.currentItemChanged.connect(self.update_doubleSpinBoxEquidistante_state)

        # Conectar o sinal de seleção do listWidgetEstacas para ajustar o estado do pushButtonTalude
        self.listWidgetEstacas.currentItemChanged.connect(self.update_pushButtonTalude_state)

        # Conecta as mudanças no listWidgetEstacas
        self.listWidgetEstacas.itemSelectionChanged.connect(self.update_radio_buttons_state)

        # Conecta as mudanças no listWidgetEstacas para ativar ou desativar o pushButtonGrafico
        self.listWidgetEstacas.itemSelectionChanged.connect(self.update_pushButtonGrafico_state)

        # Enquadra no mapa a camada correspondente ao item selecionado
        self.listWidgetSegmentos.currentItemChanged.connect(self.enquadrar_camada_lista)
        self.listWidgetEstacas.currentItemChanged.connect(self.enquadrar_camada_lista)
        self.listWidgetTalude.currentItemChanged.connect(self.enquadrar_camada_lista)

        # Atualiza o estado do pushButtonVertices ao mudar a seleção no comboBoxPoligono
        self.comboBoxPoligono.currentIndexChanged.connect(self.update_pushButtonVertices_state)
        self.comboBoxRaster.currentIndexChanged.connect(self.update_pushButtonVertices_state)

        # Atualiza o estado do pushButtonJuntar na alteração do listWidgetEstacas e listWidgetTalude
        self.listWidgetEstacas.itemSelectionChanged.connect(self.update_pushButtonJuntar_state)
        self.listWidgetTalude.itemSelectionChanged.connect(self.update_pushButtonJuntar_state)

        # Conectar eventos relacionados a mudanças no projeto
        QgsProject.instance().layersAdded.connect(self.update_pushButtonVertices_state)
        QgsProject.instance().layersRemoved.connect(self.update_pushButtonVertices_state)

        # Desconectar quaisquer conexões existentes para evitar múltiplas conexões
        try:
            self.pushButtonGrafico.clicked.disconnect()
            self.pushButtonJuntar.clicked.disconnect()
            self.pushButtonLogo.clicked.disconnect()
            self.pushButtonVertices.clicked.disconnect()
        except TypeError:
            pass  # nosec B110 | Nenhuma conexão existente

        # Conecta o botão para criar a camada de pontos a partir dos vértices
        self.pushButtonVertices.clicked.connect(self.create_point_layer_from_polygon)

        # Conecta o botão para calcular e gerar o Gráfico
        self.pushButtonGrafico.clicked.connect(self.on_pushButtonGrafico_clicked)

        # Conecta o botão para juntar as camadas
        self.pushButtonJuntar.clicked.connect(self.on_pushButtonJuntar_clicked)

        # Abre um GeoPackage anteriormente salvo pelo módulo
        self.pushButtonAbrir.clicked.connect(self.abrir_projeto_salvo)

        # Salva as camadas relacionadas ao Platô em GeoPackage
        self.pushButtonSalvar.clicked.connect(self.salvar_camadas_geopackage)

        # Conectar o botão pushButtonCancelar para fechar o diálogo
        self.pushButtonCancelar.clicked.connect(self.close)

        # Conectar o botão pushButtonLogo para abrir a pasta
        self.pushButtonLogo.clicked.connect(self.on_pushButtonLogo_clicked)

        # Inicializar o botão "Calcular" como desativado
        self.pushButtonCalcular.setEnabled(False)

        # Conectar o botão "Vertices" ao método que ativará o botão "Calcular"
        self.pushButtonVertices.clicked.connect(self.on_pushButtonVertices_clicked)

        # Certifique-se de que a scrollAreaWidgetContents tenha um layout
        if not self.scrollAreaWidgetContents.layout():
            layout = QVBoxLayout()  # ou outro tipo de layout conforme necessário
            self.scrollAreaWidgetContents.setLayout(layout)

        # Instanciar o delegado e definir nos listWidgets
        self.delegateSegmentos = ListDeleteButtonDelegate(self.listWidgetSegmentos)
        self.listWidgetSegmentos.setItemDelegate(self.delegateSegmentos)

        self.delegateEstacas = ListDeleteButtonDelegate(self.listWidgetEstacas)
        self.listWidgetEstacas.setItemDelegate(self.delegateEstacas)

        self.delegateTalude = ListDeleteButtonDelegate(self.listWidgetTalude)
        self.listWidgetTalude.setItemDelegate(self.delegateTalude)

        # Conecte o evento de duplo clique ao listWidgetEstacas
        self.listWidgetEstacas.itemDoubleClicked.connect(self.open_excel_with_attributes)

        # Atualiza o estado do botão Salvar conforme o Platô e suas camadas
        self.comboBoxPoligono.currentIndexChanged.connect(self.update_pushButtonSalvar_state)
        QgsProject.instance().layersAdded.connect(self.update_pushButtonSalvar_state)
        QgsProject.instance().layersRemoved.connect(self.update_pushButtonSalvar_state)

        self.pushButtonUsar.clicked.connect(self.abrir_ajuda_uso)

    def tr(self, message):
        return QCoreApplication.translate("PlatoManager", message)

    def init_combo_box_raster(self):
        """
        Atualiza o comboBox de raster preservando a seleção atual
        e evitando sinais intermediários durante a reconstrução.
        """
        current_raster_id = self.comboBoxRaster.currentData()

        layers = QgsProject.instance().mapLayers().values()
        raster_layers = [layer for layer in layers if layer.type() == Qgis.LayerType.Raster]

        self.comboBoxRaster.blockSignals(True)

        try:
            self.comboBoxRaster.clear()

            for raster_layer in raster_layers:
                self.comboBoxRaster.addItem(raster_layer.name(), raster_layer.id())

            index = self.comboBoxRaster.findData(current_raster_id) if current_raster_id else -1

            if index != -1:
                self.comboBoxRaster.setCurrentIndex(index)
            elif raster_layers:
                self.comboBoxRaster.setCurrentIndex(0)
            else:
                self.comboBoxRaster.setCurrentIndex(-1)

        finally:
            self.comboBoxRaster.blockSignals(False)

        self.display_raster()

    def init_combo_box_poligono(self):
        """
        Atualiza o comboBox de polígonos preservando a seleção atual
        e evitando verificações temporárias de SRC durante a reconstrução.
        """
        current_polygon_id = self.comboBoxPoligono.currentData()

        layers = QgsProject.instance().mapLayers().values()
        polygon_layers = [
            layer for layer in layers
            if layer.type() == Qgis.LayerType.Vector
            and layer.geometryType() == Qgis.GeometryType.Polygon]

        self.comboBoxPoligono.blockSignals(True)

        try:
            self.comboBoxPoligono.clear()

            for polygon_layer in polygon_layers:
                self.comboBoxPoligono.addItem(polygon_layer.name(), polygon_layer.id())

            index = self.comboBoxPoligono.findData(current_polygon_id) if current_polygon_id else -1

            if index != -1:
                self.comboBoxPoligono.setCurrentIndex(index)
            elif polygon_layers:
                self.comboBoxPoligono.setCurrentIndex(0)
            else:
                self.comboBoxPoligono.setCurrentIndex(-1)

        finally:
            self.comboBoxPoligono.blockSignals(False)

        self.display_polygon()

    def display_raster(self):
        """
        Renderiza a camada raster selecionada no QGraphicsView, ajustando a visualização
        conforme o tamanho da viewport e a extensão do raster.
        """
        # Limpa a cena antes de adicionar um novo item
        self.scene.clear()

        # Obtém o ID da camada raster selecionada
        selected_raster_id = self.comboBoxRaster.currentData()

        # Busca a camada raster pelo ID
        selected_layer = QgsProject.instance().mapLayer(selected_raster_id)

        if isinstance(selected_layer, QgsRasterLayer):
            # Configurações do mapa
            map_settings = QgsMapSettings()
            map_settings.setLayers([selected_layer])  # Definimos a camada a ser renderizada
            map_settings.setBackgroundColor(QColor(255, 255, 255))
            
            # Define o tamanho da imagem a ser renderizada
            width = self.graphicsViewRaster.viewport().width()
            height = self.graphicsViewRaster.viewport().height()
            map_settings.setOutputSize(QSize(width, height))
            
            # Define a extensão do mapa (extensão do raster)
            map_settings.setExtent(selected_layer.extent())

            # Cria a imagem para renderizar
            image = QImage(width, height, QImage.Format.Format_ARGB32)
            image.fill(Qt.GlobalColor.transparent)

            # Configura o pintor e a tarefa de renderização
            painter = QPainter(image)
            render_job = QgsMapRendererCustomPainterJob(map_settings, painter)

            # Executa a renderização
            render_job.start()
            render_job.waitForFinished()
            painter.end()

            # Cria um pixmap a partir da imagem renderizada
            pixmap = QPixmap.fromImage(image)
            pixmap_item = QGraphicsPixmapItem(pixmap)

            # Adiciona o item à cena
            self.scene.addItem(pixmap_item)

            # Ajusta a cena ao QGraphicsView, garantindo que o modo de ajuste preserve a proporção
            self.graphicsViewRaster.setSceneRect(pixmap_item.boundingRect())
            self.graphicsViewRaster.fitInView(self.scene.sceneRect(), Qt.AspectRatioMode.KeepAspectRatio)

    def display_polygon(self):
        """Atualiza a exibição no QGraphicsView:
           - se houver seleção: enquadra TODAS as selecionadas;
           - caso contrário: enquadra TODAS as feições do layer."""
        self.scenePoligono.clear()

        selected_polygon_id = self.comboBoxPoligono.currentData()
        selected_layer = QgsProject.instance().mapLayer(selected_polygon_id)

        if not selected_layer or not isinstance(selected_layer, QgsVectorLayer):
            return

        # garante que os sinais estão conectados para atualizar ao vivo
        self._ensure_polygon_signals_connected(selected_layer)

        # coleta feições poligonais válidas
        all_polys = []
        for f in selected_layer.getFeatures():
            g = f.geometry()
            if g and not g.isEmpty() and g.type() == Qgis.GeometryType.Polygon:
                all_polys.append(f)

        if not all_polys:
            if self.isVisible():
                self.mostrar_mensagem(self.tr("A camada de polígono não contém feições."), "Erro")
            return

        # selecionadas (apenas polígonos)
        selected_polys = []
        for f in selected_layer.selectedFeatures():
            g = f.geometry()
            if g and not g.isEmpty() and g.type() == Qgis.GeometryType.Polygon:
                selected_polys.append(f)

        # decide conjunto a enquadrar
        feats_to_frame = selected_polys if selected_polys else all_polys

        # calcula extent unindo os bounding boxes
        extent = None
        for f in feats_to_frame:
            bb = f.geometry().boundingBox()
            if bb and not bb.isNull():
                if extent is None:
                    extent = QgsRectangle(bb)
                else:
                    extent.combineExtentWith(bb)

        if extent is None or extent.isNull():
            if self.isVisible():
                self.mostrar_mensagem(self.tr("Não foi possível determinar o enquadramento das feições."), "Erro")
            return

        # prepara renderização
        map_settings = QgsMapSettings()
        map_settings.setLayers([selected_layer])
        map_settings.setBackgroundColor(QColor(255, 255, 255))

        width  = max(2, self.graphicsViewPoligono.viewport().width())
        height = max(2, self.graphicsViewPoligono.viewport().height())
        map_settings.setOutputSize(QSize(width, height))
        map_settings.setExtent(extent)

        image = QImage(width, height,QImage.Format.Format_ARGB32)
        image.fill(Qt.GlobalColor.transparent)

        painter = QPainter(image)
        render_job = QgsMapRendererCustomPainterJob(map_settings, painter)
        render_job.start()
        render_job.waitForFinished()
        painter.end()

        pixmap = QPixmap.fromImage(image)
        pixmap_item = QGraphicsPixmapItem(pixmap)
        self.scenePoligono.addItem(pixmap_item)
        self.graphicsViewPoligono.setSceneRect(pixmap_item.boundingRect())
        self.graphicsViewPoligono.fitInView(self.scenePoligono.sceneRect(), Qt.AspectRatioMode.KeepAspectRatio)

    def _ensure_polygon_signals_connected(self, layer: QgsVectorLayer):
        """Conecta sinais para atualizar o preview ao editar/selecionar/adicionar/remover feições.

        Importante:
        - Conecta APENAS na camada atualmente selecionada no combo.
        - Ao trocar de camada, desconecta a anterior para evitar duplicação/vazamento de conexões.
        """
        if not layer or not isinstance(layer, QgsVectorLayer):
            return

        if getattr(self, "_poly_signal_layer_id", None) == layer.id():
            return

        # troca de camada: desconecta a anterior
        self._disconnect_polygon_signals()

        # callbacks (precisam ficar referenciados para o disconnect funcionar)
        def _refresh(*_args, **_kwargs):
            self.display_polygon()

        def _on_sel_changed(*_args, **_kwargs):
            # mantém preview + estado do botão Vertices sincronizados
            self.on_selection_changed()

        slots = {}

        # sinais que existem em praticamente todas as versões
        for sig_name in ("featureAdded", "geometryChanged"):
            if hasattr(layer, sig_name):
                try:
                    getattr(layer, sig_name).connect(_refresh)
                    slots[sig_name] = _refresh
                except Exception:
                    pass  # nosec B110

        # remoção pode ser featureDeleted (fid) ou featuresDeleted (lista), dependendo da versão
        for sig_name in ("featureDeleted", "featuresDeleted"):
            if hasattr(layer, sig_name):
                try:
                    getattr(layer, sig_name).connect(_refresh)
                    slots[sig_name] = _refresh
                except Exception:
                    pass  # nosec B110

        # seleção: usa o handler dedicado (evita disparo duplo e mantém botão atualizado)
        if hasattr(layer, "selectionChanged"):
            try:
                layer.selectionChanged.connect(_on_sel_changed)
                slots["selectionChanged"] = _on_sel_changed
            except Exception:
                pass  # nosec B110

        self._poly_signal_layer_id = layer.id()
        self._poly_signal_slots = slots

    def _log_message(self, message, level=Qgis.MessageLevel.Info):
        QgsMessageLog.logMessage(message, 'TALUDE', level=level)

    def mostrar_mensagem(self, texto, tipo, duracao=1, caminho_pasta=None, caminho_arquivos=None):
        """Exibe mensagens na barra do QGIS permitindo que se acumulem."""
        bar = self.iface.messageBar()

        if tipo == "Erro":
            titulo = self.tr("Erro")
            nivel = Qgis.MessageLevel.Critical

        elif tipo == "Aviso":
            titulo = self.tr("Aviso")
            nivel = Qgis.MessageLevel.Warning

        elif tipo == "Sucesso":
            titulo = self.tr("Sucesso")
            nivel = Qgis.MessageLevel.Info

        else:
            titulo = self.tr("Info")
            nivel = Qgis.MessageLevel.Info

        mensagem = bar.createMessage(titulo, texto)
        bar.pushWidget(mensagem, level=nivel, duration=duracao)

    def reset_scroll_area(self):
        """Reseta e limpa a área de rolagem (scrollArea) e a lista de widgets (scroll_widgets)."""
        # Limpa a lista de widgets armazenada
        self.scroll_widgets.clear()

        # Limpa o layout do scrollArea
        layout = self.scrollAreaWidgetContents.layout()
        
        if layout is not None:
            while layout.count() > 0:
                item = layout.takeAt(0)
                if item.widget() is not None:
                    item.widget().deleteLater()
                elif item.layout() is not None:
                    self.clear_layout(item.layout())  # Limpa layouts aninhados

    def clear_layout(self, layout):
        """Limpa todos os widgets e layouts de um layout específico."""
        while layout.count() > 0:
            item = layout.takeAt(0)
            if item.widget() is not None:
                item.widget().deleteLater()
            elif item.layout() is not None:
                self.clear_layout(item.layout())

    def showEvent(self, event):
        """
        Trata o evento de exibição do diálogo, atualizando visualizações e resetando a interface ao abrir.
        """
        super(PlatoManager, self).showEvent(event)

        # Limpa a lista de widgets no scrollArea
        self.reset_scroll_area()

        # Ajusta a visualização quando o diálogo é mostrado
        self.display_raster()
        self.display_polygon()

        # Atualiza o listWidgetSegmentos ao abrir a janela
        self.update_list_widget_segmentos()
        self.update_list_widget_estaqueamentos()
        self.update_list_widget_talude()

        # Reseta o estado do botão pushButtonEstaqueamento (desativado)
        self.pushButtonEstaqueamento.setEnabled(False)

        # Reseta o valor do doubleSpinBoxEquidistante
        self.doubleSpinBoxEquidistante.setValue(0)

        # Verifica e aplica as configurações de ativação do pushButtonVertices
        self.update_pushButtonVertices_state()

        # Atualiza o estado do doubleSpinBoxEquidistante baseado no listWidgetSegmentos
        self.update_doubleSpinBoxEquidistante_state()

        # Atualiza o estado do pushButtonTalude baseado no listWidgetEstacas
        self.update_pushButtonTalude_state()
        
        # Atualiza o estado do radioButtonEsquerda e radioButtonDireita baseado no listWidgetEstacas
        self.update_radio_buttons_state()
        
        # Atualiza o estado do pushButtonGrafico baseado no listWidgetEstacas
        self.update_pushButtonGrafico_state()

        # Atualiza o estado do pushButtonJuntar baseado no listWidgetEstacas ou listWidgetTalude
        self.update_pushButtonJuntar_state()

        # Atualiza o estado do pushButtonCalcular baseado no click do botão pushButtonVertices
        self.on_pushButtonVertices_clicked()

        self.connect_selection_signal() # Chama após carregar ou selecionar a camada

    def closeEvent(self, event):
        """
        Trata o evento de fechamento do diálogo, removendo referências e executando ações de limpeza.
        """
        # limpeza: evita callbacks em camadas após fechar o diálogo
        self._disconnect_polygon_signals()

        parent = self.parent()
        if parent:
            parent.plato_mdt_dlg = None
        super(PlatoManager, self).closeEvent(event)

    def update_combo_box(self):
        """
        Atualiza o comboBox de raster ao adicionar ou remover camadas no projeto,
        tentando manter a seleção anterior quando possível.
        """
        # Armazena a seleção atual para restaurar após a atualização
        current_index = self.comboBoxRaster.currentIndex()
        current_layer_id = self.comboBoxRaster.itemData(current_index)

        # Atualiza o combo box quando camadas são adicionadas ou removidas
        self.init_combo_box_raster()

        # Tenta restaurar a seleção anterior
        if current_layer_id:
            index = self.comboBoxRaster.findData(current_layer_id)
            if index != -1:
                self.comboBoxRaster.setCurrentIndex(index)
            else:
                # Se a camada não existe mais, seleciona a primeira disponível
                if self.comboBoxRaster.count() > 0:
                    self.comboBoxRaster.setCurrentIndex(0)
                    self.display_raster()

    def update_combo_boxes(self):
        """Atualiza ambos os combo boxes"""
        self.init_combo_box_raster()
        self.init_combo_box_poligono()

    def handle_layers_added(self, layers):
        """
        Atualiza os comboBoxes ao adicionar camadas,
        preservando automaticamente as seleções atuais.
        """
        self.update_combo_boxes()

        polygon_layers = [
            layer for layer in layers
            if isinstance(layer, QgsVectorLayer)
            and layer.geometryType() == Qgis.GeometryType.Polygon]

        if polygon_layers:
            self.display_polygon()

    def handle_layers_removed(self, removed_layers_ids):
        """Função para tratar a remoção de camadas."""
        # Atualizar os ComboBoxes de Raster e Polígono
        self.update_combo_boxes()

        # Se a camada atualmente conectada foi removida, desconecta sinais para evitar chamadas penduradas
        if getattr(self, "_poly_signal_layer_id", None) in removed_layers_ids:
            self._disconnect_polygon_signals()

        # Verificar e atualizar os grupos e widgets associados
        self.check_layers_in_group_and_update(removed_layers_ids)

    def _disconnect_polygon_signals(self):
        """Desconecta sinais do preview do polígono previamente conectados."""
        layer_id = getattr(self, "_poly_signal_layer_id", None)
        slots = getattr(self, "_poly_signal_slots", None) or {}

        if not layer_id or not slots:
            self._poly_signal_layer_id = None
            self._poly_signal_slots = {}
            return

        layer = QgsProject.instance().mapLayer(layer_id)
        if layer and isinstance(layer, QgsVectorLayer):
            for sig_name, slot in slots.items():
                try:
                    getattr(layer, sig_name).disconnect(slot)
                except Exception:
                    # se já estava desconectado (ou o sinal não existe nesta versão), ignora
                    pass  # nosec B110

        self._poly_signal_layer_id = None
        self._poly_signal_slots = {}

    def apply_arrow_symbology(self, layer: QgsVectorLayer):
        """
        Seta sem borda:
          - preenchimento azul (#0066CC) se Inclinação > 0
          - preenchimento vermelho (#CC0000) se Inclinação < 0
          - preenchimento preto (#000000)   se Inclinação = 0
        """
        field_name = "Inclinação"

        # expressão para cor do preenchimento baseada no campo (fração)
        color_expr = (
            f'CASE '
            f'WHEN "{field_name}" > 0 THEN color_rgb(0, 85, 255) '   # -- azul
            f'WHEN "{field_name}" < 0 THEN color_rgb(255, 65, 65) '     # -- vermelho
            f'ELSE color_rgb(0, 0, 0) END')                           # -- preto

        # cria APENAS a camada de seta (sem base de linha)
        arrow_layer = QgsArrowSymbolLayer()
        arrow_layer.setHeadType(QgsArrowSymbolLayer.HeadType.HeadSingle)
        arrow_layer.setHeadLength(6)
        arrow_layer.setHeadThickness(1.4)
        arrow_layer.setArrowStartWidth(0.4)
        arrow_layer.setArrowWidth(0.6)
        arrow_layer.setColor(QColor('#000000'))  # default; será sobrescrito por data-defined

        # aplica cor data-defined no preenchimento do sub-símbolo (fill)
        sub_symbol: QgsFillSymbol = arrow_layer.subSymbol()
        if sub_symbol:
            for sl in sub_symbol.symbolLayers():
                # preenchimento controlado pela expressão
                sl.setDataDefinedProperty(
                    QgsSymbolLayer.Property.FillColor,
                    QgsProperty.fromExpression(color_expr))
                # remove COMPLETAMENTE a borda/contorno
                if hasattr(sl, "setStrokeStyle"):
                    sl.setStrokeStyle(Qt.PenStyle.NoPen)
                if hasattr(sl, "setStrokeWidth"):
                    sl.setStrokeWidth(0.0)
                if hasattr(sl, "setStrokeColor"):
                    sl.setStrokeColor(QColor(0, 0, 0, 0))  # transparente

        # símbolo de linha SEM layers-base (sem traço)
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

    def activate_labels_for_points(self, point_layer):
        """Ativa os rótulos de 'NovoZ' na camada de pontos com formatação simples, em negrito e cor preta, com deslocamento."""
        layer_settings = QgsPalLayerSettings()
        text_format = QgsTextFormat()

        # Configurações básicas do rótulo
        layer_settings.isExpression = True  # Definimos como expressão para combinar 'ID' e 'NovoZ'
        layer_settings.fieldName = "'ID: ' || \"ID\" || '\nNovoZ: ' || \"NovoZ\""  # Expressão para exibir ID e NovoZ com quebra de linha
        layer_settings.placement = Qgis.LabelPlacement.OverPoint  # Coloca o rótulo sobre o ponto

        # Configurações do texto do rótulo
        font = QFont("Arial", 10)
        font.setBold(True)  # Negrito simples
        text_format.setFont(font)
        text_format.setSize(10)  # Tamanho do texto

        # Definir a cor do texto (preto)
        text_format.setColor(QColor(0, 0, 0))  # Cor preta para o rótulo

        # Aplicar o formato de texto ao rótulo
        layer_settings.setFormat(text_format)

        # Configuração de deslocamento (offset) do rótulo
        layer_settings.xOffset = 6  # Deslocamento horizontal
        layer_settings.yOffset = 3  # Deslocamento vertical

        # Definir a rotulagem na camada
        labeling = QgsVectorLayerSimpleLabeling(layer_settings)
        point_layer.setLabeling(labeling)
        point_layer.setLabelsEnabled(True)
        point_layer.triggerRepaint()

    def activate_labels_on_layer(self, layer, field_name):
        """Ativa os rótulos em uma camada de linhas com símbolos de seta no rótulo e formatação condicional."""
        layer_settings = QgsPalLayerSettings()
        text_format = QgsTextFormat()

        # Configurações básicas do rótulo
        layer_settings.isExpression = True  # Definimos como expressão para incluir setas

        # use o nome do campo na var field_name (ex.: "Inclinação")
        layer_settings.fieldName = (
            f"with_variable('p', \"{field_name}\" * 100, "        # -- p = valor em %
            " with_variable('pr', round(@p, 3), "                 # -- pr = % arredondado a 3 casas
            "   CASE "
            "     WHEN abs(@pr) < 0.0005 THEN '→' || format_number(0, 3) || '%' "
            "     WHEN @pr < 0 THEN '⬇' || format_number(@pr, 3) || '%' "
            "     ELSE '⬆' || format_number(@pr, 3) || '%' "
            "   END""))")

        layer_settings.placement = Qgis.LabelPlacement.Line  # Coloca o rótulo ao longo da linha

        # Configurações do texto do rótulo
        font = QFont("Arial", 11)
        font.setBold(True)
        font.setItalic(True)
        text_format.setFont(font)
        text_format.setSize(11)

        # Configuração do fundo branco para o rótulo
        background = QgsTextBackgroundSettings()
        background.setEnabled(True)
        background.setFillColor(QColor(255, 255, 0))  # Cor de fundo amarelo
        text_format.setBackground(background)

        # Adiciona formatação condicional (vermelho para negativo, azul para positivo, preto para zero)
        color_expression = """CASE
                                WHEN "{field}" < 0 THEN '255,0,0'  -- Vermelho para inclinações negativas
                                WHEN "{field}" > 0 THEN '0,0,255'  -- Azul para inclinações positivas
                                ELSE '0,0,0'  -- Preto para zero
                              END""".format(field=field_name)

        # Definir as propriedades dos rótulos (cor, tamanho)
        properties = layer_settings.dataDefinedProperties()
        properties.setProperty(QgsPalLayerSettings.Property.Color, QgsProperty.fromExpression(color_expression))
        properties.setProperty(QgsPalLayerSettings.Property.Size, QgsProperty.fromValue(11))  # Tamanho da fonte

        # Aplicar o formato de texto ao rótulo
        layer_settings.setFormat(text_format)
        layer_settings.setDataDefinedProperties(properties)

        # Definir a rotulagem na camada
        labeling = QgsVectorLayerSimpleLabeling(layer_settings)
        layer.setLabeling(labeling)
        layer.setLabelsEnabled(True)
        layer.triggerRepaint()

    def _filtrar_vertices_curva(self, vertices, geom_original, distancia_minima=1.0):
        """
        Reduz a quantidade de vértices provenientes da discretização de curvas.

        Regras:
        - somente pontos intermediários muito próximos são removidos;
        - distância mínima padrão entre pontos gerados: 1,00 m;
        - vértices estruturais da geometria original são preservados;
        - considera também o fechamento do polígono.
        """
        vertices = list(vertices)

        if len(vertices) <= 3:
            return vertices

        # Vértices nativos da geometria original.
        # Em curvas, estes representam os pontos estruturais/controle
        # antes da densificação realizada para formar o polígono linear.
        vertices_estruturais = set()

        try:
            for vertex in geom_original.vertices():
                vertices_estruturais.add((round(vertex.x(), 8), round(vertex.y(), 8)))
        except Exception:
            vertices_estruturais = set()

        def chave(vertex):
            return round(vertex.x(), 8), round(vertex.y(), 8)

        def distancia(p1, p2):
            return math.hypot(p2.x() - p1.x(), p2.y() - p1.y())

        filtrados = [vertices[0]]

        for vertex in vertices[1:]:
            ultimo = filtrados[-1]
            dist = distancia(ultimo, vertex)
            estrutural = chave(vertex) in vertices_estruturais

            # Mantém pontos estruturais independentemente da distância.
            # Nos pontos intermediários da curva, exige no mínimo 1 metro.
            if estrutural or dist >= distancia_minima:
                filtrados.append(vertex)

        # Como o anel está sem o vértice final duplicado, verifica também
        # a distância entre o último ponto mantido e o primeiro.
        if len(filtrados) > 3:
            ultimo = filtrados[-1]
            primeiro = filtrados[0]

            if distancia(ultimo, primeiro) < distancia_minima:
                # Só remove se não for um vértice estrutural original.
                if chave(ultimo) not in vertices_estruturais:
                    filtrados.pop()

        return filtrados

    def create_point_layer_from_polygon(self):
        """
        Cria uma camada de pontos a partir dos vértices de um polígono selecionado, 
        atribui valores de elevação do raster, ativa rótulos e gera camada de linhas dos segmentos.
        """
        selected_polygon_id = self.comboBoxPoligono.currentData()
        selected_layer = QgsProject.instance().mapLayer(selected_polygon_id)
        
        if selected_layer and isinstance(selected_layer, QgsVectorLayer):
            features = [f for f in selected_layer.getFeatures() if f.geometry().type() == Qgis.GeometryType.Polygon]

            # Verifica se há apenas uma feição ou uma feição selecionada
            if len(features) == 1 or selected_layer.selectedFeatureCount() == 1:
                if selected_layer.selectedFeatureCount() == 1:
                    feature = selected_layer.selectedFeatures()[0]
                else:
                    feature = features[0]

                feature = self._get_active_polygon_feature(selected_layer)
                poly_id = self._get_poly_id_for_naming(selected_layer, feature)

                # Nome com ID da feição
                point_layer_name = f"{selected_layer.name()}_ID{poly_id}_{self.tr('Vértices')}"

                # Cria a camada de pontos
                point_layer = QgsVectorLayer('Point?crs=' + selected_layer.crs().authid(), point_layer_name, 'memory')
                pr = point_layer.dataProvider()

                # Adiciona campos "ID", "X", "Y", "Z", "NovoZ"
                pr.addAttributes([QgsField("ID", QMetaType.Type.Int),
                                  QgsField("X", QMetaType.Type.Double),
                                  QgsField("Y", QMetaType.Type.Double),
                                  QgsField("Z", QMetaType.Type.Double),
                                  QgsField("NovoZ", QMetaType.Type.Double)])
                point_layer.updateFields()
                self._aplicar_aliases_campos(point_layer)

                # Obtém o raster selecionado para calcular o valor de Z
                selected_raster_id = self.comboBoxRaster.currentData()
                raster_layer = QgsProject.instance().mapLayer(selected_raster_id)

                if not raster_layer or not isinstance(raster_layer, QgsRasterLayer):
                    self.mostrar_mensagem(self.tr("Camada raster inválida ou não selecionada."), "Erro")
                    return

                # Obtém a geometria da feição selecionada
                geom = feature.geometry()
                if geom.isMultipart():
                    multi = geom.asMultiPolygon()
                    if not multi or not multi[0]:
                        self.mostrar_mensagem(self.tr("Não foi possível obter os vértices do MultiPolygon."), "Erro")
                        return
                    vertices = multi[0][0]
                else:
                    poly = geom.asPolygon()
                    if not poly or not poly[0]:
                        self.mostrar_mensagem(self.tr("Não foi possível obter os vértices do Polígono."), "Erro")
                        return
                    vertices = poly[0]

                # Remove o último vértice se for igual ao primeiro para evitar duplicação
                if vertices[0] == vertices[-1]:
                    vertices.pop()

                # Em geometrias curvas, reduz os vértices intermediários excessivamente
                # próximos, mantendo distância mínima de 1 metro entre os pontos gerados.
                geom_abstrata = geom.constGet()

                if geom_abstrata and geom_abstrata.hasCurvedSegments():
                    vertices = self._filtrar_vertices_curva(vertices, geom, distancia_minima=1.0)

                points = []
                for i, vertex in enumerate(vertices):
                    x = round(vertex.x(), 3)
                    y = round(vertex.y(), 3)

                    # Identifica o valor no raster
                    identify_result = raster_layer.dataProvider().identify(QgsPointXY(x, y), Qgis.RasterIdentifyFormat.Value)

                    # Interrompe toda a geração se qualquer vértice não possuir cota válida.
                    results = identify_result.results() if identify_result.isValid() else {}
                    z_val = next(iter(results.values()), None) if results else None

                    try:
                        z_num = float(z_val)
                    except (TypeError, ValueError):
                        z_num = math.nan

                    if not math.isfinite(z_num):
                        self.mostrar_mensagem(self.tr("Não foi possível obter uma elevação válida em ({x}, {y}). Verifique se todo o polígono está dentro do raster.").format(x=x, y=y), "Erro")
                        return

                    z = round(z_num, 3)

                    # Cria o ponto
                    point = QgsFeature(point_layer.fields())
                    point.setGeometry(QgsGeometry.fromPointXY(QgsPointXY(x, y)))
                    point.setAttribute("ID", i + 1)
                    point.setAttribute("X", x)
                    point.setAttribute("Y", y)
                    point.setAttribute("Z", z)
                    point.setAttribute("NovoZ", z)
                    points.append(point)

                    # Adiciona o ponto à camada de pontos
                    pr.addFeature(point)

                # Só substitui a camada anterior depois que todos os vértices foram validados.
                existing_layers = QgsProject.instance().mapLayersByName(point_layer_name)
                if existing_layers:
                    try:
                        QgsProject.instance().removeMapLayer(existing_layers[0].id())
                    except Exception as e:
                        self.mostrar_mensagem(self.tr("Não foi possível sobrescrever a camada existente: {error}").format(error=str(e)), "Erro")
                        return

                # Em vez de addMapLayer simples, insere no topo:
                self._top_insert_layer(point_layer)

                self.mostrar_mensagem(self.tr("Camada de pontos criada com sucesso."), "Sucesso")

                # Ativar os rótulos de 'NovoZ' na camada de pontos
                self.activate_labels_for_points(point_layer)

                # Criar a camada de linhas, incluindo a linha que fecha o polígono
                self.create_line_layer_from_points(points, selected_layer.crs())

                # Popula a scrollArea com os dados das camadas
                self.populate_scroll_area()

            else:
                self.mostrar_mensagem(self.tr("Selecione apenas 1 feição"), "Erro")

    def _get_active_polygon_feature(self, selected_layer):
        """Retorna a feição de polígono 'ativa' (selecionada; senão a primeira válida)."""
        features = [f for f in selected_layer.getFeatures()
                    if f.geometry() and not f.geometry().isEmpty()
                    and f.geometry().type() == Qgis.GeometryType.Polygon]
        if selected_layer.selectedFeatureCount() == 1:
            return selected_layer.selectedFeatures()[0]
        return features[0] if features else None

    def _get_poly_id_for_naming(self, selected_layer, feature):
        """
        Retorna o ID utilizado nos nomes das camadas.
        Valores numéricos inteiros, como 2.0, são exibidos como 2.
        IDs alfanuméricos permanecem inalterados.
        """
        if feature is None:
            return None

        field_names = [f.name() for f in selected_layer.fields()]

        for cand in ("ID", "Id", "id"):
            if cand not in field_names:
                continue

            val = feature[cand]

            if val is None:
                continue

            texto = str(val).strip()

            if not texto:
                continue

            # Corrige IDs numéricos armazenados como decimal:
            # 2.0 → 2
            # 15.0 → 15
            # 2.5 → 2.5
            try:
                numero = float(texto)

                if numero.is_integer():
                    return str(int(numero))
            except (TypeError, ValueError):
                pass

            return texto

        return str(feature.id())

    def _top_insert_layer(self, layer):
        """Insere a camada no grupo correspondente ao polígono/ID."""
        project = QgsProject.instance()
        root = project.layerTreeRoot()

        # Ex.: Polígonos Temporários_1_ID4_TIN
        #      → grupo Polígonos Temporários_1_ID4
        match = re.match(r"^(.*)_ID([^_]+)_", layer.name())

        if not match:
            project.addMapLayer(layer, False)
            root.insertLayer(0, layer)
            return

        nome_grupo = f"{match.group(1)}_ID{match.group(2)}"
        group = root.findGroup(nome_grupo)

        if not group:
            # Novo grupo sempre nasce no topo da árvore do QGIS
            group = root.insertGroup(0, nome_grupo)

        project.addMapLayer(layer, False)
        group.insertLayer(0, layer)

        node = group.findLayer(layer.id())

        if node:
            node.setExpanded(False)

        group.setExpanded(True)

    def _aplicar_aliases_campos(self, layer):
        """
        Aplica nomes traduzidos somente para exibição na tabela de atributos,
        mantendo inalterados os nomes internos usados pelo código.
        """
        if not isinstance(layer, QgsVectorLayer) or not layer.isValid():
            return

        aliases = {
            "ID": self.tr("ID"),
            "X": self.tr("X"),
            "Y": self.tr("Y"),
            "Z": self.tr("Z"),
            "NovoZ": self.tr("Novo Z"),
            "Desnível": self.tr("Desnível"),
            "Acumula_dist": self.tr("Distância Acumulada"),
            "Cota": self.tr("Cota"),
            "Comprimento": self.tr("Comprimento"),
            "Inclinação": self.tr("Inclinação")}

        for nome_campo, alias in aliases.items():
            indice = layer.fields().indexOf(nome_campo)

            if indice >= 0:
                layer.setFieldAlias(indice, alias)

    def create_line_layer_from_points(self, points, crs):
        """
        Cria uma camada de linhas conectando pontos sequenciais (fechando o polígono),
        calcula comprimento e inclinação dos segmentos e aplica simbologia e rótulos.
        """
        # Obter o nome da camada de polígono selecionada
        selected_polygon_id = self.comboBoxPoligono.currentData()
        selected_layer = QgsProject.instance().mapLayer(selected_polygon_id)
        if not selected_layer:
            return
        
        feature = self._get_active_polygon_feature(selected_layer)
        poly_id = self._get_poly_id_for_naming(selected_layer, feature)

        # Definir o nome da camada de linhas baseado na camada de polígono
        line_layer_name = f"{selected_layer.name()}_ID{poly_id}_{self.tr('Segmentos')}"

        # Se já existir, remover
        existing_layers = QgsProject.instance().mapLayersByName(line_layer_name)
        if existing_layers:
            try:
                QgsProject.instance().removeMapLayer(existing_layers[0].id())
            except Exception as e:
                self.mostrar_mensagem(self.tr("Não foi possível sobrescrever a camada existente: {error}").format(error=str(e)), "Erro")
                return

        # Cria a camada de linhas
        line_layer = QgsVectorLayer(f'LineString?crs={crs.authid()}', line_layer_name, 'memory')
        pr = line_layer.dataProvider()

        # # Adiciona campos "ID", "Comprimento", "Inclinação"
        pr.addAttributes([QgsField("ID", QMetaType.Type.Int),
                          QgsField("Comprimento", QMetaType.Type.Double, "", 20, 3),
                          QgsField("Inclinação",  QMetaType.Type.Double, "", 20, 6)])

        line_layer.updateFields()
        self._aplicar_aliases_campos(line_layer)

        num_points = len(points)

        for i in range(num_points):
            point1 = points[i]
            point2 = points[(i + 1) % num_points]  # Conecta o último ponto ao primeiro

            # Cria a linha entre dois pontos consecutivos
            line = QgsFeature(line_layer.fields())
            line_geom = QgsGeometry.fromPolylineXY([point1.geometry().asPoint(), point2.geometry().asPoint()])
            comprimento = round(line_geom.length(), 3)

            # Calcula a inclinação
            z1 = point1['NovoZ']
            z2 = point2['NovoZ']
            inclinacao = round((float(z2) - float(z1)) / comprimento if comprimento != 0 else 0, 5)

            # Atribui os valores à feição
            line.setGeometry(line_geom)
            line.setAttribute("ID", i + 1)
            line.setAttribute("Comprimento", comprimento)
            line.setAttribute("Inclinação", inclinacao)

            # Adiciona a linha à camada de linhas
            pr.addFeature(line)

        # Atribui a simbologia de seta à camada de linhas
        self.apply_arrow_symbology(line_layer)

        # Ativa os rótulos na camada de linhas (usando o campo "Inclinação" como exemplo)
        self.activate_labels_on_layer(line_layer, "Inclinação")

        # Em vez de addMapLayer simples:
        self._top_insert_layer(line_layer)
        self.mostrar_mensagem(self.tr("Camada de linhas criada com sucesso."), "Sucesso")

    def populate_scroll_area(self):
        """
        Preenche a área de rolagem com widgets contendo informações dos pontos e linhas
        das camadas geradas, permitindo edição visual dos valores.
        """
        # Reset the scroll area before setting it up again
        self.reset_scroll_area()

        # Obter o nome da camada de polígono selecionada
        selected_polygon_id = self.comboBoxPoligono.currentData()
        selected_layer = QgsProject.instance().mapLayer(selected_polygon_id)

        if not selected_layer:
            return

        feature = self._get_active_polygon_feature(selected_layer)
        poly_id = self._get_poly_id_for_naming(selected_layer, feature)

        # Definir o nome da camada de pontos baseada na camada de polígono
        point_layer_name = f"{selected_layer.name()}_ID{poly_id}_{self.tr('Vértices')}"
        line_layer_name = f"{selected_layer.name()}_ID{poly_id}_{self.tr('Segmentos')}"

        # Obter as camadas de pontos e linhas pelo nome dinâmico
        point_layer = QgsProject.instance().mapLayersByName(point_layer_name)
        line_layer  = QgsProject.instance().mapLayersByName(line_layer_name)

        if not point_layer or not line_layer:
            self.mostrar_mensagem(self.tr("Camadas '{point_layer_name}' ou '{line_layer_name}' não encontradas.").format(point_layer_name=point_layer_name, line_layer_name=line_layer_name), "Erro")
            return

        point_layer = point_layer[0]  # Obtém a primeira camada correspondente (espera-se que só haja uma)
        line_layer = line_layer[0]

        points = []
        lines = []

        # Extrair dados da camada de pontos
        for feature in point_layer.getFeatures():
            point_data = {
                'ID': feature['ID'],
                'X': feature['X'],
                'Y': feature['Y'],
                'Z': feature['Z'],
                'NovoZ': feature['NovoZ']}
            points.append(point_data)

        # Extrair dados da camada de linhas
        for feature in line_layer.getFeatures():
            line_data = {
                'ID': feature['ID'],
                'Inclinação': feature['Inclinação'],
                'Comprimento': feature['Comprimento']}
            lines.append(line_data)

        # Popula a scroll area com os dados obtidos
        self.setup_scroll_area(points, lines)

    def setup_scroll_area(self, points, lines):
        """
        Monta os widgets da scrollArea em uma grade única, mantendo
        cabeçalhos e campos perfeitamente alinhados entre si.
        """
        self.points = points
        self.lines = lines

        # Certifica-se de que o layout principal da scrollArea exista.
        layout = self.scrollAreaWidgetContents.layout()

        if layout is None:
            layout = QVBoxLayout(self.scrollAreaWidgetContents)
            self.scrollAreaWidgetContents.setLayout(layout)
        else:
            self.clear_layout(layout)

        self.scroll_widgets = []

        # Grade única para cabeçalho + dados
        grid = QGridLayout()
        grid.setContentsMargins(0, 0, 0, 0)
        grid.setHorizontalSpacing(5)
        grid.setVerticalSpacing(3)

        # Larguras mínimas das colunas.
        # O QGridLayout poderá ampliá-las se a tradução exigir.
        grid.setColumnMinimumWidth(0, 38)   # IDs
        grid.setColumnMinimumWidth(1, 52)   # Z
        grid.setColumnMinimumWidth(2, 58)   # NovoZ
        grid.setColumnMinimumWidth(3, 70)   # Inclinação
        grid.setColumnMinimumWidth(4, 70)   # Desnível

        grid.setColumnStretch(0, 0)
        grid.setColumnStretch(1, 1)
        grid.setColumnStretch(2, 1)
        grid.setColumnStretch(3, 1)
        grid.setColumnStretch(4, 1)

        # Cabeçalhos
        headers = [
            self.tr("IDs"),
            self.tr("Z"),
            self.tr("NovoZ"),
            self.tr("Inclinação"),
            self.tr("Desnível")]

        for coluna, texto in enumerate(headers):
            label = QLabel(texto)
            label.setAlignment(Qt.AlignmentFlag.AlignCenter)
            label.setStyleSheet("font-weight: bold;")
            grid.addWidget(label, 0, coluna)

        # Linhas dos pontos
        for i, point in enumerate(points):
            linha = i + 1

            # ID
            label_id = QLabel(self.tr("ID: {id}").format(id=i + 1))
            label_id.setAlignment(Qt.AlignmentFlag.AlignLeft | Qt.AlignmentFlag.AlignVCenter)
            label_id.setFixedHeight(21)
            label_id.setMinimumWidth(38)
            grid.addWidget(label_id, linha, 0)

            # Z
            line_edit_z = QLineEdit()
            line_edit_z.setText(str(point['Z']))
            line_edit_z.setReadOnly(True)
            line_edit_z.setAlignment(Qt.AlignmentFlag.AlignCenter)
            line_edit_z.setFixedHeight(21)
            line_edit_z.setMinimumWidth(52)
            grid.addWidget(line_edit_z, linha, 1)

            # NovoZ
            line_edit_novoz = QLineEdit()
            line_edit_novoz.setText(str(point['NovoZ']))
            line_edit_novoz.setAlignment(Qt.AlignmentFlag.AlignCenter)
            line_edit_novoz.setFixedHeight(21)
            line_edit_novoz.setMinimumWidth(58)
            line_edit_novoz.setStyleSheet("background-color: #e0f7ff; font-style: italic; font-weight: bold; font-size: 7.8pt;")

            regex = QRegularExpression(r"-?\d+(?:[.,]\d{0,3})?")
            line_edit_novoz.setValidator(QRegularExpressionValidator(regex, line_edit_novoz))
            line_edit_novoz.editingFinished.connect(lambda idx=i: self.update_novoz(idx))

            grid.addWidget(line_edit_novoz, linha, 2)

            # Inclinação
            line_edit_inclinacao = QLineEdit()

            if i < len(lines):
                inc = lines[i].get('Inclinação', 0.0)
                line_edit_inclinacao.setText(f"{inc * 100:.3f}%")
                self._apply_inclinacao_style(line_edit_inclinacao, inc * 100)
            else:
                line_edit_inclinacao.setText("0.000%")
                self._apply_inclinacao_style(line_edit_inclinacao, 0.0)

            line_edit_inclinacao.setReadOnly(False)
            line_edit_inclinacao.setAlignment(Qt.AlignmentFlag.AlignCenter)
            line_edit_inclinacao.setFixedHeight(21)
            line_edit_inclinacao.setMinimumWidth(70)

            regex_inc = QRegularExpression(r"^-?\d+(?:[.,]\d{1,3})?\s*%?$")
            line_edit_inclinacao.setValidator(QRegularExpressionValidator(regex_inc, line_edit_inclinacao))
            line_edit_inclinacao.setProperty("user_edited", False)

            line_edit_inclinacao.textEdited.connect(
                lambda _t, le=line_edit_inclinacao: le.setProperty("user_edited", True))

            line_edit_inclinacao.editingFinished.connect(
                lambda idx=i, le=line_edit_inclinacao: self._on_inclinacao_edit_finished(idx, le))

            grid.addWidget(line_edit_inclinacao, linha, 3)

            # Desnível
            spin_box_desnivel = QDoubleSpinBox()
            spin_box_desnivel.setDecimals(3)
            spin_box_desnivel.setMinimum(-9999.99)
            spin_box_desnivel.setMaximum(9999.99)
            spin_box_desnivel.setSingleStep(0.5)

            desnivel = point['NovoZ'] - point['Z']

            spin_box_desnivel.setValue(desnivel)
            self._apply_desnivel_style(spin_box_desnivel, desnivel)

            spin_box_desnivel.setAlignment(Qt.AlignmentFlag.AlignCenter)
            spin_box_desnivel.setFixedHeight(21)
            spin_box_desnivel.setMinimumWidth(70)
            spin_box_desnivel.setKeyboardTracking(False)
            spin_box_desnivel.setCorrectionMode(QAbstractSpinBox.CorrectionMode.CorrectToNearestValue)
            spin_box_desnivel.editingFinished.connect(lambda idx=i: self._on_desnivel_edit_finished(idx))

            grid.addWidget(spin_box_desnivel, linha, 4)

            # Distância do segmento i -> i+1
            dist_i = 0.0

            if i < len(lines):
                dist_i = (lines[i].get('Dist')
                    or lines[i].get('Distancia')
                    or lines[i].get('Distância')
                    or lines[i].get('Comprimento')
                    or 0.0)

            self.scroll_widgets.append({
                'line_edit_novoz': line_edit_novoz,
                'line_edit_inclinacao': line_edit_inclinacao,
                'spin_box_desnivel': spin_box_desnivel,
                'z_val': float(point['Z']),
                'dist': float(dist_i)})

            spin_box_desnivel.valueChanged.connect(
                lambda val, idx=i: self.update_desnivel(val, idx))

        layout.addLayout(grid)
        layout.addStretch()

    def _apply_desnivel_style(self, spin: QDoubleSpinBox, value: float):
        """Aplica cor ao texto do Desnível (+ azul, - vermelho, 0 preto), mantendo o estilo atual."""
        if value > 0:
            color = "#0000ff"   # azul
        elif value < 0:
            color = "#CC0000"   # vermelho
        else:
            color = "#000000"   # preto
        # mantém seu fundo/estilo; só garante a cor do texto
        spin.setStyleSheet("background-color: #e0f7ff; color: %s;" % color)

    def _apply_inclinacao_style(self, le: QLineEdit, pct_value: float):
        """Aplica o estilo do campo de Inclinação com cor por sinal (+ azul, - vermelho, 0 preto)."""
        if pct_value > 0:
            color = "#0066CC"   # azul
        elif pct_value < 0:
            color = "#CC0000"   # vermelho
        else:
            color = "#000000"   # preto

        base = "background-color: #e0f7ff; font-style: italic; font-weight: bold; font-size: 7.9pt;"
        le.setStyleSheet(base + f" color: {color};")

    def _on_desnivel_edit_finished(self, idx: int):
        """Aplica o desnível apenas quando o usuário sai do spin (editingFinished)."""
        if idx < 0 or idx >= len(self.scroll_widgets):
            return
        val = self.scroll_widgets[idx]['spin_box_desnivel'].value()
        self.update_desnivel(val, idx)

    def _fmt(self, v: float, prec: int = 3) -> str:
        """Formata número com casas decimais, usando ponto."""
        try:
            return f"{float(v):.{prec}f}"
        except Exception:
            return ""

    def _parse_float(self, v, default=0.0) -> float:
        """Converte texto para float aceitando vírgula/ponto e '%' opcional."""
        try:
            s = str(v).strip().replace("%", "").replace(" ", "")
            s = s.replace(",", ".")
            return float(s)
        except Exception:
            return default

    def _fmt_pct(self, v: float, prec: int = 3) -> str:
        """Formata porcentagem com sufixo %."""
        try:
            return f"{float(v):.{prec}f}%"
        except Exception:
            return f"{v}%"

    def _on_inclinacao_edit_finished(self, idx: int, le: QLineEdit):
        """
        Nova lógica:
        - Ao editar a Inclinação do segmento i (linha i), ajusta-se NovoZ[i+1],
          mantendo NovoZ[i] fixo, de modo que:
             (NovoZ[i+1] - NovoZ[i]) / dist_i  ==  inclinação_digitada
        - Em seguida, recalcula as inclinações e desníveis (o que atualiza também a
          Inclinação da linha i+1 e quaisquer segmentos afetados).
        """
        if idx < 0 or idx >= len(self.scroll_widgets):
            return
        # Só executa se houve edição REAL do usuário
        if not le.property("user_edited"):
            return

        # Distância do segmento i (i -> i+1)
        dist = float(self.scroll_widgets[idx].get('dist', 0.0) or 0.0)
        if dist == 0.0:
            le.setProperty("user_edited", False)
            return

        # % digitado
        pct_novo = self._parse_float(le.text(), 0.0)

        # ΔZ do SEGMENTO i
        dz_seg = (pct_novo / 100.0) * dist

        n = len(self.points)
        i_next = (idx + 1) % n

        # Mantém NovoZ[i], ajusta NovoZ[i+1] = NovoZ[i] + ΔZ_seg
        novoz_i = float(self.points[idx]['NovoZ'])
        novo_novoz_next = round(novoz_i + dz_seg, 3)

        # Atualiza modelo e UI do NovoZ do PRÓXIMO vértice
        self.points[i_next]['NovoZ'] = novo_novoz_next
        le_nz_next = self.scroll_widgets[i_next]['line_edit_novoz']
        le_nz_next.blockSignals(True)
        le_nz_next.setText(f"{novo_novoz_next:.3f}")
        le_nz_next.blockSignals(False)

        # Atualiza Desnível do próximo: NovoZ[i+1] - Z[i+1]
        z_orig_next = float(self.points[i_next]['Z'])
        desnivel_next = round(novo_novoz_next - z_orig_next, 3)
        sb_next = self.scroll_widgets[i_next]['spin_box_desnivel']
        sb_next.blockSignals(True)
        sb_next.setValue(desnivel_next)
        sb_next.blockSignals(False)

        # Aplica a cor (azul >0, vermelho <0, preto =0)
        self._apply_desnivel_style(sb_next, desnivel_next)

        # Normaliza o texto digitado e limpa a flag de edição
        le.blockSignals(True)
        le.setText(f"{pct_novo:.3f}%")
        le.setProperty("user_edited", False)
        self._apply_inclinacao_style(le, pct_novo)   # <<< AQUI
        le.blockSignals(False)

        # Recalcula TODAS as inclinações/desníveis a partir dos NovoZ atualizados
        # (Isso ajusta também a Inclinação da linha i+1 e mantém tudo consistente.)
        self.recalculate_inclination_and_desnivel()

    def recalculate_inclination_and_desnivel(self):
        """
        Recalcula inclinação dos segmentos e desnível de cada ponto,
        atualizando a UI sem disparar sinais de edição.
        """
        num_points = len(self.points)
        if num_points == 0:
            return

        for i in range(num_points):
            # Segmento anterior (i-1 -> i), escrevendo na linha (i-1)
            prev_idx = num_points - 1 if i == 0 else i - 1
            z1 = float(self.points[prev_idx]['NovoZ'])
            z2 = float(self.points[i]['NovoZ'])
            comp_prev = float(self.lines[prev_idx]['Comprimento']) if self.lines else 0.0
            inc_prev = (z2 - z1) / comp_prev if comp_prev != 0.0 else 0.0

            # Linha (i-1): inclinação do segmento anterior
            le_prev = self.scroll_widgets[prev_idx]['line_edit_inclinacao']
            le_prev.blockSignals(True)
            le_prev.setText(f"{inc_prev*100:.3f}%")
            le_prev.setProperty("user_edited", False)  # <<< zera a flag após atualização programática
            self._apply_inclinacao_style(le_prev, inc_prev*100)   # <<< AQUI
            le_prev.blockSignals(False)

            # Segmento posterior (i -> i+1), escrevendo na linha i
            next_idx = 0 if i == num_points - 1 else i + 1
            z1p = float(self.points[i]['NovoZ'])
            z2p = float(self.points[next_idx]['NovoZ'])
            comp_i = float(self.lines[i]['Comprimento']) if self.lines else 0.0
            inc_post = (z2p - z1p) / comp_i if comp_i != 0.0 else 0.0

            # Linha i: inclinação do segmento posterior
            le_i = self.scroll_widgets[i]['line_edit_inclinacao']
            le_i.blockSignals(True)
            le_i.setText(f"{inc_post*100:.3f}%")
            le_i.setProperty("user_edited", False)     # <<< idem
            self._apply_inclinacao_style(le_i, inc_post*100)
            le_i.blockSignals(False)

            # Desnível do ponto i
            z_orig = float(self.points[i]['Z'])
            z_new  = float(self.points[i]['NovoZ'])
            desn = round(z_new - z_orig, 3)

            sb_dz = self.scroll_widgets[i]['spin_box_desnivel']
            sb_dz.blockSignals(True)
            sb_dz.setValue(desn)
            self._apply_desnivel_style(sb_dz, desn) # Altera as cores
            sb_dz.blockSignals(False)

    def update_desnivel(self, val, idx):
        """
        Atualiza o valor de NovoZ de um ponto a partir do desnível informado.
        Também sincroniza o campo NovoZ na interface e recalcula inclinações e desníveis.
        """

        try:
            desnivel = float(val)   # converte o valor recebido em número
        except ValueError:
            return  # se não for número válido, sai da função

        # calcula o NovoZ: Z original + desnível
        novo_z = round(self.points[idx]['Z'] + desnivel, 3)
        self.points[idx]['NovoZ'] = novo_z  # atualiza no modelo de dados

        # atualiza o QLineEdit de NovoZ na interface
        le_nz = self.scroll_widgets[idx]['line_edit_novoz']
        le_nz.blockSignals(True)  # evita disparar sinais recursivos
        le_nz.setText(f"{novo_z:.3f}")  # mostra sempre com 3 casas decimais
        le_nz.blockSignals(False)

        # recalcula todas as inclinações e desníveis para manter a consistência
        self.recalculate_inclination_and_desnivel()

    def update_novoz(self, idx):
        """
        Atualiza o valor de NovoZ de um ponto a partir do valor digitado no QLineEdit.
        Também sincroniza o dado com a lista de pontos e recalcula inclinações/desníveis.
        """
        # obtém o QLineEdit correspondente ao NovoZ do ponto
        le_nz = self.scroll_widgets[idx]['line_edit_novoz']
        # substitui vírgula por ponto para permitir entrada com vírgula decimal
        text = le_nz.text().replace(',', '.')

        try:
            # converte o texto para float e arredonda para 3 casas
            novo_z = round(float(text), 3)
        except ValueError:
            return  # se não for um número válido, não faz nada

        # atualiza o valor no modelo de dados (self.points)
        self.points[idx]['NovoZ'] = novo_z

        # atualiza o QLineEdit programaticamente (sem disparar sinais)
        le_nz.blockSignals(True)
        le_nz.setText(f"{novo_z:.3f}")  # garante formato com 3 casas decimais
        le_nz.blockSignals(False)

        # recalcula todas as inclinações e desníveis para manter consistência
        self.recalculate_inclination_and_desnivel()

    def update_layers(self):
        """
        Atualiza os valores dos campos 'NovoZ' na camada de pontos e 'Inclinação' na camada de linhas,
        sincronizando-os com os dados editados na interface.
        """
        # Obter o nome da camada de polígono selecionada
        selected_polygon_id = self.comboBoxPoligono.currentData()
        selected_layer = QgsProject.instance().mapLayer(selected_polygon_id)
        if not selected_layer:
            # self.mostrar_mensagem("Camada de polígono não encontrada.", "Erro")
            return

        feature = self._get_active_polygon_feature(selected_layer)
        poly_id = self._get_poly_id_for_naming(selected_layer, feature)

        # Definir os nomes das camadas de pontos e linhas baseados na camada de polígono
        point_layer_name = f"{selected_layer.name()}_ID{poly_id}_{self.tr('Vértices')}"
        line_layer_name = f"{selected_layer.name()}_ID{poly_id}_{self.tr('Segmentos')}"

        # Obter as camadas pelo nome dinâmico
        point_layer = QgsProject.instance().mapLayersByName(point_layer_name)
        line_layer  = QgsProject.instance().mapLayersByName(line_layer_name)

        if not point_layer or not line_layer:
            self.mostrar_mensagem(self.tr("Camadas '{point_layer_name}' ou '{line_layer_name}' não encontradas.").format(point_layer_name=point_layer_name, line_layer_name=line_layer_name), "Erro")
            return

        point_layer = point_layer[0]  # Espera-se que só haja uma camada correspondente
        line_layer = line_layer[0]

        # Atualizar NovoZ na camada de pontos
        point_layer.startEditing()
        for i, feature in enumerate(point_layer.getFeatures()):
            feature['NovoZ'] = self.points[i]['NovoZ']
            point_layer.updateFeature(feature)
        point_layer.commitChanges()

        # Atualizar Inclinação na camada de linhas
        line_layer.startEditing()

        num_points = len(self.points)

        for i, feature in enumerate(line_layer.getFeatures()):
            # Conectar o último ponto ao primeiro
            point1 = self.points[i]
            point2 = self.points[(i + 1) % num_points]  # Usa o operador % para fechar o polígono

            # Recalcular a inclinação entre os pontos
            z1 = point1['NovoZ']
            z2 = point2['NovoZ']
            comprimento = feature.geometry().length()

            # DEPOIS (guarda a fração com 6 casas; o rótulo formata)
            inclinacao = (float(z2) - float(z1)) / comprimento if comprimento != 0 else 0.0
            feature['Inclinação'] = round(inclinacao, 6)

            line_layer.updateFeature(feature)

        line_layer.commitChanges()

        self.mostrar_mensagem(self.tr("Camadas de pontos e linhas atualizadas com sucesso."), "Sucesso")

    def calculate_and_create_segment_layers(self):
        """
        Atualiza as camadas de pontos e linhas existentes, cria novas camadas de pontos para cada segmento
        e atualiza a lista de segmentos na interface.
        """
        # Primeiro, atualize as camadas de pontos e linhas existentes
        self.update_layers()

        # Em seguida, crie as camadas de pontos para cada segmento
        selected_polygon_id = self.comboBoxPoligono.currentData()
        selected_layer = QgsProject.instance().mapLayer(selected_polygon_id)

        if not selected_layer:
            return

        feature = self._get_active_polygon_feature(selected_layer)
        poly_id = self._get_poly_id_for_naming(selected_layer, feature)

        # Obter a camada de pontos
        point_layer_name = f"{selected_layer.name()}_ID{poly_id}_{self.tr('Vértices')}"
        point_layer = QgsProject.instance().mapLayersByName(point_layer_name)

        if not point_layer:
            self.mostrar_mensagem(self.tr("Camada '{point_layer_name}' não encontrada.").format(point_layer_name=point_layer_name), "Erro")
            return

        point_layer = point_layer[0]

        # Obter os pontos da camada de pontos
        points = [f for f in point_layer.getFeatures()]
        
        # Criar camadas de pontos para cada segmento
        self.create_point_layer_for_segments(points)

        # Atualizar o listWidgetSegmentos após criar as camadas de segmentos
        self.update_list_widget_segmentos()

        self.mostrar_mensagem(self.tr("Camadas de segmentos criadas com sucesso."), "Sucesso")

    def create_point_layer_for_segments(self, points):
        """
        Cria camadas de pontos temporárias para cada segmento do polígono, 
        agrupando-as e adicionando ao projeto para análise individual dos segmentos.
        """
        # Obter o nome da camada de polígono selecionada
        selected_polygon_id = self.comboBoxPoligono.currentData()
        selected_layer = QgsProject.instance().mapLayer(selected_polygon_id)
        if not selected_layer:
            # self.mostrar_mensagem("Camada de polígono não encontrada.", "Erro")
            return

        # Cria ou acessa o grupo baseado no nome da camada de polígono
        root = QgsProject.instance().layerTreeRoot()
        group = root.findGroup(self.tr("Segmentos"))
        if not group:
            group = root.addGroup(self.tr("Segmentos"))
        else:
            # Limpar camadas existentes no grupo antes de adicionar novas camadas
            group.removeAllChildren()

        # Iterar sobre os segmentos dos pontos
        num_points = len(points)
        for i in range(num_points):
            # Definir o nome da camada de pontos para o segmento
            feature = self._get_active_polygon_feature(selected_layer)
            poly_id = self._get_poly_id_for_naming(selected_layer, feature)

            segment_id = self.tr("Segmento_{start}_{end}").format(start=i + 1, end=(i + 2) if i + 1 < num_points else 1)
            point_layer_name = f"{selected_layer.name()}_ID{poly_id}_{segment_id}"

            point_layer = QgsVectorLayer('Point?crs=' + selected_layer.crs().authid(), point_layer_name, 'memory')
            pr = point_layer.dataProvider()

            # Adicionar campos "ID", "X", "Y", "Z", "NovoZ"
            pr.addAttributes([QgsField("ID", QMetaType.Type.Int),
                              QgsField("X", QMetaType.Type.Double),
                              QgsField("Y", QMetaType.Type.Double),
                              QgsField("Z", QMetaType.Type.Double),
                              QgsField("NovoZ", QMetaType.Type.Double)])
            point_layer.updateFields()
            self._aplicar_aliases_campos(point_layer)

            # Adicionar os dois pontos do segmento à nova camada de pontos
            point1 = points[i]
            point2 = points[(i + 1) % num_points]  # Conecta o último ponto ao primeiro

            for j, point in enumerate([point1, point2]):
                feature = QgsFeature(point_layer.fields())
                x = point.geometry().asPoint().x()
                y = point.geometry().asPoint().y()

                # Definir valores para os atributos
                feature.setGeometry(QgsGeometry.fromPointXY(QgsPointXY(x, y)))
                feature.setAttribute("ID", j + 1)
                feature.setAttribute("X", round(x, 3))
                feature.setAttribute("Y", round(y, 3))
                feature.setAttribute("Z", point['Z'])
                feature.setAttribute("NovoZ", point['NovoZ'])

                pr.addFeature(feature)

            # Adicionar a nova camada de pontos ao projeto
            QgsProject.instance().addMapLayer(point_layer, False)  # Adiciona a camada sem mostrar na árvore de camadas
            group.insertLayer(0, point_layer)  # Adiciona a camada ao grupo
            self.mostrar_mensagem(self.tr("Camada de pontos '{point_layer_name}' criada com sucesso.").format(point_layer_name=point_layer_name), "Sucesso")

    def calculate_distance_and_update_spinbox(self):
        """
        Calcula a distância entre dois pontos na camada selecionada e ajusta
        o valor máximo do spinbox de equidistância conforme o resultado.
        """
        # Obter a camada selecionada no listWidgetSegmentos
        selected_item = self.listWidgetSegmentos.currentItem()
        if not selected_item:
            self.mostrar_mensagem(self.tr("Nenhuma camada selecionada no listWidgetSegmentos."), "Erro")
            return

        # Obter a camada de pontos a partir do nome da camada
        layer_name = selected_item.text()
        layer = QgsProject.instance().mapLayersByName(layer_name)
        if not layer:
            self.mostrar_mensagem(self.tr("Camada '{layer_name}' não encontrada.").format(layer_name=layer_name), "Erro")
            return
        layer = layer[0]

        # Verificar se a camada possui exatamente dois pontos
        points = [f for f in layer.getFeatures()]
        if len(points) != 2:
            self.mostrar_mensagem(self.tr("A camada selecionada deve conter exatamente dois pontos."), "Erro")
            return

        # Calcular a distância entre os dois pontos
        point1 = points[0].geometry().asPoint()
        point2 = points[1].geometry().asPoint()
        distance = point1.distance(point2)

        # Atualizar o valor máximo do doubleSpinBoxEquidistante
        self.doubleSpinBoxEquidistante.setMinimum(0.1)
        self.doubleSpinBoxEquidistante.setMaximum(distance)
        self.mostrar_mensagem(self.tr("Camada '{layer_name}' não encontrada.").format(layer_name=layer_name), "Erro")

    def calculate_intermediate_points(self):
        """
        Gera pontos intermediários equidistantes entre dois pontos selecionados,
        cria uma nova camada de estaqueamento e aplica simbologia e rótulos.
        """
        # Guarda a linha atual para avançar somente após concluir
        # toda a substituição da camada de estaqueamento.
        current_row = self.listWidgetSegmentos.currentRow()

        # Obter a camada selecionada no listWidgetSegmentos
        selected_item = self.listWidgetSegmentos.currentItem()
        if not selected_item:
            self.mostrar_mensagem(self.tr("Nenhuma camada selecionada no listWidgetSegmentos."), "Erro")
            return

        # Obter a camada de pontos a partir do nome da camada
        layer_name = selected_item.text()
        layer = QgsProject.instance().mapLayersByName(layer_name)
        if not layer:
            self.mostrar_mensagem(self.tr("Camada '{layer_name}' não encontrada.").format(layer_name=layer_name), "Erro")
            return
        layer = layer[0]

        # Verificar se a camada possui exatamente dois pontos
        points = [f for f in layer.getFeatures()]
        if len(points) != 2:
            self.mostrar_mensagem(self.tr("A camada selecionada deve conter exatamente dois pontos."), "Erro")
            return

        # Obter o valor selecionado no doubleSpinBoxEquidistante
        equidistance = self.doubleSpinBoxEquidistante.value()

        # Verificar se o valor da equidistância é maior que zero
        if equidistance <= 0:
            self.mostrar_mensagem(self.tr("O valor da equidistância deve ser maior que zero."), "Erro")
            return

        # Calcular a distância entre os dois pontos
        point1 = points[0].geometry().asPoint()
        point2 = points[1].geometry().asPoint()
        total_distance = point1.distance(point2)

        # Verificar se a distância total entre os pontos é maior que zero
        if total_distance == 0:
            self.mostrar_mensagem(self.tr("Os dois pontos são coincidentes. A distância entre eles é zero."), "Erro")
            return

        # Monta somente as distâncias estritamente internas ao segmento.
        distancias_intermediarias = []
        distancia_atual = equidistance
        tolerancia = max(1e-9, total_distance * 1e-12)

        while distancia_atual < total_distance - tolerancia:
            distancias_intermediarias.append(distancia_atual)
            distancia_atual += equidistance

        # Obter o raster selecionado para capturar o valor de Z
        selected_raster_id = self.comboBoxRaster.currentData()
        raster_layer = QgsProject.instance().mapLayer(selected_raster_id)

        if not raster_layer or not isinstance(raster_layer, QgsRasterLayer):
            self.mostrar_mensagem(self.tr("Camada raster inválida ou não selecionada."), "Erro")
            return

        # Obter o NovoZ dos dois pontos
        novo_z1 = float(points[0]["NovoZ"])
        novo_z2 = float(points[1]["NovoZ"])
        inclination = (novo_z2 - novo_z1) / total_distance

        # Valida todas as cotas antes de remover uma camada anterior.
        distancias_pontos = [0.0] + distancias_intermediarias + [total_distance]
        dados_pontos = []

        for distancia in distancias_pontos:
            t = distancia / total_distance
            x = (1.0 - t) * point1.x() + t * point2.x()
            y = (1.0 - t) * point1.y() + t * point2.y()
            z = self.get_z_value(x, y)

            if z is None:
                return

            if distancia <= tolerancia:
                novo_z = novo_z1
            elif abs(distancia - total_distance) <= tolerancia:
                novo_z = novo_z2
            else:
                novo_z = novo_z1 + inclination * distancia

            dados_pontos.append((distancia, x, y, float(z), float(novo_z)))

        # Criar ou acessar o grupo "Estaqueamentos"
        root = QgsProject.instance().layerTreeRoot()
        group = root.findGroup(self.tr("Estaqueamentos"))

        if not group:
            group = root.addGroup(self.tr("Estaqueamentos"))

        # Extrai os números finais sem depender da tradução de "Segmento".
        try:
            prefixo_segmento, inicio, fim = layer_name.rsplit("_", 2)
            base_name, _rotulo_segmento = prefixo_segmento.rsplit("_", 1)
        except ValueError:
            self.mostrar_mensagem(self.tr("Nome da camada fora do padrão esperado: '{layer_name}'.").format(layer_name=layer_name), "Erro")
            return

        new_layer_name = f"{base_name}_{self.tr('Estacas')}_{inicio}_{fim}"

        # Só remove a versão anterior depois que todas as amostras forem validadas.
        exist = QgsProject.instance().mapLayersByName(new_layer_name)

        if exist:
            QgsProject.instance().removeMapLayer(exist[0].id())

        crs = layer.crs()
        new_point_layer = QgsVectorLayer(f"Point?crs={crs.authid()}", new_layer_name, "memory")
        pr = new_point_layer.dataProvider()

        pr.addAttributes([
            QgsField("ID", QMetaType.Type.Int),
            QgsField("X", QMetaType.Type.Double),
            QgsField("Y", QMetaType.Type.Double),
            QgsField("Z", QMetaType.Type.Double),
            QgsField("NovoZ", QMetaType.Type.Double),
            QgsField("Desnível", QMetaType.Type.Double),
            QgsField("Acumula_dist", QMetaType.Type.Double)])

        new_point_layer.updateFields()
        self._aplicar_aliases_campos(new_point_layer)

        features_out = []

        for feature_id, (distancia, x, y, z, novo_z) in enumerate(dados_pontos, start=1):
            feature = QgsFeature(new_point_layer.fields())
            feature.setGeometry(QgsGeometry.fromPointXY(QgsPointXY(x, y)))
            feature.setAttribute("ID", feature_id)
            feature.setAttribute("X", round(x, 3))
            feature.setAttribute("Y", round(y, 3))
            feature.setAttribute("Z", round(z, 3))
            feature.setAttribute("NovoZ", round(novo_z, 3))
            feature.setAttribute("Desnível", round(novo_z - z, 3))
            feature.setAttribute("Acumula_dist", round(distancia, 3))
            features_out.append(feature)

        pr.addFeatures(features_out)

        # Adicionar a nova camada de pontos ao grupo "Estaqueamento"
        QgsProject.instance().addMapLayer(new_point_layer, False)  # Adiciona a camada sem mostrar na árvore de camadas
        group.insertLayer(0, new_point_layer)  # Adiciona a camada ao grupo

        # Colapsa (fecha) a camada recém-criada no painel de camadas
        layer_node = group.findLayer(new_point_layer.id())
        if layer_node is not None:
            layer_node.setExpanded(False)

        self.mostrar_mensagem(self.tr("Camada '{new_layer_name}' criada e adicionada ao grupo '{group_name}'.").format(new_layer_name=new_layer_name, group_name=self.tr("Estaqueamentos")), "Sucesso")

        # Aplicar os rótulos à nova camada
        self.set_label_for_layer(new_point_layer, "Desnível")

        # Aplica a simbologia de desnível imediatamente após criar a camada
        self.apply_desnivel_symbology(new_point_layer)

        # Atualizar o listWidgetEstacas logo após a criação da camada
        self.update_list_widget_estaqueamentos()

        # Atualiza novamente os segmentos somente após remover e recriar
        # a camada de estaqueamento, evitando que os sinais intermediários
        self.update_list_widget_segmentos()
        self._selecionar_proximo_item(self.listWidgetSegmentos, current_row)

    def set_label_for_layer(self, layer, field_name):
        """
        Configura o rótulo para uma camada no QGIS, com base em um campo específico e formatações adicionais.
        """
        label_settings = QgsPalLayerSettings()
        label_settings.drawBackground = True  # Ativa o fundo do rótulo
        label_settings.fieldName = field_name  # Define o campo a ser rotulado

        # Configura a formatação do texto
        text_format = label_settings.format()
        font = text_format.font()
        font.setItalic(True)
        font.setBold(True)
        text_format.setFont(font)

        # Configura a cor do rótulo com base em uma expressão condicional
        color_expression = """CASE
                                WHEN "Desnível" < 0 THEN '255,0,0'  -- Vermelho
                                WHEN "Desnível" > 0 THEN '0,0,255'  -- Azul
                                ELSE '0,0,0'  -- Preto
                              END"""

        properties = label_settings.dataDefinedProperties()
        properties.setProperty(QgsPalLayerSettings.Property.Color, QgsProperty.fromExpression(color_expression))

        # Defina o tamanho da fonte usando propriedades definidas por dados
        properties.setProperty(QgsPalLayerSettings.Property.Size, QgsProperty.fromValue(8))
        label_settings.setDataDefinedProperties(properties)

        # Configura o fundo branco para os rótulos
        background_color = text_format.background()
        background_color.setEnabled(True)
        background_color.setFillColor(QColor(255, 255, 255))
        text_format.setBackground(background_color)

        label_settings.setFormat(text_format)

        # Ativa o rótulo para a camada
        layer.setLabelsEnabled(True)
        layer.setLabeling(QgsVectorLayerSimpleLabeling(label_settings))
        layer.triggerRepaint()

    def apply_desnivel_symbology(self, layer):
        """
        Colore uma camada de estaqueamento conforme o valor do campo 'Desnível',
        e aplica borda da mesma cor:
          > 0  → marcador azul com borda azul
          < 0  → marcador vermelho com borda vermelha
          = 0  → marcador cinza com borda cinza
        """

        # garante que seja camada de pontos
        if not layer or layer.geometryType() != Qgis.GeometryType.Point:
            return

        # cria símbolos com cor de fill e contorno (outline) iguais
        sym_blue = QgsMarkerSymbol.createSimple({'color': 'blue', 'outline_color': 'blue', 'outline_width': '0.1','size': '2'})
        sym_red = QgsMarkerSymbol.createSimple({'color': 'red', 'outline_color': 'red', 'outline_width': '0.1', 'size': '2'})
        sym_gray = QgsMarkerSymbol.createSimple({'color': 'gray', 'outline_color': 'gray', 'outline_width': '0.1', 'size': '2'})

        # nó raiz para o renderer baseado em regras
        root = QgsRuleBasedRenderer.Rule(None)

        # regra Aterro > 0
        rule_blue = QgsRuleBasedRenderer.Rule(sym_blue)
        rule_blue.setFilterExpression('"Desnível" > 0')
        rule_blue.setLabel(self.tr("Aterro > 0"))
        root.appendChild(rule_blue)

        # regra Corte < 0
        rule_red = QgsRuleBasedRenderer.Rule(sym_red)
        rule_red.setFilterExpression('"Desnível" < 0')
        rule_red.setLabel(self.tr("Corte < 0"))
        root.appendChild(rule_red)

        # regra Sem movimento = 0
        rule_gray = QgsRuleBasedRenderer.Rule(sym_gray)
        rule_gray.setFilterExpression('"Desnível" = 0')
        rule_gray.setLabel(self.tr("Sem alteração = 0"))
        root.appendChild(rule_gray)

        # aplica o renderer e repinta
        layer.setRenderer(QgsRuleBasedRenderer(root))
        layer.triggerRepaint()

    def get_z_value(self, x, y):
        """
        Obtém o valor de elevação (Z) do raster selecionado nas coordenadas (x, y).
        Exibe mensagem de erro caso não seja possível obter o valor.
        """
        selected_raster_id = self.comboBoxRaster.currentData()
        raster_layer = QgsProject.instance().mapLayer(selected_raster_id)
        
        if not raster_layer or not isinstance(raster_layer, QgsRasterLayer):
            self.mostrar_mensagem(self.tr("Camada raster inválida ou não selecionada."), "Erro")
            return None
        
        identify_result = raster_layer.dataProvider().identify(QgsPointXY(x, y), Qgis.RasterIdentifyFormat.Value)
        
        if identify_result.isValid():
            results = identify_result.results()
            if results:
                band_key = list(results.keys())[0]
                z_value = results.get(band_key)
                if z_value is not None:
                    return round(float(z_value), 3)

        # Se não conseguir identificar o valor Z, retorna None
        self.mostrar_mensagem(self.tr("Não foi possível identificar o valor Z nas coordenadas ({x}, {y}).").format(x=x, y=y), "Erro")
        return None

    def find_matching_talude_layers(self, estacas_layer_name, talude_layers_dict):
        """Encontra as camadas de Talude correspondentes com base no nome da camada de Estacas."""
        matching_layers = []
        for talude_layer_name in talude_layers_dict.keys():
            # Verificar se o nome da camada de Talude contém o nome da camada de Estacas
            if estacas_layer_name in talude_layer_name:
                matching_layers.append(talude_layer_name)
        return matching_layers

    def create_connections_between_layers(self, estacas_points, talude_points, crs, base_layer_name, line_layer, feature_id_start):
        """
        Cria as linhas do talude preservando a correspondência
        entre os IDs e classificando cada trecho como:

        - CORTE
        - ATERRO
        - NEUTRO
        - TRANSICAO
        """
        if (not estacas_points
            or not talude_points):
            self.mostrar_mensagem(self.tr("Não há pontos suficientes em {estacas_layer_name} ou {talude_layer_name} para criar conexões para '{base_layer_name}'.").format(estacas_layer_name=self.tr("Estacas"), talude_layer_name=self.tr("Talude"), base_layer_name=base_layer_name), "Erro")
            return feature_id_start

        def _id_ordenacao(item):
            try:
                return int(item[0]["ID"])

            except Exception:
                return int(item[0].id())

        def _classe_estaca(feature):
            """
            Classifica usando o Desnível original da estaca.
            """
            try:
                if "Desnível" not in feature.fields().names():
                    return "NEUTRO"

                desnivel = float(feature["Desnível"])

            except (TypeError, ValueError):
                return "NEUTRO"

            tolerancia = 1e-9

            if desnivel > tolerancia:
                return "ATERRO"

            if desnivel < -tolerancia:
                return "CORTE"

            return "NEUTRO"

        def _classe_trecho(classe_1, classe_2):
            if classe_1 == classe_2:
                return classe_1

            return "TRANSICAO"

        def _ponto_no_crs_destino(geom, source_crs):
            g = QgsGeometry(geom)

            if source_crs != crs:
                try:
                    transform = QgsCoordinateTransform(source_crs, crs, QgsProject.instance())

                    g.transform(transform)

                except Exception as e:
                    self.mostrar_mensagem(self.tr("Não foi possível reprojetar uma conexão de {source_crs} para {target_crs}: {error}").format(source_crs=source_crs.authid(), target_crs=crs.authid(), error=str(e)), "Erro")
                    return None

            if (not g
                or g.isEmpty()
                or g.type() != Qgis.GeometryType.Point):
                return None

            return QgsPointXY(g.asPoint())

        estacas_sorted = sorted(estacas_points, key=_id_ordenacao)
        taludes_sorted = sorted(talude_points, key=_id_ordenacao)

        min_length = min(len(estacas_sorted), len(taludes_sorted))

        if min_length == 0:
            return feature_id_start

        estacas_coords = []
        taludes_coords = []
        classes = []

        for i in range(min_length):
            estaca_feature, estaca_geom, estaca_crs = (estacas_sorted[i])

            talude_feature, talude_geom, talude_crs = (taludes_sorted[i])

            estaca_pt = _ponto_no_crs_destino(estaca_geom, estaca_crs)

            talude_pt = _ponto_no_crs_destino(talude_geom, talude_crs)

            if (estaca_pt is None
                or talude_pt is None):
                self.mostrar_mensagem(self.tr("Não foi possível criar as conexões porque uma das geometrias é inválida."), "Erro")
                return feature_id_start

            estacas_coords.append(estaca_pt)
            taludes_coords.append(talude_pt)

            classes.append( _classe_estaca(estaca_feature))

        feature_id = feature_id_start
        line_features = []

        # 1. Linhas Estaca → Talude
        for i in range(min_length):
            feature = QgsFeature(line_layer.fields())

            feature.setGeometry(
                QgsGeometry.fromPolylineXY([
                    estacas_coords[i],
                    taludes_coords[i] ]))

            feature.setAttributes([feature_id, "Ligação", base_layer_name, classes[i]])

            line_features.append(feature)

            feature_id += 1

        # 2. Contornos segmentados
        for i in range(min_length - 1):
            classe_trecho = _classe_trecho(classes[i], classes[i + 1])

            # Borda da estaca
            feature_estaca = QgsFeature(line_layer.fields())

            feature_estaca.setGeometry(
                QgsGeometry.fromPolylineXY([
                    estacas_coords[i],
                    estacas_coords[i + 1]]))

            feature_estaca.setAttributes([
                feature_id,
                "Contorno",
                base_layer_name,
                classe_trecho])

            line_features.append(feature_estaca)

            feature_id += 1

            # Borda externa do talude
            feature_talude = QgsFeature(line_layer.fields())

            feature_talude.setGeometry(
                QgsGeometry.fromPolylineXY([
                    taludes_coords[i],
                    taludes_coords[i + 1]]))

            feature_talude.setAttributes([feature_id, "Contorno", base_layer_name, classe_trecho])

            line_features.append(feature_talude)

            feature_id += 1

            # Hachuras
            h_feats, feature_id = (
                self._create_alignment_hatches(
                    estacas_coords[i],
                    estacas_coords[i + 1],
                    taludes_coords[i],
                    line_layer.fields(),
                    base_layer_name,
                    classe_trecho,
                    feature_id))

            line_features.extend(h_feats)

        line_layer.dataProvider().addFeatures(line_features)

        return feature_id

    def _create_alignment_hatches(self, p_est: QgsPointXY, p_next_est: QgsPointXY, p_tal: QgsPointXY, layer_fields, nome, classe, first_id: int) -> tuple:
        """
        Cria 3 hatchs no alinhamento Estaca-Estaca.

        Regras:
        * bases em 1/4, 1/2 e 3/4 do alinhamento;
        * o hatch fica perpendicular ao alinhamento local;
        * o lado é escolhido para apontar para dentro do talude;
        * em segmentos quase horizontais/verticais, a direção é
          travada exatamente em vertical/horizontal.
        """
        align_len = p_est.distance(p_next_est)

        if align_len <= 0:
            return [], first_id

        # Vetor unitário do alinhamento estaca -> próxima estaca
        ax = (p_next_est.x() - p_est.x()) / align_len
        ay = (p_next_est.y() - p_est.y()) / align_len

        # Vetor estaca -> talude
        tx = p_tal.x() - p_est.x()
        ty = p_tal.y() - p_est.y()

        # Normais possíveis ao alinhamento
        n1x, n1y = -ay, ax
        n2x, n2y = ay, -ax

        # Escolhe a normal que aponta para o lado do talude
        dot1 = (tx * n1x) + (ty * n1y)
        dot2 = (tx * n2x) + (ty * n2y)

        if dot1 >= dot2:
            nx, ny = n1x, n1y
        else:
            nx, ny = n2x, n2y

        # Travamento em eixo para evitar hatch inclinado
        # quando o alinhamento é praticamente horizontal
        # ou vertical.
        eixo_tol = 0.85

        if abs(ax) >= eixo_tol:
            # alinhamento quase horizontal -> hatch vertical
            hx = 0.0
            hy = 1.0 if ny >= 0 else -1.0

        elif abs(ay) >= eixo_tol:
            # alinhamento quase vertical -> hatch horizontal
            hx = 1.0 if nx >= 0 else -1.0
            hy = 0.0

        else:
            # alinhamento diagonal -> usa perpendicular real
            h_norm = math.hypot(nx, ny)

            if h_norm <= 0:
                return [], first_id

            hx = nx / h_norm
            hy = ny / h_norm

        # Distância útil do hatch = projeção do vetor estaca->talude
        # sobre a direção do hatch
        hatch_len = abs((tx * hx) + (ty * hy))

        if hatch_len <= 1e-9:
            hatch_len = p_est.distance(p_tal)

        if hatch_len <= 0:
            return [], first_id

        pos_fractions = (0.25, 0.50, 0.75)
        size_fractions = (0.40, 0.60, 0.40)

        feats = []
        fid = first_id

        for t, s in zip(pos_fractions, size_fractions):
            # ponto base ao longo do alinhamento
            bx = p_est.x() + ax * align_len * t
            by = p_est.y() + ay * align_len * t
            base_pt = QgsPointXY(bx, by)

            # ponto final do hatch
            end_pt = QgsPointXY(
                bx + hx * hatch_len * s,
                by + hy * hatch_len * s)

            f = QgsFeature(layer_fields)
            f.setGeometry(QgsGeometry.fromPolylineXY([base_pt, end_pt]))
            f.setAttributes([fid, "Hatch", nome, classe])
            feats.append(f)
            fid += 1

        return feats, fid

    def aplicar_simbologia_linhas_talude(self, layer):
        """
        Diferencia visualmente as linhas de talude.

        CORTE      = vermelho
        ATERRO     = azul
        NEUTRO     = cinza
        TRANSICAO  = amarelo
        """
        root = QgsRuleBasedRenderer.Rule(None)

        configuracoes = [
            ("CORTE",
                "#CC0000",
                self.tr("Corte")),
            ("ATERRO",
                "#0066CC",
                self.tr("Aterro")),
            ("NEUTRO",
                "#666666",
                self.tr("Sem alteração")),
            ("TRANSICAO",
                "#E6A700",
                self.tr("Transição Corte/Aterro"))]

        for classe, cor, rotulo in configuracoes:
            symbol = QgsLineSymbol.createSimple({"color": cor, "width": "0.35"})

            rule = QgsRuleBasedRenderer.Rule(symbol)
            rule.setFilterExpression(f'"Classe" = \'{classe}\'')
            rule.setLabel(rotulo)
            root.appendChild(rule)

        layer.setRenderer(QgsRuleBasedRenderer(root))
        layer.triggerRepaint()

    def process_matching_layers(self, estacas_layer, talude_layers, crs, line_layer, pr_line, feature_id):
        """Processa as camadas de Estacas e Talude correspondentes e cria as conexões."""
        estacas_points = []
        # Coletar os pontos da camada de Estacas
        for feature in estacas_layer.getFeatures():
            geom = feature.geometry()
            if geom is None or geom.isEmpty():
                continue
            if geom.type() != Qgis.GeometryType.Point:
                self.mostrar_mensagem(self.tr("A camada '{layer_name}' não é uma camada de pontos.").format(layer_name=estacas_layer.name()), "Erro")
                continue

            estacas_points.append((feature, geom, estacas_layer.crs()))

        # Coletar os pontos das camadas de Talude correspondentes
        talude_points = []
        for talude_layer in talude_layers:
            for feature in talude_layer.getFeatures():
                geom = feature.geometry()
                if geom is None or geom.isEmpty():
                    continue
                if geom.type() != Qgis.GeometryType.Point:
                    self.mostrar_mensagem(self.tr("A camada '{layer_name}' não é uma camada de pontos.").format(layer_name=talude_layer.name()), "Erro")
                    continue

                talude_points.append((feature, geom, talude_layer.crs()))

        # Criar as conexões e adicionar as feições à camada de linhas
        feature_id = self.create_connections_between_layers(estacas_points, talude_points, crs, estacas_layer.name(), line_layer, pr_line, feature_id)

        return feature_id

    def check_layers_in_group_and_update(self, removed_layers_ids):
        """
        Verifica e atualiza a interface e os grupos de camadas após remoções,
        garantindo consistência visual e funcional no projeto.
        """
        # Obter o nome da camada de polígono selecionada
        selected_polygon_id = self.comboBoxPoligono.currentData()
        selected_layer = QgsProject.instance().mapLayer(selected_polygon_id)

        if not selected_layer:
            # self.mostrar_mensagem("Camada de polígono não encontrada.", "Erro")
            self.clear_all_list_widgets()
            return

        # Verifica os grupos e atualiza os listWidgets
        self.check_group_and_update(self.tr("Segmentos"), self.listWidgetSegmentos, removed_layers_ids)
        self.check_group_and_update(self.tr("Estaqueamentos"), self.listWidgetEstacas, removed_layers_ids)
        self.check_group_and_update(self.tr("Taludes"), self.listWidgetTalude, removed_layers_ids)

    def check_group_and_update(self, group_name, list_widget, removed_layers_ids):
        """
        Verifica e atualiza a interface e os grupos de camadas após remoções,
        garantindo consistência visual e funcional no projeto.
        """
        root = QgsProject.instance().layerTreeRoot()
        group = root.findGroup(group_name)

        if not group:
            list_widget.clear()
            self._ensure_header(list_widget, group_name.capitalize())
            return

    def clear_all_list_widgets(self):
        """
        Limpa todos os listWidgets da interface, removendo itens exibidos nas listas.
        """
        self.listWidgetSegmentos.clear()
        self.listWidgetEstacas.clear()
        self.listWidgetTalude.clear()

        self._ensure_header(self.listWidgetSegmentos, self.tr("Segmentos"))
        self._ensure_header(self.listWidgetEstacas, self.tr("Estaqueamentos"))
        self._ensure_header(self.listWidgetTalude, self.tr("Taludes"))

    def update_list_widget_talude(self):
        """
        Atualiza o listWidget de taludes, exibindo as camadas relacionadas disponíveis no projeto.
        """
        self.update_list_widget(self.listWidgetTalude, self.tr("Taludes"), self.tr("Taludes"))

        # Chama a função para atualizar o estado do pushButtonJuntar
        self.update_pushButtonJuntar_state()

    def update_list_widget_estaqueamentos(self):
        """
        Atualiza o listWidget de estaqueamentos, listando as camadas criadas e disponíveis no projeto.
        """
        self.update_list_widget(self.listWidgetEstacas, self.tr("Estaqueamentos"), self.tr("Estaqueamentos"))

        # Chama a função para atualizar o estado dos botões de rádio
        self.update_radio_buttons_state()

        # Chama a função para atualizar o estado do pushButtonJuntar
        self.update_pushButtonJuntar_state()

    def update_list_widget_segmentos(self):
        """
        Atualiza o listWidget de segmentos, listando as camadas de segmentos presentes no projeto.
        """
        # Sempre cria o cabeçalho – mesmo que não haja polígono/layer selecionado
        self.update_list_widget(self.listWidgetSegmentos, self.tr("Segmentos"), self.tr("Segmentos"))

    def _ensure_header(self, list_widget: QListWidget, header_text: str):
        """
        Garante que o list_widget tenha um cabeçalho não-selecionável com o texto dado.
        Se já existir, não cria outro.
        """
        if list_widget.count() and list_widget.item(0).flags() == Qt.ItemFlag.NoItemFlags:
            # já há um cabeçalho
            return

        header_lbl = QLabel(header_text)
        header_lbl.setAlignment(Qt.AlignmentFlag.AlignCenter)
        font = QFont("Arial", 8)
        font.setWeight(QFont.Weight.Bold)
        header_lbl.setFont(font)
        header_lbl.setStyleSheet("""
            QLabel {
                background-color: #C0C0C0;
                color: #000000;
                padding: 1px;
                border: 1px solid #A0A0A0;
                border-left-color: #E0E0E0;
                border-top-color:  #E0E0E0;
                border-right-color:#808080;
                border-bottom-color:#808080;
            }
        """)

        header_item = QListWidgetItem(list_widget)
        header_item.setFlags(Qt.ItemFlag.NoItemFlags)            # não selecionável
        list_widget.addItem(header_item)
        list_widget.setItemWidget(header_item, header_lbl)
        header_item.setSizeHint(header_lbl.sizeHint())

    def update_list_widget(self, list_widget, group_name, header_text):
        """
        Atualiza o listWidget informado com as camadas pertencentes ao grupo especificado,
        exibindo um cabeçalho personalizado conforme o parâmetro.
        """
        # Zera o conteúdo
        list_widget.clear()

        # Sempre garante o cabeçalho
        self._ensure_header(list_widget, header_text)

        # Agora verifica (ou não) se há um grupo no projeto
        root  = QgsProject.instance().layerTreeRoot()
        group = root.findGroup(group_name)
        if not group:
            return     # cabeçalho permanece mesmo que o grupo não exista

        # Obtém somente as camadas de pontos do grupo
        layers = []

        for layer in group.findLayers():
            layer_obj = layer.layer()

            if (isinstance(layer_obj, QgsVectorLayer)
                and layer_obj.geometryType() == Qgis.GeometryType.Point):
                layers.append(layer_obj)

        # Ordenação natural:
        # 1_2, 2_3, 3_4, ..., 38_39, 39_1
        def natural_key(layer_obj):
            partes = re.split(r'(\d+)', layer_obj.name())

            return [(0, int(parte)) if parte.isdigit()
                else (1, parte.casefold())
                for parte in partes]

        layers.sort(key=natural_key)

        # Adiciona as camadas já ordenadas
        for layer_obj in layers:
            item = QListWidgetItem(layer_obj.name())
            item.setData(Qt.ItemDataRole.UserRole, layer_obj.id())
            item.setToolTip(layer_obj.name())
            list_widget.addItem(item)

        # Se estivermos atualizando o listWidgetSegmentos e houver uma seleção "guardada", define a nova seleção
        if list_widget == self.listWidgetSegmentos and hasattr(self, "_next_segment_index") and self._next_segment_index is not None:
            total = list_widget.count()
            # Se houver mais itens do que o índice desejado, seleciona-o (caso contrário, limpa a seleção)
            if self._next_segment_index < total:
                list_widget.setCurrentRow(self._next_segment_index)
                # self._log_message(f"Seleção movida para o item {self._next_segment_index}.", Qgis.Info)
            else:
                list_widget.setCurrentRow(-1)
                # self._log_message("Não há próximo item: seleção removida.", Qgis.Info)
            self._next_segment_index = None

        elif list_widget == self.listWidgetEstacas and hasattr(self, "_next_estaca_index") and self._next_estaca_index is not None:
            total = list_widget.count()
            if self._next_estaca_index < total:
                list_widget.setCurrentRow(self._next_estaca_index)
                # self._log_message(f"Seleção movida para o item {self._next_estaca_index} em Estaqueamentos.", Qgis.Info)
            else:
                list_widget.setCurrentRow(-1)
                # self._log_message("Não há próximo item em Estaqueamentos: seleção removida.", Qgis.Info)
            self._next_estaca_index = None

    def enquadrar_camada_lista(self, current_item, previous_item=None):
        """
        Enquadra a camada no QGIS, priorizando a área livre
        à esquerda do diálogo quando houver sobreposição.
        """
        if current_item is None:
            return

        layer_id = current_item.data(Qt.ItemDataRole.UserRole)

        if not layer_id:
            return

        layer = QgsProject.instance().mapLayer(layer_id)

        if not isinstance(layer, QgsVectorLayer) or not layer.isValid():
            return

        extent = QgsRectangle(layer.extent())

        if extent.isNull():
            return

        canvas = self.iface.mapCanvas()
        project_crs = canvas.mapSettings().destinationCrs()

        if layer.crs() != project_crs:
            try:
                transform = QgsCoordinateTransform(layer.crs(), project_crs, QgsProject.instance())
                extent = transform.transformBoundingBox(extent)
            except Exception:
                return

        # Margem de enquadramento.
        maior_dimensao = max(extent.width(), extent.height())

        if maior_dimensao > 0:
            extent.grow(maior_dimensao * 0.15)

        # Enquadra inicialmente no canvas.
        canvas.setExtent(extent)

        # Obtém a posição do diálogo em relação ao canvas.
        if self.isVisible():
            largura_canvas = canvas.width()

            if largura_canvas > 0:
                dialogo = self.frameGeometry()

                # Converte a posição global para coordenadas do canvas.
                posicao = canvas.mapFromGlobal(QPoint(dialogo.left(), dialogo.top()))

                x_dialogo = posicao.x()

                # Verifica se o diálogo realmente ocupa a parte direita.
                if 0 < x_dialogo < largura_canvas:

                    # Centro da região livre à esquerda.
                    centro_livre = x_dialogo / 2.0

                    # Evita enquadramento excessivamente próximo da borda.
                    centro_livre = max(largura_canvas * 0.15, min(centro_livre, largura_canvas * 0.45))

                    # Converte o deslocamento visual para unidades do mapa.
                    extent_atual = canvas.extent()

                    deslocamento = ((largura_canvas / 2.0 - centro_livre) * extent_atual.width() / largura_canvas)

                    # Desloca o centro do mapa para a direita,
                    # fazendo a camada aparecer mais à esquerda.
                    extent_atual.setXMinimum(extent_atual.xMinimum() + deslocamento)
                    extent_atual.setXMaximum(extent_atual.xMaximum() + deslocamento)

                    canvas.setExtent(extent_atual)

        canvas.refresh()

    def _selecionar_proximo_item(self, list_widget, linha_anterior):
        """
        Seleciona o próximo item da lista.

        Ao concluir o último item, remove a seleção em vez
        de retornar ao primeiro.
        """
        total = list_widget.count()
        primeira_linha = 1  # A linha 0 contém o cabeçalho.

        if total <= primeira_linha:
            list_widget.clearSelection()
            list_widget.setCurrentRow(-1)
            return

        proxima_linha = linha_anterior + 1

        if proxima_linha < total:
            list_widget.setCurrentRow(proxima_linha)
            list_widget.scrollToItem(list_widget.item(proxima_linha))
        else:
            # Última camada concluída: encerra a sequência.
            list_widget.clearSelection()
            list_widget.setCurrentRow(-1)

    def check_estaqueamento_button_state(self):
        """Verifica se o botão Estaqueamento deve ser ativado."""
        # Verifica se há um item selecionado no listWidgetSegmentos e se o valor do doubleSpinBoxEquidistante é maior que 0
        has_selection = self.listWidgetSegmentos.selectedItems()
        equidistance_value = self.doubleSpinBoxEquidistante.value()

        if has_selection and equidistance_value > 0:
            self.pushButtonEstaqueamento.setEnabled(True)
        else:
            self.pushButtonEstaqueamento.setEnabled(False)

    def update_doubleSpinBoxEquidistante_state(self):
        """
        Ativa ou desativa o doubleSpinBoxEquidistante com base na seleção no listWidgetSegmentos
        e ajusta o valor máximo do doubleSpinBoxEquidistante para ser o comprimento da linha selecionada.
        """
        # Verificar se há itens no listWidgetSegmentos
        if self.listWidgetSegmentos.count() == 0:
            self.doubleSpinBoxEquidistante.setEnabled(False)  # Desativa o doubleSpinBoxEquidistante se não houver itens
            self.doubleSpinBoxEquidistante.setToolTip(self.tr("Nenhuma camada de segmento disponível."))
            return

        selected_item = self.listWidgetSegmentos.currentItem()

        # Verificar se há uma camada selecionada no listWidgetSegmentos
        if not selected_item:
            self.doubleSpinBoxEquidistante.setEnabled(False)  # Desativa o doubleSpinBoxEquidistante se não houver seleção
            self.doubleSpinBoxEquidistante.setToolTip(self.tr("Selecione uma camada de segmento primeiro."))
            return

        # Obter a camada de pontos a partir do nome da camada
        layer_name = selected_item.text()
        layer = QgsProject.instance().mapLayersByName(layer_name)
        if not layer:
            self.mostrar_mensagem(self.tr("Camada '{layer_name}' não encontrada.").format(layer_name=layer_name), "Erro")
            return
        layer = layer[0]

        # Verificar se a camada possui exatamente dois pontos
        points = [f for f in layer.getFeatures()]
        if len(points) != 2:
            self.mostrar_mensagem(self.tr("A camada selecionada deve conter exatamente dois pontos."), "Erro")
            return

        # Calcular a distância entre os dois pontos
        point1 = points[0].geometry().asPoint()
        point2 = points[1].geometry().asPoint()
        total_distance = point1.distance(point2)

        # Ativar o doubleSpinBoxEquidistante e definir o valor máximo
        self.doubleSpinBoxEquidistante.setEnabled(True)
        self.doubleSpinBoxEquidistante.setMaximum(total_distance)
        self.doubleSpinBoxEquidistante.setToolTip(self.tr("Distância total: {total_distance:.2f} m. Selecione uma equidistância menor ou igual.").format(total_distance=total_distance))

        # Atualizar o valor do toolTip para mostrar a quantidade de pontos que será criada
        self.calculate_and_update_tooltip()

    def calculate_and_update_tooltip(self):
        """
        Calcula a quantidade de pontos que será criada com base no valor da equidistância
        e na linha selecionada no listWidgetSegmentos, e atualiza o toolTip.
        """
        selected_item = self.listWidgetSegmentos.currentItem()

        # Verificar se há uma camada selecionada no listWidgetSegmentos
        if not selected_item:
            self.doubleSpinBoxEquidistante.setToolTip(self.tr("Nenhuma camada de segmento selecionada."))  # Atualizar o toolTip
            return

        # Obter a camada de pontos a partir do nome da camada
        layer_name = selected_item.text()
        layer = QgsProject.instance().mapLayersByName(layer_name)
        if not layer:
            self.mostrar_mensagem(self.tr("Camada '{layer_name}' não encontrada.").format(layer_name=layer_name), "Erro")
            return
        layer = layer[0]

        # Verificar se a camada possui exatamente dois pontos
        points = [f for f in layer.getFeatures()]
        if len(points) != 2:
            self.mostrar_mensagem(self.tr("A camada selecionada deve conter exatamente dois pontos."), "Erro")
            return

        # Calcular a distância entre os dois pontos
        point1 = points[0].geometry().asPoint()
        point2 = points[1].geometry().asPoint()
        total_distance = point1.distance(point2)

        # Obter o valor de equidistância
        equidistance = self.doubleSpinBoxEquidistante.value()

        # Verificar se o valor da equidistância é válido
        if equidistance > 0 and total_distance > 0:
            # Calcular a quantidade de pontos
            num_points = int(total_distance // equidistance)
            tooltip_text = self.tr("Distância total: {total_distance:.2f} m | Pontos a criar: {num_points}").format(total_distance=total_distance, num_points=num_points)
        else:
            tooltip_text = self.tr("Equidistância inválida ou distância zero.")

        # Atualizar o toolTip do doubleSpinBox
        self.doubleSpinBoxEquidistante.setToolTip(tooltip_text)

    def update_pushButtonTalude_state(self):
        """
        Ativa ou desativa o pushButtonTalude com base na seleção no listWidgetEstacas.
        """
        selected_item = self.listWidgetEstacas.currentItem()

        # Verificar se há uma camada selecionada no listWidgetEstacas
        if not selected_item:
            self.pushButtonTalude.setEnabled(False)  # Desativa o botão se nenhuma camada estiver selecionada
            return

        # Se houver uma camada selecionada, ativa o botão
        self.pushButtonTalude.setEnabled(True)

    def update_pushButtonVertices_state(self):
        """
        Ativa ou desativa o pushButtonVertices com base nas seguintes condições:
        - Caso não haja camada de polígono no comboBoxPoligono.
        - Caso não haja camada no comboBoxRaster.
        - Caso as camadas de polígono e raster tenham georreferências diferentes.
        - Caso alguma das camadas esteja em coordenadas geográficas.
        - Se a camada de polígono tenha mais de uma feição e não haja uma única selecionada.
        - Se alguma das camadas não tiver projeção.
        """
        selected_polygon_index = self.comboBoxPoligono.currentIndex()
        selected_raster_index = self.comboBoxRaster.currentIndex()

        # Verifica se há uma camada de polígono e raster selecionada
        if selected_polygon_index == -1 or selected_raster_index == -1:
            self.pushButtonVertices.setEnabled(False)
            return

        # Obtém a camada de polígono e raster selecionada
        selected_polygon_id = self.comboBoxPoligono.currentData()
        selected_raster_id = self.comboBoxRaster.currentData()
        polygon_layer = QgsProject.instance().mapLayer(selected_polygon_id)
        raster_layer = QgsProject.instance().mapLayer(selected_raster_id)

        # Verifica se ambas as camadas são válidas
        if not polygon_layer or not raster_layer:
            self.pushButtonVertices.setEnabled(False)
            return

        # Verifica se as camadas têm projeção
        if not polygon_layer.crs().isValid() or not raster_layer.crs().isValid():
            if self.isVisible():
                self.mostrar_mensagem(self.tr("Uma ou ambas as camadas não têm projeção definida."), "Aviso")
            self.pushButtonVertices.setEnabled(False)
            return

        # Verifica se as camadas têm sistemas de coordenadas diferentes
        if polygon_layer.crs() != raster_layer.crs():
            if self.isVisible() and selected_polygon_index != -1 and selected_raster_index != -1:
                self.mostrar_mensagem(self.tr("As camadas de polígono e raster têm georreferências diferentes."), "Aviso")
            self.pushButtonVertices.setEnabled(False)
            return

        # Verifica se alguma das camadas está em coordenadas geográficas (ex.: EPSG:4326)
        if polygon_layer.crs().isGeographic() or raster_layer.crs().isGeographic():
            if self.isVisible():
                self.mostrar_mensagem(self.tr("Uma ou ambas as camadas estão em coordenadas geográficas."), "Aviso")
            self.pushButtonVertices.setEnabled(False)
            return

        # Verifica se a camada de polígono tem mais de uma feição e se não há uma única selecionada
        if polygon_layer.featureCount() > 1 and polygon_layer.selectedFeatureCount() != 1:
            if self.isVisible():
                self.mostrar_mensagem(self.tr("A camada de polígono tem mais de uma feição e nenhuma feição única está selecionada."), "Aviso")
            self.pushButtonVertices.setEnabled(False)
            return

        # Se todas as condições forem atendidas, ativa o botão
        self.pushButtonVertices.setEnabled(True)

    def on_pushButtonGrafico_clicked(self):
        """Método para ser chamado quando o botão de gráfico for clicado."""
        # Obter a camada selecionada no listWidgetEstacas
        selected_item = self.listWidgetEstacas.currentItem()
        if not selected_item:
            self.mostrar_mensagem(self.tr("Nenhuma camada de estacas selecionada."), "Erro")
            return

        estacas_layer_name = selected_item.text()
        estacas_layer = self.grafico_manager.find_layer(estacas_layer_name, QgsVectorLayer)
        if not estacas_layer:
            self.mostrar_mensagem(self.tr("Camada de estacas '{estacas_layer_name}' não encontrada.").format(estacas_layer_name=estacas_layer_name), "Erro")
            return

        # Obter a camada raster selecionada
        raster_layer_id = self.comboBoxRaster.currentData()
        raster_layer = QgsProject.instance().mapLayer(raster_layer_id)
        if not raster_layer:
            self.mostrar_mensagem(self.tr("Camada raster não encontrada."), "Erro")
            return

        # Criar a camada de pontos de apoio temporariamente para uso no gráfico
        pontos_apoio_layer = self.grafico_manager.create_support_points_layer(estacas_layer, raster_layer)

        # Passar o caminho do logotipo para o GraficoManager
        self.grafico_manager.logo_path = self.logo_path

        # Gerar o gráfico com base nas camadas de estacas e pontos de apoio (sem adicionar ao projeto)
        self.grafico_manager.plot_layers(estacas_layer, pontos_apoio_layer, 45, 45)

    def _intersecao_retas_talude(self, p1, p2, p3, p4):
        """
        Calcula a interseção das retas infinitas
        p1-p2 e p3-p4.

        Retorna QgsPointXY ou None quando forem
        paralelas ou praticamente paralelas.
        """
        x1 = p1.x()
        y1 = p1.y()
        x2 = p2.x()
        y2 = p2.y()

        x3 = p3.x()
        y3 = p3.y()
        x4 = p4.x()
        y4 = p4.y()

        denominador = ((x1 - x2) * (y3 - y4) - (y1 - y2) * (x3 - x4))

        if abs(denominador) < 1e-12:
            return None

        det1 = (x1 * y2 - y1 * x2)
        det2 = (x3 * y4 - y3 * x4)

        x = (det1 * (x3 - x4) - (x1 - x2) * det2) / denominador
        y = (det1 * (y3 - y4) - (y1 - y2) * det2) / denominador

        return QgsPointXY(x, y)

    def _ponto_talude_no_crs( self, geom, source_crs, target_crs):
        """
        Retorna o ponto transformado para o SRC de destino.
        """
        if (geom is None
            or geom.isEmpty()):
            return None

        g = QgsGeometry(geom)

        if source_crs != target_crs:
            try:
                transform = QgsCoordinateTransform(source_crs, target_crs, QgsProject.instance())

                g.transform(transform)

            except Exception:
                return None

        if g.type() != Qgis.GeometryType.Point:
            return None

        return QgsPointXY(g.asPoint())

    def _corrigir_cantos_compartilhados_talude(self, faixas, crs):
        """
        Corrige encontros entre faixas consecutivas de talude.

        Para cada canto compartilhado:
        - identifica extremidades próximas;
        - unifica o ponto da estaca;
        - calcula a interseção das bordas externas;
        - unifica o ponto externo do talude;
        - caso a interseção não seja confiável,
          usa a média dos dois pontos externos.

        Isso elimina os pequenos triângulos nos cantos.
        """

        def _ordenar_por_id(item):
            feature = item[0]

            try:
                return int(feature["ID"])

            except Exception:
                return int(feature.id())

        registros = []

        # 1. Coleta início e fim de cada faixa
        for faixa_idx, faixa in enumerate(faixas):

            estacas = sorted(faixa["estacas"], key=_ordenar_por_id)
            taludes = sorted(faixa["taludes"], key=_ordenar_por_id)

            faixa["estacas"] = estacas
            faixa["taludes"] = taludes

            n = min(len(estacas), len(taludes))

            if n < 2:
                continue

            for idx in (0, n - 1):
                idx_vizinho = (1
                    if idx == 0
                    else n - 2)

                estaca_pt = self._ponto_talude_no_crs(estacas[idx][1], estacas[idx][2], crs)

                estaca_vizinha = self._ponto_talude_no_crs(
                    estacas[idx_vizinho][1],
                    estacas[idx_vizinho][2],
                    crs)

                talude_pt = self._ponto_talude_no_crs(
                    taludes[idx][1],
                    taludes[idx][2],
                    crs)

                talude_vizinho = self._ponto_talude_no_crs(
                    taludes[idx_vizinho][1],
                    taludes[idx_vizinho][2],
                    crs)

                if (estaca_pt is None
                    or estaca_vizinha is None
                    or talude_pt is None
                    or talude_vizinho is None):
                    continue

                comprimento_local = estaca_pt.distance(estaca_vizinha)

                registros.append({
                    "faixa_idx": faixa_idx,
                    "idx": idx,
                    "estaca": estaca_pt,
                    "estaca_vizinha": estaca_vizinha,
                    "talude": talude_pt,
                    "talude_vizinho": talude_vizinho,
                    "comprimento_local": comprimento_local})

        # 2. Agrupa extremidades próximas
        # Não usamos mais round(x, 3), porque diferenças pequenas entre duas camadas impediam o encontro.
        grupos = []

        for registro in registros:

            grupo_encontrado = None

            for grupo in grupos:

                # Não pode ser outro extremo da mesma faixa
                if all(outro["faixa_idx"] == registro["faixa_idx"]
                    for outro in grupo):
                    continue

                referencia = min(registro["comprimento_local"], min(outro["comprimento_local"]
                        for outro in grupo))

                # Tolerância adaptativa.
                # Mínimo de 5 cm e máximo de 1 m.
                tolerancia = max(0.05, min(1.0, referencia * 0.10))

                if any(registro["estaca"].distance(outro["estaca"])
                    <= tolerancia
                    for outro in grupo):
                    grupo_encontrado = grupo
                    break

            if grupo_encontrado is None:
                grupos.append([registro])

            else:
                grupo_encontrado.append(registro)

        # 3. Corrige cada canto compartilhado
        for grupo in grupos:

            faixas_distintas = {registro["faixa_idx"]
                for registro in grupo}

            if len(faixas_distintas) < 2:
                continue

            # PONTO INTERNO COMUM
            # Usa a média das estacas praticamente coincidentes para remover qualquer diferença milimétrica entre as duas camadas.
            estaca_x = sum(registro["estaca"].x()
                for registro in grupo) / len(grupo)

            estaca_y = sum(registro["estaca"].y()
                for registro in grupo) / len(grupo)

            estaca_comum = QgsPointXY(estaca_x, estaca_y)

            # PONTO EXTERNO COMUM
            candidatos = []

            for i in range(len(grupo)):

                for j in range(i + 1, len(grupo)):
                    r1 = grupo[i]
                    r2 = grupo[j]

                    if (r1["faixa_idx"] == r2["faixa_idx"]):
                        continue

                    intersecao = (
                        self._intersecao_retas_talude(
                            r1["talude_vizinho"],
                            r1["talude"],
                            r2["talude_vizinho"],
                            r2["talude"]))

                    if intersecao is None:
                        continue

                    distancia_1 = intersecao.distance(r1["talude"])

                    distancia_2 = intersecao.distance(r2["talude"])

                    escala = max(
                        r1["talude"].distance(
                            r1["talude_vizinho"]),
                        r2["talude"].distance(
                            r2["talude_vizinho"]),
                        r1["estaca"].distance(
                            r1["talude"]),
                        r2["estaca"].distance(
                            r2["talude"]), 0.001)

                    # Evita um miter exageradamente distante
                    if (distancia_1 <= escala * 3.0
                        and
                        distancia_2 <= escala * 3.0):
                        candidatos.append((distancia_1 + distancia_2, intersecao))

            if candidatos:
                candidatos.sort(key=lambda item: item[0])

                talude_comum = candidatos[0][1]

            else:
                # Fallback importantíssimo:
                # mesmo sem uma interseção confiável,
                # NÃO deixa dois pontos externos diferentes.
                talude_x = sum(registro["talude"].x()
                    for registro in grupo) / len(grupo)

                talude_y = sum(registro["talude"].y()
                    for registro in grupo) / len(grupo)

                talude_comum = QgsPointXY(talude_x, talude_y)

            # 4. Substitui efetivamente os dois extremos
            for registro in grupo:

                faixa = faixas[registro["faixa_idx"]]

                idx = registro["idx"]

                # Estaca compartilhada
                feature_estaca = (faixa["estacas"][idx][0])

                faixa["estacas"][idx] = (feature_estaca, QgsGeometry.fromPointXY(estaca_comum), crs)

                # Talude compartilhado
                feature_talude = (faixa["taludes"][idx][0])

                faixa["taludes"][idx] = (feature_talude, QgsGeometry.fromPointXY(talude_comum), crs)

    def _ids_disponiveis_para_juntar(self, polygon_layer):
        """Retorna os IDs do polígono que possuem Estaqueamento disponível."""
        if not isinstance(polygon_layer, QgsVectorLayer) or not polygon_layer.isValid():
            return []

        prefixes_estacas = set()

        for i in range(self.listWidgetEstacas.count()):
            item = self.listWidgetEstacas.item(i)

            if item and item.text():
                prefixes_estacas.add(item.text())

        ids_validos = []

        for feature in polygon_layer.getFeatures():
            if not feature.hasGeometry() or feature.geometry().isEmpty():
                continue

            poly_id = self._get_poly_id_for_naming(polygon_layer, feature)

            if poly_id is None:
                continue

            poly_id = str(poly_id)
            prefixo = f"{polygon_layer.name()}_ID{poly_id}_"

            possui_estacas = any(nome.startswith(prefixo) for nome in prefixes_estacas)

            if possui_estacas:
                ids_validos.append(poly_id)

        return sorted(set(ids_validos), key=self._chave_ordenacao_natural)

    def _selecionar_ids_para_juntar(self, ids_disponiveis, id_ativo=None):
        """Permite escolher os IDs a processar. Se houver somente um, retorna diretamente."""
        if not ids_disponiveis:
            return []

        # Somente um ID: executa diretamente, sem perguntar.
        if len(ids_disponiveis) == 1:
            return list(ids_disponiveis)

        dialog = QDialog(self)
        dialog.setWindowTitle(self.tr("Selecionar Platôs"))
        dialog.setMinimumWidth(350)

        layout = QVBoxLayout(dialog)
        layout.addWidget(QLabel(self.tr("Selecione os IDs que serão processados:")))

        lista = QListWidget(dialog)

        for poly_id in ids_disponiveis:
            item = QListWidgetItem(self.tr("ID {id}").format(id=poly_id))
            item.setData(Qt.ItemDataRole.UserRole, poly_id)
            item.setFlags(item.flags() | Qt.ItemFlag.ItemIsUserCheckable)
            item.setCheckState(Qt.CheckState.Checked)

            if id_ativo is not None and str(poly_id) == str(id_ativo):
                fonte = item.font()
                fonte.setBold(True)
                item.setFont(fonte)
                item.setToolTip(self.tr("ID atualmente ativo"))

            lista.addItem(item)

        layout.addWidget(lista)

        botoes_selecao = QHBoxLayout()
        button_todos = QPushButton(self.tr("Selecionar todos"))
        button_limpar = QPushButton(self.tr("Limpar seleção"))
        botoes_selecao.addWidget(button_todos)
        botoes_selecao.addWidget(button_limpar)
        botoes_selecao.addStretch()
        layout.addLayout(botoes_selecao)

        botoes_final = QHBoxLayout()
        botoes_final.addStretch()
        button_cancelar = QPushButton(self.tr("Cancelar"))
        button_executar = QPushButton(self.tr("Executar"))
        button_executar.setDefault(True)
        botoes_final.addWidget(button_cancelar)
        botoes_final.addWidget(button_executar)
        layout.addLayout(botoes_final)

        def marcar_todos():
            for i in range(lista.count()):
                lista.item(i).setCheckState(Qt.CheckState.Checked)

        def limpar_selecao():
            for i in range(lista.count()):
                lista.item(i).setCheckState(Qt.CheckState.Unchecked)

        button_todos.clicked.connect(marcar_todos)
        button_limpar.clicked.connect(limpar_selecao)
        button_cancelar.clicked.connect(dialog.reject)
        button_executar.clicked.connect(dialog.accept)

        if dialog.exec() != QDialog.DialogCode.Accepted:
            return []

        selecionados = [
            lista.item(i).data(Qt.ItemDataRole.UserRole)
            for i in range(lista.count())
            if lista.item(i).checkState() == Qt.CheckState.Checked]

        if not selecionados:
            self.mostrar_mensagem(self.tr("Selecione pelo menos um ID para processar."), "Aviso")

        return selecionados

    def on_pushButtonJuntar_clicked(self):
        """Seleciona os IDs disponíveis e processa cada Platô separadamente."""
        selected_polygon_id = self.comboBoxPoligono.currentData()
        polygon_layer = QgsProject.instance().mapLayer(selected_polygon_id)

        if not polygon_layer or not isinstance(polygon_layer, QgsVectorLayer):
            self.mostrar_mensagem(self.tr("Selecione uma camada de polígono válida."), "Erro")
            return

        ids_disponiveis = self._ids_disponiveis_para_juntar(polygon_layer)

        if not ids_disponiveis:
            self.mostrar_mensagem(self.tr("Nenhum ID possui Estaqueamento disponível para processar."), "Aviso")
            return

        feature_ativa = self._get_active_polygon_feature(polygon_layer)
        id_ativo = self._get_poly_id_for_naming(polygon_layer, feature_ativa) if feature_ativa else None

        ids_selecionados = self._selecionar_ids_para_juntar(ids_disponiveis, id_ativo)

        if not ids_selecionados:
            return

        # A geração da malha TIN é obrigatória.
        # O checkBoxMDT controla apenas a rasterização.
        crs_inicial = polygon_layer.crs()

        if not crs_inicial.isValid():
            crs_inicial = QgsProject.instance().crs()

        output_crs = self._escolher_crs_malha(crs_inicial)

        if output_crs is None:
            return

        concluidos = []
        falhas = []

        for poly_id in ids_selecionados:
            resultado = self._processar_juncao_id(polygon_layer, poly_id, output_crs)

            if resultado:
                concluidos.append(str(poly_id))
            else:
                falhas.append(str(poly_id))

            QCoreApplication.processEvents()

        self.update_pushButtonSalvar_state()

        if falhas:
            self.mostrar_mensagem(self.tr("Processamento concluído com avisos. IDs processados: {ok}. IDs com falha: {fail}.").format(ok=", ".join(concluidos) if concluidos else "-", fail=", ".join(falhas)), "Aviso")
            return

        if len(concluidos) == 1:
            self.mostrar_mensagem(self.tr("Platô ID {id} processado com sucesso.").format(id=concluidos[0]), "Sucesso")
        else:
            self.mostrar_mensagem(self.tr("{count} platôs processados com sucesso: {ids}.").format(count=len(concluidos), ids=", ".join(concluidos)), "Sucesso")

    def _processar_juncao_id(self, polygon_layer, poly_id, output_crs=None):
        """Une Estaqueamentos e Taludes exclusivamente do polígono/ID informado."""
        unique_coords = set()
        unique_features = []
        crs_from_inputs = None

        estacas_points_global = []
        talude_points_global = []

        poly_id = str(poly_id)
        prefixo_ativo = f"{polygon_layer.name()}_ID{poly_id}_"

        def _safe_attr(feat, name, default=None):
            try:
                if name in feat.fields().names():
                    v = feat[name]
                    return v if v is not None else default
                return default
            except Exception:
                return default

        def process_list_widget(list_widget, cota_field_name, points_list, layer_type):
            nonlocal crs_from_inputs

            for index in range(list_widget.count()):
                item = list_widget.item(index)

                if not item or not item.text():
                    continue

                if not item.text().startswith(prefixo_ativo):
                    continue

                layer_id = item.data(Qt.ItemDataRole.UserRole)
                layer = QgsProject.instance().mapLayer(layer_id) if layer_id else None

                if not layer:
                    layers = QgsProject.instance().mapLayersByName(item.text())
                    layer = layers[0] if layers else None

                if not layer:
                    self.mostrar_mensagem(self.tr("Camada '{layer_name}' não encontrada.").format(layer_name=item.text()), "Erro")
                    continue

                if not isinstance(layer, QgsVectorLayer):
                    continue

                layer_name = layer.name()

                if crs_from_inputs is None:
                    crs_from_inputs = layer.crs()

                for feature in layer.getFeatures():
                    geom = feature.geometry()

                    if not geom or geom.isEmpty():
                        continue

                    if geom.type() != Qgis.GeometryType.Point:
                        self.mostrar_mensagem(self.tr("A camada '{layer_name}' não é de pontos.").format(layer_name=layer_name), "Erro")
                        continue

                    pt = geom.asPoint()
                    coord_tuple = (round(pt.x(), 6), round(pt.y(), 6))

                    if coord_tuple not in unique_coords:
                        unique_coords.add(coord_tuple)

                        src_id_val = _safe_attr(feature, "ID", None)

                        try:
                            id_int = int(src_id_val) if src_id_val is not None and str(src_id_val).strip() != "" else int(feature.id())
                        except Exception:
                            id_int = int(feature.id())

                        at_x = _safe_attr(feature, "X", pt.x())
                        at_y = _safe_attr(feature, "Y", pt.y())
                        cota = _safe_attr(feature, cota_field_name, None)

                        if cota is None:
                            try:
                                cota = pt.z()
                            except Exception:
                                cota = None

                        attributes = {"ID": id_int, "X": at_x, "Y": at_y, "Cota": cota}
                        unique_features.append((attributes, geom, layer.crs()))

                    points_list.append((feature, geom, layer.crs(), layer_name))

        process_list_widget(self.listWidgetEstacas, "NovoZ", estacas_points_global, "Estacas")
        process_list_widget(self.listWidgetTalude, "Z", talude_points_global, "Talude")

        if not estacas_points_global:
            self.mostrar_mensagem(self.tr("Nenhum estaqueamento foi encontrado para o ID {id}.").format(id=poly_id), "Erro")
            return False

        if not unique_features:
            self.mostrar_mensagem(self.tr("Nenhuma feição encontrada para o ID {id}.").format(id=poly_id), "Erro")
            return False

        crs = polygon_layer.crs()

        if not crs.isValid():
            crs = QgsCoordinateReferenceSystem("EPSG:4326")
            self.mostrar_mensagem(self.tr("CRS do polígono inválido. Usando EPSG:4326."), "Aviso")

        crs_auth = crs.authid()

        # CAMADA DE PONTOS
        merged_name = f"{polygon_layer.name()}_ID{poly_id}_{self.tr('Pontos')}"
        merged_points_layer = QgsVectorLayer(f"Point?crs={crs_auth}", merged_name, "memory")
        pr = merged_points_layer.dataProvider()

        fields = [
            QgsField("ID", QMetaType.Type.Int),
            QgsField("X", QMetaType.Type.Double),
            QgsField("Y", QMetaType.Type.Double),
            QgsField("Cota", QMetaType.Type.Double)]

        pr.addAttributes(fields)
        merged_points_layer.updateFields()
        self._aplicar_aliases_campos(merged_points_layer)

        new_features = []

        for attributes, geom, feat_crs in unique_features:
            g = QgsGeometry(geom)

            if feat_crs != crs:
                try:
                    transform = QgsCoordinateTransform(feat_crs, crs, QgsProject.instance())
                    g.transform(transform)
                except Exception as e:
                    self.mostrar_mensagem(
                        self.tr("Não foi possível reprojetar uma feição de {source_crs} para {target_crs}: {error}").format(
                            source_crs=feat_crs.authid(),
                            target_crs=crs.authid(),
                            error=str(e)),
                        "Erro")
                    return False

            if not g or g.isEmpty() or g.type() != Qgis.GeometryType.Point:
                self.mostrar_mensagem(self.tr("Foi encontrada uma geometria de ponto inválida durante a união das camadas."), "Erro")
                return False

            ponto_saida = g.asPoint()
            f = QgsFeature(merged_points_layer.fields())
            f.setGeometry(g)

            id_val = attributes.get("ID")

            try:
                id_val = int(id_val) if id_val is not None else None
            except Exception:
                id_val = None

            f.setAttribute("ID", id_val)
            f.setAttribute("X", round(ponto_saida.x(), 3))
            f.setAttribute("Y", round(ponto_saida.y(), 3))

            cota_val = attributes.get("Cota", None)

            if cota_val is None:
                try:
                    cota_val = g.asPoint().z()
                except Exception:
                    cota_val = None

            try:
                cota_val = float(cota_val) if cota_val is not None else None
            except Exception:
                cota_val = None

            f.setAttribute("Cota", cota_val)
            new_features.append(f)

        pr.addFeatures(new_features)

        for lyr in QgsProject.instance().mapLayersByName(merged_name):
            QgsProject.instance().removeMapLayer(lyr.id())

        self._top_insert_layer(merged_points_layer)

        # MALHA TIN
        malha_ok = True

        # CAMADA DE LINHAS DO TALUDE
        line_layer_name = f"{polygon_layer.name()}_ID{poly_id}_{self.tr('Linhas do Talude')}"

        for lyr in QgsProject.instance().mapLayersByName(line_layer_name):
            QgsProject.instance().removeMapLayer(lyr.id())

        line_layer = QgsVectorLayer(f"LineString?crs={crs_auth}", line_layer_name, "memory")
        lpr = line_layer.dataProvider()

        line_fields = [
            QgsField("ID", QMetaType.Type.Int),
            QgsField("Tipo", QMetaType.Type.QString),
            QgsField("Nome", QMetaType.Type.QString),
            QgsField("Classe", QMetaType.Type.QString)]

        lpr.addAttributes(line_fields)
        line_layer.updateFields()
        self._top_insert_layer(line_layer)

        feature_id = 1

        estacas_layers = {}

        for feature, geom, feature_crs, layer_name in estacas_points_global:
            estacas_layers.setdefault(layer_name, []).append((feature, geom, feature_crs))

        talude_layers = {}

        for feature, geom, feature_crs, layer_name in talude_points_global:
            talude_layers.setdefault(layer_name, []).append((feature, geom, feature_crs))

        faixas = []

        for estacas_layer_name, estacas_points in estacas_layers.items():
            matching_talude_layers = self.find_matching_talude_layers(estacas_layer_name, talude_layers)

            if not matching_talude_layers:
                continue

            for t_name in matching_talude_layers:
                faixas.append({
                    "estacas_name": estacas_layer_name,
                    "talude_name": t_name,
                    "estacas": list(estacas_points),
                    "taludes": list(talude_layers[t_name])})

        self._corrigir_cantos_compartilhados_talude(faixas, crs)

        # Gera a malha TIN independentemente do checkBoxMDT.
        mesh_name = f"{polygon_layer.name()}_ID{poly_id}_TIN"

        malha_ok = self._create_mesh_from_faixas(
            faixas,
            estacas_points_global,
            mesh_name,
            crs,
            polygon_layer,
            poly_id,
            output_crs,
            gerar_mdt=self.checkBoxMDT.isChecked())

        if not malha_ok:
            return False

        for faixa in faixas:
            feature_id = self.create_connections_between_layers(
                faixa["estacas"],
                faixa["taludes"],
                crs,
                faixa["talude_name"],
                line_layer,
                feature_id)

        self.aplicar_simbologia_linhas_talude(line_layer)

        return bool(malha_ok)

    def _rasterizar_tin_plato(self, vertices, triangulos, crs, raster_name):
        """
        Rasteriza a superfície da malha TIN em um MDT GeoTIFF.

        Cada pixel recebe a elevação interpolada dos vértices do
        triângulo correspondente.

        Fora da área triangulada, os pixels recebem NoData.

        A resolução espacial é obtida do raster selecionado no
        comboBoxRaster, considerando o SRC de saída.
        """
        try:
            from osgeo import gdal

            if not crs.isValid() or crs.isGeographic():
                self.mostrar_mensagem(self.tr("Selecione um SRC projetado para rasterizar a TIN."), "Erro")
                return False

            if not vertices or not triangulos:
                raise ValueError(self.tr("A malha não contém vértices ou triângulos válidos."))

            # Obtém a extensão da malha.
            xs = [p[0] for p in vertices]
            ys = [p[1] for p in vertices]

            xmin, xmax = min(xs), max(xs)
            ymin, ymax = min(ys), max(ys)

            if xmax <= xmin or ymax <= ymin:
                raise ValueError(self.tr("Extensão da malha inválida."))

            # Obtém a resolução do raster de referência.
            resolucao = None

            raster = QgsProject.instance().mapLayer(self.comboBoxRaster.currentData())

            if isinstance(raster, QgsRasterLayer) and raster.isValid():

                pixel_x = abs(raster.rasterUnitsPerPixelX())
                pixel_y = abs(raster.rasterUnitsPerPixelY())

                if raster.crs() == crs:
                    resolucao = min(pixel_x, pixel_y)

                else:
                    centro = raster.extent().center()

                    transform = QgsCoordinateTransform(raster.crs(), crs, QgsProject.instance())

                    a = transform.transform(QgsPointXY(centro.x(), centro.y()))
                    b = transform.transform(QgsPointXY( centro.x() + pixel_x,  centro.y()))
                    c = transform.transform(QgsPointXY(centro.x(), centro.y() + pixel_y))

                    resolucao = min(
                        math.hypot(
                            b.x() - a.x(),
                            b.y() - a.y()),
                        math.hypot(
                            c.x() - a.x(),
                            c.y() - a.y()))

            if (resolucao is None
                or not math.isfinite(resolucao)
                or resolucao <= 0 ):
                raise ValueError(self.tr("Não foi possível determinar a resolução do raster de referência." ))

            # Calcula dimensões do MDT.
            largura = max(1, math.ceil((xmax - xmin) / resolucao))

            altura = max(1, math.ceil((ymax - ymin) / resolucao))

            if largura * altura > 50_000_000:
                raise ValueError(self.tr("O MDT excede 50 milhões de pixels. Utilize uma resolução espacial maior." ))

            nodata = -9999.0

            saida = np.full((altura, largura), nodata, dtype=np.float32)

            # Interpola as cotas dentro de cada triângulo.
            for i1, i2, i3 in triangulos:

                x1, y1, z1 = vertices[i1 - 1]
                x2, y2, z2 = vertices[i2 - 1]
                x3, y3, z3 = vertices[i3 - 1]

                det = ((y2 - y3) * (x1 - x3) + (x3 - x2) * (y1 - y3))

                if abs(det) < 1e-12:
                    continue

                # Delimita a região ocupada pelo triângulo.
                col0 = max(0,  math.floor((min(x1, x2, x3) - xmin) / resolucao - 0.5 ))
                col1 = min(largura, math.ceil((max(x1, x2, x3) - xmin) / resolucao + 0.5))

                row0 = max(0, math.floor((ymax - max(y1, y2, y3)) / resolucao - 0.5))
                row1 = min(altura, math.ceil((ymax - min(y1, y2, y3)) / resolucao + 0.5))

                if col0 >= col1 or row0 >= row1:
                    continue

                # Coordenadas dos centros dos pixels.
                xx = xmin + (np.arange(col0, col1) + 0.5) * resolucao
                yy = ymax - (np.arange(row0, row1) + 0.5) * resolucao

                px, py = np.meshgrid(xx, yy)

                # Coordenadas baricêntricas.
                w1 = ((y2 - y3) * (px - x3) + (x3 - x2) * (py - y3)) / det
                w2 = ((y3 - y1) * (px - x3) + (x1 - x3) * (py - y3)) / det
                w3 = 1.0 - w1 - w2

                # Identifica pixels internos ao triângulo.
                dentro = (
                    (w1 >= -1e-9)
                    & (w2 >= -1e-9)
                    & (w3 >= -1e-9))

                if dentro.any():

                    recorte = saida[row0:row1, col0:col1]

                    # Interpolação linear das elevações.
                    valores_z = (w1 * z1 + w2 * z2 + w3 * z3)
                    recorte[dentro] = valores_z[dentro]

            if not np.any(saida != nodata):
                raise ValueError(self.tr("Nenhum pixel válido foi produzido pela triangulação."))

            # Cria arquivo GeoTIFF temporário.
            fd, caminho = tempfile.mkstemp(prefix="tempo_salvo_mdt_", suffix=".tif")

            os.close(fd)

            driver = gdal.GetDriverByName("GTiff")

            ds = driver.Create(
                caminho,
                largura,
                altura,
                1,
                gdal.GDT_Float32,
                options=[
                    "COMPRESS=LZW",
                    "TILED=YES"])

            if ds is None:
                raise RuntimeError(self.tr("Falha ao criar o GeoTIFF."))

            # Configura georreferenciamento.
            ds.SetGeoTransform((xmin, resolucao, 0.0, ymax, 0.0, -resolucao))
            ds.SetProjection(crs.toWkt())

            banda = ds.GetRasterBand(1)

            banda.SetNoDataValue(nodata)
            banda.WriteArray(saida)
            banda.FlushCache()

            ds.FlushCache()
            ds = None

            # Carrega o MDT no projeto QGIS.
            raster_layer = QgsRasterLayer(caminho, raster_name)

            if not raster_layer.isValid():
                raise RuntimeError(self.tr("O GeoTIFF gerado não pôde ser carregado."))

            # Remove somente o MDT anterior com o mesmo nome.
            for antiga in QgsProject.instance().mapLayersByName(raster_name):
                if isinstance(antiga, QgsRasterLayer):
                    QgsProject.instance().removeMapLayer(antiga.id())

            # Insere o MDT no grupo correspondente ao platô.
            self._top_insert_layer(raster_layer)

            return True

        except Exception as e:

            self.mostrar_mensagem(self.tr("Erro ao rasterizar a malha TIN: {error}").format(error=str(e)), "Erro")

            return False

    def _create_mesh_from_faixas(self, faixas, estacas_points_global, mesh_name, source_crs, polygon_layer, poly_id, output_crs=None, gerar_mdt=False):
        """
        Gera uma única TIN contendo:
        1. a superfície interna do Platô;
        2. as faixas Estaca ↔ Talude.

        O interior fica limitado ao polígono correspondente ao ID e
        o talude é triangulado somente entre pontos correspondentes.
        """
        try:
            if output_crs is None:
                output_crs = self._escolher_crs_malha(source_crs)

                if output_crs is None:
                    return False

            if not output_crs.isValid():
                self.mostrar_mensagem(self.tr("Nenhuma projeção válida foi selecionada para a malha."), "Erro")
                return False

            # Localiza exatamente a feição de polígono correspondente ao ID processado.
            feature_poly = None

            for feature in polygon_layer.getFeatures():
                feature_id = self._get_poly_id_for_naming(polygon_layer, feature)

                if str(feature_id) == str(poly_id):
                    feature_poly = feature
                    break

            if feature_poly is None or not feature_poly.hasGeometry():
                self.mostrar_mensagem(self.tr("Não foi possível localizar o polígono correspondente ao ID {id}.").format(id=poly_id), "Erro")
                return False

            geom_plato = QgsGeometry(feature_poly.geometry())

            if polygon_layer.crs() != output_crs:
                transform_poly = QgsCoordinateTransform(
                    polygon_layer.crs(), output_crs, QgsProject.instance())
                geom_plato.transform(transform_poly)

            if not geom_plato.isGeosValid():
                geom_plato = geom_plato.makeValid()

            vertices = []
            indice_vertices = {}
            triangulos = []

            def obter_cota(feature, preferido):
                nomes = feature.fields().names()

                for campo in (preferido, "NovoZ", "Z", "Cota"):
                    if campo not in nomes:
                        continue

                    valor = feature[campo]

                    try:
                        valor = float(valor)

                        if math.isfinite(valor):
                            return valor
                    except (TypeError, ValueError):
                        continue

                return None

            def obter_ponto(item, campo_cota):
                feature, geom, item_crs = item

                if not geom or geom.isEmpty() or geom.type() != Qgis.GeometryType.Point:
                    return None

                pt = QgsPointXY(geom.asPoint())

                if item_crs != output_crs:
                    try:
                        transform = QgsCoordinateTransform(
                            item_crs, output_crs, QgsProject.instance())
                        pt = transform.transform(pt)
                    except Exception:
                        return None

                z = obter_cota(feature, campo_cota)

                if z is None:
                    return None

                return pt.x(), pt.y(), z

            def indice_vertice(ponto):
                x, y, z = ponto
                chave = (round(x, 8), round(y, 8))

                if chave in indice_vertices:
                    return indice_vertices[chave]

                indice = len(vertices) + 1
                vertices.append((x, y, z))
                indice_vertices[chave] = indice

                return indice

            def adicionar_triangulo(p1, p2, p3):
                area2 = ((p2[0] - p1[0]) * (p3[1] - p1[1])
                         - (p3[0] - p1[0]) * (p2[1] - p1[1]))

                if abs(area2) <= 1e-10:
                    return

                i1 = indice_vertice(p1)
                i2 = indice_vertice(p2)
                i3 = indice_vertice(p3)

                if len({i1, i2, i3}) < 3:
                    return

                if area2 < 0:
                    i2, i3 = i3, i2

                triangulos.append((i1, i2, i3))

            # 1. INTERIOR DO PLATÔ
            pontos_borda = {}

            # O interior do Platô usa TODOS os pontos de Estaqueamento,
            # independentemente da existência de Talude naquele segmento.
            for feature, geom, item_crs, _layer_name in estacas_points_global:
                item = (feature, geom, item_crs)
                ponto = obter_ponto(item, "NovoZ")

                if ponto is None:
                    continue

                chave = (round(ponto[0], 8), round(ponto[1], 8))
                pontos_borda[chave] = ponto

            if len(pontos_borda) < 3:
                self.mostrar_mensagem(self.tr("Não há pontos suficientes na borda do Platô para gerar a superfície."), "Erro")
                return False

            lista_borda = list(pontos_borda.values())
            multi_pontos = QgsGeometry.fromMultiPointXY(
                [QgsPointXY(p[0], p[1]) for p in lista_borda])

            delaunay = multi_pontos.delaunayTriangulation(0.0, False)

            if not delaunay or delaunay.isEmpty():
                self.mostrar_mensagem(
                    self.tr("Não foi possível triangular o interior do Platô."),
                    "Erro")
                return False

            partes = delaunay.asGeometryCollection()

            if not partes and delaunay.type() == Qgis.GeometryType.Polygon:
                partes = [delaunay]

            for triangulo_geom in partes:
                if not triangulo_geom or triangulo_geom.isEmpty():
                    continue

                area_triangulo = triangulo_geom.area()

                if area_triangulo <= 1e-12:
                    continue

                # A Delaunay dos pontos da borda pode gerar triângulos
                # atravessando áreas externas em polígonos côncavos.
                # Mantém somente os pertencentes ao polígono deste ID.
                intersecao = triangulo_geom.intersection(geom_plato)

                if not intersecao or intersecao.isEmpty():
                    continue

                proporcao = intersecao.area() / area_triangulo

                if proporcao < 0.98:
                    continue

                if triangulo_geom.isMultipart():
                    multi = triangulo_geom.asMultiPolygon()

                    if not multi or not multi[0] or not multi[0][0]:
                        continue

                    anel = multi[0][0]
                else:
                    poly = triangulo_geom.asPolygon()

                    if not poly or not poly[0]:
                        continue

                    anel = poly[0]

                coords = []

                for pt in anel:
                    chave = (round(pt.x(), 8), round(pt.y(), 8))
                    ponto = pontos_borda.get(chave)

                    if ponto is None:
                        # Fallback para diferença numérica mínima.
                        mais_proximo = min(
                            lista_borda,
                            key=lambda p: math.hypot(
                                p[0] - pt.x(),
                                p[1] - pt.y()))

                        distancia = math.hypot(
                            mais_proximo[0] - pt.x(),
                            mais_proximo[1] - pt.y())

                        if distancia > 1e-5:
                            continue

                        ponto = mais_proximo

                    if not coords or (
                        round(coords[-1][0], 8),
                        round(coords[-1][1], 8)) != chave:
                        coords.append(ponto)

                # O último ponto de um anel normalmente repete o primeiro.
                if len(coords) >= 4:
                    if (round(coords[0][0], 8), round(coords[0][1], 8)) == (
                        round(coords[-1][0], 8), round(coords[-1][1], 8)):
                        coords.pop()

                if len(coords) == 3:
                    adicionar_triangulo(coords[0], coords[1], coords[2])

            # 2. FAIXAS DE TALUDE
            for faixa in faixas:
                estacas = faixa.get("estacas", [])
                taludes = faixa.get("taludes", [])
                quantidade = min(len(estacas), len(taludes))

                if quantidade < 2:
                    continue

                for i in range(quantidade - 1):
                    estaca_1 = obter_ponto(estacas[i], "NovoZ")
                    estaca_2 = obter_ponto(estacas[i + 1], "NovoZ")
                    talude_1 = obter_ponto(taludes[i], "Z")
                    talude_2 = obter_ponto(taludes[i + 1], "Z")

                    if None in (estaca_1, estaca_2, talude_1, talude_2):
                        continue

                    adicionar_triangulo(estaca_1, estaca_2, talude_1)
                    adicionar_triangulo(estaca_2, talude_2, talude_1)

            if not vertices or not triangulos:
                self.mostrar_mensagem(self.tr("Não foi possível formar triângulos válidos para a malha."), "Erro")
                return False

            fd, mesh_path = tempfile.mkstemp(
                prefix="tempo_salvo_plato_",
                suffix=".2dm")
            os.close(fd)

            with open(mesh_path, "w", encoding="utf-8") as arquivo:
                arquivo.write("MESH2D\n")

                for elemento_id, (n1, n2, n3) in enumerate(
                    triangulos, start=1):
                    arquivo.write(
                        f"E3T {elemento_id} {n1} {n2} {n3} 1\n")

                for node_id, (x, y, z) in enumerate(
                    vertices, start=1):
                    arquivo.write(
                        f"ND {node_id} {x:.8f} {y:.8f} {z:.6f}\n")

            mesh_layer = QgsMeshLayer(mesh_path, mesh_name, "mdal")

            if not mesh_layer.isValid():
                raise Exception(self.tr("Falha ao carregar a malha gerada."))

            mesh_layer.setCrs(output_crs)

            # Remove somente outra versão da TIN deste mesmo ID.
            for layer in QgsProject.instance().mapLayersByName(mesh_name):
                if isinstance(layer, QgsMeshLayer):
                    QgsProject.instance().removeMapLayer(layer.id())

            self._top_insert_layer(mesh_layer)

            # Rasteriza a TIN somente quando solicitado.
            if gerar_mdt:
                raster_name = f"{polygon_layer.name()}_ID{poly_id}_MDT"

                if not self._rasterizar_tin_plato(
                    vertices,
                    triangulos,
                    output_crs,
                    raster_name):
                    return False

            return True

        except Exception as e:
            mensagem = self.tr("Erro ao gerar a TIN '{mesh_name}': {error}").format(mesh_name=mesh_name, error=str(e))

            QgsMessageLog.logMessage(mensagem, "Tempo Salvo Tools - Platô", Qgis.MessageLevel.Critical)

            self.mostrar_mensagem(mensagem, "Erro")
            return False

    def update_pushButtonSalvar_state(self, *_args):
        """Habilita Salvar somente quando houver camadas relacionadas ao Platô atual."""
        if getattr(self, "_salvando_gpkg", False):
            self.pushButtonSalvar.setEnabled(False)
            return

        try:
            camadas, polygon_layer, _ids = self._coletar_camadas_relacionadas_plato()
            self.pushButtonSalvar.setEnabled(bool(polygon_layer and camadas))

        except Exception:
            self.pushButtonSalvar.setEnabled(False)

    def _coletar_camadas_relacionadas_plato(self):
        """
        Retorna todas as camadas de pontos e linhas pertencentes
        a todos os IDs da camada de polígonos atualmente selecionada.
        """
        project = QgsProject.instance()
        polygon_id = self.comboBoxPoligono.currentData()
        polygon_layer = project.mapLayer(polygon_id)

        if not polygon_layer or not isinstance(polygon_layer, QgsVectorLayer):
            return [], None, []

        prefixo_base = f"{polygon_layer.name()}_ID"
        padrao = re.compile(rf"^{re.escape(polygon_layer.name())}_ID([^_]+)_")

        camadas = []
        ids_encontrados = set()

        for layer in project.mapLayers().values():
            if not isinstance(layer, QgsVectorLayer) or not layer.isValid():
                continue

            if layer.geometryType() not in (
                Qgis.GeometryType.Point,
                Qgis.GeometryType.Line):
                continue

            if not layer.name().startswith(prefixo_base):
                continue

            match = padrao.match(layer.name())

            if not match:
                continue

            ids_encontrados.add(match.group(1))
            camadas.append(layer)

        # Inclui também a própria camada de polígonos.
        # Ela será necessária posteriormente para reconstruir as malhas TIN.
        if polygon_layer not in camadas:
            camadas.append(polygon_layer)

        camadas.sort(key=lambda lyr: self._chave_ordenacao_natural(lyr.name()))

        ids_encontrados = sorted(ids_encontrados,
            key=self._chave_ordenacao_natural)

        return camadas, polygon_layer, ids_encontrados

    def salvar_camadas_geopackage(self):
        """Salva em GeoPackage todas as camadas de pontos e linhas relacionadas ao Platô ativo."""
        if getattr(self, "_salvando_gpkg", False):
            self.mostrar_mensagem(self.tr("Já existe um salvamento em andamento."), "Aviso")
            return

        camadas, polygon_layer, ids_encontrados = self._coletar_camadas_relacionadas_plato()

        if not polygon_layer:
            self.mostrar_mensagem(self.tr("Selecione uma camada de polígono e uma feição válida."), "Erro")
            return

        if not camadas:
            self.mostrar_mensagem(self.tr("Não foram encontradas camadas de Platô relacionadas à camada de polígonos selecionada."), "Aviso")
            return

        nome_arquivo = f"{polygon_layer.name()}_Platos.gpkg"
        nome_arquivo = "".join("_" if c in '<>:"/\\|?*' else c for c in nome_arquivo)
        pasta_inicial = QgsProject.instance().homePath() or ""
        caminho_inicial = os.path.join(pasta_inicial, nome_arquivo) if pasta_inicial else nome_arquivo

        caminho, _ = QFileDialog.getSaveFileName(self, self.tr("Salvar dados do Platô"), caminho_inicial, self.tr("GeoPackage (*.gpkg)"))

        if not caminho:
            return

        if not caminho.lower().endswith(".gpkg"):
            caminho += ".gpkg"

        pasta_destino = os.path.dirname(caminho) or os.getcwd()

        try:
            fd, caminho_temp = tempfile.mkstemp(prefix=".tempo_salvo_plato_", suffix=".gpkg", dir=pasta_destino)
            os.close(fd)
            os.remove(caminho_temp)

        except Exception as e:
            self.mostrar_mensagem(self.tr("Não foi possível preparar o arquivo temporário: {error}").format(error=str(e)), "Erro")
            return

        fila = []

        # Captura o estilo atual antes de iniciar as tarefas
        for layer in camadas:
            doc = QDomDocument()
            erro_estilo = layer.exportNamedStyle(doc)
            fila.append({"layer_id": layer.id(), "name": layer.name(), "style_xml": doc.toString(), "style_error": erro_estilo})

        self._salvando_gpkg = True
        self._gpkg_fila = fila
        self._gpkg_indice = 0
        self._gpkg_caminho_final = caminho
        self._gpkg_caminho_temp = caminho_temp
        self._gpkg_task = None
        self._gpkg_avisos_estilo = []

        self.pushButtonSalvar.setEnabled(False)

        self._gpkg_progress_item = self.iface.messageBar().createMessage(self.tr("Salvando dados do Platô..."))
        self._gpkg_progress_bar = QProgressBar()
        self._gpkg_progress_bar.setRange(0, 100)
        self._gpkg_progress_bar.setValue(0)
        self._gpkg_progress_bar.setFormat("%p%")
        self._gpkg_progress_item.layout().addWidget(self._gpkg_progress_bar)
        self.iface.messageBar().pushWidget(self._gpkg_progress_item, Qgis.MessageLevel.Info)

        self._iniciar_proxima_camada_gpkg()

    def _iniciar_proxima_camada_gpkg(self):
        """Inicia a próxima exportação da fila, sempre uma camada por vez."""
        if not self._salvando_gpkg:
            return

        if self._gpkg_indice >= len(self._gpkg_fila):
            self._concluir_salvamento_gpkg()
            return

        entrada = self._gpkg_fila[self._gpkg_indice]
        layer = QgsProject.instance().mapLayer(entrada["layer_id"])

        if not layer or not isinstance(layer, QgsVectorLayer):
            self._falhar_salvamento_gpkg(self.tr("A camada '{layer_name}' não está mais disponível.").format(layer_name=entrada["name"]))
            return

        options = QgsVectorFileWriter.SaveVectorOptions()
        options.driverName = "GPKG"
        options.fileEncoding = "UTF-8"
        options.layerName = entrada["name"]
        options.layerOptions = ["SPATIAL_INDEX=YES"]
        options.includeConstraints = True

        if self._gpkg_indice == 0:
            options.actionOnExistingFile = QgsVectorFileWriter.ActionOnExistingFile.CreateOrOverwriteFile
        else:
            options.actionOnExistingFile = QgsVectorFileWriter.ActionOnExistingFile.CreateOrOverwriteLayer

        task = QgsVectorFileWriterTask(layer, self._gpkg_caminho_temp, options)
        self._gpkg_task = task

        task.progressChanged.connect(self._atualizar_progresso_gpkg)
        task.writeComplete.connect(self._camada_gpkg_concluida)
        task.errorOccurred.connect(lambda _codigo, mensagem: self._falhar_salvamento_gpkg(mensagem))

        QgsApplication.taskManager().addTask(task)

    def _atualizar_progresso_gpkg(self, valor):
        """Converte o progresso da camada atual em progresso global do pacote."""
        if not getattr(self, "_salvando_gpkg", False):
            return

        total = max(1, len(self._gpkg_fila))
        valor = max(0.0, min(100.0, float(valor)))
        progresso = ((self._gpkg_indice + valor / 100.0) / total) * 100.0

        if getattr(self, "_gpkg_progress_bar", None):
            self._gpkg_progress_bar.setValue(int(round(progresso)))

    def _camada_gpkg_concluida(self, _novo_arquivo):
        """Grava o estilo da camada concluída e inicia a seguinte."""
        if not getattr(self, "_salvando_gpkg", False):
            return

        entrada = self._gpkg_fila[self._gpkg_indice]

        if entrada["style_error"]:
            self._gpkg_avisos_estilo.append(f"{entrada['name']}: {entrada['style_error']}")

        elif entrada["style_xml"]:
            aviso = self._salvar_estilo_no_gpkg(self._gpkg_caminho_temp, entrada["name"], entrada["style_xml"])

            if aviso:
                self._gpkg_avisos_estilo.append(aviso)

        self._gpkg_indice += 1
        self._gpkg_task = None

        if getattr(self, "_gpkg_progress_bar", None):
            self._gpkg_progress_bar.setValue(int(round((self._gpkg_indice / len(self._gpkg_fila)) * 100.0)))

        self._iniciar_proxima_camada_gpkg()

    def _salvar_estilo_no_gpkg(self, caminho, layer_name, style_xml):
        """Copia o estilo QGIS da camada original para dentro do próprio GeoPackage."""
        uri = f"{caminho}|layername={layer_name}"
        layer_gpkg = QgsVectorLayer(uri, layer_name, "ogr")

        if not layer_gpkg.isValid():
            return self.tr("Não foi possível abrir '{layer_name}' para gravar o estilo.").format(layer_name=layer_name)

        try:
            doc = QDomDocument()
            doc.setContent(style_xml)

            resultado_importacao = layer_gpkg.importNamedStyle(doc)

            if isinstance(resultado_importacao, tuple):
                estilo_ok, erro_importacao = resultado_importacao
            else:
                estilo_ok, erro_importacao = bool(resultado_importacao), ""

            if not estilo_ok:
                return self.tr("Não foi possível aplicar o estilo de '{layer_name}': {error}").format(layer_name=layer_name, error=erro_importacao)

            _resultado, erro_banco = layer_gpkg.saveStyleToDatabaseV2(layer_name, self.tr("Estilo salvo pelo Tempo Salvo Tools"), True, "")

            if erro_banco:
                return self.tr("A camada '{layer_name}' foi salva, mas ocorreu um aviso ao gravar o estilo: {error}").format(layer_name=layer_name, error=erro_banco)

        except Exception as e:
            return self.tr("A camada '{layer_name}' foi salva, mas o estilo não pôde ser armazenado: {error}").format(layer_name=layer_name, error=str(e))

        finally:
            del layer_gpkg

        return None

    def _concluir_salvamento_gpkg(self):
        """Substitui o arquivo final somente depois que todas as camadas forem concluídas."""
        try:
            os.replace(self._gpkg_caminho_temp, self._gpkg_caminho_final)

        except Exception as e:
            self._falhar_salvamento_gpkg(self.tr("As camadas foram processadas, mas não foi possível concluir o GeoPackage: {error}").format(error=str(e)), remover_temp=False)
            return

        self._encerrar_interface_salvamento_gpkg()

        total = len(self._gpkg_fila)

        if self._gpkg_avisos_estilo:
            self.mostrar_mensagem(self.tr("GeoPackage salvo com {count} camadas. Alguns estilos apresentaram avisos.").format(count=total), "Aviso")

            for aviso in self._gpkg_avisos_estilo:
                QgsMessageLog.logMessage(aviso, "Tempo Salvo Tools", Qgis.MessageLevel.Warning)

        else:
            self.mostrar_mensagem(self.tr("GeoPackage salvo com sucesso. {count} camadas foram gravadas com seus estilos.").format(count=total), "Sucesso")

    def _falhar_salvamento_gpkg(self, mensagem, remover_temp=True):
        """Interrompe a sequência sem substituir o GeoPackage final."""
        if not getattr(self, "_salvando_gpkg", False):
            return

        if self._gpkg_task:
            try:
                self._gpkg_task.cancel()

            except Exception as e:
                QgsMessageLog.logMessage(self.tr("Não foi possível cancelar a tarefa de salvamento do GeoPackage: {error}").format(error=str(e)), "Tempo Salvo Tools", Qgis.MessageLevel.Warning)

        caminho_temp = getattr(self, "_gpkg_caminho_temp", None)

        if remover_temp and caminho_temp and os.path.exists(caminho_temp):
            try:
                os.remove(caminho_temp)

            except OSError as e:
                QgsMessageLog.logMessage(self.tr("Não foi possível remover o arquivo temporário do GeoPackage: {error}").format(error=str(e)), "Tempo Salvo Tools", Qgis.MessageLevel.Warning)

        self._encerrar_interface_salvamento_gpkg()
        self.mostrar_mensagem(self.tr("Erro ao salvar o GeoPackage: {error}").format(error=mensagem), "Erro")

    def _encerrar_interface_salvamento_gpkg(self):
        """Limpa barra de progresso e restaura o botão."""
        item = getattr(self, "_gpkg_progress_item", None)

        if item:
            try:
                self.iface.messageBar().popWidget(item)
            except Exception:
                pass # nosec B110 | O widget pode já ter sido removido da barra de mensagens

        self._salvando_gpkg = False
        self._gpkg_task = None
        self._gpkg_progress_item = None
        self._gpkg_progress_bar = None

        self.update_pushButtonSalvar_state()

    def _grupo_camada_geopackage(self, layer):
        """Identifica em qual grupo do Platô uma camada salva deve ser inserida."""
        if not isinstance(layer, QgsVectorLayer) or layer.geometryType() != Qgis.GeometryType.Point:
            return None

        campos = set(layer.fields().names())

        # Estaqueamentos possuem Acumula_dist
        if "Acumula_dist" in campos:
            return self.tr("Estaqueamentos")

        # Taludes possuem Desnível, mas não Acumula_dist
        if "Desnível" in campos and "Acumula_dist" not in campos:
            return self.tr("Taludes")

        # Segmentos individuais são camadas de dois pontos
        campos_segmento = {"ID", "X", "Y", "Z", "NovoZ"}

        if campos_segmento.issubset(campos) and layer.featureCount() == 2:
            return self.tr("Segmentos")

        # Vértices, Pontos unidos e camadas de linha permanecem fora dos grupos
        return None

    def _chave_ordenacao_natural(self, texto):
        """Ordena 1_2, 2_3, 3_4 ... 10_11 corretamente."""
        partes = re.split(r"(\d+)", texto)

        return [(0, int(parte)) if parte.isdigit() else (1, parte.casefold()) for parte in partes]

    def abrir_projeto_salvo(self):
        """Abre um GeoPackage salvo pelo Platô e restaura camadas, grupos e estilos."""
        caminho, _ = QFileDialog.getOpenFileName(self, self.tr("Abrir Projeto Salvo"), "", self.tr("GeoPackage (*.gpkg)"))

        if not caminho:
            return

        if not os.path.isfile(caminho):
            self.mostrar_mensagem(self.tr("O arquivo selecionado não existe."), "Erro")
            return

        self.pushButtonAbrir.setEnabled(False)
        progress_item = None

        try:
            detalhes = QgsProviderRegistry.instance().querySublayers(caminho)
            detalhes = [d for d in detalhes if d.type() == Qgis.LayerType.Vector]

            if not detalhes:
                self.mostrar_mensagem(self.tr("Nenhuma camada vetorial foi encontrada no GeoPackage."), "Aviso")
                return

            progress_item = self.iface.messageBar().createMessage(self.tr("Abrindo dados do Platô..."))
            progress_bar = QProgressBar()
            progress_bar.setRange(0, len(detalhes))
            progress_bar.setValue(0)
            progress_bar.setFormat("%v / %m")
            progress_item.layout().addWidget(progress_bar)
            self.iface.messageBar().pushWidget(progress_item, Qgis.MessageLevel.Info)

            project = QgsProject.instance()
            root = project.layerTreeRoot()
            options = QgsProviderSublayerDetails.LayerOptions(project.transformContext())
            options.loadDefaultStyle = True

            camadas_grupos = {
                self.tr("Segmentos"): [],
                self.tr("Estaqueamentos"): [],
                self.tr("Taludes"): []}

            camadas_principais = []
            camadas_poligono = []
            todas_camadas = []
            erros = []

            detalhes.sort(key=lambda d: self._chave_ordenacao_natural(d.name()))

            for indice, detalhe in enumerate(detalhes, start=1):
                try:
                    layer = detalhe.toLayer(options)

                    if not layer or not isinstance(layer, QgsVectorLayer) or not layer.isValid():
                        erros.append(detalhe.name())
                        progress_bar.setValue(indice)
                        QCoreApplication.processEvents()
                        continue

                    # O projeto salvo pode conter pontos, linhas e
                    # a camada poligonal original do Platô.
                    if layer.geometryType() not in (
                        Qgis.GeometryType.Point,
                        Qgis.GeometryType.Line,
                        Qgis.GeometryType.Polygon):

                        del layer
                        progress_bar.setValue(indice)
                        QCoreApplication.processEvents()
                        continue

                    if layer.geometryType() == Qgis.GeometryType.Polygon:
                        camadas_poligono.append(layer)

                    else:
                        grupo = self._grupo_camada_geopackage(layer)

                        if grupo:
                            camadas_grupos[grupo].append(layer)
                        else:
                            camadas_principais.append(layer)

                    todas_camadas.append(layer)

                except Exception as e:
                    erros.append(f"{detalhe.name()}: {e}")

                progress_bar.setValue(indice)
                QCoreApplication.processEvents()

            if not todas_camadas:
                self.mostrar_mensagem(self.tr("Não foi possível carregar nenhuma camada válida do GeoPackage."), "Erro")
                return

            # Remove somente camadas existentes que tenham exatamente
            # os mesmos nomes das camadas que serão restauradas.
            nomes_salvos = {layer.name() for layer in todas_camadas}
            ids_remover = []

            for layer_existente in project.mapLayers().values():
                if layer_existente.name() in nomes_salvos:
                    ids_remover.append(layer_existente.id())

            if ids_remover:
                project.removeMapLayers(ids_remover)

            # Registra todas as camadas de uma só vez, sem colocá-las
            # automaticamente na árvore.
            project.addMapLayers(todas_camadas, False)

            # Restaura a camada de polígonos na raiz da árvore.
            for layer in reversed(camadas_poligono):
                root.insertLayer(0, layer)

                node = root.findLayer(layer.id())

                if node:
                    node.setExpanded(False)

            # Camadas principais são agrupadas por NomeDoPolígono_ID.
            camadas_principais.sort(key=lambda layer: self._chave_ordenacao_natural(layer.name()))

            grupos_principais = {}

            for layer in camadas_principais:
                match = re.match(r"^(.*)_ID([^_]+)_", layer.name())

                if not match:
                    root.insertLayer(0, layer)
                    continue

                nome_grupo = f"{match.group(1)}_ID{match.group(2)}"
                grupos_principais.setdefault(nome_grupo, []).append(layer)

            for nome_grupo, layers in grupos_principais.items():
                group = root.findGroup(nome_grupo)

                if not group:
                    group = root.insertGroup(0, nome_grupo)

                for layer in reversed(layers):
                    group.insertLayer(0, layer)

                    node = group.findLayer(layer.id())

                    if node:
                        node.setExpanded(False)

                group.setExpanded(True)

            # Reconstrói os grupos.
            for nome_grupo in (self.tr("Segmentos"), self.tr("Estaqueamentos"), self.tr("Taludes")):
                layers = camadas_grupos[nome_grupo]

                if not layers:
                    continue

                group = root.findGroup(nome_grupo)

                if not group:
                    group = root.addGroup(nome_grupo)

                layers.sort(key=lambda layer: self._chave_ordenacao_natural(layer.name()))

                for layer in layers:
                    group.addLayer(layer)

                    node = group.findLayer(layer.id())

                    if node:
                        node.setExpanded(False)

                # Deixa a "pasta" aberta no painel de camadas
                group.setExpanded(True)

            # Atualiza o combo de polígonos e seleciona automaticamente
            # a camada poligonal restaurada do GeoPackage.
            self.init_combo_box_poligono()

            if camadas_poligono:
                polygon_layer_restaurado = camadas_poligono[0]
                indice_combo = self.comboBoxPoligono.findData(
                    polygon_layer_restaurado.id())

                if indice_combo >= 0:
                    self.comboBoxPoligono.setCurrentIndex(indice_combo)

            self.update_list_widget_segmentos()
            self.update_list_widget_estaqueamentos()
            self.update_list_widget_talude()

            self.iface.mapCanvas().refresh()

            if erros:
                for erro in erros:
                    QgsMessageLog.logMessage(str(erro), "Tempo Salvo Tools", Qgis.MessageLevel.Warning)

                self.mostrar_mensagem(self.tr("Projeto aberto. {count} camadas carregadas, com alguns avisos registrados no log.").format(count=len(todas_camadas)), "Aviso")

            else:
                self.mostrar_mensagem(self.tr("Projeto aberto com sucesso. {count} camadas foram restauradas.").format(count=len(todas_camadas)), "Sucesso")

        except Exception as e:
            self.mostrar_mensagem(self.tr("Erro ao abrir o GeoPackage: {error}").format(error=str(e)), "Erro")

        finally:
            if progress_item:
                try:
                    self.iface.messageBar().popWidget(progress_item)

                except Exception as e:
                    QgsMessageLog.logMessage(self.tr("Não foi possível remover a barra de progresso: {error}").format(error=str(e)), "Tempo Salvo Tools", Qgis.MessageLevel.Warning)

            self.pushButtonAbrir.setEnabled(True)

    def update_radio_buttons_state(self):
        """
        Habilita/desabilita e (des)seleciona os radio buttons
        de acordo com o conteúdo do listWidgetEstacas.
        """
        # cabeçalho ocupa o índice 0; conta itens “reais”
        total_itens = self.listWidgetEstacas.count() - 1  # −1 para ignorar o cabeçalho
        tem_estacas    = total_itens > 0

        # habilita / desabilita
        self.radioButtonEsquerda.setEnabled(tem_estacas)
        self.radioButtonDireita.setEnabled(tem_estacas)

        if not tem_estacas:
            # 👉 nenhum dado → nenhum botão marcado
            for rb in (self.radioButtonEsquerda, self.radioButtonDireita):
                rb.setAutoExclusive(False)   # permite “desmarcar”
                rb.setChecked(False)
                rb.setAutoExclusive(True)    # restaura exclusividade
        else:
            # 👉 há dados → garante que pelo menos um esteja marcado
            if not (self.radioButtonEsquerda.isChecked() or self.radioButtonDireita.isChecked()):
                self.radioButtonEsquerda.setChecked(True)

    def update_pushButtonGrafico_state(self):
        """
        Ativa o pushButtonGrafico somente se houver algum item real
        (isto é, não-cabeçalho) selecionado no listWidgetEstacas.
        """
        # Filtra os itens selecionados ignorando o cabeçalho
        selecionados_validos = [it for it in self.listWidgetEstacas.selectedItems()
            if it.flags() != Qt.ItemFlag.NoItemFlags]

        # Habilita se existir pelo menos um
        self.pushButtonGrafico.setEnabled(bool(selecionados_validos))

    def update_pushButtonJuntar_state(self):
        """
        Habilita o pushButtonJuntar quando houver
        pelo menos uma camada de Estaqueamento.
        """
        estacas_count = max(0, self.listWidgetEstacas.count() - 1)
        self.pushButtonJuntar.setEnabled(estacas_count > 0)

    def on_pushButtonLogo_clicked(self):
        """Método chamado ao clicar no botão para selecionar o logo."""
        # Abrir um diálogo para selecionar a imagem
        logo_path, _ = QFileDialog.getOpenFileName(self, self.tr("Selecione o logo"), "", self.tr("Arquivos de imagem (*.png *.jpg *.jpeg)"))

        if logo_path:
            # Armazenar o caminho da imagem selecionada na memória
            self.logo_path = logo_path
            self.mostrar_mensagem(self.tr("Logotipo selecionado: {logo_path}").format(logo_path=logo_path), "Sucesso")

            # Atualizar o texto e a cor do botão, sem alterar o estilo original
            self.pushButtonLogo.setText("Logo ✓")
            self.pushButtonLogo.setStyleSheet(self.pushButtonLogo.styleSheet() + "color: blue;")
        else:
            self.mostrar_mensagem(self.tr("Nenhum logotipo selecionado."), "Erro")

            # Resetar o botão para o estado inicial se não houver logo
            self.logo_path = None
            self.pushButtonLogo.setText("Logo")
            self.pushButtonLogo.setStyleSheet(self.pushButtonLogo.styleSheet() + "color: black;")

    def check_logo_status(self):
        """Verifica se existe um logo armazenado e ajusta o botão pushButtonLogo adequadamente."""
        if hasattr(self, 'logo_path') and self.logo_path:
            # Se houver um logo armazenado, exibe o texto "Logo ✓" e estilo azul
            self.pushButtonLogo.setText("Logo ✓")
            self.pushButtonLogo.setStyleSheet(self.pushButtonLogo.styleSheet() + "color: blue;")
        else:
            # Caso contrário, exibe o texto "Logo" com o estilo padrão
            self.pushButtonLogo.setText("Logo")
            self.pushButtonLogo.setStyleSheet(self.pushButtonLogo.styleSheet() + "color: black;")

    def on_pushButtonVertices_clicked(self):
        """
        Atualiza o estado dos botões Calcular e Rampa.

        Ambos somente ficam disponíveis depois que os vértices,
        segmentos e dados do scrollArea tiverem sido criados.
        """
        layout = self.scrollAreaWidgetContents.layout()

        tem_dados = (
            layout is not None
            and layout.count() > 0
            and bool(getattr(self, "points", []))
            and bool(getattr(self, "lines", []))
            and bool(getattr(self, "scroll_widgets", [])))

        self.pushButtonCalcular.setEnabled(tem_dados)
        self.pushButtonRampa.setEnabled(tem_dados)

    def _obter_normal_interna_rampa(self, p_inicio, p_fim, geom_poligono):
        """
        Determina automaticamente qual lado do segmento
        corresponde ao interior do polígono.

        Retorna a normal unitária apontando para dentro.
        """
        dx = p_fim.x() - p_inicio.x()
        dy = p_fim.y() - p_inicio.y()

        comprimento = math.hypot(dx, dy)

        if comprimento <= 0:
            return None

        ux = dx / comprimento
        uy = dy / comprimento

        # Normal à esquerda do segmento
        nx_esq = -uy
        ny_esq = ux

        # Normal à direita
        nx_dir = uy
        ny_dir = -ux

        mx = (p_inicio.x() + p_fim.x()) / 2.0
        my = (p_inicio.y() + p_fim.y()) / 2.0

        # Testa pequenos deslocamentos para cada lado do segmento.
        fatores = (0.000001, 0.00001, 0.0001, 0.001, 0.01)

        for fator in fatores:
            deslocamento = comprimento * fator

            ponto_esq = QgsGeometry.fromPointXY(
                QgsPointXY(
                    mx + nx_esq * deslocamento,
                    my + ny_esq * deslocamento))

            ponto_dir = QgsGeometry.fromPointXY(
                QgsPointXY(
                    mx + nx_dir * deslocamento,
                    my + ny_dir * deslocamento))

            dentro_esq = geom_poligono.contains(ponto_esq)
            dentro_dir = geom_poligono.contains(ponto_dir)

            if (dentro_esq
                and not dentro_dir):
                return (nx_esq, ny_esq)

            if (dentro_dir
                and not dentro_esq):
                return (nx_dir, ny_dir)

        # Fallback:
        # usa um ponto garantidamente interno do polígono.
        ponto_interno_geom = (geom_poligono.pointOnSurface())

        if (ponto_interno_geom
            and not ponto_interno_geom.isEmpty()):
            ponto_interno = (ponto_interno_geom.asPoint())

            vx = ponto_interno.x() - mx
            vy = ponto_interno.y() - my

            produto = (vx * nx_esq + vy * ny_esq)

            if produto >= 0:
                return (nx_esq, ny_esq)

            return (nx_dir, ny_dir)

        return None

    def _calcular_rampa_teorica(self, indice_segmento, inclinacao_pct, subir):
        """
        Calcula teoricamente os NovoZ de todos os vértices
        usando o segmento escolhido como linha 3D fixa.

        Nesta etapa NÃO altera self.points nem o scrollArea.
        """
        total_pontos = len(self.points)

        if total_pontos < 3:
            self.mostrar_mensagem(self.tr("São necessários pelo menos três vértices para calcular a rampa."), "Erro")
            return None

        if (indice_segmento < 0
            or indice_segmento >= total_pontos):
            self.mostrar_mensagem(self.tr("Segmento de referência inválido."), "Erro")
            return None

        indice_inicio = indice_segmento
        indice_fim = (indice_segmento + 1) % total_pontos

        ponto_inicio = self.points[indice_inicio]
        ponto_fim = self.points[indice_fim]

        # Coordenadas da linha fixa
        x0 = float(ponto_inicio["X"])
        y0 = float(ponto_inicio["Y"])
        z0 = float(ponto_inicio["NovoZ"])

        x1 = float(ponto_fim["X"])
        y1 = float(ponto_fim["Y"])
        z1 = float(ponto_fim["NovoZ"])

        p0 = QgsPointXY(x0, y0)
        p1 = QgsPointXY(x1, y1)

        dx = x1 - x0
        dy = y1 - y0

        comprimento_ref = math.hypot(dx, dy)

        if comprimento_ref <= 0:
            self.mostrar_mensagem(self.tr("O segmento de referência possui comprimento inválido."), "Erro")
            return None

        # Vetor unitário da linha de referência
        ux = dx / comprimento_ref
        uy = dy / comprimento_ref

        # Inclinação longitudinal existente na dobradiça.
        # Esta inclinação NÃO é alterada.

        inclinacao_longitudinal = (z1 - z0) / comprimento_ref

        # Obtém o polígono ativo.
        polygon_layer = QgsProject.instance().mapLayer(self.comboBoxPoligono.currentData())

        if (not polygon_layer
            or not isinstance(polygon_layer, QgsVectorLayer)):
            self.mostrar_mensagem(self.tr("Camada de polígono inválida ou não encontrada." ), "Erro")
            return None

        feature_poligono = (self._get_active_polygon_feature(polygon_layer))

        if (feature_poligono is None
            or not feature_poligono.hasGeometry()
            or feature_poligono.geometry().isEmpty()):
            self.mostrar_mensagem(self.tr("Não foi possível obter a geometria do polígono."), "Erro")
            return None

        geom_poligono = QgsGeometry(feature_poligono.geometry())

        # Seu código já possui um método específico para obter a feição ativa do polígono selecionado. 
        # Usamos exatamente essa mesma lógica aqui.
        normal = self._obter_normal_interna_rampa(p0, p1, geom_poligono)

        if normal is None:
            self.mostrar_mensagem(self.tr("Não foi possível determinar o lado interno do segmento."), "Erro")
            return None

        nx, ny = normal

        # Inclinação transversal
        # Subir  = positiva para dentro
        # Descer = negativa para dentro
        inclinacao_transversal = (abs(float(inclinacao_pct)) / 100.0)

        if not subir:
            inclinacao_transversal *= -1.0

        resultados = []

        # Guarda também os Z calculados na ordem dos pontos, para posteriormente calcular as inclinações propostas dos segmentos.
        z_propostos = []

        # Calcula todos os vértices sobre o mesmo plano.
        for i, ponto in enumerate(self.points):
            x = float( ponto["X"])
            y = float(ponto["Y"])

            vx = x - x0
            vy = y - y0

            # Distância projetada ao longo da dobradiça
            distancia_longitudinal = (vx * ux + vy * uy)

            # Distância assinada para dentro do polígono
            distancia_transversal = (vx * nx + vy * ny)

            # Cota que a linha 3D de referência teria na projeção longitudinal deste ponto.
            z_linha = (z0 + distancia_longitudinal * inclinacao_longitudinal)

            novo_z = (z_linha + distancia_transversal * inclinacao_transversal)

            # Garante matematicamente e numericamente que os dois vértices da linha fixa NÃO mudem.

            if (i == indice_inicio
                or i == indice_fim):
                novo_z = float(ponto["NovoZ"])

                distancia_transversal = 0.0

            novo_z = round(novo_z, 3)
            z_propostos.append(novo_z)

            resultados.append({
                "indice": i,
                "ID": ponto["ID"],
                "Z_original": float(
                    ponto["Z"]),
                "NovoZ_atual": float(
                    ponto["NovoZ"]),
                "NovoZ_calculado": novo_z,
                "distancia_transversal": distancia_transversal,
                "desnivel_calculado": round(
                    novo_z - float(ponto["Z"]), 3)})

        # Calcula também como ficariam as inclinações de TODOS os segmentos após a aplicação da rampa.
        inclinacoes_segmentos = []

        for i in range(total_pontos):
            proximo = (i + 1) % total_pontos

            comprimento = float(self.lines[i].get("Comprimento", 0.0) or 0.0)

            if comprimento > 0:
                inclinacao = ((z_propostos[proximo] - z_propostos[i]) / comprimento) * 100.0

            else:
                inclinacao = 0.0

            inclinacoes_segmentos.append({
                "indice": i,
                "ID_inicio": self.points[i]["ID"],
                "ID_fim": self.points[proximo]["ID"],
                "inclinacao_pct": inclinacao})

        return {
            "indice_inicio": indice_inicio,
            "indice_fim": indice_fim,
            "normal_interna": (nx, ny),
            "inclinacao_longitudinal_pct": (
                inclinacao_longitudinal * 100.0),
            "inclinacao_transversal_pct": (
                inclinacao_transversal * 100.0),
            "pontos": resultados,
            "segmentos": inclinacoes_segmentos}

    def _buscar_segmentos_coincidentes_rampa(self, indice_segmento, tolerancia=None):
        """Procura segmentos de outros Platôs que coincidam com o segmento de referência."""
        if not getattr(self, "points", None):
            return []

        total_pontos = len(self.points)

        if indice_segmento < 0 or indice_segmento >= total_pontos:
            return []

        proximo = (indice_segmento + 1) % total_pontos
        p0 = QgsPointXY(float(self.points[indice_segmento]["X"]), float(self.points[indice_segmento]["Y"]))
        p1 = QgsPointXY(float(self.points[proximo]["X"]), float(self.points[proximo]["Y"]))

        project = QgsProject.instance()
        polygon_layer = project.mapLayer(self.comboBoxPoligono.currentData())

        if not polygon_layer or not isinstance(polygon_layer, QgsVectorLayer):
            return []

        feature_atual = self._get_active_polygon_feature(polygon_layer)

        if not feature_atual:
            return []

        poly_id_atual = self._get_poly_id_for_naming(polygon_layer, feature_atual)
        nome_vertices_atual = f"{polygon_layer.name()}_ID{poly_id_atual}_{self.tr('Vértices')}"
        sufixo_vertices = f"_{self.tr('Vértices')}"
        crs_destino = polygon_layer.crs()

        if tolerancia is None:
            tolerancia = 1e-7 if crs_destino.isGeographic() else 0.01

        def coincide(a, b):
            return math.hypot(a.x() - b.x(), a.y() - b.y()) <= tolerancia

        def correspondencia_geometrica(a, b):
            """Valida a borda vizinha e interpola NovoZ sobre as extremidades atuais.

            Exige que todo o segmento de referência esteja coberto pela borda
            candidata, evitando extrapolar cotas ou selecionar bordas paralelas
            próximas que não se sobreponham.
            """
            q0, q1 = a["ponto"], b["ponto"]
            dx, dy = q1.x() - q0.x(), q1.y() - q0.y()
            comprimento_vizinho = math.hypot(dx, dy)
            rx, ry = p1.x() - p0.x(), p1.y() - p0.y()
            comprimento_ref = math.hypot(rx, ry)
            if comprimento_vizinho <= 1e-9 or comprimento_ref <= 1e-9:
                return None

            ux, uy = dx / comprimento_vizinho, dy / comprimento_vizinho

            # Parâmetro longitudinal e afastamento transversal.
            def projetar(p):
                vx, vy = p.x() - q0.x(), p.y() - q0.y()
                return vx * ux + vy * uy, abs(vx * uy - vy * ux)

            t0, afastamento0 = projetar(p0)
            t1, afastamento1 = projetar(p1)

            # Impede aceitar linhas que apenas se cruzam.
            alinhamento = abs((rx * ux + ry * uy) / comprimento_ref)
            tolerancia_angular = min(0.02, tolerancia / comprimento_ref)

            if 1.0 - alinhamento > tolerancia_angular:
                return None

            if max(afastamento0, afastamento1) > tolerancia:
                return None

            if min(t0, t1) < -tolerancia or max(t0, t1) > comprimento_vizinho + tolerancia:
                return None

            # Limita a projeção à extensão do segmento vizinho.
            t0 = min(comprimento_vizinho, max(0.0, t0))
            t1 = min(comprimento_vizinho, max(0.0, t1))

            if abs(t1 - t0) < comprimento_ref - 2.0 * tolerancia:
                return None

            # Interpola NovoZ conforme a posição de cada extremidade.
            z_a, z_b = a["NovoZ"], b["NovoZ"]
            z0 = z_a + (z_b - z_a) * (t0 / comprimento_vizinho)
            z1 = z_a + (z_b - z_a) * (t1 / comprimento_vizinho)

            invertido = t1 < t0

            return z0, z1, invertido, max(afastamento0, afastamento1)

        def chave_id(feature):
            try:
                return (0, float(feature["ID"]))
            except (TypeError, ValueError, KeyError):
                return (1, feature.id())

        candidatos = []

        for layer in project.mapLayers().values():
            if not isinstance(layer, QgsVectorLayer) or not layer.isValid():
                continue

            if layer.geometryType() != Qgis.GeometryType.Point:
                continue

            if layer.name() == nome_vertices_atual or not layer.name().endswith(sufixo_vertices):
                continue

            campos = set(layer.fields().names())

            if not {"ID", "X", "Y", "NovoZ"}.issubset(campos):
                continue

            features = list(layer.getFeatures())

            if len(features) < 3:
                continue

            features.sort(key=chave_id)

            transform = None
            transform_valido = True

            if layer.crs() != crs_destino:
                try:
                    transform = QgsCoordinateTransform(layer.crs(), crs_destino, project)

                except Exception as e:
                    transform_valido = False

                    QgsMessageLog.logMessage(self.tr("Não foi possível criar a transformação de SRC para a camada '{layer}': {error}").format(layer=layer.name(), error=str(e)), "Tempo Salvo Tools", Qgis.MessageLevel.Warning)

            if not transform_valido:
                continue

            pontos = []

            for feature in features:
                geom = feature.geometry()

                if not geom or geom.isEmpty() or geom.type() != Qgis.GeometryType.Point:
                    continue

                pt = QgsPointXY(geom.asPoint())
                ponto_transformado = True

                if transform is not None:
                    try:
                        pt = transform.transform(pt)

                    except Exception as e:
                        ponto_transformado = False

                        QgsMessageLog.logMessage(self.tr("Não foi possível transformar o ponto da feição {id}: {error}").format(id=feature.id(), error=str(e)), "Tempo Salvo Tools", Qgis.MessageLevel.Warning)

                if not ponto_transformado:
                    continue

                try:
                    novo_z = float(feature["NovoZ"])

                    if not math.isfinite(novo_z):
                        continue
                except (TypeError, ValueError):
                    continue

                pontos.append({
                    "feature": feature,
                    "ponto": pt,
                    "id": feature["ID"],
                    "NovoZ": novo_z})

            if len(pontos) < 3:
                continue

            for i in range(len(pontos)):
                j = (i + 1) % len(pontos)
                a = pontos[i]
                b = pontos[j]

                direto = coincide(p0, a["ponto"]) and coincide(p1, b["ponto"])
                invertido = coincide(p0, b["ponto"]) and coincide(p1, a["ponto"])

                # Prioriza a correspondência direta entre extremidades.
                if direto:
                    id_inicio, id_fim = a["id"], b["id"]
                    z_inicio, z_fim = a["NovoZ"], b["NovoZ"]

                    afastamento = max(math.hypot(
                            p0.x() - a["ponto"].x(),
                            p0.y() - a["ponto"].y()),
                        math.hypot(
                            p1.x() - b["ponto"].x(),
                            p1.y() - b["ponto"].y()))

                elif invertido:
                    id_inicio, id_fim = b["id"], a["id"]
                    z_inicio, z_fim = b["NovoZ"], a["NovoZ"]

                    afastamento = max(math.hypot(
                            p0.x() - b["ponto"].x(),
                            p0.y() - b["ponto"].y()),
                        math.hypot(
                            p1.x() - a["ponto"].x(),
                            p1.y() - a["ponto"].y()))

                else:
                    # Verifica coincidência por proximidade e sobreposição.
                    correspondencia = correspondencia_geometrica(a, b)

                    if correspondencia is None:
                        continue

                    z_inicio, z_fim, invertido, afastamento = correspondencia

                    if invertido:
                        id_inicio, id_fim = b["id"], a["id"]
                    else:
                        id_inicio, id_fim = a["id"], b["id"]

                nome_base = layer.name()[:-len(sufixo_vertices)]

                texto = self.tr("{layer} | ID {id_inicio} → ID {id_fim} | {z_inicio:.3f} → {z_fim:.3f} m").format(
                    layer=nome_base,
                    id_inicio=id_inicio,
                    id_fim=id_fim,
                    z_inicio=z_inicio,
                    z_fim=z_fim)

                candidatos.append({
                    "layer_id": layer.id(),
                    "layer_name": layer.name(),
                    "nome_base": nome_base,
                    "id_inicio": id_inicio,
                    "id_fim": id_fim,
                    "novo_z_inicio": z_inicio,
                    "novo_z_fim": z_fim,
                    "invertido": invertido,
                    "afastamento": afastamento,
                    "texto": texto})

        candidatos.sort(key=lambda item: self._chave_ordenacao_natural(item["texto"]))
        return candidatos

    def abrir_ajuda_uso(self):
        """Abre uma janela com orientações de uso do módulo de geração de Platô."""

        # Se a janela já estiver aberta, apenas traz para frente.
        dialog_existente = getattr(self, "_dialogo_ajuda_uso", None)

        if dialog_existente is not None and dialog_existente.isVisible():
            dialog_existente.raise_()
            dialog_existente.activateWindow()
            return

        dialog = QDialog(self)
        self._dialogo_ajuda_uso = dialog

        dialog.setWindowTitle(self.tr("Como usar - Gerar Platô sobre o MDT"))
        dialog.setWindowModality(Qt.WindowModality.NonModal)
        dialog.resize(760, 680)
        dialog.setMinimumSize(620, 500)

        layout = QVBoxLayout(dialog)
        layout.setContentsMargins(10, 10, 10, 10)
        layout.setSpacing(8)

        texto = QTextBrowser(dialog)
        texto.setOpenExternalLinks(True)


        partes = [
            f"<h2>{self.tr('Gerar Platô sobre o MDT')}</h2>",

            f"<p>{self.tr('Esta ferramenta permite projetar superfícies de platôs a partir de um Modelo Digital de Terreno (MDT) e de uma geometria poligonal. O módulo integra o controle de cotas, inclinações, rampas, estaqueamentos, taludes, triangulação TIN e geração opcional de um novo MDT raster.')}</p>",

            f"<h3>{self.tr('Como funciona')}</h3>",

            f"<p>{self.tr('O polígono define o limite inicial do platô. Seus vértices recebem as elevações do terreno no campo Z e as cotas de projeto no campo NovoZ. Essas informações são utilizadas para calcular inclinações, gerar pontos intermediários, construir taludes e formar uma superfície tridimensional por triangulação.')}</p>",

            f"<hr><h3>{self.tr('Etapas de utilização')}</h3>",

            "<ol>",

            f"<li><b>{self.tr('Selecionar o MDT e o polígono')}</b><br>"
            f"{self.tr('Selecione o raster que representa o terreno e a camada poligonal que delimita o platô. Quando houver várias feições, selecione no mapa apenas o polígono desejado.')}</li><br>",

            f"<li><b>{self.tr('Criar os vértices')}</b><br>"
            f"{self.tr('Clique em Criar Vértices. Serão gerados pontos correspondentes aos vértices do polígono, com as coordenadas e as cotas extraídas do MDT. Inicialmente, NovoZ recebe o mesmo valor de Z.')}</li><br>",

            f"<li><b>{self.tr('Definir cotas e inclinações')}</b><br>"
            f"{self.tr('Utilize os campos NovoZ, Inclinação e Desnível para ajustar a superfície projetada. A edição desses valores permite estabelecer as diferenças altimétricas e os caimentos entre os vértices do platô.')}</li><br>",

            f"<li><b>{self.tr('Configurar a rampa, quando necessário')}</b><br>"
            f"{self.tr('Clique em Rampa, escolha o Segmento de referência e informe a inclinação transversal. Defina o sentido Subindo ou Descendo para determinar a variação das cotas em relação ao segmento escolhido. Confira os valores apresentados antes de aplicar.')}</li><br>",

            f"<li><b>{self.tr('Utilizar segmentos coincidentes')}</b><br>"
            f"{self.tr('Quando houver uma borda correspondente em outro platô já calculado, selecione o Segmento de referência adequado. O campo Segmento coincidente apresentará os trechos reconhecidos. Marque Usar cotas do segmento coincidente para aproveitar os valores NovoZ e favorecer a continuidade altimétrica entre os platôs.')}</li><br>",

            f"<li><b>{self.tr('Calcular os segmentos')}</b><br>"
            f"{self.tr('Após ajustar as cotas e inclinações, clique em Calcular. O plugin atualiza os dados correspondentes e gera os segmentos individuais utilizados nas etapas seguintes.')}</li><br>",

            f"<li><b>{self.tr('Calcular os estaqueamentos')}</b><br>"
            f"{self.tr('Selecione um segmento na lista Segmentos, defina a equidistância e clique em Calcular Estaqueamento. Os pontos intermediários são distribuídos ao longo do trecho, considerando as cotas do terreno e do projeto.')}</li><br>",

            f"<li><b>{self.tr('Calcular os taludes')}</b><br>"
            f"{self.tr('Selecione o estaqueamento desejado, indique o lado Esquerdo ou Direito e clique em Calcular Talude. O programa utiliza a geometria e as cotas de projeto para determinar o encontro do talude com o MDT.')}</li><br>",

            f"<li><b>{self.tr('Repetir nos segmentos necessários')}</b><br>"
            f"{self.tr('Repita o estaqueamento e o cálculo dos taludes para os trechos que compõem o projeto. A geração de taludes não é obrigatória em todos os lados, desde que a ausência represente corretamente a solução projetada.')}</li><br>",

            f"<li><b>{self.tr('Tratar Camadas e Gerar Malha TIN')}</b><br>"
            f"{self.tr('Após concluir os cálculos, clique no botão de junção das camadas. O programa reúne os elementos tratados e gera automaticamente a malha TIN da superfície projetada. Não é necessário habilitar uma opção separada para criar a malha.')}</li><br>",

            f"<li><b>{self.tr('Gerar o MDT raster, quando necessário')}</b><br>"
            f"{self.tr('Marque a opção Gerar MDT antes de executar a junção. Com essa opção habilitada, o programa gera a malha TIN e, em seguida, rasteriza sua superfície para produzir um MDT com valores de elevação. Se estiver desmarcada, a malha TIN será criada normalmente, sem rasterização.')}</li><br>",

            f"<li><b>{self.tr('Salvar ou abrir um projeto')}</b><br>"
            f"{self.tr('Utilize Salvar Projeto para armazenar as camadas contempladas pela rotina de salvamento em GeoPackage. O botão Abrir Projeto permite recuperar os dados anteriormente salvos. Confira separadamente o armazenamento dos produtos TIN e MDT raster, especialmente quando forem gerados como arquivos temporários.')}</li>",

            "</ol>",

            f"<hr><h3>{self.tr('Entendendo os principais valores')}</h3>",

            f"<p><b>Z:</b> {self.tr('elevação original extraída do MDT utilizado como referência.')}</p>",

            f"<p><b>NovoZ:</b> {self.tr('elevação definida para a superfície de projeto.')}</p>",

            f"<p><b>{self.tr('Inclinação')}:</b> {self.tr('variação percentual de elevação entre pontos consecutivos.')}</p>",

            f"<p><b>{self.tr('Desnível')}:</b> {self.tr('diferença entre a elevação projetada NovoZ e a elevação original Z.')}</p>",

            f"<p><b>{self.tr('Equidistância')}:</b> {self.tr('espaçamento utilizado para distribuir os pontos intermediários ao longo do segmento.')}</p>",

            f"<hr><h3>{self.tr('Continuidade entre platôs')}</h3>",

            f"<p>{self.tr('Em projetos com vários platôs adjacentes, como acessos, estradas, plataformas e áreas de terraplenagem, é possível utilizar segmentos coincidentes para manter a continuidade das cotas nas bordas compartilhadas.')}</p>",

            f"<p>{self.tr('Primeiro, selecione o segmento que representa a borda de referência do platô atual. Quando houver correspondência geométrica com outro trecho, o segmento coincidente poderá ser selecionado para aproveitar suas cotas de projeto.')}</p>",

            f"<p>{self.tr('O reconhecimento considera a geometria dos segmentos e as tolerâncias utilizadas pelo programa. Pequenos afastamentos podem ser admitidos, mas é importante conferir se as bordas representam efetivamente o mesmo limite de projeto.')}</p>",

            f"<hr><h3>{self.tr('Malha TIN e MDT raster')}</h3>",

            f"<p><b>{self.tr('Malha TIN:')}</b> "
            f"{self.tr('superfície tridimensional formada por triângulos conectados, construída com as coordenadas e as elevações dos elementos calculados. É gerada automaticamente durante a junção.')}</p>",

            f"<p><b>{self.tr('MDT raster:')}</b> "
            f"{self.tr('superfície matricial derivada da TIN. Os pixels recebem valores de elevação interpolados a partir dos triângulos. Sua geração é opcional e depende da opção Gerar MDT.')}</p>",

            f"<p>{self.tr('A malha TIN e o MDT raster representam produtos diferentes da mesma superfície projetada. O raster original permanece como referência do terreno existente.')}</p>",

            f"<hr><h3>{self.tr('Organização das camadas')}</h3>",

            f"<p>{self.tr('As camadas geradas são identificadas pelo nome do polígono de origem e pelo ID da feição, permitindo trabalhar com diferentes platôs no mesmo projeto.')}</p>",

            f"<p>{self.tr('As listas Segmentos, Estaqueamentos e Taludes organizam as camadas intermediárias. Ao selecionar um item, o QGIS enquadra a camada correspondente no mapa, facilitando sua localização e conferência.')}</p>",

            f"<hr><h3>{self.tr('Recomendações importantes')}</h3>",

            "<ul>",

            f"<li>{self.tr('Utilize um MDT adequado à escala e à precisão exigidas pelo projeto.')}</li>",

            f"<li>{self.tr('Confira o sistema de referência de coordenadas e as unidades utilizadas nos cálculos.')}</li>",

            f"<li>{self.tr('Verifique as cotas NovoZ e as inclinações antes de gerar os estaqueamentos.')}</li>",

            f"<li>{self.tr('Confirme o lado correto de cada talude antes de executar o cálculo.')}</li>",

            f"<li>{self.tr('Ao utilizar segmentos coincidentes, confira a correspondência geométrica e altimétrica entre as bordas.')}</li>",

            f"<li>{self.tr('Inspecione a malha TIN quanto à presença de falhas, sobreposições ou descontinuidades.')}</li>",

            f"<li>{self.tr('Ao gerar o MDT raster, confira a resolução espacial e a extensão da superfície produzida.')}</li>",

            f"<li>{self.tr('Salve os resultados importantes e exporte os produtos temporários quando necessário.')}</li>",

            "</ul>",

            f"<hr><h3>{self.tr('Resumo do processamento')}</h3>",

            f"<p><b>{self.tr('Fluxo principal:')}</b><br>"
            f"{self.tr('MDT + Polígono → Vértices → NovoZ / Rampa → Segmentos → Estaqueamentos → Taludes → Juntar → TIN.')}</p>",

            f"<p><b>{self.tr('Com Gerar MDT habilitado:')}</b><br>"
            f"{self.tr('MDT + Polígono → Vértices → NovoZ / Rampa → Segmentos → Estaqueamentos → Taludes → Juntar → TIN → MDT raster.')}</p>"
        ]

        texto.setHtml("".join(partes))
        layout.addWidget(texto, 1)

        layout_botoes = QHBoxLayout()
        layout_botoes.addStretch()

        botao_fechar = QPushButton(self.tr("Fechar"))
        botao_fechar.setMinimumWidth(100)
        botao_fechar.clicked.connect(dialog.close)

        layout_botoes.addWidget(botao_fechar)
        layout.addLayout(layout_botoes)

        dialog.show()
        dialog.raise_()
        dialog.activateWindow()

    def abrir_dialogo_rampa(self):
        """Configura a rampa e permite herdar as cotas de um segmento coincidente."""
        if (not getattr(self, "points", None)
            or not getattr(self, "lines", None)
            or not getattr(self, "scroll_widgets", None)):
            self.mostrar_mensagem(self.tr("Crie os vértices antes de configurar a rampa."), "Erro")
            return

        total_pontos = len(self.points)
        total_segmentos = min(len(self.lines), total_pontos)

        if total_segmentos < 1:
            self.mostrar_mensagem(self.tr("Nenhum segmento disponível para configurar a rampa."), "Erro")
            return

        dialog = QDialog(self)
        dialog.setWindowTitle(self.tr("Configurar Rampa"))
        dialog.setModal(True)
        dialog.setMinimumWidth(480)

        layout_principal = QVBoxLayout(dialog)

        frame_config = QFrame(dialog)
        frame_config.setFrameShape(QFrame.Shape.Box)
        frame_config.setFrameShadow(QFrame.Shadow.Raised)

        layout_config = QVBoxLayout(frame_config)
        layout_config.setContentsMargins(10, 10, 10, 10)
        layout_config.setSpacing(7)
        layout_principal.addWidget(frame_config)

        # Segmento de referência
        layout_segmento = QHBoxLayout()
        label_segmento = QLabel(self.tr("Segmento de referência:"))
        combo_segmento = QComboBox()

        for i in range(total_segmentos):
            proximo = (i + 1) % total_pontos
            id_inicio = self.points[i].get("ID", i + 1)
            id_fim = self.points[proximo].get("ID", proximo + 1)
            combo_segmento.addItem(self.tr("ID {id_inicio} → ID {id_fim}").format(id_inicio=id_inicio, id_fim=id_fim), i)

        layout_segmento.addWidget(label_segmento)
        layout_segmento.addWidget(combo_segmento, 1)
        layout_config.addLayout(layout_segmento)

        # Segmentos coincidentes
        layout_coincidente = QHBoxLayout()
        label_coincidente = QLabel(self.tr("Segmento coincidente:"))
        combo_coincidente = QComboBox()
        layout_coincidente.addWidget(label_coincidente)
        layout_coincidente.addWidget(combo_coincidente, 1)
        layout_config.addLayout(layout_coincidente)

        check_usar_coincidente = QCheckBox(self.tr("Usar cotas do segmento coincidente"))
        check_usar_coincidente.setEnabled(False)
        layout_config.addWidget(check_usar_coincidente)

        # Informações do segmento
        label_novoz_inicial = QLabel()
        label_novoz_final = QLabel()
        label_inclinacao_atual = QLabel()
        label_comprimento = QLabel()

        layout_config.addWidget(label_novoz_inicial)
        layout_config.addWidget(label_novoz_final)
        layout_config.addWidget(label_inclinacao_atual)
        layout_config.addWidget(label_comprimento)

        # Inclinação transversal
        layout_inclinacao = QHBoxLayout()
        label_inclinacao = QLabel(self.tr("Inclinação transversal atual:"))
        spin_inclinacao = QDoubleSpinBox()
        spin_inclinacao.setDecimals(3)
        spin_inclinacao.setRange(0.0, 100.0)
        spin_inclinacao.setSingleStep(0.1)
        spin_inclinacao.setSuffix(" %")

        layout_inclinacao.addWidget(label_inclinacao)
        layout_inclinacao.addWidget(spin_inclinacao)
        layout_config.addLayout(layout_inclinacao)

        # Sentido
        layout_sentido = QHBoxLayout()
        label_sentido = QLabel(self.tr("Sentido:"))
        radio_subir = QRadioButton(self.tr("Subindo"))
        radio_descer = QRadioButton(self.tr("Descendo"))

        radio_subir.setChecked(True)

        layout_sentido.addWidget(label_sentido)
        layout_sentido.addWidget(radio_subir)
        layout_sentido.addWidget(radio_descer)
        layout_sentido.addStretch()
        layout_config.addLayout(layout_sentido)

        candidatos_atuais = []

        def candidato_selecionado():
            if not check_usar_coincidente.isChecked() or not candidatos_atuais:
                return None

            indice_combo = combo_coincidente.currentData()

            if indice_combo is None:
                return None

            try:
                return candidatos_atuais[int(indice_combo)]
            except (TypeError, ValueError, IndexError):
                return None

        def cotas_referencia(indice):
            proximo = (indice + 1) % total_pontos
            z_inicio = float(self.points[indice]["NovoZ"])
            z_fim = float(self.points[proximo]["NovoZ"])
            candidato = candidato_selecionado()

            if candidato:
                z_inicio = float(candidato["novo_z_inicio"])
                z_fim = float(candidato["novo_z_fim"])

            return z_inicio, z_fim

        def inclinacao_transversal_atual(indice, z0_ref, z1_ref):
            proximo = (indice + 1) % total_pontos
            p0 = self.points[indice]
            p1 = self.points[proximo]

            x0, y0 = float(p0["X"]), float(p0["Y"])
            x1, y1 = float(p1["X"]), float(p1["Y"])
            dx = x1 - x0
            dy = y1 - y0
            comprimento = math.hypot(dx, dy)

            if comprimento <= 1e-12:
                return 0.0

            ux = dx / comprimento
            uy = dy / comprimento
            inclinacao_longitudinal = (z1_ref - z0_ref) / comprimento

            polygon_layer = QgsProject.instance().mapLayer(self.comboBoxPoligono.currentData())

            if not polygon_layer or not isinstance(polygon_layer, QgsVectorLayer):
                return 0.0

            feature_poligono = self._get_active_polygon_feature(polygon_layer)

            if not feature_poligono or not feature_poligono.hasGeometry():
                return 0.0

            normal = self._obter_normal_interna_rampa(
                QgsPointXY(x0, y0),
                QgsPointXY(x1, y1),
                QgsGeometry(feature_poligono.geometry()))

            if normal is None:
                return 0.0

            nx, ny = normal
            numerador = 0.0
            denominador = 0.0

            for i, ponto in enumerate(self.points):
                if i in (indice, proximo):
                    continue

                x = float(ponto["X"])
                y = float(ponto["Y"])
                z = float(ponto["NovoZ"])

                vx = x - x0
                vy = y - y0
                distancia_longitudinal = vx * ux + vy * uy
                distancia_transversal = vx * nx + vy * ny

                if abs(distancia_transversal) <= 1e-9:
                    continue

                z_linha = z0_ref + distancia_longitudinal * inclinacao_longitudinal
                diferenca_z = z - z_linha

                numerador += distancia_transversal * diferenca_z
                denominador += distancia_transversal * distancia_transversal

            if denominador <= 1e-12:
                return 0.0

            return (numerador / denominador) * 100.0

        def atualizar_dados_visuais():
            indice = combo_segmento.currentData()

            if indice is None:
                return

            indice = int(indice)
            proximo = (indice + 1) % total_pontos
            novo_z_inicial, novo_z_final = cotas_referencia(indice)
            comprimento = float(self.lines[indice].get("Comprimento", 0.0) or 0.0)

            if comprimento > 0:
                inclinacao_pct = ((novo_z_final - novo_z_inicial) / comprimento) * 100.0
            else:
                inclinacao_pct = 0.0

            label_novoz_inicial.setText(
                self.tr("NovoZ inicial: {value:.3f} m").format(value=novo_z_inicial))

            label_novoz_final.setText(
                self.tr("NovoZ final: {value:.3f} m").format(value=novo_z_final))

            label_inclinacao_atual.setText(
                self.tr("Inclinação atual do segmento: {value:.3f} %").format(value=inclinacao_pct))

            label_comprimento.setText(
                self.tr("Comprimento: {value:.3f} m").format(value=comprimento))

            transversal_pct = inclinacao_transversal_atual(
                indice,
                novo_z_inicial,
                novo_z_final)

            spin_inclinacao.blockSignals(True)
            spin_inclinacao.setValue(abs(transversal_pct))
            spin_inclinacao.blockSignals(False)

            if transversal_pct < -1e-9:
                radio_descer.setChecked(True)
            else:
                radio_subir.setChecked(True)

        def atualizar_segmentos_coincidentes():
            nonlocal candidatos_atuais

            check_usar_coincidente.blockSignals(True)
            check_usar_coincidente.setChecked(False)
            check_usar_coincidente.blockSignals(False)

            combo_coincidente.blockSignals(True)
            combo_coincidente.clear()

            indice = combo_segmento.currentData()

            if indice is None:
                candidatos_atuais = []
            else:
                candidatos_atuais = self._buscar_segmentos_coincidentes_rampa(int(indice))

            if candidatos_atuais:
                for i, candidato in enumerate(candidatos_atuais):
                    combo_coincidente.addItem(candidato["texto"], i)

                combo_coincidente.setEnabled(True)
                check_usar_coincidente.setEnabled(True)
            else:
                combo_coincidente.addItem(self.tr("Nenhum segmento coincidente encontrado"))
                combo_coincidente.setEnabled(False)
                check_usar_coincidente.setEnabled(False)

            combo_coincidente.blockSignals(False)
            atualizar_dados_visuais()

        def on_coincidente_alterado(_index):
            if check_usar_coincidente.isChecked():
                atualizar_dados_visuais()

        def on_usar_coincidente_alterado(_checked):
            atualizar_dados_visuais()

        combo_segmento.currentIndexChanged.connect(
            lambda _index: atualizar_segmentos_coincidentes())

        combo_coincidente.currentIndexChanged.connect(
            on_coincidente_alterado)

        check_usar_coincidente.toggled.connect(
            on_usar_coincidente_alterado)

        atualizar_segmentos_coincidentes()

        # Botões
        layout_botoes = QHBoxLayout()
        layout_botoes.setContentsMargins(0, 0, 0, 0)
        layout_botoes.setSpacing(6)

        botao_aplicar = QPushButton(self.tr("Aplicar"))
        botao_cancelar = QPushButton(self.tr("Cancelar"))
        botao_aplicar.setMinimumHeight(30)
        botao_cancelar.setMinimumHeight(30)

        layout_botoes.addWidget(botao_aplicar, 1)
        layout_botoes.addWidget(botao_cancelar, 1)
        layout_principal.addLayout(layout_botoes)

        botao_aplicar.clicked.connect(dialog.accept)
        botao_cancelar.clicked.connect(dialog.reject)

        if dialog.exec() != QDialog.DialogCode.Accepted:
            return

        indice = int(combo_segmento.currentData())
        proximo = (indice + 1) % total_pontos
        candidato = candidato_selecionado()

        z_inicio_anterior = float(self.points[indice]["NovoZ"])
        z_fim_anterior = float(self.points[proximo]["NovoZ"])

        # Quando solicitado, a borda coincidente passa a ser a nova linha 3D fixa.
        if candidato:
            self.points[indice]["NovoZ"] = float(candidato["novo_z_inicio"])
            self.points[proximo]["NovoZ"] = float(candidato["novo_z_fim"])

        configuracao = {
            "indice_segmento": indice,
            "id_inicio": self.points[indice]["ID"],
            "id_fim": self.points[proximo]["ID"],
            "inclinacao_transversal": spin_inclinacao.value(),
            "sentido": "subir" if radio_subir.isChecked() else "descer",
            "usar_segmento_coincidente": bool(candidato),
            "segmento_coincidente": candidato["texto"] if candidato else None}

        resultado = self._calcular_rampa_teorica(
            indice_segmento=indice,
            inclinacao_pct=spin_inclinacao.value(),
            subir=radio_subir.isChecked())

        if resultado is None:
            self.points[indice]["NovoZ"] = z_inicio_anterior
            self.points[proximo]["NovoZ"] = z_fim_anterior
            return

        self._rampa_config_teste = configuracao
        self._rampa_resultado_teste = resultado

        # Atualiza também os dois vértices fixos caso tenham vindo do trecho anterior.
        if candidato:
            for idx in (indice, proximo):
                le_novoz = self.scroll_widgets[idx]["line_edit_novoz"]
                le_novoz.blockSignals(True)
                le_novoz.setText(f"{float(self.points[idx]['NovoZ']):.3f}")
                le_novoz.blockSignals(False)

        # Atualiza os demais vértices calculados pela rampa.
        for item in resultado["pontos"]:
            idx = item["indice"]

            if idx in (resultado["indice_inicio"], resultado["indice_fim"]):
                continue

            novo_z = item["NovoZ_calculado"]
            self.points[idx]["NovoZ"] = novo_z

            le_novoz = self.scroll_widgets[idx]["line_edit_novoz"]
            le_novoz.blockSignals(True)
            le_novoz.setText(f"{novo_z:.3f}")
            le_novoz.blockSignals(False)

        self.recalculate_inclination_and_desnivel()

        if candidato:
            self.mostrar_mensagem(self.tr("Rampa aplicada usando as cotas do segmento coincidente."), "Sucesso")
        else:
            self.mostrar_mensagem(self.tr("Rampa aplicada aos valores de NovoZ."), "Sucesso")

    def connect_selection_signal(self):
        """Conecta o sinal selectionChanged para detectar mudanças na seleção de feições e controlar o botão."""
        selected_polygon_id = self.comboBoxPoligono.currentData()
        selected_layer = QgsProject.instance().mapLayer(selected_polygon_id)

        if selected_layer and isinstance(selected_layer, QgsVectorLayer):
            # Conexão de seleção é gerenciada por _ensure_polygon_signals_connected()
            self._ensure_polygon_signals_connected(selected_layer)

    def on_selection_changed(self):
        """Função chamada quando a seleção de feições é alterada. Atualiza o polígono e controla o estado do botão."""
        self.display_polygon()  # Atualiza a exibição do polígono
        selected_polygon_id = self.comboBoxPoligono.currentData()
        selected_layer = QgsProject.instance().mapLayer(selected_polygon_id)
        
        # Verifica se há feições selecionadas
        if selected_layer and selected_layer.selectedFeatureCount() > 0:
            self.pushButtonVertices.setEnabled(True)  # Ativa o botão
        else:
            self.pushButtonVertices.setEnabled(False)  # Desativa o botão

        self.update_pushButtonSalvar_state()

    def open_excel_with_attributes(self, item):
        """
        Abre um arquivo Excel com as informações da tabela de atributos da camada selecionada.
        """
        if not item or not item.text():
            self.mostrar_mensagem(self.tr("Nenhuma camada selecionada."), "Erro")
            return

        # Obtém o nome da camada a partir do texto do item selecionado
        layer_name = item.text()
        layer = QgsProject.instance().mapLayersByName(layer_name)

        if not layer:
            self.mostrar_mensagem(self.tr("Camada '{layer_name}' não encontrada.").format(layer_name=layer_name), "Erro")
            return

        layer = layer[0]

        if not isinstance(layer, QgsVectorLayer):
            self.mostrar_mensagem(self.tr("'{layer_name}' não é uma camada de vetor.").format(layer_name=layer_name), "Erro")
            return

        # Extrai os atributos da camada
        fields = [field.name() for field in layer.fields()]
        features = [feat for feat in layer.getFeatures()]

        # Verifica se há feições na camada
        if not features:
            self.mostrar_mensagem(self.tr("A camada '{layer_name}' não contém feições.").format(layer_name=layer_name), "Erro")
            return

        # Cria uma lista para armazenar os dados
        dados_tabela = []

        # Percorre todas as feições e campos para extrair os dados
        for feature in features:
            linha_dados = []
            for field_name in fields:
                valor_celula = feature[field_name]
                # Tenta converter para número se possível
                try:
                    valor_celula = float(valor_celula)
                except (ValueError, TypeError):
                    pass  # nosec B110 | Mantém o valor como string se não for um número
                linha_dados.append(valor_celula)
            dados_tabela.append(linha_dados)

        # Cria um DataFrame a partir dos dados
        df = pd.DataFrame(dados_tabela, columns=fields)

        # Cria um arquivo temporário para o Excel
        temp_fd, fileName = tempfile.mkstemp(suffix=".xlsx")
        os.close(temp_fd)  # Fecha o arquivo temporário para evitar conflito de acesso

        try:
            # Salva o DataFrame no arquivo Excel
            df.to_excel(fileName, index=False)

            # Adiciona bordas a todas as células no Excel
            self.add_borders_to_excel(fileName)

            # Abre o arquivo temporário no aplicativo padrão do sistema.
            abriu = QDesktopServices.openUrl(
                QUrl.fromLocalFile(os.path.abspath(os.fspath(fileName))))

            if abriu:
                self.mostrar_mensagem( self.tr("A tabela foi exportada e aberta no Excel temporariamente."), "Sucesso")
            else:
                self.mostrar_mensagem(self.tr("A tabela foi exportada, mas não foi possível abrir o arquivo automaticamente."), "Erro")

        except Exception as e:
            self.mostrar_mensagem(self.tr("Erro ao salvar o arquivo Excel: {error}").format(error=str(e)), "Erro")

    def add_borders_to_excel(self, file_path):
        """
        Adiciona bordas a todas as células do arquivo Excel especificado.
        """
        # Abre o workbook existente
        workbook = load_workbook(file_path)
        sheet = workbook.active

        # Define o estilo da borda
        thin_border = Border(
            left=Side(style='thin'),
            right=Side(style='thin'),
            top=Side(style='thin'),
            bottom=Side(style='thin'))

        # Aplica a borda a todas as células usadas na planilha
        for row in sheet.iter_rows(min_row=1, max_row=sheet.max_row, min_col=1, max_col=sheet.max_column):
            for cell in row:
                cell.border = thin_border

        # Ajusta a largura das colunas automaticamente
        for col in sheet.columns:
            max_length = 0
            column = col[0].column_letter  # Pega a letra da coluna
            for cell in col:
                cell_text = "" if cell.value is None else str(cell.value)
                max_length = max(max_length, len(cell_text))

            adjusted_width = (max_length + 2)
            sheet.column_dimensions[column].width = adjusted_width

        # Salva as alterações no arquivo
        workbook.save(file_path)
        workbook.close()

    def _intersect_talude_mdt(self, p0: QgsPointXY, novo_z0: float, perp_dx: float, perp_dy: float, direction_factor: int, raster_layer: QgsRasterLayer, max_dist: float = 250.0) -> tuple:
        """
        Caminha num plano 45° (1:1) a partir de p0 até encontrar o MDT.

        Retorna (ponto, z_mdt, desnível) ou (None, None, None)
        quando não houver nenhuma amostra válida do raster.
        """
        passo = max(raster_layer.rasterUnitsPerPixelX(), raster_layer.rasterUnitsPerPixelY(), 1.0)

        z0_terreno = self.get_z_value(p0.x(), p0.y())

        if z0_terreno is None:
            return None, None, None

        sinal = 1 if novo_z0 >= z0_terreno else -1
        dist = 0.0
        ultimo_resultado_valido = None

        while dist < max_dist:
            dist = min(dist + passo, max_dist)

            x = p0.x() + direction_factor * perp_dx * dist
            y = p0.y() + direction_factor * perp_dy * dist

            z_mdt = self.get_z_value(x, y)

            if z_mdt is None:
                break

            z_reta = novo_z0 - sinal * dist

            ultimo_resultado_valido = (
                QgsPointXY(x, y),
                float(z_mdt),
                round(novo_z0 - float(z_mdt), 3))

            cruzou = (
                (sinal > 0 and z_mdt >= z_reta)
                or
                (sinal < 0 and z_mdt <= z_reta))

            if cruzou:
                return ultimo_resultado_valido

        if ultimo_resultado_valido is not None:
            return ultimo_resultado_valido

        return None, None, None

    def _prepare_talude_input(self):
        """
        Faz todas as verificações/leituras necessárias.
        Retorna uma tupla com (layer, points, raster_layer, lado, direction_factor, talude_layer_name, crs)
        ou None caso algum erro ocorra (as mensagens já são exibidas).
        """
        selected_item = self.listWidgetEstacas.currentItem()
        if not selected_item:
            self.mostrar_mensagem(self.tr("Nenhuma camada de estacas selecionada."), "Erro")
            return None

        layer_name = selected_item.text()
        layer_list = QgsProject.instance().mapLayersByName(layer_name)
        if not layer_list:
            self.mostrar_mensagem(self.tr("Camada '{layer_name}' não encontrada.").format(layer_name=layer_name), "Erro")
            return None
        layer = layer_list[0]

        points = [f for f in layer.getFeatures()]
        if len(points) < 2:
            self.mostrar_mensagem(self.tr("A camada selecionada deve conter pelo menos dois pontos."), "Erro")
            return None

        selected_raster_id = self.comboBoxRaster.currentData()
        raster_layer = QgsProject.instance().mapLayer(selected_raster_id)
        if not raster_layer or not isinstance(raster_layer, QgsRasterLayer):
            self.mostrar_mensagem(self.tr("Camada raster inválida ou não selecionada."), "Erro")
            return None

        if self.radioButtonEsquerda.isChecked():
            lado, lado_nome, direction_factor = "esquerda", self.tr("Esquerda"), 1
        elif self.radioButtonDireita.isChecked():
            lado, lado_nome, direction_factor = "direita", self.tr("Direita"), -1
        else:
            self.mostrar_mensagem(self.tr("Selecione se o talude será criado à esquerda ou à direita."), "Erro")
            return None

        talude_layer_name = f"{layer_name}_{self.tr('Talude')}_{lado_nome}"
        crs = layer.crs()

        return layer, points, raster_layer, lado, direction_factor, talude_layer_name, crs

    def calculate_talude(self):
        """
        Calcula e gera as camadas de talude com base nas estacas selecionadas,
        criando novas camadas e aplicando simbologia específica.
        """
        # Guarda a linha atual antes que a substituição da camada
        # dispare atualizações automáticas nos listWidgets.
        current_row = self.listWidgetEstacas.currentRow()

        dados = self._prepare_talude_input()

        if not dados:
            return  # já houve mensagem de erro

        (layer, points, raster_layer,
         lado, direction_factor,
         talude_layer_name, crs) = dados

        self._create_talude_layer(layer, points, raster_layer, lado, direction_factor, talude_layer_name, crs)

        # Restaura a sequência somente depois de concluir a criação.
        self.update_list_widget_estaqueamentos()
        self._selecionar_proximo_item(self.listWidgetEstacas, current_row)

    def _create_talude_layer(self, layer, points, raster_layer, lado, direction_factor, talude_layer_name, crs):
        """
        1) Remove qualquer camada antiga de talude com o mesmo nome.
        2) Cria uma nova camada de pontos em memória para armazenar o talude.
        3) Define os campos: ID, X, Y, Z, NovoZ e Desnível.
        4) Obtém os vértices do polígono original selecionado (fecha o anel e remove duplicação).
        5) Calcula a normal bissetriz nos vértices correspondentes ao primeiro e último ponto de estacas:
           - Para cada vértice, obtém os vetores das duas arestas adjacentes.
           - Gera os normais “à esquerda” de cada aresta.
           - Faz a média vetorial e normaliza para obter o vetor unitário diagonal.
        6) Associa cada ponto de estaca ao seu vértice mais próximo do polígono original.
        7) No loop de criação de pontos de talude:
           a) Para i == 0 e i == n-1, usa a normal bissetriz calculada.
           b) Para demais i, calcula a perpendicular simples ao segmento de estacas.
           c) Chama _intersect_talude_mdt() para projetar o ponto a 45°.
           d) Cria a feição com geometria e atributos e adiciona ao provedor.
        8) Insere a camada dentro do grupo "Talude" na árvore de camadas.
        9) Exibe mensagem de sucesso e atualiza o listWidget de taludes.
        """
        # Cria a camada de pontos em memória
        talude_layer = QgsVectorLayer(f"Point?crs={crs.authid()}", talude_layer_name, "memory")

        # Adiciona atributos necessários
        pr = talude_layer.dataProvider()
        pr.addAttributes([
            QgsField("ID", QMetaType.Type.Int),
            QgsField("X", QMetaType.Type.Double),
            QgsField("Y", QMetaType.Type.Double),
            QgsField("Z", QMetaType.Type.Double),
            QgsField("NovoZ", QMetaType.Type.Double),
            QgsField("Desnível", QMetaType.Type.Double)])
        talude_layer.updateFields()
        self._aplicar_aliases_campos(talude_layer)

        # Extrai a feição ativa e, em MultiPolygon, escolhe a parte mais próxima
        # do primeiro ponto de estaqueamento.
        poly_layer = QgsProject.instance().mapLayer(self.comboBoxPoligono.currentData())

        if not poly_layer or not isinstance(poly_layer, QgsVectorLayer):
            self.mostrar_mensagem(self.tr("Camada de polígono inválida ou não encontrada."), "Erro")
            return

        feat_poly = self._get_active_polygon_feature(poly_layer)

        if feat_poly is None or not feat_poly.hasGeometry() or feat_poly.geometry().isEmpty():
            self.mostrar_mensagem(self.tr("Não foi possível obter a feição ativa do polígono."), "Erro")
            return

        geom = feat_poly.geometry()
        partes = geom.asMultiPolygon() if geom.isMultipart() else [geom.asPolygon()]
        aneis_externos = [list(parte[0]) for parte in partes if parte and parte[0]]

        if not aneis_externos:
            self.mostrar_mensagem(self.tr("Não foi possível obter os vértices do polígono ativo."), "Erro")
            return

        p0_referencia = points[0].geometry().asPoint()

        verts = min(aneis_externos,
            key=lambda anel: min(p0_referencia.distance(v) for v in anel))

        if verts and verts[0] == verts[-1]:
            verts = verts[:-1]

        if len(verts) < 3:
            self.mostrar_mensagem(self.tr("O polígono ativo não possui vértices suficientes para calcular o talude."), "Erro")
            return

        # Função interna para calcular normal bissetriz num vértice do polígono
        def _vertex_bisector_normal(idx):
            """Retorna o normal unitário bissetriz no vértice idx do polígono."""
            p_cur  = verts[idx]
            p_prev = verts[idx-1] if idx>0 else verts[-1]
            p_next = verts[(idx+1) % len(verts)]

            # vetores de aresta
            v1x, v1y = p_cur.x() - p_prev.x(), p_cur.y() - p_prev.y()
            v2x, v2y = p_next.x() - p_cur.x(), p_next.y() - p_cur.y()

            # normais “à esquerda”
            n1x, n1y = -v1y, v1x
            n2x, n2y = -v2y, v2x

            # normaliza
            l1 = math.hypot(n1x, n1y)
            if l1>0: n1x, n1y = n1x/l1, n1y/l1
            l2 = math.hypot(n2x, n2y)
            if l2>0: n2x, n2y = n2x/l2, n2y/l2

            # média e normalização final
            ax, ay = n1x + n2x, n1y + n2y
            la = math.hypot(ax, ay)
            if la>0:
                return ax/la, ay/la
            else:
                return n2x, n2y

        # Localiza qual vértice do polígono corresponde ao primeiro/último estaqueamento
        def _find_nearest_vertex(pt):
            """
            Retorna o índice e a distância do vértice mais próximo ao ponto informado.
            """
            dists = [pt.distance(v) for v in verts]
            return dists.index(min(dists))

        def _normal_segmento_extremidade(p_ini, p_fim):
            """Retorna a normal unitária à esquerda do segmento."""
            dx = p_fim.x() - p_ini.x()
            dy = p_fim.y() - p_ini.y()
            comp = math.hypot(dx, dy)

            if comp <= 1e-12:
                return None

            return (-dy / comp, dx / comp)

        # Nas extremidades usa somente a direção do segmento que possui talude.
        p0 = QgsPointXY(points[0].geometry().asPoint())
        p1 = QgsPointXY(points[1].geometry().asPoint())
        pN_1 = QgsPointXY(points[-2].geometry().asPoint())
        pN = QgsPointXY(points[-1].geometry().asPoint())

        perp_start = _normal_segmento_extremidade(p0, p1)
        perp_end = _normal_segmento_extremidade(pN_1, pN)

        if perp_start is None or perp_end is None:
            self.mostrar_mensagem(self.tr("Não foi possível calcular a direção das extremidades do talude."), "Erro")
            return

        # Loop de criação dos pontos de talude
        n = len(points)

        def _normal_bissetriz_estacas(idx):
            """
            Calcula a normal média entre o segmento anterior
            e o posterior.

            Em trechos retos, equivale à perpendicular normal.
            Em mudanças de direção, acompanha a bissetriz do ângulo.
            """
            p_anterior = QgsPointXY(points[idx - 1].geometry().asPoint())
            p_atual = QgsPointXY(points[idx].geometry().asPoint())
            p_proximo = QgsPointXY(points[idx + 1].geometry().asPoint())

            # Vetor do segmento anterior
            dx1 = p_atual.x() - p_anterior.x()
            dy1 = p_atual.y() - p_anterior.y()

            comp1 = math.hypot(dx1, dy1)

            # Vetor do segmento posterior
            dx2 = p_proximo.x() - p_atual.x()
            dy2 = p_proximo.y() - p_atual.y()

            comp2 = math.hypot(dx2, dy2)

            if (comp1 <= 0
                or comp2 <= 0):
                return None

            # Tangentes unitárias
            tx1 = dx1 / comp1
            ty1 = dy1 / comp1

            tx2 = dx2 / comp2
            ty2 = dy2 / comp2

            # Normais à esquerda dos dois segmentos
            nx1 = -ty1
            ny1 = tx1

            nx2 = -ty2
            ny2 = tx2

            # Média das duas normais
            nx = nx1 + nx2
            ny = ny1 + ny2

            comp_normal = math.hypot(nx, ny)

            # Caso extremamente fechado em que as normais
            # praticamente se anulam.
            if comp_normal <= 1e-12:
                return (nx2, ny2)

            return (nx / comp_normal, ny / comp_normal)

        for i in range(n):
            # Ponto e cota da estaca atual são necessários em todos os casos,
            # inclusive no primeiro e no último ponto.
            p1 = QgsPointXY(points[i].geometry().asPoint())

            try:
                z1 = float(points[i]["NovoZ"])
            except (TypeError, ValueError):
                self.mostrar_mensagem(self.tr("A estaca {id} não possui um valor válido no campo NovoZ.").format(id=i + 1), "Erro")
                return
            #
            if i == 0:
                perp_dx, perp_dy = perp_start

            elif i == n - 1:
                perp_dx, perp_dy = perp_end

            else:
                normal = _normal_bissetriz_estacas(i)

                if normal is None:
                    self.mostrar_mensagem(self.tr("Não foi possível calcular a direção do talude na estaca {id}.").format(id=i + 1), "Erro")
                    return

                perp_dx, perp_dy = normal

            # Opcional: log para conferir
            if i in (0, n-1):
                ang = math.degrees(math.atan2(perp_dy, perp_dx))

            # interseção 45°
            p_talude, z_mdt, desn_t = self._intersect_talude_mdt(p1, z1, perp_dx, perp_dy, direction_factor, raster_layer)

            if p_talude is None or z_mdt is None or desn_t is None:
                self.mostrar_mensagem(self.tr("Não foi possível obter uma interseção válida do talude com o MDT para a estaca {id}.").format(id=i + 1), "Erro")
                return

            # Cria e adiciona a feição
            feat = QgsFeature(talude_layer.fields())
            feat.setGeometry(QgsGeometry.fromPointXY(p_talude))
            feat.setAttributes([
                i+1,
                round(p_talude.x(), 3),
                round(p_talude.y(), 3),
                z_mdt,
                round(z1, 3),
                desn_t])
            pr.addFeature(feat)

        # Só substitui uma camada anterior após concluir todos os pontos do talude.
        for existing_layer in QgsProject.instance().mapLayersByName(talude_layer_name):
            QgsProject.instance().removeMapLayer(existing_layer.id())

        # Insere a camada no grupo "Taludes"
        root  = QgsProject.instance().layerTreeRoot()
        group = root.findGroup(self.tr("Taludes")) or root.addGroup(self.tr("Taludes"))
        QgsProject.instance().addMapLayer(talude_layer, False)
        group.insertLayer(0, talude_layer)

        self.mostrar_mensagem(self.tr("Camada '{talude_layer_name}' de talude criada com sucesso.").format(talude_layer_name=talude_layer_name), "Sucesso")

        self.update_list_widget_talude()

    def _escolher_crs_malha(self, crs_inicial):
        """Solicita uma única vez o SRC que será utilizado na geração das malhas."""
        if not crs_inicial or not crs_inicial.isValid():
            crs_inicial = QgsProject.instance().crs()

        dialog_crs = QgsProjectionSelectionDialog(self)
        dialog_crs.setWindowTitle(self.tr("Escolher projeção da malha"))
        dialog_crs.setCrs(crs_inicial)
        dialog_crs.setShowNoProjection(False)
        dialog_crs.setRequireValidSelection()

        if dialog_crs.exec() != QDialog.DialogCode.Accepted:
            return None

        output_crs = dialog_crs.crs()

        if not output_crs.isValid():
            self.mostrar_mensagem(self.tr("Nenhuma projeção válida foi selecionada para a malha."), "Erro")
            return None

        return output_crs

    def _create_mesh_from_points_layer(self, source_layer: QgsVectorLayer, mesh_name: str, output_crs=None):
        """
        Gera TIN a partir da camada de pontos usando o campo Cota.
        Se output_crs já for informado, não pergunta novamente a projeção.
        """
        try:
            if not source_layer or source_layer.geometryType() != Qgis.GeometryType.Point:
                self.mostrar_mensagem(self.tr("Camada inválida para gerar TIN (deve ser de pontos)."), "Erro")
                return False

            if output_crs is None:
                output_crs = self._escolher_crs_malha(source_layer.crs())

                if output_crs is None:
                    return False

            use_selected = getattr(self, "checkBoxSeleciona", None).isChecked() if hasattr(self, "checkBoxSeleciona") else False
            src_for_processing = source_layer

            if use_selected:
                if source_layer.selectedFeatureCount() == 0:
                    self.mostrar_mensagem(self.tr("Não há feições selecionadas para gerar a TIN."), "Erro")
                    return False

                tmp_sel = QgsVectorLayer(f"Point?crs={source_layer.crs().authid()}", "mesh_selected_points", "memory")
                tmp_sel_dp = tmp_sel.dataProvider()
                tmp_sel_dp.addAttributes(source_layer.fields())
                tmp_sel.updateFields()
                tmp_sel_dp.addFeatures(list(source_layer.getSelectedFeatures()))
                tmp_sel.updateExtents()
                src_for_processing = tmp_sel

            if "Cota" not in src_for_processing.fields().names():
                self.mostrar_mensagem(
                    self.tr("Nenhum ponto com o campo '{field_name}' definido para gerar TIN.").format(field_name="Cota"),
                    "Erro")
                return False

            tmp = QgsVectorLayer(f"Point?crs={src_for_processing.crs().authid()}", "mesh_points_nonnull", "memory")
            tmp_dp = tmp.dataProvider()
            tmp_dp.addAttributes(src_for_processing.fields())
            tmp.updateFields()

            feats_ok = [f for f in src_for_processing.getFeatures() if f["Cota"] is not None]

            if not feats_ok:
                self.mostrar_mensagem(self.tr("Nenhum ponto com 'Cota' definida para gerar TIN."), "Erro")
                return False

            tmp_dp.addFeatures(feats_ok)
            tmp.updateExtents()
            src_for_processing = tmp

            if src_for_processing.crs() != output_crs:
                reprojection_result = processing.run(
                    "native:reprojectlayer", {
                        "INPUT": src_for_processing,
                        "TARGET_CRS": output_crs,
                        "OUTPUT": "TEMPORARY_OUTPUT"})

                reprojected_layer = reprojection_result.get("OUTPUT")

                if not isinstance(reprojected_layer, QgsVectorLayer) or not reprojected_layer.isValid():
                    self.mostrar_mensagem(self.tr("Não foi possível reprojetar os pontos para o SRC selecionado."), "Erro")
                    return False

                src_for_processing = reprojected_layer

            idx_cota = src_for_processing.fields().indexFromName("Cota")

            added_tmp = False

            if QgsProject.instance().mapLayer(src_for_processing.id()) is None:
                QgsProject.instance().addMapLayer(src_for_processing, False)
                added_tmp = True

            try:
                source_data = [{
                    "source": src_for_processing.id(),
                    "type": 0,
                    "attributeIndex": idx_cota}]

                result = processing.run(
                    "native:tinmeshcreation", {
                        "SOURCE_DATA": source_data,
                        "MESH_FORMAT": 0,
                        "CRS_OUTPUT": output_crs,
                        "OUTPUT_MESH": "TEMPORARY_OUTPUT"})
            finally:
                if added_tmp:
                    QgsProject.instance().removeMapLayer(src_for_processing.id())

            mesh_path = result["OUTPUT_MESH"]
            mesh_layer = QgsMeshLayer(mesh_path, mesh_name, "mdal")

            if not mesh_layer.isValid():
                raise Exception(self.tr("Falha ao carregar a malha gerada."))

            mesh_layer.setCrs(output_crs)

            # Evita duplicar a TIN se o mesmo ID for processado novamente.
            for layer in QgsProject.instance().mapLayersByName(mesh_name):
                if isinstance(layer, QgsMeshLayer):
                    QgsProject.instance().removeMapLayer(layer.id())

            self._top_insert_layer(mesh_layer)
            return True

        except Exception as e:
            self.mostrar_mensagem(self.tr("Erro ao gerar a TIN: {error}").format(error=str(e)), "Erro")
            return False

class GraficoManager:
    def __init__(self, plato_manager):
        """
        Inicializa o GraficoManager com uma referência para a classe PlatoManager.

        Parameters:
        - plato_manager: A instância de PlatoManager que contém o método mostrar_mensagem.
        """
        self.plato_manager = plato_manager
        self.logo_path = None  # Inicialmente, não há logo armazenado

    def tr(self, message):
        return QCoreApplication.translate("GraficoManager", message)

    def find_layer(self, layer_name, layer_type):
        """
        Retorna a camada do projeto que corresponde ao nome e tipo especificados.
        """
        for layer in QgsProject.instance().mapLayers().values():
            if layer.name() == layer_name and isinstance(layer, layer_type):
                return layer
        return None

    def sample_raster_value(self, point, raster_layer):
        """Amostra o valor Z do raster baseado nas coordenadas do ponto."""
        identify_result = raster_layer.dataProvider().identify(QgsPointXY(point.x(), point.y()), Qgis.RasterIdentifyFormat.Value)
        
        if identify_result.isValid():
            results = identify_result.results()
            if results:
                band_key = list(results.keys())[0]
                z_value = results.get(band_key)  # Use get para evitar KeyError
                if z_value is not None:  # Verifica se o valor é válido
                    return round(float(z_value), 3)
        return None  # Retorna None se não houver valor válido

    def create_support_points_layer(self, estacas_layer, raster_layer):
        """
        Cria uma camada de pontos de apoio a partir das estacas fornecidas,
        atribuindo valores de elevação a partir do raster selecionado.
        """
        # Obter a resolução do pixel da camada raster
        raster_extent = raster_layer.extent()
        raster_width = raster_layer.width()
        raster_height = raster_layer.height()
        pixel_resolution_x = raster_extent.width() / raster_width
        pixel_resolution_y = raster_extent.height() / raster_height

        # Definir o espaçamento de suporte como a resolução do pixel
        support_spacing = min(pixel_resolution_x, pixel_resolution_y)

        # Obter o CRS da camada de estacas
        crs = estacas_layer.sourceCrs().authid()
        support_layer = QgsVectorLayer(f"Point?crs={crs}", "", "memory")  # Criar a camada sem nome

        prov = support_layer.dataProvider()

        # Adiciona os campos necessários, incluindo "Acumula_dist"
        prov.addAttributes([QgsField("ID", QMetaType.Type.Int), QgsField("Original_ID", QMetaType.Type.Int),
                            QgsField("X", QMetaType.Type.Double), QgsField("Y", QMetaType.Type.Double),
                            QgsField("Znovo", QMetaType.Type.Double), QgsField("Acumula_dist", QMetaType.Type.Double)])
        support_layer.updateFields()

        estacas_features = [feat for feat in estacas_layer.getFeatures()]
        estacas_points = [feat.geometry().asPoint() for feat in estacas_features]
        all_points = []
        support_point_id = 0
        last_coord = None
        acumula_dist = 0

        # Calcular o desnível para a extensão (1 metro além do desnível)
        first_desnivel = estacas_features[0]['Desnível']
        last_desnivel = estacas_features[-1]['Desnível']
        extend_by_start = min(abs(float(first_desnivel or 0.0)) + 3.0, 10.0)
        extend_by_end = min(abs(float(last_desnivel or 0.0)) + 3.0, 10.0)

        # Adicionar pontos extras antes do primeiro ponto de estacas
        first_length = estacas_points[0].distance(estacas_points[1])
        if first_length > 0:
            first_segment_dir = estacas_points[1] - estacas_points[0]
            for i in range(int(extend_by_start // support_spacing), 0, -1):
                extra_point = QgsPointXY(
                    estacas_points[0].x() - (first_segment_dir.x() * i * support_spacing) / first_length,
                    estacas_points[0].y() - (first_segment_dir.y() * i * support_spacing) / first_length)

                z_value = self.sample_raster_value(extra_point, raster_layer)
                if z_value is None:
                    # Interrompe a extensão se o valor de Z for None
                    break
                
                support_point_id += 1
                all_points.append((extra_point, -i, support_point_id))

        # Gerar os pontos de apoio ao longo dos segmentos
        for i, start_point in enumerate(estacas_points[:-1]):
            end_point = estacas_points[i + 1]
            segment_length = start_point.distance(end_point)
            if segment_length == 0:        #  ➜ pular segmento nulo
                continue

            num_intermediate_points = int(segment_length / support_spacing)

            for j in range(num_intermediate_points + 1):
                # aqui segment_length é seguro (>0)
                x = start_point.x() + (end_point.x() - start_point.x()) * (j * support_spacing) / segment_length
                y = start_point.y() + (end_point.y() - start_point.y()) * (j * support_spacing) / segment_length

                inter_point = QgsPointXY(x, y)
                support_point_id += 1
                all_points.append((inter_point, estacas_features[i]['ID'], support_point_id))

        # Adicionar pontos extras após o último ponto de estacas
        last_length = estacas_points[-1].distance(estacas_points[-2])
        if last_length > 0:
            last_segment_dir = estacas_points[-1] - estacas_points[-2]
            for i in range(0, int(extend_by_end // support_spacing) + 1):
                extra_point = QgsPointXY(
                    estacas_points[-1].x() + (last_segment_dir.x() * i * support_spacing) / last_length,
                    estacas_points[-1].y() + (last_segment_dir.y() * i * support_spacing) / last_length)

                z_value = self.sample_raster_value(extra_point, raster_layer)
                if z_value is None:
                    # Interrompe a extensão se o valor de Z for None
                    break

                support_point_id += 1
                all_points.append((extra_point, estacas_features[-1]['ID'], support_point_id))

        # Criar os recursos e adicionar à camada com a distância acumulada
        first_positive_id_encountered = False
        for point, original_id, support_point_id in all_points:
            current_coord = (point.x(), point.y())
            if not first_positive_id_encountered:
                if original_id >= 0:
                    acumula_dist = 0
                    first_positive_id_encountered = True
                else:
                    acumula_dist = -extend_by_start + (support_point_id - 1) * support_spacing
            else:
                if last_coord:
                    segment_distance = QgsPointXY(*last_coord).distance(QgsPointXY(*current_coord))
                    acumula_dist += segment_distance
            last_coord = current_coord

            # Atributos do recurso, incluindo acumulação de distância
            feat = QgsFeature()
            feat.setGeometry(QgsGeometry.fromPointXY(QgsPointXY(*current_coord)))
            feat.setAttributes([support_point_id, original_id, round(point.x(), 3), round(point.y(), 3), None, round(acumula_dist, 3)])
            prov.addFeature(feat)

         # Amostra os valores do MDT para os pontos de apoio e atualiza o campo "Znovo"
        support_layer.startEditing()
        z_value_previous = None

        for feature in support_layer.getFeatures():
            point = feature.geometry().asPoint()
            z_value = self.sample_raster_value(point, raster_layer)
            if z_value is None and z_value_previous is not None:
                z_value = z_value_previous
            if z_value is not None:
                z_value_previous = z_value
            feature['Znovo'] = round(z_value, 3) if z_value is not None else None
            support_layer.updateFeature(feature)

        support_layer.commitChanges()

        # Retorna a camada sem adicionar ao projeto
        return support_layer

    def find_slope_intersection(self, x, y, apoio_distances, apoio_elevations, angle_degrees):
        """
        Calcula a posição de interseção do talude com base nas coordenadas iniciais,
        distâncias e elevações dos pontos de apoio e ângulo do talude.
        """
        angle_radians = math.radians(angle_degrees)
        slope = math.tan(angle_radians)
        
        # Calcula o ponto final da linha de talude (apenas como referência se não houver interseção)
        x_end = x + math.cos(angle_radians)
        y_end = y + math.sin(angle_radians)

        # Encontrar a interseção com a linha "Znovo"
        for i in range(len(apoio_distances) - 1):
            x1, y1 = apoio_distances[i], apoio_elevations[i]
            x2, y2 = apoio_distances[i + 1], apoio_elevations[i + 1]

            if x1 == x2:  # Ignora segmentos verticais, pois não haverá interseção
                continue

            # Cálculo da inclinação e interceptação da linha entre os pontos de Znovo
            slope_znovo = (y2 - y1) / (x2 - x1)
            intercept_znovo = y1 - slope_znovo * x1

            # Linhas paralelas ou quase paralelas não possuem interseção estável.
            denominador = slope - slope_znovo

            if math.isclose(denominador, 0.0, rel_tol=1e-12, abs_tol=1e-12):
                continue

            intersect_x = (intercept_znovo - y + slope * x) / denominador
            intersect_y = slope * (intersect_x - x) + y

            # Verifica se a interseção está dentro do segmento de Znovo
            if min(x1, x2) <= intersect_x <= max(x1, x2) and min(y1, y2) <= intersect_y <= max(y1, y2):
                return intersect_x, intersect_y

        # Se não houver interseção, retorna o ponto final presumido
        return x_end, y_end

    def plot_layers(self, estacas_layer, pontos_apoio_layer, angle_degrees_ti, angle_degrees_tf):
        """
        Exibe um gráfico com as camadas de estacas e pontos de apoio e desenha os taludes com base nos ângulos fornecidos.
        
        Parameters:
        - estacas_layer: Camada de estacas.
        - pontos_apoio_layer: Camada de pontos de apoio.
        - angle_degrees_ti: Ângulo do talude inicial.
        - angle_degrees_tf: Ângulo do talude final.
        """
        # Coletar dados das camadas
        estacas_data = [(f['Acumula_dist'], f['NovoZ'], f['Z'], f['Desnível'], f.geometry().asPoint().x(), f.geometry().asPoint().y()) 
                        for f in estacas_layer.getFeatures()]
        pontos_apoio_data = [(f['Acumula_dist'], f['Znovo']) for f in pontos_apoio_layer.getFeatures()]

        # Ordenar os dados
        estacas_data.sort(key=lambda x: x[0])
        pontos_apoio_data.sort(key=lambda x: x[0])

        # Desempacotar dados
        estacas_distances, estacas_novoz, z_values, desnivels, x_coords, y_coords = zip(*estacas_data)
        apoio_distances, apoio_elevations = zip(*pontos_apoio_data)

        # Criar o gráfico principal
        fig, ax = plt.subplots(figsize=(15, 9))

        # Ajusta o título da figura com o nome da camada
        nome_camada = estacas_layer.name()
        fig.canvas.manager.set_window_title(f'{nome_camada}')

        fig.subplots_adjust(left=0.08, right=0.98, bottom=0.12, top=0.9)

        ax.set_xlabel(self.tr("Distância Acumulada (m)"))
        ax.set_ylabel(self.tr("Elevação (m)"))
        ax.set_title(self.tr("Perfil Longitudinal"))

        # Plotar a linha "NovoZ"
        ax.plot(estacas_distances, estacas_novoz, color='blue', linewidth=2, label=self.tr("Perfil do Platô"))

        # Plotar a linha "Znovo"
        ax.plot(apoio_distances, apoio_elevations, color='orange', linewidth=1.5, label=self.tr("Terreno"))

        # Pegar os pontos iniciais e finais da linha "NovoZ"
        start_x, start_y = estacas_distances[0], estacas_novoz[0]
        end_x, end_y = estacas_distances[-1], estacas_novoz[-1]

        # Elevações correspondentes em Znovo
        start_znovo = apoio_elevations[0]
        end_znovo = apoio_elevations[-1]

        # Ajustar o ângulo de inclinação para o talude de entrada (TI)
        if start_y > start_znovo:
            angle_degrees_ti = angle_degrees_ti
        else:
            angle_degrees_ti = 180 - angle_degrees_ti

        # Ajustar o ângulo de inclinação para o talude de saída (TF)
        if end_y > end_znovo:
            angle_degrees_tf = 180 - angle_degrees_tf
        else:
            angle_degrees_tf = angle_degrees_tf

        # Calcular e plotar a linha de talude para o ponto inicial (TI)
        talude_start_intersection = self.find_slope_intersection(start_x, start_y, apoio_distances, apoio_elevations, angle_degrees_ti)
        if talude_start_intersection:
            if estacas_novoz[0] > start_znovo:
                ti_color = 'blue'
            else:
                ti_color = 'red'
            ax.plot([start_x, talude_start_intersection[0]], [start_y, talude_start_intersection[1]], linestyle='--', linewidth=2.5, color=ti_color)

        # Calcular e plotar a linha de talude para o ponto final (TF)
        talude_end_intersection = self.find_slope_intersection(end_x, end_y, apoio_distances, apoio_elevations, angle_degrees_tf)
        if talude_end_intersection:
            if estacas_novoz[-1] > end_znovo:
                tf_color = 'blue'
            else:
                tf_color = 'red'
            ax.plot([end_x, talude_end_intersection[0]], [end_y, talude_end_intersection[1]], linestyle='--', linewidth=2.5, color=tf_color)

        # Adicionar linhas verticais nas extremidades da linha Talude
        if talude_start_intersection:
            ax.vlines(x=talude_start_intersection[0], ymin=0, ymax=talude_start_intersection[1], colors='grey', linestyles='dashed', linewidth=0.5)

        if talude_end_intersection:
            ax.vlines(x=talude_end_intersection[0], ymin=0, ymax=talude_end_intersection[1], colors='grey', linestyles='dashed', linewidth=0.5)

        # Criar os valores combinados de X para interpolação
        corte_adjusted_x = [talude_start_intersection[0]] + list(estacas_distances) + [talude_end_intersection[0]]
        corte_adjusted_y = [talude_start_intersection[1]] + list(estacas_novoz) + [talude_end_intersection[1]]

        # Preparar as listas estendidas de x e y para 'Znovo' e 'Corte Ajustado'
        x_combined = sorted(set(corte_adjusted_x + list(apoio_distances)))
        y_corte_interpolated = np.interp(x_combined, corte_adjusted_x, corte_adjusted_y)
        y_znovo_interpolated = np.interp(x_combined, apoio_distances, apoio_elevations)

        # Limitar o intervalo de x para o preenchimento
        x_fill_min = talude_start_intersection[0]
        x_fill_max = talude_end_intersection[0]

        # Ajustes nos limites do eixo Y
        y_min0 = min(apoio_elevations) - 2  # Valor mínimo da elevação para a linha de base com uma margem
        y_min1 = min(min(estacas_novoz), y_min0) - 3  # Valor mínimo com margem adicional
        y_max = max(max(estacas_novoz), max(apoio_elevations)) + 3  # Valor máximo com margem adicional
        ax.set_ylim(y_min1, y_max)

        # Plotar a linha "Znovo"
        # ax.plot(apoio_distances, apoio_elevations, color='orange', linewidth=1.5, label='Znovo (Terreno Natural)')

        # Preencher abaixo da linha "Terreno Natural" até a linha de base 'y_min0'
        ax.fill_between(apoio_distances, apoio_elevations, y_min0, color='lightgreen', alpha=0.3, hatch='***')

        # Filtrar os valores x e y para o intervalo de interesse
        x_fill = [x for x in x_combined if x_fill_min <= x <= x_fill_max]
        y_corte_fill = np.interp(x_fill, corte_adjusted_x, corte_adjusted_y)
        y_znovo_fill = np.interp(x_fill, apoio_distances, apoio_elevations)

        # Preenchimento vermelho abaixo de "Znovo" e acima de "Corte Ajustado"
        ax.fill_between(x_fill, y_corte_fill, y_znovo_fill, where=(y_corte_fill < y_znovo_fill), interpolate=True, color='red', alpha=0.5, hatch='///', label=self.tr("Área Cortada"))

        # Preenchimento azul acima de "Znovo" e abaixo de "Corte Ajustado"
        ax.fill_between(x_fill, y_znovo_fill, y_corte_fill, where=(y_corte_fill > y_znovo_fill), interpolate=True, color='blue', alpha=0.5, hatch='\\\\', label=self.tr("Área Aterrada"))

        # Adicionar a legenda para Talude Cortado e Aterrado
        ax.plot([], [], linestyle='--', linewidth=2.5, color='red', label=self.tr("Talude Cortado"))
        ax.plot([], [], linestyle='--', linewidth=2.5, color='blue', label=self.tr("Talude Aterrado"))

        # Função auxiliar para adicionar textos ao gráfico
        def add_text(ax, text, x_pos, y_pos, text_color, bbox_props):
            """Adiciona texto ao gráfico."""
            ax.text(x_pos, y_pos, text, ha="left", va="bottom", transform=ax.transAxes, fontsize=9, weight='bold', fontstyle='italic', color=text_color, bbox=bbox_props)

        # Propriedades da caixa de anotação
        bbox_props = dict(facecolor='white', alpha=1, boxstyle="round,pad=0.5")

        # Integra a diferença positiva ao longo de todo o perfil. Isso evita
        # unir artificialmente regiões separadas de corte ou aterro.
        x_area = np.asarray(x_fill, dtype=float)

        diferenca = (np.asarray(y_znovo_fill, dtype=float)
            - np.asarray(y_corte_fill, dtype=float))

        if x_area.size >= 2:
            area_cortada = float(np.trapezoid(np.maximum(diferenca, 0.0), x=x_area))

            area_aterrada = float(np.trapezoid(np.maximum(-diferenca, 0.0), x=x_area))
        else:
            area_cortada = 0.0
            area_aterrada = 0.0

        # Calcular as inclinações com proteção para distâncias coincidentes.
        delta_estacas = estacas_distances[-1] - estacas_distances[0]
        delta_apoio = apoio_distances[-1] - apoio_distances[0]

        inclinacao_novoz = (
            (estacas_novoz[-1] - estacas_novoz[0]) / delta_estacas
            if not math.isclose(delta_estacas, 0.0, abs_tol=1e-12)
            else 0.0)

        inclinacao_znovo = (
            (apoio_elevations[-1] - apoio_elevations[0]) / delta_apoio
            if not math.isclose(delta_apoio, 0.0, abs_tol=1e-12)
            else 0.0)

        # Adicionar textos ao gráfico
        add_text(ax, self.tr("Área de Aterro: {area:.2f} m²").format(area=abs(area_aterrada)), 0.85, 1.06, 'blue', bbox_props)
        add_text(ax, self.tr("Área de Corte: {area:.2f} m²").format(area=abs(area_cortada)), 0.85, 1.016, 'magenta', bbox_props)
        add_text(ax, self.tr("Inclinação do Corte/Aterro: {inclinacao:.3f}%").format(inclinacao=inclinacao_novoz * 100), 0.005, 1.016, 'blue', bbox_props)
        add_text(ax, self.tr("Inclinação média do Terreno: {inclinacao:.3f}%").format(inclinacao=inclinacao_znovo * 100), 0.005, 1.06, 'orange', bbox_props)

        # Adicionar anotações e linhas verticais para 'Desnivel' sobre a linha "NovoZ"
        for dist, corte, z, desnivel, x, y in estacas_data:
            # Definir a cor com base no valor de 'Desnivel'
            if desnivel > 0:
                color = 'blue'
            elif desnivel < 0:
                color = 'red'
            else:
                color = 'black'
            
            # Adicionar a anotação com a cor correspondente e uma caixa ao redor do texto
            ax.annotate(f'{desnivel}', xy=(dist, corte), textcoords="offset points", xytext=(0, 7), ha='center', va='bottom', color=color, weight='bold', fontsize=8, bbox=dict(boxstyle="round,pad=0.3", facecolor='white', edgecolor="black", alpha=1))

            # Desenhar a linha vertical da linha "NovoZ" até o Eixo X
            ax.vlines(x=dist, ymin=0, ymax=corte, colors='grey', linestyles='dashed', linewidth=0.5)

        # Coletar todas as posições x onde as linhas verticais tocam o eixo X
        vertical_line_positions = list(estacas_distances)

        if talude_start_intersection:
            vertical_line_positions.append(talude_start_intersection[0])

        if talude_end_intersection:
            vertical_line_positions.append(talude_end_intersection[0])

        # Criar uma lista de xticks incluindo as posições das linhas verticais
        xticks = sorted(set(vertical_line_positions))

        # Formatar os rótulos dos xticks
        formatted_labels = [f"{tick:.0f}" for tick in xticks]

        # Configurar os xticks e seus rótulos
        ax.set_xticks(xticks)
        ax.set_xticklabels(formatted_labels, fontsize=8)

        # Personalizar os rótulos do eixo x
        for i, label in enumerate(ax.get_xticklabels()):
            if xticks[i] in vertical_line_positions:
                # Rótulos onde as linhas verticais tocam o eixo x em negrito e itálico
                label.set_fontweight('bold')
                label.set_fontstyle('italic')

        # Posicionar a legenda no canto superior esquerdo
        ax.legend(loc='upper left')
        ax.grid(axis='y', color='gray', alpha=0.5, linestyle='-', linewidth=0.4)

        # Configurar os ticks do eixo Y para variar a cada 1 metro
        ax.yaxis.set_major_locator(plt.MultipleLocator(1))

        # Definir uma altura fixa para as anotações em relação ao eixo y do gráfico
        altura_fixa_para_anotacoes = y_min1 + (y_max - y_min1) * 0.1 # 5% acima do limite inferior

        # Adicionar anotações para cada ponto na linha de "NovoZ"
        for dist, corte, z, desnivel in zip(estacas_distances, estacas_novoz, z_values, desnivels):
            # Determinar a cor da anotação com base no valor de "Desnível"
            if desnivel < 0:
                cor_anotacao = 'red'
            elif desnivel > 0:
                cor_anotacao = 'blue'
            else:
                cor_anotacao = 'black'

            # Anotação para "NovoZ" (Corte/Aterro)
            ax.annotate(f'{corte:.3f} m',
                        xy=(dist, altura_fixa_para_anotacoes),
                        xytext=(8, 0),
                        textcoords="offset points", ha='center', va='center', color=cor_anotacao, fontstyle='italic', fontweight='bold',
                        fontsize=8, rotation=90, bbox=dict(boxstyle="round,pad=0.3", facecolor='white', edgecolor=cor_anotacao))

            # Anotação para "Z" (Terreno Natural)
            ax.annotate(f'{z:.3f} m',
                        xy=(dist, altura_fixa_para_anotacoes),
                        xytext=(-10.5, 0),
                        textcoords="offset points", ha='left', va='center', color='black', fontstyle='italic', fontweight='bold',
                        fontsize=8, rotation=90, bbox=dict(boxstyle="round,pad=0.3", facecolor='white', edgecolor='orange'))

        # Adicionar rótulos representativos para "Z" e "NovoZ" alinhados com as anotações
        ax.text(0.042, (altura_fixa_para_anotacoes - y_min1) / (y_max - y_min1), self.tr("Terreno Natural"), ha='right', va='center', color='black', fontstyle='italic', fontweight='bold', fontsize=9, rotation=90, transform=ax.transAxes, bbox=dict(boxstyle="round,pad=0.3", facecolor='white', edgecolor='orange'))

        ax.text(0.06, (altura_fixa_para_anotacoes - y_min1) / (y_max - y_min1), self.tr("Corte/Aterro"), ha='right', va='center', color='blue', fontstyle='italic', fontweight='bold', fontsize=9, rotation=90, transform=ax.transAxes, bbox=dict(boxstyle="round,pad=0.5", facecolor='white', edgecolor='red'))

        # Exemplo de uso:
        fig = plt.gcf()
        self.adicionar_rosa_dos_ventos(fig, x_coords, y_coords)

        # Chama a função para adicionar o logotipo ao gráfico
        self.adicionar_logo(fig)

        plt.show()  # Exibe o gráfico

    def adicionar_rosa_dos_ventos(self, fig, x_coords, y_coords):
        """
        Adiciona uma rosa dos ventos ao gráfico.

        Parameters:
        - fig: a figura na qual a rosa dos ventos será desenhada.
        - x_coords: lista de coordenadas x do perfil.
        - y_coords: lista de coordenadas y do perfil.
        """
        # Defina o tamanho e a posição da Rosa dos Ventos
        radius = 0.035  # Raio do círculo (em unidades de figura)
        center = (0.50, 0.82)  # Posição do centro do círculo (em unidades de figura)

        # Desenha um círculo para a rosa dos ventos
        circle = Circle(center, radius, transform=fig.transFigure, edgecolor="black", facecolor="none", clip_on=False)
        fig.add_artist(circle)

        # Desenha linhas com setas para indicar as direções
        for angle in [0, 90, 180, 270]:
            x_start = center[0]
            y_start = center[1]
            x_end = center[0] + 1.0 * radius * np.cos(np.radians(angle))
            y_end = center[1] + 1.0 * radius * np.sin(np.radians(angle))

            # Adiciona uma seta ao final da linha
            arrowprops = dict(arrowstyle="->", lw=1.5, mutation_scale=10)
            fig.add_artist(patches.FancyArrowPatch((x_start, y_start), (x_end, y_end), connectionstyle="arc3,rad=0.0", transform=fig.transFigure, clip_on=False, **arrowprops))

        # Calcula o ângulo com base nas coordenadas fornecidas
        delta_x = x_coords[-1] - x_coords[0]
        delta_y = y_coords[-1] - y_coords[0]
        angle = math.atan2(delta_y, delta_x)

        # Converte o ângulo de radianos para graus para facilitar a interpretação
        angle_degrees = math.degrees(angle)

        # Determina a direção principal com base no ângulo
        if -45 < angle_degrees <= 45:
            directions = ["E", "N", "W", "S"]
        elif 45 < angle_degrees <= 135:
            directions = ["N", "W", "S", "E"]
        elif -135 < angle_degrees <= -45:
            directions = ["S", "E", "N", "W"]
        else:
            directions = ["W", "N", "E", "S"]

        # Adiciona rótulos para as direções
        label_distance = 1.4  # Ajuste essa variável para mudar a distância dos rótulos ao círculo
        for i, label in enumerate(directions):
            angle = 90 * i
            x = center[0] + label_distance * radius * np.cos(np.radians(angle))
            y = center[1] + label_distance * radius * np.sin(np.radians(angle))
            fig.text(x, y, label, ha="center", va="center")

    def adicionar_logo(self, fig):
        """
        Função para adicionar o logotipo ao gráfico, se houver um logotipo selecionado.
        
        A imagem é redimensionada proporcionalmente dentro de uma caixa de 250x150 pixels.
        
        Parameters:
        - fig: O objeto Figure do matplotlib onde o logotipo será adicionado.
        """
        if hasattr(self, 'logo_path') and self.logo_path:
            try:
                # Carregar o logotipo
                logo = plt.imread(self.logo_path)

                # Tamanho máximo da caixa onde o logo deve ser ajustado
                max_width, max_height = 150, 75

                # Obtenha a largura e a altura da imagem original
                img_height, img_width = logo.shape[:2]

                # Calcular o fator de escala para largura e altura
                width_scale = max_width / img_width
                height_scale = max_height / img_height

                # Escolher o menor fator de escala para garantir que a imagem caiba na caixa
                scale_factor = min(width_scale, height_scale)

                # Cria uma instância de OffsetImage com o logotipo redimensionado
                imagebox = OffsetImage(logo, zoom=scale_factor)

                # Opções personalizadas para a caixa
                bboxprops = dict(boxstyle="round,pad=0.5", facecolor="white", edgecolor="black", linewidth=1.5)

                # Cria uma instância de AnnotationBbox para posicionar o logotipo
                ab = AnnotationBbox(imagebox, (0.975, 0.89), frameon=True, xycoords='figure fraction', box_alignment=(1, 1), bboxprops=bboxprops)

                # Adiciona o logotipo ao gráfico
                ax = plt.gca()  # Obtém o eixo atual
                ax.add_artist(ab)

            except Exception as e:
                self.plato_manager.mostrar_mensagem(self.tr("Erro ao carregar o logotipo: {error}").format(error=str(e)), "Erro")
        else:
            self.plato_manager.mostrar_mensagem(self.tr("Nenhum logotipo disponível para adicionar ao gráfico."), "Sucesso")

class ListDeleteButtonDelegate(QStyledItemDelegate):
    def __init__(self, parent=None):
        """
        Inicializa a interface e os componentes da classe, configura sinais,
        widgets e estados iniciais do diálogo ou objeto.
        """
        super(ListDeleteButtonDelegate, self).__init__(parent)
        self.parent = parent

    def paint(self, painter, option, index):
        """
        Personaliza a renderização dos itens do listWidget, incluindo botões de exclusão
        e estilos visuais customizados na interface.
        """
        if index.isValid():
            # Ignora o cabeçalho (primeiro item)
            if index.row() == 0:
                super(ListDeleteButtonDelegate, self).paint(painter, option, index)
                return

            # Desenha o fundo com base no estado
            if option.state & QStyle.StateFlag.State_Selected:
                painter.fillRect(option.rect, option.palette.highlight())
            elif option.state & QStyle.StateFlag.State_MouseOver:
                # Estado de hover (passar o mouse sobre o item)
                hover_color = QColor("#00ffff")  # Cor definida no styleSheet
                painter.fillRect(option.rect, hover_color)
            else:
                painter.fillRect(option.rect, option.palette.base())

            # Calcula as posições
            rect = option.rect
            icon_size = 10
            icon_margin = 4
            icon_rect = QRect(
                rect.left() + icon_margin,
                rect.top() + (rect.height() - icon_size) // 2,
                icon_size,
                icon_size)
            text_rect = QRect(
                icon_rect.right() + icon_margin,
                rect.top(),
                rect.width() - icon_size - 3 * icon_margin,
                rect.height())

            # Desenha o quadradinho com borda arredondada para exclusão
            painter.save()
            painter.setRenderHint(QPainter.RenderHint.Antialiasing)
            painter.setPen(QPen(QColor(0, 0, 255), 1))  # Cor da borda do quadrado
            painter.setBrush(QBrush(QColor(255, 0, 0, 200)))  # Fundo vermelho claro
            radius = 2  # Raio das bordas arredondadas
            painter.drawRoundedRect(icon_rect, radius, radius)  # Desenha o quadrado com bordas arredondadas

            # Desenha o "x" dentro do quadrado
            painter.setPen(QPen(QColor(255, 255, 255), 2))  # Cor e espessura do "x"
            painter.drawLine(icon_rect.topLeft() + QPoint(3, 3), icon_rect.bottomRight() - QPoint(3, 3))
            painter.drawLine(icon_rect.topRight() + QPoint(-3, 3), icon_rect.bottomLeft() + QPoint(3, -3))
            painter.restore()

            # Desenha o texto
            painter.save()
            # Ajusta a cor do texto com base no estado
            if option.state & QStyle.StateFlag.State_Selected:
                text_color = option.palette.highlightedText().color()
            else:
                text_color = option.palette.text().color()
            painter.setPen(text_color)
            font = painter.font()
            font.setPointSize(8)  # Ajusta o tamanho da fonte se necessário
            painter.setFont(font)
            text = index.data(Qt.ItemDataRole.DisplayRole)
            painter.drawText(text_rect, Qt.AlignmentFlag.AlignVCenter |  Qt.TextFlag.TextSingleLine, text)
            painter.restore()

    @staticmethod
    def remove_layer_and_empty_groups(layer_id):
        """
        Remove a camada e elimina somente o grupo pai
        caso ele fique vazio.
        """
        project = QgsProject.instance()
        root = project.layerTreeRoot()
        layer_node = root.findLayer(layer_id)

        parent_group = (layer_node.parent()
            if layer_node is not None
            else None)

        if project.mapLayer(layer_id):
            project.removeMapLayer(layer_id)

        if (parent_group is not None
            and parent_group is not root
            and len(parent_group.children()) == 0):
            parent = parent_group.parent()

            if parent is not None:
                parent.removeChildNode(parent_group)

    def editorEvent(self, event, model, option, index):
        """
        Trata eventos de interação do usuário nos itens do listWidget,
        como cliques em botões de exclusão ou seleção.
        """
        if index.row() == 0:
            return False  # Ignora eventos no cabeçalho

        if event.type() == QEvent.Type.MouseButtonRelease:
            # Calcula as posições
            rect = option.rect
            icon_size = 10
            icon_margin = 4
            icon_rect = QRect(
                rect.left() + icon_margin,
                rect.top() + (rect.height() - icon_size) // 2,
                icon_size,
                icon_size)
            if icon_rect.contains(event.pos()):
                # Remove a camada correspondente do QGIS e do listWidget
                layer_id = index.data(Qt.ItemDataRole.UserRole)  # Obtém o ID da camada armazenado no UserRole do item
                # Delete a camada, e caso seja a última delete o grupo
                ListDeleteButtonDelegate.remove_layer_and_empty_groups(layer_id)
                # Não é necessário remover o item manualmente; o slot de atualização cuidará disso

                iface.mapCanvas().refresh()  # Atualiza o canvas imediatamente

                return True
        return super(ListDeleteButtonDelegate, self).editorEvent(event, model, option, index)