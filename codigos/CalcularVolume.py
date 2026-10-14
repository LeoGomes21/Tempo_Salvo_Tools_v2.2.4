from qgis.core import QgsProject, QgsRasterLayer, QgsMapSettings, QgsMapRendererCustomPainterJob, Qgis, QgsRasterShader, QgsColorRampShader, QgsSingleBandPseudoColorRenderer, QgsVectorLayer, QgsFields, QgsField, QgsPointXY, QgsGeometry, QgsRectangle, QgsFeature, QgsFillSymbol, QgsRendererRange, QgsGraduatedSymbolRenderer, QgsFeedback
from qgis.PyQt.QtWidgets import QDialog, QGraphicsScene, QGraphicsPixmapItem, QListWidgetItem, QLabel, QProgressBar, QApplication, QStyledItemDelegate, QStyle, QAbstractItemView, QFileDialog, QMessageBox
from qgis.PyQt.QtCore import Qt, QSize, QFileInfo, QRect, QPoint, QEvent, QSettings, QCoreApplication, QMetaType, QTimer, QUrl
from qgis.PyQt.QtGui import QImage, QPainter, QPixmap, QColor, QStandardItemModel, QStandardItem, QFont, QPen, QBrush, QDesktopServices
from qgis.analysis import QgsRasterCalculatorEntry, QgsRasterCalculator
from collections import deque
from qgis.utils import iface
from qgis.PyQt import uic
from osgeo import gdal
import pandas as pd
import numpy as np
import processing
import tempfile
import json
import time
import math
import os

FORM_CLASS, _ = uic.loadUiType(os.path.join(
    os.path.dirname(__file__), 'calcularVolumeMDT.ui'))

class VolumeManager(QDialog, FORM_CLASS):
    def __init__(self, parent=None):
        """Constructor."""
        super(VolumeManager, self).__init__(parent)
        # Configura a interface do usuário a partir do Designer.
        self.setupUi(self)
        # Altera o título da janela
        self.setWindowTitle(self.tr("Calcular Volumes entre MDTs"))

        self.iface = iface

        # Cria uma cena gráfica para os QGraphicsViews
        self.scene = QGraphicsScene()
        self.scene2 = QGraphicsScene()  # Segunda cena gráfica

        self.graphicsViewRaster.setScene(self.scene)
        self.graphicsViewRaster2.setScene(self.scene2)  # Configura a segunda view

        # Trava interna para evitar sincronização durante atualização dos combos
        self._atualizando_combo_rasters = False

        # Trava interna para evitar recursão ao remover o grupo Calculados
        self._removendo_grupo_calculados = False

        # Inicializa os ComboBoxes de Raster
        self.init_combo_box_raster()

        self.setup_table_view()

        # Conecta os sinais aos slots
        self.connect_signals()

        # Configura a janela para permitir minimizar, maximizar e fechar
        self.setWindowFlags(self.windowFlags() | Qt.WindowType.WindowMinimizeButtonHint | Qt.WindowType.WindowMaximizeButtonHint | Qt.WindowType.WindowCloseButtonHint)

    def tr(self, message):
        return QCoreApplication.translate("VolumeManager", message)

    def connect_signals(self):
        # Conecta os sinais aos slots
        self.comboBoxRaster.currentIndexChanged.connect(self.display_raster)
        self.comboBoxRaster2.currentIndexChanged.connect(self.display_raster2)  # Conecta ao segundo ComboBox

        # Impede que o mesmo raster seja selecionado nos dois comboBoxes
        self.comboBoxRaster.currentIndexChanged.connect(self.sync_combo_boxes)
        self.comboBoxRaster2.currentIndexChanged.connect(self.sync_combo_boxes)

        # Conecta o sinal de remoção de camada
        QgsProject.instance().layersRemoved.connect(self.update_combo_box)

        # Conecta o sinal de remoção de camada
        QgsProject.instance().layersRemoved.connect(self.update_list_view_on_layer_removed)

        # Conecta o sinal de adição de camada
        QgsProject.instance().layersAdded.connect(self.handle_layers_added)

        # Conecta o botão para Calcular a diferença entre as camadas Rasters
        self.pushButtonCalcular.clicked.connect(self.calculate_raster_difference)

        # Conecta o listWidgetRasters à função para exibir estatísticas ao selecionar uma camada
        self.listWidgetRasters.itemSelectionChanged.connect(self.display_raster_statistics)

        # Conectar o botão pushButtonVolume à função de cálculo de volume
        self.pushButtonVolume.clicked.connect(self.calculate_volume)

        # Conecta o botão de exportação ao método export_to_excel
        self.pushButtonExcel.clicked.connect(self.exportar_tabela_para_excel)

        # Conectar o botão pushButtonCancelar para fechar o diálogo
        self.pushButtonCancelar.clicked.connect(self.close)

        # Conectar a verificação das condições dos comboBoxes para ativar/desativar o pushButtonCalcular
        self.comboBoxRaster.currentIndexChanged.connect(self.verificar_condicoes_calculo)
        self.comboBoxRaster2.currentIndexChanged.connect(self.verificar_condicoes_calculo)

        # Método de inicialização do diálogo listWidget
        self.listWidgetRasters.setItemDelegate(ListDeleteButtonDelegate(self.listWidgetRasters, self))

        # Chama a verificação de condições ao iniciar
        # self.verificar_condicoes_calculo()

        self.listWidgetRasters.itemSelectionChanged.connect(self.verificar_selecao_volume)
        
        self.verificar_dados_excel()

        # Detecta a alteração do nome da camada raster
        for layer in QgsProject.instance().mapLayers().values():
            if isinstance(layer, QgsRasterLayer):
                layer.nameChanged.connect(self.update_combo_box)

    def update_combo_box(self, *args):
        """
        Atualiza os comboBoxes de raster.
        A própria função init_combo_box_raster() já preserva seleções válidas
        e evita selecionar a mesma camada nos dois combos.
        """
        self.init_combo_box_raster()

    def display_raster(self):
        # Limpa a cena antes de adicionar um novo item
        self.scene.clear()

        # Obtém o ID da camada raster selecionada
        selected_raster_id = self.comboBoxRaster.currentData()

        # Busca a camada raster pelo ID
        selected_layer = QgsProject.instance().mapLayer(selected_raster_id)
        
        if isinstance(selected_layer, QgsRasterLayer):
            # Configurações do mapa
            map_settings = QgsMapSettings()
            map_settings.setLayers([selected_layer])
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

            # Ajusta a cena ao QGraphicsView
            self.graphicsViewRaster.setSceneRect(pixmap_item.boundingRect())
            self.graphicsViewRaster.fitInView(self.scene.sceneRect(), Qt.AspectRatioMode.KeepAspectRatio)

    def display_raster2(self):
        # Limpa a segunda cena antes de adicionar um novo item
        self.scene2.clear()

        # Obtém o ID da camada raster selecionada
        selected_raster_id = self.comboBoxRaster2.currentData()

        # Busca a camada raster pelo ID
        selected_layer = QgsProject.instance().mapLayer(selected_raster_id)
        
        if isinstance(selected_layer, QgsRasterLayer):
            # Configurações do mapa
            map_settings = QgsMapSettings()
            map_settings.setLayers([selected_layer])
            map_settings.setBackgroundColor(QColor(255, 255, 255))
            
            # Define o tamanho da imagem a ser renderizada
            width = self.graphicsViewRaster2.viewport().width()
            height = self.graphicsViewRaster2.viewport().height()
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
            self.scene2.addItem(pixmap_item)

            # Ajusta a cena ao QGraphicsView
            self.graphicsViewRaster2.setSceneRect(pixmap_item.boundingRect())
            self.graphicsViewRaster2.fitInView(self.scene2.sceneRect(), Qt.AspectRatioMode.KeepAspectRatio)

    def handle_layers_added(self, layers):
        # Conecta o sinal nameChanged das novas camadas raster
        for layer in layers:
            if isinstance(layer, QgsRasterLayer):
                layer.nameChanged.connect(self.update_combo_box)
        self.update_combo_box()

    def showEvent(self, event):
        super(VolumeManager, self).showEvent(event)
        # Ajusta a visualização quando o diálogo é mostrado
        self.display_raster()
        self.display_raster2()
        self.carregar_estado_table_volumes()  # Limpa o tableView ao iniciar o diálogo

        # Verifica e carrega camadas do grupo "Calculados" ao iniciar o diálogo
        self.load_calculados_group()

        # Reseta o estado dos checkboxes ao iniciar o diálogo
        self.checkBoxPoligono.setChecked(False)
        self.checkBoxCorteAterro.setChecked(False)
        self.checkBoxSalvar.setChecked(False)
        
        # Verifica as condições para habilitar/desabilitar o botão Calcular
        self.verificar_condicoes_calculo()

        self.verificar_selecao_volume()  # reseta o estado do pushButtonVolume ao iniciar o diálogo

        # Reseta o estado do pushButtonExcel ao iniciar o diálogo
        self.verificar_dados_excel()

    def closeEvent(self, event):
        parent = self.parent()
        if parent:
            parent.volume_mdt_dlg = None
        super(VolumeManager, self).closeEvent(event)

    def add_layer_to_group(self, layer, group_name):
        """
        Adiciona a camada ao grupo informado de forma sincronizada com a árvore do QGIS.
        Evita criar nós órfãos ou grupos que depois não são removidos corretamente.
        """
        project = QgsProject.instance()
        root = project.layerTreeRoot()

        # Procura ou cria o grupo
        group = root.findGroup(group_name)
        if group is None:
            group = root.insertGroup(0, group_name)

        # Adiciona a camada ao projeto sem jogar automaticamente na raiz
        if not project.mapLayer(layer.id()):
            project.addMapLayer(layer, False)

        # Evita duplicar a camada dentro do grupo
        if not group.findLayer(layer.id()):
            group.insertLayer(0, layer)

        # Atualiza a listWidget
        self.update_list_view(group)

        self.init_combo_box_raster()

    def update_list_view_on_layer_removed(self, layer_ids):
        """
        Atualiza a lista após remoção de camadas.
        Usa QTimer para esperar a árvore do QGIS concluir a remoção.
        """
        QTimer.singleShot(0, self.remover_grupo_calculados_se_vazio)

    def atualizar_canvas_qgis(self):
        """
        Força a atualização visual do mapa do QGIS após remoção de camadas.
        Evita que camadas removidas continuem aparecendo como cache na tela.
        """
        try:
            canvas = self.iface.mapCanvas()

            # Para qualquer renderização em andamento
            try:
                canvas.stopRendering()
            except Exception:
                pass  # nosec B110

            # Limpa cache, quando disponível na versão do QGIS
            if hasattr(canvas, "clearCache"):
                try:
                    canvas.clearCache()
                except Exception:
                    pass  # nosec B110

            # Solicita repaint das camadas restantes
            for layer in QgsProject.instance().mapLayers().values():
                try:
                    layer.triggerRepaint()
                except Exception:
                    pass  # nosec B110

            # Atualiza o canvas
            try:
                canvas.refreshAllLayers()
            except Exception:
                pass  # nosec B110

            canvas.refresh()
            QCoreApplication.processEvents()

        except Exception:
            pass  # nosec B110

    def remover_grupo_calculados_se_vazio(self):
        """
        Remove o grupo 'Calculados' quando não existir mais nenhuma camada raster válida nele.
        Se sobrarem apenas vetores, como polígonos gerados a partir do raster,
        remove essas camadas também e apaga o grupo inteiro.
        """
        if getattr(self, "_removendo_grupo_calculados", False):
            return

        project = QgsProject.instance()
        root = project.layerTreeRoot()
        group = root.findGroup(self.tr("Calculados"))

        if group is None:
            self.clear_list_view()
            self.verificar_selecao_volume()
            return

        raster_nodes_validos = []
        layer_ids_restantes = []

        # Examina todas as camadas dentro do grupo Calculados
        for tree_layer in list(group.findLayers()):
            layer_id = tree_layer.layerId()
            layer = project.mapLayer(layer_id)

            # Remove nó órfão, caso exista
            if layer is None:
                parent = tree_layer.parent()
                if parent is not None:
                    parent.removeChildNode(tree_layer)
                continue

            layer_ids_restantes.append(layer_id)

            # O grupo só deve permanecer se ainda houver raster válido
            if isinstance(layer, QgsRasterLayer):
                raster_nodes_validos.append(tree_layer)

        # Se ainda existe pelo menos um raster, mantém o grupo
        if raster_nodes_validos:
            self.update_list_view(group)
            self.verificar_selecao_volume()
            return

        # Se chegou aqui, não há mais raster no grupo.
        # Então remove todas as camadas restantes, inclusive polígonos.
        self._removendo_grupo_calculados = True

        try:
            for layer_id in list(layer_ids_restantes):
                if project.mapLayer(layer_id) is not None:
                    try:
                        project.removeMapLayer(layer_id)
                    except Exception:
                        pass  # nosec B110

            # Rebusca o grupo após remover as camadas restantes
            group = root.findGroup(self.tr("Calculados"))

            if group is not None:
                parent = group.parent()
                if parent is not None:
                    parent.removeChildNode(group)

        finally:
            self._removendo_grupo_calculados = False

        self.clear_list_view()
        self.verificar_selecao_volume()

        if hasattr(self, "textEditInfo"):
            self.textEditInfo.setHtml("<p><b>{}</b></p>".format(self.tr("Nenhuma camada selecionada.")))

        self.init_combo_box_raster()

        # Força a atualização imediata do mapa
        self.atualizar_canvas_qgis()

        # Reforço com pequeno atraso, porque a árvore do QGIS às vezes termina a remoção depois
        QTimer.singleShot(100, self.atualizar_canvas_qgis)

    def clear_list_view(self):
        # Limpa o listWidgetRasters diretamente
        self.listWidgetRasters.clear()
        self._add_rasters_header()           # recoloca o cabeçalho fixo

    def _add_rasters_header(self):
        """Adiciona (ou recoloca) o cabeçalho permanente no listWidgetRasters."""
        list_widget = self.listWidgetRasters
        header_text = self.tr("Calculados")

        header_label = QLabel(header_text)
        header_label.setAlignment(Qt.AlignmentFlag.AlignCenter)
        header_label.setFont(QFont("Arial", 8, weight=QFont.Weight.Bold))
        header_label.setStyleSheet(
            """
            QLabel {
                background-color: #C0C0C0;      /* Cinza 3D */
                color: #000000;
                padding: 1px;
                border: 1px solid #A0A0A0;
                border-left-color: #E0E0E0;     /* efeito 3D */
                border-top-color:  #E0E0E0;
                border-right-color:#808080;
                border-bottom-color:#808080;
            }""")

        list_widget = self.listWidgetRasters
        header_item = QListWidgetItem(list_widget)
        header_item.setFlags(Qt.ItemFlag.NoItemFlags)          # não selecionável
        list_widget.addItem(header_item)
        list_widget.setItemWidget(header_item, header_label)
        header_item.setSizeHint(header_label.sizeHint())

    def update_list_view(self, group):
        list_widget = self.listWidgetRasters
        list_widget.clear()
        self._add_rasters_header()

        # Acrescenta somente camadas raster do grupo Calculados
        for tree_layer in group.findLayers():
            layer = tree_layer.layer()

            if isinstance(layer, QgsRasterLayer):
                item = QListWidgetItem(layer.name())
                item.setData(Qt.ItemDataRole.UserRole, layer.id())
                list_widget.addItem(item)

        list_widget.setStyleSheet(
            """
            QListWidget::item:hover   { background-color:#aaffff; }
            QListWidget::item:selected{ background-color:#00aaff; color:black; }
            QListWidget::item:hover:selected{ background-color:#00aaff; }
            QListWidget::item         { padding:1px; }
            """)

    def load_calculados_group(self):
        """
        Carrega o grupo 'Calculados' ou remove o grupo se ele estiver vazio.
        """
        self.remover_grupo_calculados_se_vazio()

    def _ids_rasters_calculados(self):
        """
        Retorna os IDs das camadas raster que estão dentro do grupo 'Calculados'.
        Essas camadas não devem entrar nos comboBoxes de entrada.
        """
        root = QgsProject.instance().layerTreeRoot()
        group = root.findGroup(self.tr("Calculados"))

        ids = set()

        if group:
            for tree_layer in group.findLayers():
                layer = tree_layer.layer()

                if isinstance(layer, QgsRasterLayer):
                    ids.add(layer.id())

        return ids

    def _rasters_disponiveis_para_calculo(self):
        """
        Retorna apenas os rasters disponíveis para cálculo,
        excluindo os rasters do grupo 'Calculados'.
        """
        calculados_ids = self._ids_rasters_calculados()

        return [
            layer
            for layer in QgsProject.instance().mapLayers().values()
            if isinstance(layer, QgsRasterLayer)
            and layer.id() not in calculados_ids]

    def init_combo_box_raster(self):
        """
        Inicializa/atualiza os comboBoxes de raster disponíveis para cálculo.
        Exclui camadas do grupo 'Calculados' e evita selecionar a mesma camada
        nos dois comboBoxes.
        """
        if getattr(self, "_atualizando_combo_rasters", False):
            return

        self._atualizando_combo_rasters = True

        current_layer_id_1 = self.comboBoxRaster.currentData()
        current_layer_id_2 = self.comboBoxRaster2.currentData()

        raster_layers = self._rasters_disponiveis_para_calculo()

        try:
            self.comboBoxRaster.blockSignals(True)
            self.comboBoxRaster2.blockSignals(True)

            self.comboBoxRaster.clear()
            self.comboBoxRaster2.clear()

            for raster_layer in raster_layers:
                self.comboBoxRaster.addItem(raster_layer.name(), raster_layer.id())
                self.comboBoxRaster2.addItem(raster_layer.name(), raster_layer.id())

            count = len(raster_layers)

            if count == 0:
                self.comboBoxRaster.setCurrentIndex(-1)
                self.comboBoxRaster2.setCurrentIndex(-1)

            elif count == 1:
                # Apenas uma camada disponível:
                # combo 1 seleciona a camada, combo 2 fica sem seleção.
                self.comboBoxRaster.setCurrentIndex(0)
                self.comboBoxRaster2.setCurrentIndex(-1)

            else:
                # Restaura o combo 1, se possível
                index_1 = self.comboBoxRaster.findData(current_layer_id_1)
                if index_1 == -1:
                    index_1 = 0

                self.comboBoxRaster.setCurrentIndex(index_1)

                # Restaura o combo 2, se possível
                index_2 = self.comboBoxRaster2.findData(current_layer_id_2)

                if index_2 == -1 or index_2 == index_1:
                    # Escolhe automaticamente uma camada diferente da primeira
                    index_2 = 1 if index_1 == 0 else 0

                self.comboBoxRaster2.setCurrentIndex(index_2)

        finally:
            self.comboBoxRaster.blockSignals(False)
            self.comboBoxRaster2.blockSignals(False)
            self._atualizando_combo_rasters = False

        # Atualiza as visualizações depois de terminar a troca dos combos
        self.display_raster()
        self.display_raster2()
        self.verificar_condicoes_calculo()

    def sync_combo_boxes(self):
        """
        Evita que os dois comboBoxes selecionem a mesma camada.
        Se houver apenas uma camada disponível, não tenta forçar troca impossível.
        """
        if getattr(self, "_atualizando_combo_rasters", False):
            return

        selected_id_1 = self.comboBoxRaster.currentData()
        selected_id_2 = self.comboBoxRaster2.currentData()

        # Se algum combo está sem seleção, apenas revalida o botão
        if not selected_id_1 or not selected_id_2:
            self.verificar_condicoes_calculo()
            return

        # Se não são iguais, está tudo certo
        if selected_id_1 != selected_id_2:
            self.verificar_condicoes_calculo()
            return

        # Se existe só uma opção, não há para onde ajustar
        if self.comboBoxRaster.count() < 2 or self.comboBoxRaster2.count() < 2:
            self.comboBoxRaster2.setCurrentIndex(-1)
            self.verificar_condicoes_calculo()
            return

        sender_combo = self.sender()

        self._atualizando_combo_rasters = True

        try:
            if sender_combo == self.comboBoxRaster:
                ajustou = self.adjust_combo_box(self.comboBoxRaster2, selected_id_1)
                if not ajustou:
                    self.comboBoxRaster2.setCurrentIndex(-1)

            elif sender_combo == self.comboBoxRaster2:
                ajustou = self.adjust_combo_box(self.comboBoxRaster, selected_id_2)
                if not ajustou:
                    self.comboBoxRaster.setCurrentIndex(-1)

        finally:
            self._atualizando_combo_rasters = False

        self.display_raster()
        self.display_raster2()
        self.verificar_condicoes_calculo()

    def adjust_combo_box(self, combo_box, excluded_id):
        """
        Seleciona no comboBox uma camada diferente da camada excluída.
        Retorna True se conseguiu ajustar, False se não encontrou alternativa.
        """
        count = combo_box.count()

        if count < 2:
            return False

        current_index = combo_box.currentIndex()

        for i in range(count):
            new_index = (current_index + 1 + i) % count

            if combo_box.itemData(new_index) != excluded_id:
                combo_box.setCurrentIndex(new_index)
                return True

        return False

    def display_raster_statistics(self):
        # Obtém o item selecionado no listWidgetRasters
        selected_items = self.listWidgetRasters.selectedItems()

        if not selected_items:
            self.textEditInfo.setHtml(f"<p><b>{self.tr('Nenhuma camada selecionada.')}</b></p>")
            return

        # Obtém o ID da camada selecionada
        selected_item = selected_items[0]
        layer_id = selected_item.data(Qt.ItemDataRole.UserRole)
        layer = QgsProject.instance().mapLayer(layer_id)

        if not isinstance(layer, QgsRasterLayer):
            self.textEditInfo.setHtml(f"<p><b>{self.tr('Camada selecionada não é um raster válido.')}</b></p>")
            return

        # Estatísticas básicas do raster
        stats = layer.dataProvider().bandStatistics(1, Qgis.RasterBandStatistic.All)

        extent = layer.extent()
        crs = layer.crs()

        # ÁREA EFETIVA DO RASTER
        pixel_size_x = abs(layer.rasterUnitsPerPixelX())
        pixel_size_y = abs(layer.rasterUnitsPerPixelY())

        area_pixel = pixel_size_x * pixel_size_y

        # elementCount representa os pixels válidos considerados
        # nas estatísticas da banda
        pixels_validos = int(stats.elementCount)

        # Área efetivamente ocupada pelos pixels válidos
        area_valida = pixels_validos * area_pixel

        # Área do retângulo envolvente - apenas informativa
        area_extent = extent.width() * extent.height()

        # Nome completo do SRC
        crs_description = crs.description()

        # INFORMAÇÕES EXIBIDAS
        info_text = (
            f"<b>{self.tr('Estatísticas:')}</b><br><br>"

            f"<b>{self.tr('Valor Mínimo:')}</b> "
            f"{stats.minimumValue:.3f}<br>"

            f"<b>{self.tr('Valor Máximo:')}</b> "
            f"{stats.maximumValue:.3f}<br>"

            f"<b>{self.tr('Pixels Válidos:')}</b> "
            f"{pixels_validos:,}<br>"

            f"<b>{self.tr('Área Válida:')}</b> "
            f"{area_valida:.3f} m²<br>"

            f"<b>{self.tr('Área da Extensão:')}</b> "
            f"{area_extent:.3f} m²<br>"

            f"<b>{self.tr('Resolução Espacial:')}</b> "
            f"{pixel_size_x:.3f} x {pixel_size_y:.3f} m<br>"

            f"<b>{self.tr('Extensão (Extent):')}</b><br>"

            f" - xmin: {extent.xMinimum():.3f}<br>"
            f" - ymin: {extent.yMinimum():.3f}<br>"
            f" - xmax: {extent.xMaximum():.3f}<br>"
            f" - ymax: {extent.yMaximum():.3f}<br>"

            f"<b>{self.tr('SRC da Camada:')}</b> "
            f"{crs.authid()} - {crs_description}<br>")

        self.textEditInfo.setReadOnly(True)
        self.textEditInfo.setHtml(info_text)

    def mostrar_mensagem(self, texto, tipo, duracao=2):
        """
        Exibe uma mensagem na barra de mensagens do QGIS, proporcionando feedback ao usuário baseado nas ações realizadas.
        As mensagens podem ser de erro ou de sucesso, com uma duração configurável e uma opção de abrir uma pasta.

        :param texto: Texto da mensagem a ser exibida.
        :param tipo: Tipo da mensagem ("Erro" ou "Sucesso") que determina a cor e o ícone da mensagem.
        :param duracao: Duração em segundos durante a qual a mensagem será exibida (padrão é 3 segundos).
        :param caminho_pasta: Caminho da pasta a ser aberta ao clicar no botão (padrão é None).
        :param caminho_arquivo: Caminho do arquivo a ser executado ao clicar no botão (padrão é None).
        """
        # Obtém a barra de mensagens da interface do QGIS
        bar = iface.messageBar()  # Acessa a barra de mensagens da interface do QGIS

        # Exibe a mensagem com o nível apropriado baseado no tipo
        if tipo == "Erro":
            # Mostra uma mensagem de erro na barra de mensagens com um ícone crítico e a duração especificada
            bar.pushMessage(self.tr("Erro"), texto, level=Qgis.MessageLevel.Critical, duration=duracao)
        elif tipo == "Sucesso":
            # Cria o item da mensagem
            msg = bar.createMessage(self.tr("Sucesso"), texto)
            
            # Adiciona a mensagem à barra com o nível informativo e a duração especificada
            bar.pushWidget(msg, level=Qgis.MessageLevel.Info, duration=duracao)

    def iniciar_progress_bar(self, total_steps, titulo=None, formato=None):
        """
        Inicia e exibe uma barra de progresso na barra de mensagens do QGIS.
        """
        if titulo is None:
            titulo = self.tr("Extraindo cotas do Raster")

        if formato is None:
            formato = self.tr("%p% - %v de %m etapas concluídas")

        progressMessageBar = self.iface.messageBar().createMessage(titulo)

        progressBar = QProgressBar()
        progressBar.setAlignment(Qt.AlignmentFlag.AlignLeft | Qt.AlignmentFlag.AlignVCenter)
        progressBar.setFormat(formato)
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
                min-height: 5px;
            }
        """)

        progressMessageBar.layout().addWidget(progressBar)
        self.iface.messageBar().pushWidget(progressMessageBar, Qgis.MessageLevel.Info)

        progressBar.setMinimum(0)
        progressBar.setMaximum(max(1, int(total_steps)))
        progressBar.setValue(0)

        return progressBar, progressMessageBar

    def add_result_raster_to_project(self, output_path, primitive_name, modified_name):
        base_name = f"{primitive_name}_{modified_name}"

        # Verificar se já existe uma camada com este nome e adicionar um sufixo para torná-lo único
        base_name = self.get_unique_layer_name(base_name)

        result_layer = QgsRasterLayer(output_path, base_name)

        if not result_layer.isValid():
            return None  # Retorna None em caso de erro

        # Verifica se o checkBoxCorteAterro está selecionado
        if self.checkBoxCorteAterro.isChecked():
            # Obtém as estatísticas da banda 1
            stats = result_layer.dataProvider().bandStatistics(1, Qgis.RasterBandStatistic.All)
            minValue = stats.minimumValue
            maxValue = stats.maximumValue

            # Cria apenas três classes para Corte, Sem Alterações e Aterro
            tolerancia_zero = 0.000001

            colorRampItems = [
                QgsColorRampShader.ColorRampItem(
                    -tolerancia_zero,
                    QColor('red'),
                    self.tr("Menor que 0 - Corte")),

                QgsColorRampShader.ColorRampItem(
                    tolerancia_zero,
                    QColor('gray'),
                    self.tr("Igual a 0 - Sem alterações")),

                QgsColorRampShader.ColorRampItem(
                    float('inf'),
                    QColor('blue'),
                    self.tr("Maior que 0 - Aterro"))]

            # Configura o shader
            colorRampShader = QgsColorRampShader()
            colorRampShader.setColorRampItemList(colorRampItems)
            colorRampShader.setColorRampType(Qgis.ShaderInterpolationMethod.Discrete)

            # Configura o raster shader
            rasterShader = QgsRasterShader()
            rasterShader.setRasterShaderFunction(colorRampShader)

            # Cria o renderizador
            renderer = QgsSingleBandPseudoColorRenderer(result_layer.dataProvider(), 1, rasterShader)
            result_layer.setRenderer(renderer)

        # Adicionar a camada ao grupo "Calculados"
        self.add_layer_to_group(result_layer, self.tr("Calculados"))

        # Retorna a camada raster criada
        return result_layer

    def get_unique_layer_name(self, base_name):
        """
        Gera um nome de camada único, adicionando um sufixo numérico, se necessário.
        """
        counter = 1
        unique_name = base_name

        while QgsProject.instance().mapLayersByName(unique_name):
            unique_name = f"{base_name}_{counter}"
            counter += 1

        return unique_name

    def _valores_quase_iguais(self, a, b, rel_tol=1e-6, abs_tol=1e-9):
        """
        Compara valores numéricos com tolerância.
        Útil para resolução de raster, que pode ter pequenas diferenças decimais.
        """
        try:
            return math.isclose(float(a), float(b), rel_tol=rel_tol, abs_tol=abs_tol)
        except Exception:
            return False

    def _valor_quase_inteiro(self, valor, tolerancia=1e-6):
        """
        Verifica se um valor está suficientemente próximo de um número inteiro.
        Usado para saber se a diferença entre origens cai exatamente na grade dos pixels.
        """
        try:
            valor = float(valor)
            return abs(valor - round(valor)) <= tolerancia
        except Exception:
            return False

    def _validar_resolucao_e_grade_rasters(self, raster_primitivo, raster_modificado):
        """
        Valida se os dois rasters possuem a mesma resolução espacial.

        Pequenas diferenças causadas apenas por precisão de ponto flutuante
        são toleradas. Qualquer diferença real de resolução gera aviso.

        Observação:
        esta rotina valida apenas a resolução. O alinhamento/origem da grade
        será validado separadamente.

        Retorna:
        - (True, "") se as resoluções forem equivalentes;
        - (False, mensagem) se houver diferença real de resolução.
        """

        res_x_1 = abs(raster_primitivo.rasterUnitsPerPixelX())
        res_y_1 = abs(raster_primitivo.rasterUnitsPerPixelY())

        res_x_2 = abs(raster_modificado.rasterUnitsPerPixelX())
        res_y_2 = abs(raster_modificado.rasterUnitsPerPixelY())

        # Verifica resoluções inválidas
        if res_x_1 <= 0 or res_y_1 <= 0:
            return False, self.tr("O raster primitivo '{raster_name}' possui resolução inválida.").format(raster_name=raster_primitivo.name())

        if res_x_2 <= 0 or res_y_2 <= 0:
            return False, self.tr("O raster modificado '{raster_name}' possui resolução inválida.").format(raster_name=raster_modificado.name())

        diferenca_x = abs(res_x_1 - res_x_2)
        diferenca_y = abs(res_y_1 - res_y_2)

         # Considera as resoluções equivalentes
        # quando forem iguais até 3 casas decimais.
        resolucao_x_igual = (round(res_x_1, 3) == round(res_x_2, 3))
        resolucao_y_igual = (round(res_y_1, 3) == round(res_y_2, 3))

        if not resolucao_x_igual or not resolucao_y_igual:
            return False, self.tr(
                "Os rasters possuem resoluções espaciais diferentes.\n\n"
                "Primitivo: {res_x_1:.3f} x {res_y_1:.3f} m\n"
                "Modificado: {res_x_2:.3f} x {res_y_2:.3f} m\n\n"
                "Diferença X: {diferenca_x:.9f} m\n"
                "Diferença Y: {diferenca_y:.9f} m\n\n"
                "Para cálculo volumétrico confiável, recomenda-se reamostrar "
                "os rasters para exatamente ou aproximadamente para a mesma resolução antes de continuar.\n\n"
                "O cálculo ainda pode ser executado usando a grade de saída ").format(
                res_x_1=res_x_1,
                res_y_1=res_y_1,
                res_x_2=res_x_2,
                res_y_2=res_y_2,
                diferenca_x=diferenca_x,
                diferenca_y=diferenca_y)

        return True, ""

    def _validar_rasters_para_calculo(self, mostrar_mensagem=False):
        """
        Valida as condições necessárias para calcular a diferença entre dois MDTs.
        Retorna um dicionário com ok=True quando tudo está correto.
        Se mostrar_mensagem=True, exibe a causa do bloqueio na barra do QGIS.
        """
        def falha(mensagem):
            if mostrar_mensagem:
                self.mostrar_mensagem(mensagem, "Erro", 3)

            return {
                "ok": False,
                "mensagem": mensagem,
                "raster_primitivo": None,
                "raster_modificado": None,
                "intersection_extent": None,
                "width": 0,
                "height": 0}

        rasters_disponiveis = self._rasters_disponiveis_para_calculo()

        if len(rasters_disponiveis) == 0:
            return falha(self.tr("Nenhum raster disponível para cálculo. Adicione pelo menos dois MDTs ao projeto."))

        if len(rasters_disponiveis) == 1:
            return falha(self.tr("Existe apenas um raster disponível para cálculo. Adicione outro MDT para comparar."))

        raster_id_primitivo = self.comboBoxRaster.currentData()
        raster_id_modificado = self.comboBoxRaster2.currentData()

        if not raster_id_primitivo or not raster_id_modificado:
            return falha(self.tr("Selecione duas camadas raster para calcular a diferença."))

        if raster_id_primitivo == raster_id_modificado:
            return falha(self.tr("Selecione dois rasters diferentes. O raster primitivo e o modificado não podem ser a mesma camada."))

        raster_primitivo = QgsProject.instance().mapLayer(raster_id_primitivo)
        raster_modificado = QgsProject.instance().mapLayer(raster_id_modificado)

        if not isinstance(raster_primitivo, QgsRasterLayer):
            return falha(self.tr("A camada selecionada como raster primitivo não é um raster válido."))

        if not isinstance(raster_modificado, QgsRasterLayer):
            return falha(self.tr("A camada selecionada como raster modificado não é um raster válido."))

        if not raster_primitivo.isValid():
            return falha(self.tr("O raster primitivo '{raster_name}' não está válido.").format(raster_name=raster_primitivo.name()))

        if not raster_modificado.isValid():
            return falha(self.tr("O raster modificado '{raster_name}' não está válido.").format(raster_name=raster_modificado.name()))

        crs_primitivo = raster_primitivo.crs()
        crs_modificado = raster_modificado.crs()

        if not crs_primitivo.isValid():
            return falha(self.tr("O raster primitivo '{raster_name}' está sem SRC válido.").format(raster_name=raster_primitivo.name()))

        if not crs_modificado.isValid():
            return falha(self.tr("O raster modificado '{raster_name}' está sem SRC válido.").format(raster_name=raster_modificado.name()))

        if crs_primitivo != crs_modificado:
            return falha(
                self.tr(
                    "Os rasters possuem SRC diferentes.\n"
                    "Primitivo: {crs_primitivo_authid} - {crs_primitivo_description}\n"
                    "Modificado: {crs_modificado_authid} - {crs_modificado_description}"
                ).format(
                    crs_primitivo_authid=crs_primitivo.authid(),
                    crs_primitivo_description=crs_primitivo.description(),
                    crs_modificado_authid=crs_modificado.authid(),
                    crs_modificado_description=crs_modificado.description()))

        if crs_primitivo.isGeographic() or crs_modificado.isGeographic():
            return falha(self.tr("Os rasters estão em coordenadas geográficas.\n"
                    "Para calcular volume corretamente, reprojete os MDTs para um SRC projetado em metros, como UTM."))

        extent_primitivo = raster_primitivo.extent()
        extent_modificado = raster_modificado.extent()

        if extent_primitivo.isEmpty() or extent_modificado.isEmpty():
            return falha(self.tr("Um dos rasters possui extensão vazia ou inválida."))

        intersection_extent = extent_primitivo.intersect(extent_modificado)

        if intersection_extent.isEmpty():
            return falha(self.tr("Os rasters não possuem área de interseção.\n"
                "Verifique se eles estão na mesma região espacial."))

        # Valida apenas se as resoluções são numericamente válidas.
        # Diferença de resolução/alinhamento será tratada como aviso no momento do cálculo.
        resolution_x = abs(raster_primitivo.rasterUnitsPerPixelX())
        resolution_y = abs(raster_primitivo.rasterUnitsPerPixelY())

        resolution_x_mod = abs(raster_modificado.rasterUnitsPerPixelX())
        resolution_y_mod = abs(raster_modificado.rasterUnitsPerPixelY())

        if resolution_x <= 0 or resolution_y <= 0:
            return falha(self.tr("O raster primitivo '{raster_name}' possui resolução inválida.").format(raster_name=raster_primitivo.name()))

        if resolution_x_mod <= 0 or resolution_y_mod <= 0:
            return falha(self.tr("O raster modificado '{raster_name}' possui resolução inválida.").format(raster_name=raster_modificado.name()))

        width = int(round(intersection_extent.width() / resolution_x))
        height = int(round(intersection_extent.height() / resolution_y))

        if width <= 0 or height <= 0:
            return falha(self.tr("A área de interseção entre os rasters é menor que a resolução do raster primitivo."))

        return {
            "ok": True,
            "mensagem": "",
            "raster_primitivo": raster_primitivo,
            "raster_modificado": raster_modificado,
            "intersection_extent": intersection_extent,
            "width": width,
            "height": height}

    def confirmar_grade_diferente_para_calculo(self, raster_primitivo, raster_modificado):
        """
        Verifica se resolução/grade dos rasters são compatíveis.
        Se não forem, avisa o usuário e permite decidir se deseja continuar.
        """
        grade_ok, mensagem_grade = self._validar_resolucao_e_grade_rasters(
            raster_primitivo,
            raster_modificado)

        if grade_ok:
            return True

        resposta = QMessageBox.question(self,
            self.tr("Atenção: rasters com grade diferente"),
            self.tr(
                "{mensagem_grade}\n\n"
                "O cálculo ainda pode ser executado usando a grade de saída do raster primitivo, "
                "mas o resultado deve ser conferido tecnicamente.\n\n"
                "Deseja continuar mesmo assim?"
            ).format(mensagem_grade=mensagem_grade),
            QMessageBox.StandardButton.Yes | QMessageBox.StandardButton.No,
            QMessageBox.StandardButton.No)

        return resposta == QMessageBox.StandardButton.Yes

    def calculate_raster_difference(self):
        validacao = self._validar_rasters_para_calculo(mostrar_mensagem=True)

        if not validacao["ok"]:
            return

        raster_primitivo = validacao["raster_primitivo"]
        raster_modificado = validacao["raster_modificado"]
        intersection_extent = validacao["intersection_extent"]
        width = validacao["width"]
        height = validacao["height"]

        # Se resolução ou grade forem diferentes, apenas avisa o usuário.
        # Não bloqueia o botão Calcular.
        if not self.confirmar_grade_diferente_para_calculo(raster_primitivo, raster_modificado):
            self.mostrar_mensagem(self.tr("Cálculo cancelado pelo usuário."), "Erro", 3)
            return

        # Definir o caminho de saída para o raster resultante
        temp_fd, temp_path = tempfile.mkstemp(suffix='.tif')
        os.close(temp_fd)  # Fechar o arquivo temporário

        # Criar as entradas para o QgsRasterCalculator
        entries = []

        entry_primitivo = QgsRasterCalculatorEntry()
        entry_primitivo.raster = raster_primitivo
        entry_primitivo.bandNumber = 1  # Usar a banda 1
        entry_primitivo.ref = 'primitivo@1'
        entries.append(entry_primitivo)

        entry_modificado = QgsRasterCalculatorEntry()
        entry_modificado.raster = raster_modificado
        entry_modificado.bandNumber = 1  # Usar a banda 1
        entry_modificado.ref = 'modificado@1'
        entries.append(entry_modificado)

        # Expressão de cálculo: -(primitivo - modificado)
        expression = '-1 * (primitivo@1 - modificado@1)'

        # Barra de progresso percentual real do QgsRasterCalculator
        progress_bar, progress_message = self.iniciar_progress_bar(100, titulo = self.tr("Calculando diferença entre MDTs"), formato = self.tr("%p% - calculando raster"))

        # Criar o objeto QgsRasterCalculator para realizar a operação
        calculator = QgsRasterCalculator(expression, temp_path, 'GTiff', intersection_extent, width, height, entries, QgsProject.instance().transformContext())

        feedback = QgsFeedback()

        def atualizar_progresso(valor):
            """
            Atualiza a barra usando o progresso informado pelo QgsRasterCalculator.
            """
            try:
                progress_bar.setValue(int(valor))
                QCoreApplication.processEvents()
            except RuntimeError:
                pass  # nosec B110

        feedback.progressChanged.connect(atualizar_progresso)

        start_time = time.time()
        result = None
        erro_ja_mostrado = False

        try:
            self.pushButtonCalcular.setEnabled(False)
            QApplication.setOverrideCursor(Qt.CursorShape.WaitCursor)

            progress_bar.setValue(1)
            QCoreApplication.processEvents()

            # Em QGIS recentes, processCalculation aceita QgsFeedback.
            # O fallback mantém compatibilidade caso alguma versão não aceite o argumento.
            try:
                result = calculator.processCalculation(feedback)

            except Exception as e:
                result = QgsRasterCalculator.Result.CalculationError
                erro_ja_mostrado = True
                self.mostrar_mensagem(self.tr("Erro inesperado ao calcular o raster: {error}").format(error=str(e)), "Erro", 3)

            progress_bar.setValue(100)

        finally:
            QApplication.restoreOverrideCursor()

            try:
                self.iface.messageBar().popWidget(progress_message)
            except Exception:
                pass  # nosec B110

            self.verificar_condicoes_calculo()

        total_time = time.time() - start_time

        if result != QgsRasterCalculator.Result.Success:
            if not erro_ja_mostrado:
                self.mostrar_mensagem(self.tr("Erro ao calcular a diferença dos rasters: {result}").format(result=str(result)), "Erro", 3)
            return
    
        # Adicionar o raster resultante ao projeto e obter a camada resultante
        result_layer = self.add_result_raster_to_project(temp_path, raster_primitivo.name(), raster_modificado.name())

        # Se o checkBoxPoligono estiver selecionado e a camada resultante for válida, gera a camada de polígonos
        if self.checkBoxPoligono.isChecked() and result_layer:
            self.gerar_camadas_poligono_custom(result_layer, raster_modificado.name())

        # Exibe mensagem de sucesso com o tempo total gasto
        self.mostrar_mensagem(self.tr("Sucesso: raster calculado em {total_time:.2f} segundos.").format(total_time=total_time), "Sucesso", 3)

    def confirmar_poligonizacao_por_pixel(self, raster_layer, width, height):
        """
        Confirma com o usuário antes de gerar polígonos por pixel.
        Evita travamentos quando o raster possui muitos pixels.
        """
        total_pixels = int(width * height)

        limite_aviso = 100_000
        limite_alto = 500_000
        limite_bloqueio = 2_000_000

        nome_raster = raster_layer.name() if isinstance(raster_layer, QgsRasterLayer) else "Raster"

        # Bloqueio de segurança para evitar travamento pesado do QGIS
        if total_pixels >= limite_bloqueio:
            total_pixels_formatado = f"{total_pixels:,}".replace(",", ".")

            QMessageBox.critical(
                self,
                self.tr("Poligonização muito pesada"),
                self.tr(
                    "O raster '{nome_raster}' possui aproximadamente {total_pixels} pixels.\n\n"
                    "Gerar um polígono para cada pixel pode travar o QGIS ou deixar o projeto muito pesado.\n\n"
                    "A operação foi bloqueada por segurança.\n\n"
                    "Sugestão: recorte o raster, reduza a resolução ou use uma poligonização por classes."
                ).format(
                    nome_raster=nome_raster,
                    total_pixels=total_pixels_formatado))
            return False

        # Aviso para rasters grandes
        if total_pixels >= limite_aviso:
            if total_pixels >= limite_alto:
                titulo = self.tr("Poligonização pesada")
                nivel = self.tr("alto")
            else:
                titulo = self.tr("Confirmar poligonização")
                nivel = self.tr("moderado")

            total_pixels_formatado = f"{total_pixels:,}".replace(",", ".")

            resposta = QMessageBox.question(
                self,
                titulo,
                self.tr(
                    "O raster '{nome_raster}' possui aproximadamente {total_pixels} pixels.\n\n"
                    "O risco de lentidão é {nivel}, pois esta rotina cria até um polígono para cada pixel válido.\n\n"
                    "Isso pode deixar o QGIS lento, gerar uma tabela de atributos muito grande "
                    "e aumentar bastante o tempo de processamento.\n\n"
                    "Deseja continuar mesmo assim?").format(
                    nome_raster=nome_raster,
                    total_pixels=total_pixels_formatado,
                    nivel=nivel),
                QMessageBox.StandardButton.Yes | QMessageBox.StandardButton.No,
                QMessageBox.StandardButton.No)

            if resposta != QMessageBox.StandardButton.Yes:
                return False

        return True

    def gerar_camadas_poligono_custom(self, raster_layer, nome_mdt_modificado=None):
        """
        Gera polígonos agrupados por setores contínuos
        de corte e aterro.

        Cada setor contíguo vira uma única feição.

        Campos:
        ID      = identificador do setor
        Classe  = Corte / Aterro
        Value   = diferença média do setor
        Area    = área total do setor
        Volume  = volume total do setor
        Pixels  = quantidade de pixels agrupados
        """
        start_time = time.time()

        tolerancia_zero = 0.000001

        origem = (raster_layer.source()
            or "").split("|", 1)[0]

        dataset = gdal.Open(origem, gdal.GA_ReadOnly)

        if dataset is None:
            self.mostrar_mensagem(self.tr("Não foi possível abrir o raster para gerar os setores de corte e aterro."), "Erro", 3)
            return

        band = dataset.GetRasterBand(1)
        valores = band.ReadAsArray()

        if valores is None:
            dataset = None

            self.mostrar_mensagem(self.tr("Não foi possível ler os valores do raster."), "Erro", 3)
            return

        valores = np.asarray(valores, dtype=np.float64)
        height, width = valores.shape

        pixelSizeX = abs(raster_layer.rasterUnitsPerPixelX())
        pixelSizeY = abs(raster_layer.rasterUnitsPerPixelY())

        area_pixel = (pixelSizeX * pixelSizeY)

        nodata = band.GetNoDataValue()

        # 1. CLASSIFICAÇÃO
        #
        # -1 = Corte
        #  0 = Sem alteração / NoData
        #  1 = Aterro
        validos = np.isfinite(valores)

        if nodata is not None:
            validos &= ~np.isclose(valores, float(nodata), rtol=0.0, atol=1e-12)

        classes = np.zeros(valores.shape, dtype=np.int8)

        classes[validos
            & (valores < -tolerancia_zero)] = -1

        classes[validos
            & (valores > tolerancia_zero)] = 1

        candidatos = np.argwhere(classes != 0)

        if candidatos.size == 0:
            dataset = None

            self.mostrar_mensagem(self.tr("Não foram encontrados setores de corte ou aterro no raster."), "Aviso", 3)
            return

        progress_bar, progress_message = (self.iniciar_progress_bar(100, titulo=self.tr("Agrupando setores de corte e aterro"), formato=self.tr("%p% - agrupando pixels contíguos")))

        QApplication.setOverrideCursor(Qt.CursorShape.WaitCursor)

        caminho_rotulos = None

        try:
            # 2. IDENTIFICA SETORES CONTÍGUOS
            #
            # Cada número positivo em "rotulos"
            # representa um setor independente.
            rotulos = np.zeros(valores.shape, dtype=np.int32)
            setores = {}

            proximo_id = 0

            total_candidatos = len(candidatos)

            for indice, coordenada in enumerate(candidatos):
                row = int(coordenada[0])
                col = int(coordenada[1])

                # Já pertence a algum setor
                if rotulos[row, col] != 0:
                    continue

                proximo_id += 1

                classe = int(classes[row, col])

                fila = deque()
                fila.append((row, col))

                rotulos[row, col] = proximo_id

                soma_valores = 0.0
                quantidade_pixels = 0

                # Agrupamento por vizinhança lateral
                # cima / baixo / esquerda / direita
                while fila:
                    r, c = fila.popleft()

                    soma_valores += float(valores[r, c])

                    quantidade_pixels += 1

                    vizinhos = (
                        (r - 1, c),
                        (r + 1, c),
                        (r, c - 1),
                        (r, c + 1))

                    for nr, nc in vizinhos:
                        if (nr < 0
                            or nr >= height
                            or nc < 0
                            or nc >= width):
                            continue

                        if (rotulos[nr, nc] == 0
                            and classes[nr, nc] == classe):
                            rotulos[nr, nc] = proximo_id

                            fila.append((nr, nc))

                setores[proximo_id
                ] = {"classe": classe,
                    "pixels": quantidade_pixels,
                    "soma_valores": soma_valores,
                    "area": (quantidade_pixels * area_pixel),
                    "volume": (soma_valores * area_pixel)}

                if (indice % 2000 == 0
                    or indice
                    == total_candidatos - 1):
                    percentual = int(45.0 * (indice + 1) / max(1, total_candidatos))

                    progress_bar.setValue(percentual)

                    QCoreApplication.processEvents()

            progress_bar.setValue(50)
            QCoreApplication.processEvents()

            # 3. CRIA RASTER TEMPORÁRIO
            # Cada setor possui um ID diferente.
            fd, caminho_rotulos = (tempfile.mkstemp(suffix="_setores.tif"))

            os.close(fd)

            # Remove o arquivo vazio criado pelo mkstemp
            # para o GDAL poder criá-lo corretamente.
            try:
                os.remove(caminho_rotulos)
            except Exception:
                pass  # nosec B110

            driver = gdal.GetDriverByName("GTiff")

            ds_rotulos = driver.Create(
                caminho_rotulos,
                width,
                height,
                1,
                gdal.GDT_Int32,
                options=["COMPRESS=LZW"])

            if ds_rotulos is None:
                raise Exception(self.tr("Não foi possível criar o raster temporário de setores."))

            ds_rotulos.SetGeoTransform(dataset.GetGeoTransform())
            projecao = (dataset.GetProjection())

            if not projecao:
                projecao = (raster_layer.crs().toWkt())

            if projecao:
                ds_rotulos.SetProjection(projecao)

            band_rotulos = (ds_rotulos.GetRasterBand(1))

            band_rotulos.WriteArray(rotulos)

            # Zero não será poligonizado
            band_rotulos.SetNoDataValue(0)

            band_rotulos.FlushCache()
            ds_rotulos.FlushCache()

            band_rotulos = None
            ds_rotulos = None
            dataset = None

            progress_bar.setValue(60)
            QCoreApplication.processEvents()

            # 4. POLIGONIZA OS SETORES
            # Como cada setor possui um ID único, cada região contínua vira uma feição.

            resultado = processing.run(
                "gdal:polygonize",
                {"INPUT": caminho_rotulos,
                    "BAND": 1,
                    "FIELD": "ID",
                    "EIGHT_CONNECTEDNESS": False,
                    "EXTRA": "",
                    "OUTPUT": "TEMPORARY_OUTPUT"})

            saida_poligonos = resultado.get("OUTPUT")

            if isinstance(saida_poligonos, QgsVectorLayer):
                camada_setores_temp = (saida_poligonos)

            else:
                camada_setores_temp = (
                    QgsVectorLayer(
                        saida_poligonos,
                        "setores_temp",
                        "ogr"))

            if (not camada_setores_temp
                or not camada_setores_temp.isValid()):
                raise Exception(self.tr("Não foi possível converter os setores raster em polígonos."))

            progress_bar.setValue(75)
            QCoreApplication.processEvents()

            # 5. CAMADA FINAL
            campos = QgsFields()

            campos.append(QgsField("ID", QMetaType.Type.Int))
            campos.append(QgsField("Classe", QMetaType.Type.QString))
            campos.append(QgsField("Value", QMetaType.Type.Double))
            campos.append(QgsField("Area", QMetaType.Type.Double))
            campos.append(QgsField("Volume", QMetaType.Type.Double))
            campos.append(QgsField("Pixels", QMetaType.Type.Int))

            nome_base_poligono = self.tr("Poligono_{raster_name}").format(raster_name=(nome_mdt_modificado
                    or raster_layer.name()))

            nome_poligono = (self.get_unique_layer_name(nome_base_poligono))

            camada_poligono = QgsVectorLayer(("Polygon?crs="
                    f"{raster_layer.crs().authid()}"), nome_poligono, "memory")

            pr = (camada_poligono.dataProvider())
            pr.addAttributes(campos)
            camada_poligono.updateFields()

            features_saida = []
            features_temp = list(camada_setores_temp.getFeatures())

            total_setores = len(features_temp)

            for indice, feat_temp in enumerate(features_temp):
                try:
                    setor_id = int(feat_temp["ID"])

                except (KeyError, TypeError, ValueError):
                    setor_id = None

                if setor_id is None:
                    continue

                dados = setores.get(setor_id)

                if dados is None:
                    continue

                quantidade_pixels = int(dados["pixels"])

                if quantidade_pixels <= 0:
                    continue

                # Valor representativo do setor:
                # diferença média dos pixels.
                valor_medio = (float( dados["soma_valores"]) / quantidade_pixels)

                classe = int(dados["classe"])

                tipo = (self.tr("Corte")
                    if classe < 0
                    else self.tr("Aterro"))

                feat = QgsFeature(camada_poligono.fields())

                feat.setGeometry(feat_temp.geometry())

                feat.setAttributes([setor_id, tipo, valor_medio, float(dados["area"]), float(dados["volume"]), quantidade_pixels])

                features_saida.append(feat)

                if (len(features_saida) >= 500
                    or indice == total_setores - 1):
                    if features_saida:
                        pr.addFeatures(features_saida)

                        features_saida.clear()

                if (indice % 250 == 0
                    or indice == total_setores - 1):
                    percentual = (75 + int(20.0 * (indice + 1) / max(1, total_setores)))

                    progress_bar.setValue(percentual )

                    QCoreApplication.processEvents()

            camada_poligono.updateExtents()

            # Mantém Corte = vermelho
            # e Aterro = azul
            self.aplicar_estilo_atribuido(camada_poligono)

            self.add_layer_to_group(camada_poligono, self.tr("Calculados"))

            progress_bar.setValue(100)

            total_time = (time.time() - start_time)

            self.mostrar_mensagem(self.tr("Camada de setores gerada com sucesso. {setores} setores em {total_time:.2f} segundos!").format(setores=(camada_poligono.featureCount()), total_time=total_time), "Sucesso", 3)

        except Exception as e:
            self.mostrar_mensagem(self.tr("Erro ao gerar setores de corte e aterro: {error}").format(error=str(e)), "Erro", 3)

        finally:
            QApplication.restoreOverrideCursor()

            try:
                self.iface.messageBar().popWidget(progress_message)
            except Exception:
                pass  # nosec B110

            dataset = None

            if (caminho_rotulos
                and os.path.exists(caminho_rotulos)):

                try:
                    os.remove(caminho_rotulos)
                except Exception:
                    pass  # nosec B110

    def aplicar_estilo_atribuido(self, camada_poligono):
        """
        Aplica um estilo de coloração atribuído a uma camada de polígonos baseado nos valores dos pixels.

        Passos detalhados:
        1. Cria uma lista para armazenar os intervalos de renderização.
        2. Cria símbolos de preenchimento para pixels positivos, negativos e nulos.
        3. Adiciona intervalos de renderização para cada tipo de símbolo.
        4. Cria um renderizador graduado com base nos intervalos de valores.
        5. Aplica o renderizador à camada de polígonos.

        Parâmetros:
        - camada_poligono: Camada de polígonos a ser estilizada.

        Retorna:
        - None
        """
        ranges = []  # Cria uma lista para armazenar os intervalos de renderização

        # Cria símbolos de preenchimento para pixels positivos, negativos e nulos
        symbol_positive = QgsFillSymbol.createSimple({'color': 'blue', 'outline_color': 'blue'})  # Azul para pixels positivos
        symbol_negative = QgsFillSymbol.createSimple({'color': 'red', 'outline_color': 'red'})  # Vermelho para pixels negativos
        symbol_zero = QgsFillSymbol.createSimple({'color': 'gray', 'outline_color': 'gray'})  # Cinza para pixels nulos

        # Adiciona intervalos de renderização para cada tipo de símbolo
        tolerancia_zero = 0.000001

        ranges.append(
            QgsRendererRange(
                float("-inf"),
                -tolerancia_zero,
                symbol_negative,
                self.tr("Menor que 0 - Corte")))

        ranges.append(
            QgsRendererRange(
                -tolerancia_zero,
                tolerancia_zero,
                symbol_zero,
                self.tr("Igual a 0 - Sem alterações")))

        ranges.append(
            QgsRendererRange(
                tolerancia_zero,
                float("inf"),
                symbol_positive,
                self.tr("Maior que 0 - Aterro")))

        renderer = QgsGraduatedSymbolRenderer('Value', ranges)  # Cria um renderizador graduado com base nos intervalos de valores
        camada_poligono.setRenderer(renderer)  # Aplica o renderizador à camada de polígonos

    def _obter_nodata_banda(self, raster_layer, band=1):
        """
        Obtém o valor NoData da banda informada, quando existir.
        Retorna None se a camada não tiver NoData definido.
        """
        if not isinstance(raster_layer, QgsRasterLayer):
            return None

        provider = raster_layer.dataProvider()

        try:
            if hasattr(provider, "sourceHasNoDataValue"):
                if not provider.sourceHasNoDataValue(band):
                    return None
        except Exception:
            pass  # nosec B110

        try:
            if hasattr(provider, "sourceNoDataValue"):
                return provider.sourceNoDataValue(band)
        except Exception:
            pass  # nosec B110

        return None

    def _valor_raster_invalido_ou_nodata(self, valor, nodata=None, tolerancia=1e-12):
        """
        Verifica se um valor raster é inválido, NaN, infinito ou NoData.
        """
        if valor is None:
            return True

        try:
            valor_float = float(valor)
        except (TypeError, ValueError):
            return True

        # Ignora NaN e infinito
        if math.isnan(valor_float) or math.isinf(valor_float):
            return True

        if nodata is not None:
            try:
                nodata_float = float(nodata)

                if math.isnan(nodata_float):
                    return math.isnan(valor_float)

                if math.isclose(valor_float, nodata_float, rel_tol=0.0, abs_tol=tolerancia):
                    return True

            except (TypeError, ValueError):
                pass  # nosec B110

        return False

    def calculate_volume(self):
        """
        Calcula os volumes de corte e aterro usando GDAL + NumPy,
        com barra de progresso durante o processamento.
        Ignora corretamente NoData, None, NaN e infinito.
        """
        selected_items = self.listWidgetRasters.selectedItems()

        if not selected_items:
            return

        selected_item = selected_items[0]
        layer_id = selected_item.data(Qt.ItemDataRole.UserRole)
        raster_layer = QgsProject.instance().mapLayer(layer_id)

        if not isinstance(raster_layer, QgsRasterLayer):
            self.mostrar_mensagem(self.tr("A camada selecionada não é um raster válido."), "Erro", 3)
            return

        layer_name = raster_layer.name()

        # Fatores independentes de ajuste volumétrico
        fator_corte = (self.doubleSpinBoxEmpolamentoCorte.value())
        fator_aterro = (self.doubleSpinBoxEmpolamentoAterro.value())

        # Caminho físico do raster
        raster_path = raster_layer.source().split("|")[0]

        if not raster_path or not os.path.exists(raster_path):
            self.mostrar_mensagem(self.tr("Não foi possível localizar o arquivo físico do raster para calcular o volume."), "Erro", 3)
            return

        dataset = None

        progress_bar, progress_message = self.iniciar_progress_bar(
            100,
            titulo = self.tr("Calculando volumes"),
            formato = self.tr("%p% - processando raster"))

        try:
            self.pushButtonVolume.setEnabled(False)
            QApplication.setOverrideCursor(Qt.CursorShape.WaitCursor)

            progress_bar.setValue(5)
            QCoreApplication.processEvents()

            dataset = gdal.Open(raster_path, gdal.GA_ReadOnly)

            if dataset is None:
                self.mostrar_mensagem(self.tr("Não foi possível abrir o raster com GDAL."), "Erro", 3)
                return

            progress_bar.setValue(15)
            QCoreApplication.processEvents()

            band = 1
            band_obj = dataset.GetRasterBand(band)

            if band_obj is None:
                self.mostrar_mensagem(self.tr("Não foi possível acessar a banda 1 do raster."), "Erro", 3)
                return

            progress_bar.setValue(25)
            QCoreApplication.processEvents()

            array = band_obj.ReadAsArray()

            if array is None:
                self.mostrar_mensagem(self.tr("Não foi possível ler os valores do raster."), "Erro", 3)
                return

            progress_bar.setValue(45)
            QCoreApplication.processEvents()

            # Converte para float64 para permitir NaN e evitar estouro numérico
            array = array.astype(np.float64, copy=False)

            pixel_size_x = abs(raster_layer.rasterUnitsPerPixelX())
            pixel_size_y = abs(raster_layer.rasterUnitsPerPixelY())
            area_pixel = pixel_size_x * pixel_size_y

            if area_pixel <= 0:
                self.mostrar_mensagem(self.tr("O raster possui resolução inválida para cálculo de área."), "Erro", 3)
                return

            progress_bar.setValue(55)
            QCoreApplication.processEvents()

            # NoData pelo GDAL; se não existir, tenta pelo provider do QGIS
            nodata = band_obj.GetNoDataValue()

            if nodata is None:
                nodata = self._obter_nodata_banda(raster_layer, band)

            # Máscara inicial: remove NaN e infinito
            mascara_valida = np.isfinite(array)

            # Remove NoData, quando existir
            if nodata is not None:
                try:
                    nodata_float = float(nodata)

                    if math.isnan(nodata_float):
                        mascara_valida &= ~np.isnan(array)
                    else:
                        mascara_valida &= ~np.isclose(
                            array,
                            nodata_float,
                            rtol=0.0,
                            atol=1e-12)

                except (TypeError, ValueError):
                    pass  # nosec B110

            progress_bar.setValue(70)
            QCoreApplication.processEvents()

            valores_validos = array[mascara_valida]

            pixels_validos = int(valores_validos.size)
            pixels_totais = int(array.size)
            pixels_ignorados = pixels_totais - pixels_validos

            if pixels_validos == 0:
                self.mostrar_mensagem(self.tr("Nenhum pixel válido encontrado para calcular o volume. Verifique o raster ou o valor NoData."), "Erro", 3)
                return

            progress_bar.setValue(80)
            QCoreApplication.processEvents()

            volumes = valores_validos * area_pixel

            total_corte = float(volumes[volumes < 0].sum())
            total_aterro = float(volumes[volumes > 0].sum())

            total_corte_ajustado = (total_corte * fator_corte)
            total_aterro_ajustado = (total_aterro * fator_aterro)

            progress_bar.setValue(92)
            QCoreApplication.processEvents()

            self.fill_table_view_volumes(
                layer_name,
                total_corte,
                total_aterro,
                total_corte_ajustado,
                total_aterro_ajustado,
                fator_corte,
                fator_aterro)

            progress_bar.setValue(100)
            QCoreApplication.processEvents()

            self.mostrar_mensagem(self.tr("Volume calculado com sucesso. Pixels válidos: {pixels_validos}. Pixels ignorados: {pixels_ignorados}.").format(pixels_validos=pixels_validos, pixels_ignorados=pixels_ignorados), "Sucesso", 3)

        except Exception as e:
            self.mostrar_mensagem(self.tr("Erro ao calcular o volume: {error}").format(error=str(e)), "Erro", 3)

        finally:
            dataset = None

            try:
                QApplication.restoreOverrideCursor()
            except Exception:
                pass  # nosec B110

            try:
                self.iface.messageBar().popWidget(progress_message)
            except Exception:
                pass  # nosec B110

            self.verificar_selecao_volume()
            self.verificar_dados_excel()

    def salvar_estado_table_volumes(self):
        """
        Salva os resultados exibidos no tableViewVolumes
        dentro do projeto QGIS.
        """
        model = self.tableViewVolumes.model()
        project = QgsProject.instance()

        if (model is None
            or model.rowCount() == 0):
            try:
                project.removeEntry("TempoSalvoTools", "VolumeManager/tableViewVolumes")
            except Exception:
                pass  # nosec B110

            return

        dados = []

        row = 0

        while row < model.rowCount():
            nome_item = model.item(row, 0)

            if (nome_item is None
                or not nome_item.text().strip()):
                row += 1
                continue

            if row + 1 >= model.rowCount():
                break

            dados.append({
                "layer_name": nome_item.text(),
                "volume_corte": model.index(row, 2).data() or "",
                "fator_corte": model.index(row, 3).data() or "",
                "volume_corte_ajustado": model.index(row, 4).data() or "",
                "volume_aterro": model.index(row + 1, 2).data() or "",
                "fator_aterro": model.index(row + 1, 3).data() or "",
                "volume_aterro_ajustado": model.index(row + 1, 4).data() or ""})

            row += 2

        try:
            project.writeEntry("TempoSalvoTools", "VolumeManager/tableViewVolumes", json.dumps(dados, ensure_ascii=False))

        except Exception:
            pass  # nosec B110


    def carregar_estado_table_volumes(self):
        """
        Restaura os resultados anteriormente armazenados
        no projeto QGIS.
        """
        project = QgsProject.instance()

        try:
            texto, ok = project.readEntry("TempoSalvoTools", "VolumeManager/tableViewVolumes", "")

        except Exception:
            texto = ""
            ok = False

        if (not ok
            or not texto):
            self.tableViewVolumes.setModel(None)
            self.apply_table_style()
            self.verificar_dados_excel()
            return

        try:
            dados = json.loads(texto)

        except (TypeError, ValueError, json.JSONDecodeError):
            dados = []

        if not dados:
            self.tableViewVolumes.setModel(None)
            self.apply_table_style()
            self.verificar_dados_excel()
            return

        model = QStandardItemModel()

        model.setHorizontalHeaderLabels([
            self.tr("Nome da Camada"),
            self.tr("Descrição"),
            self.tr("Volume Geométrico (m³)"),
            self.tr("Fator"),
            self.tr("Volume Ajustado (m³)")])

        for registro in dados:
            nome = QStandardItem(str(registro.get("layer_name", "")))

            model.appendRow([nome,
                QStandardItem(self.tr("Corte")),
                QStandardItem(str(registro.get("volume_corte", ""))),
                QStandardItem(str(registro.get("fator_corte", ""))),
                QStandardItem(str(registro.get("volume_corte_ajustado", "")))])

            model.appendRow([
                QStandardItem(""),
                QStandardItem(self.tr("Aterro")),
                QStandardItem(str(registro.get("volume_aterro", ""))),
                QStandardItem(str(registro.get("fator_aterro", ""))),
                QStandardItem(str(registro.get("volume_aterro_ajustado", "")))])

        self.tableViewVolumes.setModel(model)

        for row in range(model.rowCount()):
            for column in range(model.columnCount()):
                item = model.item(row, column)

                if item is not None:
                    item.setFlags(item.flags()
                        & ~Qt.ItemFlag.ItemIsEditable)

        self.reaplicar_spans_table_volumes()
        self.apply_table_style()
        self.tableViewVolumes.resizeColumnsToContents()
        self.verificar_dados_excel()

    def fill_table_view_volumes(self, layer_name, total_corte, total_aterro, total_corte_ajustado, total_aterro_ajustado, fator_corte, fator_aterro):
        """
        Preenche a tabela com volumes geométricos e ajustados,
        utilizando fatores independentes para corte e aterro.
        """
        model = self.tableViewVolumes.model()

        if model is None:
            model = QStandardItemModel()

            model.setHorizontalHeaderLabels([
                self.tr("Nome da Camada"),
                self.tr("Descrição"),
                self.tr("Volume Geométrico (m³)"),
                self.tr("Fator"),
                self.tr("Volume Ajustado (m³)")])

            self.tableViewVolumes.setModel(model)

        start_row = model.rowCount()

        corte_item = QStandardItem(self.tr("Corte"))
        aterro_item = QStandardItem(self.tr("Aterro"))

        # Volumes geométricos
        volume_corte = QStandardItem(f"{abs(total_corte):.3f}")
        volume_aterro = QStandardItem(f"{total_aterro:.3f}")

        # Fatores independentes
        fator_corte_item = QStandardItem(f"{fator_corte:.3f}")
        fator_aterro_item = QStandardItem(f"{fator_aterro:.3f}")

        # Volumes ajustados
        volume_corte_ajustado = QStandardItem(f"{abs(total_corte_ajustado):.3f}")

        volume_aterro_ajustado = QStandardItem(f"{total_aterro_ajustado:.3f}")

        name_item = QStandardItem(layer_name)

        # Corte
        model.appendRow([
            name_item,
            corte_item,
            volume_corte,
            fator_corte_item,
            volume_corte_ajustado])

        # Aterro
        model.appendRow([
            QStandardItem(""),
            aterro_item,
            volume_aterro,
            fator_aterro_item,
            volume_aterro_ajustado])

        # Mescla o nome da camada nas duas linhas
        self.tableViewVolumes.setSpan(start_row, 0, 2, 1)

        # Mantém a tabela não editável
        for row in range(model.rowCount()):
            for column in range(model.columnCount()):
                item = model.item(row, column)

                if item is not None:
                    item.setFlags(item.flags()
                        & ~Qt.ItemFlag.ItemIsEditable)

        self.apply_table_style()
        self.tableViewVolumes.resizeColumnsToContents()
        self.verificar_dados_excel()

        # Persiste os resultados no projeto
        self.salvar_estado_table_volumes()

    def apply_table_style(self):
        """
        Aplica o estilo de borda ao tableViewVolumes.
        """
        self.tableViewVolumes.setAlternatingRowColors(True)
        self.tableViewVolumes.setStyleSheet("""
            QTableView {
                gridline-color: black;
                border: 1px solid gray;
                background-color: #ffffff;
                alternate-background-color: #f2f2f2;  /* Cor para as linhas alternadas */
            }
            QHeaderView::section {
                background-color: #d3d3d3;
                font-weight: bold;
            }
        """)

    def reset_table_view(self):
        """
        Limpa os dados do tableViewVolumes
        e remove os resultados persistidos no projeto.
        """
        self.tableViewVolumes.clearSpans()
        self.tableViewVolumes.setModel(None)

        try:
            QgsProject.instance().removeEntry( "TempoSalvoTools", "VolumeManager/tableViewVolumes")
        except Exception:
            pass  # nosec B110

        self.apply_table_style()
        self.verificar_dados_excel()

    def reaplicar_spans_table_volumes(self):
        """
        Reaplica as mesclagens da coluna 'Nome da Camada' após exclusões.
        Cada camada ocupa duas linhas: Corte e Aterro.
        """
        model = self.tableViewVolumes.model()

        # Remove todos os spans antigos
        self.tableViewVolumes.clearSpans()

        if model is None or model.rowCount() == 0:
            return

        row = 0
        while row < model.rowCount():
            item_nome = model.item(row, 0)

            # A linha principal da camada tem nome preenchido
            if item_nome is not None and item_nome.text().strip():
                if row + 1 < model.rowCount():
                    self.tableViewVolumes.setSpan(row, 0, 2, 1)
                row += 2
            else:
                row += 1

        self.tableViewVolumes.resizeColumnsToContents()

    def setup_table_view(self):
        # Aplica o DeleteButtonDelegate na primeira coluna, passando também o manager
        delegate = DeleteButtonDelegate(self.tableViewVolumes, self)
        self.tableViewVolumes.setItemDelegateForColumn(0, delegate)

        # Configura a tabela para não ser editável
        self.tableViewVolumes.setEditTriggers(QAbstractItemView.EditTrigger.NoEditTriggers)

        # Aplica estilo personalizado à tabela
        self.apply_table_style()

    def escolher_local_para_salvar(self, nome_padrao, tipo_arquivo):
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
        fileName, _ = QFileDialog.getSaveFileName(
            self,
            self.tr("Salvar Camada"),
            nome_completo_proposto,
            tipo_arquivo)

        # Verifica se um nome de arquivo foi escolhido
        if fileName:
            # Atualiza o último diretório usado nas configurações do QGIS
            settings.setValue("lastDir", os.path.dirname(fileName))

            # Assegura que o arquivo tenha a extensão correta
            if not fileName.endswith(extensao):
                fileName += extensao

        return fileName  # Retorna o caminho completo do arquivo escolhido ou None se cancelado

    def exportar_tabela_para_excel(self):
        """
        Exporta o conteúdo do tableViewVolumes para um arquivo Excel, garantindo que números sejam exportados
        sem formatação de divisão de milhar e como números.
        Se o checkBoxSalvar estiver selecionado, abre a caixa de diálogo para escolher o local de salvamento.
        Caso contrário, salva em um local temporário e abre o Excel automaticamente.
        """
        # Nome e tipo de arquivo padrão
        nome_padrao = self.tr("volumes_exportados.xlsx")
        tipo_arquivo = self.tr("Excel Files (*.xlsx)")

        if self.checkBoxSalvar.isChecked():
            # Abre a caixa de diálogo para escolher o local de salvamento
            fileName = self.escolher_local_para_salvar(nome_padrao, tipo_arquivo)
        else:
            # Cria um caminho temporário para salvar o arquivo Excel
            temp_fd, fileName = tempfile.mkstemp(suffix=".xlsx")
            os.close(temp_fd)  # Fecha o arquivo temporário

        if fileName:
            # Obtém o modelo da tabela do tableViewVolumes
            model = self.tableViewVolumes.model()

            # Cria uma lista para armazenar os dados
            dados_tabela = []

            # Percorre todas as linhas e colunas do modelo
            for row in range(model.rowCount()):
                linha_dados = []

                for col in range(model.columnCount()):
                    valor_celula = model.index(row, col).data()

                    try:
                        valor_celula = float(valor_celula)
                    except (ValueError, TypeError):
                        pass  # nosec B110

                    linha_dados.append(valor_celula)

                dados_tabela.append(linha_dados)

            # Cria o DataFrame com a coluna adicional de empolamento
            df = pd.DataFrame(
                dados_tabela,
                columns=[
                    self.tr("Nome da Camada"),
                    self.tr("Descrição"),
                    self.tr("Volume Geométrico (m³)"),
                    self.tr("Fator"),
                    self.tr("Volume Ajustado (m³)")])

            # Salva o DataFrame no arquivo Excel
            try:
                with pd.ExcelWriter(fileName, engine="xlsxwriter") as writer:
                    nome_planilha = self.tr("Volumes")
                    df.to_excel(writer, index=False, sheet_name=nome_planilha, header=False, startrow=1)

                    workbook = writer.book
                    worksheet = writer.sheets[nome_planilha]

                    # Formatos
                    formato_cabecalho = workbook.add_format({
                        'bold': True,
                        'border': 1,
                        'align': 'center',
                        'valign': 'vcenter'})

                    formato_texto = workbook.add_format({
                        'border': 1})

                    formato_volume = workbook.add_format({
                        'border': 1,
                        'num_format': '0.000'})

                    formato_fator = workbook.add_format({
                        'border': 1,
                        'num_format': '0.000'})

                    # Cabeçalhos
                    for col, cabecalho in enumerate(df.columns):
                        worksheet.write(0, col, cabecalho, formato_cabecalho)

                    # Dados
                    for linha in range(len(df)):
                        for coluna in range(len(df.columns)):
                            valor = df.iloc[linha, coluna]

                            if pd.isna(valor):
                                worksheet.write_blank(linha + 1, coluna, None, formato_texto)

                            elif coluna in (2, 4):
                                worksheet.write_number(
                                    linha + 1,
                                    coluna,
                                    float(valor),
                                    formato_volume)

                            elif coluna == 3:
                                worksheet.write_number(
                                    linha + 1,
                                    coluna,
                                    float(valor),
                                    formato_fator)

                            else:
                                worksheet.write(linha + 1, coluna, valor, formato_texto)

                    # Ajuste das larguras das colunas
                    worksheet.set_column(0, 0, 34)
                    worksheet.set_column(1, 1, 14)
                    worksheet.set_column(2, 2, 24)
                    worksheet.set_column(3, 3, 12)
                    worksheet.set_column(4, 4, 24)

                if self.checkBoxSalvar.isChecked():
                    # Mensagem de sucesso se o usuário escolheu salvar
                    self.mostrar_mensagem(self.tr("Exportação concluída com sucesso: {file_name}").format(file_name=fileName), "Sucesso")
                else:
                    # Abre o arquivo temporário no aplicativo padrão do sistema.
                    abriu = QDesktopServices.openUrl(
                        QUrl.fromLocalFile(os.path.abspath(os.fspath(fileName))))

                    if abriu:
                        self.mostrar_mensagem(
                            self.tr("A tabela foi exportada e aberta no Excel temporariamente."), "Sucesso")
                    else:
                        self.mostrar_mensagem(self.tr("A tabela foi exportada, mas não foi possível abrir o arquivo automaticamente."), "Erro")

            except Exception as e:
                self.mostrar_mensagem(self.tr("Erro ao salvar o arquivo Excel: {error}").format(error=str(e)), "Erro")

    def verificar_selecao_volume(self):
        """
        Verifica se há uma camada raster selecionada no listWidgetRasters
        e ativa/desativa o botão pushButtonVolume.
        """
        selected_items = self.listWidgetRasters.selectedItems()

        if not selected_items:
            self.pushButtonVolume.setEnabled(False)
            return

        selected_item = selected_items[0]
        layer_id = selected_item.data(Qt.ItemDataRole.UserRole)
        layer = QgsProject.instance().mapLayer(layer_id)

        self.pushButtonVolume.setEnabled(isinstance(layer, QgsRasterLayer))

    def verificar_dados_excel(self):
        """
        Verifica se há dados no tableViewVolumes e ativa/desativa o pushButtonExcel.
        """
        model = self.tableViewVolumes.model()
        if model is None or model.rowCount() == 0:
            self.pushButtonExcel.setEnabled(False)
        else:
            self.pushButtonExcel.setEnabled(True)

    def verificar_condicoes_calculo(self):
        """
        Verifica as condições para ativar/desativar o botão pushButtonCalcular.
        Também atualiza o tooltip com o motivo quando o botão estiver desabilitado.
        """
        validacao = self._validar_rasters_para_calculo(mostrar_mensagem=False)

        if validacao["ok"]:
            self.pushButtonCalcular.setEnabled(True)
            self.pushButtonCalcular.setToolTip(self.tr("Calcular diferença entre os MDTs selecionados."))
        else:
            self.pushButtonCalcular.setEnabled(False)
            self.pushButtonCalcular.setToolTip(validacao["mensagem"])

class DeleteButtonDelegate(QStyledItemDelegate):
    def __init__(self, parent=None, manager=None):
        super(DeleteButtonDelegate, self).__init__(parent)
        self.parent = parent
        self.manager = manager

    def paint(self, painter, option, index):
        super(DeleteButtonDelegate, self).paint(painter, option, index)

        # Renderizar o ícone de deletar somente na célula que contém o nome da camada
        if index.isValid() and index.column() == 0:
            cell_data = index.data()

            if cell_data:
                rect = option.rect
                icon_rect = QRect(rect.left() + 3, rect.top() + 3, 10, 10)

                painter.save()
                painter.setRenderHint(QPainter.RenderHint.Antialiasing)

                # Quadrado vermelho com borda azul
                painter.setPen(QPen(QColor(0, 0, 255), 2))
                painter.setBrush(QBrush(QColor(255, 0, 0, 200)))
                painter.drawRoundedRect(icon_rect, 2, 2)

                # X branco
                painter.setPen(QPen(QColor(255, 255, 255), 2))
                painter.drawLine(
                    icon_rect.topLeft() + QPoint(2, 2),
                    icon_rect.bottomRight() - QPoint(2, 2))
                painter.drawLine(
                    icon_rect.topRight() + QPoint(-2, 2),
                    icon_rect.bottomLeft() + QPoint(2, -2))

                painter.restore()

    def editorEvent(self, event, model, option, index):
        if not index.isValid() or index.column() != 0:
            return super(DeleteButtonDelegate, self).editorEvent(event, model, option, index)

        if event.type() == QEvent.Type.MouseButtonRelease:
            rect = option.rect
            icon_rect = QRect(rect.left() + 3, rect.top() + 3, 10, 10)

            if icon_rect.contains(event.pos()):
                # Só permite deletar se a célula tem nome de camada
                cell_data = index.data()
                if not cell_data:
                    return True

                row_to_remove = index.row()

                # Garante que remove sempre o par correto: Corte + Aterro
                if row_to_remove % 2 != 0:
                    row_to_remove -= 1

                rows_left = model.rowCount() - row_to_remove
                rows_to_remove = min(2, rows_left)

                if rows_to_remove > 0:
                    model.removeRows(row_to_remove, rows_to_remove)

                # Se acabou tudo, reseta a tabela pelo VolumeManager
                if model.rowCount() == 0:
                    if self.manager is not None:
                        self.manager.reset_table_view()
                    else:
                        model.clear()

                    return True

                # Se ainda existem dados, reorganiza os spans e atualiza o botão Excel
                if self.manager is not None:
                    self.manager.reaplicar_spans_table_volumes()
                    self.manager.salvar_estado_table_volumes()
                    self.manager.verificar_dados_excel()

                return True

        return super(DeleteButtonDelegate, self).editorEvent(event, model, option, index)

class ListDeleteButtonDelegate(QStyledItemDelegate):
    def __init__(self, parent=None, manager=None):
        super(ListDeleteButtonDelegate, self).__init__(parent)
        self.parent = parent
        self.manager = manager

    def paint(self, painter, option, index):
        if index.isValid():
            # Evita desenhar o botão no item de cabeçalho
            if index.row() == 0:
                return super(ListDeleteButtonDelegate, self).paint(painter, option, index)

            # Determinar a cor de fundo com base no estado
            if option.state & QStyle.StateFlag.State_Selected:
                background_color = QColor("#00aaff")  # Azul normal para item selecionado
            elif option.state & QStyle.StateFlag.State_MouseOver:
                background_color = QColor("#aaffff")  # Azul claro quando o mouse está sobre o item
            else:
                background_color = option.palette.base().color()

            painter.fillRect(option.rect, background_color)

            # Calcula as posições
            rect = option.rect
            icon_size = 11
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
            painter.setPen(QPen(QColor(0, 0, 255), 2))  # Cor da borda do quadrado
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
            # Definir a cor do texto com base no fundo para melhor contraste
            if option.state & QStyle.StateFlag.State_Selected:
                text_color = QColor('black')
            else:
                text_color = option.palette.text().color()

            painter.setPen(text_color)
            font = painter.font()
            font.setPointSize(10)  # Ajusta o tamanho da fonte se necessário
            painter.setFont(font)
            text = index.data(Qt.ItemDataRole.DisplayRole)
            painter.drawText(text_rect, Qt.AlignmentFlag.AlignVCenter | Qt.TextFlag.TextSingleLine, text)
            painter.restore()
        else:
            super(ListDeleteButtonDelegate, self).paint(painter, option, index)

    def editorEvent(self, event, model, option, index):
        # Evita interações com o item de cabeçalho
        if not index.isValid() or index.row() == 0:
            return False

        if event.type() == QEvent.Type.MouseButtonRelease:
            rect = option.rect
            icon_size = 12
            icon_margin = 4

            icon_rect = QRect(
                rect.left() + icon_margin,
                rect.top() + (rect.height() - icon_size) // 2,
                icon_size,
                icon_size)

            if icon_rect.contains(event.pos()):
                layer_id = index.data(Qt.ItemDataRole.UserRole)

                if not layer_id:
                    return True

                project = QgsProject.instance()
                root = project.layerTreeRoot()
                group = root.findGroup(self.tr("Calculados"))

                # Remove primeiro o nó da camada dentro do grupo,
                # para evitar que o grupo fique com nó órfão.
                if group is not None:
                    layer_node = group.findLayer(layer_id)
                    if layer_node is not None:
                        group.removeChildNode(layer_node)

                # Remove a camada do projeto
                if project.mapLayer(layer_id) is not None:
                    project.removeMapLayer(layer_id)

                # Atualiza/remover o grupo depois que o QGIS terminar os sinais internos
                if self.manager is not None:
                    QTimer.singleShot(0, self.manager.remover_grupo_calculados_se_vazio)
                    QTimer.singleShot(120, self.manager.atualizar_canvas_qgis)

                    self.manager.verificar_selecao_volume()

                    if hasattr(self.manager, "textEditInfo"):
                        self.manager.textEditInfo.setHtml("<p><b>{}</b></p>".format(QCoreApplication.translate("calcularVolumeMDT", "Nenhuma camada selecionada.")))
                else:
                    model.removeRow(index.row())

                return True

        return super(ListDeleteButtonDelegate, self).editorEvent(event, model, option, index)