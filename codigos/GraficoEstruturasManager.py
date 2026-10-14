from qgis.PyQt.QtWidgets import QDockWidget, QTableWidgetItem, QTableWidget, QAbstractItemView, QInputDialog, QDialog, QListWidgetItem, QProgressBar, QApplication, QWidget, QGroupBox, QVBoxLayout, QStyledItemDelegate, QStyle, QFileDialog, QPushButton
from qgis.core import QgsProject, QgsRasterLayer, Qgis, QgsVectorLayer, QgsWkbTypes, QgsFeature, QgsGeometry, QgsPointXY, QgsField, QgsLayerTreeLayer, QgsFields, QgsLayerTreeGroup, QgsRaster, QgsPalLayerSettings, QgsProperty, QgsVectorLayerSimpleLabeling, QgsSymbolLayer, QgsTextFormat, QgsTextBufferSettings, QgsUnitTypes, QgsMapLayer, QgsVectorFileWriter, QgsCoordinateTransformContext, QgsCoordinateTransform, QgsRectangle, QgsMessageLog
from qgis.PyQt.QtCore import Qt, QVariant, QRect, QPoint, QPointF, QEvent, QItemSelection, QItemSelectionModel, QSettings, QTimer, QMetaType, QCoreApplication, QUrl
from qgis.PyQt.QtGui import QPainter, QStandardItemModel, QStandardItem, QBrush, QColor, QFont, QPen, QCursor, QDesktopServices
from matplotlib.backends.backend_qt5agg import FigureCanvasQTAgg as FigureCanvas
from matplotlib.offsetbox import OffsetImage, AnnotationBbox
from matplotlib.backends.backend_pdf import PdfPages
from matplotlib.patches import Circle, Wedge
import matplotlib.patches as mpatches
from matplotlib.figure import Figure
from matplotlib.lines import Line2D
from pyqtgraph import PlotWidget
import matplotlib.pyplot as plt
from qgis.utils import iface
import matplotlib.patches
from qgis.PyQt import uic
import pyqtgraph as pg
import numpy as np
import sqlite3
import ezdxf
import time
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
    os.path.dirname(__file__), 'GraficoEstruturaSolar.ui'))

class UserCancelled(Exception):
    """Sinal interno para abortar uma operação longa quando o usuário cancela um diálogo."""
    pass

class EstruturasManager(QDockWidget, FORM_CLASS):
    def __init__(self, parent=None):
        """Constructor."""
        super(EstruturasManager, self).__init__(parent)
        # Configura a interface do usuário a partir do Designer.
        self.setupUi(self)

        # Altera o título da janela
        self.setWindowTitle(self.tr("Gráficos de Estruturas Solar"))

        # Armazena a referência da interface QGIS
        self.iface = iface

        # Adiciona o dock widget à interface QGIS na parte inferior
        iface.addDockWidget(Qt.DockWidgetArea.BottomDockWidgetArea, self)

        # Atributos de controle para seleção bidirecional
        self.selected_layer = None     # Armazena a camada atualmente exibida na tabela
        self.feature_ids = []          # Lista dos IDs das feições (para indexar as linhas da tabela)
        # Cache: FID -> row (para sincronização rápida mapa -> tabela)
        self._fid_to_row = {}

        # Inicializa a variável para armazenar a camada atualmente selecionada
        self.current_estruturas_layer = None  

        # Configura o comportamento de seleção da tabela
        self.tableWidget_Dados1.setSelectionBehavior(QAbstractItemView.SelectionBehavior.SelectRows)
        self.tableWidget_Dados1.setSelectionMode(QAbstractItemView.SelectionMode.MultiSelection)

        # Inicializa o ComboBox de Raster e Camadas
        self.init_combo_box_raster()
        self.init_combo_box_pontos()

        # Se já existe alguma camada de pontos, carrega a tabela de imediato
        if self.comboBoxPontos.count() > 0:
            self.load_table_widget_dados1()

        # Configura o gráfico ao iniciar
        self.setup_graph()

        # Configurações do listWidget_Lista
        self.listWidget_Lista.setItemDelegate(ListDeleteButtonDelegate(self.listWidget_Lista))
        self.listWidget_Lista.setMouseTracking(True)
        self.listWidget_Lista.setSelectionBehavior(QAbstractItemView.SelectionBehavior.SelectItems)
        self.listWidget_Lista.setSelectionMode(QAbstractItemView.SelectionMode.SingleSelection)

        # current_dir é criar_vetor/codigos
        current_dir = os.path.dirname(os.path.abspath(__file__))
        # plugin_dir agora será criar_vetor
        self.plugin_dir = os.path.dirname(current_dir)

        # Chama a função uma vez para garantir que o estado inicial seja atualizado corretamente
        self.atualizar_estado_botoes_calcular()

        # Chama a função uma vez para garantir que o estado inicial seja atualizado corretamente
        self.atualizar_estado_botao()

        self.support_layers = []  # ou como for definido

        self._altimetria_fields = {}  # cache: layer.id() -> nome do campo de altimetria

        # Certifique-se de criar o container e o dicionário de widgets, se necessário:
        self.dados_container = QWidget()
        self.dados_layout = QVBoxLayout(self.dados_container)
        self.scrollAreaDADOS.setWidget(self.dados_container)
        self.scrollAreaDADOS.setWidgetResizable(True)
        self.support_widgets = {}  # Chave: layer.id(), Valor: widget (group box)

        self.update_horizontalScrollBarSelec() #VERIFICAR A NECESSIDADE
        self.update_pushButtonSeq_state(self.spinBoxSelec.value())

        self.style_horizontal_scrollbar()  # Aplica o estilo

        self._lock_messagebar = False #Bloqueia as Mensagens

        self.pushButtonPDF.setEnabled(False)

        # Conecta os sinais aos slots
        self.connect_signals()

    def tr(self, message):
        """
        Traduz textos deste diálogo.
        O contexto precisa ser estável para o Qt Linguist encontrar as traduções.
        """
        return QCoreApplication.translate("EstruturasManager", message)

    def connect_signals(self):

        # Conecta o sinal de alteração de nome
        for layer in QgsProject.instance().mapLayers().values():
            layer.nameChanged.connect(self.on_layer_name_changed)

        # Conecta o sinal de mudança de seleção no comboBoxPontos
        self.comboBoxPontos.currentIndexChanged.connect(self.load_table_widget_dados1)

        # Conecta a mudança de seleção na tabela
        self.tableWidget_Dados1.itemSelectionChanged.connect(self.table_selection_changed)

        self.pushButtonCalcular.clicked.connect(self.calcular)

        self.listWidget_Lista.itemSelectionChanged.connect(self.on_listwidget_selection_changed)
        self.doubleSpinBox_1.valueChanged.connect(self.recalc_current_layer)
        self.doubleSpinBox_2.valueChanged.connect(self.recalc_current_layer)

        self.listWidget_Lista.setItemDelegate(ListDeleteButtonDelegate(self.listWidget_Lista))

        self.pushButtonMat.clicked.connect(self.plot_layers)

        # Sempre verificar o estado do botão quando houver mudanças
        self.listWidget_Lista.itemSelectionChanged.connect(self.atualizar_estado_botao)
        self.comboBoxRaster.currentIndexChanged.connect(self.atualizar_estado_botao)

        self.spinBoxSelec.valueChanged.connect(self.on_spinBoxSelec_value_changed)

        # Conecta o botão pushButtonSeq a uma função:
        self.pushButtonSeq.clicked.connect(self.on_pushButtonSeq_clicked)

        self.spinBoxSelec.valueChanged.connect(self.update_pushButtonSeq_state)

        self.horizontalScrollBarSelec.valueChanged.connect(self.on_horizontalScrollBarSelec_value_changed)

        # Botão Calcular Tudo
        self.pushButtonCalculaTudo.clicked.connect(self.calcular_tudo)

        # Conectar o botão pushButtonExportarDXF
        self.pushButtonExportarDXF.clicked.connect(self.pushButtonExportarDXF_clicked)

        # Fecha o diálogo
        self.pushButtonFecharD.clicked.connect(self.close)

        # Atualizar tabela e gráfico quando parâmetros mudarem
        self.doubleSpinBoxComp.valueChanged.connect(self.on_spin_parameters_changed)
        self.doubleSpinBoxPadrao.valueChanged.connect(self.on_spin_parameters_changed)
        self.doubleSpinBoxVaria.valueChanged.connect(self.on_spin_parameters_changed)
        self.spinBoxQ.valueChanged.connect(self.on_spin_parameters_changed)

        # Exportar todas as camadas do grupo 'Estruturas' para GeoPackage
        self.pushButtonExportarGPKG.clicked.connect(self.pushButtonExportarGPKG_clicked)

        # Abrir GeoPackage de Estruturas
        self.pushButtonAdicionar.clicked.connect(self.pushButtonAdicionar_clicked)

        self.pushButtonPDF.clicked.connect(self.exportar_pdf_estruturas)

        # Escolher logotipo personalizado
        self.pushButtonLogo.clicked.connect(self.pushButtonLogo_clicked)

    def showEvent(self, event):
        """
        Sobrescreve o evento de exibição do diálogo para resetar os Widgets.
        """
        super(EstruturasManager, self).showEvent(event)

        self._connect_project_signals()

        # Reseta o gráfico sempre que o diálogo for exibido
        self.reset_graph()

        # Reseta o tableView_2
        self.tableView_2.setModel(None)

        # Reseta o listWidget_inc
        self.listWidget_inc.clear()

        # Se houver pelo menos uma camada de pontos no comboBox, já carregar a tabela
        if self.comboBoxPontos.count() > 0:
            # Opcionalmente, forçar seleção do primeiro índice:
            self.load_table_widget_dados1()
        else:
            # Se não há camadas, limpa a tabela
            self.tableWidget_Dados1.clear()
            self.tableWidget_Dados1.setRowCount(0)
            self.tableWidget_Dados1.setColumnCount(0)

        # Atualiza o listWidget com as camadas do grupo 'Estruturas'
        self.update_list_widget_estruturas()
        
        # Atualiza o botão pushButtonExportarDXF 
        self.atualizar_estado_pushButtonExportarDXF()
        
        # Inicializa estado do botão Exportar GPKG
        self.atualizar_estado_pushButtonExportarGPKG()

        self.atualizar_estado_pushButtonPDF()

    def closeEvent(self, event):
        """
        Quando o diálogo/dock é fechado, removemos toda a sincronização de seleção
        para evitar travadinhas quando o usuário tinha muitas feições selecionadas.
        """
        # sinaliza cancelamento
        self._calc_tudo_cancelled = True

        # desconecta e limpa
        self._disconnect_project_signals()
        self._disconnect_layer_name_signals()
        self._disconnect_graph_signals()
        self._resetar_sincronizacao_selecao()
        self._clear_progress_bar_if_any()
        self._dispose_support_layers_on_close()

        super(EstruturasManager, self).closeEvent(event)

    def _connect_project_signals(self):
        # Evita conectar duas vezes
        if getattr(self, "_project_signals_connected", False):
            return

        prj = QgsProject.instance()

        # callbacks principais
        self._sig_layers_added_main = self.on_layers_added
        self._sig_layers_removed_main = self.on_layers_removed

        # callbacks para atualizar Exportar DXF (sem lambda)
        self._sig_layers_added_exportar = self._on_project_layers_changed_exportar
        self._sig_layers_removed_exportar = self._on_project_layers_changed_exportar

        for sig, cb in (
            (prj.layersAdded, self._sig_layers_added_main),
            (prj.layersRemoved, self._sig_layers_removed_main),
            (prj.layersAdded, self._sig_layers_added_exportar),
            (prj.layersRemoved, self._sig_layers_removed_exportar)):
            try:
                sig.connect(cb)
            except Exception:
                pass  # nosec B110

        self._project_signals_connected = True

    def _disconnect_project_signals(self):
        prj = QgsProject.instance()

        for attr, sig in (
            ("_sig_layers_added_main", prj.layersAdded),
            ("_sig_layers_removed_main", prj.layersRemoved),
            ("_sig_layers_added_exportar", prj.layersAdded),
            ("_sig_layers_removed_exportar", prj.layersRemoved)):
            cb = getattr(self, attr, None)
            if cb:
                try:
                    sig.disconnect(cb)
                except Exception:
                    pass  # nosec B110
                setattr(self, attr, None)

        self._project_signals_connected = False

    def _on_project_layers_changed_exportar(self, *args):
        """
        Callback do projeto: ao adicionar/remover camadas, atualiza o estado do botão Exportar DXF.
        Aceita *args porque layersAdded e layersRemoved têm assinaturas diferentes.
        """
        try:
            self.atualizar_estado_pushButtonExportarDXF()
        except Exception:
            pass  # nosec B110

    def _clear_progress_bar_if_any(self):
        try:
            if self._w_alive(getattr(self, "_calc_tudo_progressMsg", None)):
                self.iface.messageBar().popWidget(self._calc_tudo_progressMsg)
        except Exception:
            pass  # nosec B110
        self._calc_tudo_progressBar = None
        self._calc_tudo_progressMsg = None
        self._lock_messagebar = False

    def _dispose_support_layers_on_close(self):
        if hasattr(self, "support_layers"):
            # remover referências para permitir GC (não estão no projeto)
            self.support_layers.clear()

    def _disconnect_graph_signals(self):
        try:
            self.graphWidget.scene().sigMouseMoved.disconnect(self.mouse_moved)
        except Exception:
            pass  # nosec B110
        # Remova overlays para GC mais fácil
        for attr in ("vLine", "hLine", "coord_text"):
            if hasattr(self, attr) and getattr(self, attr):
                try:
                    self.graphWidget.removeItem(getattr(self, attr))
                except Exception:
                    pass  # nosec B110
                setattr(self, attr, None)

    def _disconnect_layer_name_signals(self):
        # Desconecta nameChanged de todas as camadas onde foi conectado
        for layer in QgsProject.instance().mapLayers().values():
            try:
                layer.nameChanged.disconnect(self.on_layer_name_changed)
            except Exception:
                pass  # nosec B110

    def _resetar_sincronizacao_selecao(self):
        # 1) Desconecta da camada atual, se existir
        if getattr(self, "selected_layer", None):
            try:
                self.selected_layer.selectionChanged.disconnect(self.on_map_selection_changed)
            except Exception:
                pass  # nosec B110

        # 2) Limpa seleção da tabela
        if self.tableWidget_Dados1.selectionModel():
            self._block_table_selection_signals(True)
            self.tableWidget_Dados1.clearSelection()
            self._block_table_selection_signals(False)

        # 3) Zera o spinBox
        self.spinBoxSelec.blockSignals(True)
        self.spinBoxSelec.setValue(0)
        self.spinBoxSelec.blockSignals(False)

        # 4) Reseta o scrollbar (se estiver usando bloco de seleção)
        self.horizontalScrollBarSelec.blockSignals(True)
        self.horizontalScrollBarSelec.setValue(0)
        self.horizontalScrollBarSelec.blockSignals(False)

        # 5) Não temos mais camada “ativa” para sincronizar
        self.selected_layer = None

    def style_horizontal_scrollbar(self):
        """
        Aplica um estilo moderno e com efeito 3D ao horizontalScrollBarSelec.
        Agora um pouco mais fino e ajustado.
        """
        style = """
        QScrollBar:horizontal {
            border: 1px solid #999;
            background: qlineargradient(x1:0, y1:0, x2:1, y2:0,
                                        stop:0 #f2f2f2, stop:1 #e6e6e6);
            height: 14px; /* 🔹 Altura reduzida para ficar mais fino */
            margin: 0px 18px 0px 18px; /* Ajuste para os botões laterais */
            border-radius: 3px;
        }

        /* 'Handle' (pegador) com efeito 3D e borda arredondada */
        QScrollBar::handle:horizontal {
            background: qlineargradient(x1:0, y1:0, x2:0, y2:1,
                                        stop:0 #88b7f0, stop:1 #568dd6);
            border: 1px solid #666;
            min-width: 20px;
            border-radius: 4px;
            margin: 1px;
        }

        /* Hover no handle para efeito de realce */
        QScrollBar::handle:horizontal:hover {
            background: qlineargradient(x1:0, y1:0, x2:0, y2:1,
                                        stop:0 #aad7ff, stop:1 #6aa3ee);
        }

        /* Botão esquerdo (sub-line) */
        QScrollBar::sub-line:horizontal {
            border: 1px solid #666;
            background: qlineargradient(x1:0, y1:0, x2:0, y2:1,
                                        stop:0 #cfcfcf, stop:1 #a9a9a9);
            width: 18px;
            subcontrol-position: left;
            subcontrol-origin: margin;
            border-radius: 3px;
        }

        /* Botão direito (add-line) */
        QScrollBar::add-line:horizontal {
            border: 1px solid #666;
            background: qlineargradient(x1:0, y1:0, x2:0, y2:1,
                                        stop:0 #cfcfcf, stop:1 #a9a9a9);
            width: 18px;
            subcontrol-position: right;
            subcontrol-origin: margin;
            border-radius: 3px;
        }

        /* Remove as setas padrão */
        QScrollBar::up-arrow:horizontal, QScrollBar::down-arrow:horizontal {
            width: 0;
            height: 0;
        }

        /* Fundo entre o handle e os botões */
        QScrollBar::add-page:horizontal, QScrollBar::sub-page:horizontal {
            background: none;
        }
        """

        self.horizontalScrollBarSelec.setStyleSheet(style)

    def update_pushButtonSeq_state(self, value):
        if value == 0:
            self.pushButtonSeq.setEnabled(False)
        else:
            self.pushButtonSeq.setEnabled(True)

    def update_horizontalScrollBarSelec(self):
        """
        Atualiza o horizontalScrollBarSelec para que o range dele
        leve em conta o tamanho do bloco (singleStep).
        Assim, quando estivermos pulando de 5 em 5, o último valor
        do scroll será 'row_count - 5', e não 'row_count'.
        """
        row_count = self.tableWidget_Dados1.rowCount()

        # tamanho do bloco atual (quantas linhas quero selecionar por vez)
        step = self.horizontalScrollBarSelec.singleStep()
        if step <= 0:
            step = 1

        self.horizontalScrollBarSelec.blockSignals(True)
        self.horizontalScrollBarSelec.setMinimum(0)

        if row_count == 0:
            max_val = 0
        else:
            # último início possível de bloco
            # ex.: 50 linhas, step=10 -> último início = 40
            max_val = max(0, row_count - step)

        self.horizontalScrollBarSelec.setMaximum(max_val)
        self.horizontalScrollBarSelec.setPageStep(step)
        self.horizontalScrollBarSelec.blockSignals(False)

    def on_pushButtonSeq_clicked(self):
        # Lê o valor atual do spinBoxSelec
        step_val = self.spinBoxSelec.value()
        if step_val <= 0:
            step_val = 1

        # Define o singleStep do horizontalScrollBarSelec
        self.horizontalScrollBarSelec.setSingleStep(step_val)

        # Recalcula o range do scrollbar com esse novo passo
        self.update_horizontalScrollBarSelec()

    def on_horizontalScrollBarSelec_value_changed(self, new_val):
        """
        Ao mover o horizontalScrollBarSelec, selecionamos um bloco de linhas
        do tableWidget_Dados1 com tamanho = singleStep() do scroll.
        Agora o valor do scroll é travado para não passar do último bloco possível.
        """
        row_count = self.tableWidget_Dados1.rowCount()
        if row_count == 0:
            return

        step = self.horizontalScrollBarSelec.singleStep()
        if step <= 0:
            step = 1

        # último início possível de bloco
        max_start = max(0, row_count - step)

        # garante que não passe do fim
        start_row = min(max(new_val, 0), max_start)
        end_row = min(start_row + step - 1, row_count - 1)

        # bloqueia sinais pra não disparar de volta
        self._block_table_selection_signals(True)
        self.tableWidget_Dados1.clearSelection()

        for row in range(start_row, end_row + 1):
            self.tableWidget_Dados1.selectRow(row)

        self._block_table_selection_signals(False)

        # sincroniza com a camada
        self.table_selection_changed()

        # (opcional) rolar pra ficar visível
        item = self.tableWidget_Dados1.item(start_row, 0)
        if item:
            self.tableWidget_Dados1.scrollToItem( item, QAbstractItemView.ScrollHint.PositionAtCenter)

    def _get_selected_layer_safe(self):
        """
        Retorna self.selected_layer se ainda estiver viva (não deletada no C++).
        Caso contrário, zera self.selected_layer e retorna None.
        """
        lyr = getattr(self, "selected_layer", None)
        if not self._w_alive(lyr):
            self.selected_layer = None
            return None
        return lyr

    def table_selection_changed(self):
        """
        Quando a seleção muda na tabela, selecionamos as feições correspondentes na camada.
        """
        layer = self._get_selected_layer_safe()
        if layer is None:
            return

        # Obtém as linhas selecionadas na tabela
        selected_rows = self.tableWidget_Dados1.selectionModel().selectedRows()

        # Mapeia as linhas selecionadas para os IDs de feição
        selected_feature_ids = []
        for index in selected_rows:
            row = index.row()
            item = self.tableWidget_Dados1.item(row, 0)  # Pegamos o item da primeira coluna
            if item is not None:
                fid = item.data(Qt.ItemDataRole.UserRole)
                if fid is not None:
                    selected_feature_ids.append(fid)

        # Aplica a seleção na camada
        layer.selectByIds(selected_feature_ids)
        
        # Atualiza o spinBoxSelec com a quantidade de feições selecionadas
        self.update_spinBoxSelec()

        # Atualiza o estado do pushButtonSeq
        self.update_pushButtonSeq_state(self.spinBoxSelec.value())
        self.atualizar_estado_botoes_calcular()

    def _block_table_selection_signals(self, block: bool):
        """Bloqueia sinais do QTableWidget e do selectionModel (motor da seleção)."""
        try:
            self.tableWidget_Dados1.blockSignals(block)
        except Exception:
            pass  # nosec B110

        sm = None
        try:
            sm = self.tableWidget_Dados1.selectionModel()
        except Exception:
            sm = None

        if sm:
            try:
                sm.blockSignals(block)
            except Exception:
                pass  # nosec B110

    def on_map_selection_changed(self, selected, deselected, clearAndSelect):
        """
        Quando o usuário seleciona feições no mapa (canvas),
        sincroniza essa seleção com o tableWidget_Dados1.
        """
        layer = self._get_selected_layer_safe()
        if layer is None:
            return

        # FIDs atualmente selecionados na camada
        try:
            selected_fids = set(layer.selectedFeatureIds())
        except RuntimeError:
            # camada morreu entre o check e o acesso
            self.selected_layer = None
            return

        # Evita disparar callbacks enquanto ajustamos (tabela + selectionModel)
        self._block_table_selection_signals(True)

        fid_to_row = getattr(self, "_fid_to_row", {}) or {}

        # Usa o payload do sinal quando for "clear and select" (geralmente seleções grandes)
        try:
            if clearAndSelect:
                selected_fids = list(selected)  # já é a seleção “final” desse evento
            else:
                selected_fids = layer.selectedFeatureIds()
        except RuntimeError:
            self.selected_layer = None
            return

        # Seleciona na tabela em lote (rápido)
        self._select_table_rows_by_fids_fast(selected_fids)

        # Atualiza contagem sem varrer selectedRows() (evita custo extra)
        n_selected = len(selected_fids)
        self.spinBoxSelec.blockSignals(True)
        self.spinBoxSelec.setValue(n_selected)
        self.spinBoxSelec.blockSignals(False)
        self._prev_spin_box_selec = n_selected

        self.atualizar_estado_botoes_calcular()
        self.update_pushButtonSeq_state(n_selected)

    def update_spinBoxSelec(self):
        """Atualiza o spinBoxSelec com o número correto de linhas selecionadas."""
        if self.tableWidget_Dados1.selectionModel():
            selected_rows = self.tableWidget_Dados1.selectionModel().selectedRows()
            count = len(selected_rows)

            # Bloquear sinais para evitar loop
            self.spinBoxSelec.blockSignals(True)
            self.spinBoxSelec.setValue(count)
            self.spinBoxSelec.blockSignals(False)

            # Atualizar variável de controle
            self._prev_spin_box_selec = count
        else:
            self.spinBoxSelec.blockSignals(True)
            self.spinBoxSelec.setValue(0)
            self.spinBoxSelec.blockSignals(False)
            self._prev_spin_box_selec = 0

        # 🔹 Atualiza o estado do botão pushButtonSeq ao alterar o spinBox
        self.update_pushButtonSeq_state(self.spinBoxSelec.value())

    def on_spinBoxSelec_value_changed(self, new_val):
        """
        Quando o valor do spinBoxSelec é alterado,
        a seleção na tabela é ajustada para que o bloco contíguo
        de linhas selecionadas aumente ou diminua de acordo.
        Se não houver seleção, começa do 0.
        Após a alteração, a seleção é sincronizada com a camada do QGIS.
        """
        # Obter o número de linhas atualmente selecionadas
        sel_model = self.tableWidget_Dados1.selectionModel()
        if not sel_model:
            return
        current_selected = sorted([index.row() for index in sel_model.selectedRows()])
        current_count = len(current_selected)

        # Bloqueia sinais para evitar loop
        self._block_table_selection_signals(True)
        
        # Se não há seleção, comece do 0
        if current_count == 0:
            start = 0
            last_selected = -1  # Nenhuma linha selecionada ainda
        else:
            # Assumindo que a seleção seja contígua; usamos o maior índice selecionado
            start = current_selected[0]
            last_selected = current_selected[-1]

        diff = new_val - current_count

        if diff > 0:
            # Queremos aumentar a seleção: adicionar 'diff' linhas após a última selecionada.
            for i in range(diff):
                next_row = last_selected + 1 if last_selected >= 0 else 0
                if next_row < self.tableWidget_Dados1.rowCount():
                    # Seleciona a linha 'next_row'
                    self.tableWidget_Dados1.selectRow(next_row)
                    last_selected = next_row
                else:
                    # Se não há mais linhas disponíveis, saia do loop.
                    break
        elif diff < 0:
            # Queremos diminuir a seleção: remover 'abs(diff)' linhas, removendo a última linha selecionada cada vez.
            for i in range(-diff):
                # Reobter a lista de linhas selecionadas (em ordem decrescente)
                sel_rows = sorted([index.row() for index in self.tableWidget_Dados1.selectionModel().selectedRows()], reverse=True)
                if sel_rows:
                    row_to_remove = sel_rows[0]
                    index = self.tableWidget_Dados1.model().index(row_to_remove, 0)
                    self.tableWidget_Dados1.selectionModel().select(index, QItemSelectionModel.SelectionFlag.Deselect | QItemSelectionModel.SelectionFlag.Rows)
                else:
                    break

        # Desbloqueia os sinais da tabela
        self._block_table_selection_signals(False)

        # Atualiza o spinBoxSelec para refletir a nova contagem
        new_count = len(self.tableWidget_Dados1.selectionModel().selectedRows())
        self.spinBoxSelec.blockSignals(True)
        self.spinBoxSelec.setValue(new_count)
        self._prev_spin_box_selec = new_count
        self.spinBoxSelec.blockSignals(False)

        # Atualiza a seleção na camada do QGIS para sincronizar com a tabela
        self.table_selection_changed()

    def _select_more_features(self, count):
        """Seleciona mais `count` feições na tabela."""
        total_rows = self.tableWidget_Dados1.rowCount()
        
        # Obtém as linhas já selecionadas
        selected_rows = {index.row() for index in self.tableWidget_Dados1.selectionModel().selectedRows()}
        
        # Bloqueia sinais para evitar recursão infinita
        self._block_table_selection_signals(True)

        # Seleciona mais linhas
        for row in range(total_rows):
            if len(selected_rows) >= count:
                break
            if row not in selected_rows:
                self.tableWidget_Dados1.selectRow(row)
                selected_rows.add(row)

        self._block_table_selection_signals(False)

    def _deselect_some_features(self, count):
        """Deselects `count` rows from the selection."""
        selected_rows = sorted(index.row() for index in self.tableWidget_Dados1.selectionModel().selectedRows())

        # Bloqueia sinais para evitar recursão infinita
        self._block_table_selection_signals(True)

        for _ in range(count):
            if selected_rows:
                row = selected_rows.pop()
                self.tableWidget_Dados1.selectionModel().select(
                    self.tableWidget_Dados1.model().index(row, 0),
                    QItemSelectionModel.SelectionFlag.Deselect)

        self._block_table_selection_signals(False)

    def load_table_widget_dados1(self):
        """
        Carrega a tabela (tableWidget_Dados1) a partir da camada selecionada no comboBoxPontos,
        preservando a seleção de feições e evitando cascatas de sinais (tabela, spinBox e QGIS)
        durante o carregamento.
        """
        layer_id = self.comboBoxPontos.currentData()
        layer = QgsProject.instance().mapLayer(layer_id)

        # Se a camada não for válida, limpa a tabela e retorna
        if not layer or not isinstance(layer, QgsVectorLayer) or layer.geometryType() != QgsWkbTypes.GeometryType.PointGeometry:
            try:
                if getattr(self, "selected_layer", None) is not None:
                    self.selected_layer.selectionChanged.disconnect(self.on_map_selection_changed)
            except Exception:
                pass  # nosec B110

            self.tableWidget_Dados1.clear()
            self.tableWidget_Dados1.setRowCount(0)
            self.tableWidget_Dados1.setColumnCount(0)
            self.selected_layer = None
            self.feature_ids = []
            self._fid_to_row = {}
            self.spinBoxSelec.blockSignals(True)
            self.spinBoxSelec.setMaximum(0)
            self.spinBoxSelec.setValue(0)
            self.spinBoxSelec.blockSignals(False)
            self._prev_spin_box_selec = 0
            return

        # Salva a seleção atual da camada (antes de qualquer coisa)
        saved_selection = list(layer.selectedFeatureIds())

        # Desconecta temporariamente para não disparar on_map_selection_changed durante o load
        try:
            if getattr(self, "selected_layer", None) is not None:
                self.selected_layer.selectionChanged.disconnect(self.on_map_selection_changed)
        except Exception:
            pass  # nosec B110
        try:
            layer.selectionChanged.disconnect(self.on_map_selection_changed)
        except Exception:
            pass  # nosec B110

        # Bloqueia sinais (tabela + selectionModel) e spinBox durante todo o carregamento
        self._block_table_selection_signals(True)
        self.spinBoxSelec.blockSignals(True)

        try:
            self.selected_layer = layer

            fields = layer.fields()
            features = list(layer.getFeatures())

            # Configura colunas
            self.tableWidget_Dados1.setColumnCount(len(fields))
            self.tableWidget_Dados1.setHorizontalHeaderLabels([f.name() for f in fields])

            # Limpa linhas e caches
            self.feature_ids = []
            self._fid_to_row = {}   # <-- NOVO
            self.tableWidget_Dados1.setRowCount(0)

            # Preenche tabela e cria cache FID -> row
            for row_idx, feat in enumerate(features):
                self.tableWidget_Dados1.insertRow(row_idx)

                fid = feat.id()
                self.feature_ids.append(fid)
                self._fid_to_row[fid] = row_idx

                for col_idx, field in enumerate(fields):
                    value = feat[field.name()]
                    item = QTableWidgetItem(str(value))
                    item.setFlags(Qt.ItemFlag.ItemIsSelectable | Qt.ItemFlag.ItemIsEnabled)
                    if col_idx == 0:
                        item.setData(Qt.ItemDataRole.UserRole, fid)
                    self.tableWidget_Dados1.setItem(row_idx, col_idx, item)

            # Ajustes visuais
            self.tableWidget_Dados1.resizeColumnsToContents()
            self.tableWidget_Dados1.verticalHeader().setDefaultSectionSize(20)

            # Reaplica seleção NA TABELA (sem varrer tudo, usando cache)
            self.tableWidget_Dados1.clearSelection()
            if saved_selection:
                for fid in saved_selection:
                    row = self._fid_to_row.get(fid)
                    if row is not None:
                        self.tableWidget_Dados1.selectRow(row)

            # Atualiza spinBox (sem disparar valueChanged)
            row_count = self.tableWidget_Dados1.rowCount()
            self.spinBoxSelec.setMaximum(row_count)

            n_selected = 0
            sm = self.tableWidget_Dados1.selectionModel()
            if sm:
                n_selected = len(sm.selectedRows())

            self.spinBoxSelec.setValue(n_selected)
            self._prev_spin_box_selec = n_selected

            # Estados de botões dependentes
            self.update_pushButtonSeq_state(n_selected)
            self.atualizar_estado_botoes_calcular()

        finally:
            self.spinBoxSelec.blockSignals(False)
            self._block_table_selection_signals(False)

        # Reconecta por último (agora sim, seguro)
        try:
            layer.selectionChanged.disconnect(self.on_map_selection_changed)
        except Exception:
            pass  # nosec B110
        layer.selectionChanged.connect(self.on_map_selection_changed)

    def _select_table_rows_by_fids_fast(self, fids):
        """
        Seleciona rapidamente na tableWidget_Dados1 as linhas correspondentes aos FIDs,
        usando cache fid->row e seleção em lote (ranges) para evitar travadas em seleções grandes.
        """
        if not fids:
            self._block_table_selection_signals(True)
            self.tableWidget_Dados1.setUpdatesEnabled(False)
            try:
                self.tableWidget_Dados1.clearSelection()
            finally:
                self.tableWidget_Dados1.setUpdatesEnabled(True)
                self._block_table_selection_signals(False)
            return

        fid_to_row = getattr(self, "_fid_to_row", None) or {}

        # Fallback: se não tiver cache, volta para o caminho lento (mas com updates desligados)
        if not fid_to_row:
            self._block_table_selection_signals(True)
            self.tableWidget_Dados1.setUpdatesEnabled(False)
            try:
                self.tableWidget_Dados1.clearSelection()
                fset = set(fids)
                for row in range(self.tableWidget_Dados1.rowCount()):
                    item = self.tableWidget_Dados1.item(row, 0)
                    if item is None:
                        continue
                    fid = item.data(Qt.ItemDataRole.UserRole)
                    if fid in fset:
                        self.tableWidget_Dados1.selectRow(row)
            finally:
                self.tableWidget_Dados1.setUpdatesEnabled(True)
                self._block_table_selection_signals(False)
            return

        rows = [fid_to_row.get(fid) for fid in set(fids)]
        rows = sorted(r for r in rows if r is not None)
        if not rows:
            return

        sm = self.tableWidget_Dados1.selectionModel()
        if sm is None:
            return

        model = self.tableWidget_Dados1.model()
        last_col = max(0, self.tableWidget_Dados1.columnCount() - 1)

        self._block_table_selection_signals(True)
        self.tableWidget_Dados1.setUpdatesEnabled(False)

        try:
            sel = QItemSelection()

            # Compacta em ranges contíguos (ex: 10-80, 120-140, ...)
            start = prev = rows[0]
            for r in rows[1:]:
                if r == prev + 1:
                    prev = r
                else:
                    sel.select(model.index(start, 0), model.index(prev, last_col))
                    start = prev = r
            sel.select(model.index(start, 0), model.index(prev, last_col))

            sm.select(sel, QItemSelectionModel.SelectionFlag.ClearAndSelect | QItemSelectionModel.SelectionFlag.Rows)
        finally:
            self.tableWidget_Dados1.setUpdatesEnabled(True)
            self._block_table_selection_signals(False)

    def reset_graph(self):
        """
        Reseta os dados de todas as curvas do gráfico, inclusive reconfigurando o pen_new_line para a curve_CotaEstaca2,
        se estes atributos já existirem.
        """
        # Verifica se os atributos de curva foram criados
        for attr in ['curve_Z', 'curve_CotaEstaca', 'leftover_lines',
                     'vertical_lines_inrange', 'vertical_lines_outrange', 'curve_CotaEstaca2']:
            if hasattr(self, attr):
                getattr(self, attr).setData([], [])
        
        # Reinicializa o pen_new_line e o aplica à curve_CotaEstaca2 (se existir)
        self.pen_new_line = pg.mkPen(color='blue', width=5, style=Qt.PenStyle.SolidLine)
        self.pen_new_line.setCapStyle(Qt.PenCapStyle.FlatCap)  # Define extremidades retangulares
        if hasattr(self, 'curve_CotaEstaca2'):
            self.curve_CotaEstaca2.setPen(self.pen_new_line)

    def init_combo_box_raster(self):
        """
        Inicializa o comboBoxRaster com as camadas Raster do projeto.
        Adiciona uma mensagem inicial "Selecione um Raster".
        """
        # Armazena o ID da camada raster atualmente selecionada
        current_raster_id = self.comboBoxRaster.currentData()

        # Obtém todas as camadas do projeto atual
        layers = QgsProject.instance().mapLayers().values()

        # Filtra apenas camadas raster
        raster_layers = [layer for layer in layers if isinstance(layer, QgsRasterLayer)]

        # Limpa o ComboBox antes de adicionar itens
        self.comboBoxRaster.clear()

        # Adiciona a mensagem inicial ao ComboBox
        self.comboBoxRaster.addItem(self.tr("Raster (Opcional)"), None)

        # Adiciona as camadas raster ao ComboBox
        for raster_layer in raster_layers:
            self.comboBoxRaster.addItem(raster_layer.name(), raster_layer.id())

        # Tenta restaurar a seleção anterior, se possível
        if current_raster_id:
            index = self.comboBoxRaster.findData(current_raster_id)
            if index != -1:
                self.comboBoxRaster.setCurrentIndex(index)
            else:
                # Nenhuma seleção anterior ou inválida; exibe a mensagem inicial
                self.comboBoxRaster.setCurrentIndex(0)
        else:
            # Nenhuma seleção; exibe a mensagem inicial
            self.comboBoxRaster.setCurrentIndex(0)

    def _get_estruturas_layer_ids(self):
        """
        Retorna um set() com os IDs das camadas que estão dentro
        do grupo 'Estruturas'.
        """
        root = QgsProject.instance().layerTreeRoot()
        estruturas_group = None
        for child in root.children():
            if isinstance(child, QgsLayerTreeGroup) and child.name() == self.tr("Estruturas"):
                estruturas_group = child
                break

        if not estruturas_group:
            return set()

        ids = set()
        for child in estruturas_group.children():
            if isinstance(child, QgsLayerTreeLayer) and child.layer():
                ids.add(child.layer().id())
        return ids

    def _is_layer_from_estruturas(self, layer):
        """
        Diz se a camada é uma camada gerada pelo módulo de estruturas,
        mesmo que ainda não esteja no grupo.

        Critérios:
        - está no grupo 'Estruturas'; OU
        - nome começa com 'M' + número (M1, M2, M10...); OU
        - nome termina com '_Suporte'
        """
        if not layer:
            return False

        # 1) está no grupo?
        estruturas_ids = self._get_estruturas_layer_ids()
        if layer.id() in estruturas_ids:
            return True

        # 2) nome típico das camadas calculadas
        name = layer.name()
        if name.endswith(self.tr("_Suporte")):
            return True

        # M1, M2, M10 etc.
        if re.match(r"^M\d+(\b|_)", name):
            return True

        return False

    def init_combo_box_pontos(self):
        """
        Inicializa o comboBoxPontos com as camadas vetoriais do tipo PONTO,
        excluindo as do grupo 'Estruturas' e as que seguem o padrão M.../_Suporte.
        """
        current_point_layer_id = self.comboBoxPontos.currentData()

        all_layers = QgsProject.instance().mapLayers().values()

        self.comboBoxPontos.clear()

        point_layers = []
        for lyr in all_layers:
            if (
                isinstance(lyr, QgsVectorLayer)
                and lyr.geometryType() == QgsWkbTypes.GeometryType.PointGeometry
                and not self._is_layer_from_estruturas(lyr)):    # 👈 filtro definitivo

                point_layers.append(lyr)

        for p_lyr in point_layers:
            self.comboBoxPontos.addItem(p_lyr.name(), p_lyr.id())

        # restaurar seleção anterior se ainda existir
        if current_point_layer_id and current_point_layer_id in [point_layer.id() for point_layer in point_layers]:
            idx = self.comboBoxPontos.findData(current_point_layer_id)
            if idx != -1:
                self.comboBoxPontos.setCurrentIndex(idx)
            else:
                if point_layers:
                    self.comboBoxPontos.setCurrentIndex(0)
        else:
            if point_layers:
                self.comboBoxPontos.setCurrentIndex(0)

    def update_combo_box_pontos(self, layers):
        """
        Atualiza o comboBoxPontos quando camadas são adicionadas,
        mas ignora as que estão dentro do grupo 'Estruturas'.

        Mantém a camada atualmente selecionada sempre que possível.
        """
        estruturas_ids = self._get_estruturas_layer_ids()

        point_layers_added = [lyr for lyr in layers
            if (isinstance(lyr, QgsVectorLayer)
                and lyr.geometryType() == QgsWkbTypes.GeometryType.PointGeometry
                and lyr.id() not in estruturas_ids)]      # 👈 ignora as do grupo Estruturas

        if not point_layers_added:
            return

        # tentar preservar o item já selecionado
        self.init_combo_box_pontos()

    def update_combo_box_raster(self, layers):
        """Atualiza o comboBoxRaster quando novas camadas são adicionadas ao projeto."""
        # Verifica se há novas camadas raster entre as adicionadas
        raster_layers_added = [layer for layer in layers if isinstance(layer, QgsRasterLayer)]
        if raster_layers_added:
            # Atualiza o comboBoxRaster
            self.init_combo_box_raster()
            # Seleciona a última camada raster adicionada
            self.comboBoxRaster.setCurrentIndex(self.comboBoxRaster.count() - 1)

    def on_layers_added(self, layers):
        """
        Quando qualquer camada é adicionada, checamos se há Raster ou Pontos
        e chamamos as funções de atualização correspondentes.
        """
        for layer in layers:
            layer.nameChanged.connect(self.on_layer_name_changed)

            # 🔹 Só aplica estilo se:
            #    - o dock estiver VISÍVEL
            #    - for realmente uma camada de estruturas (_is_layer_from_estruturas)
            if (self.isVisible()                      # <<< aqui a trava pelo diálogo aberto
                and isinstance(layer, QgsVectorLayer)
                and layer.geometryType() == QgsWkbTypes.GeometryType.PointGeometry
                and self._is_layer_from_estruturas(layer)):
                try:
                    self.set_label_for_layer(layer)
                except Exception as e:
                    self.mostrar_mensagem(self.tr("Erro ao aplicar estilo na camada {layer_name}: {error}").format(layer_name=layer.name(), error=str(e)), "Erro")

        self.update_combo_box_raster(layers)
        self.update_combo_box_pontos(layers)

        if self.comboBoxPontos.count() > 0:
            self.load_table_widget_dados1()

        # atualiza listWidget
        self.update_list_widget_estruturas()

        # se alguma das camadas novas for exatamente a que estávamos olhando, atualiza gráfico
        layer_ids = [lyr.id() for lyr in layers]
        if self.current_estruturas_layer and self.current_estruturas_layer.id() in layer_ids:
            self.current_estruturas_layer = None
            self.update_graph()

        # botão DXF
        self.atualizar_estado_pushButtonExportarDXF()

        # botão GPKG
        self.atualizar_estado_pushButtonExportarGPKG()

    def on_layer_name_changed(self):
        """
        Chamado quando o nome de qualquer camada no projeto é alterado.
        Atualizamos apenas o texto dos itens nos ComboBoxes e no listWidget_Lista,
        sem recriar tudo.
        """
        # Atualiza nomes no comboBoxRaster
        for i in range(self.comboBoxRaster.count()):
            layer_id = self.comboBoxRaster.itemData(i)
            layer = QgsProject.instance().mapLayer(layer_id)
            if layer and isinstance(layer, QgsRasterLayer):
                self.comboBoxRaster.setItemText(i, layer.name())

        # Atualiza nomes no comboBoxPontos
        for i in range(self.comboBoxPontos.count()):
            layer_id = self.comboBoxPontos.itemData(i)
            layer = QgsProject.instance().mapLayer(layer_id)
            if layer and isinstance(layer, QgsVectorLayer) and layer.geometryType() == QgsWkbTypes.GeometryType.PointGeometry:
                self.comboBoxPontos.setItemText(i, layer.name())

        # 🔹 Atualiza nomes no listWidget_Lista (grupo 'Estruturas')
        for i in range(self.listWidget_Lista.count()):
            item = self.listWidget_Lista.item(i)
            layer_id = item.data(Qt.ItemDataRole.UserRole)
            layer = QgsProject.instance().mapLayer(layer_id)
            if layer:
                item.setText(layer.name())
                item.setToolTip(layer.name())   # 🔹 Atualiza também o tooltip

    def selecionar_coluna(self, numeric_fields):
        """
        Abre um diálogo para o usuário escolher qual campo numérico usar como altimetria (Z).
        Retorna o nome do campo escolhido.
        Se o usuário clicar em Cancelar, levanta UserCancelled para abortar o processo chamador.
        """
        dialog = QInputDialog(self)
        dialog.setWindowTitle(self.tr("Selecionar Campo"))
        dialog.setLabelText(self.tr("Escolha o Campo Z:"))
        dialog.setComboBoxItems(numeric_fields)

        if dialog.exec() != QDialog.DialogCode.Accepted:
            raise UserCancelled()

        return dialog.textValue()

    def get_z_from_raster(self, raster_layer, x, y):
        """
        Obtém o valor de Z de um Raster para as coordenadas X, Y fornecidas.
        """
        raster_provider = raster_layer.dataProvider()
        raster_extent = raster_layer.extent()

        # Converte as coordenadas do ponto para o sistema de referência do raster
        raster_crs = raster_layer.crs()
        point_crs = self.selected_layer.crs()
        if point_crs != raster_crs:
            transform = QgsCoordinateTransform(point_crs, raster_crs, QgsProject.instance())
            point = transform.transform(QgsPointXY(x, y))
        else:
            point = QgsPointXY(x, y)

        # Verifica se o ponto está dentro da extensão do Raster
        if not raster_extent.contains(point):
            return 0  # Se o ponto está fora do Raster, retorna 0

        # Obtém o valor de Z no ponto
        ident = raster_provider.identify(point, QgsRaster.IdentifyFormat.IdentifyFormatValue)
        if ident.isValid():
            band_values = ident.results()
            if band_values:
                return list(band_values.values())[0]  # Retorna o primeiro valor da banda

        return 0  # Caso não consiga obter o valor

    def generate_layer_name(self, raster_name=""):
        """
        Gera um nome para a nova camada no formato:
          - M1, M2, M3, ...
          - M1_MDT, M2_MDT, ...
        Regras:
          - O índice (1, 2, 3, ...) não se repete entre M# e M#_ALGUMA_COISA.
          - Sempre usa o menor índice livre (se M1 foi deletada, o próximo volta a ser M1).
          - Garante que o nome final ainda não exista no projeto.
        """
        # Nomes de todas as camadas do projeto
        existing_layer_names = {layer.name() for layer in QgsProject.instance().mapLayers().values()}

        # Descobre quais índices já estão sendo usados em nomes do tipo M<number>...
        used_indices = set()
        for name in existing_layer_names:
            m = re.match(r"^M(\d+)(?:\b|_)", name)
            if m:
                try:
                    used_indices.add(int(m.group(1)))
                except ValueError:
                    pass  # nosec B110

        # Procura o menor índice positivo que esteja livre
        idx = 1
        while True:
            if idx not in used_indices:
                base = f"M{idx}"
                new_name = f"{base}_{raster_name}" if raster_name else base

                # Segurança extra: garante que o nome completo não existe
                if new_name not in existing_layer_names:
                    return new_name

                # Se por algum motivo já existir, marca o índice como usado e continua
                used_indices.add(idx)

            idx += 1

    def create_point_layer(self, layer_name, point_features):
        """
        Cria uma nova camada de pontos com os atributos:
            X, Y, Z, CotaEstaca, AlturaEstaca

        point_features deve ser uma lista de tuplas:
           (x, y, z, cota_estaca, altura_estaca)
        """
        # Define os campos
        fields = QgsFields()
        fields.append(QgsField("X", QMetaType.Type.Double))
        fields.append(QgsField("Y", QMetaType.Type.Double))
        fields.append(QgsField("Z", QMetaType.Type.Double))
        fields.append(QgsField("CotaEstaca", QMetaType.Type.Double))  # Novo campo
        fields.append(QgsField("AlturaEstaca", QMetaType.Type.Double))  # Novo campo

        # Cria a camada de memória
        crs = self.selected_layer.crs()  # Usa o mesmo sistema de coordenadas da camada original
        new_layer = QgsVectorLayer(f"Point?crs={crs.authid()}", layer_name, "memory")
        new_layer_data = new_layer.dataProvider()

        # Adiciona os campos à camada
        new_layer_data.addAttributes(fields)
        new_layer.updateFields()

        # Adiciona as feições
        for x, y, z, cota_estaca, altura_estaca in point_features:
            feat = QgsFeature()
            feat.setGeometry(QgsGeometry.fromPointXY(QgsPointXY(x, y)))
            feat.setAttributes([x, y, z, cota_estaca, altura_estaca])
            new_layer_data.addFeature(feat)

        # Atualiza a camada
        new_layer.updateExtents()
        return new_layer

    def on_layers_removed(self, layer_ids):
        """
        Atualiza os ComboBoxes e limpa a tabela se a camada atual for removida.
        Também remove automaticamente a camada de suporte associada e,
        se o grupo 'Estruturas' ficar vazio, remove o grupo.
        """
        # Evita o uso com o diálogo fechado
        if not self.isVisible():
            return

        self.init_combo_box_raster()
        self.init_combo_box_pontos()

        # Verifica se a camada selecionada foi removida
        current_layer_id = self.comboBoxPontos.currentData()
        if current_layer_id not in layer_ids:
            self.load_table_widget_dados1()
        else:
            # Limpa a tabela caso a camada selecionada tenha sido removida
            self.tableWidget_Dados1.clear()
            self.tableWidget_Dados1.setRowCount(0)
            self.tableWidget_Dados1.setColumnCount(0)

        # Atualiza listWidget
        self.update_list_widget_estruturas()

        # Atualiza o listWidget removendo os itens das camadas deletadas
        for i in reversed(range(self.listWidget_Lista.count())):  # Percorre de trás para frente
            item = self.listWidget_Lista.item(i)
            if item and item.data(Qt.ItemDataRole.UserRole) in layer_ids:
                self.listWidget_Lista.takeItem(i)  # Remove o item da lista

        # Se a camada removida era a selecionada...
        layer = getattr(self, "current_estruturas_layer", None)
        if self._w_alive(layer) and layer.id() in layer_ids:
            removed_main_layer_name = layer.name()
            self.current_estruturas_layer = None
            self.graphWidget.clear()

            # Tenta remover do QGIS a camada "removed_main_layer_name + '_Suporte'"
            support_name = removed_main_layer_name + self.tr("_Suporte")
            for lyr in list(self.support_layers):
                if lyr.name() == support_name:
                    QgsProject.instance().removeMapLayer(lyr.id())
                    self.support_layers.remove(lyr)
                    break

        # Inicializa a lista antes de qualquer verificação
        support_layers_to_remove = []

        for layer in self.support_layers:
            # 1) Se o ID da camada de suporte está explicitamente em layer_ids, remova
            if layer.id() in layer_ids:
                QgsProject.instance().removeMapLayer(layer.id())
                support_layers_to_remove.append(layer)
                continue  # já tratou esse caso

            # 2) Verifica se a camada de suporte pertence a uma camada principal removida
            if layer.name().endswith(self.tr("_Suporte")):
                main_name = layer.name().replace(self.tr("_Suporte"), "")

                # Verifica se essa camada principal ainda existe no projeto
                main_layer = next(
                    (ly for ly in QgsProject.instance().mapLayers().values()
                     if ly.name() == main_name),
                    None)

                if main_layer is None:  # Se a camada principal foi removida, remova a de suporte
                    QgsProject.instance().removeMapLayer(layer.id())
                    support_layers_to_remove.append(layer)

        # Agora a variável está definida e pode ser usada na filtragem
        self.support_layers = [lyr for lyr in self.support_layers if lyr not in support_layers_to_remove]

        # Atualiza a exibição da tabela de dados
        self.update_scroll_area_dados()

        # Atualiza tableView_2 e listWidget_inc
        self.update_tableView_2()
        self.update_listWidget_inc()

        # 🔹 Garante que self.selected_layer seja resetado corretamente
        layer_sel = getattr(self, "selected_layer", None)
        if self._w_alive(layer_sel) and layer_sel.id() in layer_ids:
            try:
                layer_sel.selectionChanged.disconnect(self.on_map_selection_changed)
            except Exception:
                pass  # nosec B110
            self.selected_layer = None

        # Monitora a remoção do botão pushButtonExportarDXF 
        self.atualizar_estado_pushButtonExportarDXF()
        
        # botão GPKG
        self.atualizar_estado_pushButtonExportarGPKG()

        # 🔹 Se a última camada do grupo 'Estruturas' foi removida, apaga o grupo
        try:
            root = QgsProject.instance().layerTreeRoot()
            estruturas_group = None

            for child in root.children():
                if isinstance(child, QgsLayerTreeGroup) and child.name() == self.tr("Estruturas"):
                    estruturas_group = child
                    break

            # Se o grupo existe e não tem mais filhos, remove-o
            if estruturas_group is not None and len(estruturas_group.children()) == 0:
                parent = estruturas_group.parent() or root
                parent.removeChildNode(estruturas_group)
        except Exception:
            # Qualquer problema aqui, apenas ignora para não quebrar o fluxo
            pass  # nosec B110

        # Força atualização imediata do canvas do QGIS
        try:
            self.iface.mapCanvas().refreshAllLayers()
        except Exception:
            pass  # nosec B110

    def add_layer_to_group(self, layer, group_name):
        """
        Adiciona a camada ao grupo especificado e retorna a camada que ficou efetivamente no projeto.
        Garante que o QgsLayerTreeGroup não seja um objeto já destruído.
        """
        root = QgsProject.instance().layerTreeRoot()

        # Procura um grupo válido com esse nome
        group = None
        for child in root.children():
            if (isinstance(child, QgsLayerTreeGroup)
                    and child.name() == group_name
                    and self._w_alive(child)):
                group = child
                break

        # Se não achar ou o grupo estiver "morto", cria um novo
        if group is None or not self._w_alive(group):
            group = root.addGroup(group_name)

        # Adiciona a camada ao projeto (sem criar nó no root)
        if layer.id() not in QgsProject.instance().mapLayers():
            QgsProject.instance().addMapLayer(layer, False)

        # Tenta adicionar ao grupo; se der erro de objeto deletado, recria o grupo e tenta de novo
        try:
            group.addLayer(layer)
        except RuntimeError:
            # Grupo ficou inválido entre a busca e o uso → recria
            root = QgsProject.instance().layerTreeRoot()
            group = root.addGroup(group_name)
            group.addLayer(layer)

        # Verifica se a camada tem um provedor de dados válido
        if not layer.dataProvider():
            self.mostrar_mensagem(self.tr("Erro ao acessar a camada para atualização."), "Erro")
            return layer  # ou retorne None

        layer_name = layer.name()
        m_match = re.match(r"M(\d+)", layer_name)  # Extrai o número M do nome da camada
        m_value = m_match.group(1) if m_match else "1"

        existing_fields = [field.name() for field in layer.fields()]

        # Se o campo 'sequencia' não existe, cria uma nova camada e substitui a original
        if 'sequencia' not in existing_fields:
            new_fields = [QgsField('sequencia', QMetaType.Type.QString)] + layer.fields().toList()
            new_layer = QgsVectorLayer(f"Point?crs={layer.crs().authid()}", layer_name, "memory")
            new_layer_data = new_layer.dataProvider()
            new_layer_data.addAttributes(new_fields)
            new_layer.updateFields()

            new_features = []
            for i, feature in enumerate(layer.getFeatures()):
                new_feature = QgsFeature()
                new_feature.setGeometry(feature.geometry())
                e_value = i + 1
                attributes = [f'M{m_value}E{e_value}'] + feature.attributes()

                # Ajusta X e Y para 3 casas decimais
                geom = feature.geometry()
                if geom and not geom.isEmpty():
                    point = geom.asPoint()
                    x_rounded = round(point.x(), 3)
                    y_rounded = round(point.y(), 3)
                    if 'X' in existing_fields:
                        x_index = existing_fields.index('X') + 1  # +1 pois 'sequencia' foi adicionada no início
                        attributes[x_index] = x_rounded
                    if 'Y' in existing_fields:
                        y_index = existing_fields.index('Y') + 1
                        attributes[y_index] = y_rounded

                new_feature.setAttributes(attributes)
                new_features.append(new_feature)

            new_layer_data.addFeatures(new_features)
            new_layer.updateExtents()

            # Remove a camada antiga e adiciona a nova
            QgsProject.instance().removeMapLayer(layer)
            QgsProject.instance().addMapLayer(new_layer, False)

            # ⚠️ Reobtém o grupo de forma segura antes de adicionar a nova camada
            root = QgsProject.instance().layerTreeRoot()
            group = None
            for child in root.children():
                if (isinstance(child, QgsLayerTreeGroup)
                        and child.name() == group_name
                        and self._w_alive(child)):
                    group = child
                    break
            if group is None or not self._w_alive(group):
                group = root.addGroup(group_name)
            group.addLayer(new_layer)

            result_layer = new_layer
        else:
            # Se o campo já existe, apenas atualiza os valores e utiliza a própria camada
            layer.startEditing()
            for i, feature in enumerate(layer.getFeatures()):
                e_value = i + 1
                feature['sequencia'] = f'M{m_value}E{e_value}'
                geom = feature.geometry()
                if geom and not geom.isEmpty():
                    point = geom.asPoint()
                    feature['X'] = round(point.x(), 3)
                    feature['Y'] = round(point.y(), 3)
                layer.updateFeature(feature)
            layer.commitChanges()
            result_layer = layer

        self.mostrar_mensagem(self.tr("Nova camada '{layer_name}' adicionada com coluna '{field_name}' como primeira coluna, sequência contínua e X/Y ajustados.").format(layer_name=layer_name, field_name="sequencia"), "Sucesso")

        self.update_list_widget_estruturas()

        # Força o combo a ser reconstruído já com a Mx dentro do grupo
        self.init_combo_box_pontos()

        return result_layer

    def update_list_widget_estruturas(self):
        """
        Limpa o listWidget_Lista e adiciona o nome de todas as camadas
        presentes no grupo 'Estruturas'.
        """
        self.listWidget_Lista.clear()
        
        root = QgsProject.instance().layerTreeRoot()
        grupo_estruturas = None
        for child in root.children():
            if isinstance(child, QgsLayerTreeGroup) and child.name() == self.tr("Estruturas"):
                grupo_estruturas = child
                break

        if not grupo_estruturas:
            # Se não existe grupo, garante que o botão PDF fique desabilitado
            self.atualizar_estado_pushButtonPDF()
            return

        for child in grupo_estruturas.children():
            if isinstance(child, QgsLayerTreeLayer):
                layer = child.layer()
                if layer is not None:
                    item = QListWidgetItem(layer.name())
                    item.setData(Qt.ItemDataRole.UserRole, layer.id())  # Armazena o ID da camada para remoção
                    item.setToolTip(layer.name())          # 🔹 Tooltip com o nome completo
                    self.listWidget_Lista.addItem(item)

        # 🔹 Atualiza o estado do botão PDF sempre que a lista for recalculada
        self.atualizar_estado_pushButtonPDF()

    def recalc_current_layer(self):
        """
        Lê os valores de doubleSpinBox_1 e 2, localiza as feições na self.current_estruturas_layer,
        e atualiza CotaEstaca e AlturaEstaca por interpolação linear 
        entre o primeiro e o último, na ordem da coluna 'sequencia' (se existir) ou FID.
        """

        lyr = self.current_estruturas_layer
        if not lyr:
            return  # Nenhuma camada selecionada

        # Lê os valores do spinBox
        delta1 = self.doubleSpinBox_1.value()
        delta2 = self.doubleSpinBox_2.value()

        # Precisamos garantir que a camada tenha campos: X, Y, Z, CotaEstaca, AlturaEstaca
        # Se não tiver, não há como recalcular. (Você pode tratar esse caso, exibir mensagem, etc.)
        field_names = [f.name() for f in lyr.fields()]
        if not all(fname in field_names for fname in ["X","Y","Z","CotaEstaca","AlturaEstaca"]):
            self.mostrar_mensagem(self.tr("A camada selecionada não possui os campos X, Y, Z, CotaEstaca, AlturaEstaca."), "Erro")
            return

        # Vamos determinar a ordem das feições.
        #   1) Se existe campo 'sequencia', ordenamos por ele.
        #      (Alternativamente, você poderia ordenar pela string M1E1, M1E2..., mas teria
        #       que extrair o número da estaca. Por simplicidade, basta ordenar pela FID,
        #       ou por X crescente, etc., depende da sua lógica.)
        #   2) Se não, podemos ordenar pela FID.
        sequencia_index = lyr.fields().indexFromName("sequencia")
        features_all = list(lyr.getFeatures())

        def get_seq_num(feat):
            # Exemplo simples: se 'sequencia' = 'M1E3', extrair o número 3
            # Mas isso depende do seu padrão. Aqui faço um parse simples:
            val = feat["sequencia"]

            # Espera algo tipo M1E3
            # Tentar extrair a parte numérica após 'E'
            try:
                idxE = val.index("E")
                return int(val[idxE + 1:])
            except (AttributeError, TypeError, ValueError):
                return feat.id()

        if sequencia_index >= 0:
            # Ordenar usando a função get_seq_num
            features_all.sort(key=get_seq_num)
        else:
            # Se não existe 'sequencia', ordena por FID
            features_all.sort(key=lambda f: f.id())

        if len(features_all) < 2:
            # Precisamos de pelo menos 2 pontos para interpolar
            return

        # Montar lista com (feature, X, Y, Z)
        feats_info = []
        for f in features_all:
            x_ = f["X"]
            y_ = f["Y"]
            z_ = f["Z"]
            feats_info.append((f, x_, y_, z_))

        # Pega o primeiro e o último
        first_feat, x0, y0, z0 = feats_info[0]
        last_feat,  x1, y1, z1 = feats_info[-1]

        cota_first = z0 + delta1
        cota_last = z1 + delta2

        dx = x1 - x0
        dy = y1 - y0
        dist_total = math.sqrt(dx*dx + dy*dy)

        # Evitar zero
        if dist_total == 0:
            # Se for zero, significa que todos os pontos estão no mesmo lugar,
            # ou só existe 1 ponto.
            # Você pode decidir o que fazer, p. ex.:
            for (f, x_, y_, z_) in feats_info:
                # CotaEstaca = z0 + delta1 (ou delta2, pois first=last)
                # AlturaEstaca = cotaEstaca - z_
                cota_estaca = z0 + delta1
                altura_estaca = cota_estaca - z_
                f["CotaEstaca"] = cota_estaca
                f["AlturaEstaca"] = altura_estaca
            lyr.startEditing()
            for f,_,_,_ in feats_info:
                lyr.updateFeature(f)
            lyr.commitChanges()
            return

        # Caso normal: dist_total > 0
        dc = cota_last - cota_first

        lyr.startEditing()

        for (f, x_, y_, z_) in feats_info:
            # distância parcial do (x_, y_) até (x0, y0)
            dparc = math.sqrt((x_ - x0)**2 + (y_ - y0)**2)
            frac = dparc / dist_total
            cota_estaca = cota_first + dc * frac
            altura_estaca = cota_estaca - z_

            # Agora arredonda todos para 3 casas decimais
            f["X"] = round(x_, 3)
            f["Y"] = round(y_, 3)
            f["Z"] = round(z_, 3)
            f["CotaEstaca"] = round(cota_estaca, 3)
            f["AlturaEstaca"] = round(altura_estaca, 3)

            lyr.updateFeature(f)

        lyr.commitChanges()

        # Se existir camada de suporte para esta estrutura, usa o gráfico com suporte;
        # caso contrário, usa o gráfico padrão.
        if self.has_support_for_current_layer():
            self.update_support_graph()
        else:
            self.update_graph()

        self.update_tableView_2()
        self.update_listWidget_inc()

    def setup_graph(self):
        """
        Configura o gráfico no scrollAreaGrafico.
        Melhora a suavização, ativa o anti-aliasing e configura as curvas de perfil.
        """
        self.graphWidget = PlotWidget()
        self.graphWidget.setAntialiasing(True)

        self.layout_grafico = QVBoxLayout(self.scrollAreaGrafico)
        self.layout_grafico.addWidget(self.graphWidget)

        # self.graphWidget.setTitle("Perfil de Elevação")
        self.graphWidget.setLabel("bottom", self.tr("Distância Acumulada (m)"))
        self.graphWidget.setLabel("left", self.tr("Altitude (m)"))
        # self.graphWidget.showGrid(x=True, y=True, alpha=0.3)

        self.legend = pg.LegendItem(colCount=10, offset=(0, 0))
        # Associa a legenda ao plot principal:
        self.legend.setParentItem(self.graphWidget.getPlotItem())

        # Defina a posição onde deseja que a legenda fique.
        # Por exemplo, (0, 0) é o topo-esquerda do gráfico.
        self.legend.setPos(1, 0)

        self.graphWidget.addLegend()
        self.graphWidget.setRenderHint(QPainter.RenderHint.Antialiasing)
        self.graphWidget.setRenderHint(QPainter.RenderHint.SmoothPixmapTransform)

    def update_tableView_2(self):
        """
        Atualiza o tableView_2 exibindo as colunas 'sequencia' e 'AlturaEstaca'
        da camada atualmente selecionada (self.current_estruturas_layer).
        Os dados são exibidos com alinhamento centralizado, são somente para leitura,
        e a cor de cada linha indica se AlturaEstaca está dentro do intervalo definido
        por doubleSpinBoxPadrao ± doubleSpinBoxVaria (azul se estiver dentro, vermelho se estiver fora).
        """
        # Se não houver camada selecionada, limpa o tableView_2.
        if not self.current_estruturas_layer:
            self.tableView_2.setModel(None)
            return

        # Verifica se os campos necessários existem
        field_names = [field.name() for field in self.current_estruturas_layer.fields()]
        if "sequencia" not in field_names or "AlturaEstaca" not in field_names:
            self.tableView_2.setModel(None)
            return

        # Pega os valores dos spinBoxes para definir o intervalo
        padraoValue = self.doubleSpinBoxPadrao.value()
        variaValue = self.doubleSpinBoxVaria.value()
        lower_lim = padraoValue - variaValue
        upper_lim = padraoValue + variaValue

        # Cria um modelo padrão com 2 colunas
        model = QStandardItemModel()
        model.setHorizontalHeaderLabels([self.tr("LISTA"), self.tr("AlturaEstaca")])

        # Fonte em negrito
        bold_font = QFont()
        bold_font.setBold(True)

        # Itera sobre as feições da camada e adiciona os dados ao modelo
        for feature in self.current_estruturas_layer.getFeatures():
            seq = feature["sequencia"]
            altura = feature["AlturaEstaca"]

            item_seq = QStandardItem(str(seq))
            item_altura = QStandardItem(str(altura))

            # Somente leitura
            item_seq.setEditable(False)
            item_altura.setEditable(False)

            # Alinhamentos:
            # - LISTA (sequencia): centralizado
            item_seq.setTextAlignment(Qt.AlignmentFlag.AlignCenter)
            # - AlturaEstaca: à ESQUERDA (com alinhamento vertical no centro)
            item_altura.setTextAlignment(Qt.AlignmentFlag.AlignLeft | Qt.AlignmentFlag.AlignVCenter)

            # Fonte em negrito
            bold_font = QFont()
            bold_font.setBold(True)
            item_seq.setFont(bold_font)
            item_altura.setFont(bold_font)

            # Coloração conforme limites
            try:
                numeric_altura = float(altura)
            except Exception:
                numeric_altura = 0.0
            color = Qt.GlobalColor.blue if lower_lim <= numeric_altura <= upper_lim else Qt.GlobalColor.red
            item_seq.setForeground(color)
            item_altura.setForeground(color)

            model.appendRow([item_seq, item_altura])

        self.tableView_2.setModel(model)
        self.tableView_2.resizeColumnsToContents()
        # Reduz a altura das linhas (por exemplo, 20 pixels)
        self.tableView_2.verticalHeader().setDefaultSectionSize(20)
        # Impede a edição na view
        self.tableView_2.setEditTriggers(QAbstractItemView.EditTrigger.NoEditTriggers)

    def update_listWidget_inc(self):
        """
        Atualiza o listWidget_inc exibindo:
          - A inclinação média entre os valores de Z (calculada como a média dos incrementos de Z dividido
            pela distância acumulada entre pontos consecutivos), exibida em laranja.
          - A inclinação entre o primeiro e o último valor de CotaEstaca (calculada de forma global), exibida em azul.
        Os valores são convertidos para porcentagem e exibidos com o símbolo '%'.
        O listWidget_inc é resetado a cada atualização.
        """
        # Reseta o listWidget_inc
        self.listWidget_inc.clear()

        # Verifica se existe uma camada selecionada
        if not self.current_estruturas_layer:
            return

        # Verifica se os campos necessários existem
        field_names = [field.name() for field in self.current_estruturas_layer.fields()]
        if "Z" not in field_names or "CotaEstaca" not in field_names or "sequencia" not in field_names:
            return

        # Obtém as feições da camada ordenadas pela coluna 'sequencia' (ou FID, se não houver)
        seq_index = self.current_estruturas_layer.fields().indexFromName("sequencia")
        feats = list(self.current_estruturas_layer.getFeatures())
        
        def get_seq_num(feat):
            val = feat["sequencia"]
            try:
                idxE = val.index("E")
                return int(val[idxE + 1:])
            except (AttributeError, TypeError, ValueError):
                return feat.id()
        
        if seq_index >= 0:
            feats.sort(key=get_seq_num)
        else:
            feats.sort(key=lambda f: f.id())
        
        # Verifica se há pelo menos 2 pontos para calcular inclinação
        if len(feats) < 2:
            return

        # Construção dos arrays: x_vals (distância acumulada), z_vals e cota_vals
        x_vals = []
        z_vals = []
        cota_vals = []
        dist_acum = 0.0
        prev_x = None
        for f in feats:
            x_val = f["X"]
            z_val = f["Z"]
            cota_val = f["CotaEstaca"]

            if prev_x is not None:
                dx = abs(x_val - prev_x)
                dist_acum += dx
            else:
                dist_acum = 0.0
            x_vals.append(dist_acum)
            z_vals.append(z_val)
            cota_vals.append(cota_val)
            prev_x = x_val

        # Cálculo da inclinação média entre os valores de Z (média dos incrementos)
        slopes = []
        for i in range(len(x_vals)-1):
            dx = x_vals[i+1] - x_vals[i]
            if dx != 0:
                slope = (z_vals[i+1] - z_vals[i]) / dx
                slopes.append(slope)
        if slopes:
            avg_slope_z = sum(slopes) / len(slopes)
        else:
            avg_slope_z = 0.0

        # Cálculo da inclinação entre o primeiro e o último valor de CotaEstaca
        dx_total = x_vals[-1] - x_vals[0]
        if dx_total != 0:
            slope_cota = (cota_vals[-1] - cota_vals[0]) / dx_total
        else:
            slope_cota = 0.0

        # Converte as inclinações para porcentagem (m/m * 100) e formata com 2 casas decimais
        avg_slope_z_pct = avg_slope_z * 100
        slope_cota_pct = slope_cota * 100

        avg_slope_z_str = self.tr("Inclinação média Z: {avg_slope_z_pct:.2f}%").format(avg_slope_z_pct=avg_slope_z_pct)
        slope_cota_str = self.tr("Inclinação da Estrutura: {slope_cota_pct:.2f}%").format(slope_cota_pct=slope_cota_pct)

        # Cria itens de lista com as cores definidas:
        item_z = QListWidgetItem(avg_slope_z_str)
        item_z.setForeground(QBrush(QColor("orange")))  # Inclinação de Z em laranja
        # Aumenta o tamanho do texto:
        font_z = QFont()
        font_z.setPointSize(10)
        item_z.setFont(font_z)

        item_cota = QListWidgetItem(slope_cota_str)
        item_cota.setForeground(QBrush(QColor("blue")))   # Inclinação de CotaEstaca em azul
        font_cota = QFont()
        font_cota.setPointSize(10)
        item_cota.setFont(font_cota)

        # Adiciona os itens ao listWidget_inc
        self.listWidget_inc.addItem(item_z)
        self.listWidget_inc.addItem(item_cota)

    def sample_raster_value(self, point, raster_layer):
        """Amostra o valor Z do raster baseado nas coordenadas do ponto."""
        identify_result = raster_layer.dataProvider().identify(QgsPointXY(point.x(), point.y()), QgsRaster.IdentifyFormat.IdentifyFormatValue)
        
        if identify_result.isValid():
            results = identify_result.results()
            if results:
                band_key = list(results.keys())[0]
                z_value = results.get(band_key)  # Use get para evitar KeyError
                if z_value is not None:  # Verifica se o valor é válido
                    return round(float(z_value), 3)
        return None  # Retorna None se não houver valor válido

    def create_support_points_layer(self, estacas_layer, raster_layer):
        start_time = time.time()
        
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

        # Define o nome da camada de suporte com o nome da camada de estacas + "_Suporte"
        support_layer_name = self.tr("{layer_name}_Suporte").format(layer_name=estacas_layer.name())

        # Cria a camada de suporte (em memória) com o nome ajustado
        support_layer = QgsVectorLayer(f"Point?crs={crs}", support_layer_name, "memory")

        prov = support_layer.dataProvider()

        # Adiciona os campos necessários, incluindo "Acumula_dist"
        fields = [
            QgsField("ID", QMetaType.Type.Int),
            QgsField("Original_ID", QMetaType.Type.Int),
            QgsField("X", QMetaType.Type.Double),
            QgsField("Y", QMetaType.Type.Double),
            QgsField("Znovo", QMetaType.Type.Double),
            QgsField("Acumula_dist", QMetaType.Type.Double)]
        prov.addAttributes(fields)
        support_layer.updateFields()

        # Obtém todas as feições e os pontos da camada de estacas
        estacas_features = [feat for feat in estacas_layer.getFeatures()]
        estacas_points = [feat.geometry().asPoint() for feat in estacas_features]
        all_points = []  # Lista para guardar os pontos de suporte gerados
        support_point_id = 0
        last_coord = None
        acumula_dist = 0

        # Alteração: usar o campo "AlturaEstaca" em vez de "Desnivel"
        altura_index = estacas_layer.fields().indexFromName('AlturaEstaca')
        if altura_index == -1:
            self.mostrar_mensagem(self.tr("O campo 'AlturaEstaca' não foi encontrado na camada."), "Erro")
            return

        # Obter os valores de AlturaEstaca para o primeiro e o último ponto
        first_altura = estacas_features[0][altura_index]
        last_altura = estacas_features[-1][altura_index]

        # Definir extensão antes do primeiro ponto e após o último
        extend_by_start = min(abs(first_altura) + 2, 2)  # No máximo 2 metros
        extend_by_end = min(abs(last_altura) + 2, 2)       # No máximo 2 metros

        # Calcular o número total de pontos para a barra de progresso
        num_points_before_first_stake = int(extend_by_start // support_spacing)
        num_points_after_last_stake = int(extend_by_end // support_spacing) + 1
        num_points_along_segments = 0

        for i, start_point in enumerate(estacas_points[:-1]):
            end_point = estacas_points[i + 1]
            segment_length = start_point.distance(end_point)
            num_intermediate_points = int(segment_length / support_spacing)
            num_points_along_segments += num_intermediate_points + 1  # +1 para incluir o ponto final

        total_points = num_points_before_first_stake + num_points_along_segments + num_points_after_last_stake
        total_steps = total_points * 2  # Multiplica por 2 para incluir as etapas de atualização de Znovo

        # Iniciar a barra de progresso
        progressBar, progressMessageBar = self.iniciar_progress_bar(total_steps)

        # Helper: atualiza a barra sem quebrar se o usuário fechar a mensagem / widget for destruído
        def _pb_set(v: int):
            nonlocal progressBar
            if not progressBar or not self._w_alive(progressBar):
                progressBar = None
                # se estamos rodando o calc_tudo, cancela geral
                if getattr(self, "_calc_tudo_iter", None):
                    self._calc_tudo_cancelled = True
                    raise UserCancelled()
                return
        current_step = 0

        # Adicionar pontos extras antes do primeiro ponto de estacas
        dx0 = estacas_points[1].x() - estacas_points[0].x()
        dy0 = estacas_points[1].y() - estacas_points[0].y()
        seg0_len = math.hypot(dx0, dy0) or 1.0  # evita zero

        # pontos ANTES do primeiro
        for i in range(num_points_before_first_stake, 0, -1):
            fx = estacas_points[0].x() - dx0 * (i * support_spacing) / seg0_len
            fy = estacas_points[0].y() - dy0 * (i * support_spacing) / seg0_len
            extra_point = QgsPointXY(fx, fy)

            z_value = self.sample_raster_value(extra_point, raster_layer)
            if z_value is None:
                break  # Interrompe se não há valor de Z
            support_point_id += 1
            # Como a coluna "ID" não está explícita, para Original_ID usamos um valor negativo indicando ponto extra
            all_points.append((extra_point, -i, support_point_id))
            # Conta da Barra de Progresso
            current_step += 1
            _pb_set(current_step)
            QApplication.processEvents()

        # Gerar os pontos de apoio ao longo dos segmentos
        for i, start_point in enumerate(estacas_points[:-1]):
            end_point = estacas_points[i + 1]
            segment_length = start_point.distance(end_point)
            num_intermediate_points = int(segment_length / support_spacing)
            for j in range(num_intermediate_points + 1):
                x = start_point.x() + (end_point.x() - start_point.x()) * (j * support_spacing) / segment_length
                y = start_point.y() + (end_point.y() - start_point.y()) * (j * support_spacing) / segment_length
                inter_point = QgsPointXY(x, y)
                support_point_id += 1
                # Se a camada de estacas não possui um campo "ID", usamos o índice (i+1) como Original_ID
                original_id = i + 1
                all_points.append((inter_point, original_id, support_point_id))
                # Conta da Barra de Progresso
                current_step += 1
                _pb_set(current_step)
                QApplication.processEvents()

        # Adicionar pontos extras após o último ponto de estacas
        dx1 = estacas_points[-1].x() - estacas_points[-2].x()
        dy1 = estacas_points[-1].y() - estacas_points[-2].y()
        seg1_len = math.hypot(dx1, dy1) or 1.0

        # pontos APÓS o último
        for i in range(0, num_points_after_last_stake):
            lx = estacas_points[-1].x() + dx1 * (i * support_spacing) / seg1_len
            ly = estacas_points[-1].y() + dy1 * (i * support_spacing) / seg1_len
            extra_point = QgsPointXY(lx, ly)

            z_value = self.sample_raster_value(extra_point, raster_layer)
            if z_value is None:
                break
            support_point_id += 1
            # Se a camada de estacas não possui um campo "ID", usamos o número total de estacas como Original_ID
            original_id = estacas_features[-1]['ID'] if 'ID' in estacas_features[-1].fields().names() else len(estacas_features)
            all_points.append((extra_point, original_id, support_point_id))
            # Conta da Barra de Progresso
            current_step += 1
            _pb_set(current_step)
            QApplication.processEvents()

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

            feat = QgsFeature()
            feat.setGeometry(QgsGeometry.fromPointXY(QgsPointXY(*current_coord)))
            feat.setAttributes([support_point_id, original_id, round(point.x(), 3), round(point.y(), 3), None, round(acumula_dist, 3)])
            prov.addFeature(feat)
            # Conta da Barra de Progresso
            current_step += 1
            _pb_set(current_step)
            QApplication.processEvents()

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
            # Conta da Barra de Progresso
            current_step += 1
            _pb_set(current_step)
            QApplication.processEvents()

        support_layer.commitChanges()
        
        # Finaliza a Barra de Progresso
        try:
            if self._w_alive(progressMessageBar):
                self.iface.messageBar().popWidget(progressMessageBar)

        except UserCancelled:
            # fecha barra se ainda estiver viva, libera lock, e interrompe
            try:
                if self._w_alive(progressMessageBar):
                    self.iface.messageBar().popWidget(progressMessageBar)
            except Exception:
                pass  # nosec B110
            self._lock_messagebar = False

            # se estiver rodando dentro do Calcular Tudo, deixe propagar para o _processar_proximo_bloco tratar bonito
            if getattr(self, "_calc_tudo_iter", None):
                raise
            return None

        end_time = time.time()
        elapsed_time = end_time - start_time
        self.mostrar_mensagem(self.tr("Camada de suporte criada com sucesso em {elapsed_time:.2f} segundos.").format(elapsed_time=elapsed_time), "Sucesso")
        
        # NÃO adicionamos a camada ao projeto. Em vez disso, armazenamos em uma lista interna.
        if not hasattr(self, "support_layers"):
            self.support_layers = []

        self.support_layers.append(support_layer)

        # Atualiza o scrollAreaDADOS para incluir a nova tabela
        self.update_scroll_area_dados()

        return support_layer

    def _get_altimetria_field_name(self, layer: QgsVectorLayer):
        """
        Descobre e guarda (em cache) o nome do campo de altimetria (Z) da camada:
        - Tenta 'Z' (case-insensitive)
        - Tenta nomes típicos: alt, altimetria, altitude, cota, elev, etc.
        - Se houver mais de um candidato, pergunta ao usuário.
        - Se nada for encontrado, retorna None e o Z será considerado 0.
        """
        if not layer:
            return None

        # cache
        if layer.id() in self._altimetria_fields:
            return self._altimetria_fields[layer.id()]

        fields = layer.fields()
        numeric_types = (QMetaType.Type.Int, QMetaType.Type.Double)

        # 1) Primeiro tenta um campo 'Z' (case-insensitive)
        for f in fields:
            if f.type() in numeric_types and f.name().lower() == "z":
                self._altimetria_fields[layer.id()] = f.name()
                return f.name()

        # 2) Tenta nomes típicos de altimetria
        candidatos_nomes = [
            "z", "alt", "altimetria", "altitude",
            "cota", "cota_z", "elev", "elevacao", "elevação",
            "nivel", "nível"]
        candidatos = [
            f.name() for f in fields
            if f.type() in numeric_types and f.name().lower() in candidatos_nomes]

        if len(candidatos) == 1:
            self._altimetria_fields[layer.id()] = candidatos[0]
            return candidatos[0]
        elif len(candidatos) > 1:
            # Pergunta ao usuário qual deseja usar
            escolhido = self.selecionar_coluna(candidatos)  # pode levantar UserCancelled
            if escolhido:
                self._altimetria_fields[layer.id()] = escolhido
                return escolhido

            # Se aceitou mas veio vazio (raro), aí sim trata como "sem campo"
            self._altimetria_fields[layer.id()] = None
            self.mostrar_mensagem(self.tr("Nenhum campo de altimetria foi selecionado. O valor de Z será considerado 0."), "Info")
            return None

        # 3) Nenhum nome típico → se houver campos numéricos, pergunta qual usar
        numeric_fields = [f.name() for f in fields if f.type() in numeric_types]
        if numeric_fields:
            escolhido = self.selecionar_coluna(numeric_fields)  # pode levantar UserCancelled
            if escolhido:
                self._altimetria_fields[layer.id()] = escolhido
                return escolhido

            self._altimetria_fields[layer.id()] = None
            self.mostrar_mensagem(self.tr("Nenhum campo de altimetria foi selecionado. O valor de Z será considerado 0."), "Info")
            return None

        # 4) Não há nenhum campo numérico
        self._altimetria_fields[layer.id()] = None
        self.mostrar_mensagem(self.tr("A camada não possui campos numéricos para altimetria. O valor de Z será considerado 0."), "Info")
        return None

    def _get_z_from_attribute(self, layer: QgsVectorLayer, feature: QgsFeature):
        """
        Retorna o valor de Z a partir do campo de altimetria detectado.
        Se não houver campo válido ou o valor não for numérico, retorna 0.0.
        """
        field_name = self._get_altimetria_field_name(layer)
        if not field_name:
            return 0.0

        try:
            val = feature[field_name]
        except KeyError:
            return 0.0

        if val is None:
            return 0.0

        try:
            return float(val)
        except (TypeError, ValueError):
            return 0.0

    def calcular(self):
        """
        Calcula uma nova camada de pontos a partir das feições selecionadas no tableWidget_Dados1.
        Se uma camada Raster estiver selecionada, o Z será obtido do Raster.
        A camada é adicionada ao grupo "Estruturas" com o nome correto.

        Também cria duas colunas:
          - CotaEstaca
          - AlturaEstaca
        usando interpolação linear entre o primeiro e o último ponto.

        Se o usuário cancelar a escolha do campo de altimetria, a operação é abortada sem gerar camada.
        """
        # Verifica se existe uma camada associada
        if not self.selected_layer:
            self.mostrar_mensagem(self.tr("Nenhuma camada associada ao tableWidget."), "Erro")
            return

        # Verifica se há feições selecionadas
        selected_feature_ids = self.selected_layer.selectedFeatureIds()
        if not selected_feature_ids:
            self.mostrar_mensagem(self.tr("Nenhuma feição selecionada na tabela."), "Erro")
            return

        # Ordena as feições selecionadas na mesma ordem que aparece no tableWidget
        selected_features = [feat for feat in self.selected_layer.getFeatures() if feat.id() in selected_feature_ids]
        selected_features.sort(key=lambda f: self.feature_ids.index(f.id()))

        # Recupera valor do doubleSpinBox_1 e 2
        delta1 = self.doubleSpinBox_1.value()  # Ajuste no 1º ponto
        delta2 = self.doubleSpinBox_2.value()  # Ajuste no último ponto

        # Obtém a camada raster selecionada (se existir)
        raster_layer_id = self.comboBoxRaster.currentData()
        raster_layer = QgsProject.instance().mapLayer(raster_layer_id) if raster_layer_id else None

        # Gera nome para a nova camada
        raster_name = raster_layer.name() if raster_layer else ""
        layer_name = self.generate_layer_name(raster_name)

        # 1) Monta a lista dos pontos (x, y, z) na ordem das feições
        point_features = []
        try:
            for feature in selected_features:
                geom = feature.geometry()
                if geom.isEmpty():
                    continue
                point = geom.asPoint()
                x, y = point.x(), point.y()

                # Se houver um Raster selecionado, extrai o Z do Raster
                if raster_layer:
                    z_real = self.get_z_from_raster(raster_layer, x, y)
                    # Se get_z_from_raster retorna None, significa que não há valor de raster p/ esse ponto
                    if z_real is None:
                        self.mostrar_mensagem(self.tr("Não existe raster sob algum dos pontos selecionados."), "Erro")
                        return
                else:
                    # Usa campo de altimetria genérico (pode abrir diálogo e pode ser cancelado)
                    z_real = self._get_z_from_attribute(self.selected_layer, feature)

                point_features.append((x, y, z_real))

        except UserCancelled:
            # Usuário cancelou a escolha do campo: aborta SEM erro e SEM criar camada
            try:
                self.mostrar_mensagem(self.tr("Operação cancelada pelo usuário."), "Info", duracao=2, forcar=False)
            except Exception:
                pass  # nosec B110
            return

        # Se não houve geometria válida
        if not point_features:
            self.mostrar_mensagem(self.tr("Nenhuma geometria válida encontrada nas feições selecionadas."), "Erro")
            return

        # 2) Calcula a CotaEstaca e a AlturaEstaca usando interpolação linear entre 1º e último ponto
        x0, y0, z0 = point_features[0]
        x1, y1, z1 = point_features[-1]

        cota_first = z0 + delta1
        cota_last = z1 + delta2
        dc = cota_last - cota_first
        dist_total = math.sqrt((x1 - x0)**2 + (y1 - y0)**2)

        if dist_total == 0 and len(point_features) > 1:
            self.mostrar_mensagem(self.tr("Primeiro e último pontos coincidem, não é possível interpolar."), "Erro")
            return

        final_features = []
        for (x, y, z_real) in point_features:
            frac = math.sqrt((x - x0)**2 + (y - y0)**2) / dist_total if dist_total > 0 else 0.0
            cota_estaca = cota_first + (dc * frac)
            altura_estaca = cota_estaca - z_real
            final_features.append((x, y, z_real, cota_estaca, altura_estaca))

        # Agora criamos uma lista com arredondamento de 3 casas decimais
        final_features_3 = []
        for (xx, yy, zz, cc, aa) in final_features:
            final_features_3.append((
                round(xx, 3),
                round(yy, 3),
                round(zz, 3),
                round(cc, 3),
                round(aa, 3)))

        # Cria a nova camada usando os valores arredondados
        new_layer = self.create_point_layer(layer_name, final_features_3)

        # 4) Adiciona a camada ao grupo "Estruturas"
        new_layer = self.add_layer_to_group(new_layer, self.tr("Estruturas"))

        # 5) Label
        self.set_label_for_layer(new_layer)

        self.mostrar_mensagem(self.tr("Nova camada '{layer_name}' criada e adicionada ao grupo 'Estruturas'.").format(layer_name=layer_name), "Sucesso")

        # Se houver raster, cria suporte
        if raster_layer:
            support_layer = self.create_support_points_layer(new_layer, raster_layer)
            if support_layer:
                self.mostrar_mensagem(self.tr("Camada de suporte criada com sucesso."), "Sucesso")

        # Monitora o botão pushButtonExportarDXF
        self.atualizar_estado_pushButtonExportarDXF()

    def mouse_moved(self, evt):
        """
        Exibe um crosshair apenas sobre a linha do suporte (Terreno Natural),
        garantindo que o cursor "grude" à linha quando dentro de uma tolerância.
        """
        # Se ainda não temos os objetos do crosshair criados, não faz nada
        if not (hasattr(self, "vLine") and hasattr(self, "hLine") and hasattr(self, "coord_text")):
            return

        if self.graphWidget.plotItem is None:
            return  # Segurança se o gráfico ainda não existe

        pos = evt  # evt já vem como QPointF
        plot_item = self.graphWidget.plotItem

        if plot_item.sceneBoundingRect().contains(pos):
            mousePoint = plot_item.vb.mapSceneToView(pos)
            x = mousePoint.x()
            y = mousePoint.y()

            # Verifica se temos self.support_x / self.support_y
            if hasattr(self, 'support_x') and hasattr(self, 'support_y') and len(self.support_x) > 1:
                x_min = self.support_x[0]
                x_max = self.support_x[-1]
                if x_min <= x <= x_max:
                    # Interpola y_suporte (altura do Terreno Natural nesse x)
                    y_suporte = np.interp(x, self.support_x, self.support_y)

                    # Define tolerância (5% do range vertical, por exemplo)
                    y_range = max(self.support_y) - min(self.support_y)
                    tolerance = y_range * 0.05 if y_range > 0 else 0.0

                    if tolerance == 0.0 or abs(y - y_suporte) <= tolerance:
                        # "Gruda" em (x, y_suporte)
                        self.vLine.setPos(x)
                        self.hLine.setPos(y_suporte)
                        self.vLine.show()
                        self.hLine.show()

                        self.coord_text.setFont(QFont("Arial", 8, weight=QFont.Weight.Bold))
                        self.coord_text.setText(self.tr("Elevação: {y_suporte:.2f} m\nDistância: {x:.2f} m").format(y_suporte=y_suporte, x=x))
                        self.coord_text.setPos(x, y_suporte)
                        self.coord_text.show()
                        return

            # Se chegou aqui, ou não há suporte_x/suporte_y, ou mouse está fora do range
            self.vLine.hide()
            self.hLine.hide()
            self.coord_text.hide()
        else:
            # Fora do gráfico
            self.vLine.hide()
            self.hLine.hide()
            self.coord_text.hide()

    def update_graph(self):
        """
        Atualiza o gráfico com os valores de Z, CotaEstaca, etc.,
        e desenha as linhas de diferença abaixo de CotaEstaca e Z,
        conforme doubleSpinBoxComp.

        Agora também inclui a linha "CotaEstaca + 10cm" em segmentos,
        dividida pelo spinBoxQ e com espaços (gaps) de 5 cm entre eles.
        """
        self.graphWidget.clear()

        lyr = self.current_estruturas_layer
        if not lyr:
            return

        field_names = [f.name() for f in lyr.fields()]
        # Verifica se há campos necessários
        if not all(fname in field_names for fname in ["X", "Y", "Z", "CotaEstaca", "AlturaEstaca"]):
            return

        feats = list(lyr.getFeatures())

        # Ordenação pela 'sequencia', se existir
        if "sequencia" in field_names:
            def get_seq_num(feature):
                val = feature["sequencia"]

                try:
                    idxE = val.index("E")
                    return int(val[idxE + 1:])
                except (AttributeError, TypeError, ValueError):
                    return feature.id()

            feats.sort(key=get_seq_num)
        else:
            feats.sort(key=lambda f: f.id())

        # Variáveis de controle
        dist_acum = 0.0
        prev_x = None

        # Arrays para plotar Z, CotaEstaca
        x_vals_z = []
        y_vals_z = []
        x_vals_cota = []
        y_vals_cota = []

        # Arrays para as linhas verticais (dentro/fora do limite de AlturaEstaca)
        inrange_x = []
        inrange_y = []
        outrange_x = []
        outrange_y = []

        # Arrays para a linha vermelha (abaixo de CotaEstaca): (compValue - cota_)
        comp_x = []
        comp_y = []

        # Arrays para a linha magenta (abaixo de Z): (compValue - AlturaEstaca)
        magenta_x = []
        magenta_y = []

        # Parâmetros para saber se a AlturaEstaca está em intervalo
        padraoValue = self.doubleSpinBoxPadrao.value()
        variaValue = self.doubleSpinBoxVaria.value()
        lower_lim = padraoValue - variaValue
        upper_lim = padraoValue + variaValue

        # Valor que queremos comparar: doubleSpinBoxComp
        compValue = self.doubleSpinBoxComp.value()

        for f in feats:
            geom = f.geometry()
            if geom and not geom.isEmpty():
                pt = geom.asPoint()
                if prev_x is not None:
                    dist_acum += math.hypot(pt.x() - prev_x.x(), pt.y() - prev_x.y())
                else:
                    dist_acum = 0.0
                prev_x = pt

                z_ = f["Z"]
                cota_ = f["CotaEstaca"]
                alt_ = f["AlturaEstaca"]  # alt_ = cota_ - z_

                # Armazena para plotar Z e CotaEstaca
                x_vals_z.append(dist_acum)
                y_vals_z.append(z_)

                x_vals_cota.append(dist_acum)
                y_vals_cota.append(cota_)

                # Verifica se AlturaEstaca está dentro ou fora do intervalo
                if lower_lim <= alt_ <= upper_lim:
                    # Se estiver DENTRO do intervalo, plotamos em azul
                    inrange_x.extend([dist_acum, dist_acum, np.nan])
                    inrange_y.extend([z_, cota_, np.nan])
                else:
                    # Se estiver FORA do intervalo, plotamos em vermelho
                    outrange_x.extend([dist_acum, dist_acum, np.nan])
                    outrange_y.extend([z_, cota_, np.nan])

                # Calcula a diferença para CotaEstaca (linha vermelha abaixo de CotaEstaca)
                diff_cota = compValue - cota_
                if diff_cota > 0:
                    comp_x.extend([dist_acum, dist_acum, np.nan])
                    comp_y.extend([cota_, cota_ - diff_cota, np.nan])

                # Calcula a diferença para Z (linha magenta abaixo de Z) = compValue - AlturaEstaca
                diff_magenta = compValue - alt_
                if diff_magenta > 0:
                    magenta_x.extend([dist_acum, dist_acum, np.nan])
                    magenta_y.extend([z_, z_ - diff_magenta, np.nan])

        # Plot das séries principais

        # Plot Z em laranja
        pen_z = pg.mkPen(color='orange', width=2)
        self.graphWidget.plot(x_vals_z, y_vals_z, pen=pen_z, symbol='o', symbolSize=6, name="Z")

        # Plot CotaEstaca em prata
        pen_cota = pg.mkPen(color='silver', width=3)
        self.graphWidget.plot(x_vals_cota, y_vals_cota, pen=pen_cota, symbol='x', symbolSize=6, name="CotaEstaca")

        # Plot das linhas verticais “in range” (azuis)
        pen_inrange = pg.mkPen(color='blue', width=3, style=Qt.PenStyle.DashLine)
        self.graphWidget.plot(inrange_x, inrange_y, pen=pen_inrange, name=self.tr("AlturaEstaca (Dentro)"))

        # Plot das linhas verticais “out range” (vermelhas)
        pen_outrange = pg.mkPen(color='red', width=3, style=Qt.PenStyle.DashLine)
        self.graphWidget.plot(outrange_x, outrange_y, pen=pen_outrange, name=self.tr("AlturaEstaca (Fora)"))

        # Plot das linhas verticais magenta (compValue - AlturaEstaca), abaixo de Z
        if magenta_x:
            pen_magenta = pg.mkPen(color='magenta', width=6)
            self.graphWidget.plot(magenta_x, magenta_y, pen=pen_magenta, name=self.tr("Estaca Aterrada"))

        # Criando a segunda linha paralela, 10 cm acima, com segmentos ===
        y_vals_cota2 = [valor + 0.10 for valor in y_vals_cota]

        # Lê o número de segmentos a partir do spinBoxQ
        Q = int(self.spinBoxQ.value())  
        if Q < 1:
            Q = 1

        # Define o 1º e o último X do array para a extensão horizontal
        x_start = x_vals_cota[0]
        x_end   = x_vals_cota[-1]
        total_length = x_end - x_start

        # Gap (espaço) de 5 cm -> 0.05 m
        gap = 0.05

        # Se houver mais de 1 segmento, reduz o comprimento desenhável
        if Q > 1:
            drawn_length = total_length - (Q - 1) * gap
            if drawn_length < 0:  # caso Q seja enorme
                drawn_length = 0
        else:
            drawn_length = total_length

        segment_length = drawn_length / Q if Q else 0

        seg_x = []
        seg_y = []

        # Vamos interpolar, pois x_seg_start / x_seg_end podem não estar exatamente em x_vals_cota
        for i in range(Q):
            x_seg_start = x_start + i * (segment_length + gap)
            x_seg_end   = x_seg_start + segment_length

            # Interpola valores de Y
            y_seg_start = np.interp(x_seg_start, x_vals_cota, y_vals_cota2)
            y_seg_end   = np.interp(x_seg_end,   x_vals_cota, y_vals_cota2)

            # Adiciona [início, fim, np.nan] para "quebrar" a linha
            seg_x.extend([x_seg_start, x_seg_end, np.nan])
            seg_y.extend([y_seg_start, y_seg_end, np.nan])

        # Pen grosso, cor azul, extremidades quadradas
        pen_cota2 = pg.mkPen(color='blue', width=5, style=Qt.PenStyle.SolidLine)
        pen_cota2.setCapStyle(Qt.PenCapStyle.SquareCap)

        # Plota a linha segmentada
        self.graphWidget.plot(seg_x, seg_y, pen=pen_cota2, name=self.tr("Módulos"))

        # Ajuste automático de eixo
        self.graphWidget.enableAutoRange(axis=pg.ViewBox.XYAxes, enable=True)

    def _refresh_graph_and_table(self):
        """
        Atualiza imediatamente o tableView_2 e o gráfico (scrollAreaGrafico)
        com base na camada atual em self.current_estruturas_layer.
        """
        if not self.current_estruturas_layer:
            return

        # Atualiza tabela
        self.update_tableView_2()

        # Atualiza o gráfico correto (com ou sem suporte)
        if self.has_support_for_current_layer():
            self.update_support_graph()
        else:
            self.update_graph()

    def on_spin_parameters_changed(self, value):
        """
        Slot genérico para mudanças em:
          - doubleSpinBoxComp
          - doubleSpinBoxPadrao
          - doubleSpinBoxVaria
          - spinBoxQ
        """
        self._refresh_graph_and_table()

    @staticmethod
    def calcular_inclinacao_media(x_vals, y_vals):
        """
        Calcula a inclinação média (em m/m) com base nos valores de x e y.
        Retorna a média dos incrementos (slopes) entre os pontos.
        """
        slopes = []
        for i in range(1, len(x_vals)):
            dx = x_vals[i] - x_vals[i - 1]
            if dx == 0:
                continue
            slope = (y_vals[i] - y_vals[i - 1]) / dx
            slopes.append(slope)
        if slopes:
            return np.mean(slopes)
        else:
            return 0.0

    def get_estacas_data(self, estacas_layer):
        """
        Obtém os dados da camada de estruturas (estacas) calculando a distância acumulada entre os pontos.
        Retorna uma lista de tuplas:
           (dist_acumulada, CotaEstaca, Z, AlturaEstaca, x, y)
        """
        features = list(estacas_layer.getFeatures())
        field_names = [f.name() for f in estacas_layer.fields()]

        # Ordena as feições: se houver o campo 'sequencia', usa-o; caso contrário, usa FID.
        if "sequencia" in field_names:
            def seq_key(f):
                try:
                    # Exemplo: "M1E3" -> 3
                    return int(f["sequencia"].split("E")[1])
                except Exception:
                    return f.id()
            features.sort(key=seq_key)
        else:
            features.sort(key=lambda f: f.id())

        data = []
        dist_acum = 0.0
        prev_point = None
        import math
        for f in features:
            pt = f.geometry().asPoint()
            if prev_point is not None:
                # Calcula a distância Euclidiana entre o ponto atual e o anterior
                dist_acum += math.hypot(pt.x() - prev_point.x(), pt.y() - prev_point.y())
            else:
                dist_acum = 0.0
            # Obtém os valores dos campos necessários
            try:
                cota_estaca = f["CotaEstaca"]
                z_value = f["Z"]
                altura_estaca = f["AlturaEstaca"]
            except KeyError:
                self.mostrar_mensagem(self.tr("A camada de estruturas não possui os campos 'CotaEstaca', 'Z' ou 'AlturaEstaca'."), "Erro")
                return []
            data.append((dist_acum, cota_estaca, z_value, altura_estaca, pt.x(), pt.y()))
            prev_point = pt

        return data

    def atualizar_estado_botao(self):
        """
        Habilita o botão do gráfico sempre que houver
        uma camada de estruturas selecionada no listWidget_Lista.
        O tipo de gráfico (com ou sem raster) será decidido em plot_layers().
        """
        camada_selecionada = self.listWidget_Lista.selectedItems()
        self.pushButtonMat.setEnabled(bool(camada_selecionada))

    def configurar_ticks_eixo_x(self, ax, estacas_distances, talude_start_intersection=None, talude_end_intersection=None, step=5):
        """
        Configura os rótulos do eixo X com:
          - Múltiplos de 'step' (default=5).
          - Valores das estacas (estacas_distances).
          - Pontos de interseção do talude, caso existam.
          - Formatação especial (negrito + itálico) nos rótulos especiais (estacas + interseções).
        """
        # Se houver interseções do talude, use-as; caso contrário, use bordas default
        if talude_start_intersection:
            x_mag_left = talude_start_intersection[0]
        else:
            x_mag_left = estacas_distances[0]

        if talude_end_intersection:
            x_mag_right = talude_end_intersection[0]
        else:
            x_mag_right = estacas_distances[-1]

        # 1) Crie uma lista de ticks de 'step' em 'step' metros
        xticks = list(np.arange(min(estacas_distances), max(estacas_distances) + step, step))

        # 2) Adicione pontos especiais (magenta/interseções e distâncias das estacas)
        pontos_especiais = [x_mag_left, x_mag_right] + list(estacas_distances)
        for xi in pontos_especiais:
            if xi not in xticks:
                xticks.append(xi)

        # Ordene
        xticks.sort()

        # 3) Formate os rótulos
        formatted_labels = []
        for tick in xticks:
            if tick in [x_mag_left, x_mag_right]:
                label_str = f"{tick:.1f}"  # com 1 casa decimal
            elif tick in estacas_distances:
                label_str = f"{tick:.1f}"
            else:
                # para os múltiplos de step, formata como int se for inteiro
                label_str = f"{int(tick)}" if float(tick).is_integer() else f"{tick:.1f}"
            formatted_labels.append(label_str)

        # 4) Aplica no eixo
        ax.set_xticks(xticks)
        ax.set_xticklabels(formatted_labels, fontsize=7)

        # 5) Aplica estilos especiais aos rótulos 'especiais'
        for i, label in enumerate(ax.get_xticklabels()):
            tick_value = xticks[i]
            if tick_value in pontos_especiais:
                label.set_fontweight('bold')
                label.set_fontstyle('italic')

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
            fig.add_artist(mpatches.FancyArrowPatch((x_start, y_start), (x_end, y_end), connectionstyle="arc3,rad=0.0", transform=fig.transFigure, clip_on=False, **arrowprops))

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
        Função para adicionar o logotipo ao gráfico do QGis (ou personalizado),
        mantendo a transparência do fundo e adicionando contorno.

        Se o usuário tiver escolhido um logo via pushButtonLogo, tenta usar esse.
        Se não existir mais, volta a usar o ícone padrão 'icones/Qgis.png'.
        """
        try:
            settings = QSettings()

            # Caminho salvo para logotipo personalizado
            custom_logo_path = settings.value("tempo_salvo_tools/custom_logo_path", "", type=str)

            icon_path = None

            # Se o usuário definiu um logo e ele ainda existe, usa ele
            if custom_logo_path and os.path.exists(custom_logo_path):
                icon_path = custom_logo_path
            else:
                # Se o custom não existe mais, volta pro padrão
                icon_path_default = os.path.join(self.plugin_dir, 'icones', 'Qgis.png')
                if os.path.exists(icon_path_default):
                    icon_path = icon_path_default
                    # Se o custom foi salvo mas sumiu do disco, limpa o setting
                    if custom_logo_path:
                        settings.remove("tempo_salvo_tools/custom_logo_path")
                else:
                    raise FileNotFoundError(self.tr("Logotipo padrão não encontrado em: {icon_path_default}").format(icon_path_default=icon_path_default))

            # Carrega a imagem (mantém transparência)
            logo = plt.imread(icon_path)

            # Tamanho máximo para o logo
            max_width, max_height = 150, 75
            img_height, img_width = logo.shape[:2]
            scale_factor = min(max_width / img_width, max_height / img_height)

            # Criar a imagem com zoom proporcional
            imagebox = OffsetImage(logo, zoom=scale_factor)

            # Fundo transparente e contorno
            bboxprops = dict(
                boxstyle="round,pad=0.5",
                facecolor="none",
                edgecolor="blue",
                linewidth=1.0)

            # Posicionamento dentro do gráfico no canto superior esquerdo
            ab = AnnotationBbox(
                imagebox,
                (0.085, 0.89),  # Ajuste fino da posição
                frameon=True,
                xycoords='figure fraction',
                box_alignment=(0, 1),
                bboxprops=bboxprops)

            ax = fig.gca()
            ax.add_artist(ab)

        except Exception as e:
            self.mostrar_mensagem(self.tr("Erro ao carregar o logotipo: {error}").format(error=str(e)), "Erro", duracao=5, forcar=True)

    def pushButtonLogo_clicked(self):
        """
        Abre um diálogo para o usuário escolher uma imagem de logotipo.
        O caminho é salvo em QSettings e será usado em adicionar_logo().
        """
        settings = QSettings()
        last_dir = settings.value("tempo_salvo_tools/logoLastDir", "", type=str)

        file_path, _ = QFileDialog.getOpenFileName(self, self.tr("Selecionar logotipo"), last_dir, self.tr("Imagens (*.png *.jpg *.jpeg *.bmp *.gif)"))

        if not file_path:
            return

        # Atualiza o último diretório e o caminho do logo personalizado
        settings.setValue("tempo_salvo_tools/logoLastDir", os.path.dirname(file_path))
        settings.setValue("tempo_salvo_tools/custom_logo_path", file_path)

        self.mostrar_mensagem(self.tr("Logotipo atualizado com sucesso. Os próximos gráficos usarão a nova imagem."), "Sucesso")

    def atualizar_estado_botoes_calcular(self):
        """
        Habilita ou desabilita ambos os botões (pushButtonCalcular e pushButtonCalculaTudo)
        de acordo com a quantidade de feições selecionadas na tabela.
        """
        # Usa selectedRows() para obter as linhas únicas selecionadas
        linhas_selecionadas = self.tableWidget_Dados1.selectionModel().selectedRows()
        
        # Se houver pelo menos 2 linhas selecionadas, ativa ambos os botões
        if len(linhas_selecionadas) >= 2:
            self.pushButtonCalcular.setEnabled(True)
            self.pushButtonCalculaTudo.setEnabled(True)
        else:
            self.pushButtonCalcular.setEnabled(False)
            self.pushButtonCalculaTudo.setEnabled(False)

    def update_scroll_area_dados(self):
        """
        Atualiza o scrollAreaDADOS exibindo a tabela de atributos de todas as camadas de suporte
        armazenadas em self.support_layers, de forma incremental.

        Cada widget (GroupBox com a tabela) permanece até que sua camada principal (conforme listWidget_Lista)
        seja removida.
        """
        # Certifica-se de que o container e o dicionário de widgets já foram criados.
        if not hasattr(self, 'dados_container'):
            self.dados_container = QWidget()
            self.dados_layout = QVBoxLayout(self.dados_container)
            self.scrollAreaDADOS.setWidget(self.dados_container)
            self.scrollAreaDADOS.setWidgetResizable(True)
        if not hasattr(self, 'support_widgets'):
            self.support_widgets = {}  # chave: layer.id(), valor: QGroupBox

        # Obtenha os nomes das camadas principais ativas no listWidget_Lista.
        active_main_names = {self.listWidget_Lista.item(i).text() for i in range(self.listWidget_Lista.count())}

        # Remoção dos widgets cujas camadas principais não estão mais ativas
        # Itera sobre os widgets já criados; se o nome da camada principal (extraído do título)
        # não estiver na lista ativa, remove o widget.
        for layer_id, widget in list(self.support_widgets.items()):
            # Supondo que o título do QGroupBox seja algo como "NomeDaCamada_Suporte"
            support_title = widget.title()  # Título do group box
            # Se o título terminar com "_Suporte", extraímos o nome principal:
            if support_title.endswith(self.tr("_Suporte")):
                main_name = support_title.replace(self.tr("_Suporte"), "")
            else:
                main_name = support_title
            if main_name not in active_main_names:
                self.dados_layout.removeWidget(widget)
                widget.deleteLater()
                del self.support_widgets[layer_id]

        # Função auxiliar para criar a tabela de atributos de uma camada de suporte
        def create_support_table(layer):
            table = QTableWidget()
            fields = layer.fields()
            features = list(layer.getFeatures())
            table.setRowCount(len(fields))
            # A primeira coluna é para os nomes dos atributos, as demais para cada feição
            table.setColumnCount(len(features) + 1)
            headers = [self.tr("Atributo")] + [self.tr("Feição {index}").format(index=i + 1) for i in range(len(features))]
            table.setHorizontalHeaderLabels(headers)
            table.setVerticalHeaderLabels([""] * len(fields))
            # Preenche a primeira coluna com os nomes dos atributos
            for row, field in enumerate(fields):
                item = QTableWidgetItem(field.name())
                item.setFlags(Qt.ItemFlag.ItemIsEnabled)
                item.setTextAlignment(Qt.AlignmentFlag.AlignCenter)
                table.setItem(row, 0, item)
            # Preenche as demais colunas com os valores de cada feição
            for col, feat in enumerate(features):
                for row, field in enumerate(fields):
                    valor = feat[field.name()]
                    item = QTableWidgetItem(str(valor))
                    item.setFlags(Qt.ItemFlag.ItemIsEnabled)
                    item.setTextAlignment(Qt.AlignmentFlag.AlignCenter)
                    table.setItem(row, col + 1, item)
            table.resizeColumnsToContents()
            table.resizeRowsToContents()
            table.setEditTriggers(QAbstractItemView.EditTrigger.NoEditTriggers)
            return table

        # Adiciona novos widgets para as camadas de suporte que ainda não possuem widget
        for layer in self.support_layers:
            layer_id = layer.id()
            # Considerando que o nome da camada de suporte tenha o padrão "NomeDaCamada_Suporte"
            if layer.name().endswith(self.tr("_Suporte")):
                main_name = layer.name().replace(self.tr("_Suporte"), "")
            else:
                main_name = layer.name()
            # Só cria o widget se a camada principal estiver ativa
            if main_name in active_main_names:
                if layer_id not in self.support_widgets:
                    group_box = QGroupBox(layer.name())
                    layout = QVBoxLayout(group_box)
                    table = create_support_table(layer)
                    layout.addWidget(table)
                    self.dados_layout.addWidget(group_box)
                    self.support_widgets[layer_id] = group_box

    def update_support_graph(self):
        """
        Atualiza o gráfico usando a camada de suporte correspondente
        à camada de estruturas atualmente selecionada (self.current_estruturas_layer).
        Se não houver camada de suporte, cai automaticamente no gráfico sem raster.
        """
        # 1) Verifica se a camada de estruturas está definida
        if not self.current_estruturas_layer:
            self.mostrar_mensagem(self.tr("Nenhuma camada de estruturas selecionada."), "Erro")
            return

        estacas_layer = self.current_estruturas_layer
        struct_layer_name = estacas_layer.name()

        # 3) Constrói o nome esperado da camada de suporte
        expected_support_name = struct_layer_name + self.tr("_Suporte")

        # 4) Localiza no self.support_layers a camada que tenha esse nome
        support_layer = None
        for lyr in getattr(self, "support_layers", []):
            if lyr.name() == expected_support_name:
                support_layer = lyr
                break

        # 🔹 Se NÃO houver camada de suporte para essa estrutura,
        #    significa que ela foi gerada sem raster → usa o gráfico padrão.
        if support_layer is None:
            self.update_graph()
            return

        # 5) Monta dados do Perfil (dist_e, cota_e) a partir da camada de estacas
        feats_estacas = list(estacas_layer.getFeatures())
        if not feats_estacas:
            self.mostrar_mensagem(self.tr("A camada de estruturas não possui feições."), "Erro")
            return

        field_names = [f.name() for f in estacas_layer.fields()]
        if "sequencia" in field_names:
            def get_seq(feature):
                try:
                    return int(feature["sequencia"].split("E")[1])
                except (AttributeError, TypeError, IndexError, ValueError):
                    return feature.id()
            feats_estacas.sort(key=get_seq)
        else:
            feats_estacas.sort(key=lambda f: f.id())

        dist_e = []
        cota_e = []
        dist_acum = 0.0
        prev_pt = None

        for f in feats_estacas:
            geom = f.geometry()
            if geom and not geom.isEmpty():
                pt = geom.asPoint()
                if prev_pt is not None:
                    dist_acum += math.hypot(pt.x() - prev_pt.x(), pt.y() - prev_pt.y())
                prev_pt = pt
                cota = f["CotaEstaca"] if "CotaEstaca" in field_names else 0
                dist_e.append(dist_acum)
                cota_e.append(cota)

        if not dist_e:
            self.mostrar_mensagem(self.tr("Não há dados de perfil para plotar."), "Erro")
            return

        # 6) Lê parâmetros dos spinBoxes
        padraoValue = self.doubleSpinBoxPadrao.value()
        variaValue = self.doubleSpinBoxVaria.value()
        lower_lim = padraoValue - variaValue
        upper_lim = padraoValue + variaValue
        compValue = self.doubleSpinBoxComp.value()

        # 7) Limpa o gráfico e plota o Perfil (CotaEstaca) em prata
        self.graphWidget.clear()
        self.graphWidget.plot(
            dist_e, cota_e,
            pen=pg.mkPen(color='silver', width=2),
            symbol='x', symbolSize=8, symbolBrush='blue',
            name=self.tr("Perfil"))

        # 8) Agora obtemos dist_s, z_s APENAS da camada de suporte desse layer
        feats_support = list(support_layer.getFeatures())
        if not feats_support:
            self.mostrar_mensagem(self.tr("A camada de suporte '{expected_support_name}' não possui feições.").format(expected_support_name=expected_support_name), "Erro")
            return

        sup_field_names = [fld.name() for fld in support_layer.fields()]

        # Ordena pelas distâncias, se existir "Acumula_dist"
        if "Acumula_dist" in sup_field_names:
            feats_support.sort(key=lambda sf: sf["Acumula_dist"])
        else:
            feats_support.sort(key=lambda sf: sf.id())

        dist_s = []
        z_s = []

        for sf in feats_support:
            if "Acumula_dist" in sup_field_names and "Znovo" in sup_field_names:
                dist_s.append(sf["Acumula_dist"])
                z_s.append(sf["Znovo"])

        if not dist_s:
            self.mostrar_mensagem(self.tr("Camada {layer_name} não possui valores '{field_dist}' e '{field_z}' válidos.").format(layer_name=support_layer.name(), field_dist="Acumula_dist", field_z="Znovo"), "Erro")
            return

        # 8a) Plota a linha do terreno (vermelho)
        self.graphWidget.plot(dist_s, z_s, pen=pg.mkPen(color='red', width=2), symbol=None, name=self.tr("Terreno Natural"))

        # 8b) Constrói as linhas verticais in range / out range específicas desse suporte
        inrange_x = []
        inrange_y = []
        outrange_x = []
        outrange_y = []
        comp_x = []
        comp_y = []
        magenta_x = []
        magenta_y = []

        for i in range(len(dist_e)):
            x_val = dist_e[i]
            cota_val = cota_e[i]
            
            # Interpola no dist_s para obter z_val
            z_val = np.interp(x_val, dist_s, z_s)
            alt_val = cota_val - z_val

            # in range vs out range (corrigido com tolerância)
            if lower_lim - 1e-6 <= alt_val <= upper_lim + 1e-6:
                inrange_x.extend([x_val, x_val, np.nan])
                inrange_y.extend([z_val, cota_val, np.nan])
            else:
                outrange_x.extend([x_val, x_val, np.nan])
                outrange_y.extend([z_val, cota_val, np.nan])

            # Diferença (compValue - CotaEstaca)
            diff_cota = compValue - cota_val
            if diff_cota > 0:
                comp_x.extend([x_val, x_val, np.nan])
                comp_y.extend([cota_val, cota_val - diff_cota, np.nan])

            # Diferença (compValue - AlturaEstaca) -> compValue - (cota - z)
            diff_alt = compValue - alt_val
            if diff_alt > 0:
                magenta_x.extend([x_val, x_val, np.nan])
                magenta_y.extend([z_val, z_val - diff_alt, np.nan])

        pen_inrange = pg.mkPen(color='blue', width=3, style=Qt.PenStyle.DashLine)
        self.graphWidget.plot(
            inrange_x, inrange_y,
            pen=pen_inrange,
            name=self.tr("AlturaEstaca (Dentro)"))

        pen_outrange = pg.mkPen(color='red', width=3, style=Qt.PenStyle.DashLine)
        self.graphWidget.plot(
            outrange_x, outrange_y,
            pen=pen_outrange,
            name=self.tr("AlturaEstaca (Fora)"))

        if comp_x:
            pen_comp = pg.mkPen(color='darkRed', width=2)
            self.graphWidget.plot(
                comp_x, comp_y,
                pen=pen_comp,
                name=self.tr("Dif (Comp - Cota)"))

        if magenta_x:
            pen_magenta = pg.mkPen(color='magenta', width=6)
            self.graphWidget.plot(
                magenta_x, magenta_y,
                pen=pen_magenta,
                name=self.tr("Estaca Aterrada"))

        # 8c) Definimos self.support_x e self.support_y para o crosshair:
        self.support_x = dist_s
        self.support_y = z_s

        # 9) Linha "Perfil + 10cm"
        perfil_plus10 = [valor + 0.10 for valor in cota_e]
        Q = int(self.spinBoxQ.value())
        if Q < 1:
            Q = 1

        x_start = dist_e[0]
        x_end = dist_e[-1]
        total_length = x_end - x_start
        gap = 0.05

        if Q > 1:
            drawn_length = total_length - (Q - 1) * gap
            if drawn_length < 0:
                drawn_length = 0
        else:
            drawn_length = total_length

        segment_length = drawn_length / Q if Q else 0
        seg_x = []
        seg_y = []

        for i in range(Q):
            seg_x_start = x_start + i * (segment_length + gap)
            seg_x_end = seg_x_start + segment_length
            y_seg_start = np.interp(seg_x_start, dist_e, perfil_plus10)
            y_seg_end = np.interp(seg_x_end, dist_e, perfil_plus10)
            seg_x.extend([seg_x_start, seg_x_end, np.nan])
            seg_y.extend([y_seg_start, y_seg_end, np.nan])

        pen_perfil_plus10 = pg.mkPen(color='blue', width=5, style=Qt.PenStyle.SolidLine)
        pen_perfil_plus10.setCapStyle(Qt.PenCapStyle.SquareCap)
        self.graphWidget.plot(
            seg_x, seg_y,
            pen=pen_perfil_plus10,
            name=self.tr("Módulos" ))

        # 10) Ajuste automático
        self.graphWidget.enableAutoRange(axis=pg.ViewBox.XYAxes, enable=True)

        # 11) Crosshair
        self.vLine = pg.InfiniteLine(angle=90, pen=pg.mkPen(color='green', width=1))
        self.hLine = pg.InfiniteLine(angle=0, pen=pg.mkPen(color='green', width=1))
        self.graphWidget.addItem(self.vLine, ignoreBounds=True)
        self.graphWidget.addItem(self.hLine, ignoreBounds=True)
        self.vLine.hide()
        self.hLine.hide()

        self.coord_text = pg.TextItem("", anchor=(0,1), color='white')
        self.graphWidget.addItem(self.coord_text)
        self.coord_text.hide()

        # 12) Conecta o movimento do mouse ao crosshair
        try:
            self.graphWidget.scene().sigMouseMoved.disconnect(self.mouse_moved)
        except Exception:
            pass  # nosec B110
        self.graphWidget.scene().sigMouseMoved.connect(self.mouse_moved)

    def _calcular_tudo_generator(self, point_layer, all_features, chunk_size, delta1, delta2, raster_layer, raster_name):
        """
        Gera (yield) um bloco por vez de feições já processadas.
        Cada vez que o caller chamar next(...), um bloco será calculado e a camada criada.
        """
        total_feats = len(all_features)
        start_index = 0
        block_number = 1  # só para informação de progresso

        while start_index < total_feats:
            end_index = start_index + chunk_size
            block_feats = all_features[start_index:end_index]

            # Monta lista de pontos (x,y,z)
            point_list = []
            for feat in block_feats:
                geom = feat.geometry()
                if geom.isEmpty():
                    continue
                pt = geom.asPoint()
                x, y = pt.x(), pt.y()

                # Z: do raster ou do atributo de altimetria
                if raster_layer:
                    z_value = self.get_z_from_raster(raster_layer, x, y)
                    if z_value is None:
                        z_value = 0.0
                else:
                    # Usa campo de altimetria genérico (não só 'Z')
                    z_value = self._get_z_from_attribute(point_layer, feat)

                # 🔹 AGORA sim, adiciona para cada feição
                point_list.append((x, y, z_value))

            # Se menos de 2 pontos, pula este bloco
            if len(point_list) < 2:
                start_index = end_index
                block_number += 1
                continue

            # Interpola entre o primeiro e o último
            x0, y0, z0 = point_list[0]
            x1, y1, z1 = point_list[-1]

            cota_first = z0 + delta1
            cota_last  = z1 + delta2
            dist_total = math.sqrt((x1 - x0) ** 2 + (y1 - y0) ** 2)
            dc = cota_last - cota_first

            final_feats = []
            for (xx, yy, zz) in point_list:
                if dist_total > 0:
                    frac = math.sqrt((xx - x0) ** 2 + (yy - y0) ** 2) / dist_total
                else:
                    frac = 0.0
                cota_estaca   = cota_first + dc * frac
                altura_estaca = cota_estaca - zz
                final_feats.append((
                    round(xx, 3),
                    round(yy, 3),
                    round(zz, 3),
                    round(cota_estaca, 3),
                    round(altura_estaca, 3)))

            # 🔹 Nome da camada agora usa a mesma lógica global
            layer_name = self.generate_layer_name(raster_name)

            # Cria a camada e adiciona ao grupo 'Estruturas'
            new_layer   = self.create_point_layer(layer_name, final_feats)
            final_layer = self.add_layer_to_group(new_layer, "Estruturas")
            self.set_label_for_layer(final_layer)

            # Camada de suporte, se tiver raster
            if raster_layer:
                self.create_support_points_layer(final_layer, raster_layer)

            # Devolve info deste bloco
            yield {
                "block_number": block_number,
                "layer": final_layer,
                "count_feats": len(point_list)}

            # Próximo bloco
            start_index = end_index
            block_number += 1

    def mostrar_mensagem(self, texto, tipo, duracao=3, caminho_pasta=None, caminho_arquivo=None, forcar=False):
        """
        Exibe uma mensagem na barra de mensagens do QGIS, proporcionando feedback ao usuário
        baseado nas ações realizadas.
        Agora ela respeita um "cadeado" (self._lock_messagebar) para não sobrepor barras
        de progresso que estejam sendo exibidas.

        :param texto: Texto da mensagem a ser exibida.
        :param tipo: Tipo da mensagem ("Erro" ou "Sucesso") que determina a cor e o ícone da mensagem.
        :param duracao: Duração em segundos durante a qual a mensagem será exibida (padrão é 3 segundos).
        :param caminho_pasta: Caminho da pasta a ser aberta ao clicar no botão (padrão é None).
        :param caminho_arquivo: Caminho do arquivo a ser executado ao clicar no botão (padrão é None).
        :param forcar: Se True, mostra na barra mesmo que ela esteja "travada" por uma barra de progresso.
        """
        # se o messageBar estiver "reservado" por uma barra de progresso, não vamos empurrar nada
        # a menos que o chamador peça explicitamente (forcar=True)
        if getattr(self, "_lock_messagebar", False) and not forcar:
            # manda pro log do QGIS para não perder a mensagem
            # (Menu → Exibir → Painéis → Registro de mensagens → "Tempo Salvo Tools")
            QgsMessageLog.logMessage(f"{tipo}: {texto}", "Tempo Salvo Tools", level=Qgis.MessageLevel.Info)
            return

        # barra de mensagens do QGIS
        bar = self.iface.messageBar()

        if tipo == "Erro":
            bar.pushMessage(self.tr("Erro"), texto, level=Qgis.MessageLevel.Critical, duration=duracao)

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
            # caso venha "Info" ou outro tipo
            bar.pushMessage("Info", texto, level=Qgis.MessageLevel.Info, duration=duracao)

    def _w_alive(self, w):
        """Retorna True se o widget ainda é válido (não foi deletado)."""
        return (w is not None) and (not sip.isdeleted(w))

    def calcular_tudo(self):
        """
        Inicia o processamento em blocos (não bloqueante) para criar as camadas M1, M2, ...
        a partir da camada de pontos selecionada.
        """
        # se já tinha um processamento anterior, finaliza silenciosamente
        if hasattr(self, "_calc_tudo_iter") and self._calc_tudo_iter:
            self._finalizar_calcular_tudo(mensagem_ok=False)

        layer_id = self.comboBoxPontos.currentData()
        point_layer = QgsProject.instance().mapLayer(layer_id)
        if not point_layer or not isinstance(point_layer, QgsVectorLayer):
            self.mostrar_mensagem(self.tr("Nenhuma camada de pontos válida foi selecionada."), "Erro")
            return
        if point_layer.geometryType() != QgsWkbTypes.GeometryType.PointGeometry:
            self.mostrar_mensagem(self.tr("A camada selecionada não é de pontos."), "Erro")
            return

        chunk_size = self.spinBoxSelec.value()
        if chunk_size < 2:
            self.mostrar_mensagem(self.tr("Para criar camadas por bloco, selecione no mínimo 2 no spinBoxSelec."), "Erro")
            return

        delta1 = self.doubleSpinBox_1.value()
        delta2 = self.doubleSpinBox_2.value()

        raster_layer_id = self.comboBoxRaster.currentData()
        raster_layer = QgsProject.instance().mapLayer(raster_layer_id) if raster_layer_id else None
        raster_name = raster_layer.name() if raster_layer else ""

        # Se não tem raster, vamos resolver o campo de altimetria AGORA (e permitir cancelar tudo)
        if not raster_layer:
            try:
                self._get_altimetria_field_name(point_layer)
            except UserCancelled:
                self.mostrar_mensagem(self.tr("Operação cancelada pelo usuário."), "Info", duracao=2, forcar=False)
                return

        all_features = list(point_layer.getFeatures())
        total_feats = len(all_features)
        if total_feats < 2:
            self.mostrar_mensagem(self.tr("A camada de pontos não possui feições suficientes."), "Erro")
            return

        num_chunks = math.ceil(total_feats / chunk_size)

        progressBar, progressMessageBar = self.iniciar_progress_bar(num_chunks, titulo=self.tr("Calcular Tudo (M1, M2, ...)"), bind_calc_tudo=True, cancel_on_close=True)

        progressBar.setValue(0)

        self._calc_tudo_iter = self._calcular_tudo_generator(point_layer=point_layer, all_features=all_features, chunk_size=chunk_size, delta1=delta1, delta2=delta2, raster_layer=raster_layer, raster_name=raster_name)

        self._calc_tudo_total_chunks = num_chunks
        self._calc_tudo_done_chunks = 0

        self.mostrar_mensagem(self.tr("Serão criadas {num_chunks} novas camadas, cada bloco terá até {chunk_size} feições.").format(num_chunks=num_chunks, chunk_size=chunk_size), "Sucesso", duracao=2, forcar=False)

        QTimer.singleShot(0, self._processar_proximo_bloco)

    def _processar_proximo_bloco(self):
        """
        Processa UM bloco do gerador e agenda o próximo.
        Quando acabar, atualiza UI e fecha barra.
        """
        # se o gerador já foi cancelado / dock fechado, sai
        if not getattr(self, "_calc_tudo_iter", None):
            return
        try:
            bloco_info = next(self._calc_tudo_iter)

        except StopIteration:
            self._finalizar_calcular_tudo()
            return

        except UserCancelled:
            self._finalizar_calcular_tudo(mensagem_ok=False)
            self.mostrar_mensagem(self.tr("Processo cancelado."), "Info", duracao=2, forcar=True)
            return

        except Exception as e:
            self._finalizar_calcular_tudo(mensagem_ok=False)
            self.mostrar_mensagem(self.tr("Erro ao processar bloco: {error}").format(error=str(e)), "Erro", forcar=True)
            return

        # 1 bloco processado
        self._calc_tudo_done_chunks += 1

        # atualiza barra **apenas se ela ainda existir**
        pb = getattr(self, "_calc_tudo_progressBar", None)
        if self._w_alive(pb):
            try:
                pb.setValue(self._calc_tudo_done_chunks)
            except RuntimeError:
                # widget morreu entre o if e o setValue
                self._calc_tudo_progressBar = None
                self._calc_tudo_progressMsg = None
                self._lock_messagebar = False
        else:
            # se não existe mais barra → não tenta recriar
            self._calc_tudo_progressBar = None
            self._calc_tudo_progressMsg = None
            self._lock_messagebar = False

        # ainda tem blocos? agenda o próximo
        if self._calc_tudo_done_chunks < getattr(self, "_calc_tudo_total_chunks", 0):
            QTimer.singleShot(10, self._processar_proximo_bloco)
        else:
            # por segurança, se o gerador ainda não deu StopIteration
            self._finalizar_calcular_tudo()

    def _finalizar_calcular_tudo(self, mensagem_ok=True):
        """
        Finaliza o processo assíncrono de 'Calcular Tudo':
        - Fecha e remove a barra de progresso, se ainda existir.
        - Limpa variáveis internas de controle do processamento em blocos.
        - Libera o uso da messageBar (destrava _lock_messagebar).
        - Opcionalmente exibe uma mensagem de sucesso ao usuário.
        """
        # Fecha o widget de barra de progresso se ainda estiver vivo no messageBar
        try:
            if self._w_alive(getattr(self, "_calc_tudo_progressMsg", None)):
                self.iface.messageBar().popWidget(self._calc_tudo_progressMsg)
        except Exception:
            # Qualquer erro ao remover a barra é ignorado para não quebrar o fluxo
            pass  # nosec B110

        # Limpa estado interno do processamento em blocos
        self._calc_tudo_progressBar = None     # Referência da QProgressBar
        self._calc_tudo_progressMsg = None     # Widget de mensagem da barra
        self._calc_tudo_iter = None            # Gerador usado no cálculo em blocos
        self._calc_tudo_total_chunks = 0       # Número total de blocos previstos
        self._calc_tudo_done_chunks = 0        # Quantidade de blocos já processados
        self._lock_messagebar = False          # Libera a messageBar para outras mensagens

        # Mostra mensagem de sucesso ao final, se desejado
        if mensagem_ok:
            self.mostrar_mensagem(self.tr("Processo concluído! Verifique as camadas criadas no grupo 'Estruturas'."), "Sucesso", duracao=3, forcar=False)

    def set_label_for_layer(self, layer):
        """
        Configura rótulos e cores para a camada, exibindo:
          - 'sequencia' e 'AlturaEstaca' em duas linhas
          - Texto em negrito, maior
          - Posição à direita dos pontos, com deslocamento horizontal
          - Cor baseada na regra do update_tableView_2 (azul ou vermelho).
        """
        # 1) Obter limites da lógica de cor (update_tableView_2)
        padraoValue = self.doubleSpinBoxPadrao.value()
        variaValue  = self.doubleSpinBoxVaria.value()
        lower_lim = padraoValue - variaValue
        upper_lim = padraoValue + variaValue

        # # 2) Expressão para cor: azul se dentro do intervalo; vermelho se fora

        color_expression = f"""
            CASE
                WHEN "AlturaEstaca" >= {lower_lim} AND "AlturaEstaca" <= {upper_lim}
                    THEN color_rgb(0,0,255)      -- azul
                ELSE
                    color_rgb(255,0,0)           -- vermelho
                END
        """
        # 3) Expressão de RÓTULO (duas linhas)

        label_expression = "\"sequencia\" || '\n' || \"AlturaEstaca\""

        # 4) Configurar estilo do texto (QFont + QgsTextFormat)

        text_format = QgsTextFormat()

        # 5) Configurar PalLayerSettings
        pal_settings = QgsPalLayerSettings()
        pal_settings.enabled = True
        pal_settings.isExpression = True
        pal_settings.fieldName = label_expression  # expressão do rótulo
        pal_settings.format = text_format

        # Posição: usar OverPoint para rótulos de ponto
        pal_settings.placement = Qgis.LabelPlacement.OverPoint

        # Quadrante: à direita
        # (Veja a documentação do enum LabelQuadrantPosition para outras opções)
        pal_settings.quadOffset = QgsPalLayerSettings.QuadrantPosition.QuadrantRight

        # Em QGIS 3.30+, defina deslocamento via xOffset/yOffset:
        pal_settings.xOffset = 10  # Experimente valores maiores para notar claramente
        pal_settings.yOffset = 0
        pal_settings.offsetUnits = QgsUnitTypes.RenderUnit.RenderPixels

        # Propriedades definidas por dados: cor do texto
        ddp = pal_settings.dataDefinedProperties()
        ddp.setProperty(QgsPalLayerSettings.Property.Color, QgsProperty.fromExpression(color_expression))
        # Se quiser forçar um tamanho de fonte via expressão, pode usar:
        #   ddp.setProperty(QgsPalLayerSettings.Size, QgsProperty.fromValue(14))
        pal_settings.setDataDefinedProperties(ddp)

        # 6) Aplicar a rotulagem na camada
        layer.setLabelsEnabled(True)
        layer.setLabeling(QgsVectorLayerSimpleLabeling(pal_settings))

        # 7) Ajustar cor das feições (pontos) via renderer, mesma lógica azul/vermelho
        renderer = layer.renderer()
        if renderer:
            symbol = renderer.symbol()
            if symbol and symbol.symbolLayerCount() > 0:
                sym_layer = symbol.symbolLayer(0)

                ddp_sym = sym_layer.dataDefinedProperties()
                ddp_sym.setProperty(
                    QgsSymbolLayer.Property.PropertyFillColor,
                    QgsProperty.fromExpression(color_expression))
                ddp_sym.setProperty(
                    QgsSymbolLayer.Property.PropertyStrokeColor,
                    QgsProperty.fromExpression(color_expression))
                sym_layer.setDataDefinedProperties(ddp_sym)

        # 8) Forçar repaint e refrescar o mapa
        layer.triggerRepaint()
        try:
            iface.mapCanvas().refreshAllLayers()
        except Exception:
            pass  # nosec B110

    def sync_spinboxes_from_layer(self, lyr: QgsVectorLayer):
        """
        Lê o primeiro e o último ponto da camada de estruturas selecionada
        e coloca nos doubleSpinBox_1 e doubleSpinBox_2 os deltas usados
        (CotaEstaca - Z) do início e do fim.

        Se a camada não tiver Z ou CotaEstaca, não faz nada.
        """
        if not lyr:
            return

        field_names = [f.name() for f in lyr.fields()]
        if "Z" not in field_names or "CotaEstaca" not in field_names:
            # nada pra sincronizar
            return

        feats = list(lyr.getFeatures())
        if not feats:
            return

        # mesma ordem que você já usa nas outras partes
        if "sequencia" in field_names:
            def _seq_num(ft):
                try:
                    idxE = ft["sequencia"].index("E")
                    return int(ft["sequencia"][idxE+1:])
                except Exception:
                    return ft.id()
            feats.sort(key=_seq_num)
        else:
            feats.sort(key=lambda f: f.id())

        if len(feats) == 1:
            first = last = feats[0]
        else:
            first = feats[0]
            last  = feats[-1]

        try:
            z_first = float(first["Z"])
            c_first = float(first["CotaEstaca"])
            delta1  = c_first - z_first
        except Exception:
            delta1 = 0.0

        try:
            z_last = float(last["Z"])
            c_last = float(last["CotaEstaca"])
            delta2 = c_last - z_last
        except Exception:
            delta2 = 0.0

        # aplica sem disparar recalc
        self.doubleSpinBox_1.blockSignals(True)
        self.doubleSpinBox_1.setValue(round(delta1, 3))
        self.doubleSpinBox_1.blockSignals(False)

        self.doubleSpinBox_2.blockSignals(True)
        self.doubleSpinBox_2.setValue(round(delta2, 3))
        self.doubleSpinBox_2.blockSignals(False)

    def escolher_local_para_salvar(self, nome_padrao, tipo_arquivo):
        """
        Abre uma caixa de diálogo para o usuário escolher onde salvar o arquivo.

        - Usa `nome_padrao` como base para o nome do arquivo.
        - Garante que o arquivo terá a extensão correta (derivada de `tipo_arquivo`, se necessário).
        - Incrementa automaticamente (_1, _2, ...) se já existir arquivo com o mesmo nome.
        - Lembra o último diretório utilizado via QSettings ("lastDir").
        - Retorna o caminho completo escolhido ou None se o usuário cancelar.
        """
        # Acessa as configurações do QGIS para recuperar o último diretório utilizado
        settings = QSettings()
        lastDir = settings.value("lastDir", "")  # Usa uma string vazia como padrão se não houver último diretório

        # Configura as opções da caixa de diálogo para salvar arquivos
        options = QFileDialog.Options()
        
        # Gera o nome e a extensão do arquivo
        base_nome_padrao, extensao = os.path.splitext(nome_padrao)
        if not extensao:  # Caso o nome não inclua uma extensão, extrair do tipo_arquivo
            extensao = tipo_arquivo.split("*.")[-1].replace(")", "")
        numero = 1
        nome_proposto = base_nome_padrao

        # Incrementa o número no nome até encontrar um nome que não exista
        while os.path.exists(os.path.join(lastDir, nome_proposto + "." + extensao)):
            nome_proposto = f"{base_nome_padrao}_{numero}"
            numero += 1

        # Propõe o nome completo no último diretório utilizado
        nome_completo_proposto = os.path.join(lastDir, nome_proposto + "." + extensao)

        # Exibe a caixa de diálogo para salvar arquivos com o nome proposto
        fileName, _ = QFileDialog.getSaveFileName(self, self.tr("Salvar Camada"), nome_completo_proposto, tipo_arquivo, options=options)

        # Verifica se um nome de arquivo foi escolhido
        if fileName:
            # Atualiza o último diretório usado nas configurações do QGIS
            settings.setValue("lastDir", os.path.dirname(fileName))

            # Assegura que o arquivo tenha a extensão correta
            if not fileName.endswith(f".{extensao}"):
                fileName += f".{extensao}"

        return fileName  # Retorna o caminho completo do arquivo escolhido ou None se cancelado

    def exportar_camadas_para_gpkg(self, layers, caminho_arquivo):
        """
        Exporta todas as camadas vetoriais passadas em 'layers' para um único
        arquivo GeoPackage em 'caminho_arquivo'.

        Cada camada vira uma tabela no GPKG com o nome da própria camada.
        Os dados (CotaEstaca, AlturaEstaca, etc.) ficam preservados para
        reuso posterior sem precisar recalcular.
        """
        context = QgsProject.instance().transformContext()
        erros = []
        primeira = True

        total_layers = len(layers)
        if total_layers <= 0:
            self.mostrar_mensagem(self.tr("Nenhuma camada para exportar."), "Erro")
            return

        # Barra de progresso para exportação do GPKG
        progressBar, progressMessageBar = self.iniciar_progress_bar(total_layers, titulo=self.tr("Exportando GeoPackage do grupo 'Estruturas'..."))
        current_step = 0

        try:
            for layer in layers:
                options = QgsVectorFileWriter.SaveVectorOptions()
                options.driverName = "GPKG"
                options.layerName = layer.name()

                # Primeira camada: cria/zera o arquivo; demais: apenas cria/sobrescreve a layer
                if primeira:
                    options.actionOnExistingFile = QgsVectorFileWriter.ActionOnExistingFile.CreateOrOverwriteFile
                    primeira = False
                else:
                    options.actionOnExistingFile = QgsVectorFileWriter.ActionOnExistingFile.CreateOrOverwriteLayer

                error, error_message = QgsVectorFileWriter.writeAsVectorFormatV2(
                    layer, caminho_arquivo, context, options)

                if error != QgsVectorFileWriter.WriterError.NoError:
                    erros.append(f"{layer.name()}: {error_message}")

                # Atualiza barra de progresso
                current_step += 1
                if self._w_alive(progressBar):
                    try:
                        progressBar.setValue(current_step)
                    except RuntimeError:
                        pass  # nosec B110
                QApplication.processEvents()

        finally:
            # Garante que a barra seja removida e o messageBar desbloqueado
            self._clear_progress_bar_if_any()

        if erros:
            msg = self.tr("Algumas camadas não foram exportadas:\n{errors}").format(errors="\n".join(erros))
            self.mostrar_mensagem(msg, "Erro")
        else:
            pasta = os.path.dirname(caminho_arquivo)
            self.mostrar_mensagem(self.tr("GeoPackage do grupo 'Estruturas' exportado com sucesso!"), "Sucesso", caminho_pasta=pasta, caminho_arquivo=caminho_arquivo)

    def iniciar_progress_bar(self, total_steps, titulo=None, *, bind_calc_tudo=False, cancel_on_close=False):
        """
        Cria e exibe uma barra de progresso persistente na messageBar do QGIS.
        - bind_calc_tudo=True: armazena refs em _calc_tudo_* (usado apenas pelo Calcular Tudo)
        - cancel_on_close=True: se o usuário fechar no X durante execução, cancela a operação vinculada
        """
        if titulo is None:
            titulo = self.tr("Gerando...")

        bar = self.iface.messageBar()
        progressMessageBar = bar.createMessage(titulo)

        progressBar = QProgressBar(progressMessageBar)
        progressBar.setAlignment(Qt.AlignmentFlag.AlignLeft | Qt.AlignmentFlag.AlignVCenter)
        progressBar.setFormat(self.tr("%p% - %v de %m etapas concluídas"))
        progressBar.setMinimumWidth(300)

        progressMessageBar.layout().addWidget(progressBar)
        bar.pushWidget(progressMessageBar, Qgis.MessageLevel.Info, 0)

        progressBar.setMaximum(total_steps)
        progressBar.setValue(0)

        # trava messageBar enquanto esta barra existir
        self._lock_messagebar = True

        if bind_calc_tudo:
            self._calc_tudo_progressBar = progressBar
            self._calc_tudo_progressMsg = progressMessageBar
            self._calc_tudo_cancelled = False

        def _on_pb_destroyed(*_):
            # sempre libera a messageBar
            self._lock_messagebar = False

            if bind_calc_tudo:
                self._calc_tudo_progressBar = None
                self._calc_tudo_progressMsg = None

                # Se estava rodando e o usuário fechou -> cancela
                if cancel_on_close and getattr(self, "_calc_tudo_iter", None):
                    self._calc_tudo_cancelled = True
                    self._calc_tudo_iter = None
                    self._calc_tudo_total_chunks = 0
                    self._calc_tudo_done_chunks = 0

                    # evita mexer na UI "no meio" da destruição
                    QTimer.singleShot(0, lambda: self.mostrar_mensagem(self.tr("Processo cancelado (barra fechada)."), "Info", duracao=2, forcar=True))

        progressBar.destroyed.connect(_on_pb_destroyed)
        progressMessageBar.destroyed.connect(_on_pb_destroyed)

        return progressBar, progressMessageBar

    def obter_camadas_e_caminho_gpkg(self):
        """
        Busca todas as camadas vetoriais dentro do grupo 'Estruturas'
        e pergunta ao usuário onde salvar o GeoPackage.
        Retorna (layers, caminho_arquivo) ou None se cancelar/erro.
        """
        root = QgsProject.instance().layerTreeRoot()
        grupo_estruturas = None

        # Localiza o grupo 'Estruturas'
        for child in root.children():
            if isinstance(child, QgsLayerTreeGroup) and child.name() == self.tr("Estruturas"):
                grupo_estruturas = child
                break

        if not grupo_estruturas:
            self.mostrar_mensagem(self.tr("O grupo 'Estruturas' não foi encontrado no projeto."), "Erro")
            return None

        # Coleta todas as camadas vetoriais do grupo (independente do tipo geométrico)
        layers = []
        for child in grupo_estruturas.children():
            if isinstance(child, QgsLayerTreeLayer):
                layer = child.layer()
                if layer and layer.type() == QgsMapLayer.LayerType.VectorLayer:
                    layers.append(layer)

        if not layers:
            self.mostrar_mensagem(self.tr("Nenhuma camada vetorial foi encontrada no grupo 'Estruturas'."), "Erro")
            return None

        # Escolhe o local para salvar o GeoPackage
        nome_padrao = self.tr("Estruturas")
        caminho_arquivo = self.escolher_local_para_salvar(nome_padrao, self.tr("GeoPackage (*.gpkg)"))
        if not caminho_arquivo:
            return None  # Usuário cancelou

        return (layers, caminho_arquivo)

    def pushButtonExportarGPKG_clicked(self):
        """
        Handler do botão que exporta todas as camadas do grupo 'Estruturas'
        para um único arquivo GeoPackage.
        """
        result = self.obter_camadas_e_caminho_gpkg()
        if result:
            layers, caminho_arquivo = result
            self.exportar_camadas_para_gpkg(layers, caminho_arquivo)

    def _add_existing_layer_to_group(self, layer, group_name=None):
        """
        Adiciona uma camada já existente no projeto ao grupo informado (padrão: 'Estruturas').

        - Cria o grupo se ele ainda não existir.
        - Garante que a camada esteja registrada no QgsProject.
        - Adiciona a camada ao QgsLayerTreeGroup correspondente.
        """
        if group_name is None:
            group_name = self.tr("Estruturas")

        root = QgsProject.instance().layerTreeRoot()

        # Procura o grupo pelo nome entre os filhos da raiz
        group = next(
            (g for g in root.children()
             if isinstance(g, QgsLayerTreeGroup) and g.name() == group_name), None)

        # Se o grupo não existir, cria um novo com o nome fornecido
        if not group:
            group = root.addGroup(group_name)

        # Evita duplicar a mesma layer no projeto
        if layer.id() not in QgsProject.instance().mapLayers().keys():
            QgsProject.instance().addMapLayer(layer, False)  # adiciona a camada sem criar nó na raiz

        # Adiciona a camada ao grupo (nó do layer tree)
        group.addLayer(layer)

    def pushButtonAdicionar_clicked(self):
        """
        Importa camadas M# e *_Suporte de um GeoPackage para o grupo 'Estruturas',
        com barra de progresso, mas agora otimizada:
          - Canvas congelado durante a importação
          - Sinais do projeto bloqueados no loop
          - Rótulos aplicados ao final
          - Atualizações da UI e barra de progresso com throttle
        """
        file_path, _ = QFileDialog.getOpenFileName(self, self.tr("Abrir GeoPackage"), "", "GeoPackage (*.gpkg)")
        if not file_path:
            return
        if not os.path.exists(file_path):
            self.mostrar_mensagem(self.tr("Arquivo GeoPackage não encontrado."), "Erro", forcar=True)
            return

        # Lê as tabelas de feições do GPKG
        try:
            conn = sqlite3.connect(file_path)
            cur = conn.cursor()
            cur.execute("SELECT table_name FROM gpkg_contents WHERE data_type='features'")
            layer_names = [r[0] for r in cur.fetchall()]
            conn.close()
        except Exception as e:
            self.mostrar_mensagem(self.tr("Não foi possível ler o GeoPackage:\n{error}").format(error=str(e)), "Erro", forcar=True)
            return

        if not layer_names:
            self.mostrar_mensagem(self.tr("GeoPackage não possui camadas de feições."), "Erro", forcar=True)
            return

        # Garante o grupo 'Estruturas'
        root = QgsProject.instance().layerTreeRoot()
        grupo_estruturas = None
        for child in root.children():
            if isinstance(child, QgsLayerTreeGroup) and child.name() == self.tr("Estruturas"):
                grupo_estruturas = child
                break
        if not grupo_estruturas:
            grupo_estruturas = root.addGroup(self.tr("Estruturas"))

        if not hasattr(self, "support_layers"):
            self.support_layers = []

        re_main = re.compile(r"^M\d+(\b|_)")
        added_main = 0
        added_support = 0
        skipped = []

        def fields_ok(vl, required):
            names = {f.name() for f in vl.fields()}
            return all(r in names for r in required)

        total_steps = len(layer_names)
        progressBar = None
        if total_steps > 0:
            progressBar, progressMessageBar = self.iniciar_progress_bar(total_steps, titulo=self.tr("Importando camadas do GeoPackage..."))

        # ⚡ otimizações de UI
        canvas = self.iface.mapCanvas()
        project = QgsProject.instance()
        mains_to_style = []  # aplicamos rótulos no final
        throttle_each = max(1, total_steps // 60)  # atualiza barra ~60 vezes
        current_step = 0

        try:
            # congelar render e sinais (reduz MUITO redraw/overhead)
            try:
                canvas.setRenderFlag(False)
            except Exception:
                pass  # nosec B110
            try:
                project.blockSignals(True)
            except Exception:
                pass  # nosec B110

            for name in layer_names:
                is_support = name.endswith(self.tr("_Suporte"))
                is_main = bool(re_main.match(name)) and not is_support

                if not (is_main or is_support):
                    skipped.append(self.tr("{name} (nome não reconhecido)").format(name=name))
                    current_step += 1
                    if progressBar and self._w_alive(progressBar) and (current_step % throttle_each == 0 or current_step == total_steps):
                        try:
                            progressBar.setValue(current_step)
                        except RuntimeError:
                            pass  # nosec B110
                    continue

                uri = f"{file_path}|layername={name}"
                vl = QgsVectorLayer(uri, name, "ogr")
                if not vl.isValid():
                    skipped.append(self.tr("{name} (camada inválida)").format(name=name))
                    current_step += 1
                    if progressBar and self._w_alive(progressBar) and (current_step % throttle_each == 0 or current_step == total_steps):
                        try:
                            progressBar.setValue(current_step)
                        except RuntimeError:
                            pass  # nosec B110
                    continue

                if vl.geometryType() != QgsWkbTypes.GeometryType.PointGeometry:
                    skipped.append(self.tr("{name} (não é camada de pontos)").format(name=name))
                    current_step += 1
                    if progressBar and self._w_alive(progressBar) and (current_step % throttle_each == 0 or current_step == total_steps):
                        try:
                            progressBar.setValue(current_step)
                        except RuntimeError:
                            pass  # nosec B110
                    continue

                if is_main and not fields_ok(vl, ["X", "Y", "Z", "CotaEstaca", "AlturaEstaca"]):
                    skipped.append(self.tr("{name} (faltam campos {fields})").format(name=name, fields="X, Y, Z, CotaEstaca, AlturaEstaca"))
                    current_step += 1
                    if progressBar and self._w_alive(progressBar) and (current_step % throttle_each == 0 or current_step == total_steps):
                        try:
                            progressBar.setValue(current_step)
                        except RuntimeError:
                            pass  # nosec B110
                    continue

                if is_support and not fields_ok(vl, ["Acumula_dist", "Znovo"]):
                    skipped.append(self.tr("{name} (faltam campos {fields})").format(name=name, fields="Acumula_dist, Znovo"))
                    current_step += 1
                    if progressBar and self._w_alive(progressBar) and (current_step % throttle_each == 0 or current_step == total_steps):
                        try:
                            progressBar.setValue(current_step)
                        except RuntimeError:
                            pass  # nosec B110
                    continue

                # adiciona ao projeto (sem redesenhar) e move para o grupo
                project.addMapLayer(vl, False)
                grupo_estruturas.addLayer(vl)

                if is_main:
                    mains_to_style.append(vl)
                    added_main += 1
                if is_support:
                    self.support_layers.append(vl)
                    added_support += 1

                # throttle da barra
                current_step += 1
                if progressBar and self._w_alive(progressBar) and (current_step % throttle_each == 0 or current_step == total_steps):
                    try:
                        progressBar.setValue(current_step)
                    except RuntimeError:
                        pass  # nosec B110

            # aplica rótulos depois que tudo está dentro do projeto (canvas ainda congelado)
            for vl in mains_to_style:
                try:
                    self.set_label_for_layer(vl)
                except Exception as e:
                    self.mostrar_mensagem(self.tr("Erro ao aplicar estilo em {layer_name}: {error}").format(layer_name=vl.name(), error=str(e)), "Aviso")

        finally:
            # limpa barra e destrava UI/canvas
            self._clear_progress_bar_if_any()
            try:
                project.blockSignals(False)
            except Exception:
                pass  # nosec B110
            try:
                canvas.setRenderFlag(True)
                canvas.refreshAllLayers()
            except Exception:
                pass  # nosec B110

        # Atualizações únicas de UI no final
        self.update_list_widget_estruturas()
        self.atualizar_estado_pushButtonExportarDXF()
        self.update_scroll_area_dados()
        self.atualizar_estado_pushButtonExportarGPKG()

        # Feedback
        if added_main or added_support:
            msg = self.tr("Importadas {added_main} camada(s) M# e {added_support} camada(s) de suporte.").format(added_main=added_main, added_support=added_support)
            if skipped:
                msg += self.tr(" Ignoradas: {skipped_count}.").format(skipped_count=len(skipped))
            self.mostrar_mensagem(msg, "Sucesso", forcar=True)
        else:
            msg = self.tr("Nenhuma camada utilizável foi encontrada no GeoPackage.")
            if skipped:
                msg += self.tr(" Verifique nomes e campos.")
            self.mostrar_mensagem(msg, "Erro", forcar=True)

    def atualizar_estado_pushButtonExportarGPKG(self):
        """
        Habilita o botão pushButtonExportarGPKG somente se existir ao menos
        UMA camada vetorial no grupo 'Estruturas'.
        (Não interfere em outros grupos/camadas do projeto.)
        """
        try:
            root = QgsProject.instance().layerTreeRoot()
            grupo_estruturas = None
            for child in root.children():
                if isinstance(child, QgsLayerTreeGroup) and child.name() == self.tr("Estruturas"):
                    grupo_estruturas = child
                    break

            if not grupo_estruturas:
                self.pushButtonExportarGPKG.setEnabled(False)
                return

            tem_vetorial = False
            for child in grupo_estruturas.children():
                if isinstance(child, QgsLayerTreeLayer):
                    lyr = child.layer()
                    if lyr and lyr.type() == QgsMapLayer.LayerType.VectorLayer:
                        tem_vetorial = True
                        break

            self.pushButtonExportarGPKG.setEnabled(tem_vetorial)
        except Exception:
            # Em qualquer erro, por segurança, desabilita
            self.pushButtonExportarGPKG.setEnabled(False)

    def plot_layers(self, modo_pdf=False):
        """
        Coleta os dados da camada de estruturas selecionada e, se existir,
        da respectiva camada de apoio, calcula a distância acumulada
        e plota o gráfico com Matplotlib.

        - Se houver camada de apoio (<nome>_Suporte) → usa a lógica antiga (com raster).
        - Se NÃO houver camada de apoio → usa os próprios valores de Z da camada de
          estruturas como “terreno” (gráfico sem raster).
        """
        # Verifica se há uma camada de estruturas selecionada (no listWidget_Lista)
        if not self.current_estruturas_layer:
            self.mostrar_mensagem(self.tr("Nenhuma camada de estruturas selecionada."), "Erro")
            return

        estacas_layer = self.current_estruturas_layer

        # Procura a camada de apoio correspondente (com o nome "<nome_estacas>_Suporte")
        support_layer = None
        if hasattr(self, "support_layers"):
            for lyr in self.support_layers:
                if lyr.name() == self.tr("{layer_name}_Suporte").format(layer_name=estacas_layer.name()):
                    support_layer = lyr
                    break

        # Obtém os dados da camada de estruturas
        estacas_data = self.get_estacas_data(estacas_layer)
        if not estacas_data:
            self.mostrar_mensagem(self.tr("Nenhum dado encontrado na camada de estruturas."), "Erro")
            return

        # Ordena pela distância acumulada
        estacas_data.sort(key=lambda x: x[0])
        estacas_distances, estacas_cortes, z_values, desnivels, x_coords, y_coords = zip(*estacas_data)

        # Tenta obter os dados da camada de apoio, se ela existir
        apoio_distances = None
        apoio_elevations = None

        if support_layer:
            pontos_apoio_data = []
            for f in support_layer.getFeatures():
                try:
                    acumula_dist = f["Acumula_dist"]
                    znovo = f["Znovo"]
                except KeyError:
                    self.mostrar_mensagem(self.tr("A camada de apoio não possui os campos 'Acumula_dist' e 'Znovo'."), "Erro")
                    return
                pontos_apoio_data.append((acumula_dist, znovo))

            if not pontos_apoio_data:
                self.mostrar_mensagem(self.tr("Nenhum dado encontrado na camada de apoio."), "Erro")
                return

            pontos_apoio_data.sort(key=lambda x: x[0])
            apoio_distances, apoio_elevations = zip(*pontos_apoio_data)

        # Se NÃO houver camada de apoio (estrutura criada sem raster),
        # usamos os próprios valores de Z da camada de estruturas como "terreno".
        if apoio_distances is None or apoio_elevations is None:
            apoio_distances = estacas_distances
            apoio_elevations = z_values

        # Cria a estrutura da área do gráfico
        fig, ax = plt.subplots(figsize=(10, 6))
        fig.set_size_inches(15, 9)
        fig.subplots_adjust(left=0.08, right=0.98, bottom=0.12, top=0.9)

        # Se estiver exportando para PDF, coloca o nome da camada no topo da página
        if modo_pdf and self.current_estruturas_layer:
            fig.suptitle(self.current_estruturas_layer.name(), fontsize=14, fontweight='bold')

        # Determina limites de Y
        y_min0 = min(apoio_elevations) - 2
        y_min1 = min(min(estacas_cortes), y_min0) - 2
        y_max = max(max(estacas_cortes), max(apoio_elevations)) + 4
        ax.set_ylim(y_min1, y_max)

        # Ticks de 1 em 1 no eixo Y
        ax.yaxis.set_major_locator(plt.MultipleLocator(1))

        # Preenchendo a área abaixo da linha do terreno natural (apoio_elevations)
        ax.fill_between(apoio_distances, apoio_elevations, y_min0, color='lightgreen', alpha=0.5, hatch='***')

        # Desenha linhas verticais (exemplo: do eixo X até a CotaEstaca)
        ax.vlines(x=estacas_distances, ymin=0, ymax=estacas_cortes, colors='grey', linestyles='dashed', linewidth=0.5)

        # Cálculo de inclinações
        inclinacao_media_corte = self.calcular_inclinacao_media(estacas_distances, estacas_cortes)
        inclinacao_media_znovo = self.calcular_inclinacao_media(apoio_distances, apoio_elevations)

        # Adiciona textos das inclinações
        bbox_props = dict(boxstyle="round,pad=0.3", fc="white", ec="black", lw=1)
        ax.text(0.005, 1.016, self.tr("Inclinação do Perfil: {inclination:.3f}%").format(inclination=inclinacao_media_corte * 100), transform=ax.transAxes, color='blue', bbox=bbox_props)

        ax.text(0.005, 1.06, self.tr("Inclinação média do Terreno: {inclination:.3f}%").format(inclination=inclinacao_media_znovo * 100), transform=ax.transAxes, color='orange', bbox=bbox_props)

        # Interpolação dos valores de elevação do terreno natural para os pontos das estacas
        interp_apoio_elevations = np.interp(estacas_distances, apoio_distances, apoio_elevations)

        # Borda das linhas
        for xi, yi1, yi2 in zip(estacas_distances, estacas_cortes, interp_apoio_elevations):
            ax.vlines(xi, yi1, yi2, color='black', linewidth=4, alpha=0.8)

        # Linha interna
        for xi, yi1, yi2 in zip(estacas_distances, estacas_cortes, interp_apoio_elevations):
            ax.vlines(xi, yi1, yi2, color='silver', linewidth=2.5, alpha=1)

        # Define um afastamento para a barra de conexão das setas
        afastamento_barra = -0.15
        deslocamento_x = 0.30

        # Limites para lógica azul / vermelho (mesma usada em AlturaEstaca)
        padraoValue = self.doubleSpinBoxPadrao.value()
        variaValue = self.doubleSpinBoxVaria.value()
        lower_lim = padraoValue - variaValue
        upper_lim = padraoValue + variaValue

        for xi, yi_estaca, yi_terreno, desnivel in zip(
            estacas_distances, estacas_cortes, interp_apoio_elevations, desnivels):
            # Desenhe a linha de dimensão vertical com setas em ambas as extremidades
            ax.annotate("", xy=(xi, yi_terreno), xycoords="data", xytext=(xi, yi_estaca), textcoords="data", arrowprops=dict(arrowstyle="<->", lw=1.0, connectionstyle=f"bar,fraction={afastamento_barra}", color="orange"))

            # Define cor do texto conforme intervalo (azul dentro, vermelho fora)
            dentro = lower_lim <= desnivel <= upper_lim
            text_color = "blue" if dentro else "red"
            edge_color = "orange" if dentro else "darkred"

            # Adicione o valor do desnível
            ax.text(xi + deslocamento_x, (yi_terreno + yi_estaca) / 2, f"{desnivel:.2f} m", verticalalignment="center", horizontalalignment="left", fontsize=8.5, fontstyle="italic", rotation=90, fontweight="bold", color=text_color, bbox=dict(boxstyle="round,pad=0.1", edgecolor=edge_color, facecolor="white"))

        # Interpola de novo se necessário (mas se já estiver salvo em interp_apoio_elevations, pode reutilizar)
        interp_apoio_elevations = np.interp(estacas_distances, apoio_distances, apoio_elevations)
        Altura_Estaca = self.doubleSpinBoxComp.value()
        
        afastamento_barra_value_below = 0.18
        deslocamento_x_value_below = 0.45
        
        for xi, yi1, des in zip(estacas_distances, interp_apoio_elevations, desnivels):
            y_bottom = yi1 - (Altura_Estaca - des)
            # Preencher a área simulando concreto
            ax.fill_between([xi - 0.15, xi + 0.15], [y_bottom, y_bottom], [yi1, yi1], facecolor='Ivory', hatch='ooo', edgecolor='DarkSlateBlue', alpha=0.8)

            # Calcule value_below
            value_below = Altura_Estaca - des

            # Desenhe a linha de dimensão vertical
            ax.annotate("", xy=(xi, y_bottom), xycoords='data', xytext=(xi, yi1), textcoords='data', arrowprops=dict(arrowstyle="<->", lw=1, connectionstyle=f"bar,fraction={afastamento_barra_value_below}", color='green'))

            # Texto do value_below
            ax.text(xi - deslocamento_x_value_below, (y_bottom + yi1) / 2, f"{value_below:.2f} m",
                    verticalalignment='center', horizontalalignment='right',
                    fontsize=8.5, fontstyle='italic', fontweight='bold', color='magenta', rotation=90, 
                    bbox=dict(boxstyle='round,pad=0.1', edgecolor='darkGreen', facecolor='white'))

        # Anotação da altura da estaca
        ax.annotate(self.tr("Altura da Estaca: {altura_estaca:.1f} metros").format(altura_estaca=Altura_Estaca), xy=(0.005, 0.82), xycoords='axes fraction', fontsize=8, fontweight='bold', color='blue', fontstyle='italic', bbox=dict(boxstyle='round,pad=0.2', edgecolor='CadetBlue', facecolor='white'))

        # Crie o array Slopes (cálculo de inclinações em % entre cada par de pontos consecutivos)
        Slopes = []
        for i in range(1, len(estacas_distances)):
            dx = estacas_distances[i] - estacas_distances[i - 1]
            dy = interp_apoio_elevations[i] - interp_apoio_elevations[i - 1]
            slope_percent = 0.0 if dx == 0 else (100.0 * dy / dx)
            Slopes.append(slope_percent)

        # Ajuste estes valores conforme necessário
        deslocamento_x_slope = -1.75  # Deslocamento horizontal para a anotação
        deslocamento_y_slope = 0.20   # Deslocamento vertical para a anotação

        for i, (xi, yi, slope) in enumerate(zip(estacas_distances[1:], interp_apoio_elevations[1:], Slopes), start=1):
            # pular a primeira estaca se quiser (i == 1 corresponde à segunda estaca)
            slope_text = f"{slope:.2f}%"
            ax.text(xi + deslocamento_x_slope, yi + deslocamento_y_slope, slope_text,
                    verticalalignment='top', horizontalalignment='center',
                    fontsize=6.5, color='purple', rotation=0, fontweight='bold', fontstyle='italic',
                    bbox=dict(boxstyle='round,pad=0.2', edgecolor='darkGreen', facecolor='white'))

            # Linha horizontal de referência
            ax.hlines(yi, xi - 2, xi + 0.5, color='purple', linestyles='dashed', linewidth=1)

        # Calcule a inclinação da linha "Perfil"
        perfil_slope = (estacas_cortes[-1] - estacas_cortes[0]) / (estacas_distances[-1] - estacas_distances[0])

        # Estenda as distâncias para a linha "Perfil"
        estacas_distances_perfil_extended = np.array([estacas_distances[0] - 1] + list(estacas_distances) + [estacas_distances[-1] + 1])

        # Calcule as novas elevações baseadas na inclinação
        estacas_cortes_perfil_extended = np.array([estacas_cortes[0] - perfil_slope] + list(estacas_cortes) + [estacas_cortes[-1] + perfil_slope])

        # Calcule a inclinação da linha "Placas"
        placas_slope = perfil_slope  # assumindo a mesma inclinação do perfil

        # Distâncias para a linha "Placas"
        estacas_distances_placas_extended = np.array([estacas_distances[0] - 0.8] + list(estacas_distances) + [estacas_distances[-1] + 0.8])

        # Linha "Perfil" (contorno grosso em preto)
        ax.plot(estacas_distances_perfil_extended, estacas_cortes_perfil_extended, color='black', linewidth=5)
                
        # Linha "Perfil" (prata, um pouco mais fina por cima do contorno)
        ax.plot(estacas_distances_perfil_extended, estacas_cortes_perfil_extended, color='silver', linewidth=3.5)
                
        # Linha "Perfil" com marcadores apenas entre as extremidades
        ax.plot(estacas_distances_perfil_extended[1:-1], estacas_cortes_perfil_extended[1:-1], color='silver', marker='P', markersize=10, markeredgewidth=0.9, markeredgecolor='gray', markerfacecolor='silver', linewidth=3.5, label=self.tr("Perfil"))

        # Ajuste: aumentar a extensão nas extremidades da linha "Módulos"
        extra = 1.20  # metros de prolongamento em cada ponta (antes era 0.80)

        # X (distâncias) estendido
        estacas_distances_placas_extended = np.array([estacas_distances[0] - extra] + list(estacas_distances) + [estacas_distances[-1] + extra])

        # Y (cotas) estendido com offset de +0.13 e prolongamento linear pelo declive
        estacas_cortes_placas_extended = np.array([estacas_cortes[0] - placas_slope * extra + 0.13] + [c + 0.13 for c in estacas_cortes] + [estacas_cortes[-1] + placas_slope * extra + 0.13])

        # Plotar a linha "Módulos" (tracejada customizada)
        ax.plot(estacas_distances_placas_extended, estacas_cortes_placas_extended, color='blue', linewidth=4.5, linestyle=(0, (9, 0.2)), label=self.tr("Módulos"))

        # Plotar a linha "Terreno Natural" (outra cor)
        ax.plot(apoio_distances, apoio_elevations, color='DarkGoldenRod', linewidth=1.5, label=self.tr("Terreno Natural"))

        # Configuração adicional do gráfico
        xlabel_text = self.tr("Distância Acumulada (m)")
        xlabel = ax.text(0.5, -0.07, xlabel_text, ha='center', va='center', transform=ax.transAxes, fontsize=10)
        # Aplicando boxstyle ao rótulo do eixo x
        xlabel.set_bbox(dict(facecolor='blue', alpha=0.8, edgecolor='blue', boxstyle='darrow,pad=0.08'))

        # Texto para o rótulo do eixo y
        ylabel_text = self.tr("Elevação (m)")
        ylabel = ax.text(-0.05, 0.5, ylabel_text, ha='center', va='center', transform=ax.transAxes, fontsize=13, rotation=90, weight='bold', fontstyle='italic')
        # Aplicando boxstyle ao rótulo do eixo y
        ylabel.set_bbox(dict(facecolor='lightblue', alpha=0.5, edgecolor='black', boxstyle='Round4,pad=0.25'))
        
        title_text = self.tr("Perfil de Estrutura Solar")
        title = ax.text(0.5, 1.05, title_text, ha='center', va='center', transform=ax.transAxes, fontsize=12, weight='bold')
        title.set_bbox(dict(facecolor='cyan', alpha=0.5, edgecolor='blue', boxstyle='round4,pad=0.5'))

        # Mostra a legenda no canto superior esquerdo do gráfico
        ax.grid(axis='y', color='gray', alpha=0.5, linestyle='-', linewidth=0.4)

        # Definindo o novo título da janela
        plt.get_current_fig_manager().set_window_title(self.tr("Gráfico de Estrutura Solar"))

        # Cria os patches para a legenda (concreto, estaca, etc.)
        concrete_patch = mpatches.Patch(facecolor='Ivory', hatch='/ooo/', edgecolor='DarkSlateBlue', alpha=0.8, label=self.tr("Concretagem"))
        stake_patch = mpatches.Patch(facecolor='silver', edgecolor='grey', linewidth=1, hatch='--', label=self.tr("Estaca"))

        # Obtém os handles e labels atuais da legenda
        handles, labels = ax.get_legend_handles_labels()

        # Acrescenta os patches aos handles existentes
        handles.extend([concrete_patch, stake_patch])

        # Atualiza a legenda com os novos handles
        ax.legend(handles=handles)

        # Exemplo de uso:
        fig = plt.gcf()
        self.adicionar_rosa_dos_ventos(fig, x_coords, y_coords)

        # Chama a função para adicionar o logotipo ao gráfico
        self.adicionar_logo(fig)

        # Exemplo fictício de interseções do talude:
        talude_start_intersection = (estacas_distances[0] - 2, 0)  # ou None se não existir
        talude_end_intersection   = (estacas_distances[-1] + 2, 0) # ou None se não existir

        # Finalizou toda a plotagem? Então agora chamamos a função.
        self.configurar_ticks_eixo_x(ax=ax, estacas_distances=estacas_distances, talude_start_intersection=talude_start_intersection, talude_end_intersection=talude_end_intersection, step=5)

        # Exibe ou retorna a figura, dependendo do modo
        if modo_pdf:
            # no modo PDF, quem chamou é que salva a figura
            return fig
        else:
            plt.show()
            return None

    def atualizar_estado_pushButtonPDF(self):
        """
        Habilita o botão de exportar PDF somente se houver
        ao menos uma camada listada em listWidget_Lista.
        """
        tem_camadas = self.listWidget_Lista.count() > 0
        self.pushButtonPDF.setEnabled(tem_camadas)

    def exportar_pdf_estruturas(self):
        """
        Exporta um PDF com uma página para cada camada de pontos do grupo 'Estruturas',
        usando o gráfico já existente (plot_layers) e exibindo uma barra de progresso.
        """

        # 1) Localiza o grupo 'Estruturas'
        root = QgsProject.instance().layerTreeRoot()
        grupo_estruturas = None
        for child in root.children():
            if isinstance(child, QgsLayerTreeGroup) and child.name() == "Estruturas":
                grupo_estruturas = child
                break

        if not grupo_estruturas:
            self.mostrar_mensagem(self.tr("O grupo 'Estruturas' não foi encontrado no projeto."), "Erro")
            return

        # 2) Coleta camadas de pontos dentro do grupo
        layers = []
        for child in grupo_estruturas.children():
            if isinstance(child, QgsLayerTreeLayer):
                lyr = child.layer()
                if (lyr and lyr.type() == QgsMapLayer.LayerType.VectorLayer
                        and lyr.geometryType() == QgsWkbTypes.GeometryType.PointGeometry):
                    layers.append(lyr)

        if not layers:
            self.mostrar_mensagem(self.tr("Nenhuma camada de pontos foi encontrada no grupo 'Estruturas'."), "Erro")
            return

        # 3) Pede o caminho do PDF
        caminho_pdf = self.escolher_local_para_salvar(self.tr("Estruturas", "PDF (*.pdf)"))
        if not caminho_pdf:
            return  # usuário cancelou

        # 4) Cria barra de progresso
        total_paginas = len(layers)
        progressBar, progressMessageBar = self.iniciar_progress_bar(total_paginas, titulo=self.tr("Exportando PDF das Estruturas..."))
        passo_atual = 0

        # Guarda a camada corrente para restaurar depois
        camada_original = self.current_estruturas_layer

        try:
            with PdfPages(caminho_pdf) as pdf:
                for lyr in layers:
                    # atualiza camada atual
                    self.current_estruturas_layer = lyr

                    # gera figura com o gráfico
                    fig = self.plot_layers(modo_pdf=True)
                    if fig is None:
                        continue

                    pdf.savefig(fig)
                    plt.close(fig)

                    # atualiza barra de progresso
                    passo_atual += 1
                    if self._w_alive(progressBar):
                        progressBar.setValue(passo_atual)
                        QApplication.processEvents()

            # restaura camada selecionada
            self.current_estruturas_layer = camada_original

            # encerra barra
            try:
                if self._w_alive(progressMessageBar):
                    self.iface.messageBar().popWidget(progressMessageBar)
            except Exception:
                pass  # nosec B110
            self._lock_messagebar = False

            pasta = os.path.dirname(caminho_pdf)
            self.mostrar_mensagem(self.tr("PDF das estruturas exportado com sucesso!"), "Sucesso", caminho_pasta=pasta, caminho_arquivo=caminho_pdf)

        except Exception as e:
            # em caso de erro, fecha barra e restaura estado
            try:
                if self._w_alive(progressMessageBar):
                    self.iface.messageBar().popWidget(progressMessageBar)
            except Exception:
                pass  # nosec B110
            self._lock_messagebar = False
            self.current_estruturas_layer = camada_original
            self.mostrar_mensagem(self.tr("Erro ao exportar PDF: {error}").format(error=str(e)), "Erro", forcar=True)

    def has_support_for_current_layer(self):
        """
        Retorna True se existir uma camada de suporte em self.support_layers
        para a camada atualmente selecionada (self.current_estruturas_layer).
        """
        if not self.current_estruturas_layer:
            return False
        if not hasattr(self, "support_layers"):
            return False

        expected_support_name = self.current_estruturas_layer.name() + self.tr("_Suporte")
        for lyr in self.support_layers:
            try:
                if lyr and lyr.name() == expected_support_name:
                    return True
            except RuntimeError:
                # Camada já destruída
                continue
        return False

    def _zoom_to_layer(self, layer, margin_pct=0.08):
        """
        Aplica zoom no mapa para a extensão da `layer`.
        - Atualiza extents antes de ler.
        - Reprojeta para o CRS do mapa se necessário.
        - Garante uma margem mínima mesmo quando a extensão tem largura/altura 0.
        """
        try:
            if not layer:
                return

            # garante extents atualizados
            try:
                layer.updateExtents()
            except Exception:
                pass  # nosec B110

            rect = layer.extent()
            if not rect or rect.isEmpty():
                return

            canvas = self.iface.mapCanvas()
            dest_crs = canvas.mapSettings().destinationCrs()

            # CRS da camada
            lyr_crs = layer.crs() if hasattr(layer, "crs") else None

            # transforma bbox se CRS diferentes
            if lyr_crs and dest_crs and lyr_crs.isValid() and dest_crs.isValid() and (lyr_crs != dest_crs):
                xform = QgsCoordinateTransform(lyr_crs, dest_crs, QgsProject.instance())
                rect = xform.transformBoundingBox(rect)

            # margem (inclui caso width/height == 0)
            mupp = canvas.mapSettings().mapUnitsPerPixel() or 1.0  # unidades por pixel
            min_pad = mupp * 80  # ~80px de margem mínima

            if margin_pct is None:
                margin_pct = 0.0

            dx = rect.width() * margin_pct if rect.width() > 0 else min_pad
            dy = rect.height() * margin_pct if rect.height() > 0 else min_pad

            rect = QgsRectangle(
                rect.xMinimum() - dx, rect.yMinimum() - dy,
                rect.xMaximum() + dx, rect.yMaximum() + dy)

            # zoom (zoomToFeatureExtent costuma ser mais “decidido” que setExtent puro)
            try:
                canvas.zoomToFeatureExtent(rect)
            except Exception:
                canvas.setExtent(rect)

            canvas.refresh()

        except Exception as e:
            self.mostrar_mensagem(self.tr("Não foi possível aplicar o zoom: {error}").format(error=str(e)), "Erro")

    def on_listwidget_selection_changed(self):
        """
        Atualiza a camada corrente e a UI quando o usuário seleciona um item no listWidget_Lista,
        ignorando cliques no ícone de deletar para não disparar zoom/sincronizações durante a remoção.
        """
        # Se o clique atual foi no ícone de deletar, não faz nada aqui
        try:
            pos = self.listWidget_Lista.viewport().mapFromGlobal(QCursor.pos())
            item = self.listWidget_Lista.itemAt(pos)
            if item:
                rect = self.listWidget_Lista.visualItemRect(item)
                icon_size = 11
                icon_margin = 6
                icon_rect = QRect(
                    rect.left() + icon_margin,
                    rect.top() + (rect.height() - icon_size) // 2,
                    icon_size,
                    icon_size)
                if icon_rect.contains(pos):
                    return
        except Exception:
            pass  # nosec B110

        items = self.listWidget_Lista.selectedItems()

        # Nada selecionado → limpa estado/UX
        if not items:
            self.current_estruturas_layer = None
            try:
                self.graphWidget.clear()
            except Exception:
                pass  # nosec B110
            self.update_tableView_2()
            self.update_listWidget_inc()
            self.pushButtonMat.setEnabled(False)
            self.atualizar_estado_pushButtonPDF()
            return

        # Resolve o layer via ID guardado no item (Qt.UserRole)
        layer_id = items[0].data(Qt.ItemDataRole.UserRole)
        layer = QgsProject.instance().mapLayer(layer_id)

        # Checagens de segurança
        if (layer is None
            or not isinstance(layer, QgsVectorLayer)
            or layer.geometryType() != QgsWkbTypes.GeometryType.PointGeometry
            or not self._w_alive(layer)
            or not layer.isValid()):
            self.current_estruturas_layer = None
            try:
                self.graphWidget.clear()
            except Exception:
                pass  # nosec B110
            self.update_tableView_2()
            self.update_listWidget_inc()
            self.pushButtonMat.setEnabled(False)
            self.atualizar_estado_pushButtonPDF()
            return

        # Atualiza camada corrente
        self.current_estruturas_layer = layer

        # 🔎 Zoom na camada selecionada (com salvaguardas)
        try:
            if hasattr(self, "_zoom_to_layer") and callable(self._zoom_to_layer):
                self._zoom_to_layer(layer)

        except Exception as e:
            # Evita quebrar o fluxo se o zoom falhar
            self.mostrar_mensagem(self.tr("Zoom para a camada falhou: {error}").format(error=str(e)), "Tempo Salvo Tools", "Erro")

        # Sincroniza controles e atualiza UI
        self.sync_spinboxes_from_layer(layer)
        self.update_tableView_2()
        self.update_listWidget_inc()

        # Atualiza gráfico conforme suporte
        if self.has_support_for_current_layer():
            self.update_support_graph()
        else:
            self.update_graph()

        # Habilita botões dependentes e estado do PDF
        self.pushButtonMat.setEnabled(True)
        self.atualizar_estado_pushButtonPDF()

    def pushButtonExportarDXF_clicked(self):
        """
        Slot do botão 'Exportar DXF'.

        - Obtém todas as camadas do grupo 'Estruturas' e o caminho onde o
          arquivo DXF será salvo (via obter_camadas_e_caminho_dxf).
        - Se o usuário não cancelar, chama exportar_camadas_para_dxf para
          gerar o DXF com as camadas selecionadas.
        """
        # Chama o helper que devolve (lista_de_camadas, caminho_do_arquivo) ou None se cancelar
        result = self.obter_camadas_e_caminho_dxf()
        if result:
            # Desempacota a tupla retornada
            layers, caminho_arquivo = result
            # Executa a exportação das camadas para DXF
            self.exportar_camadas_para_dxf(layers, caminho_arquivo)

    def atualizar_estado_pushButtonExportarDXF(self):
        """
        Verifica se há alguma camada vetorial de pontos no grupo 'Estruturas'.
        Se existir ao menos uma, habilita o pushButtonExportarDXF; caso contrário, desabilita.
        """
        # Acessa o layer tree root
        root = QgsProject.instance().layerTreeRoot()

        grupo_estruturas = None
        # Localiza o grupo 'Estruturas'
        for child in root.children():
            if isinstance(child, QgsLayerTreeGroup) and child.name() == "Estruturas":
                grupo_estruturas = child
                break

        # Se não encontrou o grupo, desabilita o botão e retorna
        if not grupo_estruturas:
            self.pushButtonExportarDXF.setEnabled(False)
            return

        # Verifica se dentro do grupo existe alguma camada de pontos
        tem_camada_ponto = False
        for child in grupo_estruturas.children():
            if isinstance(child, QgsLayerTreeLayer):
                layer = child.layer()
                if (layer 
                    and layer.type() == QgsMapLayer.LayerType.VectorLayer 
                    and layer.geometryType() == QgsWkbTypes.GeometryType.PointGeometry):
                    tem_camada_ponto = True
                    break

        # Habilita o botão se houver pelo menos 1 camada de pontos
        self.pushButtonExportarDXF.setEnabled(tem_camada_ponto)

    def obter_camadas_e_caminho_dxf(self):
        """
        Verifica se existe o grupo 'Estruturas' no projeto e obtém todas as camadas vetoriais (pontos) dentro dele.
        Em seguida, solicita ao usuário um caminho para salvar o arquivo DXF.
        Retorna uma tupla (layers, caminho_arquivo) ou None se ocorrer algum erro ou cancelamento.
        """
        # 1) Verificar se existe o grupo "Estruturas"
        root = QgsProject.instance().layerTreeRoot()
        grupo_estruturas = None
        for child in root.children():
            if isinstance(child, QgsLayerTreeGroup) and child.name() == self.tr("Estruturas"):
                grupo_estruturas = child
                break
        if not grupo_estruturas:
            self.mostrar_mensagem(self.tr("O grupo 'Estruturas' não foi encontrado no projeto."), "Erro")
            return None

        # 2) Obter todas as camadas (vetoriais) dentro do grupo "Estruturas"
        layers = []
        for child in grupo_estruturas.children():
            if isinstance(child, QgsLayerTreeLayer):
                layer = child.layer()
                # Consideramos apenas camadas de pontos
                if layer and layer.type() == QgsMapLayer.LayerType.VectorLayer and layer.geometryType() == QgsWkbTypes.GeometryType.PointGeometry:
                    layers.append(layer)
        if not layers:
            self.mostrar_mensagem(self.tr("Nenhuma camada de pontos foi encontrada no grupo 'Estruturas'."), "Erro")
            return None

        # 3) Escolher local para salvar o DXF
        nome_padrao = self.tr("Estruturas")
        caminho_arquivo = self.escolher_local_para_salvar(nome_padrao, "DXF (*.dxf)")
        if not caminho_arquivo:
            return None  # Usuário cancelou

        return (layers, caminho_arquivo)

    def get_dxf_color(self, altura):
        """
        Determina a cor DXF com base no valor de AlturaEstaca, comparando-o com o intervalo definido
        por doubleSpinBoxPadrao e doubleSpinBoxVaria.
        Retorna:
          - 5 para azul (se AlturaEstaca estiver dentro do intervalo),
          - 1 para vermelho (caso contrário).
        """
        try:
            numeric_altura = float(altura)
        except Exception as e:
            self.mostrar_mensagem(self.tr("Erro ao converter AlturaEstaca '{altura}' para float: {error}").format(altura=altura, error=str(e)), "Erro")
            numeric_altura = 0.0
        padraoValue = self.doubleSpinBoxPadrao.value()
        variaValue = self.doubleSpinBoxVaria.value()
        lower_lim = padraoValue - variaValue
        upper_lim = padraoValue + variaValue
        self.mostrar_mensagem(self.tr("Comparando AlturaEstaca: {numeric_altura} com intervalo [{lower_lim}, {upper_lim}]").format(numeric_altura=numeric_altura, lower_lim=lower_lim, upper_lim=upper_lim), "Aviso")

        if lower_lim <= numeric_altura <= upper_lim:
            return 5  # Azul
        else:
            return 1  # Vermelho

    def get_pen_for_feature(self, feature, espessura=2):
        """
        Retorna um QPen com a cor definida com base em "AlturaEstaca".
        Usa o mesmo critério: se AlturaEstaca estiver fora do intervalo definido,
        retorna vermelho; se estiver dentro, azul; caso contrário, preto.
        """
        # Obtém o valor e converte para float, se possível:
        try:
            valor = float(feature["AlturaEstaca"])
        except Exception:
            valor = 0.0

        padrao = self.doubleSpinBoxPadrao.value()
        varia = self.doubleSpinBoxVaria.value()
        lower_lim = padrao - varia
        upper_lim = padrao + varia

        # Se estiver dentro do intervalo, azul; senão, vermelho.
        if lower_lim <= valor <= upper_lim:
            cor = QColor("blue")
        else:
            cor = QColor("red")
        return QPen(cor, espessura)

    def criar_block_quadrado_traco(self, doc, block_name, cor):
        """
        Cria (ou obtém) um bloco com o nome 'block_name' no documento DXF 'doc', 
        onde todas as entidades (o quadrado e o traço) terão a cor definida por 'cor' (um inteiro DXF).
        
        O bloco contém:
          - Um quadrado centrado na origem (de -0.5 a 0.5 em X e Y)
          - Um traço vertical no centro, que se estende para cima (de (0,0) a (0,0.6))
        """
        try:
            block = doc.blocks.new(name=block_name)
        except ezdxf.DXFValueError:
            # Se o bloco já existe, apenas o obtém
            block = doc.blocks.get(block_name)

        # Limpar entidades do bloco se necessário:
        # block.reset()

        # Cria o quadrado com cor definida (não usamos BYBLOCK, definimos explicitamente)
        corners = [
            (-0.5, -0.5),
            (-0.5,  0.5),
            ( 0.5,  0.5),
            ( 0.5, -0.5),
            (-0.5, -0.5)]
        block.add_lwpolyline(
            corners,
            dxfattribs={"color": cor})  # Cor definida

        # Traço vertical no centro: agora estende para cima, de (0,0) a (0,0.6)
        block.add_line(
            (0, 0),
            (0, 0.6),
            dxfattribs={"color": cor})

        return block_name

    def get_dxf_color_for_altura(self, altura):
        """
        Determina a cor DXF com base no valor de AlturaEstaca e nos valores dos spinBoxes.
        Retorna 5 (azul) se AlturaEstaca estiver dentro do intervalo definido,
        ou 1 (vermelho) se estiver fora.
        """
        try:
            a = float(altura)
        except Exception:
            a = 0.0

        padraoValue = self.doubleSpinBoxPadrao.value()
        variaValue  = self.doubleSpinBoxVaria.value()
        lower_lim = padraoValue - variaValue
        upper_lim = padraoValue + variaValue

        if lower_lim <= a <= upper_lim:
            return 5  # Azul
        else:
            return 1  # Vermelho

    def exportar_camadas_para_dxf(self, layers, caminho_arquivo):
        """
        Exporta as camadas de pontos do grupo 'Estruturas' para um arquivo DXF.
        - Entidades AZUIS vão para a layer "Aprovadas"
        - Entidades VERMELHAS vão para a layer "Reprovadas"
        - Desenha um retângulo envolvendo as feições de cada camada
          (azul se todas aprovadas, vermelho se alguma reprovada)
        - Acima do retângulo, escreve em magenta:
            NomeDaCamada --> Inclinação da Estrutura: XX,YY%
        """
        # 1) Cria o documento DXF e define o estilo "Arial"
        doc = ezdxf.new()

        if "Arial" not in doc.styles:
            doc.styles.new("Arial", dxfattribs={"font": "arial.ttf"})

        msp = doc.modelspace()

        # 2) Cria os dois blocos (azul e vermelho)
        block_azul = self.criar_block_quadrado_traco(doc, "QuadradoTraço_azul", 5)
        block_vermelho = self.criar_block_quadrado_traco(doc, "QuadradoTraço_vermelho", 1)

        # 3) Garante que as duas LAYERS DXF existam
        layer_aprovadas = self.tr("Aprovadas")
        layer_reprovadas = self.tr("Reprovadas")

        if layer_aprovadas not in doc.layers:
            doc.layers.add(layer_aprovadas, dxfattribs={"color": 5})

        if layer_reprovadas not in doc.layers:
            doc.layers.add(layer_reprovadas, dxfattribs={"color": 1})

        # 4) Itera sobre as camadas de pontos do QGIS
        for layer in layers:
            # 4.1) Calcula a inclinação da estrutura (se possível)
            slope_pct_str = self.tr("N/D")
            field_names = {f.name() for f in layer.fields()}
            if {"CotaEstaca", "Z", "AlturaEstaca"}.issubset(field_names):
                try:
                    dados = self.get_estacas_data(layer)  # [(dist_acum, CotaEstaca, Z, AlturaEstaca, x, y), ...]
                    if len(dados) >= 2:
                        dist0, cota0, _, _, _, _ = dados[0]
                        dist1, cota1, _, _, _, _ = dados[-1]
                        dx_total = dist1 - dist0
                        if abs(dx_total) > 0:
                            slope = (cota1 - cota0) / dx_total * 100.0
                        else:
                            slope = 0.0
                        slope_pct_str = f"{slope:.2f}%"
                except Exception as e:
                    self.mostrar_mensagem(self.tr("Não foi possível calcular a inclinação para {layer_name}: {error}").format(layer_name=layer.name(), error=str(e)), "Aviso")

            # 4.2) Variáveis para o retângulo em torno das feições
            min_x = float("inf")
            max_x = float("-inf")
            min_y = float("inf")
            max_y = float("-inf")
            all_approved = True         # vira False se achar alguma reprovada
            layer_has_features = False  # vira True se a camada tiver pelo menos uma feição válida

            for feature in layer.getFeatures():
                geom = feature.geometry()
                if not geom or geom.isEmpty():
                    continue

                pt = geom.asPoint()
                x, y = pt.x(), pt.y()
                layer_has_features = True

                # Atualiza extents
                if x < min_x:
                    min_x = x
                if x > max_x:
                    max_x = x
                if y < min_y:
                    min_y = y
                if y > max_y:
                    max_y = y

                # Determina a cor com base em AlturaEstaca
                if "AlturaEstaca" in feature.fields().names():
                    dxf_color = self.get_dxf_color_for_altura(feature["AlturaEstaca"])
                else:
                    dxf_color = 7  # fallback (branco/preto)

                layer_aprovadas = self.tr("Aprovadas")
                layer_reprovadas = self.tr("Reprovadas")

                if dxf_color == 5:
                    dxf_layer_name = layer_aprovadas
                    block_name = block_azul

                elif dxf_color == 1:
                    dxf_layer_name = layer_reprovadas
                    block_name = block_vermelho
                    all_approved = False

                else:
                    dxf_layer_name = layer_reprovadas
                    block_name = block_vermelho
                    all_approved = False

                # fator de escala do bloco
                scale_factor = 0.35

                # 4a) Insere o bloco na layer correspondente
                insert_entity = msp.add_blockref(block_name, (x, y), dxfattribs={"layer": dxf_layer_name})
                insert_entity.dxf.xscale = scale_factor
                insert_entity.dxf.yscale = scale_factor
                insert_entity.dxf.zscale = 1.0

                # 4b) (Opcional) MTEXT com sequencia + AlturaEstaca
                if "sequencia" in feature.fields().names() and "AlturaEstaca" in feature.fields().names():
                    label_text = f"{feature['sequencia']}\n{feature['AlturaEstaca']}"
                    mtext_entity = msp.add_mtext(
                        label_text,
                        dxfattribs={"layer": dxf_layer_name, "style": "Arial", "color": dxf_color})
                    mtext_entity.dxf.char_height = 0.25

                    # deslocamento do texto
                    text_offset_x = 0.25
                    text_offset_y = 0.7
                    mtext_entity.dxf.insert = (x + text_offset_x, y + text_offset_y)
                    mtext_entity.dxf.attachment_point = 1  # Top Left

            # 4.3) Desenha o retângulo + título magenta, se houver feições
            if layer_has_features and min_x < max_x and min_y < max_y:
                # Margens ao redor do conjunto de pontos
                margem_x = 0.5
                margem_y = 1.0   # 🔹 altura um pouco maior

                x1 = min_x - margem_x
                x2 = max_x + margem_x
                y1 = min_y - margem_y
                y2 = max_y + margem_y

                # Cor e layer do retângulo: azul se tudo aprovado; vermelho se houver reprovada
                rect_color = 5 if all_approved else 1
                rect_layer_name = self.tr("Aprovadas") if all_approved else self.tr("Reprovadas")

                # Retângulo
                msp.add_lwpolyline(
                    [(x1, y1),
                     (x1, y2),
                     (x2, y2),
                     (x2, y1),
                     (x1, y1)],
                    dxfattribs={"layer": rect_layer_name, "color": rect_color})

                # 🔹 Texto magenta logo acima do retângulo
                titulo = self.tr("{layer_name} --> Inclinação da Estrutura: {slope_pct}").format(layer_name=layer.name(), slope_pct=slope_pct_str)
                texto_y = y2 + 0.7
                texto_x = (x1 + x2) / 2.0

                titulo_entity = msp.add_mtext(
                    titulo,
                    dxfattribs={
                        "layer": rect_layer_name,
                        "style": "Arial",
                        "color": 6})   # 6 = magenta

                titulo_entity.dxf.char_height = 0.54
                titulo_entity.dxf.insert = (texto_x, texto_y)
                # 2 = Top Center → texto fica centrado horizontalmente acima
                titulo_entity.dxf.attachment_point = 2

        # 5) Salvar o arquivo DXF
        try:
            doc.saveas(caminho_arquivo)
            caminho_pasta = os.path.dirname(caminho_arquivo)
            self.mostrar_mensagem(self.tr("Exportação DXF concluída com camadas '{layer_aprovadas}' e '{layer_reprovadas}'!").format(layer_aprovadas=self.tr("Aprovadas"), layer_reprovadas=self.tr("Reprovadas")), "Sucesso", caminho_pasta=caminho_pasta, caminho_arquivo=caminho_arquivo)
        except Exception as e:
            self.mostrar_mensagem(self.tr("Erro ao salvar o DXF: {error}").format(error=str(e)), "Erro")

class ListDeleteButtonDelegate(QStyledItemDelegate):
    def __init__(self, parent=None):
        super(ListDeleteButtonDelegate, self).__init__(parent)
        self.parent = parent

    def paint(self, painter, option, index):
        if not index.isValid():
            return

        rect = option.rect
        icon_size = 10  # Tamanho do ícone
        icon_margin = 6  # Margem para o ícone

        # Ícone à esquerda
        icon_rect = QRect(
            rect.left() + icon_margin,
            rect.top() + (rect.height() - icon_size) // 2,
            icon_size,
            icon_size)
        # Texto deslocado para a direita do ícone
        text_rect = QRect(
            icon_rect.right() + icon_margin,
            rect.top(),
            rect.width() - icon_size - 2 * icon_margin,
            rect.height())

        # Define o fundo do item:
        if option.state & QStyle.StateFlag.State_Selected:
            # Fundo de seleção: azul clarinho
            painter.fillRect(option.rect, QColor("#00aaff"))
        elif option.state & QStyle.StateFlag.State_MouseOver:
            # Quando o mouse passa sobre o item, fundo verde clarinho
            painter.fillRect(option.rect, QColor("#90EE90"))
        else:
            # Fundo padrão (base do palette)
            painter.fillRect(option.rect, option.palette.base())

        # Desenha o ícone de deletar (quadrado vermelho com contorno azul e "X" branco)
        painter.save()
        painter.setRenderHint(QPainter.RenderHint.Antialiasing)
        painter.setPen(QPen(QColor(0, 85, 255), 2))  # Contorno azul (1px)
        painter.setBrush(QBrush(QColor(255, 0, 0, 180)))  # Fundo vermelho
        painter.drawRoundedRect(icon_rect, 3, 3)

        # Desenha o "X" branco dentro do quadrado
        painter.setPen(QPen(QColor(255, 255, 255), 2))
        painter.drawLine(icon_rect.topLeft() + QPoint(3, 3), icon_rect.bottomRight() - QPoint(3, 3))
        painter.drawLine(icon_rect.topRight() + QPoint(-3, 3), icon_rect.bottomLeft() + QPoint(3, -3))
        painter.restore()

        # Desenha o texto da camada
        painter.save()
        painter.setPen(option.palette.text().color())
        font = painter.font()
        font.setPointSize(9)
        painter.setFont(font)
        text = index.data(Qt.ItemDataRole.DisplayRole)
        painter.drawText(text_rect, Qt.AlignmentFlag.AlignVCenter | Qt.TextFlag.TextSingleLine, text)
        painter.restore()

    def editorEvent(self, event, model, option, index):
        # Apaga no PRESS (antes da seleção disparar e antes do zoom mexer no foco)
        if event.type() == QEvent.Type.MouseButtonPress and event.button() == Qt.MouseButton.LeftButton:
            rect = option.rect
            icon_size = 11
            icon_margin = 6
            icon_rect = QRect(
                rect.left() + icon_margin,
                rect.top() + (rect.height() - icon_size) // 2,
                icon_size,
                icon_size)

            if icon_rect.contains(event.pos()):
                layer_id = index.data(Qt.ItemDataRole.UserRole)
                if layer_id:
                    QgsProject.instance().removeMapLayer(layer_id)
                # True = evento tratado → evita seleção/zoom e evita “perder” o clique
                return True

        return super(ListDeleteButtonDelegate, self).editorEvent(event, model, option, index)