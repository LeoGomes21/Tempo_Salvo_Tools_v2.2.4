from qgis.core import QgsProject, Qgis, QgsVectorLayer, QgsWkbTypes, QgsGeometry, QgsPointXY, QgsFeature, QgsLineSymbol, QgsField, QgsMarkerLineSymbolLayer,  QgsPalLayerSettings, QgsMarkerSymbol, QgsTextFormat, QgsVectorLayerSimpleLabeling, QgsSymbolLayer, QgsUnitTypes, QgsEditorWidgetSetup, QgsLayerTreeLayer,  QgsSingleSymbolRenderer, QgsProperty, QgsTemplatedLineSymbolLayerBase, QgsTextBufferSettings, QgsRuleBasedLabeling, QgsFeatureRequest
from qgis.PyQt.QtWidgets import QDialog, QCheckBox, QColorDialog,QStyledItemDelegate, QStyle, QFileDialog, QPushButton, QInputDialog, QAbstractItemView
from qgis.PyQt.QtGui import QPainter, QColor, QPen, QBrush, QStandardItemModel, QStandardItem, QDesktopServices
from qgis.PyQt.QtCore import Qt, QRect, QPoint, QEvent, QSettings, QItemSelectionModel, QDir, QStandardPaths, QUrl, QMetaType, QCoreApplication
from ezdxf.enums import TextEntityAlignment
from qgis.gui import QgsMapToolEmitPoint
from ezdxf import colors as _ezcolors
from functools import partial
from qgis.PyQt import uic
import ezdxf
import math
import os

FORM_CLASS, _ = uic.loadUiType(os.path.join(os.path.dirname(__file__), 'NotasManager.ui'))

class NotaMecanicas(QDialog, FORM_CLASS):
    def __init__(self, iface, parent=None):
        parent = parent or iface.mainWindow()
        super().__init__(parent)
        self.iface = iface
        self.setupUi(self)
        self.setWindowTitle(self.tr("Notas Mecânicas"))

        # Nome do grupo usado no Layer Tree para as camadas deste módulo
        self._group_name = self.tr("Notas")

        # Estado do tree
        self._tv_model = None
        self._tv_last_layer_ids = []
        self._tv_selected_layer_id = None
        self._last_layer_connected = None

        self._last_layer_fields_connected = None   # camada cujos sinais de fields estão conectados

        # Mensageria
        self._widget_msg_sucesso = None

        self._signals_connected = False

        self._combo_name_conns = {}

        self._field_conns = {}  # {(layer_id, "layer|prov", sig_name): (sig, slot)}

        # Cache de widgets
        self.cbSeleciona = self.findChild(QCheckBox, 'checkBoxSeleciona')

        self._init_treeview_camadas()
        self.populate_combo_box()

        # Hover azul claro
        self.treeViewCamada.setStyleSheet("QTreeView::item:hover { background: #cceeff; }")

        self.connect_signals()

        # popula o combo de indicador (uma vez)
        self._init_combo_indicador()

        # Não modal
        self.setModal(False)
        self.setWindowModality(Qt.WindowModality.NonModal)

        self._mt_livre = None         # map tool temporário
        self._mt_prev = None          # map tool anterior (para restaurar)
        self._pending_free_text = ""  # texto digitado para a próxima nota livre
        self._pending_free_layer_id = None  # camada alvo da próxima nota livre

        self._tree_layer_conns = {}   # Evita connects duplicados no tree

        # Estado inicial: seguros (desabilitados) até a primeira sincronização
        try:
            if self.pushButtonConectada: self.pushButtonConectada.setEnabled(False)
            if self.pushButtonDXF:       self.pushButtonDXF.setEnabled(False)
        except Exception:
            pass  # nosec B110

        # já existe: self._last_layer_connected = None
        self._last_layer_connected_id = None

        # já existe: self._last_layer_fields_connected = None
        self._last_layer_fields_connected_id = None

        # Janela de ferramenta do QGIS (fica acima das janelas do app),
        # mas NÃO fica acima de outras apps do Windows
        flags = self.windowFlags()
        flags |= Qt.WindowType.WindowCloseButtonHint
        flags &= ~Qt.WindowType.WindowStaysOnTopHint    # remove "sempre no topo" global
        self.setWindowFlags(flags)

        self.show()  # re-aplica os flags

    def tr(self, message):
        """
        Traduz textos deste diálogo.
        O contexto precisa ser estável para o Qt Linguist encontrar as traduções.
        """
        return QCoreApplication.translate("NotaMecanicas", message)

    def update_field_connections(self):
        """
        Conecta sinais relevantes da camada atual para detectar mudanças em fields
        e manter o comboBoxCampo sincronizado.

        ✅ Fix: nunca chama old.id() se old já foi deletado.
           Usa _last_layer_fields_connected_id (string) como fonte segura.
        """
        if not hasattr(self, "_field_conns") or self._field_conns is None:
            self._field_conns = {}

        def _disconnect_layer_records(layer_id: str):
            """Desconecta tudo registrado para um layer_id (layer e provider)."""
            for key in list(self._field_conns.keys()):
                lid, where, sig_name = key
                if lid != layer_id:
                    continue
                sig, slot = self._field_conns.pop(key, (None, None))
                try:
                    if sig and slot:
                        self._safe_disconnect(sig, slot)
                except Exception:
                    pass  # nosec B110

        def _connect_once(layer_id: str, where: str, sig, sig_name: str, slot) -> None:
            """Conecta só uma vez por (layer_id, where, sig_name)."""
            key = (layer_id, where, sig_name)
            if key in self._field_conns:
                return
            try:
                ok = self._safe_connect(sig, slot)
                if ok:
                    self._field_conns[key] = (sig, slot)
            except Exception:
                pass  # nosec B110

        # camada atual do combo
        layer_id = self.comboBoxCamada.currentData()
        lyr = QgsProject.instance().mapLayer(layer_id) if layer_id else None

        # ID antigo (seguro) da camada com fields conectados
        old_id = getattr(self, "_last_layer_fields_connected_id", None)

        # se a camada mudou OU virou inválida, desconecta pelo ID antigo (sem tocar no objeto antigo)
        if old_id and (not isinstance(lyr, QgsVectorLayer) or lyr.id() != old_id):
            _disconnect_layer_records(old_id)

        if isinstance(lyr, QgsVectorLayer):
            slot = self._refresh_comboBoxCampo

            # sinais no layer
            for sig_name in ("fieldsChanged", "updatedFields", "attributeAdded", "attributeDeleted", "attributeRenamed", "editingStopped"):
                try:
                    sig = getattr(lyr, sig_name, None)
                    if sig:
                        _connect_once(lyr.id(), "layer", sig, sig_name, slot)
                except Exception:
                    pass  # nosec B110

            # sinais no provider (quando existir)
            try:
                prov = lyr.dataProvider()
                sig = getattr(prov, "fieldsChanged", None) if prov else None
                if sig:
                    _connect_once(lyr.id(), "prov", sig, "fieldsChanged", slot)
            except Exception:
                pass  # nosec B110

            # atualiza caches
            self._last_layer_fields_connected = lyr
            self._last_layer_fields_connected_id = lyr.id()
        else:
            # sem layer válida: limpa caches
            self._last_layer_fields_connected = None
            self._last_layer_fields_connected_id = None

        # Atualiza imediatamente
        self._refresh_comboBoxCampo()

    def update_layer_connections(self):
        """Conecta selectionChanged da camada do combo e mantém fields sincronizados."""
        # desconecta anterior
        try:
            if self._last_layer_connected is not None:
                self._last_layer_connected.selectionChanged.disconnect(self.update_checkBoxSeleciona)
        except Exception:
            pass  # nosec B110

        self._last_layer_connected = None
        self._last_layer_connected_id = None

        layer_id = self.comboBoxCamada.currentData()
        if layer_id:
            layer = QgsProject.instance().mapLayer(layer_id)
            if layer:
                try:
                    layer.selectionChanged.connect(self.update_checkBoxSeleciona)
                except Exception:
                    pass  # nosec B110
                self._last_layer_connected = layer
                try:
                    self._last_layer_connected_id = layer.id()
                except Exception:
                    self._last_layer_connected_id = None

        # sempre atualiza UI dependente
        self.update_checkBoxSeleciona()
        self.update_field_connections()   # mantém comboBoxCampo atualizado

    def _on_project_layer_will_be_removed_cleanup(self, layer_id: str):
        """
        Cleanup ANTES da camada ser deletada pelo QGIS.
        """
        # combo
        try:
            self._disconnect_combo_layer_name_changed(layer_id)
        except Exception:
            pass  # nosec B110

        # tree
        for key in list(getattr(self, "_tree_layer_conns", {}).keys()):
            if key[0] == layer_id:
                sig, slot = self._tree_layer_conns.pop(key)
                try:
                    sig.disconnect(slot)
                except Exception:
                    pass  # nosec B110

        # Fields: remove registros por layer_id (sem tocar no QgsVectorLayer deletado)
        try:
            if hasattr(self, "_field_conns") and self._field_conns:
                for key in list(self._field_conns.keys()):
                    if key[0] == layer_id:
                        sig, slot = self._field_conns.pop(key, (None, None))
                        try:
                            if sig and slot:
                                self._safe_disconnect(sig, slot)
                        except Exception:
                            pass  # nosec B110
        except Exception:
            pass  # nosec B110

        # Limpa caches se eram dessa layer
        if getattr(self, "_last_layer_fields_connected_id", None) == layer_id:
            self._last_layer_fields_connected = None
            self._last_layer_fields_connected_id = None

        if getattr(self, "_last_layer_connected_id", None) == layer_id:
            self._last_layer_connected = None
            self._last_layer_connected_id = None

        # se era a selecionada, limpa seleção interna
        if getattr(self, "_tv_selected_layer_id", None) == layer_id:
            self._tv_selected_layer_id = None

    def showEvent(self, event):
        """
        Sobrescreve o evento de exibição do diálogo para resetar os Widgets.
        """
        super(NotaMecanicas, self).showEvent(event)

        # Garante que ao reabrir, tudo volte a funcionar
        self.connect_signals()

        # Reset do checkBoxSeleciona
        checkBox = self.findChild(QCheckBox, 'checkBoxSeleciona')
        if checkBox:
            checkBox.setChecked(False)
            checkBox.setEnabled(False)
        
        self.populate_combo_box()  # Atualiza o comboBoxCamada com as camadas disponíveis

        self.update_checkBoxSeleciona()  # Atualiza o estado do checkBoxSeleciona com base nas feições selecionadas

        self.update_layer_connections()  # Conecta os sinais da camada atual

        self.update_field_connections()
        self._refresh_comboBoxCampo()

        self.atualizar_treeViewCamadas()

        self._update_push_buttons_state()

    def _safe_connect(self, signal, slot):
        """Conecta com UniqueConnection quando possível, sem quebrar em versões/assinaturas diferentes."""
        if signal is None:
            return False
        try:
            signal.connect(slot, Qt.ConnectionType.UniqueConnection)
            return True
        except TypeError:
            # algumas assinaturas/sinais não aceitam UniqueConnection
            try:
                signal.connect(slot)
                return True
            except Exception:
                return False
        except Exception:
            return False

    def connect_signals(self):
        """Conecta todos os sinais da UI/projeto para manter a interface e as notas sincronizadas"""
        if getattr(self, "_signals_connected", False):
            return

        prj = QgsProject.instance()

        # Combo: camada mudou
        self._safe_connect(self.comboBoxCamada.currentIndexChanged, self.update_checkBoxSeleciona)
        self._safe_connect(self.comboBoxCamada.currentIndexChanged, self.update_layer_connections)
        self._safe_connect(self.comboBoxCamada.currentIndexChanged, self._refresh_comboBoxCampo)
        self._safe_connect(self.comboBoxCamada.currentIndexChanged, self._update_push_buttons_state)
        self._safe_connect(self.comboBoxCamada.currentIndexChanged, self._on_source_layer_changed)

        # Projeto: camadas mudaram (repopula combo e tree e reavalia botões)
        self._safe_connect(prj.layersAdded, self.populate_combo_box)
        self._safe_connect(prj.layersRemoved, self.populate_combo_box)
        self._safe_connect(prj.layerWillBeRemoved, self.populate_combo_box)

        # MUITO útil: algumas rotas de adição disparam layerWasAdded (depende do fluxo do QGIS)
        self._safe_connect(getattr(prj, "layerWasAdded", None), self.populate_combo_box)

        self._safe_connect(prj.layersAdded, self.atualizar_treeViewCamadas)
        self._safe_connect(prj.layersRemoved, self.atualizar_treeViewCamadas)
        self._safe_connect(prj.layerWillBeRemoved, self.atualizar_treeViewCamadas)

        self._safe_connect(prj.layersAdded, self._update_push_buttons_state)
        self._safe_connect(prj.layersRemoved, self._update_push_buttons_state)
        self._safe_connect(prj.layerWillBeRemoved, self._update_push_buttons_state)

        self._safe_connect(prj.layerWillBeRemoved, self._on_project_layer_will_be_removed_cleanup)

        # Botões
        self._safe_connect(self.pushButtonFechar.clicked, self.close)
        self._safe_connect(self.pushButtonConectada.clicked, self._on_push_conectada)
        self._safe_connect(self.pushButtonLivre.clicked, self._on_push_livre)
        self._safe_connect(self.pushButtonDXF.clicked, self._on_push_dxf)
        self._safe_connect(self.pushButtonCor.clicked, self._on_pick_label_color_for_layer)
        self._safe_connect(self.pushButtonCorLinha.clicked, self._on_pick_line_color_for_layer)

        # Demais sinais que você já tinha (mantém, mas use _safe_connect se quiser padronizar)
        self._safe_connect(self.doubleSpinBoxTamanho.valueChanged, self._restyle_selected_note_layer)
        self._safe_connect(self.comboBoxIndicador.currentIndexChanged, self._restyle_selected_note_layer)
        self._safe_connect(self.doubleSpinBoxLinha.valueChanged, self._resize_diagonal_current_layer)
        self._safe_connect(self.doubleSpinBoxCauda.valueChanged, self._resize_horizontal_current_layer)
        self._safe_connect(self.comboBoxCampo.currentIndexChanged, self._update_labels_from_field_for_selected_layer)
        self._safe_connect(self.doubleSpinBoxTexto.valueChanged, self._on_text_size_changed)

        for rb in (self.radioButtonSuperiorD, self.radioButtonSuperiorE, self.radioButtonInferiorD, self.radioButtonInferiorE):
            try:
                self._safe_connect(rb.toggled, self._on_quadrant_toggled)
            except Exception:
                pass  # nosec B110

        self._signals_connected = True

    def _safe_disconnect(self, signal, slot):
        """Desconecta sem levantar exceção se não estiver conectado."""
        try:
            signal.disconnect(slot)
            return True
        except Exception:
            return False

    def _cleanup_maptool_livre(self):
        """Desarma o maptool livre e restaura o maptool anterior (evita callback em objeto destruído)."""
        try:
            canvas = self.iface.mapCanvas()
        except Exception:
            return

        # Desconecta o callback do clique (se ainda estiver)
        try:
            if self._mt_livre:
                self._mt_livre.canvasClicked.disconnect(self._finish_free_note)
        except Exception:
            pass  # nosec B110

        # Restaura ferramenta anterior, se fizer sentido
        try:
            if self._mt_prev and canvas:
                canvas.setMapTool(self._mt_prev)
        except Exception:
            pass  # nosec B110

        self._mt_livre = None
        self._mt_prev = None

    def _disconnect_project_signals(self):
        """Remove conexões com QgsProject para evitar sinais chamando métodos após o diálogo fechar."""
        prj = QgsProject.instance()

        # sinais do projeto ligados em connect_signals()
        for sig in (prj.layersAdded, prj.layersRemoved, prj.layerWillBeRemoved, getattr(prj, "layerWasAdded", None)):
            if sig is None:
                continue
            self._safe_disconnect(sig, self.populate_combo_box)
            self._safe_disconnect(sig, self.atualizar_treeViewCamadas)
            self._safe_disconnect(sig, self._update_push_buttons_state)

        self._safe_disconnect(prj.layerWillBeRemoved, self._on_project_layer_will_be_removed_cleanup)

    def _disconnect_layer_signals(self):
        """Remove conexões com a camada atual (selection/fields) para evitar sinais pendurados."""
        # selectionChanged
        try:
            if self._last_layer_connected is not None:
                self._safe_disconnect(self._last_layer_connected.selectionChanged, self.update_checkBoxSeleciona)
        except Exception:
            pass  # nosec B110
        self._last_layer_connected = None

        # fields (usa sua rotina existente para desconectar do old)
        try:
            old = self._last_layer_fields_connected
            if isinstance(old, QgsVectorLayer):
                for sig_name in ("fieldsChanged", "updatedFields", "attributeAdded", "attributeDeleted", "attributeRenamed", "editingStopped"):
                    try:
                        sig = getattr(old, sig_name, None)
                        if sig:
                            self._safe_disconnect(sig, self._refresh_comboBoxCampo)
                    except Exception:
                        pass  # nosec B110
                try:
                    prov = old.dataProvider()
                    if prov and hasattr(prov, "fieldsChanged"):
                        self._safe_disconnect(prov.fieldsChanged, self._refresh_comboBoxCampo)
                except Exception:
                    pass  # nosec B110
        except Exception:
            pass  # nosec B110
        self._last_layer_fields_connected = None

    def _disconnect_ui_signals(self):
        """Opcional, mas seguro: remove conexões da UI (evita callbacks durante fechamento)."""
        try:
            self._safe_disconnect(self.comboBoxCamada.currentIndexChanged, self.update_checkBoxSeleciona)
            self._safe_disconnect(self.comboBoxCamada.currentIndexChanged, self.update_layer_connections)
            self._safe_disconnect(self.comboBoxCamada.currentIndexChanged, self._refresh_comboBoxCampo)
            self._safe_disconnect(self.comboBoxCamada.currentIndexChanged, self._update_push_buttons_state)
            self._safe_disconnect(self.comboBoxCamada.currentIndexChanged, self._on_source_layer_changed)
        except Exception:
            pass  # nosec B110

        try:
            self._safe_disconnect(self.pushButtonFechar.clicked, self.close)
        except Exception:
            pass  # nosec B110

        try:
            self._safe_disconnect(self.pushButtonConectada.clicked, self._on_push_conectada)
            self._safe_disconnect(self.pushButtonLivre.clicked, self._on_push_livre)
            self._safe_disconnect(self.pushButtonDXF.clicked, self._on_push_dxf)
            self._safe_disconnect(self.pushButtonCor.clicked, self._on_pick_label_color_for_layer)
            self._safe_disconnect(self.pushButtonCorLinha.clicked, self._on_pick_line_color_for_layer)
        except Exception:
            pass  # nosec B110

        try:
            self._safe_disconnect(self.doubleSpinBoxTamanho.valueChanged, self._restyle_selected_note_layer)
            self._safe_disconnect(self.comboBoxIndicador.currentIndexChanged, self._restyle_selected_note_layer)
            self._safe_disconnect(self.doubleSpinBoxLinha.valueChanged, self._resize_diagonal_current_layer)
            self._safe_disconnect(self.doubleSpinBoxCauda.valueChanged, self._resize_horizontal_current_layer)
            self._safe_disconnect(self.comboBoxCampo.currentIndexChanged, self._update_labels_from_field_for_selected_layer)
            self._safe_disconnect(self.doubleSpinBoxTexto.valueChanged, self._on_text_size_changed)
        except Exception:
            pass  # nosec B110

        for radio_button in (
            self.radioButtonSuperiorD,
            self.radioButtonSuperiorE,
            self.radioButtonInferiorD,
            self.radioButtonInferiorE):
            try:
                self._safe_disconnect(radio_button.toggled, self._on_quadrant_toggled)
            except Exception:
                pass  # nosec B110

    def closeEvent(self, event):
        """
        Fecha o diálogo com limpeza completa:
        - desarma maptool livre
        - desconecta sinais do QgsProject
        - desconecta sinais da camada atual
        (evita RuntimeError: wrapped C/C++ object ... has been deleted)
        """
        # 1) impedir callbacks do map canvas depois de fechar
        try:
            self._cleanup_maptool_livre()
        except Exception:
            pass  # nosec B110

        # 2) desligar sinais do projeto (os que mais causam crash pós-fechamento)
        try:
            self._disconnect_project_signals()
        except Exception:
            pass  # nosec B110

        # 3) desligar sinais da camada (selection/fields)
        try:
            self._disconnect_layer_signals()
        except Exception:
            pass  # nosec B110

        # 4) opcional: desligar sinais da UI
        try:
            self._disconnect_ui_signals()
        except Exception:
            pass  # nosec B110

        try:
            self._disconnect_tree_layer_signals()
        except Exception:
            pass  # nosec B110

        # Permite reconectar quando reabrir
        self._signals_connected = False

        self._disconnect_combo_layer_name_changed()

        # 5) deixa o Qt finalizar o fechamento
        super().closeEvent(event)

    def _on_text_size_changed(self, *args):
        """Slot do doubleSpinBoxTexto: reaplica labeling mantendo habilitado."""
        lyr = self._get_selected_dim_layer()
        if not lyr:
            return
        try:
            tmm = float(self.doubleSpinBoxTexto.value() or 10.0)
        except Exception:
            tmm = 10.0
        self._apply_point_labeling(lyr, tmm, True)

    def _on_quadrant_toggled(self, checked: bool):
        """Slot comum para os rádios de quadrante."""
        if checked:
            self._reorient_current_layer()

    def _tree_on_name_changed(self, layer_id: str, *args):
        """Slot nomeado (sem lambda) para renomeio."""
        self._sync_tree_item_name(layer_id)

    def _tree_on_style_changed(self, layer_id: str, *args):
        """Slot nomeado (sem lambda) para mudança de estilo/cor."""
        self._sync_tree_item_color(layer_id)

    def _connect_tree_layer_signal(self, lyr: QgsVectorLayer, sig_name: str, handler):
        """
        Conecta signals do layer sem lambda, usando partial + registro para desconectar depois.
        handler deve ser um método tipo: handler(layer_id, *args)
        """
        try:
            sig = getattr(lyr, sig_name, None)
            if not sig:
                return
            key = (lyr.id(), sig_name)
            if key in self._tree_layer_conns:
                return  # já conectado
            slot = partial(handler, lyr.id())
            sig.connect(slot)
            self._tree_layer_conns[key] = (sig, slot)
        except Exception:
            pass  # nosec B110

    def _disconnect_tree_layer_signals(self):
        """Desconecta todas as conexões registradas do tree."""
        for key, (sig, slot) in list(self._tree_layer_conns.items()):
            try:
                sig.disconnect(slot)
            except Exception:
                pass  # nosec B110
        self._tree_layer_conns.clear()

    def _combo_on_layer_name_changed(self, layer_id: str, *args):
        """Atualiza apenas o item do combo correspondente à camada renomeada."""
        try:
            idx = self.comboBoxCamada.findData(layer_id)
            if idx < 0:
                return
            lyr = QgsProject.instance().mapLayer(layer_id)
            if lyr:
                self.comboBoxCamada.setItemText(idx, lyr.name())
        except Exception:
            pass  # nosec B110

    def _connect_combo_layer_name_changed(self, lyr: QgsVectorLayer):
        """Conecta nameChanged do layer ao combo UMA vez (sem duplicar)."""
        try:
            lid = lyr.id()
            if lid in self._combo_name_conns:
                return
            sig = getattr(lyr, "nameChanged", None)
            if not sig:
                return
            slot = partial(self._combo_on_layer_name_changed, lid)
            sig.connect(slot)
            self._combo_name_conns[lid] = (sig, slot)
        except Exception:
            pass  # nosec B110

    def _disconnect_combo_layer_name_changed(self, layer_id: str | None = None):
        """Desconecta nameChanged do combo (de um layer específico ou de todos)."""
        if layer_id:
            rec = self._combo_name_conns.pop(layer_id, None)
            if rec:
                sig, slot = rec
                try:
                    sig.disconnect(slot)
                except Exception:
                    pass  # nosec B110
            return

        for lid in list(self._combo_name_conns.keys()):
            self._disconnect_combo_layer_name_changed(lid)

    def _init_combo_indicador(self):
        """
        Preenche o comboBoxIndicador com as opções fixas:
        - 'Seta'      (code: 'arrow')
        - 'Circular'  (code: 'circle')
        - 'Quadrado'  (code: 'square')
        Preserva a seleção anterior, se houver.
        """
        cb = self.comboBoxIndicador
        if cb is None:
            return

        # preserva seleção atual (pelo código armazenado em UserRole)
        current_code = cb.currentData(Qt.ItemDataRole.UserRole) if cb.count() > 0 else None

        cb.blockSignals(True)
        cb.clear()

        items = [
            (self.tr("Seta"), "arrow"),
            (self.tr("Circular"), "circle"),
            (self.tr("Quadrado"), "square")]
        for label, code in items:
            cb.addItem(label, code)

        # restaura seleção anterior (se existir), senão define padrão "Seta"
        if current_code is not None:
            idx = cb.findData(current_code, role=Qt.ItemDataRole.UserRole)
            if idx != -1:
                cb.setCurrentIndex(idx)
            else:
                cb.setCurrentIndex(0)
        else:
            cb.setCurrentIndex(0)

        cb.blockSignals(False)

    def get_indicador(self) -> tuple[str, str]:
        """
        Retorna (label, code) do comboBoxIndicador.
        Ex.: ('Circular', 'circle')
        """
        cb = self.comboBoxIndicador
        if cb is None or cb.currentIndex() < 0:
            return ("", "")
        return (cb.currentText(), cb.currentData(Qt.ItemDataRole.UserRole))

    def _point_from_geom(self, geom: QgsGeometry) -> QgsPointXY | None:
        """
        Extrai um QgsPointXY de geometrias Point/MultiPoint (qualquer variante Z/M).
        Retorna None para geometrias inválidas.
        """
        if not geom or geom.isEmpty():
            return None
        wkb = geom.wkbType()
        try:
            if QgsWkbTypes.isSingleType(wkb):
                p = geom.asPoint()
                return QgsPointXY(p.x(), p.y())
            elif QgsWkbTypes.isMultiType(wkb):
                m = geom.asMultiPoint()
                if m:
                    return QgsPointXY(m[0].x(), m[0].y())
        except Exception:
            pass  # nosec B110
        return None

    def _suggest_leader_offset(self, lyr: QgsVectorLayer) -> tuple[float, float]:
        """
        Offset em unidades do mapa proporcional à extensão (3% da menor dimensão).
        """
        ext = lyr.extent()
        if ext and not ext.isEmpty():
            w = max(1e-9, ext.width())
            h = max(1e-9, ext.height())
        else:
            w, h = (100.0, 100.0)
        v = 0.03 * min(w, h)
        return (v, v)
    
    def _add_layer_to_group(self, layer: QgsVectorLayer, group_name: str = None):
        """
        Adiciona a camada de notas ao grupo "Notas" no painel de camadas,
        insere o nó no topo do grupo, força a seleção dessa camada no
        treeView interno do plugin e, opcionalmente, foca a camada no
        painel de camadas do QGIS (Layer Panel).
        """
        if group_name is None:
            group_name = self.tr("Notas")

        prj = QgsProject.instance()                 # projeto QGIS atual
        root = prj.layerTreeRoot()                  # raiz da árvore de camadas

        prj.addMapLayer(layer, addToLegend=False)   # adiciona a layer ao projeto, sem pôr direto na legenda

        group = root.findGroup(group_name) or root.addGroup(group_name)  # encontra/cria o grupo "Notas"
        node = QgsLayerTreeLayer(layer)             # cria o nó da layer para a árvore
        group.insertChildNode(0, node)              # insere no topo do grupo (posição 0)

        # força a camada aparecer selecionada no tree do plugin
        self._tv_selected_layer_id = layer.id()
        try:
            self.atualizar_treeViewCamadas()        # sincroniza o treeViewCamada com a nova seleção
        except Exception:
            pass  # nosec B110

        # opcional: também seleciona a camada no painel de camadas do QGIS
        try:
            self.iface.layerTreeView().setCurrentLayer(layer)  # destaca a layer no Layer Panel
        except Exception:
            pass  # nosec B110

    def _refresh_comboBoxCampo(self, *args):
        """
        Repopula o comboBoxCampo com os campos da camada atualmente
        selecionada em comboBoxCamada. Robusto a sinais com parâmetros.
        """
        cb = self.comboBoxCampo
        if cb is None:
            return

        cb.blockSignals(True)
        cb.clear()

        layer_id = self.comboBoxCamada.currentData()
        lyr = QgsProject.instance().mapLayer(layer_id) if layer_id else None

        if isinstance(lyr, QgsVectorLayer):
            for fld in lyr.fields():
                cb.addItem(fld.name())

        cb.blockSignals(False)

    def mostrar_mensagem(self, texto, tipo, duracao=2, caminho_pasta=None, caminho_arquivo=None):
        """
        Exibe mensagem na barra do QGIS.
        tipo: 'Erro', 'Aviso' ou 'Sucesso'
        """
        bar = self.iface.messageBar()

        # remove eventual widget anterior de sucesso
        if tipo == "Sucesso" and getattr(self, "_widget_msg_sucesso", None) is not None:
            try:
                bar.popWidget(self._widget_msg_sucesso)
            except Exception:
                bar.clearWidgets()
            self._widget_msg_sucesso = None

        if tipo == "Erro":
            bar.pushMessage("Erro", texto, level=Qgis.MessageLevel.Critical, duration=duracao)

        elif tipo == "Aviso":
            bar.pushMessage("Aviso", texto, level=Qgis.MessageLevel.Warning, duration=duracao)

        elif tipo == "Sucesso":
            msg = bar.createMessage("Sucesso", texto)

            def _abrir_path(path: str):
                if not path:
                    return
                # resolve / normaliza para evitar "url" estranha
                abs_path = os.path.abspath(path)
                QDesktopServices.openUrl(QUrl.fromLocalFile(abs_path))

            # botão para abrir pasta (opcional)
            if caminho_pasta:
                btn_pasta = QPushButton(self.tr("Abrir Pasta"))
                btn_pasta.clicked.connect(lambda _, p=caminho_pasta: _abrir_path(p))
                msg.layout().insertWidget(1, btn_pasta)

            # botão para abrir arquivo (opcional)
            if caminho_arquivo:
                btn_exec = QPushButton(self.tr("Abrir Arquivo"))
                btn_exec.clicked.connect(lambda _, p=caminho_arquivo: _abrir_path(p))
                msg.layout().insertWidget(2, btn_exec)

            self._widget_msg_sucesso = bar.pushWidget(msg, level=Qgis.MessageLevel.Info, duration=duracao)

    def update_checkBoxSeleciona(self):
        """
        Atualiza o estado do checkBoxSeleciona com base na seleção de feições da camada atualmente selecionada.

        Parâmetros:
        self : objeto
            Referência à instância atual da classe.

        A função realiza as seguintes ações:
        - Obtém o ID da camada atualmente selecionada no comboBoxCamada.
        - Se uma camada válida for encontrada, verifica a quantidade de feições selecionadas na camada.
        - Se houver feições selecionadas, o checkBoxSeleciona é ativado.
        - Se não houver feições selecionadas ou a camada não for válida, o checkBoxSeleciona é desativado e desmarcado.
        """
        layer_id = self.comboBoxCamada.currentData()
        cb = self.cbSeleciona
        if not cb:
            return
        if layer_id:
            layer = QgsProject.instance().mapLayer(layer_id)
            if layer:
                cb.setEnabled(layer.selectedFeatureCount() > 0)
                if layer.selectedFeatureCount() == 0:
                    cb.setChecked(False)
                return
        cb.setEnabled(False); cb.setChecked(False)

    def populate_combo_box(self, *args):
        """
        Popula o comboBoxCamada com as camadas de PONTOS disponíveis no projeto.

        A função:
        - Preserva a seleção atual, se possível;
        - Conecta nameChanged para manter o rótulo sincronizado;
        - Reconecta os sinais da camada atual (selectionChanged) ao final.
        """
        current_layer_id = self.comboBoxCamada.currentData()
        self.comboBoxCamada.blockSignals(True)
        self.comboBoxCamada.clear()

        for layer in QgsProject.instance().mapLayers().values():
            if isinstance(layer, QgsVectorLayer) and QgsWkbTypes.geometryType(layer.wkbType()) == QgsWkbTypes.GeometryType.PointGeometry:
                self.comboBoxCamada.addItem(layer.name(), layer.id())
                self._connect_combo_layer_name_changed(layer)

        # Restaura a seleção anterior, se ainda existir
        if current_layer_id:
            idx = self.comboBoxCamada.findData(current_layer_id)
            if idx != -1:
                self.comboBoxCamada.setCurrentIndex(idx)

        self.comboBoxCamada.blockSignals(False)

        # Garantir que os sinais e o estado do checkbox reflitam a camada atual
        self.update_layer_connections()
        self.update_checkBoxSeleciona()
        self._update_push_buttons_state()

    def _gerar_nome_unico(self, nome_base):
        """Gera nome único para camada, evitando duplicidade no projeto."""
        layers_names = [layer.name() for layer in QgsProject.instance().mapLayers().values()]
        nome = nome_base
        contador = 1
        while nome in layers_names:
            nome = f"{nome_base}_{contador}"
            contador += 1
        return nome

    def configurar_campo_oculto(self, camada: QgsVectorLayer, nomes: list[str]):
        """
        Oculta os campos dados tanto na tabela de atributos quanto no formulário de edição.
        """
        for nome in nomes:
            idx = camada.fields().indexOf(nome)
            if idx != -1:
                setup = QgsEditorWidgetSetup("Hidden", {})
                camada.setEditorWidgetSetup(idx, setup)

    def _init_treeview_camadas(self):
        """Cria o modelo e configura o treeViewCamada."""
        model = QStandardItemModel(0, 1, self)  # 1 coluna
        model.setHeaderData(0, Qt.Orientation.Horizontal, self.tr("Notas"))
        self._tv_model = model

        # Centraliza o cabeçalho
        header = self.treeViewCamada.header()
        header.setDefaultAlignment(Qt.AlignmentFlag.AlignCenter)

        self.treeViewCamada.setModel(model)
        self.treeViewCamada.setHeaderHidden(False)
        self.treeViewCamada.setRootIsDecorated(False)  # sem ícones de expandir
        self.treeViewCamada.setAllColumnsShowFocus(True)
        self.treeViewCamada.setItemsExpandable(False)
        self.treeViewCamada.setExpandsOnDoubleClick(False)
        self.treeViewCamada.setSelectionBehavior(QAbstractItemView.SelectionBehavior.SelectRows)
        self.treeViewCamada.setSelectionMode(QAbstractItemView.SelectionMode.SingleSelection)

        # delegate do “X”
        self.treeViewCamada.setItemDelegate(TreeDeleteButtonDelegate(self))

        # conecta seleção
        try:
            self.treeViewCamada.selectionModel().selectionChanged.connect(self._on_tv_selection_changed)
        except Exception:
            pass  # nosec B110 | se ainda não houver selectionModel, a próxima chamada a atualizar resolverá

    def atualizar_treeViewCamadas(self):
        """
        Preenche o treeViewCamada com as camadas do grupo 'Notas'.
        Regras:
          - Texto em negrito;
          - Garante sempre 1 selecionada, se houver itens;
          - Se nova camada foi adicionada, seleciona a nova;
          - Se deletada, seleciona a anterior (ou última disponível);
          - Se seleção anterior ainda existir, preserva.
        """
        if self._tv_model is None:
            self._init_treeview_camadas()

        model, view = self._tv_model, self.treeViewCamada
        old_ids = list(self._tv_last_layer_ids)
        prev_selected_id = self._tv_selected_layer_id

        model.removeRows(0, model.rowCount())

        root = QgsProject.instance().layerTreeRoot()
        grupo = root.findGroup(self._group_name)
        new_ids = []

        if grupo:
            for node in grupo.findLayers():
                lyr = node.layer()
                if isinstance(lyr, QgsVectorLayer) and lyr.geometryType() == QgsWkbTypes.GeometryType.LineGeometry:
                    it = QStandardItem(lyr.name())
                    f = it.font(); f.setBold(True); it.setFont(f)
                    it.setEditable(False)
                    it.setData(lyr.id(), Qt.ItemDataRole.UserRole)
                    try:
                        it.setForeground(QBrush(self._get_layer_main_color(lyr)))
                    except Exception:
                        pass  # nosec B110
                    model.appendRow(it)

                    # nome → tree em tempo real (sem duplicar)
                    try:
                        # lyr.nameChanged.connect(lambda lid=lyr.id(): self._sync_tree_item_name(lid))
                        self._connect_tree_layer_signal(lyr, "nameChanged", self._tree_on_name_changed)
                    except Exception:
                        pass  # nosec B110
                    try:
                        # lyr.rendererChanged.connect(lambda lid=lyr.id(): self._sync_tree_item_color(lid))
                        self._connect_tree_layer_signal(lyr, "rendererChanged", self._tree_on_style_changed)
                    except Exception:
                        pass  # nosec B110
                    try:
                        # lyr.styleChanged.connect(lambda lid=lyr.id(): self._sync_tree_item_color(lid))
                        self._connect_tree_layer_signal(lyr, "styleChanged", self._tree_on_style_changed)
                    except Exception:
                        pass  # nosec B110

                    new_ids.append(lyr.id())

        self._tv_last_layer_ids = list(new_ids)

        # garantir seleção
        to_select = prev_selected_id if prev_selected_id in new_ids else (new_ids[-1] if new_ids else None)
        self._tv_selected_layer_id = to_select

        if to_select is not None:
            # percorre linhas e seleciona a correspondente
            for row in range(model.rowCount()):
                idx = model.index(row, 0)
                if model.data(idx, Qt.ItemDataRole.UserRole) == to_select:
                    sel_model = view.selectionModel()
                    if sel_model:
                        sel_model.clearSelection()
                        sel_model.select(idx,
                            QItemSelectionModel.SelectionFlag.Select | QItemSelectionModel.SelectionFlag.Rows)
                        view.setCurrentIndex(idx)
                    break

        self._update_push_buttons_state()

    def _sync_tree_item_name(self, layer_id: str):
        """Sincroniza o nome do item do tree com o nome atual da camada."""
        layer = QgsProject.instance().mapLayer(layer_id)
        item = self._find_tree_item_by_layer_id(layer_id)
        if layer and item:
            item.setText(layer.name())

    def update_combo_box_item(self, *args):
        """Atualiza textos do comboBoxCamada conforme renomeios."""
        for i in range(self.comboBoxCamada.count()):
            lid = self.comboBoxCamada.itemData(i)
            layer = QgsProject.instance().mapLayer(lid)
            if layer:
                self.comboBoxCamada.setItemText(i, layer.name())

    def _on_source_layer_changed(self, *_):
        """
        Reage à troca do comboBoxCamada:
          - Repopula o comboBoxCampo (sem emitir sinais).
          - Preserva o campo anteriormente usado pela camada de notas, se existir na nova camada.
          - Reaplica imediatamente os rótulos (nm_text) a partir do novo layer+campo.
        """
        # 1) Repopula lista de campos do novo layer
        try:
            self.comboBoxCampo.blockSignals(True)
            self._refresh_comboBoxCampo()
        finally:
            self.comboBoxCampo.blockSignals(False)

        # 2) Se houver uma camada de notas selecionada, tentamos preservar o campo anterior
        lyr = self._get_selected_dim_layer()
        if not isinstance(lyr, QgsVectorLayer):
            # Nada a rotular agora
            return

        # Campo que a camada de notas usava anteriormente (se houver)
        prev_field = str(lyr.customProperty("nm_field_name", "")).strip()
        if prev_field:
            idx = self.comboBoxCampo.findText(prev_field)
            if idx >= 0:
                # Seleciona o mesmo campo no novo layer (se ele existir lá também)
                self.comboBoxCampo.blockSignals(True)
                self.comboBoxCampo.setCurrentIndex(idx)
                self.comboBoxCampo.blockSignals(False)
            # Se não existir, mantém o que o _refresh colocou (primeiro da lista / vazio)

        # 3) Atualiza imediatamente os rótulos (respeita notas LIVRES e demais regras)
        self._update_labels_from_field_for_selected_layer()

    def _get_layer_main_color(self, layer: QgsVectorLayer) -> QColor:
        """Tenta ler a cor 'principal' do símbolo (fallback: preto)."""
        try:
            r = layer.renderer()
            if not r:
                return QColor("black")
            sym = r.symbol()
            if not sym or sym.symbolLayerCount() == 0:
                return QColor("black")
            sll0 = sym.symbolLayer(0)
            if hasattr(sll0, "color"):
                c = sll0.color()
                if isinstance(c, QColor) and c.isValid():
                    return c
            if hasattr(sll0, "outlineColor"):
                c = sll0.outlineColor()
                if isinstance(c, QColor) and c.isValid():
                    return c
        except Exception:
            pass  # nosec B110
        return QColor("black")

    def _find_tree_item_by_layer_id(self, layer_id: str) -> QStandardItem | None:
        """Retorna o item do treeViewCamada correspondente ao ID da camada, ou None se não encontrado."""
        if not self._tv_model:
            return None
        for row in range(self._tv_model.rowCount()):
            idx = self._tv_model.index(row, 0)
            if self._tv_model.data(idx, Qt.ItemDataRole.UserRole) == layer_id:
                return self._tv_model.itemFromIndex(idx)
        return None

    def _sync_tree_item_color(self, layer_id: str):
        """Atualiza a cor do texto do item do tree para refletir a cor da camada."""
        layer = QgsProject.instance().mapLayer(layer_id)
        item  = self._find_tree_item_by_layer_id(layer_id)
        if not layer or not item:
            return
        col = self._get_layer_main_color(layer)
        item.setForeground(QBrush(col))

    def _on_pick_color_for_layer(self):
        """
        Abre o seletor de cor e aplica a cor escolhida:
          - ao nome da camada (item do treeViewCamada);
          - ao símbolo da camada de dimensão (linha, setas e tick).
        Atualiza em tempo real.
        """
        # índice selecionado no treeView
        view = self.treeViewCamada
        sel = view.selectionModel().selectedIndexes()
        if not sel:
            self.mostrar_mensagem(self.tr("Selecione uma camada de dimensão na lista."), "Aviso")
            return
        idx = sel[0]
        layer_id = self._tv_model.data(idx, Qt.ItemDataRole.UserRole)
        layer = QgsProject.instance().mapLayer(layer_id)
        if not isinstance(layer, QgsVectorLayer) or layer.geometryType() != QgsWkbTypes.GeometryType.LineGeometry:
            self.mostrar_mensagem(self.tr("A camada selecionada não é uma camada de linhas de Notas."), "Erro")
            return

        # cor inicial (tenta pegar do símbolo base)
        initial = QColor("black")
        try:
            sym = layer.renderer().symbol()
            if sym and sym.symbolLayerCount() > 0:
                sll0 = sym.symbolLayer(0)
                if hasattr(sll0, "color"):
                    initial = sll0.color()
                elif hasattr(sll0, "outlineColor"):
                    initial = sll0.outlineColor()
        except Exception:
            pass  # nosec B110

        color = QColorDialog.getColor(initial, self, self.tr("Escolha a cor da dimensão"))
        if not color.isValid():
            return

        # pinta item do treeview
        item = self._tv_model.itemFromIndex(idx)
        if item:
            item.setForeground(QBrush(color))

        # aplica cor no símbolo da camada
        self._apply_dim_color(layer, color)

        # Monitora a atualização das notas
        self._sync_tree_item_color(layer.id())

        # refresh visual
        layer.triggerRepaint()
        try:
            self.iface.mapCanvas().refresh()
        except Exception:
            pass  # nosec B110

    def _apply_dim_color(self, layer: QgsVectorLayer, color: QColor):
        """
        Aplica 'color' às partes da camada de dimensão de forma SEGURA:
          - pausa renderização do canvas;
          - clona o símbolo e sub-símbolos antes de editar;
          - seta um renderer novo na camada;
          - retoma renderização.
        """
        if not layer or not layer.renderer():
            return

        canvas = None
        try:
            canvas = self.iface.mapCanvas()
            if canvas:
                canvas.setRenderFlag(False)  # ⏸️ pausa render
        except Exception:
            canvas = None

        try:
            # 1) Clona o símbolo raiz (não muta o símbolo em uso pelo render)
            sym_old = layer.renderer().symbol()
            if sym_old is None:
                return
            sym = sym_old.clone()

            # 2) Edita as symbol layers do clone
            count = sym.symbolLayerCount()
            for i in range(count):
                sll = sym.symbolLayer(i)

                # Linha principal: tenta setColor se disponível
                if hasattr(sll, "setColor"):
                    try:
                        sll.setColor(color)
                    except Exception:
                        pass  # nosec B110

                # Marcadores ao longo da linha (ticks e setas)
                if isinstance(sll, QgsMarkerLineSymbolLayer):
                    sub_old = sll.subSymbol()
                    if sub_old:
                        sub = sub_old.clone()   # ✅ CLONE do sub-símbolo
                        try:
                            sub.setColor(color)
                            if hasattr(sub, "setOutlineColor"):
                                sub.setOutlineColor(color)
                        except Exception:
                            pass  # nosec B110
                        sll.setSubSymbol(sub)

            # 3) Cria renderer novo com o símbolo clonado/editado
            new_renderer = QgsSingleSymbolRenderer(sym)
            layer.setRenderer(new_renderer)

            # (Opcional) Atualiza cor do rótulo para casar com a linha
            try:
                lbl = layer.labeling()
                if isinstance(lbl, QgsVectorLayerSimpleLabeling):
                    pal = lbl.settings()
                    fmt = pal.format()
                    fmt.setColor(color)
                    pal.setFormat(fmt)
                    layer.setLabeling(QgsVectorLayerSimpleLabeling(pal))
                    layer.setLabelsEnabled(True)
            except Exception:
                pass  # nosec B110

            # 4) Repaint
            layer.triggerRepaint()

            # garante que o tree reflita a cor final aplicada no símbolo
            try:
                self._sync_tree_item_color(layer.id())
            except Exception:
                pass  # nosec B110

        finally:
            # 5) Retoma renderização do canvas
            if canvas:
                canvas.setRenderFlag(True)
                try:
                    canvas.refresh()
                except Exception:
                    pass  # nosec B110

    def _get_selected_dim_layer(self):
        """Retorna a camada (QgsVectorLayer) atualmente selecionada no treeViewCamada."""
        try:
            idxs = self.treeViewCamada.selectionModel().selectedIndexes()
        except Exception:
            return None
        if not idxs:
            return None
        idx = idxs[0]
        lyr_id = self._tv_model.data(idx, Qt.ItemDataRole.UserRole)
        lyr = QgsProject.instance().mapLayer(lyr_id)
        if isinstance(lyr, QgsVectorLayer) and lyr.geometryType() == QgsWkbTypes.GeometryType.LineGeometry:
            return lyr
        return None

    def escolher_local_para_salvar(self, nome_padrao, tipo_arquivo):
        """
        Permite ao usuário escolher um local e um nome de arquivo para salvar uma camada.
        Lembra o último diretório usado e evita sobrescrever propondo sufixo _1, _2, ...
        """
        settings = QSettings()
        lastDir = settings.value("lastDir", "", type=str)

        # Fallback quando lastDir vier vazio/inválido
        if not lastDir or not os.path.isdir(lastDir):
            standard_location = getattr(QStandardPaths, "StandardLocation", QStandardPaths)
            docs = QStandardPaths.writableLocation(standard_location.DocumentsLocation)

            lastDir = docs if docs and os.path.isdir(docs) else QDir.homePath()

        options = QFileDialog.Options()

        base_nome_padrao, extensao = os.path.splitext(nome_padrao)
        numero = 1
        nome_proposto = base_nome_padrao

        # incrementa sufixo no diretório inicial
        while os.path.exists(os.path.join(lastDir, nome_proposto + extensao)):
            nome_proposto = f"{base_nome_padrao}_{numero}"
            numero += 1

        nome_completo_proposto = os.path.join(lastDir, nome_proposto + extensao)

        fileName, _ = QFileDialog.getSaveFileName(self, self.tr("Salvar Camada"), nome_completo_proposto, tipo_arquivo, options=options)

        if fileName:
            # Salva lastDir corretamente (sempre absoluto)
            settings.setValue("lastDir", os.path.dirname(os.path.abspath(fileName)))

            # garante extensão (case-insensitive)
            if extensao and not fileName.lower().endswith(extensao.lower()):
                fileName += extensao

            return fileName

        return None

    def _mm_to_map_units(self, mm: float) -> float:
        """
        Converte mm em unidades do mapa (no zoom atual do canvas).
        """
        try:
            canvas = self.iface.mapCanvas()
            dpi = canvas.logicalDpiX() or 96.0
            mup = canvas.mapUnitsPerPixel() or 1.0
            pixels_per_mm = dpi / 25.4
            return mm * pixels_per_mm * mup
        except Exception:
            # fallback (evita travar se algo faltar)
            return mm

    def _head_contact_point(self, p_center: QgsPointXY, p1: QgsPointXY, r_map: float, indicador: str) -> QgsPointXY:
        """
        Ponto na BORDA do indicador (círculo/quadrado) na direção p_center->p1.
        r_map = raio (círculo) ou semi-lado (quadrado).
        """
        dx = p1.x() - p_center.x()
        dy = p1.y() - p_center.y()
        if abs(dx) < 1e-12 and abs(dy) < 1e-12:
            return QgsPointXY(p_center.x() + r_map, p_center.y())
        if (indicador or "").lower() == "square":
            a = r_map
            t = a / max(abs(dx), abs(dy))
            return QgsPointXY(p_center.x() + dx * t, p_center.y() + dy * t)
        else:
            L = (dx*dx + dy*dy) ** 0.5
            ux, uy = dx / L, dy / L
            return QgsPointXY(p_center.x() + ux * r_map, p_center.y() + uy * r_map)

    def _center_from_border(self, p_border: QgsPointXY, p1: QgsPointXY, r_map: float, indicador: str) -> QgsPointXY:
        """
        Dado um ponto de BORDA (onde o líder encosta) e o próximo vértice p1,
        retorna o centro do indicador para o raio/semi-lado r_map.
        """
        vx = p1.x() - p_border.x()
        vy = p1.y() - p_border.y()
        if abs(vx) < 1e-12 and abs(vy) < 1e-12:
            return QgsPointXY(p_border.x(), p_border.y())

        if (indicador or "").lower() == "square":
            # normaliza em norma L∞ (max-abs) para lado 'a' = r_map
            a = r_map
            m = max(abs(vx), abs(vy))
            ux, uy = vx / m, vy / m
            return QgsPointXY(p_border.x() - a * ux, p_border.y() - a * uy)
        else:
            # círculo: volta 'r' ao longo da direção do líder
            L = (vx*vx + vy*vy) ** 0.5
            ux, uy = vx / L, vy / L
            return QgsPointXY(p_border.x() - r_map * ux, p_border.y() - r_map * uy)

    def _is_closed_polyline(self, pl, eps: float = 1e-9) -> bool:
        """
        Verifica se uma polilinha está fechada.
        
        Considera "fechada" quando:
          - A lista de pontos existe e tem pelo menos 2 pontos; e
          - O primeiro e o último ponto coincidem dentro de uma tolerância (eps).
        
        Parâmetros
        pl : list[QgsPointXY]
            Sequência de vértices da polilinha.
        eps : float, opcional
            Tolerância numérica para comparar as coordenadas (default: 1e-9).
        
        Retorna
        bool
            True se a polilinha é fechada, False caso contrário.
        """
        # garante que existe uma lista de pontos e com tamanho mínimo
        has_points = bool(pl) and len(pl) >= 2
        # diferença em X entre o primeiro e o último ponto
        dx_close = abs(pl[0].x() - pl[-1].x()) if has_points else float("inf")
        # diferença em Y entre o primeiro e o último ponto
        dy_close = abs(pl[0].y() - pl[-1].y()) if has_points else float("inf")
        # fechado se dx e dy estiverem dentro da tolerância
        return has_points and (dx_close < eps) and (dy_close < eps)

    def _extract_first_polyline(self, geom: QgsGeometry) -> list:
        """
        Extrai a primeira polilinha de uma geometria do QGIS.

        Regras de extração:
          - Se `geom` for uma LineString → retorna `geom.asPolyline()`.
          - Se `geom` for uma MultiLineString → retorna o primeiro anel/linha (`geom.asMultiPolyline()[0]`).
          - Para qualquer outro tipo ou em caso de erro/geom vazia → retorna lista vazia.

        Parâmetros
        geom : QgsGeometry
            Geometria de entrada (pode ser LineString, MultiLineString, etc.).

        Retorna
        list[QgsPointXY]
            Lista de vértices (QgsPointXY) da primeira polilinha encontrada,
            ou `[]` se não for possível extrair.
        """
        # Sai cedo se a geometria não existe ou está vazia
        if not geom or geom.isEmpty():
            return []

        # Tenta extrair como LineString simples
        try:
            pl = geom.asPolyline()
            if pl:
                return pl  # ← caso comum: uma única polilinha
        except Exception:
            pass  # nosec B110 | mantém robustez mesmo se o provider não suportar

        # Tenta extrair como MultiLineString e pegar a primeira
        try:
            mpls = geom.asMultiPolyline()
            if mpls:
                return mpls[0]  # ← primeiro componente da multi-geometria
        except Exception:
            pass  # nosec B110 | ignora e segue para retorno vazio

        # Nenhuma polilinha válida foi encontrada
        return []

    def _closed_polyline_center(self, pts):
        """Centro de uma polilinha fechada (círculo aproximado ou quadrado)."""
        if not pts:
            return None
        try:
            # garante fechado
            if abs(pts[0].x()-pts[-1].x()) > 1e-12 or abs(pts[0].y()-pts[-1].y()) > 1e-12:
                ring = pts + [pts[0]]
            else:
                ring = pts
            g = QgsGeometry.fromPolygonXY([ring])
            p = g.centroid().asPoint()
            return QgsPointXY(p.x(), p.y())
        except Exception:
            # fallback: centro do bbox
            xs = [p.x() for p in pts]; ys = [p.y() for p in pts]
            return QgsPointXY(0.5*(min(xs)+max(xs)), 0.5*(min(ys)+max(ys)))

    def _rebuild_indicator_geoms_in_layer(self, layer: QgsVectorLayer, indicador: str, size_mm: float):
        """
        - 'circle'/'square': usa o CENTRO existente (se houver figura fechada perto do início do líder),
          translada TODO o líder para que comece na BORDA, e recria a figura no mesmo centro.
        - 'arrow': só remove figuras fechadas antigas (e, se houver líderes ancorados na borda, move-os ao centro).
        Obs: toda conversão mm->map é feita pelo fator congelado da camada (nm_mm2mu).
        """
        if not isinstance(layer, QgsVectorLayer):
            return

        prov = layer.dataProvider()
        if prov is None:
            return

        indicador = (indicador or "arrow").lower()

        leaders = []      # [(fid, [pts...])]
        closed_figs = []  # [(fid, [pts...], center)]

        for f in layer.getFeatures():
            pl = self._extract_first_polyline(f.geometry())
            if len(pl) >= 2:
                if self._is_closed_polyline(pl):
                    center = self._closed_polyline_center(pl)
                    closed_figs.append((f.id(), pl, center))
                else:
                    leaders.append((f.id(), pl))

        def _nearest_center(pt: QgsPointXY):
            best = None
            best_d2 = None
            for _, _, c in closed_figs:
                if c is None:
                    continue
                dx = pt.x() - c.x()
                dy = pt.y() - c.y()
                d2 = dx * dx + dy * dy
                if best_d2 is None or d2 < best_d2:
                    best_d2 = d2
                    best = c
            return best

        # Ramo ARROW: remove figuras e (opcional) recentraliza líderes
        if indicador not in ("circle", "square"):
            # Se existir figura próxima, e o líder está ancorado na BORDA, traz de volta ao CENTRO.
            # Se não existir figura, não mexe no líder.
            geom_changes = {}
            if closed_figs:
                for fid, pl in leaders:
                    if len(pl) < 2:
                        continue
                    c = _nearest_center(pl[0])
                    if not c:
                        continue
                    dx = c.x() - pl[0].x()
                    dy = c.y() - pl[0].y()
                    if abs(dx) > 1e-9 or abs(dy) > 1e-9:
                        new_pl = [QgsPointXY(p.x() + dx, p.y() + dy) for p in pl]
                        geom_changes[fid] = QgsGeometry.fromPolylineXY(new_pl)

            if geom_changes:
                prov.changeGeometryValues(geom_changes)

            # remove figuras fechadas antigas (círculo/quadrado)
            if closed_figs:
                prov.deleteFeatures([fid for fid, _, _ in closed_figs])

            layer.updateExtents()
            layer.triggerRepaint()
            try:
                self.iface.mapCanvas().refresh()
            except Exception:
                pass  # nosec B110
            return

        # circle/square: manter centro e ancorar líder na BORDA
        # Conversão pelo fator da LAYER (congelado)
        r_req_map = self._mm_to_map_units_for_layer(layer, float(size_mm) / 2.0)

        # centros por líder (preferir figura existente; fallback = início do leader)
        centers = []
        for _, pl in leaders:
            if len(pl) < 2:
                centers.append(None)
                continue
            c = _nearest_center(pl[0]) if closed_figs else None
            centers.append(c or QgsPointXY(pl[0].x(), pl[0].y()))

        # Colisão usando gap/min em mm convertidos pela LAYER (congelado)
        r_eff_list = self._compute_safe_radii(centers, indicador, r_req_map, gap_mm=1.0, min_mm=0.2, layer=layer)  # <<< importante
        

        # índices (para setar nm_role=2 nas figuras, se existir)
        flds = layer.fields()
        ix_role = flds.indexOf("nm_role") if flds is not None else -1

        geom_changes = {}  # fid -> nova geom do líder
        new_figs = []      # novas figuras fechadas

        for idx, (fid, pl) in enumerate(leaders):
            if len(pl) < 2:
                continue

            center = centers[idx]
            if center is None:
                continue

            r_map = r_eff_list[idx]

            # novo início na BORDA na direção do 1º segmento
            border = self._head_contact_point(center, pl[1], r_map, indicador)

            # translada TODO o líder para começar na borda
            dx = border.x() - pl[0].x()
            dy = border.y() - pl[0].y()
            if abs(dx) > 1e-9 or abs(dy) > 1e-9:
                new_pl = [QgsPointXY(p.x() + dx, p.y() + dy) for p in pl]
                geom_changes[fid] = QgsGeometry.fromPolylineXY(new_pl)

            # recria figura centrada em 'center' com r_map efetivo
            if indicador == "circle":
                N = 64
                pts = [
                    QgsPointXY(
                        center.x() + r_map * math.cos(2.0 * math.pi * k / N),
                        center.y() + r_map * math.sin(2.0 * math.pi * k / N)
                    ) for k in range(N)]
                pts.append(pts[0])
            else:
                a = r_map
                pts = [
                    QgsPointXY(center.x() - a, center.y() - a),
                    QgsPointXY(center.x() + a, center.y() - a),
                    QgsPointXY(center.x() + a, center.y() + a),
                    QgsPointXY(center.x() - a, center.y() + a),
                    QgsPointXY(center.x() - a, center.y() - a)]

            nf = QgsFeature()
            nf.setGeometry(QgsGeometry.fromPolylineXY(pts))
            nf.setAttributes([None] * flds.count())
            if ix_role >= 0:
                nf.setAttribute(ix_role, 2)  # figura
            new_figs.append(nf)

        # Remove antigas, aplica mudanças e adiciona novas
        if closed_figs:
            prov.deleteFeatures([fid for fid, _, _ in closed_figs])
        if geom_changes:
            prov.changeGeometryValues(geom_changes)
        if new_figs:
            prov.addFeatures(new_figs)

        layer.updateExtents()
        layer.triggerRepaint()
        try:
            self.iface.mapCanvas().refresh()
        except Exception:
            pass  # nosec B110

    def _compute_safe_radii(self, centers: list, indicador: str, requested_r_map: float, gap_mm: float = 1.0, min_mm: float = 0.2, layer: QgsVectorLayer | None = None) -> list[float]:
        """
        Retorna, para cada centro, o raio/semilado máximo permitido (em unidades do MAPA)
        para não colidir com a nota vizinha mais próxima, respeitando uma folga (gap_mm).

        ✅ Correção: quando `layer` é informado, converte gap/min em mm usando o fator congelado
        da própria layer (nm_mm2mu). Se layer=None, mantém comportamento antigo.
        """
        n = len(centers)
        if n == 0:
            return []

        if layer is not None:
            gap_map = self._mm_to_map_units_for_layer(layer, gap_mm)
            min_map = self._mm_to_map_units_for_layer(layer, min_mm)
        else:
            gap_map = self._mm_to_map_units(gap_mm)
            min_map = self._mm_to_map_units(min_mm)

        r_eff = [requested_r_map] * n
        indicador = (indicador or "arrow").lower()

        for i in range(n):
            ci = centers[i]
            if ci is None:
                r_eff[i] = max(min_map, requested_r_map)
                continue

            dmin = float("inf")
            for j in range(n):
                if i == j or centers[j] is None:
                    continue
                dx = ci.x() - centers[j].x()
                dy = ci.y() - centers[j].y()
                d = math.hypot(dx, dy)
                if d < dmin:
                    dmin = d

            if dmin < float("inf"):
                allowed_circ_R = max(0.0, 0.5 * (dmin - gap_map))
                if indicador == "square":
                    allowed = allowed_circ_R / math.sqrt(2.0)
                else:
                    allowed = allowed_circ_R
                r_eff[i] = max(min_map, min(requested_r_map, allowed))
            else:
                r_eff[i] = max(min_map, requested_r_map)

        return r_eff

    def _leader_lengths(self, lyr: QgsVectorLayer) -> tuple[float, float]:
        """
        Retorna (hlen, dlen) em unidades do mapa:
          - hlen: comprimento do trecho horizontal final (p1->p2)  [doubleSpinBoxCauda, em mm]
          - dlen: comprimento do trecho diagonal (p0->p1)          [doubleSpinBoxLinha, em mm]
        """
        ext = lyr.extent()
        if ext and not ext.isEmpty():
            w = max(1e-9, ext.width())
            h = max(1e-9, ext.height())
            base = min(w, h)
        else:
            base = 100.0

        # Horizontal (cauda) por spinner
        try:
            mm_h = float(self.doubleSpinBoxCauda.value())
        except Exception:
            mm_h = 0.0
        if mm_h > 0:
            hlen = self._mm_to_map_units(mm_h)
        else:
            hlen = 0.06 * base  # fallback

        # Diagonal por spinner (já havia no patch anterior)
        try:
            mm_d = float(self.doubleSpinBoxLinha.value())
        except Exception:
            mm_d = 0.0
        if mm_d > 0:
            dlen = self._mm_to_map_units(mm_d)
        else:
            dlen = 0.05 * base  # fallback

        return (hlen, dlen)

    def _resize_horizontal_current_layer(self, *args):
        """
        Ajusta o comprimento do 2º segmento (p1->p2) para o valor em mm do doubleSpinBoxCauda,
        apenas em líderes (polilinhas ABERTAS). Não toca nas figuras fechadas (círculo/quadrado).
        """
        lyr = self._get_selected_dim_layer()
        if not lyr:
            return

        try:
            mm = float(self.doubleSpinBoxCauda.value())
        except Exception:
            mm = 0.0
        if mm <= 0:
            return

        target = self._mm_to_map_units_for_layer(lyr, mm)
        prov = lyr.dataProvider()

        geom_changes = {}
        for f in lyr.getFeatures():
            pl = self._extract_first_polyline(f.geometry())
            # Pula figuras fechadas e líderes sem a “perninha” horizontal
            if len(pl) < 3 or self._is_closed_polyline(pl):
                continue

            p0, p1, p2 = pl[0], pl[1], pl[2]

            sgn = 1.0 if (p2.x() - p1.x()) >= 0 else -1.0
            new_p2 = QgsPointXY(p1.x() + sgn*target, p1.y())

            dx = new_p2.x() - p2.x()
            dy = new_p2.y() - p2.y()

            new_pl = [p0, p1, new_p2]
            for k in range(3, len(pl)):
                pk = pl[k]
                new_pl.append(QgsPointXY(pk.x()+dx, pk.y()+dy))

            geom_changes[f.id()] = QgsGeometry.fromPolylineXY(new_pl)
            lyr.setCustomProperty("nm_tail_mm", float(self.doubleSpinBoxCauda.value()))

        if geom_changes:
            prov.changeGeometryValues(geom_changes)
            lyr.updateExtents(); lyr.triggerRepaint()
            try: self.iface.mapCanvas().refresh()
            except Exception: 
                pass  # nosec B110

        # ✅ Só move o texto se checkBoxDeslocar estiver marcado
        try:
            move_text = bool(self.checkBoxDeslocar.isChecked())
        except Exception:
            move_text = False

        if move_text:
            self._update_label_anchors(lyr)
            self._apply_point_labeling(lyr, float(self.doubleSpinBoxTexto.value() or 10.0), lyr.labelsEnabled())

    def _resize_diagonal_current_layer(self, *args):
        """
        Ajusta o comprimento do 1º segmento (p0->p1) para o valor em mm do doubleSpinBoxLinha,
        apenas em líderes (polilinhas ABERTAS). Não toca nas figuras fechadas (círculo/quadrado).
        """
        lyr = self._get_selected_dim_layer()
        if not lyr:
            return

        try:
            mm = float(self.doubleSpinBoxLinha.value())
        except Exception:
            mm = 0.0
        if mm <= 0:
            return

        dlen_target = self._mm_to_map_units_for_layer(lyr, mm)
        prov = lyr.dataProvider()
        geom_changes = {}

        for f in lyr.getFeatures():
            pl = self._extract_first_polyline(f.geometry())
            # Pula figuras fechadas (círculo/quadrado) e inválidas
            if len(pl) < 2 or self._is_closed_polyline(pl):
                continue

            p0, p1 = pl[0], pl[1]
            vx = p1.x() - p0.x(); vy = p1.y() - p0.y()
            L = (vx*vx + vy*vy) ** 0.5
            if L < 1e-12:
                continue

            ux, uy = vx/L, vy/L
            new_p1 = QgsPointXY(p0.x() + ux*dlen_target, p0.y() + uy*dlen_target)

            dx = new_p1.x() - p1.x()
            dy = new_p1.y() - p1.y()

            new_pl = [p0, new_p1]
            for k in range(2, len(pl)):
                pk = pl[k]
                new_pl.append(QgsPointXY(pk.x()+dx, pk.y()+dy))

            geom_changes[f.id()] = QgsGeometry.fromPolylineXY(new_pl)
            lyr.setCustomProperty("nm_line_mm", float(self.doubleSpinBoxLinha.value()))

        if geom_changes:
            prov.changeGeometryValues(geom_changes)
            lyr.updateExtents(); lyr.triggerRepaint()
            try: self.iface.mapCanvas().refresh()
            except Exception: pass  # nosec B110

        # Garante o movimento do texto na Cauda
        self._update_label_anchors(lyr)
        self._apply_point_labeling(lyr, float(self.doubleSpinBoxTexto.value() or 10.0), lyr.labelsEnabled())

    def _current_mm2mu(self) -> float:
        """Fator (unidades do mapa) por milímetro na tela, no canvas atual."""
        try:
            canvas = self.iface.mapCanvas()
            dpi = canvas.logicalDpiX() or 96.0
            mup = canvas.mapUnitsPerPixel() or 1.0
            return (dpi / 25.4) * mup
        except Exception:
            return 1.0

    def _mm_to_map_units_for_layer(self, layer: QgsVectorLayer, mm: float) -> float:
        """Converte mm usando o fator congelado da camada (se houver)."""
        fac = None
        try:
            fac = float(layer.customProperty("nm_mm2mu", ""))
        except Exception:
            fac = None
        if not fac or fac <= 0:
            fac = self._current_mm2mu()
        return mm * fac

    def _load_ui_from_layer_properties(self, lyr: QgsVectorLayer):
        """
        Sincroniza a UI a partir das propriedades salvas na camada de notas.

        O que faz:
          - Lê da camada as customProperties:
              • nm_indicator  → tipo do indicador (arrow/circle/square)
              • nm_size_mm    → tamanho do indicador (mm)
              • nm_line_mm    → comprimento do 1º segmento/linha inclinada (mm)
              • nm_tail_mm    → comprimento do 2º segmento/linha horizontal (mm)
          - Atualiza os widgets correspondentes: comboBoxIndicador, doubleSpinBoxTamanho,
            doubleSpinBoxLinha e doubleSpinBoxCauda.
          - Bloqueia os sinais temporariamente para não disparar restilização/rebuild
            enquanto apenas refletimos os valores na UI.

        Parâmetros
        lyr : QgsVectorLayer
            Camada de notas atualmente selecionada.
        """
        cb   = self.comboBoxIndicador
        sp_t = self.doubleSpinBoxTamanho
        sp_d = self.doubleSpinBoxLinha
        sp_h = self.doubleSpinBoxCauda

        # Bloqueia sinais para evitar _restyle_selected_note_layer durante a sincronização
        for w in (cb, sp_t, sp_d, sp_h):
            try:
                w.blockSignals(True)  # # evita disparar valueChanged/currentIndexChanged aqui
            except Exception:
                pass  # nosec B110

        try:
            # Lê o tipo do indicador salvo na camada e posiciona o combo
            code = lyr.customProperty("nm_indicator", "arrow")  # # default: "arrow"
            idx = cb.findData(code, role=Qt.ItemDataRole.UserRole)           # # procura pelo UserRole (código)
            if idx != -1:
                cb.setCurrentIndex(idx)                         # # aplica seleção no combo

            # Tamanho do indicador (mm) → spinner
            val_t = float(lyr.customProperty("nm_size_mm", sp_t.value()))
            sp_t.setValue(val_t)                                # # atualiza spinner de tamanho

            # Comprimento da linha inclinada (mm) → spinner
            val_d = float(lyr.customProperty("nm_line_mm", sp_d.value()))
            sp_d.setValue(val_d)                                # # atualiza spinner da diagonal

            # Comprimento da linha horizontal (mm) → spinner
            val_h = float(lyr.customProperty("nm_tail_mm", sp_h.value()))
            sp_h.setValue(val_h)                                # # atualiza spinner da cauda
        except Exception:
            # Mantém a UI como estava se algo falhar, sem interromper o fluxo
            pass  # nosec B110
        finally:
            # Desbloqueia os sinais ao final para voltar ao comportamento normal
            for w in (cb, sp_t, sp_d, sp_h):
                try:
                    w.blockSignals(False)  # # reativa emissão de sinais
                except Exception:
                    pass  # nosec B110

    def _update_labels_from_field_for_selected_layer(self, *args):
        """
        Atualiza o texto das notas (campo 'nm_text') a partir do campo escolhido em
        comboBoxCampo da camada de PONTOS selecionada no comboBoxCamada.
        
        Regras:
        - Se houver um campo válido, copia seu valor para cada líder correspondente,
          formatando números para remover casas decimais desnecessárias (ex.: 2.0 -> "2"),
          usando a precisão do campo do QGIS.
        - Se não houver campo válido, limpa 'nm_text' e desliga a rotulagem.
        - Apenas feições com 'nm_role' == 1 (líderes) recebem texto; as demais ficam vazias.
        - Ao final, aplica as mudanças e atualiza a renderização.
        """
        lyr = self._get_selected_dim_layer()
        if not isinstance(lyr, QgsVectorLayer):
            return

        # Notas LIVRES não dependem de comboBoxCamada/campo: não sobrescrever nm_text
        if str(lyr.customProperty("nm_mode", "")) == "free":
            # Mantém os textos; apenas garante âncoras/estilo e rótulos ligados
            self._update_label_anchors(lyr)
            try:
                tmm = float(self.doubleSpinBoxTexto.value() or 10.0)
            except Exception:
                tmm = float(lyr.customProperty("nm_text_size_mm", 10.0))
            self._apply_point_labeling(lyr, tmm, True)
            lyr.triggerRepaint()
            try: self.iface.mapCanvas().refresh()
            except Exception: pass  # nosec B110
            return

        # Camada de origem dos valores (PONTOS) vinda do combo
        src_id = self.comboBoxCamada.currentData()
        src = QgsProject.instance().mapLayer(src_id) if src_id else None
        if not isinstance(src, QgsVectorLayer):
            return

        f_name = self.comboBoxCampo.currentText().strip() if self.comboBoxCampo.count() > 0 else ""

        # Monta mapa FID(origem)->texto formatado (quando há campo válido)
        values = {}
        field_names = {fld.name() for fld in src.fields()}  # conjunto p/ checagem rápida
        if f_name and f_name in field_names:
            # Precisão do campo no QGIS (usa como limite de casas decimais)
            prec = 6
            try:
                idxp = src.fields().indexOf(f_name)
                if idxp != -1:
                    prec = max(0, src.fields()[idxp].precision())
            except Exception:
                pass  # nosec B110

            for pf in src.getFeatures():
                try:
                    # Converte o valor com a função que remove zeros desnecessários
                    values[pf.id()] = self._fmt_label(pf[f_name], max_dec=prec)
                except Exception:
                    values[pf.id()] = ""

            # Persiste a origem do texto na camada de notas
            lyr.setCustomProperty("nm_field_name", f_name)
            lyr.setCustomProperty("nm_src_layer_id", src.id())
        else:
            # Sem campo válido: desligar texto
            values = None

        # Índices de campos na camada de notas
        flds   = lyr.fields()
        ix_text = flds.indexOf("nm_text")
        ix_role = flds.indexOf("nm_role")
        ix_src  = flds.indexOf("nm_src_fid")

        # Prepara alterações de atributos por feição
        changes = {}
        for lf in lyr.getFeatures():
            # Só líderes (nm_role == 1) recebem texto
            if ix_role != -1 and lf.attribute(ix_role) == 1:
                new_txt = ""
                if values is not None and ix_src != -1:
                    src_fid = lf.attribute(ix_src)  # FID da feição de origem
                    new_txt = values.get(src_fid, "")
                if ix_text != -1:
                    changes.setdefault(lf.id(), {})[ix_text] = new_txt
            else:
                # Figuras / outros: garantimos texto vazio
                if ix_text != -1:
                    changes.setdefault(lf.id(), {})[ix_text] = ""

        # Aplica alterações no provedor
        if changes:
            lyr.dataProvider().changeAttributeValues(changes)

        # Liga/desliga rotulagem com base na existência de um campo válido
        try:
            lbl = lyr.labeling()
            if isinstance(lbl, QgsVectorLayerSimpleLabeling):
                lyr.setLabelsEnabled(values is not None)  # habilita se houver texto de origem
        except Exception:
            pass  # nosec B110

        # Atualiza o mapa
        lyr.triggerRepaint()
        try:
            self.iface.mapCanvas().refresh()
        except Exception:
            pass  # nosec B110

    def _on_tv_selection_changed(self, selected, deselected):
        """Atualiza o ID da camada selecionada e sincroniza os controles da UI com essa camada."""
        idxs = self.treeViewCamada.selectionModel().selectedIndexes()
        if not idxs:
            self._tv_selected_layer_id = None
            return

        idx = idxs[0]
        self._tv_selected_layer_id = self._tv_model.data(idx, Qt.ItemDataRole.UserRole)

        # ► Sincroniza widgets com a camada selecionada
        try:
            self._sync_controls_from_selected_note_layer()
        except Exception:
            pass  # nosec B110

        lyr = self._get_selected_dim_layer()
        if not lyr:
            return

        # traz o tamanho salvo dessa camada para a UI (se houver) e reaplica
        try:
            tmm = float(lyr.customProperty("nm_text_size_mm", self.doubleSpinBoxTexto.value() or 10.0))
        except Exception:
            tmm = float(self.doubleSpinBoxTexto.value() or 10.0)

        # evitar realimentação em cascata
        self.doubleSpinBoxTexto.blockSignals(True)
        self.doubleSpinBoxTexto.setValue(tmm)
        self.doubleSpinBoxTexto.blockSignals(False)

        self._apply_point_labeling(lyr, tmm, True)
        self._update_push_buttons_state()

    def _sync_controls_from_selected_note_layer(self):
        """
        Lê as customProperties da camada de notas selecionada e reflete nos widgets:
          - comboBoxIndicador
          - doubleSpinBoxTamanho (indicador)
          - doubleSpinBoxLinha (diagonal) e doubleSpinBoxCauda (horizontal)
          - doubleSpinBoxTexto (tamanho do rótulo)
          - comboBoxCamada e comboBoxCampo (origem e campo do rótulo)
        """
        lyr = self._get_selected_dim_layer()
        if not lyr:
            return

        # Indicador / tamanhos gravados na camada
        indicador = str(lyr.customProperty("nm_indicator", "arrow")).lower()
        size_mm   = float(lyr.customProperty("nm_size_mm", 3.0))
        line_mm   = float(lyr.customProperty("nm_line_mm", 0.0))   # diagonal
        tail_mm   = float(lyr.customProperty("nm_tail_mm", 0.0))   # horizontal
        text_mm   = float(lyr.customProperty("nm_text_size_mm", max(1.0, float(getattr(self.doubleSpinBoxTexto, "value", lambda: 2.5)()))))

        # indicador → combo
        try:
            cb = self.comboBoxIndicador
            cb.blockSignals(True)
            i = cb.findData(indicador, role=Qt.ItemDataRole.UserRole)
            cb.setCurrentIndex(i if i >= 0 else 0)
            cb.blockSignals(False)
        except Exception:
            pass  # nosec B110

        # tamanho indicador
        try:
            sb = self.doubleSpinBoxTamanho
            sb.blockSignals(True); sb.setValue(size_mm); sb.blockSignals(False)
        except Exception:
            pass  # nosec B110

        # diagonal/horizontal (se 0.0, tenta inferir da geometria do primeiro leader)
        try:
            fac = float(lyr.customProperty("nm_mm2mu", self._current_mm2mu()))
            if (line_mm <= 0.0 or tail_mm <= 0.0):
                for f in lyr.getFeatures():
                    pl = self._extract_first_polyline(f.geometry())
                    if len(pl) >= 3 and not self._is_closed_polyline(pl):
                        # comprimentos em unidades do mapa
                        dlen_mu = math.hypot(pl[1].x()-pl[0].x(), pl[1].y()-pl[0].y())
                        hlen_mu = abs(pl[2].x()-pl[1].x())  # é horizontal
                        if line_mm <= 0.0: line_mm = dlen_mu / fac
                        if tail_mm <= 0.0: tail_mm = hlen_mu / fac
                        break
        except Exception:
            pass  # nosec B110

        try:
            sb = self.doubleSpinBoxLinha
            sb.blockSignals(True); sb.setValue(max(0.0, line_mm)); sb.blockSignals(False)
        except Exception:
            pass  # nosec B110

        try:
            sb = self.doubleSpinBoxCauda
            sb.blockSignals(True); sb.setValue(max(0.0, tail_mm)); sb.blockSignals(False)
        except Exception:
            pass  # nosec B110

        # tamanho do texto
        try:
            sb = self.doubleSpinBoxTexto
            sb.blockSignals(True); sb.setValue(max(0.1, text_mm)); sb.blockSignals(False)
        except Exception:
            pass  # nosec B110

        # quadrante salvo na camada -> rádios
        try:
            quad = str(lyr.customProperty("nm_quadrant", "NE")).upper()
            # evitar loops de sinal
            for rb in (self.radioButtonSuperiorD, self.radioButtonSuperiorE,
                       self.radioButtonInferiorD, self.radioButtonInferiorE):
                rb.blockSignals(True)
            if quad == "NW":
                self.radioButtonSuperiorE.setChecked(True)
            elif quad == "SE":
                self.radioButtonInferiorD.setChecked(True)
            elif quad == "SW":
                self.radioButtonInferiorE.setChecked(True)
            else:
                self.radioButtonSuperiorD.setChecked(True)
        finally:
            for rb in (self.radioButtonSuperiorD, self.radioButtonSuperiorE,
                       self.radioButtonInferiorD, self.radioButtonInferiorE):
                try: rb.blockSignals(False)
                except Exception: pass  # nosec B110

        # origem e campo
        try:
            src_id     = str(lyr.customProperty("nm_src_layer_id", ""))
            field_name = str(lyr.customProperty("nm_field_name", "")).strip()

            # seleciona a camada de origem no comboBoxCamada (pra popular os campos)
            if src_id:
                i = self.comboBoxCamada.findData(src_id)
                if i >= 0:
                    self.comboBoxCamada.blockSignals(True)
                    self.comboBoxCamada.setCurrentIndex(i)
                    self.comboBoxCamada.blockSignals(False)
                    # atualiza campos e seleciona o campo configurado
                    self._refresh_comboBoxCampo()
                    if field_name:
                        j = self.comboBoxCampo.findText(field_name)
                        if j >= 0:
                            self.comboBoxCampo.blockSignals(True)
                            self.comboBoxCampo.setCurrentIndex(j)
                            self.comboBoxCampo.blockSignals(False)
        except Exception:
            pass  # nosec B110

    def _update_label_anchors(self, layer: QgsVectorLayer):
        """
        Recalcula nm_lblx/nm_lbly = meio do segmento horizontal (p1->p2) para todos os líderes.
        """
        if not isinstance(layer, QgsVectorLayer):
            return

        flds   = layer.fields()
        ix_role = flds.indexOf("nm_role")
        ix_lblx = flds.indexOf("nm_lblx")
        ix_lbly = flds.indexOf("nm_lbly")
        if ix_role < 0 or ix_lblx < 0 or ix_lbly < 0:
            return

        changes = {}
        for f in layer.getFeatures():
            try:
                if int(f.attribute(ix_role) or 0) != 1:
                    continue
            except Exception:  # nosec B112
                continue

            pl = self._extract_first_polyline(f.geometry())
            if len(pl) < 3:
                continue  # líder esperado: p0, p1, p2
            p1, p2 = pl[1], pl[2]
            mx = 0.5 * (p1.x() + p2.x())
            my = 0.5 * (p1.y() + p2.y())
            changes[f.id()] = {ix_lblx: mx, ix_lbly: my}

        if changes:
            layer.dataProvider().changeAttributeValues(changes)
            layer.triggerRepaint()
            try:
                self.iface.mapCanvas().refresh()
            except Exception:
                pass  # nosec B110

    def _apply_point_labeling(self, layer: QgsVectorLayer, text_mm: float, enable: bool = True):
        """
        Rotula a camada por 'nm_text' ancorando no meio do segmento horizontal (nm_lblx/nm_lbly),
        com o texto ACIMA da linha. Compatível com QGIS 3.36 (sem setFilterExpression).
        """
        if not isinstance(layer, QgsVectorLayer):
            return

        # guarda o tamanho na camada para sincronizar a UI depois
        try:
            layer.setCustomProperty("nm_text_size_mm", float(text_mm))
        except Exception:
            pass  # nosec B110

        # formato do texto
        fmt = QgsTextFormat()
        fmt.setSize(text_mm)
        fmt.setSizeUnit(QgsUnitTypes.RenderUnit.RenderMillimeters)

        # Cor do texto a partir da propriedade da camada (padrão preto)
        try:
            rgba = str(layer.customProperty("nm_text_color", "0,0,0,255"))
            r, g, b, a = [int(x) for x in rgba.split(",")]
            fmt.setColor(QColor(r, g, b, a))
        except Exception:
            pass  # nosec B110

        buf = QgsTextBufferSettings()
        buf.setEnabled(True)
        buf.setSize(0.4)
        buf.setSizeUnit(QgsUnitTypes.RenderUnit.RenderMillimeters)
        buf.setColor(QColor(255, 255, 255))
        fmt.setBuffer(buf)

        # configuração PAL
        pal = QgsPalLayerSettings()
        pal.fieldName = "nm_text"                           # o texto vem do campo nm_text
        # placement do rótulo (API nova ≥ 3.34 usa Qgis.LabelPlacement)
        try:
            pal.placement = Qgis.LabelPlacement.OverPoint
        except Exception:
            placement_enum = getattr(QgsPalLayerSettings, "Placement", QgsPalLayerSettings)

            pal.placement = getattr(placement_enum, "OverPoint", placement_enum.AroundPoint)
        pal.setFormat(fmt)

        # âncora X/Y vinda de campos
        dd = pal.dataDefinedProperties()
        dd.setProperty(QgsPalLayerSettings.Property.PositionX, QgsProperty.fromExpression('"nm_lblx"'))
        dd.setProperty(QgsPalLayerSettings.Property.PositionY, QgsProperty.fromExpression('"nm_lbly"'))

        # desloca o texto para cima/baixo conforme o quadrante (offset em mm)
        quad = str(layer.customProperty("nm_quadrant", "NE")).upper()
        sign_y = 1.0 if quad in ("NE", "NW") else -1.0

        pal.offsetUnits = QgsUnitTypes.RenderUnit.RenderMillimeters
        pal.xOffset = 0.0
        pal.yOffset = sign_y * max(0.5, text_mm * 0.35)

        # Tentar filtrar via propriedade data-defined "Show" (compatível e simples)
        used_dd_show = False
        try:
            dd.setProperty(QgsPalLayerSettings.Property.Show, QgsProperty.fromExpression('coalesce("nm_role",0)=1'))
            used_dd_show = True
        except Exception:
            used_dd_show = False

        pal.setDataDefinedProperties(dd)

        # Aplicar rotulagem
        if used_dd_show:
            # Um único estilo com "Show" controlando a visibilidade por feição
            layer.setLabeling(QgsVectorLayerSimpleLabeling(pal))
        else:
            # Fallback: regra única com filtro (para versões sem DD 'Show')
            root = QgsRuleBasedLabeling.Rule(QgsPalLayerSettings())  # raiz vazia
            rule = QgsRuleBasedLabeling.Rule(pal)
            rule.setFilterExpression('coalesce("nm_role",0)=1')      # só líderes rotulam
            root.appendChild(rule)
            layer.setLabeling(QgsRuleBasedLabeling(root))

        layer.setLabelsEnabled(enable)
        layer.triggerRepaint()
        try:
            self.iface.mapCanvas().refresh()
        except Exception:
            pass  # nosec B110

    def _on_pick_label_color_for_layer(self):
        """Escolhe e aplica a cor do TEXTO (labels) da camada de notas selecionada."""
        lyr = self._get_selected_dim_layer()
        if not isinstance(lyr, QgsVectorLayer):
            self.mostrar_mensagem(self.tr("Selecione uma camada de notas no painel."), "Aviso")
            return

        # cor inicial: lê da camada (se já houver) ou usa preto
        init = QColor("black")
        try:
            rgba = str(lyr.customProperty("nm_text_color", "0,0,0,255"))
            parts = [int(p) for p in rgba.split(",")]
            if len(parts) == 4:
                init = QColor(parts[0], parts[1], parts[2], parts[3])
        except Exception:
            pass  # nosec B110

        color = QColorDialog.getColor(init, self, self.tr("Escolha a cor do texto"))
        if not color.isValid():
            return

        # salva na camada e reaplica a rotulagem com o mesmo tamanho atual
        lyr.setCustomProperty("nm_text_color", f"{color.red()},{color.green()},{color.blue()},{color.alpha()}")

        try:
            text_mm = float(lyr.customProperty("nm_text_size_mm", self.doubleSpinBoxTexto.value() or 10.0))
        except Exception:
            text_mm = float(self.doubleSpinBoxTexto.value() or 10.0)

        self._apply_point_labeling(lyr, text_mm, lyr.labelsEnabled())
        lyr.triggerRepaint()
        try:
            self.iface.mapCanvas().refresh()
        except Exception:
            pass  # nosec B110

    def _apply_indicator_style(self, layer: QgsVectorLayer, indicador: str, size_mm: float):
        """
        Aplica o estilo do layer conforme o indicador,
        usando a cor salva em nm_line_color (padrão: preto).
        - arrow: triângulo no primeiro vértice com mesma cor da linha
        - circle/square: só linha (as figuras são geometrias, usam a mesma cor de stroke)
        """
        if not isinstance(layer, QgsVectorLayer):
            return

        indicador = (indicador or "arrow").lower()

        # Cor da linha/indicador a partir da camada (persistente)
        try:
            rgba = str(layer.customProperty("nm_line_color", "0,0,0,255"))
            r, g, b, a = [int(x) for x in rgba.split(",")]
        except Exception:
            r, g, b, a = (0, 0, 0, 255)

        line_sym = QgsLineSymbol.createSimple({
            "line_color": f"{r},{g},{b},{a}",
            "line_width": "0.40",
            "line_width_unit": "MM",
            "capstyle": "flat",
            "joinstyle": "miter"})

        if indicador == "arrow":
            head = QgsMarkerSymbol.createSimple({
                "name": "triangle",
                "color": f"{r},{g},{b},{a}",
                "outline_style": "no",
                "size": f"{max(0.1, float(size_mm)):.2f}",
                "size_unit": "MM",
                # Deixa o triângulo "apontando" para a direita no sistema local
                # (0° = leste). A rotação ao longo da linha virá do MarkerLine.
                "angle": "-90"})

            ml = QgsMarkerLineSymbolLayer()

            # 1) Posicionar no PRIMEIRO vértice
            try:
                ml.setPlacement(QgsTemplatedLineSymbolLayerBase.Placement.FirstVertex)
            except Exception:
                try:
                    ml.setPlacement(QgsMarkerLineSymbolLayer.Placement.Interval)
                except Exception:
                    ml.setPlacement(1)
                ml.setInterval(1e12)

            # 2) Rotação automática ao longo do 1º segmento
            try:
                ml.setRotateSymbols(True)
            except Exception:
                # Fallback para versões sem rotateSymbols
                dd_angle = ("degrees(azimuth(geometry_point_n($geometry, 1), "
                            "geometry_point_n($geometry, 2)))")
                try:
                    sl0 = head.symbolLayer(0)
                    if sl0:
                        sl0.setDataDefinedProperty(QgsSymbolLayer.Property.PropertyAngle, QgsProperty.fromExpression(dd_angle))
                except Exception:
                    pass  # nosec B110

            # 3) ► ANCORAGEM NO ÁPICE: Right + Center (sem recuo)
            try:
                sl0 = head.symbolLayer(0)
                if sl0 is not None:
                    # APIs disponíveis no QGIS 3.30+ (aprox.)
                    sl0.setHorizontalAnchorPoint(Qgis.MarkerHorizontalAnchor.Right)
                    sl0.setVerticalAnchorPoint(Qgis.MarkerVerticalAnchor.Center)
            except Exception:
                # Fallback para versões sem âncoras:
                # recua centro até o ápice (~metade do tamanho em mm)
                try:
                    ml.setOffsetAlongLineUnit(QgsUnitTypes.RenderUnit.RenderMillimeters)
                    ml.setOffsetAlongLine(float(size_mm) * 0.5)
                except Exception:
                    try:
                        ml.setDataDefinedProperty(QgsSymbolLayer.Property.PropertyOffsetAlongLine, QgsProperty.fromExpression(f"{-(float(size_mm)*0.5)}"))
                    except Exception:
                        pass  # nosec B110
            else:
                # Com âncora no ápice, NÃO recuar: a ponta estará exatamente no vértice
                try:
                    ml.setOffsetAlongLineUnit(QgsUnitTypes.RenderUnit.RenderMillimeters)
                    ml.setOffsetAlongLine(0.0)
                except Exception:
                    try:
                        ml.setDataDefinedProperty(QgsSymbolLayer.Property.PropertyOffsetAlongLine, QgsProperty.fromExpression("0"))
                    except Exception:
                        pass  # nosec B110

            ml.setSubSymbol(head)
            line_sym.appendSymbolLayer(ml)

        layer.setRenderer(QgsSingleSymbolRenderer(line_sym))
        layer.triggerRepaint()
        try:
            self.iface.mapCanvas().refresh()
        except Exception:
            pass  # nosec B110

    def _on_pick_line_color_for_layer(self):
        """Escolhe e aplica a cor da LINHA e do INDICADOR da camada de notas selecionada."""
        lyr = self._get_selected_dim_layer()
        if not isinstance(lyr, QgsVectorLayer):
            self.mostrar_mensagem(self.tr("Selecione uma camada de notas no painel."), "Aviso")
            return

        # cor inicial: usa a salva em nm_line_color (ou lê do símbolo, se não houver)
        init = QColor("black")
        try:
            rgba = str(lyr.customProperty("nm_line_color", ""))
            if rgba:
                r, g, b, a = [int(x) for x in rgba.split(",")]
                init = QColor(r, g, b, a)
            else:
                # tenta derivar do símbolo atual
                sym = lyr.renderer().symbol() if lyr.renderer() else None
                if sym and sym.symbolLayerCount() > 0:
                    sll0 = sym.symbolLayer(0)
                    if hasattr(sll0, "color"):
                        init = sll0.color()
                    elif hasattr(sll0, "outlineColor"):
                        init = sll0.outlineColor()
        except Exception:
            pass  # nosec B110

        color = QColorDialog.getColor(init, self, self.tr("Escolha a cor da linha/indicador"))
        if not color.isValid():
            return

        # persiste na camada
        lyr.setCustomProperty("nm_line_color", f"{color.red()},{color.green()},{color.blue()},{color.alpha()}")

        # reaplica o estilo do indicador usando a cor persistida
        try:
            indicador = str(lyr.customProperty("nm_indicator", "arrow")).lower()
        except Exception:
            indicador = "arrow"
        try:
            size_mm = float(lyr.customProperty("nm_size_mm", self.doubleSpinBoxTamanho.value() or 3.0))
        except Exception:
            size_mm = float(self.doubleSpinBoxTamanho.value() or 3.0)

        self._apply_indicator_style(lyr, indicador, size_mm)

        # atualiza a cor do item no tree
        try:
            self._sync_tree_item_color(lyr.id())
        except Exception:
            pass  # nosec B110

        lyr.triggerRepaint()
        try:
            self.iface.mapCanvas().refresh()
        except Exception:
            pass  # nosec B110

    def _current_quadrant_from_ui(self) -> str:
        """
        Lê os radio buttons e retorna 'NE' (sup.dir), 'NW' (sup.esq),
        'SE' (inf.dir) ou 'SW' (inf.esq). Padrão = NE.
        """
        try:
            if self.radioButtonSuperiorE.isChecked():
                return "NW"
            if self.radioButtonInferiorD.isChecked():
                return "SE"
            if self.radioButtonInferiorE.isChecked():
                return "SW"
        except Exception:
            pass  # nosec B110
        return "NE"

    def _quadrant_vectors(self, quad: str) -> tuple[float,float,int,bool]:
        """
        Dado o quadrante, retorna:
          (ux, uy)  -> vetor unitário da diagonal (p0->p1)
          hsign     -> +1 (cauda pra direita) ou -1 (cauda pra esquerda)
          above     -> True = texto acima; False = texto abaixo
        """
        root2 = math.sqrt(2.0)
        quad = (quad or "NE").upper()
        if quad == "NW":
            return (-1.0/root2, +1.0/root2, -1, True)
        if quad == "SE":
            return (+1.0/root2, -1.0/root2, +1, False)
        if quad == "SW":
            return (-1.0/root2, -1.0/root2, -1, False)
        # NE
        return (+1.0/root2, +1.0/root2, +1, True)

    def _restyle_selected_note_layer(self, *args):
        """
        Reaplica o estilo da camada selecionada no tree.
        - 'arrow'  -> restaura o cabeçote via marker.
        - 'circle'/'square' -> restaura renderer e REGENERA as figuras no início do leader.
        Em todos os casos: recalcula as âncoras e reaplica o labeling para o texto acompanhar.
        """
        lyr = self._get_selected_dim_layer()
        if not lyr:
            return

        # lê UI
        try:
            size_mm = float(self.doubleSpinBoxTamanho.value())
            if size_mm <= 0:
                size_mm = 3.0
        except Exception:
            size_mm = 3.0

        _, indicador = self.get_indicador() if hasattr(self, "get_indicador") else ("", "arrow")
        indicador = (indicador or "arrow").lower()

        # aplica renderer conforme indicador
        self._apply_indicator_style(lyr, indicador, size_mm)

        lyr.setCustomProperty("nm_indicator", indicador)
        lyr.setCustomProperty("nm_size_mm", size_mm)

        # para circle/square: recria as geometrias do cabeçote (linhas) e apaga as antigas
        if indicador in ("circle", "square"):
            self._rebuild_indicator_geoms_in_layer(lyr, indicador, size_mm)
        else:
            # se voltou para 'arrow', apaga quaisquer figuras fechadas remanescentes
            self._rebuild_indicator_geoms_in_layer(lyr, "arrow", size_mm)

        # ✅ depois de mexer nas geometrias, atualize as âncoras e o labeling
        try:
            text_mm = float(self.doubleSpinBoxTexto.value())
        except Exception:
            text_mm = float(lyr.customProperty("nm_text_size_mm", 2.5))

        self._update_label_anchors(lyr)
        self._apply_point_labeling(lyr, text_mm, lyr.labelsEnabled())

        lyr.triggerRepaint()
        try:
            self.iface.mapCanvas().refresh()
        except Exception:
            pass  # nosec B110

    def _on_push_conectada(self):
        """
        Cria camada de líderes (LineString) com indicador (seta/círculo/quadrado)
        a partir da camada de PONTOS do combo. Adiciona ao grupo 'Notas'.
        """
        # 1) Camada de entrada (PONTOS)
        layer_id = self.comboBoxCamada.currentData()
        in_lyr = QgsProject.instance().mapLayer(layer_id) if layer_id else None
        if not isinstance(in_lyr, QgsVectorLayer) or QgsWkbTypes.geometryType(in_lyr.wkbType()) != QgsWkbTypes.GeometryType.PointGeometry:
            self.mostrar_mensagem(self.tr("Escolha uma camada de PONTOS no combo."), "Erro")
            return

        # 2) Feições de entrada (selecionadas ou todas)
        try:
            use_selected = bool(self.checkBoxSeleciona.isChecked() and in_lyr.selectedFeatureCount() > 0)
        except Exception:
            use_selected = in_lyr.selectedFeatureCount() > 0
        feats = list(in_lyr.getSelectedFeatures() if use_selected else in_lyr.getFeatures())
        if not feats:
            self.mostrar_mensagem(self.tr("Nenhuma feição de ponto válida encontrada."), "Aviso")
            return

        # 3) Camada de saída (LineString, CRS do input)
        crs_auth = in_lyr.crs().authid() or in_lyr.crs().toWkt()
        out_name = self._gerar_nome_unico(self.tr("Notas_Conectadas"))
        uri = f"LineString?crs={crs_auth}"
        out_lyr = QgsVectorLayer(uri, out_name, "memory")
        prov = out_lyr.dataProvider()
        if not out_lyr.isValid():
            self.mostrar_mensagem(self.tr("Falha ao criar camada de notas."), "Erro")
            return

        # 3.1) Congele o fator mm→map nesta camada (para criação e futuros resizes)
        out_lyr.setCustomProperty("nm_mm2mu", self._current_mm2mu())

        # 3.2) Campos (texto/role/origem) + ÂNCORA DO RÓTULO
        prov.addAttributes([
            QgsField("nm_text", QMetaType.Type.QString),        # texto do rótulo
            QgsField("nm_role", QMetaType.Type.Int),           # 1 = leader, 2 = figura
            QgsField("nm_src_fid", QMetaType.Type.LongLong),   # FID do ponto origem
            QgsField("nm_lblx", QMetaType.Type.Double),        # X da âncora do rótulo
            QgsField("nm_lbly", QMetaType.Type.Double)])       # Y da âncora do rótulo
        
        out_lyr.updateFields()

        # 3.3) Metadados de origem/campo
        out_lyr.setCustomProperty("nm_src_layer_id", in_lyr.id())
        field_name = self.comboBoxCampo.currentText().strip() if self.comboBoxCampo.count() > 0 else ""
        out_lyr.setCustomProperty("nm_field_name", field_name)

        # índices dos campos
        flds    = out_lyr.fields()
        ix_text = flds.indexOf("nm_text")
        ix_role = flds.indexOf("nm_role")
        ix_src  = flds.indexOf("nm_src_fid")
        ix_lblx = flds.indexOf("nm_lblx")
        ix_lbly = flds.indexOf("nm_lbly")

        # tamanho do texto (mm) vindo do doubleSpinBoxTexto
        try:
            text_mm = float(self.doubleSpinBoxTexto.value())
            if text_mm <= 0:
                text_mm = 10.0
        except Exception:
            text_mm = 10.0
        # ↳ padronizado: salvar apenas nm_text_size_mm
        out_lyr.setCustomProperty("nm_text_size_mm", text_mm)

        # 4) Leitura da UI
        try:
            size_mm = float(self.doubleSpinBoxTamanho.value())
            if size_mm <= 0:
                size_mm = 3.0
        except Exception:
            size_mm = 3.0

        _, indicador = self.get_indicador() if hasattr(self, "get_indicador") else ("", "arrow")
        indicador = (indicador or "arrow").lower()

        # 5) Comprimentos alvo (mm dos spinners → unidades do mapa)
        try:
            mm_diag = float(self.doubleSpinBoxLinha.value())
        except Exception:
            mm_diag = 0.0
        try:
            mm_tail = float(self.doubleSpinBoxCauda.value())
        except Exception:
            mm_tail = 0.0

        # fallbacks (em unidades do mapa) baseados na extensão da layer de pontos
        hlen_fb, dlen_fb = self._leader_lengths(in_lyr)

        # usa o fator CONGELADO da camada de saída
        dlen = self._mm_to_map_units_for_layer(out_lyr, mm_diag) if mm_diag > 0 else dlen_fb
        hlen = self._mm_to_map_units_for_layer(out_lyr, mm_tail) if mm_tail > 0 else hlen_fb

        quad = self._current_quadrant_from_ui()
        ux, uy, hsign, above = self._quadrant_vectors(quad)
        out_lyr.setCustomProperty("nm_quadrant", quad)

        # 5.1) Grava propriedades da CAMADA (fora do loop)
        fac = float(out_lyr.customProperty("nm_mm2mu", self._current_mm2mu()))
        out_lyr.setCustomProperty("nm_indicator", indicador)          # 'arrow'|'circle'|'square'
        out_lyr.setCustomProperty("nm_size_mm", size_mm)              # tamanho do indicador (mm)
        out_lyr.setCustomProperty("nm_line_mm", dlen / fac)           # diagonal (mm)
        out_lyr.setCustomProperty("nm_tail_mm", hlen / fac)           # horizontal (mm)

        # 5.2 Tamanhos "seguros" por feição (evita invasão na CRIAÇÃO) ---
        use_cap = indicador in ("circle", "square")
        r_eff_list = None
        if use_cap:
            # centros = os próprios pontos de entrada (onde o cabeçote é centrado)
            centers = []
            for f in feats:
                p = self._point_from_geom(f.geometry())
                centers.append(QgsPointXY(p.x(), p.y()) if p else None)

            r_req_map = self._mm_to_map_units_for_layer(out_lyr, size_mm / 2.0)
            # usa a mesma rotina já empregada na reconstrução
            r_eff_list = self._compute_safe_radii(
                centers,
                indicador,           # "circle" ou "square"
                r_req_map,
                gap_mm=1.0)           # ajuste se quiser mais/menos folga visual

        # 6) Construção das geometrias
        new_feats = []
        in_field_names = [fld.name() for fld in in_lyr.fields()]

        for idx, f in enumerate(feats):          # <<< usar enumerate
            pt_xy = self._point_from_geom(f.geometry())
            if not pt_xy:
                continue

            px, py = pt_xy.x(), pt_xy.y()

            # líder base seguindo o quadrante
            p1 = QgsPointXY(px + ux * dlen, py + uy * dlen)
            p2 = QgsPointXY(p1.x() + hsign * hlen, p1.y())
            start_pt = QgsPointXY(px, py)

            # raio/semilado em UNIDADES DO MAPA, já "clampado" se for círculo/quadrado
            if indicador in ("circle", "square"):
                r_map = r_eff_list[idx] if r_eff_list else self._mm_to_map_units_for_layer(out_lyr, size_mm / 2.0)  # <<<

                # encostar o líder na BORDA usando o r_map efetivo
                border = self._head_contact_point(QgsPointXY(px, py), p1, r_map, indicador)
                dx = border.x() - px
                dy = border.y() - py
                start_pt = border
                p1 = QgsPointXY(p1.x() + dx, p1.y() + dy)
                p2 = QgsPointXY(p2.x() + dx, p2.y() + dy)
            else:
                r_map = None  # seta não usa

            # âncora do rótulo = meio do segmento horizontal
            mx = 0.5 * (p1.x() + p2.x())
            my = 0.5 * (p1.y() + p2.y())

            # texto (se houver campo)
            txt = ""
            if field_name and field_name in in_field_names:
                try:
                    v = f[field_name]
                    # opcional: pegar precisão do campo
                    prec = 6
                    try:
                        idx = in_lyr.fields().indexOf(field_name)
                        if idx != -1:
                            prec = max(0, in_lyr.fields()[idx].precision())
                    except Exception:
                        pass  # nosec B110
                    txt = self._fmt_label(v, max_dec=prec)
                except Exception:
                    txt = ""

            # feição do líder
            feat_leader = QgsFeature()
            feat_leader.setGeometry(QgsGeometry.fromPolylineXY([start_pt, p1, p2]))
            feat_leader.setAttributes([None] * flds.count())
            feat_leader.setAttribute(ix_text, txt)
            feat_leader.setAttribute(ix_role, 1)
            feat_leader.setAttribute(ix_src, int(f.id()))
            feat_leader.setAttribute(ix_lblx, mx)
            feat_leader.setAttribute(ix_lbly, my)
            new_feats.append(feat_leader)

            # figura fechada com r_map EFETIVO
            if indicador in ("circle", "square"):
                if indicador == "circle":
                    N = 64
                    pts = [QgsPointXY(px + r_map * math.cos(2.0 * math.pi * k / N),
                                      py + r_map * math.sin(2.0 * math.pi * k / N)) for k in range(N)]
                    pts.append(pts[0])
                else:
                    a = r_map
                    pts = [
                        QgsPointXY(px - a, py - a),
                        QgsPointXY(px + a, py - a),
                        QgsPointXY(px + a, py + a),
                        QgsPointXY(px - a, py + a),
                        QgsPointXY(px - a, py - a)]
                nf = QgsFeature()
                nf.setGeometry(QgsGeometry.fromPolylineXY(pts))
                nf.setAttributes([None] * flds.count())
                nf.setAttribute(ix_role, 2)
                new_feats.append(nf)

        if not new_feats:
            self.mostrar_mensagem(self.tr("Nenhuma feição de ponto válida encontrada."), "Aviso")
            return

        prov.addFeatures(new_feats)
        out_lyr.updateExtents()

        # 7) RÓTULOS — APENAS via _apply_point_labeling (âncora nm_lblx/nm_lbly)
        enable_labels = bool(field_name and field_name in [fld.name() for fld in in_lyr.fields()])
        self._apply_point_labeling(out_lyr, text_mm, enable_labels)

        # 8) Estilo conforme indicador (seta = marker no 1º vértice; figuras = só linha)
        self._apply_indicator_style(out_lyr, indicador, size_mm)

        # 9) Adiciona ao grupo e feedback
        self._add_layer_to_group(out_lyr, getattr(self, "_group_name", self.tr("Notas")))
        try:
            self.iface.setActiveLayer(out_lyr)
            self.iface.mapCanvas().refresh()
        except Exception:
            pass  # nosec B110

        self.mostrar_mensagem(self.tr("Camada '{layer_name}' criada com {feature_count} geometrias.").format(layer_name=out_lyr.name(), feature_count=out_lyr.featureCount()), "Sucesso")

    def _fmt_label(self, v, max_dec=6) -> str:
        """
        Converte o valor do campo em string para rótulo:
        - inteiros ficam sem casa decimal (2.0 -> '2')
        - reais perdem zeros à direita (2.5000 -> '2.5')
        - valores None viram string vazia
        """
        if v is None:
            return ""
        # já numérico
        if isinstance(v, int):
            return str(v)
        if isinstance(v, float):
            if not math.isfinite(v):
                return ""
            if abs(v - round(v)) < 1e-9:
                return str(int(round(v)))
            s = f"{v:.{max_dec}f}".rstrip("0").rstrip(".")
            return s or "0"
        # tentar converter strings numéricas
        s = str(v).strip()
        try:
            fv = float(s)
            if abs(fv - round(fv)) < 1e-9:
                return str(int(round(fv)))
            return f"{fv:.{max_dec}f}".rstrip("0").rstrip(".")
        except Exception:
            # não-numérico: retorna como está
            return s

    def _figure_center_and_radius(self, pts, indicador):
        """
        Dado o anel de uma figura fechada, retorna (centro, raio_efetivo):
          - circle: raio médio até os vértices
          - square: semi-lado (metade do menor lado do bbox)
        """
        c = self._closed_polyline_center(pts)
        if not c:
            return None, None

        if (indicador or "").lower() == "square":
            xs = [p.x() for p in pts]; ys = [p.y() for p in pts]
            a = 0.5 * min(max(xs)-min(xs), max(ys)-min(ys))  # semi-lado efetivo
            return c, a
        else:
            dists = [math.hypot(p.x()-c.x(), p.y()-c.y()) for p in pts]
            r = (sum(dists) / max(1, len(dists)))            # raio médio
            return c, r

    def _reorient_current_layer(self):
        """
        Reorienta TODOS os líderes (p0→p1→p2) conforme os rádios NE/NW/SE/SW.
        - Mantém tamanhos atuais vindos da UI.
        - Para 'circle' e 'square': ancora a ponta do líder exatamente na BORDA
          da figura, usando o **raio efetivo** medido na geometria (quando existir),
          com fallback para o raio nominal (spinner) se a figura não estiver presente.
        - Atualiza a âncora dos rótulos (meio do segmento horizontal) e reaplica a
          rotulagem com deslocamento vertical apropriado ao quadrante.
        """
        lyr = self._get_selected_dim_layer()
        if not isinstance(lyr, QgsVectorLayer):
            return

        # 1) Leitura dos controles (fonte da verdade)
        try:
            _, indicador = self.get_indicador()
        except Exception:
            indicador = str(lyr.customProperty("nm_indicator", "arrow"))
        indicador = (indicador or "arrow").lower()

        try: size_mm = float(self.doubleSpinBoxTamanho.value())
        except Exception: size_mm = float(lyr.customProperty("nm_size_mm", 3.0))
        size_mm = max(0.1, size_mm)

        try: line_mm = float(self.doubleSpinBoxLinha.value())
        except Exception: line_mm = float(lyr.customProperty("nm_line_mm", 10.0))
        line_mm = max(0.0, line_mm)

        try: tail_mm = float(self.doubleSpinBoxCauda.value())
        except Exception: tail_mm = float(lyr.customProperty("nm_tail_mm", 10.0))
        tail_mm = max(0.0, tail_mm)

        try: text_mm = float(self.doubleSpinBoxTexto.value())
        except Exception: text_mm = float(lyr.customProperty("nm_text_size_mm", 2.5))
        text_mm = max(0.1, text_mm)

        quad = self._current_quadrant_from_ui()                # quadrante escolhido
        ux, uy, hsign, _ = self._quadrant_vectors(quad)        # vetores por quadrante
        lyr.setCustomProperty("nm_quadrant", quad)

        # 2) Conversões para unidades do mapa (congeladas na layer)
        dlen = self._mm_to_map_units_for_layer(lyr, line_mm)   # comprimento da diagonal
        hlen = self._mm_to_map_units_for_layer(lyr, tail_mm)   # comprimento da cauda
        r_nom = self._mm_to_map_units_for_layer(lyr, size_mm / 2.0)   # raio nominal

        prov = lyr.dataProvider()
        flds = lyr.fields()
        ix_role = flds.indexOf("nm_role")
        ix_src  = flds.indexOf("nm_src_fid")
        ix_lblx = flds.indexOf("nm_lblx")
        ix_lbly = flds.indexOf("nm_lbly")

        # Camada de origem (pontos) para fallback do centro
        src_id = str(lyr.customProperty("nm_src_layer_id", ""))
        src = QgsProject.instance().mapLayer(src_id) if src_id else None

        # 3) Indexa figuras fechadas existentes medindo o RAIO EFETIVO ---
        #     Cada item: (centro, r_eff)
        closed_figs = []
        for g in lyr.getFeatures():
            try:
                if int(g.attribute(ix_role) or 0) == 1:
                    continue  # pula líderes; queremos só as figuras (círculo/quadrado)
            except Exception:
                pass  # nosec B110
            plg = self._extract_first_polyline(g.geometry())
            if self._is_closed_polyline(plg):
                c, r_eff = self._figure_center_and_radius(plg, indicador)  # ← raio real!
                if c and r_eff:
                    closed_figs.append((c, r_eff))

        def nearest_center_with_r(ref_pt: QgsPointXY):
            """Retorna (centro, r_eff) da figura fechada mais próxima ao ref_pt; (None, None) se não houver."""
            if not closed_figs:
                return (None, None)
            best = None; best_d2 = None
            for (c, r_eff) in closed_figs:
                dx = c.x() - ref_pt.x(); dy = c.y() - ref_pt.y()
                d2 = dx*dx + dy*dy
                if best_d2 is None or d2 < best_d2:
                    best_d2 = d2; best = (c, r_eff)
            return best

        # 4) Reorienta feição a feição
        geom_changes, attr_changes = {}, {}

        for f in lyr.getFeatures():
            try:
                if int(f.attribute(ix_role) or 0) != 1:
                    continue  # só líderes
            except Exception:  # nosec B112
                continue

            pl = self._extract_first_polyline(f.geometry())
            if len(pl) < 2:
                continue

            p0 = pl[0]  # início atual do líder

            # Novos p1/p2 pelo quadrante
            p1_new = QgsPointXY(p0.x() + ux * dlen, p0.y() + uy * dlen)
            p2_new = QgsPointXY(p1_new.x() + hsign * hlen, p1_new.y())
            start_new = QgsPointXY(p0.x(), p0.y())

            # Se 'circle'/'square', ancora exatamente na BORDA
            if indicador in ("circle", "square"):
                c, r_eff = nearest_center_with_r(p0)
                if not c and isinstance(src, QgsVectorLayer) and ix_src >= 0:
                    # Fallback: usa o ponto de origem
                    try:
                        src_fid = int(f.attribute(ix_src))
                        src_feat = next(src.getFeatures(QgsFeatureRequest(src_fid)), None)
                        if src_feat:
                            c = self._point_from_geom(src_feat.geometry())
                    except Exception:
                        c = None

                use_r = r_eff if (r_eff and r_eff > 0) else r_nom   # ← prefere raio efetivo
                if c:
                    border = self._head_contact_point(c, p1_new, use_r, indicador)  # ponto de contato na borda
                    dx = border.x() - p0.x()
                    dy = border.y() - p0.y()
                    start_new = border                               # ponta do líder na borda
                    p1_new = QgsPointXY(p1_new.x() + dx, p1_new.y() + dy)
                    p2_new = QgsPointXY(p2_new.x() + dx, p2_new.y() + dy)

            # Atualiza geometria do líder (p0, p1, p2)
            new_pl = [start_new, p1_new, p2_new]
            geom_changes[f.id()] = QgsGeometry.fromPolylineXY(new_pl)

            # Reposiciona âncora do rótulo no meio de p1–p2
            if ix_lblx >= 0 and ix_lbly >= 0:
                mx = 0.5 * (p1_new.x() + p2_new.x())
                my = 0.5 * (p1_new.y() + p2_new.y())
                attr_changes[f.id()] = {ix_lblx: mx, ix_lbly: my}

        # 5) Aplica alterações e atualiza rótulos
        if geom_changes:
            prov.changeGeometryValues(geom_changes)
        if attr_changes:
            prov.changeAttributeValues(attr_changes)

        # Recalcula âncoras e reaplica rotulagem (acima/abaixo conforme quadrante)
        self._update_label_anchors(lyr)
        self._apply_point_labeling(lyr, float(self.doubleSpinBoxTexto.value() or 10.0), lyr.labelsEnabled())

        lyr.updateExtents()
        lyr.triggerRepaint()
        try:
            self.iface.mapCanvas().refresh()
        except Exception:
            pass  # nosec B110

    def _get_or_create_free_layer(self, init_from_ui: bool = False, force_new: bool = False) -> QgsVectorLayer:
        """
        Obtém ou cria a camada de Notas Livres conforme os rádios:

          - radioButtonMesma:
              reutiliza a camada coletiva 'Notas_Livres';
              se não existir, cria a primeira.

          - radioButtonIndependente:
              cria uma nova camada independente para a nota atual.

        force_new=True força criação de nova camada, usado principalmente
        para nota livre independente.
        """
        mode = self._free_layer_mode_from_ui()

        if mode == "shared" and not force_new:
            lyr = self._find_shared_free_layer()
            if isinstance(lyr, QgsVectorLayer):
                return lyr

            return self._create_free_layer(init_from_ui=init_from_ui, policy="shared")

        return self._create_free_layer(init_from_ui=init_from_ui, policy="independent")

    def _free_layer_mode_from_ui(self) -> str:
        """
        Retorna o modo de criação da Nota Livre:
          - 'shared'      -> radioButtonMesma
          - 'independent' -> radioButtonIndependente

        Fallback seguro: shared.
        """
        try:
            if hasattr(self, "radioButtonIndependente") and self.radioButtonIndependente.isChecked():
                return "independent"
        except Exception:
            pass  # nosec B110

        return "shared"

    def _iter_free_note_layers(self):
        """Itera pelas camadas de notas livres dentro do grupo Notas."""
        root = QgsProject.instance().layerTreeRoot()
        grupo = root.findGroup(getattr(self, "_group_name", self.tr("Notas")))
        if not grupo:
            return

        for node in grupo.findLayers():
            lyr = node.layer()
            if isinstance(lyr, QgsVectorLayer) and lyr.geometryType() == QgsWkbTypes.GeometryType.LineGeometry:
                if str(lyr.customProperty("nm_mode", "")) == "free":
                    yield lyr

    def _find_shared_free_layer(self) -> QgsVectorLayer | None:
        """
        Procura a camada coletiva de notas livres.

        Regra:
        - primeiro procura nm_free_policy == 'shared';
        - se encontrar camada livre antiga sem política, assume como coletiva
          para manter compatibilidade com notas já criadas antes deste ajuste.
        """
        fallback_old_free = None

        for lyr in self._iter_free_note_layers() or []:
            policy = str(lyr.customProperty("nm_free_policy", "")).strip().lower()

            if policy == "shared":
                return lyr

            # Compatibilidade com camadas antigas, criadas antes de existir nm_free_policy
            if not policy and fallback_old_free is None:
                fallback_old_free = lyr

        if fallback_old_free is not None:
            try:
                fallback_old_free.setCustomProperty("nm_free_policy", "shared")
            except Exception:
                pass  # nosec B110
            return fallback_old_free

        return None

    def _create_free_layer(self, init_from_ui: bool = False, policy: str = "shared") -> QgsVectorLayer:
        """
        Cria uma camada de Nota Livre.

        policy:
          - 'shared'      -> camada coletiva Notas_Livres
          - 'independent' -> camada individual Nota_Livre
        """
        policy = (policy or "shared").lower()
        if policy not in ("shared", "independent"):
            policy = "shared"

        crs = self.iface.mapCanvas().mapSettings().destinationCrs()
        uri = f"LineString?crs={crs.authid() or crs.toWkt()}"

        base_name = "Notas_Livres" if policy == "shared" else "Nota_Livre"
        name = self._gerar_nome_unico(base_name)

        lyr = QgsVectorLayer(uri, name, "memory")
        prov = lyr.dataProvider()
        prov.addAttributes([
            QgsField("nm_text", QMetaType.Type.QString),
            QgsField("nm_role", QMetaType.Type.Int),
            QgsField("nm_src_fid", QMetaType.Type.LongLong),
            QgsField("nm_lblx", QMetaType.Type.Double),
            QgsField("nm_lbly", QMetaType.Type.Double)
        ])
        lyr.updateFields()

        # Congela conversão e marca como livre
        lyr.setCustomProperty("nm_mm2mu", self._current_mm2mu())
        lyr.setCustomProperty("nm_mode", "free")
        lyr.setCustomProperty("nm_free_policy", policy)

        # Inicializa a partir da UI antes de adicionar ao tree
        if init_from_ui:
            try:
                _, indicador = self.get_indicador()
            except Exception:
                indicador = "arrow"

            indicador = (indicador or "arrow").lower()

            try:
                size_mm = float(self.doubleSpinBoxTamanho.value() or 3.0)
            except Exception:
                size_mm = 3.0

            try:
                line_mm = float(self.doubleSpinBoxLinha.value() or 10.0)
            except Exception:
                line_mm = 10.0

            try:
                tail_mm = float(self.doubleSpinBoxCauda.value() or 10.0)
            except Exception:
                tail_mm = 10.0

            try:
                text_mm = float(self.doubleSpinBoxTexto.value() or 10.0)
            except Exception:
                text_mm = 10.0

            quad = self._current_quadrant_from_ui()

            lyr.setCustomProperty("nm_indicator", indicador)
            lyr.setCustomProperty("nm_size_mm", size_mm)
            lyr.setCustomProperty("nm_line_mm", line_mm)
            lyr.setCustomProperty("nm_tail_mm", tail_mm)
            lyr.setCustomProperty("nm_text_size_mm", text_mm)
            lyr.setCustomProperty("nm_quadrant", quad)

            # Nota livre não depende de camada/campo de origem
            lyr.setCustomProperty("nm_src_layer_id", "")
            lyr.setCustomProperty("nm_field_name", "")

        self._add_layer_to_group(lyr, getattr(self, "_group_name", self.tr("Notas")))
        return lyr

    def _on_push_livre(self):
        """
        Abre um diálogo para o usuário digitar o texto da Nota Livre e,
        se confirmado, habilita um clique no mapa para posicionar a nota.
        """
        # se já tinha um maptool livre armado, desarma antes de armar de novo
        try:
            self._cleanup_maptool_livre()
        except Exception:
            pass  # nosec B110

        text, ok = QInputDialog.getText(self, self.tr("Nota Livre"), self.tr("Texto do rótulo:"))
        if not ok:
            return

        self._pending_free_text = str(text)

        # Define a camada alvo agora e guarda o ID.
        # Isso evita criar duas camadas no modo independente:
        # uma ao apertar o botão e outra ao clicar no mapa.
        force_new = self._free_layer_mode_from_ui() == "independent"
        lyr = self._get_or_create_free_layer(
            init_from_ui=True,
            force_new=force_new)

        try:
            self._pending_free_layer_id = lyr.id()
        except Exception:
            self._pending_free_layer_id = None

        # 3) Habilita captura de um clique no mapa
        canvas = self.iface.mapCanvas()
        self._mt_prev = canvas.mapTool()                  # # guarda a ferramenta anterior
        self._mt_livre = QgsMapToolEmitPoint(canvas)      # # ferramenta simples que emite um ponto
        self._mt_livre.canvasClicked.connect(self._finish_free_note)  # # conecta o callback
        canvas.setMapTool(self._mt_livre)
        self.mostrar_mensagem(self.tr("Clique no mapa para posicionar a Nota Livre."), "Aviso", duracao=3)

    def _finish_free_note(self, qpt, button):
        """
        Constrói a geometria da Nota Livre a partir do clique no mapa
        e aplica estilo/rotulagem conforme os controles atuais.
        """
        # desarma e restaura anterior de forma centralizada
        self._cleanup_maptool_livre()

        # Camada alvo já definida em _on_push_livre.
        # No modo independente isso é essencial para não criar camada duplicada.
        lyr = None
        try:
            if self._pending_free_layer_id:
                lyr = QgsProject.instance().mapLayer(self._pending_free_layer_id)
        except Exception:
            lyr = None

        if not isinstance(lyr, QgsVectorLayer):
            lyr = self._get_or_create_free_layer(init_from_ui=True)

        self._pending_free_layer_id = None

        prov = lyr.dataProvider()

        # Lê os controles atuais
        try: text_mm = float(self.doubleSpinBoxTexto.value() or 10.0)
        except Exception: text_mm = 10.0

        try: size_mm = float(self.doubleSpinBoxTamanho.value() or 3.0)
        except Exception: size_mm = 3.0

        try: line_mm = float(self.doubleSpinBoxLinha.value() or 10.0)
        except Exception: line_mm = 10.0

        try: tail_mm = float(self.doubleSpinBoxCauda.value() or 10.0)
        except Exception: tail_mm = 10.0

        try: _, indicador = self.get_indicador()
        except Exception: indicador = str(lyr.customProperty("nm_indicator", "arrow"))
        indicador = (indicador or "arrow").lower()

        quad = self._current_quadrant_from_ui()
        ux, uy, hsign, _ = self._quadrant_vectors(quad)

        # Persistir na layer (para que os outros botões funcionem igual)
        lyr.setCustomProperty("nm_indicator", indicador)
        lyr.setCustomProperty("nm_size_mm", size_mm)
        lyr.setCustomProperty("nm_line_mm", line_mm)
        lyr.setCustomProperty("nm_tail_mm", tail_mm)
        lyr.setCustomProperty("nm_text_size_mm", text_mm)
        lyr.setCustomProperty("nm_quadrant", quad)

        # Conversões para unidades do mapa usando o fator da própria layer
        dlen = self._mm_to_map_units_for_layer(lyr, line_mm)
        hlen = self._mm_to_map_units_for_layer(lyr, tail_mm)
        rmap = self._mm_to_map_units_for_layer(lyr, size_mm / 2.0)

        # Ponto de inserção
        px, py = qpt.x(), qpt.y()

        # p0→p1→p2 no quadrante
        p0 = QgsPointXY(px, py)
        p1 = QgsPointXY(px + ux * dlen, py + uy * dlen)
        p2 = QgsPointXY(p1.x() + hsign * hlen, p1.y())

        start_pt = QgsPointXY(p0.x(), p0.y())

        # Se for círculo/quadrado, ancora na BORDA (ponta do líder toca a figura)
        if indicador in ("circle", "square"):
            border = self._head_contact_point(QgsPointXY(px, py), p1, rmap, indicador)  # # ponto na borda
            dx = border.x() - px
            dy = border.y() - py
            start_pt = border
            p1 = QgsPointXY(p1.x() + dx, p1.y() + dy)   # # translada o líder
            p2 = QgsPointXY(p2.x() + dx, p2.y() + dy)

        # Âncora do rótulo = meio do segmento horizontal
        mx = 0.5 * (p1.x() + p2.x())
        my = 0.5 * (p1.y() + p2.y())

        # Cria o líder (role=1)
        flds = lyr.fields()
        ix_text = flds.indexOf("nm_text")
        ix_role = flds.indexOf("nm_role")
        ix_src  = flds.indexOf("nm_src_fid")
        ix_lblx = flds.indexOf("nm_lblx")
        ix_lbly = flds.indexOf("nm_lbly")

        feat_leader = QgsFeature()
        feat_leader.setGeometry(QgsGeometry.fromPolylineXY([start_pt, p1, p2]))
        feat_leader.setAttributes([None] * flds.count())
        if ix_text >= 0: feat_leader.setAttribute(ix_text, self._pending_free_text)  # # texto digitado
        if ix_role >= 0: feat_leader.setAttribute(ix_role, 1)
        if ix_src  >= 0: feat_leader.setAttribute(ix_src, None)
        if ix_lblx >= 0: feat_leader.setAttribute(ix_lblx, mx)
        if ix_lbly >= 0: feat_leader.setAttribute(ix_lbly, my)

        new_feats = [feat_leader]

        # Cria a figura (role=2) se circle/square
        if indicador in ("circle", "square"):
            if indicador == "circle":
                N = 64
                pts = [QgsPointXY(px + rmap*math.cos(2*math.pi*k/N),
                                  py + rmap*math.sin(2*math.pi*k/N)) for k in range(N)]
                pts.append(pts[0])
            else:
                a = rmap
                pts = [
                    QgsPointXY(px-a, py-a), QgsPointXY(px+a, py-a),
                    QgsPointXY(px+a, py+a), QgsPointXY(px-a, py+a),
                    QgsPointXY(px-a, py-a)]
            nf = QgsFeature()
            nf.setGeometry(QgsGeometry.fromPolylineXY(pts))
            nf.setAttributes([None] * flds.count())
            if ix_role >= 0: nf.setAttribute(ix_role, 2)
            new_feats.append(nf)

        # Grava feições
        prov.addFeatures(new_feats)
        lyr.updateExtents()

        # Rotulagem (habilitada) e estilo do indicador
        self._apply_point_labeling(lyr, text_mm, True)
        self._apply_indicator_style(lyr, indicador, size_mm)

        # Seleciona a layer no painel e dá feedback
        try:
            self.iface.setActiveLayer(lyr)
        except Exception:
            pass  # nosec B110

        lyr.triggerRepaint()

        self.iface.mapCanvas().refresh()

        self.mostrar_mensagem(self.tr("Nota Livre criada na camada '{layer_name}'.").format(layer_name=lyr.name()), "Sucesso")

    def _project_in_meters(self) -> bool:
        """
        Retorna True se o CRS do projeto usa METROS como unidade (não geográfica).
        Se falso, não garantimos comprimentos 'reais' e devemos pedir UTM.
        """
        try:
            crs = QgsProject.instance().crs()
            if crs.isGeographic():
                return False
            # QGIS 3.x: units -> QgsUnitTypes.DistanceUnit.DistanceMeters quando é métrico
            return crs.mapUnits() == QgsUnitTypes.DistanceUnit.DistanceMeters
        except Exception:
            return False

    def _layer_truecolor_rgba(self, lyr: QgsVectorLayer) -> tuple[int,int,int,int]:
        """
        Lê nm_line_color (r,g,b,a) da camada; fallback preto.
        """
        try:
            rgba = str(lyr.customProperty("nm_line_color", "0,0,0,255"))
            r, g, b, a = [int(x) for x in rgba.split(",")]
            return (r, g, b, a)
        except Exception:
            return (0, 0, 0, 255)

    def _arrow_triangle(self, p0: QgsPointXY, p1: QgsPointXY, arrow_len: float) -> list[tuple[float,float]]:
        """
        Retorna os 3 vértices (x,y) de um triângulo sólido para a seta,
        com ápice em p0 e base centrada na direção p0->p1.
        - arrow_len: comprimento ápice→base (em METROS).
        Largura da base = 0.8 * arrow_len.
        """
        vx = p1.x() - p0.x()
        vy = p1.y() - p0.y()
        L = (vx*vx + vy*vy) ** 0.5
        if L < 1e-12:
            # direção degenerada: seta apontando para +X
            ux, uy = 1.0, 0.0
        else:
            ux, uy = vx / L, vy / L

        # normal à esquerda
        nx, ny = -uy, ux

        base_len   = arrow_len
        half_width = 0.4 * arrow_len  # base = 0.8*len

        bx = p0.x() + ux * base_len
        by = p0.y() + uy * base_len

        c1x, c1y = bx + nx * half_width, by + ny * half_width
        c2x, c2y = bx - nx * half_width, by - ny * half_width

        # ordem: ápice, canto1, canto2
        return [(p0.x(), p0.y()), (c1x, c1y), (c2x, c2y)]

    def _on_push_dxf(self):
        """
        Exporta a camada de notas para DXF (ezdxf).
        - Suporta: seta, círculo e quadrado.
        - Exporta rótulos como MTEXT, sempre ACIMA da linha horizontal:
            • Inserção no meio de p1->p2 (nm_lblx/nm_lbly).
            • Ancoragem BOTTOM_CENTER + deslocamento positivo (para cima).
        - Exige projeto em METROS; em graus aborta e avisa.
        - Mostra mensagem de sucesso com botões Abrir Pasta/Arquivo.
        """
        lyr = self._get_selected_dim_layer()
        if not isinstance(lyr, QgsVectorLayer):
            self.mostrar_mensagem(self.tr("Selecione uma camada de notas."), "Aviso")
            return

        indicador = str(lyr.customProperty("nm_indicator", "arrow")).lower()
        if indicador not in ("arrow", "circle", "square"):
            indicador = "arrow"

        # 1) Precisa estar em metros (UTM)
        if not self._project_in_meters():
            self.mostrar_mensagem(self.tr("O projeto está em coordenadas geográficas (graus) ou não está em METROS. Projete seu projeto para UTM (metros) antes de exportar."), "Aviso")
            return

        # 2) Caminho do DXF
        dxf_path = self.escolher_local_para_salvar(f"{lyr.name()}.dxf", self.tr("Arquivos DXF (*.dxf)"))
        if not dxf_path:
            return

        # 3) Documento DXF (métrico)
        try:
            doc = ezdxf.new(dxfversion="R2013")
        except Exception:
            doc = ezdxf.new()
        try:
            doc.units = ezdxf.units.M
            doc.header["$INSUNITS"] = ezdxf.units.M
            doc.header["$MEASUREMENT"] = 1
        except Exception:
            pass  # nosec B110
        msp = doc.modelspace()

        def _parse_rgba(prop_str, default=(0, 0, 0, 255)):
            try:
                r, g, b, a = [int(x) for x in str(prop_str).split(",")]
                return (max(0,min(255,r)), max(0,min(255,g)), max(0,min(255,b)), max(0,min(255,a)))
            except Exception:
                return default

        # Cor linha/indicador
        r, g, b, a = _parse_rgba(lyr.customProperty("nm_line_color", "0,0,0,255"))
        dxf_layer_name = lyr.name()[:255] if lyr.name() else self.tr("Notas")
        try:
            if dxf_layer_name not in doc.layers:
                doc.layers.add(dxf_layer_name, true_color=_ezcolors.rgb2int((r, g, b)))
        except Exception:
            if dxf_layer_name not in doc.layers:
                doc.layers.add(dxf_layer_name)

        # Tamanhos (mm → m)
        try:
            size_mm = float(lyr.customProperty("nm_size_mm", self.doubleSpinBoxTamanho.value() or 3.0))
        except Exception:
            size_mm = float(self.doubleSpinBoxTamanho.value() or 3.0)
        arrow_size_m = max(0.001, self._mm_to_map_units_for_layer(lyr, size_mm))

        try:
            text_mm = float(lyr.customProperty("nm_text_size_mm", self.doubleSpinBoxTexto.value() or 10.0))
        except Exception:
            text_mm = float(self.doubleSpinBoxTexto.value() or 10.0)

        # Deslocamentos para o texto (sempre PARA CIMA da linha)
        # offset_mm idêntico ao usado no labeling; gap = offset + pequena fração da altura
        offset_mm = max(0.5, text_mm * 0.35)
        offset_m  = self._mm_to_map_units_for_layer(lyr, offset_mm)
        h_text    = max(0.001, self._mm_to_map_units_for_layer(lyr, text_mm))

        # e uma folga fixa adicional de 0.6 mm para garantir que não "pegue" na linha.
        line_width_mm = 0.40
        base_mm   = max(0.5, 0.9 * text_mm)     # sobe bem mais (90% da altura do texto)
        safety_mm = 0.5 * line_width_mm + 0.6    # meia espessura + folga extra
        gap_m     = self._mm_to_map_units_for_layer(lyr, base_mm + safety_mm)

        # Altura do texto (m) segue igual:
        h_text = max(0.001, self._mm_to_map_units_for_layer(lyr, text_mm))

        # Cor do texto
        tr, tg, tb, ta = _parse_rgba(lyr.customProperty("nm_text_color", "0,0,0,255"))
        def _is_blackish(r, g, b, tol=10): return r <= tol and g <= tol and b <= tol

        # Índices
        flds    = lyr.fields()
        ix_role = flds.indexOf("nm_role")
        ix_text = flds.indexOf("nm_text")
        ix_lblx = flds.indexOf("nm_lblx")
        ix_lbly = flds.indexOf("nm_lbly")

        num_leaders = num_heads = num_figs = num_texts = 0

        for f in lyr.getFeatures():
            pl = self._extract_first_polyline(f.geometry())
            if len(pl) < 2:
                continue

            is_closed = self._is_closed_polyline(pl)

            # Figuras (círculo/quadrado)
            if is_closed and indicador in ("circle", "square"):
                pts_xy = [(p.x(), p.y()) for p in pl]
                if len(pl) >= 2 and abs(pl[0].x()-pl[-1].x()) < 1e-12 and abs(pl[0].y()-pl[-1].y()) < 1e-12:
                    pts_xy = pts_xy[:-1]
                try:
                    msp.add_lwpolyline(
                        pts_xy,
                        dxfattribs={"layer": dxf_layer_name, "closed": True, "true_color": _ezcolors.rgb2int((r, g, b))})
                except Exception:
                    try:
                        poly = msp.add_polyline2d(pts_xy, dxfattribs={"layer": dxf_layer_name}); poly.close(True)
                    except Exception:
                        pass  # nosec B110
                num_figs += 1
                continue

            # Líder (linha inclinada + horizontal)
            if not is_closed:
                pts_xy = [(p.x(), p.y()) for p in pl]
                try:
                    msp.add_lwpolyline(
                        pts_xy,
                        dxfattribs={"layer": dxf_layer_name, "closed": False, "true_color": _ezcolors.rgb2int((r, g, b))})
                except Exception:
                    try:
                        poly = msp.add_polyline2d(pts_xy, dxfattribs={"layer": dxf_layer_name}); poly.close(False)
                    except Exception:
                        pass  # nosec B110
                num_leaders += 1

                # Cabeça (seta)
                if indicador == "arrow" and len(pl) >= 2:
                    try:
                        p0, p1 = pl[0], pl[1]
                        tri = self._arrow_triangle(p0, p1, arrow_size_m * 0.9)
                        msp.add_solid(tri, dxfattribs={"layer": dxf_layer_name, "true_color": _ezcolors.rgb2int((r, g, b))})
                        num_heads += 1
                    except Exception:
                        try:
                            tri = self._arrow_triangle(pl[0], pl[1], arrow_size_m * 0.9)
                            msp.add_lwpolyline(tri + [tri[0]], dxfattribs={"layer": dxf_layer_name, "closed": True, "true_color": _ezcolors.rgb2int((r, g, b))})
                            num_heads += 1
                        except Exception:
                            pass  # nosec B110

                # TEXTO (sempre ACIMA da linha, usando MTEXT)
                is_leader = True
                try:
                    if ix_role >= 0:
                        is_leader = int(f.attribute(ix_role) or 0) == 1
                except Exception:
                    is_leader = True

                if is_leader and ix_text >= 0:
                    try:
                        label_txt = f.attribute(ix_text)
                        label_txt = "" if label_txt is None else str(label_txt)
                    except Exception:
                        label_txt = ""

                    if label_txt.strip():
                        # Âncora (meio p1-p2) ou fallback
                        try:
                            x0 = float(f.attribute(ix_lblx)) if ix_lblx >= 0 else None
                            y0 = float(f.attribute(ix_lbly)) if ix_lbly >= 0 else None
                        except Exception:
                            x0, y0 = None, None
                        if x0 is None or y0 is None:
                            if len(pl) >= 3:
                                p1, p2 = pl[1], pl[2]
                                x0 = 0.5 * (p1.x() + p2.x()); y0 = 0.5 * (p1.y() + p2.y())
                            else:
                                p_last = pl[-1]; x0, y0 = p_last.x(), p_last.y()

                        # Inserção SEMPRE acima: ancoragem BOTTOM_CENTER e y_ins = y0 + gap
                        x_ins = x0
                        y_ins = y0 + gap_m

                        mtxt = msp.add_mtext(
                            label_txt,
                            dxfattribs={"layer": dxf_layer_name, "char_height": h_text})
                        mtxt.set_location((x_ins, y_ins))
                        try:
                            mtxt.dxf.attachment_point = TextEntityAlignment.BOTTOM_CENTER
                        except Exception:
                            pass  # nosec B110

                        # Cor do texto (preto → 7 white/black; outras cores → true_color)
                        try:
                            if _is_blackish(tr, tg, tb):
                                mtxt.dxf.color = 7
                                if hasattr(mtxt.dxf, "true_color"):
                                    mtxt.dxf.discard("true_color")
                            else:
                                mtxt.dxf.color = 256
                                mtxt.dxf.true_color = _ezcolors.rgb2int((tr, tg, tb))
                        except Exception:
                            pass  # nosec B110

                        num_texts += 1

        # Salva DXF
        try:
            doc.saveas(dxf_path)
        except Exception as e:
            self.mostrar_mensagem(self.tr("Falha ao salvar DXF: {error}").format(error=str(e)), "Erro")
            return

        # Mensagem com botões (Abrir Pasta / Abrir Arquivo)
        base = self.tr("Exportados {num_leaders} líder(es)").format(num_leaders=num_leaders)
        if indicador == "arrow":
            base += self.tr(", {num_heads} cabeça(s) de seta").format(num_heads=num_heads)
        else:
            figura = self.tr("círculo") if indicador == "circle" else self.tr("quadrado")
            base += self.tr(", {num_figs} figura(s) ({figura})").format(num_figs=num_figs, figura=figura)
        base += self.tr(" e {num_texts} texto(s) para DXF.").format(num_texts=num_texts)
        self.mostrar_mensagem(base, "Sucesso", caminho_pasta=os.path.dirname(dxf_path), caminho_arquivo=dxf_path)

    def _update_push_buttons_state(self):
        """
        Habilita/Desabilita botões conforme o estado atual da UI:
          - Conectada: habilita se houver ao menos UM item no comboBoxCamada.
          - DXF: habilita se houver camada de notas selecionada no treeViewCamada.
        """
        try:
            # Conectada -> só habilita se o combo tiver camadas (seu populate coloca apenas camadas de PONTOS)
            has_point_layers = self.comboBoxCamada.count() > 0
            if hasattr(self, "pushButtonConectada") and self.pushButtonConectada:
                self.pushButtonConectada.setEnabled(has_point_layers)
        except Exception:
            pass  # nosec B110

        try:
            # DXF -> só habilita se houver uma camada de notas selecionada no tree
            has_selected_note_layer = self._get_selected_dim_layer() is not None
            if hasattr(self, "pushButtonDXF") and self.pushButtonDXF:
                self.pushButtonDXF.setEnabled(has_selected_note_layer)
        except Exception:
            pass  # nosec B110

class TreeDeleteButtonDelegate(QStyledItemDelegate):
    def __init__(self, parent=None):
        super().__init__(parent)
        self.parent = parent  # diálogo (tem self.iface)

    def paint(self, painter, option, index):
        """Desenha cada item do treeViewCamada com fundo customizado, texto em negrito e botão 'X' para remover a camada."""
        # pinta normal para linhas inválidas
        if not index.isValid():
            return super().paint(painter, option, index)

        # linha “header” não é um item: no nosso caso usamos header do QTreeView,
        # então todos os índices são itens reais. Vamos customizar tudo.

        # Fundo
        if option.state & QStyle.StateFlag.State_Selected:
            painter.fillRect(option.rect, option.palette.highlight())
        elif option.state & QStyle.StateFlag.State_MouseOver:
            painter.fillRect(option.rect, QColor("#E8F4FF"))
        else:
            painter.fillRect(option.rect, option.palette.base())

        # Layout (desenha “X” + texto)
        rect = option.rect
        icon_size = 11
        icon_margin = 6
        icon_rect = QRect(rect.left() + icon_margin,
                          rect.top() + (rect.height() - icon_size) // 2,
                          icon_size, icon_size)
        text_rect = QRect(icon_rect.right() + icon_margin,
                          rect.top(),
                          rect.width() - icon_size - 3*icon_margin,
                          rect.height())

        # Botão X
        painter.save()
        painter.setRenderHint(QPainter.RenderHint.Antialiasing)
        painter.setPen(QPen(QColor(0, 0, 255), 1))
        painter.setBrush(QBrush(QColor(255, 0, 0, 200)))
        painter.drawRoundedRect(icon_rect, 2, 2)
        painter.setPen(QPen(QColor(255, 255, 255), 2))
        painter.drawLine(icon_rect.topLeft() + QPoint(3, 3), icon_rect.bottomRight() - QPoint(3, 3))
        painter.drawLine(icon_rect.topRight() + QPoint(-3, 3), icon_rect.bottomLeft() + QPoint(3, -3))
        painter.restore()

        # Texto (em negrito) — respeita 
        painter.save()
        text = index.data(Qt.ItemDataRole.DisplayRole)

        # tenta pegar a cor do item (setForeground)
        brush = index.data(Qt.ItemDataRole.ForegroundRole)
        if isinstance(brush, QBrush) and brush.color().isValid():
            text_color = brush.color()
        else:
            # fallback para a paleta (selecionado x normal)
            text_color = (option.palette.highlightedText().color()
                          if option.state & QStyle.StateFlag.State_Selected
                          else option.palette.text().color())

        painter.setPen(QPen(text_color))
        font = painter.font()
        font.setBold(True)
        painter.setFont(font)
        painter.drawText(text_rect, Qt.AlignmentFlag.AlignVCenter | Qt.TextFlag.TextSingleLine, text)
        painter.restore()

    @staticmethod
    def remove_layer_and_cleanup(layer_id, group_name=None):
        """
        Remove a camada pelo ID e apaga o grupo se, após a remoção,
        ele não possuir mais nenhuma camada.
        """
        if group_name is None:
            group_name = QCoreApplication.translate("NotasManager", "Notas")

        project = QgsProject.instance()
        root = project.layerTreeRoot()

        if not layer_id:
            return

        layer = project.mapLayer(layer_id)
        if not layer:
            return

        # Remove a camada do projeto.
        # Isso também remove o nó dela da árvore de camadas do QGIS.
        project.removeMapLayer(layer_id)

        # Após remover a camada, verifica se o grupo ficou sem layers.
        group = root.findGroup(group_name)
        if group is not None:
            try:
                remaining_layers = group.findLayers()
            except Exception:
                remaining_layers = []

            if not remaining_layers:
                parent = group.parent()
                if parent is not None:
                    parent.removeChildNode(group)

    def editorEvent(self, event, model, option, index):
        """Detecta clique no botão 'X' da lista e remove a camada correspondente do projeto."""
        if event.type() == QEvent.Type.MouseButtonRelease:
            rect = option.rect
            icon_size = 12
            icon_margin = 6

            icon_rect = QRect(
                rect.left() + icon_margin,
                rect.top() + (rect.height() - icon_size) // 2,
                icon_size,
                icon_size)

            if icon_rect.contains(event.pos()):
                layer_id = index.data(Qt.ItemDataRole.UserRole)

                group_name = getattr(self.parent, "_group_name", None) or self.parent.tr("Notas")
                TreeDeleteButtonDelegate.remove_layer_and_cleanup(layer_id, group_name)

                # Limpa seleção interna se era a camada removida
                try:
                    if getattr(self.parent, "_tv_selected_layer_id", None) == layer_id:
                        self.parent._tv_selected_layer_id = None
                except Exception:
                    pass  # nosec B110

                # Atualiza o treeViewCamada e botões do plugin
                try:
                    self.parent.atualizar_treeViewCamadas()
                except Exception:
                    pass  # nosec B110

                try:
                    self.parent._update_push_buttons_state()
                except Exception:
                    pass  # nosec B110

                try:
                    self.parent.iface.mapCanvas().refresh()
                except Exception:
                    pass  # nosec B110

                return True

        return super().editorEvent(event, model, option, index)