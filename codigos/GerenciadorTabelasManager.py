from qgis.core import QgsProject, QgsMessageLog, Qgis, QgsVectorLayer, QgsWkbTypes, QgsField, QgsFields, QgsFeature, QgsGeometry, QgsCoordinateTransform
from qgis.PyQt.QtWidgets import QDialog, QTableWidgetItem, QAbstractItemView, QHeaderView, QMenu, QPushButton
from qgis.PyQt.QtGui import QKeySequence, QColor, QDesktopServices, QShortcut
from qgis.PyQt.QtCore import Qt, QSignalBlocker, QDate, QDateTime, QEvent, QCoreApplication, QUrl
from qgis.gui import QgsProjectionSelectionDialog
from qgis.PyQt import uic
import os
import re

FORM_CLASS, _ = uic.loadUiType(os.path.join(
    os.path.dirname(__file__), 'GerenciadordeTabelas.ui'))

class TabelasManager(QDialog, FORM_CLASS):
    def __init__(self, iface, plugin, parent=None):
        """Constructor."""
        super(TabelasManager, self).__init__(parent)
        # Configura a interface do usuário a partir do Designer.
        self.setupUi(self)

        self.iface = iface  # Armazena a referência da interface QGIS
        self.plugin = plugin        # Guarda a referência ao plugin

        # Altera o título da janela
        self.setWindowTitle(self.tr("Gerenciador de Tabelas"))

        self.setWindowFlags(
            self.windowFlags()
            | Qt.WindowType.Window
            | Qt.WindowType.WindowMinimizeButtonHint)

        # Cria uma seleção sobre a Camada no treeView
        self.tableWidgetAtributos.setStyleSheet("""
            QTableWidget::item:hover:!selected {
                background-color: #00ffff; /* Cor de fundo ao passar o mouse sobre itens não selecionados */}
            QTableWidget::item:selected {/* Estilo para itens selecionados, se necessário */}""")

        self.tableWidgetCampo.setStyleSheet("""
            QTableWidget::item:hover:!selected {
                background-color: #43ffba; /* Cor de fundo ao passar o mouse sobre itens não selecionados */}
            QTableWidget::item:selected {/* Estilo para itens selecionados, se necessário */}""")

        # controle interno para evitar conexões duplicadas
        self._project_signals_connected = False
        self._connected_layer_ids = set()

        self._current_table_layer = None
        self._table_sync_guard = False

        self._select_equal_attrs_guard = False

        self.pushButtonCamadasAtributos.setEnabled(False)

        self._setup_table_widgets()

        self.lineEditPesquisar.setPlaceholderText(self.tr("Pesquisar atributo..."))
        self.lineEditPesquisar.setClearButtonEnabled(True)

        self.lineEditProjecao.setReadOnly(True)
        self.lineEditProjecao.setStyleSheet("color: #0055ff;")
        self._selected_target_crs = None

        self.pushButtonCampo.setEnabled(False)

        self.pushButtonNovaCamada.setEnabled(False)
        self.pushButtonReprojetar.setEnabled(False)
        self.pushButtonSalvarCamadaEditada.setEnabled(False)
        self.pushButtonAbrirCalculadora.setEnabled(False)
        # Conecta os sinais aos slots
        self.connect_signals()

    def tr(self, message):
        """
        Traduz textos deste diálogo.
        O contexto precisa ser estável para o Qt Linguist encontrar as traduções.
        """
        return QCoreApplication.translate("TabelasManager", message)

    def connect_signals(self):
        """Conecta sinais básicos da UI."""
        self.radioButtonLinha.toggled.connect(self.update_combo_box_item)
        self.radioButtonPoligono.toggled.connect(self.update_combo_box_item)
        self.radioButtonPonto.toggled.connect(self.update_combo_box_item)

        self.comboBoxCamada.currentIndexChanged.connect(self._on_current_layer_changed)

        self.tableWidgetCampo.itemSelectionChanged.connect(
            self._on_tablewidgetcampo_selection_changed)

        self.tableWidgetCampo.itemChanged.connect(self._on_tablewidgetcampo_item_changed)
        self.tableWidgetAtributos.itemChanged.connect(self._on_tablewidgetatributos_item_changed)

        # atalhos mais intuitivos
        self._shortcut_move_up = QShortcut(QKeySequence("Ctrl+Up"), self.tableWidgetCampo)
        self._shortcut_move_down = QShortcut(QKeySequence("Ctrl+Down"), self.tableWidgetCampo)

        self._shortcut_move_up.activated.connect(self._move_selected_field_up)
        self._shortcut_move_down.activated.connect(self._move_selected_field_down)

        # menu de contexto
        self.tableWidgetCampo.setContextMenuPolicy(Qt.ContextMenuPolicy.CustomContextMenu)
        self.tableWidgetCampo.customContextMenuRequested.connect(self._show_tablewidgetcampo_context_menu)

        self.pushButtonSalvarCamadaEditada.clicked.connect(self._save_edited_layer)

        self.pushButtonNovaCamada.clicked.connect(self._create_new_layer_from_ui)

        self.tableWidgetAtributos.itemSelectionChanged.connect(self._on_tablewidgetatributos_selection_changed)

        self.checkBoxSelecionaAtributos.toggled.connect(self._on_checkbox_select_equal_attributes_toggled)

        self.pushButtonCamadasAtributos.clicked.connect(self._create_layer_from_selected_attributes)

        self.lineEditPesquisar.textChanged.connect(self._filter_attributes_table)

        self.comboBoxCamada.currentIndexChanged.connect(self._update_projection_lineedit_from_layer)

        self.pushButtonReprojetar.clicked.connect(self._choose_target_projection)

        self.tableWidgetAtributos.setContextMenuPolicy(Qt.ContextMenuPolicy.CustomContextMenu)
        self.tableWidgetAtributos.customContextMenuRequested.connect(self._zoom_to_attribute_feature_by_right_click)

        self.pushButtonCampo.clicked.connect(self._create_layer_from_selected_field)

        self.pushButtonAbrirCalculadora.clicked.connect(self._open_field_calculator)

        self.pushButtonFechar.clicked.connect(self.close)

    def showEvent(self, event):
        """
        Sobrescreve o evento de exibição do diálogo para resetar os Widgets
        e conectar sinais dinâmicos do projeto/camadas.
        """
        super(TabelasManager, self).showEvent(event)

        self._connect_project_signals()
        self._connect_layer_signals()
        self._refresh_layer_ui()
        self._on_current_layer_changed()

    def closeEvent(self, event):
        """
        Em vez de destruir o diálogo, apenas oculta e limpa conexões dinâmicas.
        Também reseta a sincronização tabela <-> camada.
        """
        self._table_sync_guard = False

        if self._current_table_layer is not None:
            try:
                self._current_table_layer.updatedFields.disconnect(self._load_selected_layer_tables)
            except Exception:
                pass  # nosec B110

            try:
                self._current_table_layer.attributeValueChanged.disconnect(self._reload_attributes_only)
            except Exception:
                pass  # nosec B110

            try:
                self._current_table_layer.selectionChanged.disconnect(self._sync_table_selection_from_layer)
            except Exception:
                pass  # nosec B110

            try:
                self._current_table_layer.featureAdded.disconnect(
                    self._reload_tables_after_feature_change)
            except Exception:
                pass  # nosec B110

            try:
                self._current_table_layer.featureDeleted.disconnect(
                    self._reload_tables_after_feature_change)
            except Exception:
                pass  # nosec B110

            self._current_table_layer = None

        self._disconnect_project_signals()
        self._disconnect_layer_signals()

        self.hide()
        event.ignore()

    def _log_message(self, message, level=Qgis.MessageLevel.Info):
        """Opcional para visualizar erros"""
        QgsMessageLog.logMessage(message, 'Tabela', level=level)

    def mostrar_mensagem(self, texto, tipo, duracao=3, caminho_pasta=None, caminho_arquivo=None):
        """
        Exibe uma mensagem na barra de mensagens do QGIS, proporcionando feedback ao usuário baseado nas ações realizadas.
        As mensagens podem ser de erro ou de sucesso, com uma duração configurável e uma opção de abrir uma pasta.

        :param texto: Texto da mensagem a ser exibida.
        :param tipo: Tipo da mensagem ("Erro" ou "Sucesso") que determina a cor e o ícone da mensagem.
        :param duracao: Duração em segundos durante a qual a mensagem será exibida (padrão é 3 segundos).
        :param caminho_pasta: Caminho da pasta a ser aberta ao clicar no botão (padrão é None).
        :param caminho_arquivo: Caminho do arquivo a ser executado ao clicar no botão (padrão é None).
        """
        bar = self.iface.messageBar()

        if tipo == "Erro":
            bar.pushMessage("Erro", texto, level=Qgis.MessageLevel.Critical, duration=duracao)

        elif tipo == "Sucesso":
            msg = bar.createMessage("Sucesso", texto)

            if caminho_pasta:
                botao_abrir_pasta = QPushButton(self.tr("Abrir Pasta"))
                botao_abrir_pasta.clicked.connect(
                    lambda _checked=False, caminho=caminho_pasta:
                        QDesktopServices.openUrl(
                            QUrl.fromLocalFile(
                                os.path.abspath(os.fspath(caminho)))))
                msg.layout().insertWidget(1, botao_abrir_pasta)

            if caminho_arquivo:
                botao_executar = QPushButton(self.tr("Abrir Arquivo"))
                botao_executar.clicked.connect(
                    lambda _checked=False, caminho=caminho_arquivo:
                        QDesktopServices.openUrl(
                            QUrl.fromLocalFile(
                                os.path.abspath(os.fspath(caminho)))))
                msg.layout().insertWidget(2, botao_executar)

            bar.pushWidget(msg, level=Qgis.MessageLevel.Info, duration=duracao)

        elif tipo == "Aviso":
            bar.pushMessage("Aviso", texto, level=Qgis.MessageLevel.Warning, duration=duracao)

    def populate_combo_box(self):
        """
        Avalia as camadas vetoriais do projeto, habilita/desabilita os rádios
        conforme os tipos existentes e define a seleção inicial.
        """
        project_layers = QgsProject.instance().mapLayers().values()

        line_layers = []
        polygon_layers = []
        point_layers = []

        for layer in project_layers:
            try:
                if not isinstance(layer, QgsVectorLayer):
                    continue
                if not layer.isValid():
                    continue

                geom_type = layer.geometryType()

                if geom_type == Qgis.GeometryType.Line:
                    line_layers.append(layer)
                elif geom_type == Qgis.GeometryType.Polygon:
                    polygon_layers.append(layer)
                elif geom_type == Qgis.GeometryType.Point:
                    point_layers.append(layer)

            except Exception as e:
                layer_name = layer.name() if hasattr(layer, "name") else self.tr("sem_nome")
                self._log_message(self.tr("Erro ao avaliar camada '{layer_name}': {error}").format(layer_name=layer_name, error=str(e)), Qgis.MessageLevel.Warning)

        has_lines = bool(line_layers)
        has_polygons = bool(polygon_layers)
        has_points = bool(point_layers)

        previous_selection = None
        if self.radioButtonLinha.isChecked():
            previous_selection = "linha"
        elif self.radioButtonPoligono.isChecked():
            previous_selection = "poligono"
        elif self.radioButtonPonto.isChecked():
            previous_selection = "ponto"

        blockers = [
            QSignalBlocker(self.radioButtonLinha),
            QSignalBlocker(self.radioButtonPoligono),
            QSignalBlocker(self.radioButtonPonto),
            QSignalBlocker(self.comboBoxCamada)]

        try:
            self.radioButtonLinha.setEnabled(has_lines)
            self.radioButtonPoligono.setEnabled(has_polygons)
            self.radioButtonPonto.setEnabled(has_points)

            self.radioButtonLinha.setChecked(False)
            self.radioButtonPoligono.setChecked(False)
            self.radioButtonPonto.setChecked(False)

            # tenta preservar a seleção atual, se ainda existir
            if previous_selection == "linha" and has_lines:
                self.radioButtonLinha.setChecked(True)
            elif previous_selection == "poligono" and has_polygons:
                self.radioButtonPoligono.setChecked(True)
            elif previous_selection == "ponto" and has_points:
                self.radioButtonPonto.setChecked(True)
            else:
                # regra inicial padrão
                if has_lines:
                    self.radioButtonLinha.setChecked(True)
                elif has_polygons:
                    self.radioButtonPoligono.setChecked(True)
                elif has_points:
                    self.radioButtonPonto.setChecked(True)
                else:
                    self._clear_layer_dependent_widgets()
                    self.comboBoxCamada.setEnabled(False)
                    return

            self.comboBoxCamada.setEnabled(True)

        finally:
            del blockers

        self.update_combo_box_item()
    
    def update_combo_box_item(self):
        """
        Atualiza o comboBoxCamada de acordo com o tipo geométrico selecionado
        nos radio buttons.
        """
        current_layer_id = self.comboBoxCamada.currentData()

        self.comboBoxCamada.clear()

        project_layers = QgsProject.instance().mapLayers().values()
        selected_layers = []

        for layer in project_layers:
            if not isinstance(layer, QgsVectorLayer):
                continue
            if not layer.isValid():
                continue

            geom_type = layer.geometryType()

            if self.radioButtonLinha.isChecked() and geom_type == Qgis.GeometryType.Line:
                selected_layers.append(layer)
            elif self.radioButtonPoligono.isChecked() and geom_type == Qgis.GeometryType.Polygon:
                selected_layers.append(layer)
            elif self.radioButtonPonto.isChecked() and geom_type == Qgis.GeometryType.Point:
                selected_layers.append(layer)

        selected_layers.sort(key=lambda lyr: lyr.name().lower())

        restore_index = -1
        for i, layer in enumerate(selected_layers):
            self.comboBoxCamada.addItem(layer.name(), layer.id())
            if layer.id() == current_layer_id:
                restore_index = i

        self.comboBoxCamada.setEnabled(self.comboBoxCamada.count() > 0)

        if self.comboBoxCamada.count() == 0:
            self._clear_layer_dependent_widgets()
            self.comboBoxCamada.setEnabled(False)
            return

        if restore_index >= 0:
            self.comboBoxCamada.setCurrentIndex(restore_index)
        elif self.comboBoxCamada.count() > 0:
            self.comboBoxCamada.setCurrentIndex(0)

        self._on_current_layer_changed() # Atualiza as Tabelas
        self._update_main_action_buttons_state()

    def _setup_table_widgets(self):
        """Configura visual e comportamento das tabelas de campos e atributos."""
        for table, title in (
            (self.tableWidgetCampo, self.tr("Campos")),
            (self.tableWidgetAtributos, self.tr("Atributos"))):
            table.setColumnCount(1)
            table.setHorizontalHeaderLabels([title])
            table.setRowCount(0)

            table.horizontalHeader().setStretchLastSection(True)
            table.horizontalHeader().setSectionResizeMode(
                0, QHeaderView.ResizeMode.Stretch)
            table.verticalHeader().setVisible(True)
            table.verticalHeader().setDefaultSectionSize(35)
            table.verticalHeader().setHighlightSections(True)

            table.setSelectionBehavior(
                QAbstractItemView.SelectionBehavior.SelectRows)
            table.setSelectionMode(
                QAbstractItemView.SelectionMode.SingleSelection)

            table.setAlternatingRowColors(True)
            table.setSortingEnabled(False)
            table.setWordWrap(False)

            font = table.font()
            font.setPointSize(font.pointSize() + 1)
            table.setFont(font)

        # Campos: edição pode continuar mais agressiva
        self.tableWidgetCampo.setEditTriggers(
            QAbstractItemView.EditTrigger.DoubleClicked
            | QAbstractItemView.EditTrigger.EditKeyPressed
            | QAbstractItemView.EditTrigger.SelectedClicked)

        # Atributos: melhor para Ctrl/Shift + clique
        self.tableWidgetAtributos.setEditTriggers(
            QAbstractItemView.EditTrigger.DoubleClicked
            | QAbstractItemView.EditTrigger.EditKeyPressed)

        # Reordenação controlada por código, mais estável no Qt6
        self.tableWidgetCampo.setDragEnabled(False)
        self.tableWidgetCampo.setAcceptDrops(False)
        self.tableWidgetCampo.viewport().setAcceptDrops(False)
        self.tableWidgetCampo.setDragDropMode(
            QAbstractItemView.DragDropMode.NoDragDrop)

        self.tableWidgetAtributos.setDragDropMode(
            QAbstractItemView.DragDropMode.NoDragDrop)

        # Atributos: seleção múltipla no padrão Ctrl/Shift + clique
        self.tableWidgetAtributos.setSelectionBehavior(
            QAbstractItemView.SelectionBehavior.SelectItems)
        self.tableWidgetAtributos.setSelectionMode(
            QAbstractItemView.SelectionMode.ExtendedSelection)

    def _selected_vector_layer(self):
        """Retorna a camada vetorial atualmente selecionada no combo."""
        layer_id = self.comboBoxCamada.currentData()
        if not layer_id:
            return None

        layer = QgsProject.instance().mapLayer(layer_id)
        if not isinstance(layer, QgsVectorLayer):
            return None
        if not layer.isValid():
            return None
        return layer

    def _selected_field_index(self):
        """Retorna o índice do campo atualmente selecionado em Campos."""
        row = self.tableWidgetCampo.currentRow()
        if row < 0:
            return None

        item = self.tableWidgetCampo.item(row, 0)
        if item is None:
            return None

        return item.data(Qt.ItemDataRole.UserRole)

    def _reload_attributes_only(self, *args):
        """Recarrega apenas a tabela de atributos e reaplica a seleção vinda da camada."""
        self._load_attributes_for_selected_field()

    def _format_attribute_value_for_display(self, value, field) -> str:
        """
        Formata o valor apenas para exibição na tabela de atributos.
        - NULL aparece como <NULL>
        - string vazia aparece vazia mesmo
        """
        if value is None:
            return "<NULL>"

        family = self._field_type_family(field)
        field_name = (field.name() or "").strip().lower() if field is not None else ""

        if family == "int":
            try:
                return str(int(value))
            except Exception:
                return str(value).strip()

        if family == "float":
            try:
                num = float(value)

                if field_name in {"id", "fid", "pk", "codigo", "código"} and num.is_integer():
                    return str(int(num))

                return f"{num:.15g}"
            except Exception:
                return str(value).strip()

        if family == "bool":
            return "True" if bool(value) else "False"

        return str(value).strip()

    def _validate_and_fix_attribute_item(self, item) -> bool:
        if item is None:
            return False

        current_text = (item.text() or "").strip()
        original_value = item.data(Qt.ItemDataRole.UserRole + 3)
        field = self._selected_field()
        original_display = self._format_attribute_value_for_display(original_value, field)

        # Se não houve edição real, não valida novamente
        if current_text == original_display:
            blocker = QSignalBlocker(self.tableWidgetAtributos)
            try:
                item.setText(current_text)
                item.setData(Qt.ItemDataRole.UserRole + 1, current_text)
                item.setData(Qt.ItemDataRole.UserRole + 2, current_text)
                self._apply_item_style(item)
            finally:
                del blocker
            return True

        ok, normalized, error_message = self._normalize_attribute_text_by_field(
            current_text, field)

        if not ok:
            self._restore_previous_valid_attribute_value(item)
            self.mostrar_mensagem(error_message, "Erro", duracao=2)
            return False

        blocker = QSignalBlocker(self.tableWidgetAtributos)
        try:
            item.setText(normalized)
            item.setData(Qt.ItemDataRole.UserRole + 1, normalized)
            item.setData(Qt.ItemDataRole.UserRole + 2, normalized)
            self._apply_item_style(item)
        finally:
            del blocker

        return True

    def _normalize_attribute_text_by_field(self, text: str, field):
        """
        Valida e normaliza texto digitado conforme o tipo do campo.
        Agora aceita string vazia para campos que não sejam numéricos estritos.
        """
        text = (text or "").strip()
        family = self._field_type_family(field)

        # Permite string vazia sem erro
        if text == "":
            return True, "", ""

        if family == "int":
            try:
                value = int(text)
                return True, str(value), ""
            except Exception:
                return False, None, self.tr("Este campo aceita apenas números inteiros.")

        if family == "float":
            try:
                normalized = text.replace(",", ".")
                value = float(normalized)
                return True, f"{value:.15g}", ""
            except Exception:
                return False, None, self.tr("Este campo aceita apenas números.")

        if family == "bool":
            lowered = text.lower()
            if lowered in {"true", "1", "sim", "yes"}:
                return True, "True", ""
            if lowered in {"false", "0", "não", "nao", "no"}:
                return True, "False", ""
            return False, None, self.tr("Este campo aceita apenas valores booleanos.")

        return True, text, ""

    def _apply_item_style(self, item):
        """Aplica estilo padrão aos itens das tabelas."""
        item.setTextAlignment(int(Qt.AlignmentFlag.AlignVCenter | Qt.AlignmentFlag.AlignLeft))

        # NULL exibido em cinza
        if (item.text() or "").strip() == "<NULL>":
            item.setForeground(Qt.GlobalColor.gray)
        else:
            item.setForeground(Qt.GlobalColor.black)

    def _sync_layer_selection_from_table(self):
        """
        Tabela -> camada:
        seleciona na camada exatamente as feições cujos itens estão
        selecionados na tabela de atributos.
        """
        if self._table_sync_guard:
            return

        layer = self._selected_vector_layer()
        if layer is None:
            return

        selected_fids = self._selected_attribute_feature_ids_in_table()

        self._table_sync_guard = True
        try:
            if not selected_fids:
                layer.removeSelection()
                return

            layer.selectByIds(selected_fids)

        finally:
            self._table_sync_guard = False

    def _on_geometry_filter_changed(self, *args):
        """Atualiza combo, campos e atributos ao trocar o tipo geométrico."""
        self.populate_layers()
        self._on_current_layer_changed()

    def _on_tablewidgetcampo_item_changed(self, item):
        """Valida nomes dos campos após edição."""
        if item is None:
            return
        self._validate_and_fix_field_item(item)

    def _on_tablewidgetatributos_item_changed(self, item):
        """Valida atributos conforme o tipo do campo selecionado."""
        if item is None:
            return
        self._validate_and_fix_attribute_item(item)

    def _move_selected_field_up(self):
        """Move o campo selecionado uma linha para cima."""
        table = self.tableWidgetCampo
        row = table.currentRow()

        if row <= 0:
            return

        blocker = QSignalBlocker(self.tableWidgetCampo)
        try:
            self._swap_rows_text_and_ids(self.tableWidgetCampo, row, row - 1)
            table.selectRow(row - 1)
        finally:
            del blocker

        self._load_attributes_for_selected_field()

    def _move_selected_field_down(self):
        """Move o campo selecionado uma linha para baixo."""
        table = self.tableWidgetCampo
        row = table.currentRow()

        if row < 0 or row >= table.rowCount() - 1:
            return

        blocker = QSignalBlocker(self.tableWidgetCampo)
        try:
            self._swap_rows_text_and_ids(self.tableWidgetCampo, row, row + 1)
            table.selectRow(row + 1)
        finally:
            del blocker

        self._load_attributes_for_selected_field()

    def _sanitize_field_name(self, text: str) -> str:
        text = (text or "").strip()
        text = re.sub(r"[\s\-/\\]+", "_", text)
        text = re.sub(r"[^A-Za-z0-9_]", "_", text)
        text = re.sub(r"_+", "_", text)
        text = text.strip("_")
        return text

    def _is_duplicate_field_name(self, candidate_name: str, current_item) -> bool:
        table = self.tableWidgetCampo
        candidate_fold = (candidate_name or "").casefold()

        for row in range(table.rowCount()):
            item = table.item(row, 0)
            if item is None or item is current_item:
                continue
            if (item.text() or "").strip().casefold() == candidate_fold:
                return True

        return False

    def _restore_previous_valid_field_name(self, item, fallback="campo"):
        if item is None:
            return

        previous_valid = item.data(Qt.ItemDataRole.UserRole + 2)
        if not previous_valid:
            previous_valid = fallback

        blocker = QSignalBlocker(self.tableWidgetCampo)
        try:
            item.setText(previous_valid)
            item.setData(Qt.ItemDataRole.UserRole + 1, previous_valid)
            self._apply_item_style(item)
        finally:
            del blocker

    def _validate_and_fix_field_item(self, item) -> bool:
        if item is None:
            return False

        sanitized = self._sanitize_field_name(item.text())

        if not sanitized:
            self._restore_previous_valid_field_name(item)
            self.mostrar_mensagem(self.tr("O nome do campo não pode ficar vazio."), "Erro", duracao=3)
            return False

        if sanitized[0].isdigit():
            self._restore_previous_valid_field_name(item)
            self.mostrar_mensagem(self.tr("O nome do campo não pode começar com número."), "Erro", duracao=3)
            return False

        if self._is_duplicate_field_name(sanitized, item):
            self._restore_previous_valid_field_name(item)
            self.mostrar_mensagem(self.tr("O nome de campo '{field_name}' já existe.").format(field_name=sanitized), "Erro", duracao=3)
            return False

        blocker = QSignalBlocker(self.tableWidgetCampo)
        try:
            item.setText(sanitized)
            item.setData(Qt.ItemDataRole.UserRole + 1, sanitized)
            item.setData(Qt.ItemDataRole.UserRole + 2, sanitized)
            self._apply_item_style(item)
        finally:
            del blocker

        return True

    def _selected_field(self):
        """Retorna o QgsField atualmente selecionado em Campos."""
        layer = self._selected_vector_layer()
        field_idx = self._selected_field_index()

        if layer is None or field_idx is None:
            return None

        fields = layer.fields()
        if field_idx < 0 or field_idx >= len(fields):
            return None

        return fields[field_idx]

    def _field_type_family(self, field) -> str:
        if field is None:
            return "other"

        type_name = (field.typeName() or "").strip().lower()

        if any(k in type_name for k in ("int", "integer", "smallint", "bigint", "serial")):
            return "int"

        if any(k in type_name for k in ("real", "double", "float", "numeric", "decimal")):
            return "float"

        if "bool" in type_name:
            return "bool"

        if "datetime" in type_name or "timestamp" in type_name:
            return "datetime"

        if type_name == "date" or ("date" in type_name and "time" not in type_name):
            return "date"

        if any(k in type_name for k in ("char", "text", "string", "varchar")):
            return "string"

        return "other"

    def _restore_previous_valid_attribute_value(self, item, fallback=""):
        if item is None:
            return

        previous_valid = item.data(Qt.ItemDataRole.UserRole + 2)
        if previous_valid is None:
            previous_valid = fallback

        blocker = QSignalBlocker(self.tableWidgetAtributos)
        try:
            item.setText(str(previous_valid))
            item.setData(Qt.ItemDataRole.UserRole + 1, str(previous_valid))
            self._apply_item_style(item)
        finally:
            del blocker

    def _normalize_bool_text(self, text: str):
        val = (text or "").strip().casefold()

        true_set = {"1", "true", "t", "sim", "s", "yes", "y", "verdadeiro"}
        false_set = {"0", "false", "f", "nao", "não", "n", "no", "falso"}

        if val in true_set:
            return "True"
        if val in false_set:
            return "False"
        return None

    def _build_attribute_replacement_map(self, source_layer):
        """
        Cria mapa {old_text: typed_new_value} para o campo selecionado.
        """
        field_idx = self._selected_field_index()
        if field_idx is None:
            return {}, None

        source_field = source_layer.fields()[field_idx]
        replacements = self._get_attribute_replacements()

        repl_map = {}
        for old_text, new_text in replacements:
            repl_map[old_text] = self._convert_text_to_field_value(new_text, source_field)

        return repl_map, field_idx

    def _swap_rows_text_and_ids(self, table, row_a, row_b):
        """Troca conteúdo e metadados entre duas linhas da tabela."""
        if row_a < 0 or row_b < 0:
            return
        if row_a >= table.rowCount() or row_b >= table.rowCount():
            return
        if row_a == row_b:
            return

        item_a = table.takeItem(row_a, 0)
        item_b = table.takeItem(row_b, 0)

        table.setItem(row_a, 0, item_b)
        table.setItem(row_b, 0, item_a)

        if table.item(row_a, 0):
            self._apply_item_style(table.item(row_a, 0))
        if table.item(row_b, 0):
            self._apply_item_style(table.item(row_b, 0))

    def _refresh_layer_ui(self, *args, **kwargs):
        """
        Atualiza radios, combo e reconecta sinais das camadas quando necessário.
        Aceita *args para ser usado diretamente como slot de sinais do QGIS.
        """
        self._connect_layer_signals()
        self.populate_combo_box()

    def _show_tablewidgetcampo_context_menu(self, pos):
        """Exibe menu de contexto para reordenar campos."""
        table = self.tableWidgetCampo
        if table.rowCount() == 0:
            return

        row = table.currentRow()
        if row < 0:
            item = table.itemAt(pos)
            if item is not None:
                row = item.row()
                table.selectRow(row)

        if row < 0:
            return

        menu = QMenu(table)

        action_up = menu.addAction(self.tr("Mover para cima"))
        action_down = menu.addAction(self.tr("Mover para baixo"))

        action_up.setEnabled(row > 0)
        action_down.setEnabled(row < table.rowCount() - 1)

        chosen = menu.exec(table.viewport().mapToGlobal(pos))
        if chosen == action_up:
            self._move_selected_field_up()
        elif chosen == action_down:
            self._move_selected_field_down()

    def _connect_layer_signals(self):
        """
        Conecta sinais relevantes de camadas vetoriais válidas.
        Atualmente observa mudança de nome da camada.
        """
        project_layers = QgsProject.instance().mapLayers().values()
        current_ids = set()

        for layer in project_layers:
            if not isinstance(layer, QgsVectorLayer):
                continue
            if not layer.isValid():
                continue

            layer_id = layer.id()
            current_ids.add(layer_id)

            if layer_id in self._connected_layer_ids:
                continue

            try:
                layer.nameChanged.connect(self._refresh_layer_ui)
                self._connected_layer_ids.add(layer_id)
            except Exception:
                pass  # nosec B110

        # limpa ids de camadas que saíram do projeto
        removed_ids = self._connected_layer_ids - current_ids
        if removed_ids:
            self._connected_layer_ids -= removed_ids

    def _disconnect_layer_signals(self):
        """
        Desconecta sinais das camadas atualmente no projeto.
        """
        project_layers = QgsProject.instance().mapLayers().values()

        for layer in project_layers:
            if not isinstance(layer, QgsVectorLayer):
                continue
            if not layer.isValid():
                continue

            try:
                layer.nameChanged.disconnect(self._refresh_layer_ui)
            except Exception:
                pass  # nosec B110

        self._connected_layer_ids.clear()

    def _get_field_rename_map(self):
        """
        Retorna lista de tuplas (field_idx, old_name, new_name) para campos renomeados.
        """
        renames = []

        for row in range(self.tableWidgetCampo.rowCount()):
            item = self.tableWidgetCampo.item(row, 0)
            if item is None:
                continue

            field_idx = item.data(Qt.ItemDataRole.UserRole)
            old_name = item.data(Qt.ItemDataRole.UserRole + 3)
            new_name = (item.text() or "").strip()

            if field_idx is None or not old_name or not new_name:
                continue

            if old_name != new_name:
                renames.append((field_idx, old_name, new_name))

        return renames

    def _convert_text_to_field_value(self, text: str, field):
        """
        Converte texto normalizado para o tipo Python esperado.
        """
        family = self._field_type_family(field)
        raw = (text or "").strip()

        if family == "int":
            return int(raw)

        if family == "float":
            return float(raw.replace(",", "."))

        if family == "bool":
            return raw.casefold() in {"true", "1", "sim", "verdadeiro"}

        if family == "date":
            d = QDate.fromString(raw, "yyyy-MM-dd")
            return d if d.isValid() else raw

        if family == "datetime":
            dt = QDateTime.fromString(raw, "yyyy-MM-dd HH:mm:ss")
            return dt if dt.isValid() else raw

        return raw

    def _apply_field_renames(self, layer, rename_ops):
        """
        Aplica renomeação de campos na camada.
        """
        if not rename_ops:
            return True, ""

        provider = layer.dataProvider()
        rename_map = {field_idx: new_name for field_idx, _old_name, new_name in rename_ops}

        ok = provider.renameAttributes(rename_map)
        if not ok:
            return False, self.tr("Não foi possível renomear um ou mais campos da camada.")

        layer.updateFields()
        return True, ""

    def _apply_attribute_value_replacements(self, layer, field_idx, replacements):
        """
        Aplica substituição de valores nas feições do campo selecionado.
        """
        if field_idx is None or not replacements:
            return True, ""

        field = layer.fields()[field_idx]

        repl_map = {}
        for old_text, new_text in replacements:
            repl_map[old_text] = self._convert_text_to_field_value(new_text, field)

        if not layer.isEditable():
            if not layer.startEditing():
                return False, self.tr("Não foi possível iniciar a edição da camada.")

        changed_any = False

        for feat in layer.getFeatures():
            try:
                current_value = feat[field_idx]
            except Exception:   # nosec B112
                continue

            if current_value is None:
                continue

            current_text = str(current_value).strip()
            if current_text not in repl_map:
                continue

            new_value = repl_map[current_text]
            if current_value == new_value:
                continue

            if not layer.changeAttributeValue(feat.id(), field_idx, new_value):
                return False, self.tr("Falha ao atualizar atributo na feição {feature_id}.").format(feature_id=feat.id())

            changed_any = True

        if changed_any:
            if not layer.commitChanges():
                layer.rollBack()
                return False, self.tr("Não foi possível salvar as alterações dos atributos.")

        return True, ""

    def _save_edited_layer(self):
        """
        Salva as alterações editadas na interface:
        - renomeação de campos
        - substituição de valores do campo selecionado
        """
        layer = self._selected_vector_layer()
        if layer is None:
            self.mostrar_mensagem(self.tr("Nenhuma camada válida foi selecionada."), "Erro", duracao=3)
            return

        # valida novamente antes de persistir
        for row in range(self.tableWidgetCampo.rowCount()):
            item = self.tableWidgetCampo.item(row, 0)
            if item is not None and not self._validate_and_fix_field_item(item):
                return

        for row in range(self.tableWidgetAtributos.rowCount()):
            item = self.tableWidgetAtributos.item(row, 0)
            if item is None:
                continue

            original_text = item.data(Qt.ItemDataRole.UserRole + 3)
            current_text = (item.text() or "").strip()

            # Só valida se houve alteração real
            if original_text is not None and current_text == str(original_text).strip():
                continue

            if not self._validate_and_fix_attribute_item(item):
                return

        rename_ops = self._get_field_rename_map()
        field_idx = self._selected_field_index()
        attr_replacements = self._get_attribute_replacements()

        # 1) renomear campos
        ok, error_message = self._apply_field_renames(layer, rename_ops)
        if not ok:
            self.mostrar_mensagem(error_message, "Erro", duracao=3)
            return

        # 2) atualizar atributos do campo selecionado
        ok, error_message = self._apply_attribute_value_replacements(layer, field_idx, attr_replacements)
        if not ok:
            self.mostrar_mensagem(error_message, "Erro", duracao=3)
            return

        # Atualiza referências "originais" após salvar
        self._load_selected_layer_tables()
        self._load_attributes_for_selected_field()

        self.mostrar_mensagem(self.tr("Camada editada salva com sucesso. A reordenação dos campos, por enquanto, vale apenas na interface."), "Sucesso", duracao=2)

    def _nome_unico_no_projeto(self, base_name: str) -> str:
        """
        Gera um nome único dentro do QgsProject.

        Parameters
        base_name : str
            Nome base proposto para a camada (sem sufixo numérico).

        Returns
        str
            Nome único: base_name, base_name_1, base_name_2, ...
        """
        existing = {lyr.name() for lyr in QgsProject.instance().mapLayers().values()}
        if base_name not in existing:
            return base_name

        counter = 1
        while f"{base_name}_{counter}" in existing:
            counter += 1
        return f"{base_name}_{counter}"

    def _get_ui_field_order(self):
        """
        Retorna a ordem atual da interface:
        [(old_idx, new_name), ...]
        """
        ordered = []

        for row in range(self.tableWidgetCampo.rowCount()):
            item = self.tableWidgetCampo.item(row, 0)
            if item is None:
                continue

            old_idx = item.data(Qt.ItemDataRole.UserRole)
            new_name = (item.text() or "").strip()

            if old_idx is None or not new_name:
                continue

            ordered.append((old_idx, new_name))

        return ordered

    def _get_attribute_replacements(self):
        """
        Retorna lista de substituições para o campo selecionado:
        [(old_value_text, new_value_text), ...]
        consolidando duplicados pelo valor original.
        """
        replacements_map = {}

        for row in range(self.tableWidgetAtributos.rowCount()):
            item = self.tableWidgetAtributos.item(row, 0)
            if item is None:
                continue

            old_value = item.data(Qt.ItemDataRole.UserRole + 3)
            new_value = (item.text() or "").strip()

            if old_value is None or new_value == "":
                continue

            old_text = str(old_value).strip()
            if old_text != new_value:
                replacements_map[old_text] = new_value

        return list(replacements_map.items())

    def _build_reordered_fields(self, source_layer):
        """
        Monta QgsFields na ordem da interface, preservando tipo/origem.
        """
        ordered = self._get_ui_field_order()
        source_fields = source_layer.fields()

        new_fields = QgsFields()

        for old_idx, new_name in ordered:
            src_field = source_fields[old_idx]
            new_field = QgsField(src_field)
            new_field.setName(new_name)
            new_fields.append(new_field)

        return new_fields

    def _create_reordered_memory_layer(self, source_layer):
        """
        Cria uma nova camada memory com a mesma geometria/CRS da original.
        """
        wkb_str = QgsWkbTypes.displayString(source_layer.wkbType())
        target_crs = self._effective_target_crs(source_layer)
        crs_authid = (
            target_crs.authid()
            if target_crs is not None and target_crs.isValid()
            else source_layer.crs().authid())
        uri = f"{wkb_str}?crs={crs_authid}"

        layer_name = self._nome_unico_no_projeto(f"{source_layer.name()}_editada")

        new_layer = QgsVectorLayer(uri, layer_name, "memory")
        return new_layer

    def _populate_new_layer_from_ui(self, source_layer, new_layer):
        """
        Copia feições da camada original para a nova camada,
        respeitando a ordem/nome dos campos e substituições de atributos.
        """
        ordered = self._get_ui_field_order()
        new_fields = self._build_reordered_fields(source_layer)
        repl_map, selected_field_idx = self._build_attribute_replacement_map(source_layer)

        provider = new_layer.dataProvider()
        if not provider.addAttributes(list(new_fields)):
            return False, self.tr("Não foi possível criar os campos da nova camada.")

        new_layer.updateFields()

        new_features = []

        for src_feat in source_layer.getFeatures():
            feat = QgsFeature(new_layer.fields())
            feat.setGeometry(src_feat.geometry())

            attrs = []
            for old_idx, _new_name in ordered:
                value = src_feat[old_idx]

                if old_idx == selected_field_idx and value is not None:
                    text_value = str(value).strip()
                    if text_value in repl_map:
                        value = repl_map[text_value]

                attrs.append(value)

            feat.setAttributes(attrs)
            new_features.append(feat)

        if not provider.addFeatures(new_features):
            return False, self.tr("Não foi possível copiar as feições para a nova camada.")

        new_layer.updateExtents()
        return True, ""

    def _create_new_layer_from_ui(self):
        """
        Cria uma nova camada com:
        - mesma geometria da original
        - ordem dos campos conforme UI
        - nomes dos campos conforme UI
        - atributos alterados do campo selecionado
        """
        source_layer = self._selected_vector_layer()
        if source_layer is None:
            self.mostrar_mensagem(self.tr("Nenhuma camada válida foi selecionada."), "Erro", duracao=3)
            return

        # valida antes de persistir
        for row in range(self.tableWidgetCampo.rowCount()):
            item = self.tableWidgetCampo.item(row, 0)
            if item is not None and not self._validate_and_fix_field_item(item):
                return

        for row in range(self.tableWidgetAtributos.rowCount()):
            item = self.tableWidgetAtributos.item(row, 0)
            if item is None:
                continue

            original_text = item.data(Qt.ItemDataRole.UserRole + 3)
            current_text = (item.text() or "").strip()

            # Só valida se houve alteração real
            if original_text is not None and current_text == str(original_text).strip():
                continue

            if not self._validate_and_fix_attribute_item(item):
                return

        new_layer = self._create_reordered_memory_layer(source_layer)
        if new_layer is None or not new_layer.isValid():
            self.mostrar_mensagem(self.tr("Não foi possível criar a nova camada."), "Erro", duracao=2)
            return

        ok, error_message = self._populate_new_layer_from_ui(source_layer, new_layer)
        if not ok:
            self.mostrar_mensagem(error_message, "Erro", duracao=2)
            return

        self._copy_layer_visual_style(source_layer, new_layer)

        QgsProject.instance().addMapLayer(new_layer)

        self.mostrar_mensagem(self.tr("Nova camada criada com sucesso: {layer_name}").format(layer_name=new_layer.name()), "Sucesso", duracao=2)

    def _selected_attribute_texts(self):
        """Retorna os textos atualmente selecionados na tabela de atributos."""
        values = set()

        for item in self.tableWidgetAtributos.selectedItems():
            if item is None:
                continue

            text = (item.text() or "").strip()
            if text:
                values.add(text)

        return values

    def _on_checkbox_select_equal_attributes_toggled(self, checked):
        """
        Quando marcado, expande a seleção atual para todos os atributos
        com o mesmo texto dos itens já selecionados.
        """
        if self._select_equal_attrs_guard:
            return

        if not checked:
            return

        selected_values = self._selected_attribute_texts()

        if not selected_values:
            self._select_equal_attrs_guard = True
            try:
                self.checkBoxSelecionaAtributos.setChecked(False)
            finally:
                self._select_equal_attrs_guard = False
            return

        self._select_equal_attrs_guard = True
        try:
            for row in range(self.tableWidgetAtributos.rowCount()):
                item = self.tableWidgetAtributos.item(row, 0)
                if item is None:
                    continue

                text = (item.text() or "").strip()
                if text in selected_values:
                    item.setSelected(True)
        finally:
            self._select_equal_attrs_guard = False

        self._sync_layer_selection_from_table()

    def _auto_uncheck_select_equal_attributes(self):
        """Desmarca automaticamente o checkbox sem provocar recursão."""
        if self._select_equal_attrs_guard:
            return

        if not self.checkBoxSelecionaAtributos.isChecked():
            return

        self._select_equal_attrs_guard = True
        try:
            self.checkBoxSelecionaAtributos.setChecked(False)
        finally:
            self._select_equal_attrs_guard = False

    def _uncheck_select_equal_attributes_only(self):
        """
        Desmarca o checkbox sem alterar seleção da tabela nem da camada.
        Usado em troca de camada/campo.
        """
        if self._select_equal_attrs_guard:
            return

        if not self.checkBoxSelecionaAtributos.isChecked():
            return

        self._select_equal_attrs_guard = True
        try:
            self.checkBoxSelecionaAtributos.setChecked(False)
        finally:
            self._select_equal_attrs_guard = False

    def _uncheck_select_equal_attributes_from_layer_sync(self):
        """
        Desmarca o checkbox quando a seleção vier da camada ativa do combo,
        sem limpar a seleção da tabela nem da camada.
        """
        if self._select_equal_attrs_guard:
            return

        if not self.checkBoxSelecionaAtributos.isChecked():
            return

        self._select_equal_attrs_guard = True
        try:
            self.checkBoxSelecionaAtributos.setChecked(False)
        finally:
            self._select_equal_attrs_guard = False

    def _sync_table_selection_from_layer(self, *args):
        """
        Camada -> tabela:
        marca na tabela exatamente os itens cujos FIDs estão selecionados na camada.
        Se a mudança veio de uma ação externa na camada ativa, desmarca o checkbox.
        """
        if self._table_sync_guard:
            return

        layer = self._selected_vector_layer()
        if layer is None:
            return

        # Se a sincronização veio da própria camada ativa do combo,
        # e não foi disparada pelo fluxo interno tabela -> camada,
        # desmarca o checkbox sem afetar as seleções.
        self._uncheck_select_equal_attributes_from_layer_sync()

        selected_fids = {feat.id() for feat in layer.selectedFeatures()}

        self._table_sync_guard = True
        blocker = QSignalBlocker(self.tableWidgetAtributos)
        try:
            self.tableWidgetAtributos.clearSelection()

            if not selected_fids:
                return

            for row in range(self.tableWidgetAtributos.rowCount()):
                item = self.tableWidgetAtributos.item(row, 0)
                if item is None:
                    continue

                fid = item.data(Qt.ItemDataRole.UserRole + 4)
                if fid is None:
                    continue

                try:
                    if int(fid) in selected_fids:
                        item.setSelected(True)
                except Exception:
                    pass  # nosec B110

        finally:
            del blocker
            self._table_sync_guard = False

        # mudança vinda da camada ativa do combo:
        self._uncheck_select_equal_attributes_from_layer_sync()
        self._update_select_equal_checkbox_state()
        self._update_attribute_subset_button_state()

    def _update_select_equal_checkbox_state(self):
        """
        Habilita o checkbox apenas quando houver:
        - camada válida no combo
        - ao menos um item selecionado na tabela de atributos

        Se perder essas condições, desmarca sem alterar a seleção atual.
        """
        layer = self._selected_vector_layer()
        has_layer = layer is not None
        has_selection = len(self.tableWidgetAtributos.selectedItems()) > 0

        enable_checkbox = has_layer and has_selection

        if not enable_checkbox and self.checkBoxSelecionaAtributos.isChecked():
            self._uncheck_select_equal_attributes_only()

        self.checkBoxSelecionaAtributos.setEnabled(enable_checkbox)

    def _on_tablewidgetatributos_selection_changed(self):
        """Sincroniza a seleção da tabela de atributos para a camada do QGIS."""
        if not self._select_equal_attrs_guard:
            self._auto_uncheck_select_equal_attributes()

        self._sync_layer_selection_from_table()
        self._update_select_equal_checkbox_state()
        self._update_attribute_subset_button_state()

    def _on_current_layer_changed(self, *args):
        """Atualiza tabelas e reconecta sinais da camada atualmente selecionada."""
        layer = self._selected_vector_layer()

        if layer is None:
            self._clear_layer_dependent_widgets()
            return

        self._uncheck_select_equal_attributes_only()
        self._connect_current_layer_table_signals()
        self._load_selected_layer_tables()
        self._update_select_equal_checkbox_state()
        self._update_attribute_subset_button_state()
        self._update_projection_lineedit_from_layer()
        self._update_field_subset_button_state()
        self._update_main_action_buttons_state()

    def _on_tablewidgetcampo_selection_changed(self):
        """Atualiza a lista de atributos quando o campo selecionado muda."""
        self._uncheck_select_equal_attributes_only()
        self._load_attributes_for_selected_field()
        self._update_select_equal_checkbox_state()
        self._update_attribute_subset_button_state()
        self._update_field_subset_button_state()
        self._update_main_action_buttons_state()

    def _selected_attribute_feature_ids_in_table(self):
        """
        Retorna os FIDs atualmente selecionados na tabela de atributos.
        Se houver itens repetidos, remove duplicados preservando a ordem.
        """
        fids = []

        for item in self.tableWidgetAtributos.selectedItems():
            if item is None:
                continue

            fid = item.data(Qt.ItemDataRole.UserRole + 4)
            if fid is None:
                continue

            try:
                fids.append(int(fid))
            except Exception:
                pass  # nosec B110

        return list(dict.fromkeys(fids))

    def _current_selected_feature_ids(self):
        """
        Prioriza a seleção da tabela de atributos.
        Se não houver, usa a seleção atual da camada.
        """
        table_fids = self._selected_attribute_feature_ids_in_table()
        if table_fids:
            return table_fids

        layer = self._selected_vector_layer()
        if layer is None:
            return []

        try:
            return [feat.id() for feat in layer.selectedFeatures()]
        except Exception:
            return []

    def _simplify_layer_name_part(self, text: str, max_len: int = 24) -> str:
        """
        Simplifica uma parte do nome da camada para evitar nomes enormes.
        """
        text = (text or "").strip()
        text = re.sub(r"\s+", "_", text)
        text = re.sub(r"[^A-Za-z0-9_À-ÿ]", "", text)
        text = re.sub(r"_+", "_", text).strip("_")

        if not text:
            return self.tr("Atributos")

        if len(text) <= max_len:
            return text

        parts = [p for p in text.split("_") if p]
        if len(parts) >= 2:
            compact = "_".join(parts[:2])
            if len(compact) <= max_len:
                return compact[:max_len]

        return text[:max_len].rstrip("_")

    def _build_attribute_subset_layer_name(self, source_layer, selected_fids):
        """
        Monta o nome da nova camada:
        - NomeOriginal_NomeDoAtributo
        - NomeOriginal_Atributos
        - com sufixo automático _1, _2, ...
        """
        base_layer_name = source_layer.name() if source_layer is not None else self.tr("Camada")
        field_idx = self._selected_field_index()

        if source_layer is None or field_idx is None or not selected_fids:
            return self._nome_unico_no_projeto(f"{base_layer_name}_Atributos")

        values = []
        seen = set()

        for fid in selected_fids:
            feat = source_layer.getFeature(fid)
            if not feat.isValid():
                continue

            try:
                value = feat[field_idx]
            except Exception:  # nosec B112
                continue

            if value is None:
                continue

            text = str(value).strip()
            if not text:
                continue

            folded = text.casefold()
            if folded not in seen:
                seen.add(folded)
                values.append(text)

        if len(values) == 1:
            suffix = self._simplify_layer_name_part(values[0], max_len=24)
        else:
            suffix = self.tr("Atributos")

        base_name = f"{base_layer_name}_{suffix}"

        # simplificação adicional para nomes muito longos
        if len(base_name) > 50:
            short_base = self._simplify_layer_name_part(base_layer_name, max_len=22)
            short_suffix = self._simplify_layer_name_part(suffix, max_len=20)
            base_name = f"{short_base}_{short_suffix}"

        return self._nome_unico_no_projeto(base_name)

    def _copy_layer_visual_style(self, source_layer, target_layer):
        """
        Copia configurações visuais básicas da camada original para a nova camada.
        """
        if source_layer is None or target_layer is None:
            return

        try:
            renderer = source_layer.renderer()
            if renderer is not None:
                target_layer.setRenderer(renderer.clone())
        except Exception:
            pass  # nosec B110

        try:
            target_layer.setOpacity(source_layer.opacity())
        except Exception:
            pass  # nosec B110

        try:
            target_layer.setBlendMode(source_layer.blendMode())
        except Exception:
            pass  # nosec B110

        try:
            labeling = source_layer.labeling()
            if labeling is not None:
                target_layer.setLabeling(labeling.clone())
                target_layer.setLabelsEnabled(source_layer.labelsEnabled())
        except Exception:
            pass  # nosec B110

        try:
            target_layer.triggerRepaint()
        except Exception:
            pass  # nosec B110

    def _create_feature_subset_memory_layer(self, source_layer, selected_fids):
        """
        Cria nova camada memory com a mesma geometria/CRS/campos,
        contendo apenas as feições dos FIDs informados.
        """
        if source_layer is None or not selected_fids:
            return None, self.tr("Nenhuma feição foi selecionada.")

        wkb_str = QgsWkbTypes.displayString(source_layer.wkbType())
        target_crs = self._effective_target_crs(source_layer)
        crs_authid = (
            target_crs.authid()
            if target_crs is not None and target_crs.isValid()
            else source_layer.crs().authid())
        uri = f"{wkb_str}?crs={crs_authid}"

        layer_name = self._build_attribute_subset_layer_name(source_layer, selected_fids)

        # uri = f"{wkb_str}?crs={crs_authid}"
        new_layer = QgsVectorLayer(uri, layer_name, "memory")

        if new_layer is None or not new_layer.isValid():
            return None, self.tr("Não foi possível criar a nova camada.")

        provider = new_layer.dataProvider()

        source_fields = source_layer.fields()
        if not provider.addAttributes(list(source_fields)):
            return None, self.tr("Não foi possível copiar os campos da camada.")

        new_layer.updateFields()

        new_features = []
        selected_fids_set = set(selected_fids)

        for feat in source_layer.getFeatures():
            if feat.id() not in selected_fids_set:
                continue

            new_feat = QgsFeature(new_layer.fields())
            geom = feat.geometry()

            source_crs = source_layer.crs()
            target_crs = self._effective_target_crs(source_layer)

            if (geom is not None
                and source_crs is not None and source_crs.isValid()
                and target_crs is not None and target_crs.isValid()
                and source_crs != target_crs):
                geom = QgsGeometry(geom)
                transform = QgsCoordinateTransform(source_crs, target_crs, QgsProject.instance())
                geom.transform(transform)

            new_feat.setGeometry(geom)
            new_feat.setAttributes(feat.attributes())
            new_features.append(new_feat)

        if not new_features:
            return None, self.tr("Nenhuma feição válida foi encontrada para criar a nova camada.")

        if not provider.addFeatures(new_features):
            return None, self.tr("Não foi possível copiar as feições selecionadas.")

        new_layer.updateExtents()
        self._copy_layer_visual_style(source_layer, new_layer)

        return new_layer, ""

    def _create_layer_from_selected_attributes(self):
        """
        Cria uma nova camada contendo apenas as feições atualmente selecionadas,
        priorizando a seleção da tabela de atributos.
        """
        source_layer = self._selected_vector_layer()
        if source_layer is None:
            self.mostrar_mensagem(self.tr("Nenhuma camada válida foi selecionada."), "Erro", duracao=2)
            return

        selected_fids = self._current_selected_feature_ids()
        if not selected_fids:
            self.mostrar_mensagem(self.tr("Selecione ao menos um atributo ou uma feição para criar a nova camada."), "Erro", duracao=2)
            return

        new_layer, error_message = self._create_feature_subset_memory_layer(source_layer, selected_fids)
        if new_layer is None:
            self.mostrar_mensagem(error_message or self.tr("Não foi possível criar a camada filtrada."), "Erro", duracao=2)
            return

        QgsProject.instance().addMapLayer(new_layer)

        self.mostrar_mensagem(self.tr("Nova camada criada com sucesso: {layer_name}").format(layer_name=new_layer.name()), "Sucesso", duracao=3)

    def _update_attribute_subset_button_state(self):
        """
        Habilita o botão de criar camada por atributos quando houver:
        - camada válida no combo
        - seleção na tabela de atributos OU seleção de feições na camada
        """
        layer = self._selected_vector_layer()

        has_layer = layer is not None
        has_table_selection = len(self.tableWidgetAtributos.selectedItems()) > 0

        has_layer_selection = False
        if layer is not None:
            try:
                has_layer_selection = layer.selectedFeatureCount() > 0
            except Exception:
                has_layer_selection = False

        self.pushButtonCamadasAtributos.setEnabled(
            has_layer and (has_table_selection or has_layer_selection))

    def _filter_attributes_table(self, text: str):
        """
        Filtra em tempo real a tabela de atributos pelo texto digitado no lineEditPesquisar.
        A busca é por 'contém', sem diferenciar maiúsculas/minúsculas.
        """
        search = (text or "").strip().casefold()

        for row in range(self.tableWidgetAtributos.rowCount()):
            item = self.tableWidgetAtributos.item(row, 0)

            if item is None:
                self.tableWidgetAtributos.setRowHidden(row, False)
                continue

            item_text = (item.text() or "").strip().casefold()
            hide_row = bool(search) and (search not in item_text)
            self.tableWidgetAtributos.setRowHidden(row, hide_row)

    def _set_projection_lineedit_text(self, text: str, color: str):
        """Atualiza o texto e a cor do lineEditProjecao."""
        self.lineEditProjecao.setText(text or "")
        self.lineEditProjecao.setStyleSheet(f"color: {color};")

    def _format_layer_crs_text(self, layer) -> str:
        """Monta um texto amigável da projeção da camada."""
        if layer is None:
            return ""

        crs = layer.crs()
        if not crs.isValid():
            return self.tr("SRC inválido")

        authid = crs.authid() or ""
        desc = crs.description() or ""

        if authid and desc:
            return f"{authid} - {desc}"
        if authid:
            return authid
        if desc:
            return desc
        return self.tr("SRC desconhecido")

    def _format_crs_text(self, crs) -> str:
        """Monta um texto amigável para um CRS selecionado."""
        if crs is None or not crs.isValid():
            return ""

        authid = crs.authid() or ""
        desc = crs.description() or ""

        if authid and desc:
            return f"{authid} - {desc}"
        if authid:
            return authid
        if desc:
            return desc
        return self.tr("SRC desconhecido")

    def _update_projection_lineedit_from_layer(self):
        """
        Atualiza o lineEditProjecao com o SRC real da camada selecionada no combo.
        Também limpa eventual CRS alvo pendente de reprojeção.
        """
        layer = self._selected_vector_layer()
        self._selected_target_crs = None
        self._set_projection_lineedit_text(self._format_layer_crs_text(layer), "#0055ff")

    def _choose_target_projection(self):
        """
        Abre o diálogo de seleção de projeção e atualiza o lineEditProjecao
        com a projeção escolhida, sem alterar a camada ainda.
        """
        dlg = QgsProjectionSelectionDialog(self)

        layer = self._selected_vector_layer()
        if layer is not None and layer.crs().isValid():
            try:
                dlg.setCrs(layer.crs())
            except Exception:
                pass  # nosec B110

        if dlg.exec():
            try:
                crs = dlg.crs()
            except Exception:
                crs = None

            if crs is not None and crs.isValid():
                self._selected_target_crs = crs
                self._set_projection_lineedit_text(
                    self._format_crs_text(crs),
                    "#ff00ff")

    def _effective_target_crs(self, source_layer):
        """
        Retorna o CRS alvo a usar:
        - CRS escolhido no lineEditProjecao, se válido
        - senão, CRS da camada de origem
        """
        if self._selected_target_crs is not None and self._selected_target_crs.isValid():
            return self._selected_target_crs

        if source_layer is not None:
            return source_layer.crs()

        return None

    def _zoom_to_attribute_feature_by_right_click(self, pos):
        """
        Ao clicar com o botão direito em uma célula da tabela de atributos,
        dá zoom na feição correspondente da camada atualmente selecionada.
        """
        layer = self._selected_vector_layer()
        if layer is None:
            return

        item = self.tableWidgetAtributos.itemAt(pos)
        if item is None:
            return

        fid = item.data(Qt.ItemDataRole.UserRole + 4)
        if fid is None:
            return

        try:
            fid = int(fid)
        except Exception:
            return

        feat = layer.getFeature(fid)
        if not feat.isValid():
            return

        geom = feat.geometry()
        if geom is None or geom.isEmpty():
            return

        # opcional: ao clicar com botão direito, destacar a linha clicada
        blocker = QSignalBlocker(self.tableWidgetAtributos)
        try:
            self.tableWidgetAtributos.setCurrentItem(item)
        finally:
            del blocker

        canvas = self.iface.mapCanvas()
        extent = geom.boundingBox()

        # se for ponto ou bbox degenerado, cria uma folga para o zoom funcionar melhor
        if extent.width() == 0 and extent.height() == 0:
            center = extent.center()
            tol = 5.0
            extent.setXMinimum(center.x() - tol)
            extent.setXMaximum(center.x() + tol)
            extent.setYMinimum(center.y() - tol)
            extent.setYMaximum(center.y() + tol)
        else:
            extent.scale(1.20)

        canvas.setExtent(extent)
        canvas.refresh()

    def _update_field_subset_button_state(self):
        """
        Habilita o botão de criar camada por campo quando houver:
        - camada válida no combo
        - um campo selecionado na tabela de campos
        """
        layer = self._selected_vector_layer()
        field_idx = self._selected_field_index()

        has_layer = layer is not None
        has_field = field_idx is not None

        self.pushButtonCampo.setEnabled(has_layer and has_field)

    def _build_field_subset_layer_name(self, source_layer, field_name: str):
        """
        Monta o nome da nova camada baseada no campo selecionado.
        Ex.: NomeOriginal_Campo, com simplificação e sufixo único.
        """
        base_layer_name = source_layer.name() if source_layer is not None else self.tr("Camada")
        suffix = self._simplify_layer_name_part(field_name or self.tr("Campo"), max_len=24)

        base_name = f"{base_layer_name}_{suffix}"

        if len(base_name) > 50:
            short_base = self._simplify_layer_name_part(base_layer_name, max_len=22)
            short_suffix = self._simplify_layer_name_part(suffix, max_len=20)
            base_name = f"{short_base}_{short_suffix}"

        return self._nome_unico_no_projeto(base_name)

    def _create_layer_from_selected_field(self):
        """
        Cria uma nova camada com base no campo atualmente selecionado.
        Mantém as feições da camada, estilo e usa a projeção efetiva escolhida.
        """
        source_layer = self._selected_vector_layer()
        field_idx = self._selected_field_index()
        field = self._selected_field()

        if source_layer is None:
            self.mostrar_mensagem(self.tr("Nenhuma camada válida foi selecionada."), "Erro", duracao=2)
            return

        if field_idx is None or field is None:
            self.mostrar_mensagem(self.tr("Selecione um campo para criar a nova camada."), "Erro", duracao=2)
            return

        wkb_str = QgsWkbTypes.displayString(source_layer.wkbType())

        target_crs = self._effective_target_crs(source_layer)
        crs_authid = (target_crs.authid()
            if target_crs is not None and target_crs.isValid()
            else source_layer.crs().authid())

        layer_name = self._build_field_subset_layer_name(source_layer, field.name())
        uri = f"{wkb_str}?crs={crs_authid}"

        new_layer = QgsVectorLayer(uri, layer_name, "memory")
        if new_layer is None or not new_layer.isValid():
            self.mostrar_mensagem(self.tr("Não foi possível criar a nova camada."), "Erro", duracao=2)
            return

        provider = new_layer.dataProvider()

        # mantém a estrutura da camada original
        selected_field = source_layer.fields()[field_idx]

        if not provider.addAttributes([QgsField(selected_field)]):
            self.mostrar_mensagem(self.tr("Não foi possível copiar o campo selecionado."), "Erro", duracao=2)
            return

        new_layer.updateFields()

        source_crs = source_layer.crs()
        new_features = []

        for feat in source_layer.getFeatures():
            new_feat = QgsFeature(new_layer.fields())

            geom = feat.geometry()
            if (
                geom is not None
                and source_crs is not None and source_crs.isValid()
                and target_crs is not None and target_crs.isValid()
                and source_crs != target_crs):
                geom = QgsGeometry(geom)
                transform = QgsCoordinateTransform(source_crs, target_crs, QgsProject.instance())
                geom.transform(transform)

            new_feat.setGeometry(geom)
            new_feat.setAttributes([feat[field_idx]])
            new_features.append(new_feat)

        if not provider.addFeatures(new_features):
            self.mostrar_mensagem(self.tr("Não foi possível copiar as feições da camada."), "Erro", duracao=2)
            return

        new_layer.updateExtents()
        self._copy_layer_visual_style(source_layer, new_layer)
        QgsProject.instance().addMapLayer(new_layer)

        self.mostrar_mensagem(self.tr("Nova camada criada com sucesso: {layer_name}").format(layer_name=new_layer.name()), "Sucesso", duracao=3)

    def _clear_layer_dependent_widgets(self):
        """
        Limpa os widgets dependentes da camada quando não houver
        camada válida selecionada no combo.
        """
        blocker_campos = QSignalBlocker(self.tableWidgetCampo)
        blocker_attrs = QSignalBlocker(self.tableWidgetAtributos)
        blocker_combo = QSignalBlocker(self.comboBoxCamada)

        try:
            self.comboBoxCamada.clear()

            self.tableWidgetCampo.clearSelection()
            self.tableWidgetCampo.setRowCount(0)

            self.tableWidgetAtributos.clearSelection()
            self.tableWidgetAtributos.setRowCount(0)

            self.lineEditPesquisar.clear()

            self._selected_target_crs = None
            self.lineEditProjecao.clear()
            self.lineEditProjecao.setStyleSheet("color: #0055ff;")

            self.checkBoxSelecionaAtributos.setChecked(False)
            self.checkBoxSelecionaAtributos.setEnabled(False)

            self.pushButtonCamadasAtributos.setEnabled(False)
            self.pushButtonCampo.setEnabled(False)
            self.pushButtonAbrirCalculadora.setEnabled(False)

            self.pushButtonNovaCamada.setEnabled(False)
            self.pushButtonReprojetar.setEnabled(False)
            self.pushButtonSalvarCamadaEditada.setEnabled(False)

        finally:
            del blocker_combo
            del blocker_attrs
            del blocker_campos

    def _update_new_layer_button_state(self):
        """
        Habilita o botão 'Criar Nova Camada' quando houver camada válida
        e ao menos um campo carregado.
        """
        layer = self._selected_vector_layer()
        has_layer = layer is not None
        has_fields = self.tableWidgetCampo.rowCount() > 0

        self.pushButtonNovaCamada.setEnabled(has_layer and has_fields)

    def _update_reproject_button_state(self):
        """
        Habilita o botão 'Reprojetar' quando houver camada válida selecionada.
        """
        layer = self._selected_vector_layer()
        self.pushButtonReprojetar.setEnabled(layer is not None)

    def _update_main_action_buttons_state(self):
        """Atualiza o estado dos principais botões de ação da ferramenta."""
        self._update_new_layer_button_state()
        self._update_reproject_button_state()
        self._update_save_edited_layer_button_state()
        self._update_field_calculator_button_state()

    def _update_field_calculator_button_state(self):
        """
        Habilita o botão da calculadora apenas quando houver camada válida selecionada.
        """
        layer = self._selected_vector_layer()
        self.pushButtonAbrirCalculadora.setEnabled(layer is not None)

    def _update_save_edited_layer_button_state(self):
        """
        Habilita o botão 'Salvar Camada Editada' quando houver camada válida
        e ao menos um campo carregado.
        """
        layer = self._selected_vector_layer()
        has_layer = layer is not None
        has_fields = self.tableWidgetCampo.rowCount() > 0

        self.pushButtonSalvarCamadaEditada.setEnabled(has_layer and has_fields)

    def _open_field_calculator(self):
        """
        Abre apenas a calculadora de campo da camada atualmente selecionada.
        """
        layer = self._selected_vector_layer()
        if layer is None:
            self.mostrar_mensagem(self.tr("Nenhuma camada válida foi selecionada."), "Erro", duracao=3)
            return

        try:
            self.iface.setActiveLayer(layer)
            self.iface.actionOpenFieldCalculator().trigger()
        except Exception as e:
            self._log_message(self.tr("Falha ao abrir a calculadora de campo: {error}").format(error=str(e)), Qgis.MessageLevel.Warning)
            self.mostrar_mensagem(self.tr("Não foi possível abrir a calculadora de campo."), "Erro", duracao=3)

    def changeEvent(self, event):
        """
        Quando o diálogo volta a ficar ativo, força refresh das camadas.
        Isso ajuda principalmente após criar camada temporária pela janela nativa do QGIS.
        """
        super(TabelasManager, self).changeEvent(event)

        try:
            if event.type() == QEvent.Type.ActivationChange and self.isActiveWindow():
                self._refresh_layer_ui()
                self._on_current_layer_changed()
        except Exception:
            pass  # nosec B110

    def _connect_project_signals(self):
        """
        Conecta sinais do projeto apenas uma vez.
        """
        if self._project_signals_connected:
            return

        project = QgsProject.instance()

        try:
            project.layersAdded.connect(self._refresh_layer_ui)
        except Exception:
            pass  # nosec B110

        try:
            project.layersRemoved.connect(self._refresh_layer_ui)
        except Exception:
            pass  # nosec B110

        try:
            project.layerWasAdded.connect(self._refresh_layer_ui)
        except Exception:
            pass  # nosec B110

        try:
            project.legendLayersAdded.connect(self._refresh_layer_ui)
        except Exception:
            pass  # nosec B110

        self._project_signals_connected = True

    def _disconnect_project_signals(self):
        """
        Desconecta sinais do projeto.
        """
        if not self._project_signals_connected:
            return

        project = QgsProject.instance()

        for signal in (
            getattr(project, "layersAdded", None),
            getattr(project, "layersRemoved", None),
            getattr(project, "layerWasAdded", None),
            getattr(project, "legendLayersAdded", None)):
            if signal is None:
                continue
            try:
                signal.disconnect(self._refresh_layer_ui)
            except Exception:
                pass  # nosec B110

        self._project_signals_connected = False

    def _connect_current_layer_table_signals(self):
        """
        Conecta os sinais da camada atual usados para manter as tabelas em sincronia
        com alterações estruturais, de atributos, feições e seleção.
        """
        if self._current_table_layer is not None:
            try:
                self._current_table_layer.updatedFields.disconnect(self._load_selected_layer_tables)
            except Exception:
                pass  # nosec B110

            try:
                self._current_table_layer.attributeValueChanged.disconnect(self._reload_attributes_only)
            except Exception:
                pass  # nosec B110

            try:
                self._current_table_layer.selectionChanged.disconnect(self._sync_table_selection_from_layer)
            except Exception:
                pass  # nosec B110

            try:
                self._current_table_layer.featureAdded.disconnect(self._reload_tables_after_feature_change)
            except Exception:
                pass  # nosec B110

            try:
                self._current_table_layer.featureDeleted.disconnect(self._reload_tables_after_feature_change)
            except Exception:
                pass  # nosec B110

        self._current_table_layer = self._selected_vector_layer()

        if self._current_table_layer is not None:
            try:
                self._current_table_layer.updatedFields.connect(self._load_selected_layer_tables)
            except Exception:
                pass  # nosec B110

            try:
                self._current_table_layer.attributeValueChanged.connect(self._reload_attributes_only)
            except Exception:
                pass  # nosec B110

            try:
                self._current_table_layer.selectionChanged.connect(self._sync_table_selection_from_layer)
            except Exception:
                pass  # nosec B110

            try:
                self._current_table_layer.featureAdded.connect(self._reload_tables_after_feature_change)
            except Exception:
                pass  # nosec B110

            try:
                self._current_table_layer.featureDeleted.connect(self._reload_tables_after_feature_change)
            except Exception:
                pass  # nosec B110

    def _reload_tables_after_feature_change(self, *args):
        """
        Recarrega campos e atributos quando feições são adicionadas/removidas.
        """
        self._load_selected_layer_tables()

    def _load_selected_layer_tables(self):
        """Carrega os campos da camada selecionada e inicializa os atributos."""
        layer = self._selected_vector_layer()

        blocker_campos = QSignalBlocker(self.tableWidgetCampo)
        blocker_attrs = QSignalBlocker(self.tableWidgetAtributos)
        try:
            self.tableWidgetCampo.setRowCount(0)
            self.tableWidgetAtributos.setRowCount(0)

            if layer is None:
                return

            fields = layer.fields()

            if len(fields) == 0:
                row = self.tableWidgetCampo.rowCount()
                self.tableWidgetCampo.insertRow(row)

                item = QTableWidgetItem("FID")
                item.setData(Qt.ItemDataRole.UserRole, -1)  # campo virtual
                item.setFlags(item.flags() & ~Qt.ItemFlag.ItemIsEditable)
                self._apply_item_style(item)
                self.tableWidgetCampo.setItem(row, 0, item)
            else:
                for idx, field in enumerate(fields):
                    row = self.tableWidgetCampo.rowCount()
                    self.tableWidgetCampo.insertRow(row)

                    item = QTableWidgetItem(field.name())
                    item.setData(Qt.ItemDataRole.UserRole, idx)
                    self._apply_item_style(item)
                    self.tableWidgetCampo.setItem(row, 0, item)

            self.tableWidgetCampo.resizeRowsToContents()

            if self.tableWidgetCampo.rowCount() > 0:
                self.tableWidgetCampo.setCurrentCell(0, 0)

        finally:
            del blocker_attrs
            del blocker_campos

        if self.tableWidgetCampo.rowCount() > 0:
            self._load_attributes_for_selected_field()

        self._update_field_subset_button_state()
        self._update_main_action_buttons_state()

    def _attribute_sort_key(self, raw_value, display_text, field):
        text = (display_text or "").strip()

        if raw_value is None or text == "<NULL>":
            return (3, 0, "")

        family = self._field_type_family(field)

        if family in ("int", "float"):
            try:
                value_text = str(raw_value).strip().replace(",", ".")
                if re.fullmatch(r"[+-]?\d+", value_text):
                    return (0, int(value_text), text.casefold())
                return (0, float(value_text), text.casefold())
            except Exception:
                pass  # nosec B110

        text_num = text.replace(",", ".")
        if re.fullmatch(r"[+-]?\d+(?:\.\d+)?", text_num):
            try:
                if "." not in text_num:
                    return (0, int(text_num), text.casefold())
                return (0, float(text_num), text.casefold())
            except Exception:
                pass  # nosec B110

        return (1, text.casefold(), "")

    def _load_attributes_for_selected_field(self):
        """
        Carrega em Atributos todos os valores do campo selecionado em Campos,
        uma linha por feição, preservando valores repetidos.

        Quando o campo selecionado for o FID virtual (-1), exibe apenas células
        vazias, mantendo o vínculo com a feição pelo feat_id.
        """
        layer = self._selected_vector_layer()
        field_idx = self._selected_field_index()
        field = self._selected_field()

        blocker = QSignalBlocker(self.tableWidgetAtributos)
        try:
            self.tableWidgetAtributos.setRowCount(0)

            if layer is None or field_idx is None:
                return

            rows_data = []

            for feat in layer.getFeatures():
                try:
                    if field_idx == -1:
                        raw_value = ""
                        display_text = ""
                    else:
                        raw_value = feat[field_idx]
                        display_text = self._format_attribute_value_for_display(raw_value, field)
                except Exception:  # nosec B112
                    continue

                rows_data.append((feat.id(), raw_value, display_text))

            if field_idx == -1:
                rows_data.sort(key=lambda x: x[0])
            else:
                rows_data.sort(key=lambda x: self._attribute_sort_key(x[1], x[2], field))

            for feat_id, raw_value, display_text in rows_data:
                row = self.tableWidgetAtributos.rowCount()
                self.tableWidgetAtributos.insertRow(row)

                item_attr = QTableWidgetItem(display_text)
                item_attr.setData(Qt.ItemDataRole.UserRole, field_idx)
                item_attr.setData(Qt.ItemDataRole.UserRole + 1, display_text)
                item_attr.setData(Qt.ItemDataRole.UserRole + 2, display_text)
                item_attr.setData(Qt.ItemDataRole.UserRole + 3, raw_value)
                item_attr.setData(Qt.ItemDataRole.UserRole + 4, feat_id)

                if field_idx == -1:
                    item_attr.setFlags(item_attr.flags() & ~Qt.ItemFlag.ItemIsEditable)
                else:
                    item_attr.setFlags(item_attr.flags() | Qt.ItemFlag.ItemIsEditable)

                self._apply_item_style(item_attr)
                self.tableWidgetAtributos.setItem(row, 0, item_attr)

            self.tableWidgetAtributos.resizeRowsToContents()

        finally:
            del blocker

        self._sync_table_selection_from_layer()
        self._update_select_equal_checkbox_state()
        self._update_attribute_subset_button_state()
        self._filter_attributes_table(self.lineEditPesquisar.text())

    def _selected_attribute_values_in_table(self):
        """
        Retorna os valores originais atualmente selecionados na tabela de atributos.
        Ignora o campo virtual FID (-1).
        """
        values = set()

        for item in self.tableWidgetAtributos.selectedItems():
            if item is None:
                continue

            field_idx = item.data(Qt.ItemDataRole.UserRole)
            if field_idx == -1:
                continue

            original_value = item.data(Qt.ItemDataRole.UserRole + 3)
            if original_value is None:
                original_value = item.text()

            text = str(original_value).strip()
            if text:
                values.add(text)

        return values