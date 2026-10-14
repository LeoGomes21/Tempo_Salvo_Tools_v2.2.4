from qgis.core import QgsProject, QgsMessageLog, Qgis, QgsVectorLayer, QgsWkbTypes, QgsMapSettings, QgsMapRendererCustomPainterJob, QgsGeometry, QgsPointXY, QgsFeature, QgsLineSymbol, QgsCoordinateReferenceSystem, QgsCoordinateTransform, QgsField, QgsMarkerLineSymbolLayer, QgsSimpleMarkerSymbolLayer, QgsPalLayerSettings, QgsSymbol, QgsSimpleLineSymbolLayer, QgsMarkerSymbol, QgsTextFormat, QgsVectorLayerSimpleLabeling, QgsSymbolLayer, QgsUnitTypes, QgsEditorWidgetSetup, QgsDistanceArea, QgsEditFormConfig, QgsLayerTreeLayer, QgsLayerTreeGroup, QgsSingleSymbolRenderer, QgsProperty, QgsLabelLineSettings, QgsVector
from qgis.PyQt.QtWidgets import QDialog, QCheckBox, QColorDialog, QApplication, QListWidget, QLabel,QStyledItemDelegate, QStyle, QFileDialog, QPushButton, QAbstractItemView
from qgis.PyQt.QtGui import QImage, QPainter, QPixmap, QColor, QPen, QIntValidator, QFont, QBrush, QPalette, QStandardItemModel, QStandardItem, QDesktopServices
from qgis.PyQt.QtCore import Qt, QSize, QVariant, QRect, QPoint, QEvent, QSettings, QMetaType, QCoreApplication, QUrl
from qgis.utils import iface
from qgis.PyQt import uic
import ezdxf
import math
import os

FORM_CLASS, _ = uic.loadUiType(os.path.join(os.path.dirname(__file__), 'Dimensionamento_Vetores.ui'))

class DimensionarVetores(QDialog, FORM_CLASS):
    def __init__(self, parent=None):
        """Constructor."""
        super(DimensionarVetores, self).__init__(parent)
        # Configura a interface do usuário a partir do Designer.
        self.setupUi(self)

        self.iface = iface

        # Altera o título da janela
        self.setWindowTitle(self.tr("Dimensionamento de Vetores"))

        self._widget_msg_sucesso = None # referência ao último widget de sucesso
        self._dim_conn_layer     = None # referência à camada de dimensões
        self._dim_conn_srcLayer  = None # camada-origem que está “linkada”
        self._dim_conn_links     = {} # {fid_origem: [fids_dimensão]}

        # depois de self.setupUi(self)
        self._tv_model = None
        self._tv_last_layer_ids = []
        self._tv_selected_layer_id = None
        self._last_layer_connected = None

        # ANGULAR CONNECTED
        self._ang_conn_layer      = None # camada de arcos
        self._ang_conn_srcLayer   = None # camada origem (polígono)
        self._ang_conn_layer_id   = ""   # id da camada angular
        self._ang_conn_links      = {}   # {fid_src: [fids_arc]}

        # AZIMUTE CONNECTED
        self._azi_conn_layer      = None # camada de azimutes
        self._azi_conn_srcLayer   = None # camada origem (polígono)
        self._azi_conn_layer_id   = ""   # id da camada de azimutes
        self._azi_conn_links      = {}   # {fid_src: [fids_azimute]}

        # RUMO CONNECTED
        self._rumo_conn_layer      = None # camada de rumos
        self._rumo_conn_srcLayer   = None # camada origem (polígono)
        self._rumo_conn_layer_id   = ""   # id da camada de rumos
        self._rumo_conn_links      = {}   # {fid_src: [fids_rumo]}

        self._btns_last_src_layer = None  # para (des)conectar sinais de featureAdd/Del da camada do combo

        # configurar tree view
        self._init_treeview_camadas()

        self._update_buttons_state()

        # Preenche o comboBox com camadas de linha
        self.populate_combo_box()

        # Ao passar o mouse (hover) com um azul claro
        style = "QTreeView::item:hover { background: #cceeff; }"  # Azul claro no hover
        self.treeViewCamada.setStyleSheet(style)

        # Conecta os sinais aos slots
        self.connect_signals()

    def tr(self, message):
        """
        Traduz textos deste diálogo.
        O contexto precisa ser estável para o Qt Linguist encontrar as traduções.
        """
        return QCoreApplication.translate("DimensionarVetores", message)

    def connect_signals(self):

       # Conecta a mudança de seleção no comboBoxCamada para atualizar o checkBoxSeleciona
        self.comboBoxCamada.currentIndexChanged.connect(self.update_checkBoxSeleciona)

        # Conecta também para atualizar os sinais da camada (selectionChanged)
        self.comboBoxCamada.currentIndexChanged.connect(self.update_layer_connections)

        # Conecta sinais do projeto para atualizar comboBox quando camadas forem adicionadas, removidas ou renomeadas
        QgsProject.instance().layersAdded.connect(self.populate_combo_box)
        QgsProject.instance().layersRemoved.connect(self.populate_combo_box)
        QgsProject.instance().layerWillBeRemoved.connect(self.populate_combo_box)

        # Conecta o botão pushButtonFechar
        self.pushButtonFechar.clicked.connect(self.close)

        self.pushButtonLivre.clicked.connect(self.criar_camada_dimensionamento)

        self.pushButtonConectada.clicked.connect(self.criar_camada_dimensionamento_conectada)

        # self.pushButtonAngular.clicked.connect(self.criar_camada_dimensionamento_angular)
        self.pushButtonAngular.clicked.connect(self.criar_camada_dimensionamento_angular_conectada)

        # Atualiza lista de camadas de dimensão ao mudar estrutura do projeto
        QgsProject.instance().layersAdded.connect(self.atualizar_treeViewCamadas)
        QgsProject.instance().layersRemoved.connect(self.atualizar_treeViewCamadas)
        QgsProject.instance().layerWillBeRemoved.connect(self.atualizar_treeViewCamadas)

        self.treeViewCamada.setItemDelegate(TreeDeleteButtonDelegate(self))

        self.pushButtonCor.clicked.connect(self._on_pick_color_for_layer)

        # Liga os 4 controles de estilo (aplica em tempo real na camada selecionada)
        for sb in (self.doubleSpinBoxTamanho,   # tamanho da seta (mm)
                   self.doubleSpinBoxAux,       # comprimento do símbolo auxiliar (tick) (mm)
                   self.doubleSpinBoxTexto,     # tamanho do texto (pt)
                   self.doubleSpinBoxRecuo):    # recuo da seta (mm)
            sb.valueChanged.connect(self._on_symbol_controls_changed)

        self.doubleSpinBoxTamanhoM.valueChanged.connect(self._on_min_length_changed_selected)
        self.checkBoxDirecao.stateChanged.connect(self._on_direction_changed_selected)

        # Formato do rótulo angular: graus decimais ou GMS (graus/minutos/segundos)
        chk_ang = getattr(self, "checkBoxAngulo", None) or self.findChild(QCheckBox, "checkBoxAngulo")
        if chk_ang is not None:
            chk_ang.stateChanged.connect(self._on_ang_format_changed_selected)

        btn_az = getattr(self, "pushButtonAzimute", None)
        if btn_az is not None:
            btn_az.clicked.connect(self.criar_camada_dimensionamento_azimute_conectada)

        btn_ru = getattr(self, "pushButtonRumo", None)
        if btn_ru is not None:
            btn_ru.clicked.connect(self.criar_camada_dimensionamento_rumo_conectada)

        for rb_name in ("radioButtonVerdadeiro", "radioButtonPlano"):
            rb = getattr(self, rb_name, None)
            if rb is not None:
                rb.toggled.connect(self._on_azimute_mode_changed_selected)

        for rb_name in ("radioButtonVerdadeiro", "radioButtonPlano"):
            rb = getattr(self, rb_name, None)
            if rb is not None:
                rb.toggled.connect(self._on_rumo_mode_changed_selected)

        chk_inv = self._get_checkBox_inverter_direcao_azimute()

        if chk_inv is not None:
            chk_inv.toggled.connect(self._on_rumo_inverter_direcao_changed)
            chk_inv.toggled.connect(self._on_azimute_inverter_direcao_changed)

        self.pushButtonDXF.clicked.connect(self.exportar_dim_layer_para_dxf)

        self.comboBoxCamada.currentIndexChanged.connect(self._update_buttons_state)

        QgsProject.instance().layersAdded.connect(self._update_buttons_state)
        QgsProject.instance().layersRemoved.connect(self._update_buttons_state)
        QgsProject.instance().layerWillBeRemoved.connect(self._update_buttons_state)

    def showEvent(self, event):
        """
        Sobrescreve o evento de exibição do diálogo para resetar os Widgets.
        """
        super(DimensionarVetores, self).showEvent(event)

        # Reset do checkBoxSeleciona
        checkBox = self.findChild(QCheckBox, 'checkBoxSeleciona')
        if checkBox:
            checkBox.setChecked(False)
            checkBox.setEnabled(False)
        
        self.populate_combo_box()  # Atualiza o comboBoxCamada com as camadas disponíveis

        self.update_checkBoxSeleciona()  # Atualiza o estado do checkBoxSeleciona com base nas feições selecionadas

        self.update_layer_connections()  # Conecta os sinais da camada atual

        self.atualizar_treeViewCamadas()

        self._hook_src_layer_feature_signals()
        self._update_buttons_state()

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
            except Exception:
                bar.clearWidgets()
            self._widget_msg_sucesso = None

        if tipo == "Erro":
            bar.pushMessage("Erro", texto, level=Qgis.MessageLevel.Critical, duration=duracao)

        elif tipo == "Aviso":
            bar.pushMessage("Aviso", texto, level=Qgis.MessageLevel.Warning, duration=duracao)

        elif tipo == "Sucesso":
            msg = bar.createMessage("Sucesso", texto)

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
        layer_id = self.comboBoxCamada.currentData()  # Obtém o ID da camada selecionada no comboBoxCamada
        if layer_id:  # Verifica se há uma camada selecionada
            layer = QgsProject.instance().mapLayer(layer_id)  # Obtém a camada correspondente ao ID
            if layer:  # Verifica se a camada existe
                selected_features = layer.selectedFeatureCount()  # Conta o número de feições selecionadas na camada
                if selected_features > 0:  # Se houver feições selecionadas, ativa o checkBoxSeleciona
                    self.findChild(QCheckBox, 'checkBoxSeleciona').setEnabled(True)
                else:  # Se não houver feições selecionadas, desativa o checkBoxSeleciona e o desmarca
                    self.findChild(QCheckBox, 'checkBoxSeleciona').setEnabled(False)
                    self.findChild(QCheckBox, 'checkBoxSeleciona').setChecked(False)
            else:  # Se a camada não for válida, desativa o checkBoxSeleciona e o desmarca
                self.findChild(QCheckBox, 'checkBoxSeleciona').setEnabled(False)
                self.findChild(QCheckBox, 'checkBoxSeleciona').setChecked(False)
        else:  # Se não houver uma camada selecionada, desativa o checkBoxSeleciona e o desmarca
            self.findChild(QCheckBox, 'checkBoxSeleciona').setEnabled(False)
            self.findChild(QCheckBox, 'checkBoxSeleciona').setChecked(False)

    def update_layer_connections(self):
        """
        Conecta o sinal selectionChanged da camada selecionada no comboBoxCamada à função update_checkBoxSeleciona,
        e atualiza o estado do checkBoxSeleciona imediatamente.

        Parâmetros:
        self : objeto
            Referência à instância atual da classe.

        A função realiza as seguintes ações:
        - Obtém o ID da camada atualmente selecionada no comboBoxCamada.
        - Se uma camada válida for encontrada, conecta o sinal selectionChanged da camada à função update_checkBoxSeleciona.
        - Atualiza imediatamente o estado do checkBoxSeleciona com base na seleção de feições.
        - Se não houver uma camada selecionada, desativa o checkBoxSeleciona.
        """
        layer_id = self.comboBoxCamada.currentData()
        # desconecta da anterior
        try:
            if self._last_layer_connected is not None:
                self._last_layer_connected.selectionChanged.disconnect(self.update_checkBoxSeleciona)
        except Exception:
            pass  # nosec B110

        if layer_id:
            layer = QgsProject.instance().mapLayer(layer_id)
            if layer:
                try:
                    layer.selectionChanged.connect(self.update_checkBoxSeleciona)
                except Exception:
                    pass  # nosec B110
                self._last_layer_connected = layer
                self.update_checkBoxSeleciona()
                return

        self._last_layer_connected = None

        self._hook_src_layer_feature_signals()
        self._update_buttons_state()

        self.update_checkBoxSeleciona()

    def populate_combo_box(self):
        """
        Popula o comboBoxCamada com as camadas de polígonos disponíveis no projeto e realiza ações relacionadas.

        Parâmetros:
        self : objeto
            Referência à instância atual da classe.

        A função realiza as seguintes ações:
        - Salva a camada atualmente selecionada no comboBoxCamada.
        - Bloqueia temporariamente os sinais do comboBoxCamada para evitar atualizações desnecessárias.
        - Limpa o comboBoxCamada antes de preenchê-lo novamente.
        - Adiciona as camadas de polígonos disponíveis ao comboBoxCamada.
        - Restaura a seleção da camada anterior, se possível.
        - Desbloqueia os sinais do comboBoxCamada após preenchê-lo.
        - Preenche o comboBoxRotulagem com os campos da camada selecionada.
        - Ativa ou desativa o botão pushButtonConverter com base na presença de camadas no comboBoxCamada.
        """
        current_layer_id = self.comboBoxCamada.currentData()  # Salva a camada atualmente selecionada
        self.comboBoxCamada.blockSignals(True)  # Evita disparar eventos desnecessários
        self.comboBoxCamada.clear()

        layer_list = QgsProject.instance().mapLayers().values()
        polygon_layers = [
            layer for layer in layer_list 
            if isinstance(layer, QgsVectorLayer) and QgsWkbTypes.geometryType(layer.wkbType()) == QgsWkbTypes.GeometryType.PolygonGeometry]

        for layer in polygon_layers:
            self.comboBoxCamada.addItem(layer.name(), layer.id())
            layer.nameChanged.connect(self.update_combo_box_item)  # Mantém a conexão para atualizar nomes

        # Restaura a camada anteriormente selecionada, se ainda existir
        if current_layer_id:
            index = self.comboBoxCamada.findData(current_layer_id)
            if index != -1:
                self.comboBoxCamada.setCurrentIndex(index)

        self.comboBoxCamada.blockSignals(False)  # Libera os sinais
        
        # Reconecta os sinais da camada atual, garantindo que o selectionChanged esteja conectado
        self.update_layer_connections()

        # Reconecta sinais da camada atual + atualiza botões
        self.update_layer_connections()
        self._hook_src_layer_feature_signals()
        self._update_buttons_state()

    def update_combo_box_item(self):
        """
        Atualiza o texto dos itens no comboBoxCamada com base nos nomes atuais das camadas no projeto.

        Parâmetros:
        self : objeto
            Referência à instância atual da classe.

        A função realiza as seguintes ações:
        - Itera sobre os itens no comboBoxCamada.
        - Para cada item, obtém o ID da camada correspondente.
        - Atualiza o nome exibido no comboBoxCamada com o nome atual da camada, caso a camada ainda exista.
        - Atualiza o campo de nome do polígono (lineEditNome) após atualizar o comboBox.
        """
        for i in range(self.comboBoxCamada.count()):  # Itera sobre todos os itens no comboBoxCamada
            layer_id = self.comboBoxCamada.itemData(i)  # Obtém o ID da camada para o item atual
            layer = QgsProject.instance().mapLayer(layer_id)  # Obtém a camada correspondente ao ID
            if layer:  # Verifica se a camada existe
                self.comboBoxCamada.setItemText(i, layer.name())  # Atualiza o texto do item com o nome atual da camada

    def _hook_src_layer_feature_signals(self):
        """(Re)conecta featureAdded/featureDeleted da camada atualmente selecionada no combo,
        para atualizar os botões em tempo real quando o número de feições mudar."""
        # desconecta da anterior
        try:
            if isinstance(self._btns_last_src_layer, QgsVectorLayer):
                self._btns_last_src_layer.featureAdded.disconnect(self._on_src_layer_feature_changed)
                self._btns_last_src_layer.featureDeleted.disconnect(self._on_src_layer_feature_changed)
        except Exception:
            pass  # nosec B110

        self._btns_last_src_layer = None

        # conecta na atual
        layer_id = self.comboBoxCamada.currentData()
        if not layer_id:
            return
        lyr = QgsProject.instance().mapLayer(layer_id)
        if isinstance(lyr, QgsVectorLayer):
            try:
                lyr.featureAdded.connect(self._on_src_layer_feature_changed)
                lyr.featureDeleted.connect(self._on_src_layer_feature_changed)
                self._btns_last_src_layer = lyr
            except Exception:
                pass  # nosec B110

    def _on_src_layer_feature_changed(self, *args):
        """Reavalia e atualiza o estado dos botões quando ocorre adição ou exclusão de feições na camada de origem."""
        # qualquer mudança de feições → reavalia botões
        self._update_buttons_state()

    def _update_buttons_state(self):
        """Habilita/Desabilita botões conforme:
           - Conectada/Angular: precisa haver camada no combo E a camada ter feições (>0).
           - Cor/DXF: precisa haver itens no treeViewCamada.
           Atualiza em 'tempo real' pois é chamado por vários sinais."""
        # estado do combo
        has_combo_layers = self.comboBoxCamada.count() > 0
        layer_id = self.comboBoxCamada.currentData()
        lyr = QgsProject.instance().mapLayer(layer_id) if layer_id else None
        has_features = False
        try:
            if isinstance(lyr, QgsVectorLayer):
       # featureCount() é barato o suficiente aqui
                has_features = (lyr.featureCount() or 0) > 0
        except Exception:
            has_features = False

        # estado do tree
        has_tree_items = False
        try:
            has_tree_items = (self._tv_model.rowCount() > 0)
        except Exception:
            pass  # nosec B110

        # aplica nos botões (usa getattr para não quebrar se algum não existir)
        for btn_name, enabled in (
            ("pushButtonConectada", has_combo_layers and has_features),
            ("pushButtonAngular",   has_combo_layers and has_features),
            ("pushButtonAzimute",   has_combo_layers and has_features),
            ("pushButtonRumo",      has_combo_layers and has_features),
            ("pushButtonCor",       has_tree_items),
            ("pushButtonDXF",       has_tree_items)):
            btn = getattr(self, btn_name, None)
            if btn is not None:
                btn.setEnabled(bool(enabled))

    def _rumo_layer(self):
        """Retorna a camada de rumo conectada, ou None se não existir."""
        return QgsProject.instance().mapLayer(getattr(self, "_rumo_conn_layer_id", ""))

    def _azimute_para_rumo(self, azimute_graus: float) -> tuple[str, float, str]:
        """
        Converte azimute em rumo quadrantal.

        Retorna:
        - letra inicial: N ou S
        - ângulo do rumo: 0 a 90 graus
        - letra final: E ou W
        """
        try:
            az = float(azimute_graus) % 360.0
        except Exception:
            az = 0.0

        eps = 1e-10

        if az < 90.0 or abs(az - 360.0) <= eps:
            return "N", az, "E"

        if abs(az - 90.0) <= eps:
            return "N", 90.0, "E"

        if az < 180.0:
            return "S", 180.0 - az, "E"

        if abs(az - 180.0) <= eps:
            return "S", 0.0, "E"

        if az < 270.0:
            return "S", az - 180.0, "W"

        if abs(az - 270.0) <= eps:
            return "N", 90.0, "W"

        return "N", 360.0 - az, "W"

    def _formatar_rotulo_rumo(self, azimute_graus: float, modo: str, usar_gms: bool | None = None) -> str:
        """Formata o rótulo do rumo, respeitando checkBoxAngulo."""
        if usar_gms is None:
            usar_gms = self._usar_angulos_em_gms()

        ns, ang_rumo, ew = self._azimute_para_rumo(azimute_graus)

        if usar_gms:
            ang_txt = self._formatar_angulo_gms(ang_rumo)
        else:
            ang_txt = f"{float(ang_rumo):.4f}°"

        prefixo = "RP" if str(modo).lower() == "plano" else "RV"
        return f"{prefixo} = {ns} {ang_txt} {ew}"

    def _gera_dim_rumo_para_feat(self, feat: QgsFeature, crs: QgsCoordinateReferenceSystem, *, modo: str, min_segment_len: float = 0.0, label_gms: bool = False) -> list[QgsFeature]:
        """
        Gera dimensões de rumo para TODOS os lados externos do polígono,
        em percurso circular.

        Regras:
        - começa no vértice mais ao Norte;
        - empate: mais à esquerda;
        - percorre o polígono no sentido horário;
        - radioButtonVerdadeiro calcula rumo verdadeiro;
        - radioButtonPlano calcula rumo plano invertendo a direção;
        - checkBoxAngulo alterna decimal/GMS;
        - checkBoxDirecao controla fora/dentro;
        - doubleSpinBoxTamanhoM filtra lados pequenos;
        - checkbox 'Inverter direção' inverte o sentido de cálculo.
        """
        geom = feat.geometry()

        if not geom or geom.isEmpty():
            return []

        modo = str(modo).lower()
        feats_dim = []
        parts = geom.asMultiPolygon() if geom.isMultipart() else [geom.asPolygon()]

        # Padrão = fora
        # Marcado "Inverter posição" = dentro
        want_outside = not bool(self.checkBoxDirecao.isChecked())

        for part in parts:
            if not part:
                continue

            ring = part[0]  # apenas anel externo

            pts = self._ring_circular_desde_norte_oeste(
                ring,
                sentido_horario=True)

            if len(pts) < 2:
                continue

            for i in range(len(pts)):
                p_start = QgsPointXY(pts[i])
                p_end = QgsPointXY(pts[(i + 1) % len(pts)])

                if not self._segmento_azimute_valido(
                        p_start,
                        p_end,
                        crs,
                        min_segment_len=min_segment_len):
                    continue

       # Direção-base circular:
       # - Verdadeiro: percorre no sentido horário
       # - Plano: por regra anterior, inverte a direção
                if modo == "plano":
                    p_calc_1, p_calc_2 = p_end, p_start
                else:
                    p_calc_1, p_calc_2 = p_start, p_end

       # Checkbox "Inverter direção"
                try:
                    if self._azimute_inverter_direcao_extra():
                        p_calc_1, p_calc_2 = p_calc_2, p_calc_1
                except Exception:
                    pass  # nosec B110

                if modo == "plano":
                    az = self._calcular_azimute_plano(p_calc_1, p_calc_2)
                else:
                    az = self._calcular_azimute_verdadeiro(p_calc_1, p_calc_2, crs)

                p_draw_1, p_draw_2 = self._orientar_segmento_para_mesmo_lado(
                    geom,
                    p_calc_1,
                    p_calc_2,
                    want_outside=want_outside,
                    crs=crs
                )

                f = QgsFeature()
                f.setGeometry(QgsGeometry.fromPolylineXY([
                    QgsPointXY(p_draw_1),
                    QgsPointXY(p_draw_2)
                ]))
                f.setAttributes([
                    round(az, 6),
                    self._formatar_rotulo_rumo(az, modo, label_gms)
                ])
                feats_dim.append(f)

        return feats_dim

    def criar_camada_dimensionamento_rumo_conectada(self):
        """Cria uma camada conectada de dimensão de rumo a partir da camada poligonal selecionada."""
        layer_id = self.comboBoxCamada.currentData()

        if not layer_id:
            self.mostrar_mensagem(self.tr("Selecione uma camada de polígono."), "Erro")
            return

        src_layer = QgsProject.instance().mapLayer(layer_id)

        if not isinstance(src_layer, QgsVectorLayer):
            self.mostrar_mensagem(self.tr("Camada inválida selecionada."), "Erro")
            return

        if not self._validar_crs_utm_para_dimensionamento(src_layer):
            return

        try:
            if self._rumo_conn_srcLayer:
                self._rumo_conn_srcLayer.geometryChanged.disconnect(self._rumo_on_geom_changed)
                self._rumo_conn_srcLayer.featureAdded.disconnect(self._rumo_on_feat_added)
                self._rumo_conn_srcLayer.featureDeleted.disconnect(self._rumo_on_feat_deleted)
        except Exception:
            pass  # nosec B110

        modo = self._azimute_modo_atual()
        min_segment_len = float(self.doubleSpinBoxTamanhoM.value())
        label_gms = self._usar_angulos_em_gms()

        chk = self.findChild(QCheckBox, "checkBoxSeleciona")
        feats_src = list(src_layer.getSelectedFeatures()) if (chk and chk.isChecked()) else list(src_layer.getFeatures())

        if not feats_src:
            self.mostrar_mensagem(self.tr("Nenhuma feição encontrada para dimensionar o rumo."), "Erro")
            return

        crs = src_layer.crs()

        layer = self._criar_camada_dim_base("Dim_Rumo", crs, [], editavel=False)

        layer.setCustomProperty("dim/rumo", True)
        layer.setCustomProperty("dim/connected", True)
        layer.setCustomProperty("dim/src_layer_id", src_layer.id())
        layer.setCustomProperty("dim/rumo_modo", modo)
        layer.setCustomProperty("dim/min_segment_len", min_segment_len)
        layer.setCustomProperty("dim/label_gms", bool(label_gms))
        layer.setCustomProperty("dim/inverter_direcao", self._azimute_inverter_direcao_extra())

        try:
            arrow = float(self.doubleSpinBoxTamanho.value())
            tick = float(self.doubleSpinBoxAux.value())
            text = float(self.doubleSpinBoxTexto.value())
            afast = float(self.doubleSpinBoxRecuo.value())
        except Exception:
            arrow, tick, text, afast = 2.5, 4.0, 8.0, 0.2

        self._apply_dim_sizes(layer, arrow, tick, text, afast_mu=afast)
        layer.setCustomProperty("dim/recuo_ui", afast)

        self._rumo_conn_layer = layer
        self._rumo_conn_layer_id = layer.id()
        self._rumo_conn_srcLayer = src_layer
        self._rumo_conn_links = {}

        prov = layer.dataProvider()

        for feat in feats_src:
            rumo_feats = self._gera_dim_rumo_para_feat(
                feat,
                crs,
                modo=modo,
                min_segment_len=min_segment_len,
                label_gms=label_gms)
            ok, new_feats = prov.addFeatures(rumo_feats)
            self._rumo_conn_links[feat.id()] = [f.id() for f in new_feats]

        layer.setReadOnly(True)
        layer.triggerRepaint()

        src_layer.geometryChanged.connect(self._rumo_on_geom_changed)
        src_layer.featureAdded.connect(self._rumo_on_feat_added)
        src_layer.featureDeleted.connect(self._rumo_on_feat_deleted)

        self.mostrar_mensagem(self.tr("Dimensão de rumo criada."), "Sucesso")
        self.layer_dimensoes = layer
        self.atualizar_treeViewCamadas()

        try:
            self.iface.mapCanvas().refresh()
        except Exception:
            pass  # nosec B110

    def _rebuild_dim_rumo(self, layer: QgsVectorLayer, modo: str | None = None, min_segment_len: float | None = None, label_gms: bool | None = None):
        """Recria a camada de rumo mantendo vínculo por FID."""
        if not bool(layer.customProperty("dim/rumo", False)):
            return

        src_id = layer.customProperty("dim/src_layer_id", "")
        src = QgsProject.instance().mapLayer(src_id)

        if not isinstance(src, QgsVectorLayer):
            self.mostrar_mensagem(self.tr("Camada de origem não encontrada para esta dimensão de rumo."), "Aviso")
            return

        if modo is None:
            modo = str(layer.customProperty("dim/rumo_modo", self._azimute_modo_atual()))

        if min_segment_len is None:
            min_segment_len = float(layer.customProperty("dim/min_segment_len", 0.0))

        if label_gms is None:
            label_gms = bool(layer.customProperty("dim/label_gms", self._usar_angulos_em_gms()))

        modo = str(modo).lower()

        layer.setCustomProperty("dim/rumo_modo", modo)
        layer.setCustomProperty("dim/min_segment_len", float(min_segment_len))
        layer.setCustomProperty("dim/label_gms", bool(label_gms))

        layer.setReadOnly(False)
        prov = layer.dataProvider()

        prov.deleteFeatures([f.id() for f in layer.getFeatures()])
        self._rumo_conn_links.clear()

        crs = src.crs()

        for feat in src.getFeatures():
            rumo_feats = self._gera_dim_rumo_para_feat(
                feat,
                crs,
                modo=modo,
                min_segment_len=float(min_segment_len),
                label_gms=bool(label_gms))

            ok, new_feats = prov.addFeatures(rumo_feats)
            self._rumo_conn_links[feat.id()] = [f.id() for f in new_feats]

        layer.setReadOnly(True)
        layer.triggerRepaint()

        try:
            self.iface.mapCanvas().refresh()
        except Exception:
            pass  # nosec B110

    def _on_rumo_mode_changed_selected(self, *_):
        """Recalcula a camada de rumo selecionada ao alternar Verdadeiro/Plano."""
        layer = self._get_selected_dim_layer()

        if not layer or not bool(layer.customProperty("dim/rumo", False)):
            return

        modo = self._azimute_modo_atual()
        layer.setCustomProperty("dim/rumo_modo", modo)

        self._rebuild_dim_rumo(
            layer,
            modo=modo,
            min_segment_len=float(layer.customProperty("dim/min_segment_len", self.doubleSpinBoxTamanhoM.value())),
            label_gms=bool(layer.customProperty("dim/label_gms", self._usar_angulos_em_gms())))

    def _on_azimute_inverter_direcao_changed(self, checked):
        """Recalcula a camada de azimute ao inverter a direção."""
        layer = self._get_selected_dim_layer()

        if not layer or not bool(layer.customProperty("dim/azimute", False)):
            return

        layer.setCustomProperty("dim/inverter_direcao", bool(checked))

        self._rebuild_dim_azimute(
            layer,
            modo=str(layer.customProperty("dim/azimute_modo", self._azimute_modo_atual())),
            min_segment_len=float(layer.customProperty("dim/min_segment_len", self.doubleSpinBoxTamanhoM.value())),
            label_gms=bool(layer.customProperty("dim/label_gms", self._usar_angulos_em_gms())))

    def _on_rumo_inverter_direcao_changed(self, checked):
        """Recalcula a camada de rumo ao inverter a direção."""
        layer = self._get_selected_dim_layer()

        if not layer or not bool(layer.customProperty("dim/rumo", False)):
            return

        layer.setCustomProperty("dim/inverter_direcao", bool(checked))

        self._rebuild_dim_rumo(
            layer,
            modo=str(layer.customProperty("dim/rumo_modo", self._azimute_modo_atual())),
            min_segment_len=float(layer.customProperty("dim/min_segment_len", self.doubleSpinBoxTamanhoM.value())),
            label_gms=bool(layer.customProperty("dim/label_gms", self._usar_angulos_em_gms())))

    def _rumo_on_geom_changed(self, fid, new_geom):
        """Atualiza o rumo quando a geometria da feição de origem é modificada."""
        layer = self._rumo_layer()
        src = self._rumo_conn_srcLayer

        if not layer or not src:
            return

        modo = str(layer.customProperty("dim/rumo_modo", self._azimute_modo_atual()))
        min_segment_len = float(layer.customProperty("dim/min_segment_len", self.doubleSpinBoxTamanhoM.value()))
        label_gms = bool(layer.customProperty("dim/label_gms", self._usar_angulos_em_gms()))

        layer.setReadOnly(False)
        prov = layer.dataProvider()
        prov.deleteFeatures(self._rumo_conn_links.get(fid, []))

        feat = src.getFeature(fid)

        rumo_feats = self._gera_dim_rumo_para_feat(
            feat,
            src.crs(),
            modo=modo,
            min_segment_len=min_segment_len,
            label_gms=label_gms)

        ok, new_feats = prov.addFeatures(rumo_feats)
        self._rumo_conn_links[fid] = [f.id() for f in new_feats]

        layer.setReadOnly(True)
        layer.triggerRepaint()

    def _rumo_on_feat_added(self, fid):
        """Cria rumo quando nova feição é adicionada à camada de origem."""
        layer = self._rumo_layer()
        src = self._rumo_conn_srcLayer

        if not layer or not src:
            return

        modo = str(layer.customProperty("dim/rumo_modo", self._azimute_modo_atual()))
        min_segment_len = float(layer.customProperty("dim/min_segment_len", self.doubleSpinBoxTamanhoM.value()))
        label_gms = bool(layer.customProperty("dim/label_gms", self._usar_angulos_em_gms()))

        feat = src.getFeature(fid)

        rumo_feats = self._gera_dim_rumo_para_feat(
            feat,
            src.crs(),
            modo=modo,
            min_segment_len=min_segment_len,
            label_gms=label_gms)

        layer.setReadOnly(False)
        prov = layer.dataProvider()

        ok, new_feats = prov.addFeatures(rumo_feats)
        self._rumo_conn_links[fid] = [f.id() for f in new_feats]

        layer.setReadOnly(True)
        layer.triggerRepaint()

    def _rumo_on_feat_deleted(self, fid):
        """Remove o rumo associado quando uma feição de origem é deletada."""
        layer = self._rumo_layer()

        if not layer:
            return

        layer.setReadOnly(False)
        prov = layer.dataProvider()

        prov.deleteFeatures(self._rumo_conn_links.pop(fid, []))

        layer.setReadOnly(True)
        layer.triggerRepaint()

    def _az_layer(self):
        """Retorna a camada de azimute conectada, ou None se não existir."""
        return QgsProject.instance().mapLayer(getattr(self, "_azi_conn_layer_id", ""))

    def _azimute_modo_atual(self) -> str:
        """Retorna 'plano' ou 'verdadeiro' conforme os radioButtons da UI."""
        rb_plano = getattr(self, "radioButtonPlano", None)
        if rb_plano is not None and rb_plano.isChecked():
            return "plano"
        return "verdadeiro"

    def _formatar_rotulo_azimute(self, azimute_graus: float, modo: str, usar_gms: bool | None = None) -> str:
        """Formata o rótulo do azimute, respeitando checkBoxAngulo."""
        if usar_gms is None:
            usar_gms = self._usar_angulos_em_gms()

        ang_txt = self._formatar_angulo_gms(azimute_graus) if usar_gms else f"{float(azimute_graus):.4f}°"
        prefixo = "AzP" if str(modo).lower() == "plano" else "AzV"
        return f"{prefixo} = {ang_txt}"

    def _segment_length_mu_or_m(self, p1: QgsPointXY, p2: QgsPointXY, crs: QgsCoordinateReferenceSystem) -> float:
        """Comprimento do segmento. Em CRS geográfico mede em metros; em CRS projetado mede na unidade do mapa."""
        geom = QgsGeometry.fromPolylineXY([QgsPointXY(p1), QgsPointXY(p2)])

        try:
            if crs and crs.isGeographic():
                da = QgsDistanceArea()
                da.setSourceCrs(crs, QgsProject.instance().transformContext())
                da.setEllipsoid(QgsProject.instance().crs().ellipsoidAcronym())
                return float(da.measureLength(geom))
        except Exception:
            pass  # nosec B110

        return float(geom.length())

    def _ring_area_assinada(self, pts: list[QgsPointXY]) -> float:
        """
        Retorna a área assinada do anel.
        Em coordenadas XY usuais:
        - área > 0: anti-horário
        - área < 0: horário
        """
        if not pts or len(pts) < 3:
            return 0.0

        area2 = 0.0
        n = len(pts)

        for i in range(n):
            p1 = pts[i]
            p2 = pts[(i + 1) % n]
            area2 += p1.x() * p2.y() - p2.x() * p1.y()

        return area2 * 0.5

    def _ring_circular_desde_norte_oeste(self, ring, *, sentido_horario: bool = True) -> list[QgsPointXY]:
        """
        Organiza o anel para cálculo circular de Azimute/Rumo.

        Regras:
        - remove ponto final duplicado;
        - força sentido horário ou anti-horário;
        - inicia no vértice mais ao Norte;
        - se houver empate no Norte, inicia no mais à esquerda.
        """
        pts = self._ring_sem_fechamento(ring)

        if len(pts) < 2:
            return pts

        area = self._ring_area_assinada(pts)

        # area > 0 = anti-horário; area < 0 = horário
        if sentido_horario and area > 0:
            pts = list(reversed(pts))
        elif not sentido_horario and area < 0:
            pts = list(reversed(pts))

        # Vértice inicial: mais ao Norte; empate: mais à esquerda
        start_idx = min(
            range(len(pts)),
            key=lambda i: (-pts[i].y(), pts[i].x()))

        return pts[start_idx:] + pts[:start_idx]

    def _ring_sem_fechamento(self, ring) -> list[QgsPointXY]:
        """Remove o último ponto se ele repetir o primeiro ponto do anel."""
        pts = [QgsPointXY(p) for p in ring]

        if len(pts) > 1:
            p0, pN = pts[0], pts[-1]
            if abs(p0.x() - pN.x()) <= 1e-12 and abs(p0.y() - pN.y()) <= 1e-12:
                pts = pts[:-1]

        return pts

    def _orientar_segmento_azimute_por_norte_oeste(self, p1: QgsPointXY, p2: QgsPointXY) -> tuple[QgsPointXY, QgsPointXY]:
        """
        Orienta um segmento para cálculo/desenho de azimute:
        - início no ponto mais ao Norte;
        - se os dois pontos estiverem alinhados ao Norte/Sul, início no mais à esquerda.
        """
        p1 = QgsPointXY(p1)
        p2 = QgsPointXY(p2)

        eps = 1e-12

        if p1.y() > p2.y() + eps:
            return p1, p2
        if p2.y() > p1.y() + eps:
            return p2, p1

        # Mesmo Y: começa pelo mais à esquerda
        if p1.x() <= p2.x():
            return p1, p2
        return p2, p1

    def _segmento_azimute_valido(self, p1: QgsPointXY, p2: QgsPointXY, crs: QgsCoordinateReferenceSystem, min_segment_len: float = 0.0) -> bool:
        """Valida segmento de azimute, incluindo comprimento mínimo do doubleSpinBoxTamanhoM."""
        if abs(p1.x() - p2.x()) <= 1e-12 and abs(p1.y() - p2.y()) <= 1e-12:
            return False

        if float(min_segment_len) > 0:
            return self._segment_length_mu_or_m(p1, p2, crs) >= float(min_segment_len)

        return True

    def _selecionar_segmento_azimute(self, ring, crs: QgsCoordinateReferenceSystem, min_segment_len: float = 0.0):
        """
        Compatibilidade: retorna o primeiro segmento válido orientado pelo critério Norte/Oeste.

        A geração principal do azimute agora percorre TODOS os lados em
        `_gera_dim_azimute_para_feat`.
        """
        pts = self._ring_sem_fechamento(ring)

        if len(pts) < 2:
            return None

        for i in range(len(pts)):
            p1 = pts[i]
            p2 = pts[(i + 1) % len(pts)]

            if not self._segmento_azimute_valido(p1, p2, crs, min_segment_len):
                continue

            return self._orientar_segmento_azimute_por_norte_oeste(p1, p2)

        return None

    def _calcular_azimute_plano(self, p1: QgsPointXY, p2: QgsPointXY) -> float:
        """Azimute plano: 0° no Norte, 90° no Leste, no sistema de coordenadas da camada."""
        dx = p2.x() - p1.x()
        dy = p2.y() - p1.y()

        if abs(dx) <= 1e-15 and abs(dy) <= 1e-15:
            return 0.0

        return (math.degrees(math.atan2(dx, dy)) + 360.0) % 360.0

    def _calcular_azimute_verdadeiro(self, p1: QgsPointXY, p2: QgsPointXY, crs: QgsCoordinateReferenceSystem) -> float:
        """
        Azimute verdadeiro usando o motor geodésico do QGIS.

        Isso tende a coincidir melhor com o valor de Rolamento medido diretamente
        no QGIS, pois usa QgsDistanceArea com CRS de origem e elipsoide do projeto.
        """
        try:
            src_crs = crs if crs and crs.isValid() else QgsProject.instance().crs()

            da = QgsDistanceArea()
            da.setSourceCrs(src_crs, QgsProject.instance().transformContext())

            # Usa o elipsoide configurado no projeto; se não houver, usa WGS84.
            try:
                ellipsoid = QgsProject.instance().ellipsoid()
                if ellipsoid:
                    da.setEllipsoid(ellipsoid)
                else:
                    da.setEllipsoid("WGS84")
            except Exception:
                try:
                    da.setEllipsoid(src_crs.ellipsoidAcronym())
                except Exception:
                    da.setEllipsoid("WGS84")

   # bearing retorna em radianos.
            bearing_rad = da.bearing(QgsPointXY(p1), QgsPointXY(p2))

            return (math.degrees(bearing_rad) + 360.0) % 360.0

        except Exception:
   # fallback seguro para não travar o plugin
            return self._calcular_azimute_plano(p1, p2)

    def _gera_dim_azimute_para_feat(self, feat: QgsFeature, crs: QgsCoordinateReferenceSystem, *, modo: str, min_segment_len: float = 0.0, label_gms: bool = False) -> list[QgsFeature]:
        """
        Gera dimensões de azimute para TODOS os lados externos do polígono,
        em percurso circular.

        Regra principal:
        - começa no vértice mais ao Norte;
        - empate: mais à esquerda;
        - percorre o polígono no sentido horário;
        - radioButtonPlano inverte a direção de cálculo;
        - checkbox 'Inverter direção' inverte novamente a direção de cálculo;
        - checkBoxDirecao controla apenas dentro/fora visual.
        """
        geom = feat.geometry()

        if not geom or geom.isEmpty():
            return []

        modo = str(modo).lower()
        feats_dim = []
        parts = geom.asMultiPolygon() if geom.isMultipart() else [geom.asPolygon()]

        # Padrão = fora
        # Marcado "Inverter posição" = dentro
        want_outside = not bool(self.checkBoxDirecao.isChecked())

        for part in parts:
            if not part:
                continue

            ring = part[0]  # apenas anel externo

   # Aqui está o coração do ajuste:
   # antes cada lado era orientado individualmente;
   # agora o polígono é percorrido circularmente.
            pts = self._ring_circular_desde_norte_oeste(
                ring,
                sentido_horario=True)

            if len(pts) < 2:
                continue

            for i in range(len(pts)):
                p_start = QgsPointXY(pts[i])
                p_end = QgsPointXY(pts[(i + 1) % len(pts)])

                if not self._segmento_azimute_valido(
                        p_start,
                        p_end,
                        crs,
                        min_segment_len=min_segment_len):
                    continue

       # Direção-base circular:
       # - Verdadeiro: percorre no sentido horário
       # - Plano: por regra anterior, inverte a direção
                if modo == "plano":
                    p_calc_1, p_calc_2 = p_end, p_start
                else:
                    p_calc_1, p_calc_2 = p_start, p_end

       # Checkbox "Inverter direção" do bloco Azimute/Rumo:
       # inverte a direção de cálculo, não a posição visual.
                if self._azimute_inverter_direcao_extra():
                    p_calc_1, p_calc_2 = p_calc_2, p_calc_1

                if modo == "plano":
                    az = self._calcular_azimute_plano(p_calc_1, p_calc_2)
                else:
                    az = self._calcular_azimute_verdadeiro(p_calc_1, p_calc_2, crs)

       # Geometria visual: mantém tudo do mesmo lado, dentro/fora.
                p_draw_1, p_draw_2 = self._orientar_segmento_para_mesmo_lado(
                    geom,
                    p_calc_1,
                    p_calc_2,
                    want_outside=want_outside,
                    crs=crs)

                f = QgsFeature()
                f.setGeometry(QgsGeometry.fromPolylineXY([
                    QgsPointXY(p_draw_1),
                    QgsPointXY(p_draw_2)]))
                f.setAttributes([
                    round(az, 6),
                    self._formatar_rotulo_azimute(az, modo, label_gms)])
                feats_dim.append(f)

        return feats_dim

    def criar_camada_dimensionamento_azimute_conectada(self):
        """Cria uma camada conectada de dimensão de azimute a partir da camada poligonal selecionada."""
        layer_id = self.comboBoxCamada.currentData()

        if not layer_id:
            self.mostrar_mensagem(self.tr("Selecione uma camada de polígono."), "Erro")
            return

        src_layer = QgsProject.instance().mapLayer(layer_id)

        if not self._validar_crs_utm_para_dimensionamento(src_layer):
            return

        if not isinstance(src_layer, QgsVectorLayer):
            self.mostrar_mensagem(self.tr("Camada inválida selecionada."), "Erro")
            return

        try:
            if self._azi_conn_srcLayer:
                self._azi_conn_srcLayer.geometryChanged.disconnect(self._azi_on_geom_changed)
                self._azi_conn_srcLayer.featureAdded.disconnect(self._azi_on_feat_added)
                self._azi_conn_srcLayer.featureDeleted.disconnect(self._azi_on_feat_deleted)
        except Exception:
            pass  # nosec B110

        modo = self._azimute_modo_atual()
        min_segment_len = float(self.doubleSpinBoxTamanhoM.value())
        label_gms = self._usar_angulos_em_gms()

        chk = self.findChild(QCheckBox, "checkBoxSeleciona")
        feats_src = list(src_layer.getSelectedFeatures()) if (chk and chk.isChecked()) else list(src_layer.getFeatures())

        if not feats_src:
            self.mostrar_mensagem(self.tr("Nenhuma feição encontrada para dimensionar o azimute."), "Erro")
            return

        crs = src_layer.crs()

        layer = self._criar_camada_dim_base("Dim_Azimute", crs, [], editavel=False)

        layer.setCustomProperty("dim/azimute", True)
        layer.setCustomProperty("dim/connected", True)
        layer.setCustomProperty("dim/src_layer_id", src_layer.id())
        layer.setCustomProperty("dim/azimute_modo", modo)
        layer.setCustomProperty("dim/min_segment_len", min_segment_len)
        layer.setCustomProperty("dim/label_gms", bool(label_gms))
        layer.setCustomProperty("dim/inverter_direcao", self._azimute_inverter_direcao_extra())

        try:
            arrow = float(self.doubleSpinBoxTamanho.value())
            tick = float(self.doubleSpinBoxAux.value())
            text = float(self.doubleSpinBoxTexto.value())
            afast = float(self.doubleSpinBoxRecuo.value())
        except Exception:
            arrow, tick, text, afast = 2.5, 4.0, 8.0, 0.2

        self._apply_dim_sizes(layer, arrow, tick, text, afast_mu=afast)
        layer.setCustomProperty("dim/recuo_ui", afast)
        self._azi_conn_layer = layer
        self._azi_conn_layer_id = layer.id()
        self._azi_conn_srcLayer = src_layer
        self._azi_conn_links = {}

        prov = layer.dataProvider()

        for feat in feats_src:
            az_feats = self._gera_dim_azimute_para_feat(
                feat,
                crs,
                modo=modo,
                min_segment_len=min_segment_len,
                label_gms=label_gms)
            ok, new_feats = prov.addFeatures(az_feats)
            self._azi_conn_links[feat.id()] = [f.id() for f in new_feats]

        layer.setReadOnly(True)
        layer.triggerRepaint()

        src_layer.geometryChanged.connect(self._azi_on_geom_changed)
        src_layer.featureAdded.connect(self._azi_on_feat_added)
        src_layer.featureDeleted.connect(self._azi_on_feat_deleted)

        self.mostrar_mensagem(self.tr("Dimensão de azimute criada."), "Sucesso")
        self.layer_dimensoes = layer
        self.atualizar_treeViewCamadas()

        try:
            self.iface.mapCanvas().refresh()
        except Exception:
            pass  # nosec B110

    def _rebuild_dim_azimute(self, layer: QgsVectorLayer, modo: str | None = None, min_segment_len: float | None = None, label_gms: bool | None = None):
        """Recria a camada de azimute mantendo vínculo por FID."""
        if not bool(layer.customProperty("dim/azimute", False)):
            return

        src_id = layer.customProperty("dim/src_layer_id", "")
        src = QgsProject.instance().mapLayer(src_id)

        if not isinstance(src, QgsVectorLayer):
            self.mostrar_mensagem(self.tr("Camada de origem não encontrada para esta dimensão de azimute."), "Aviso")
            return

        if modo is None:
            modo = str(layer.customProperty("dim/azimute_modo", self._azimute_modo_atual()))

        if min_segment_len is None:
            min_segment_len = float(layer.customProperty("dim/min_segment_len", 0.0))

        if label_gms is None:
            label_gms = bool(layer.customProperty("dim/label_gms", self._usar_angulos_em_gms()))

        modo = str(modo).lower()

        layer.setCustomProperty("dim/azimute_modo", modo)
        layer.setCustomProperty("dim/min_segment_len", float(min_segment_len))
        layer.setCustomProperty("dim/label_gms", bool(label_gms))

        layer.setReadOnly(False)
        prov = layer.dataProvider()

        prov.deleteFeatures([f.id() for f in layer.getFeatures()])
        self._azi_conn_links.clear()

        crs = src.crs()

        for feat in src.getFeatures():
            az_feats = self._gera_dim_azimute_para_feat(
                feat,
                crs,
                modo=modo,
                min_segment_len=float(min_segment_len),
                label_gms=bool(label_gms))

            ok, new_feats = prov.addFeatures(az_feats)
            self._azi_conn_links[feat.id()] = [f.id() for f in new_feats]

        layer.setReadOnly(True)
        layer.triggerRepaint()

        try:
            self.iface.mapCanvas().refresh()
        except Exception:
            pass  # nosec B110

    def _on_azimute_mode_changed_selected(self, *_):
        """Recalcula a camada de azimute selecionada ao alternar Verdadeiro/Plano."""
        layer = self._get_selected_dim_layer()

        if not layer or not bool(layer.customProperty("dim/azimute", False)):
            return

        modo = self._azimute_modo_atual()
        layer.setCustomProperty("dim/azimute_modo", modo)

        self._rebuild_dim_azimute(
            layer,
            modo=modo,
            min_segment_len=float(layer.customProperty("dim/min_segment_len", self.doubleSpinBoxTamanhoM.value())),
            label_gms=bool(layer.customProperty("dim/label_gms", self._usar_angulos_em_gms())))

    def _azi_on_geom_changed(self, fid, new_geom):
        """Atualiza o azimute quando a geometria da feição de origem é modificada."""
        layer = self._az_layer()
        src = self._azi_conn_srcLayer

        if not layer or not src:
            return

        modo = str(layer.customProperty("dim/azimute_modo", self._azimute_modo_atual()))
        min_segment_len = float(layer.customProperty("dim/min_segment_len", self.doubleSpinBoxTamanhoM.value()))
        label_gms = bool(layer.customProperty("dim/label_gms", self._usar_angulos_em_gms()))

        layer.setReadOnly(False)
        prov = layer.dataProvider()
        prov.deleteFeatures(self._azi_conn_links.get(fid, []))

        feat = src.getFeature(fid)

        az_feats = self._gera_dim_azimute_para_feat(
            feat,
            src.crs(),
            modo=modo,
            min_segment_len=min_segment_len,
            label_gms=label_gms)

        ok, new_feats = prov.addFeatures(az_feats)
        self._azi_conn_links[fid] = [f.id() for f in new_feats]

        layer.setReadOnly(True)
        layer.triggerRepaint()

    def _azi_on_feat_added(self, fid):
        """Cria azimute quando nova feição é adicionada à camada de origem."""
        layer = self._az_layer()
        src = self._azi_conn_srcLayer

        if not layer or not src:
            return

        modo = str(layer.customProperty("dim/azimute_modo", self._azimute_modo_atual()))
        min_segment_len = float(layer.customProperty("dim/min_segment_len", self.doubleSpinBoxTamanhoM.value()))
        label_gms = bool(layer.customProperty("dim/label_gms", self._usar_angulos_em_gms()))

        feat = src.getFeature(fid)

        az_feats = self._gera_dim_azimute_para_feat(
            feat,
            src.crs(),
            modo=modo,
            min_segment_len=min_segment_len,
            label_gms=label_gms)

        layer.setReadOnly(False)
        prov = layer.dataProvider()

        ok, new_feats = prov.addFeatures(az_feats)
        self._azi_conn_links[fid] = [f.id() for f in new_feats]

        layer.setReadOnly(True)
        layer.triggerRepaint()

    def _azi_on_feat_deleted(self, fid):
        """Remove o azimute associado quando uma feição de origem é deletada."""
        layer = self._az_layer()

        if not layer:
            return

        layer.setReadOnly(False)
        prov = layer.dataProvider()

        prov.deleteFeatures(self._azi_conn_links.pop(fid, []))

        layer.setReadOnly(True)
        layer.triggerRepaint()

    def _ponto_em_geom(self, geom: QgsGeometry, pt: QgsPointXY) -> bool:
        """Retorna True se o ponto estiver dentro da geometria."""
        try:
            return geom.contains(QgsGeometry.fromPointXY(QgsPointXY(pt)))
        except Exception:
            return False

    def _dist_teste_lado_mu(self, p1: QgsPointXY, p2: QgsPointXY, crs: QgsCoordinateReferenceSystem) -> float:
        """
        Distância de teste, em unidades do mapa, para verificar se um lado está
        para dentro ou para fora do polígono.
        Funciona corretamente em CRS projetado e geográfico.
        """
        try:
            recuo_ui = abs(float(self.doubleSpinBoxRecuo.value()))
        except Exception:
            recuo_ui = 0.2

        mid = QgsPointXY((p1.x() + p2.x()) / 2.0, (p1.y() + p2.y()) / 2.0)
        recuo_mu = self._recuo_ui_para_map_units(crs, recuo_ui, mid)

        seg_len_mu = QgsGeometry.fromPolylineXY([QgsPointXY(p1), QgsPointXY(p2)]).length()

        if crs and crs.isGeographic():
            eps = max(recuo_mu * 0.25, seg_len_mu * 0.02, 1e-8)
        else:
            eps = max(recuo_mu * 0.25, seg_len_mu * 0.02, 0.05)

        return max(recuo_mu + eps, eps)

    def _orientar_segmento_para_mesmo_lado(self, geom_poligono: QgsGeometry, p1: QgsPointXY, p2: QgsPointXY, want_outside: bool, crs: QgsCoordinateReferenceSystem) -> tuple[QgsPointXY, QgsPointXY]:
        """
        Ajusta a orientação da geometria do segmento para que o offset positivo
        fique sempre do mesmo lado do polígono.

        want_outside = True  -> força tudo para fora
        want_outside = False -> força tudo para dentro
        """
        p1 = QgsPointXY(p1)
        p2 = QgsPointXY(p2)

        dx = p2.x() - p1.x()
        dy = p2.y() - p1.y()
        L = math.hypot(dx, dy)

        if L <= 1e-12:
            return p1, p2

        # normal à esquerda da direção p1 -> p2
        nx = -dy / L
        ny =  dx / L

        d = self._dist_teste_lado_mu(p1, p2, crs)

        mid = QgsPointXY((p1.x() + p2.x()) / 2.0, (p1.y() + p2.y()) / 2.0)

        def _testar(dist):
            pt_left  = QgsPointXY(mid.x() + nx * dist, mid.y() + ny * dist)
            pt_right = QgsPointXY(mid.x() - nx * dist, mid.y() - ny * dist)
            left_inside  = self._ponto_em_geom(geom_poligono, pt_left)
            right_inside = self._ponto_em_geom(geom_poligono, pt_right)
            return left_inside, right_inside

        left_inside, right_inside = _testar(d)

        # fallback se inconclusivo
        if left_inside == right_inside:
            left_inside, right_inside = _testar(d * 3.0)

        if left_inside == right_inside:
            return p1, p2

        # neste símbolo/renderer, o offset positivo está ficando à DIREITA da direção
        positive_side_is_inside = right_inside

        # queremos fora e positivo está dentro -> inverte
        # queremos dentro e positivo está fora -> inverte
        need_reverse = (want_outside == positive_side_is_inside)

        if need_reverse:
            return QgsPointXY(p2), QgsPointXY(p1)

        return QgsPointXY(p1), QgsPointXY(p2)

    def _get_checkBox_inverter_direcao_azimute(self):
        """Retorna o checkbox de inversão de direção usado por Azimute e Rumo."""
        nomes_possiveis = (
            "checkBoxInverterDirecao",
            "checkBoxInverterDirecaoAzimute",
            "checkBoxAzimuteInverterDirecao",
            "checkBoxDirecaoAzimute",
            "checkBoxInverteDirecao")

        for nome in nomes_possiveis:
            chk = getattr(self, nome, None)

            if isinstance(chk, QCheckBox):
                return chk

            chk = self.findChild(QCheckBox, nome)

            if isinstance(chk, QCheckBox):
                return chk

        textos_validos = {
            "inverter direção",
            "inverter direcao",
            "invert direction",
            "reverse direction"}

        for chk in self.findChildren(QCheckBox):
            if chk.text().strip().lower() in textos_validos:
                return chk

        return None

    def _azimute_inverter_direcao_extra(self) -> bool:
        """Retorna True se o checkbox 'Inverter direção' do azimute estiver marcado."""
        chk = self._get_checkBox_inverter_direcao_azimute()
        return bool(chk and chk.isChecked())

    def _gerar_nome_unico(self, nome_base):
        """Gera nome único para camada, evitando duplicidade no projeto."""
        layers_names = [layer.name() for layer in QgsProject.instance().mapLayers().values()]
        nome = nome_base
        contador = 1
        while nome in layers_names:
            nome = f"{nome_base}_{contador}"
            contador += 1
        return nome

    def closeEvent(self, event):
        """Desconecta atualização automática ao fechar o diálogo."""
        super().closeEvent(event)

    def configurar_campo_oculto(self, camada: QgsVectorLayer, nomes: list[str]):
        """
        Oculta os campos dados tanto na tabela de atributos quanto no formulário de edição.
        """
        for nome in nomes:
            idx = camada.fields().indexOf(nome)
            if idx != -1:
                setup = QgsEditorWidgetSetup("Hidden", {})
                camada.setEditorWidgetSetup(idx, setup)

    def atualizar_dimensao_atribs(self, camada: QgsVectorLayer, fid: int):
        """
        Calcula o comprimento da feição 'fid', grava nos campos
        'comprimento' (numérico) e 'label' (string).
        """
        f = camada.getFeature(fid)

        # Comprimento em unidades do layer/project
        da = QgsDistanceArea()
        if camada.crs().isGeographic():
            da.setSourceCrs(camada.crs(), QgsProject.instance().transformContext())
            da.setEllipsoid(QgsProject.instance().crs().ellipsoidAcronym())
            comp = da.measureLength(f.geometry())      # metros
        else:
            comp = f.geometry().length()      # mesma unidade do layer

        comp = round(comp, 3)                 # 3 casas

        # Índices de campos
        idx_comp = camada.fields().indexOf("comprimento")
        idx_lab  = camada.fields().indexOf("label")

        # Muda valores
        camada.changeAttributeValue(fid, idx_comp, comp)
        camada.changeAttributeValue(fid, idx_lab, f"{comp:.2f} m")

        # Etiqueta é configurada uma única vez
        if not getattr(camada, "etiquetas_configuradas", False):
            self.configurar_etiquetas(camada)
            camada.etiquetas_configuradas = True

    def _get_rendered_offset_mu(self, layer: QgsVectorLayer, default_val: float = 0.0) -> float:
        """Obtém o valor de offset (afastamento em map units) aplicado ao símbolo da camada, com fallback padrão."""
        try:
            r = layer.renderer()
            if r:
                sym = r.symbol()
                if sym and sym.symbolLayerCount() > 0:
                    sll0 = sym.symbolLayer(0)
                    if hasattr(sll0, "offset"):
                        return float(sll0.offset())   # valor com sinal
        except Exception:
            pass  # nosec B110
        return float(default_val)

    def configurar_etiquetas(self, camada: QgsVectorLayer, sinal_lado: int | None = None, distancia_mu: float = 0.0):
        """Configura os rótulos da camada de dimensionamento para exibir o campo 'label', alinhados à linha, no mesmo lado e afastamento definidos pelo símbolo."""
        pal = QgsPalLayerSettings()
        pal.fieldName = 'label'
        pal.placement = QgsPalLayerSettings.Placement.Line

        # >>> lado/distância vindos do offset real do símbolo
        off = self._get_rendered_offset_mu(camada, default_val=(distancia_mu * (1 if (sinal_lado or 1) > 0 else -1)))
        pal.dist = abs(off)
        pal.distUnits = QgsUnitTypes.RenderUnit.RenderMapUnits
        pal.placementFlags = (QgsPalLayerSettings.BelowLine if off >= 0 else QgsPalLayerSettings.AboveLine)

        fmt = QgsTextFormat()
        fmt.setSize(8)
        fmt.setColor(QColor("black"))
        pal.setFormat(fmt)

        camada.setLabeling(QgsVectorLayerSimpleLabeling(pal))
        camada.setLabelsEnabled(True)

    def criar_camada_dimensionamento(self):
        """
        Cria uma camada de dimensionamento do tipo 'Livre',
        permitindo que o usuário insira manualmente as linhas de cota.
        A camada é adicionada ao grupo 'Dimensionamento' e entra em modo edição.
        """
        if not self._validar_crs_utm_para_dimensionamento():
            return

        crs = self.iface.mapCanvas().mapSettings().destinationCrs()
        # Nenhuma feição ainda — camada vazia mas editável
        layer = self._criar_camada_dim_base("Dim_Livre", crs, [], editavel=True)

        # Suprime o formulário de edição
        cfg = layer.editFormConfig()
        cfg.setSuppress(QgsEditFormConfig.FeatureFormSuppress.SuppressOn)
        layer.setEditFormConfig(cfg)

        # Atualiza atributos ao adicionar feições
        layer.featureAdded.connect(lambda fid: self.atualizar_dimensao_atribs(layer, fid))

        # Deixar ativa, entrar em edição e ligar a ferramenta de captura
        try:
   # 1) torna a nova camada a camada ativa
            self.iface.setActiveLayer(layer)
        except Exception:
            pass  # nosec B110

        # 2) garante modo de edição
        if not layer.isEditable():
            layer.startEditing()

        # 3) ativa a ferramenta de digitalizar (adicionar feição de linha)
        #    Em QGIS 3.x, actionAddFeature usa o tipo da camada ativa.
        try:
            self.iface.actionAddFeature().trigger()
        except Exception:
   # fallback para builds que ainda expõem ações específicas por geometria
            try:
                self.iface.actionAddPolyline().trigger()
            except Exception:
                pass  # nosec B110

        self.mostrar_mensagem(self.tr("Camada de dimensionamento criada com sucesso (edição e digitalização ativadas)."), "Sucesso")
        self.layer_dimensoes = layer

        self.atualizar_treeViewCamadas()  # atualiza a lista

    def _dim_on_geom_changed(self, fid, new_geom):
        """Atualiza as dimensões ligadas quando a geometria de uma feição da camada de origem é modificada."""
        layer = self._dim_layer()
        if not layer or not self._dim_conn_srcLayer:
            return

        layer.setReadOnly(False) # 🔓 destrava

        prov = layer.dataProvider()
        prov.deleteFeatures(self._dim_conn_links.get(fid, []))

        feat = self._dim_conn_srcLayer.getFeature(fid)
        min_len = self.doubleSpinBoxTamanhoM.value()
        feats_dim = self._gera_dimensoes_para_feat(feat, layer.crs(), comprimento_min=min_len)

        ok, feats_dim = prov.addFeatures(feats_dim)
        self._dim_conn_links[fid] = [f.id() for f in feats_dim]

        layer.triggerRepaint()
        layer.setReadOnly(True) # 🔒 trava de novo

    def _dim_on_feat_added(self, fid):
        """Cria e adiciona dimensões correspondentes quando uma nova feição é inserida na camada de origem."""
        layer = self._dim_layer()
        if not layer:
            return

        # Guarda contra duplicação: se geometryChanged já gerou as dimensões, não refaz
        if fid in self._dim_conn_links and self._dim_conn_links.get(fid):
            return

        prov = layer.dataProvider()  # provedor da camada de dimensões
        feat = self._dim_conn_srcLayer.getFeature(fid)  # feição recém adicionada da camada de origem
        min_len = self.doubleSpinBoxTamanhoM.value()  # comprimento mínimo configurado no spinBox

        # gera as linhas de dimensão para a feição adicionada
        feats_dim = self._gera_dimensoes_para_feat(feat, layer.crs(), comprimento_min=min_len)

        # adiciona as dimensões à camada
        ok, feats_dim = prov.addFeatures(feats_dim)

        # registra os FIDs das dimensões criadas, vinculando ao fid da feição origem
        self._dim_conn_links[fid] = [f.id() for f in feats_dim]

        layer.triggerRepaint() # força o redesenho da camada

    def _dim_layer(self):
        """Retorna a camada de dimensão conectada ou None se não existir mais."""
        return QgsProject.instance().mapLayer(getattr(self, "_dim_conn_layer_id", ""))

    def _dim_on_feat_deleted(self, fid):
        """Remove as dimensões associadas quando uma feição é deletada da camada de origem."""
        layer = self._dim_layer()
        if not layer:
            return

        prov = layer.dataProvider()
        prov.deleteFeatures(self._dim_conn_links.pop(fid, []))

        layer.triggerRepaint()

    def criar_camada_dimensionamento_conectada(self):
        """
        Gera dimensões conectadas às feições de uma camada poligonal.
        Se checkBoxSeleciona marcado → só feições selecionadas, senão todas.
        Dimensões acompanham alterações em tempo real.
        """
        layer_id = self.comboBoxCamada.currentData()
        if not layer_id:
            self.mostrar_mensagem(self.tr("Selecione uma camada de polígono."), "Erro")
            return
        src_layer = QgsProject.instance().mapLayer(layer_id)

        src_layer = QgsProject.instance().mapLayer(layer_id)

        if not isinstance(src_layer, QgsVectorLayer):
            self.mostrar_mensagem(self.tr("Camada inválida selecionada."), "Erro")
            return

        if not self._validar_crs_utm_para_dimensionamento(src_layer):
            return

        # Escolhe feições origem
        chk = self.findChild(QCheckBox, 'checkBoxSeleciona')
        feats_src = list(src_layer.getSelectedFeatures()) if chk and chk.isChecked() else list(src_layer.getFeatures())
        if not feats_src:
            self.mostrar_mensagem(self.tr("Nenhuma feição encontrada para dimensionar."), "Erro")
            return

        crs = src_layer.crs()

        # Cria camada base (não editável)
        layer = self._criar_camada_dim_base("Dim_Conectada", crs, [], editavel=False)

        # marca como conectada e guarda a origem
        layer.setCustomProperty("dim/connected", True)
        layer.setCustomProperty("dim/src_layer_id", src_layer.id())

        self._dim_conn_layer = layer

        layer.setReadOnly(True) # trava p/ o usuário

        self._dim_conn_layer_id = layer.id()  # ✅ Aqui sim é válido!
        self._dim_conn_srcLayer = src_layer

        # Gera dimensões iniciais
        prov = self._dim_conn_layer.dataProvider()
        for feat in feats_src:
   # feats_dim = self._gera_dimensoes_para_feat(feat, crs)
            min_len = self.doubleSpinBoxTamanhoM.value()
            feats_dim = self._gera_dimensoes_para_feat(feat, layer.crs(), comprimento_min=min_len)

            ok, feats_dim = prov.addFeatures(feats_dim)   # ← pega Features já com FIDs reais
            self._dim_conn_links[feat.id()] = [f.id() for f in feats_dim]

        self._dim_conn_layer.triggerRepaint()

        # Conecta sinais dinâmicos
        src_layer.geometryChanged.connect(self._dim_on_geom_changed)
        src_layer.featureAdded.connect(self._dim_on_feat_added)
        src_layer.featureDeleted.connect(self._dim_on_feat_deleted)

        self.mostrar_mensagem(self.tr("Dimensões conectadas dinâmicas criadas."), "Sucesso")
        self.layer_dimensoes = self._dim_conn_layer

        self.atualizar_treeViewCamadas() # Atualiza a lista

    def _sync_tree_item_name(self, layer_id: str):
        """Atualiza o texto do item do tree para refletir o nome atual da camada."""
        item  = self._find_tree_item_by_layer_id(layer_id)
        if not item:
            return
        layer = QgsProject.instance().mapLayer(layer_id)
        if not layer:
            return
        item.setText(layer.name())

    def atualizar_dimensao_conectada(self):
        """
        Atualiza a camada de dimensão conectada dinamicamente, com base nos novos parâmetros
        (ex: comprimento mínimo ou direção).
        """
        if not self._dim_conn_layer or not self._dim_conn_srcLayer:
            return

        # Desconecta sinais antigos temporariamente
        try:
            self._dim_conn_srcLayer.geometryChanged.disconnect(self._dim_on_geom_changed)
            self._dim_conn_srcLayer.featureAdded.disconnect(self._dim_on_feat_added)
            self._dim_conn_srcLayer.featureDeleted.disconnect(self._dim_on_feat_deleted)
        except Exception:
            pass  # nosec B110

        # Remove camada de dimensão anterior
        QgsProject.instance().removeMapLayer(self._dim_conn_layer.id())
        self._dim_conn_layer = None
        self._dim_conn_layer_id = ""
        self._dim_conn_links.clear()

        # Gera nova camada com os novos parâmetros
        self.criar_camada_dimensionamento_conectada()

        return

    def _gera_dimensoes_para_feat(self, feat: QgsFeature, crs: QgsCoordinateReferenceSystem, comprimento_min: float = 0.0) -> list[QgsFeature]:
        """
        Cria linhas de dimensão.
        - Segmentos menores que comprimento_min são sempre agregados ao vizinho,
          inclusive se ficarem no final do anel (garante cobertura sem “buracos”).
        """
        geom = feat.geometry()
        if not geom or geom.isEmpty() or not geom.isGeosValid():
            return []

        da = QgsDistanceArea()
        da.setSourceCrs(crs, QgsProject.instance().transformContext())
        da.setEllipsoid(QgsProject.instance().crs().ellipsoidAcronym())

        parts = geom.asMultiPolygon() if geom.isMultipart() else [geom.asPolygon()]
        feats_dim = []

        for part in parts:
            for ring in part:
       # percorre todos os lados do anel
                comp_acum = 0.0
                p0 = ring[0]   # ponto de início do trecho em acumulação
                last_fid = None         # índice do último feature criado
                for i in range(len(ring) - 1):
                    p1 = ring[i]
                    p2 = ring[i + 1]
                    seg_len = (da.measureLength(QgsGeometry.fromPolylineXY([QgsPointXY(p1), QgsPointXY(p2)]))
                                if crs.isGeographic() else
                                QgsGeometry.fromPolylineXY([QgsPointXY(p1), QgsPointXY(p2)]).length())

                    comp_acum += seg_len

           # quando ultrapassar limite, cria/atualiza feature
                    if comp_acum >= comprimento_min:
                        f = QgsFeature()
                        f.setGeometry(QgsGeometry.fromPolylineXY([QgsPointXY(p0), QgsPointXY(p2)]))
                        f.setAttributes([round(comp_acum, 3), f"{comp_acum:.2f} m"])
                        feats_dim.append(f)
                        last_fid = len(feats_dim) - 1
               # reinicia acumulação
                        comp_acum = 0.0
                        p0 = p2

       # Se sobrou trecho < min no final, agrega à última linha criada
                if comp_acum > 0 and last_fid is not None:
           # estende a geometria e o comprimento do último feature
                    f_last = feats_dim[last_fid]
                    g_last = f_last.geometry().asPolyline()
                    g_last[-1] = QgsPointXY(ring[-1])       # ajusta ponto final
                    f_last.setGeometry(QgsGeometry.fromPolylineXY(g_last))
                    total = f_last.attribute(0) + comp_acum
                    f_last.setAttributes([round(total, 3), f"{total:.2f} m"])

        return feats_dim

    def _init_treeview_camadas(self):
        """Cria o modelo e configura o treeViewCamada."""
        model = QStandardItemModel(0, 1, self)  # 1 coluna
        model.setHeaderData(0, Qt.Orientation.Horizontal, self.tr("Dimensionamentos"))
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

        try:
            self._tv_model.rowsInserted.connect(lambda *args: self._update_buttons_state())
            self._tv_model.rowsRemoved.connect(lambda *args: self._update_buttons_state())
            self._tv_model.modelReset.connect(lambda *args: self._update_buttons_state())
        except Exception:
            pass  # nosec B110

    def atualizar_treeViewCamadas(self):
        """
        Preenche o treeViewCamada com as camadas do grupo 'Dimensionamento'.
        Regras:
          - Texto em negrito;
          - Garante sempre 1 selecionada, se houver itens;
          - Se nova camada foi adicionada, seleciona a nova;
          - Se deletada, seleciona a anterior (ou última disponível);
          - Se seleção anterior ainda existir, preserva.
        """
        if self._tv_model is None:
            self._init_treeview_camadas()

        model = self._tv_model
        view  = self.treeViewCamada

        # snapshot anterior
        old_ids = list(self._tv_last_layer_ids)
        prev_selected_id = self._tv_selected_layer_id

        # limpa modelo
        model.removeRows(0, model.rowCount())

        # coleta camadas do grupo
        root = QgsProject.instance().layerTreeRoot()
        grupo_dim = root.findGroup(self.tr("Dimensionamento"))

        new_ids = []
        if grupo_dim:
            for node in grupo_dim.findLayers():
                lyr = node.layer()
                if isinstance(lyr, QgsVectorLayer) and lyr.geometryType() == QgsWkbTypes.GeometryType.LineGeometry:
                    it = QStandardItem(lyr.name())
                    f  = it.font()
                    f.setBold(True)
                    it.setFont(f)
                    it.setEditable(False)
                    it.setData(lyr.id(), Qt.ItemDataRole.UserRole)
                    model.appendRow(it)

           # mantém o nome sincronizado em tempo real
                    try:
                        lyr.nameChanged.connect(lambda lid=lyr.id(): self._sync_tree_item_name(lid))
                    except Exception:
                        pass  # nosec B110

           # pinta o texto do item com a cor atual da camada
                    try:
                        it.setForeground(QBrush(self._get_layer_main_color(lyr)))
                    except Exception:
                        pass  # nosec B110

           # mantém sincronizado se o estilo/cor da camada mudar
                    try:
                        lyr.rendererChanged.connect(lambda lid=lyr.id(): self._sync_tree_item_color(lid))
                    except Exception:
                        pass  # nosec B110
                    try:
                        lyr.styleChanged.connect(lambda lid=lyr.id(): self._sync_tree_item_color(lid))
                    except Exception:
                        pass  # nosec B110

                    new_ids.append(lyr.id())

        # guarda nova ordem
        self._tv_last_layer_ids = list(new_ids)

        # atualiza estado dos botões já após popular a lista (importante para 1 item)
        self._update_buttons_state()

        # helper para selecionar por id
        def _select_id(layer_id: str) -> bool:
            for row in range(model.rowCount()):
                idx = model.index(row, 0)
                if model.data(idx, Qt.ItemDataRole.UserRole) == layer_id:
                    view.setCurrentIndex(idx)
                    self._tv_selected_layer_id = layer_id
                    return True
            return False

        # sem camadas → limpa seleção
        if not new_ids:
            view.clearSelection()
            self._tv_selected_layer_id = None
            self._update_buttons_state()  # <- garante desabilitar quando zera
            return

        # diffs
        added_ids   = [i for i in new_ids if i not in old_ids]
        removed_ids = [i for i in old_ids if i not in new_ids]

        # 1) se houve adição → seleciona a última adicionada
        if added_ids and _select_id(added_ids[-1]):
            self._update_buttons_state()  # <- atualiza antes de sair
            return

        # 2) preserva seleção anterior se ela ainda existir
        if prev_selected_id and prev_selected_id in new_ids and _select_id(prev_selected_id):
            self._update_buttons_state()  # <- atualiza antes de sair
            return

        # 3) se houve remoção → seleciona a "anterior" aproximada
        if removed_ids:
            try:
                removed_pos = min(old_ids.index(r) for r in removed_ids if r in old_ids)
            except ValueError:
                removed_pos = 0
            new_index = min(removed_pos, len(new_ids) - 1)
            if _select_id(new_ids[new_index]):
                self._update_buttons_state()  # <- atualiza antes de sair
                return

        # 4) fallback: seleciona a primeira
        _select_id(new_ids[0])

        # após resolver seleção/fallback
        self._update_buttons_state()

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

    def _get_or_create_dimensionamento_group(self):
        """
        Retorna o grupo top-level 'Dimensionamento' e garante que ele
        permaneça sempre no topo da árvore de camadas.
        """
        root = QgsProject.instance().layerTreeRoot()

        for index, child in enumerate(root.children()):
            if isinstance(child, QgsLayerTreeGroup) and child.name() == self.tr("Dimensionamento"):

                if index == 0:
                    return child

                grupo_topo = child.clone()
                root.insertChildNode(0, grupo_topo)
                root.removeChildNode(child)

                return grupo_topo

        return root.insertGroup(0, self.tr("Dimensionamento"))

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
            self.mostrar_mensagem(self.tr("A camada selecionada não é uma camada de linhas de dimensionamento."), "Erro")
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

        # Monitora a atualização do dimensionamento
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

    def _on_tv_selection_changed(self, selected, deselected):
        """Atualiza o ID da camada selecionada no treeViewCamada e sincroniza os controles da UI com essa camada."""
        idxs = self.treeViewCamada.selectionModel().selectedIndexes()
        if not idxs:
            self._tv_selected_layer_id = None
            return
        idx = idxs[0]
        self._tv_selected_layer_id = self._tv_model.data(idx, Qt.ItemDataRole.UserRole)
        # Atualiza os controles com os valores da camada selecionada
        self._sync_symbol_controls_from_layer(self._get_selected_dim_layer())

    def _criar_camada_dim_base(self, nome, crs, features, editavel=True, *, main_color=None, line_color=None, tick_color=None, arrow_color=None, label_color=None, ):
        """
        Cria uma camada de dimensionamento com estilo e rótulo padronizados,
        adiciona ao grupo 'Dimensionamento' e retorna a camada criada.

        Parâmetros de cor:
          - Você pode passar UMA cor em `main_color` (aplicada a tudo)
            ou cores específicas em `line_color`, `tick_color`, `arrow_color`, `label_color`.
          - Tipos aceitos: QColor, str ("#RRGGBB" ou nome CSS), tuple (r,g,b).
          - Se nada for passado, usa preto (compatível com chamadas antigas).
        """
        # helper de cor
        def _to_qcolor(c, fallback=QColor("black")):
            if c is None:
                return fallback
            if isinstance(c, QColor):
                return c
            if isinstance(c, str):
                qc = QColor(c)
                return qc if qc.isValid() else fallback
            if isinstance(c, (tuple, list)) and len(c) in (3, 4):
                try:
                    return QColor(*c)
                except Exception:
                    return fallback
            return fallback

        # resolve a paleta final
        base      = _to_qcolor(main_color, QColor("black"))
        col_line  = _to_qcolor(line_color,  base)
        col_tick  = _to_qcolor(tick_color,  base)
        col_arrow = _to_qcolor(arrow_color, base)
        col_label = _to_qcolor(label_color, base)

        # cria camada
        uri = f"LineString?crs={crs.authid()}"
        layer = QgsVectorLayer(uri, self._gerar_nome_unico(nome), "memory")
        prov = layer.dataProvider()
        prov.addAttributes([
            QgsField("comprimento", QMetaType.Type.Double),
            QgsField("label", QMetaType.Type.QString)])
        layer.updateFields()

        # lê valores atuais da UI (com defaults se UI ainda não existir)
        try:
            arrow_size_mm = float(self.doubleSpinBoxTamanho.value())      # tamanho da seta
        except Exception:
            arrow_size_mm = 2.5
        try:
            tick_len_mm = float(self.doubleSpinBoxAux.value())   # comprimento do tick
        except Exception:
            tick_len_mm = 4.0
        try:
            text_size_pt = float(self.doubleSpinBoxTexto.value())         # tamanho do texto
        except Exception:
            text_size_pt = 8.0
        try:
            afast_mu = float(self.doubleSpinBoxRecuo.value())    # afastamento (map units)
        except Exception:
            afast_mu = 0.2

        # recuo da seta (ao longo da linha) continua automático
        arrow_recuo_mm = arrow_size_mm * 0.5

        # Direção/offset perpendicular
        sinal = +1 if self.checkBoxDirecao.isChecked() else -1
        offset_mu = afast_mu * sinal

        # símbolo da linha
        line_symbol = QgsLineSymbol.createSimple({'color': 'black', 'width': '0.3'})
        base_layer = line_symbol.symbolLayer(0)
        base_layer.setOffset(offset_mu)
        base_layer.setOffsetUnit(QgsUnitTypes.RenderUnit.RenderMapUnits)
        base_layer.setWidth(0.20)
        base_layer.setWidthUnit(QgsUnitTypes.RenderUnit.RenderMillimeters)
        if hasattr(base_layer, "setColor"):
            base_layer.setColor(col_line)

        # TICK (line marker)
        tick_symbol = QgsMarkerSymbol.createSimple({
            'name': 'line',
            'size': str(tick_len_mm), # usa UI
            'line_width': '0.2',
            'color': col_tick.name(),
            'angle': '0'})

        # SETAS (head/tail)
        arrow_head = QgsMarkerSymbol.createSimple({
            'name': 'triangle',
            'size': str(arrow_size_mm),        # usa UI
            'color': col_arrow.name(),
            'outline_style': 'no',
            'angle': '-90'})
        arrow_tail = QgsMarkerSymbol.createSimple({
            'name': 'triangle',
            'size': str(arrow_size_mm),        # usa UI
            'color': col_arrow.name(),
            'outline_style': 'no',
            'angle': '-90'})

        def _append_marker(placement, marker_sym, along_mm=0):
            ml = QgsMarkerLineSymbolLayer()
            ml.setPlacement(placement)
            ml.setRotateSymbols(True)
            ml.setOffset(offset_mu)
            ml.setOffsetUnit(QgsUnitTypes.RenderUnit.RenderMapUnits)
            ml.setOffsetAlongLine(along_mm)
            ml.setOffsetAlongLineUnit(QgsUnitTypes.RenderUnit.RenderMillimeters)
   # garante cor e tamanho no subSymbol (além do createSimple)
            sub = marker_sym.clone()
            try:
       # cor
                sub.setColor(col_tick if marker_sym == tick_symbol else col_arrow)
                if hasattr(sub, "setOutlineColor"):
                    sub.setOutlineColor(col_tick if marker_sym == tick_symbol else col_arrow)
       # tamanho (reforça o que já veio no createSimple)
                if marker_sym == tick_symbol:
                    sub.setSize(tick_len_mm)
                else:
                    sub.setSize(arrow_size_mm)
            except Exception:
                pass  # nosec B110
            ml.setSubSymbol(sub)
            line_symbol.appendSymbolLayer(ml)

        # ticks (sem recuo)
        for plc in (QgsMarkerLineSymbolLayer.Placement.FirstVertex, QgsMarkerLineSymbolLayer.Placement.LastVertex):
            _append_marker(plc, tick_symbol, along_mm=0)

        # setas (com recuo da UI)
        _append_marker(QgsMarkerLineSymbolLayer.Placement.FirstVertex, arrow_head, arrow_recuo_mm)
        _append_marker(QgsMarkerLineSymbolLayer.Placement.LastVertex,  arrow_tail, arrow_recuo_mm)

        layer.renderer().setSymbol(line_symbol)

        # feições
        prov.addFeatures(features)

        # campos ocultos
        self.configurar_campo_oculto(layer, ["comprimento", "label"])

        # rotulagem (cor + tamanho do texto vindos da UI)
        self.configurar_etiquetas(layer, sinal_lado=(+1 if self.checkBoxDirecao.isChecked() else -1), distancia_mu=abs(offset_mu))

        # adiciona ao grupo "Dimensionamento"
        grupo_dim = self._get_or_create_dimensionamento_group()

        QgsProject.instance().addMapLayer(layer, False)
        grupo_dim.addLayer(layer)

        # bloqueia edição se necessário
        if not editavel:
            layer.startEditing()
            layer.commitChanges()
   # layer.setReadOnly(True)

        return layer

    def _rebuild_dim_angular(self, layer: QgsVectorLayer, use_interno: bool | None = None, radius_mu: float | None = None, min_angle_deg: float | None = None, label_gms: bool | None = None):
        """Recria os arcos de uma camada angular mantendo estilo/cores e o mapa de links."""
        if not bool(layer.customProperty("dim/angular", False)):
            return

        src_id = layer.customProperty("dim/src_layer_id", "")
        src = QgsProject.instance().mapLayer(src_id)

        if not isinstance(src, QgsVectorLayer):
            self.mostrar_mensagem(self.tr("Camada de origem não encontrada para esta dimensão angular."), "Aviso")
            return

        if use_interno is None:
            use_interno = bool(layer.customProperty("dim/internal", True))

        if radius_mu is None:
            radius_mu = float(layer.customProperty("dim/radius_mu", 0.5))

        if min_angle_deg is None:
            min_angle_deg = float(layer.customProperty("dim/min_angle_deg", 0.0))

        if label_gms is None:
            label_gms = bool(layer.customProperty("dim/label_gms", self._usar_angulos_em_gms()))

        connected = bool(layer.customProperty("dim/connected", False))

        layer.setCustomProperty("dim/radius_mu", radius_mu)
        layer.setCustomProperty("dim/internal", bool(use_interno))
        layer.setCustomProperty("dim/min_angle_deg", float(min_angle_deg))
        layer.setCustomProperty("dim/label_gms", bool(label_gms))

        layer.setReadOnly(False)
        prov = layer.dataProvider()

        prov.deleteFeatures([f.id() for f in layer.getFeatures()])

        if connected:
            self._ang_conn_links.clear()

        for feat in src.getFeatures():
            arcs = self._gera_dim_angular_para_feat(
                feat,
                use_interno=use_interno,
                radius_mu=radius_mu,
                min_angle_deg=min_angle_deg,
                label_gms=label_gms)

            if not arcs:
                if connected:
                    self._ang_conn_links[feat.id()] = []
                continue

            ok, new_feats = prov.addFeatures(arcs)

            if connected:
                self._ang_conn_links[feat.id()] = [f.id() for f in new_feats]

        layer.setReadOnly(True)
        layer.triggerRepaint()

        try:
            self.iface.mapCanvas().refresh()
        except Exception:
            pass  # nosec B110

    def _sync_symbol_controls_from_layer(self, layer: QgsVectorLayer):
        """Sincroniza os valores dos controles da UI (seta, tick, recuo e texto) com o estilo atual da camada selecionada."""
        if not layer or not layer.renderer():
            return
        sym = layer.renderer().symbol()
        if not sym:
            return

        arrow_size = tick_len = afast_mu = None

        is_angular = bool(layer.customProperty("dim/angular", False))
        is_azimute = bool(layer.customProperty("dim/azimute", False))
        is_rumo = bool(layer.customProperty("dim/rumo", False))

        if is_angular:
            afast_mu = float(layer.customProperty("dim/radius_mu", self.doubleSpinBoxRecuo.value()))
        elif is_azimute or is_rumo:
            afast_mu = float(layer.customProperty("dim/recuo_ui", self.doubleSpinBoxRecuo.value()))
        else:
            try:
                sll0 = sym.symbolLayer(0)
                if hasattr(sll0, "offset"):
                    afast_mu = abs(float(sll0.offset()))
            except Exception:
                pass  # nosec B110

        for i in range(sym.symbolLayerCount()):
            sll = sym.symbolLayer(i)
            if isinstance(sll, QgsMarkerLineSymbolLayer):
                sub = sll.subSymbol()
                if not sub:
                    continue
                for sl in sub.symbolLayers():
                    if isinstance(sl, QgsSimpleMarkerSymbolLayer):
                        shp = sl.shape()
                        if shp == QgsSimpleMarkerSymbolLayer.Shape.Triangle:
                            arrow_size = sl.size()
                        elif shp == QgsSimpleMarkerSymbolLayer.Shape.Line:
                            tick_len = sl.size()

        text_size = None
        try:
            lbl = layer.labeling()
            if isinstance(lbl, QgsVectorLayerSimpleLabeling):
                pal = lbl.settings()
                text_size = pal.format().size()
        except Exception:
            pass  # nosec B110

        def _set(spin, val):
            if val is None:
                return
            spin.blockSignals(True); spin.setValue(float(val)); spin.blockSignals(False)

        _set(self.doubleSpinBoxTamanho, arrow_size if arrow_size is not None else self.doubleSpinBoxTamanho.value())
        _set(self.doubleSpinBoxAux,     tick_len   if tick_len   is not None else self.doubleSpinBoxAux.value())
        _set(self.doubleSpinBoxRecuo,   afast_mu   if afast_mu   is not None else self.doubleSpinBoxRecuo.value())
        _set(self.doubleSpinBoxTexto,   text_size  if text_size  is not None else self.doubleSpinBoxTexto.value())

    def _apply_dim_sizes(self, layer: QgsVectorLayer, arrow_size_mm: float, tick_len_mm: float, text_size_pt: float, afast_mu: float):
        """Aplica na camada os tamanhos definidos na UI: seta, tick, texto e afastamento (offset)."""
        if not layer or not layer.renderer():
            return

        is_angular = bool(layer.customProperty("dim/angular", False))
        is_azimute = bool(layer.customProperty("dim/azimute", False))
        is_rumo = bool(layer.customProperty("dim/rumo", False))

        canvas = getattr(self.iface, "mapCanvas", lambda: None)()
        if canvas:
            canvas.setRenderFlag(False)

        try:
            sym_old = layer.renderer().symbol()
            if sym_old is None:
                return
            sym = sym_old.clone()

            # valor da UI do recuo
            afast_ui = float(afast_mu)

            # sinal para dimensões lineares comuns
            sinal = +1 if self.checkBoxDirecao.isChecked() else -1

            if is_angular:
                offset_mu = 0.0
            elif is_azimute or is_rumo:
                ref_point = None
                try:
                    if layer.featureCount() > 0:
                        ext = layer.extent()
                        ref_point = QgsPointXY(ext.center().x(), ext.center().y())
                except Exception:
                    pass  # nosec B110

                offset_mu = self._recuo_ui_para_map_units(layer.crs(), afast_ui, ref_point)
                offset_mu = abs(offset_mu)  # azimute usa sempre positivo
                layer.setCustomProperty("dim/recuo_ui", afast_ui)
            else:
                offset_mu = float(afast_ui) * sinal

            arrow_recuo_mm = max(0.0, arrow_size_mm * 0.5)

            try:
                sll0 = sym.symbolLayer(0)
                if hasattr(sll0, "setOffset"):
                    sll0.setOffset(offset_mu)
                    if hasattr(sll0, "setOffsetUnit"):
                        sll0.setOffsetUnit(QgsUnitTypes.RenderUnit.RenderMapUnits)
            except Exception:
                pass  # nosec B110

            for i in range(sym.symbolLayerCount()):
                sll = sym.symbolLayer(i)
                if isinstance(sll, QgsMarkerLineSymbolLayer):
                    sll.setOffset(offset_mu)
                    sll.setOffsetUnit(QgsUnitTypes.RenderUnit.RenderMapUnits)

                    sub_old = sll.subSymbol()
                    if not sub_old:
                        continue
                    sub = sub_old.clone()

                    is_arrow = is_tick = False
                    for sl in sub.symbolLayers():
                        if isinstance(sl, QgsSimpleMarkerSymbolLayer):
                            shp = sl.shape()
                            if shp == QgsSimpleMarkerSymbolLayer.Shape.Triangle:
                                is_arrow = True
                            elif shp == QgsSimpleMarkerSymbolLayer.Shape.Line:
                                is_tick = True

                    if is_arrow:
                        for sl in sub.symbolLayers():
                            if isinstance(sl, QgsSimpleMarkerSymbolLayer):
                                sl.setSize(arrow_size_mm)
                        sll.setOffsetAlongLine(arrow_recuo_mm)
                        sll.setOffsetAlongLineUnit(QgsUnitTypes.RenderUnit.RenderMillimeters)

                    if is_tick:
                        for sl in sub.symbolLayers():
                            if isinstance(sl, QgsSimpleMarkerSymbolLayer):
                                sl.setSize(tick_len_mm)

                    sll.setSubSymbol(sub)

            layer.setRenderer(QgsSingleSymbolRenderer(sym))

   # Rótulo
            try:
                lbl = layer.labeling()
                if not isinstance(lbl, QgsVectorLayerSimpleLabeling):
                    self.configurar_etiquetas(layer)
                else:
                    pal = lbl.settings()
                    fmt = pal.format()
                    fmt.setSize(text_size_pt)
                    fmt.setSizeUnit(QgsUnitTypes.RenderUnit.RenderPoints)
                    pal.setFormat(fmt)

                    off = self._get_rendered_offset_mu(layer, default_val=offset_mu)
                    pal.dist = abs(off)
                    pal.distUnits = QgsUnitTypes.RenderUnit.RenderMapUnits
                    pal.placementFlags = (
                        QgsPalLayerSettings.BelowLine if off >= 0
                        else QgsPalLayerSettings.AboveLine)

                    pal.placement = QgsPalLayerSettings.Placement.Line
                    pal.curved = True
                    layer.setLabeling(QgsVectorLayerSimpleLabeling(pal))
                    layer.setLabelsEnabled(True)
            except Exception:
                pass  # nosec B110

            layer.triggerRepaint()

        finally:
            if canvas:
                canvas.setRenderFlag(True)
                try:
                    canvas.refresh()
                except Exception:
                    pass  # nosec B110

    def _gera_dim_angular_para_feat(self, feat: QgsFeature, *, use_interno: bool, radius_mu: float, min_angle_deg: float, label_gms: bool = False) -> list[QgsFeature]:
        """
        Gera as feições de arco para TODOS os vértices de um polígono.

        IMPORTANTE:
        - `radius_mu` é interpretado como METROS.
        - Se o CRS da camada de origem for GEOGRÁFICO, converte metros para graus localmente.
        - Se o CRS for PROJETADO, usa a unidade do CRS.
        """
        geom = feat.geometry()
        if not geom or geom.isEmpty():
            return []

        src_layer = getattr(self, "_ang_conn_srcLayer", None)
        crs = src_layer.crs() if isinstance(src_layer, QgsVectorLayer) else QgsProject.instance().crs()
        is_geog = crs.isGeographic()

        def _radius_xy_in_mu(at_point: QgsPointXY) -> tuple[float, float]:
            if not is_geog:
                try:
                    mu_unit = crs.mapUnits()
                    factor = QgsUnitTypes.fromUnitToUnitFactor(QgsUnitTypes.DistanceUnit.DistanceMeters, mu_unit)
                except Exception:
                    factor = 1.0
                r_mu = radius_mu * factor
                return r_mu, r_mu

            lat_rad = math.radians(at_point.y())

            m_per_deg_lat = (
                111132.92
                - 559.82 * math.cos(2 * lat_rad)
                + 1.175 * math.cos(4 * lat_rad)
                - 0.0023 * math.cos(6 * lat_rad))
            m_per_deg_lon = (
                111412.84 * math.cos(lat_rad)
                - 93.5 * math.cos(3 * lat_rad)
                + 0.118 * math.cos(5 * lat_rad))

            deg_per_m_lat = 1.0 / max(1e-9, m_per_deg_lat)
            deg_per_m_lon = 1.0 / max(1e-9, m_per_deg_lon)

            return radius_mu * deg_per_m_lon, radius_mu * deg_per_m_lat

        feats_dim = []
        parts = geom.asMultiPolygon() if geom.isMultipart() else [geom.asPolygon()]

        for part in parts:
            for ring in part:
                n = len(ring)
                if n < 3:
                    continue

                m = n - 1  # anel fechado

                for i in range(m):
                    p_prev = QgsPointXY(ring[(i - 1) % m])
                    p = QgsPointXY(ring[i])
                    p_next = QgsPointXY(ring[(i + 1) % m])

                    vx1, vy1 = (p_prev.x() - p.x(), p_prev.y() - p.y())
                    vx2, vy2 = (p_next.x() - p.x(), p_next.y() - p.y())

                    l1 = math.hypot(vx1, vy1)
                    l2 = math.hypot(vx2, vy2)

                    if l1 == 0 or l2 == 0:
                        continue

                    ux1, uy1 = vx1 / l1, vy1 / l1
                    ux2, uy2 = vx2 / l2, vy2 / l2

                    dot = max(-1.0, min(1.0, ux1 * ux2 + uy1 * uy2))
                    ang = math.degrees(math.acos(dot))

                    cross = ux1 * uy2 - uy1 * ux2
                    if cross < 0:
                        ang = 360.0 - ang

                    ang_final = ang if use_interno else (360.0 - ang)

                    if ang_final < float(min_angle_deg):
                        continue

                    a1 = math.atan2(uy1, ux1)
                    a2 = math.atan2(uy2, ux2)

                    delta_short = ((a2 - a1 + math.pi) % (2 * math.pi)) - math.pi
                    delta_long = delta_short - 2 * math.pi if delta_short >= 0 else delta_short + 2 * math.pi

                    interno_pede_longo = ang > 180.0
                    want_long = interno_pede_longo if use_interno else not interno_pede_longo
                    delta = delta_long if want_long else delta_short

                    steps = max(24, int(abs(delta) / (math.pi / 180.0)))

                    rx_mu, ry_mu = _radius_xy_in_mu(p)

                    pts = [
                        QgsPointXY(
                            p.x() + rx_mu * math.cos(a1 + delta * (k / steps)),
                            p.y() + ry_mu * math.sin(a1 + delta * (k / steps)))
                        for k in range(steps + 1)]

                    f = QgsFeature()
                    f.setGeometry(QgsGeometry.fromPolylineXY(pts))
                    f.setAttributes([
                        round(ang_final, 2),
                        self._formatar_rotulo_angular(ang_final, label_gms)])
                    feats_dim.append(f)

        return feats_dim

    def criar_camada_dimensionamento_angular_conectada(self):
        """Cria a camada de arcos e conecta sinais da camada de origem em tempo real."""
        layer_id = self.comboBoxCamada.currentData()

        if not layer_id:
            self.mostrar_mensagem(self.tr("Selecione uma camada de polígono."), "Erro")
            return

        src_layer = QgsProject.instance().mapLayer(layer_id)

        if not isinstance(src_layer, QgsVectorLayer):
            self.mostrar_mensagem(self.tr("Camada inválida selecionada."), "Erro")
            return

        try:
            if self._ang_conn_srcLayer:
                self._ang_conn_srcLayer.geometryChanged.disconnect(self._ang_on_geom_changed)
                self._ang_conn_srcLayer.featureAdded.disconnect(self._ang_on_feat_added)
                self._ang_conn_srcLayer.featureDeleted.disconnect(self._ang_on_feat_deleted)
        except Exception:
            pass  # nosec B110

        min_angle_deg = float(self.doubleSpinBoxTamanhoM.value())
        raio_mu = float(self.doubleSpinBoxRecuo.value())
        use_interno = self.checkBoxDirecao.isChecked()
        label_gms = self._usar_angulos_em_gms()

        chk = self.findChild(QCheckBox, "checkBoxSeleciona")
        feats_src = list(src_layer.getSelectedFeatures()) if (chk and chk.isChecked()) else list(src_layer.getFeatures())

        if not feats_src:
            self.mostrar_mensagem(self.tr("Nenhuma feição encontrada para dimensionar."), "Erro")
            return

        crs = src_layer.crs()
        layer = self._criar_camada_dim_base("Dim_Angular", crs, [], editavel=False)

        layer.setCustomProperty("dim/angular", True)
        layer.setCustomProperty("dim/connected", True)
        layer.setCustomProperty("dim/src_layer_id", src_layer.id())
        layer.setCustomProperty("dim/radius_mu", raio_mu)
        layer.setCustomProperty("dim/min_angle_deg", min_angle_deg)
        layer.setCustomProperty("dim/internal", bool(use_interno))
        layer.setCustomProperty("dim/label_gms", bool(label_gms))

        try:
            arrow = float(self.doubleSpinBoxTamanho.value())
            tick = float(self.doubleSpinBoxAux.value())
            text = float(self.doubleSpinBoxTexto.value())
        except Exception:
            arrow, tick, text = 2.5, 4.0, 8.0

        self._apply_dim_sizes(layer, arrow, tick, text, afast_mu=0.0)

        self._ang_conn_layer = layer
        self._ang_conn_layer_id = layer.id()
        self._ang_conn_srcLayer = src_layer
        self._ang_conn_links = {}

        prov = layer.dataProvider()

        for feat in feats_src:
            arcs = self._gera_dim_angular_para_feat(
                feat,
                use_interno=use_interno,
                radius_mu=raio_mu,
                min_angle_deg=min_angle_deg,
                label_gms=label_gms)

            ok, new_feats = prov.addFeatures(arcs)
            self._ang_conn_links[feat.id()] = [f.id() for f in new_feats]

        layer.setReadOnly(True)
        layer.triggerRepaint()

        src_layer.geometryChanged.connect(self._ang_on_geom_changed)
        src_layer.featureAdded.connect(self._ang_on_feat_added)
        src_layer.featureDeleted.connect(self._ang_on_feat_deleted)

        self.mostrar_mensagem(self.tr("Dimensão Angular Conectada criada."), "Sucesso")
        self.layer_dimensoes = layer
        self.atualizar_treeViewCamadas()

        try:
            self.iface.mapCanvas().refresh()
        except Exception:
            pass  # nosec B110

    def _ang_layer(self):
        """Retorna a camada de dimensão angular conectada, ou None se não existir."""
        return QgsProject.instance().mapLayer(getattr(self, "_ang_conn_layer_id", ""))

    def _ang_on_geom_changed(self, fid, new_geom):
        """Atualiza os arcos de dimensão angular quando a geometria da feição de origem é modificada."""
        layer = self._ang_layer()
        src = self._ang_conn_srcLayer

        if not layer or not src:
            return

        use_interno = bool(layer.customProperty("dim/internal", True))
        raio_mu = float(layer.customProperty("dim/radius_mu", 0.5))
        min_deg = float(layer.customProperty("dim/min_angle_deg", 0.0))
        label_gms = bool(layer.customProperty("dim/label_gms", self._usar_angulos_em_gms()))

        layer.setReadOnly(False)
        prov = layer.dataProvider()
        prov.deleteFeatures(self._ang_conn_links.get(fid, []))

        feat = src.getFeature(fid)

        arcs = self._gera_dim_angular_para_feat(
            feat,
            use_interno=use_interno,
            radius_mu=raio_mu,
            min_angle_deg=min_deg,
            label_gms=label_gms)

        ok, new_feats = prov.addFeatures(arcs)
        self._ang_conn_links[fid] = [f.id() for f in new_feats]

        layer.setReadOnly(True)
        layer.triggerRepaint()

    def _on_min_length_changed_selected(self, value: float):
        """
        Recalcula APENAS a camada selecionada.
        Para camada angular, este valor funciona como ângulo mínimo.
        Para dimensão linear conectada, funciona como comprimento mínimo.
        """
        layer = self._get_selected_dim_layer()

        if not layer:
            return

        if bool(layer.customProperty("dim/azimute", False)):
            layer.setCustomProperty("dim/min_segment_len", float(value))

            self._rebuild_dim_azimute(
                layer,
                modo=str(layer.customProperty("dim/azimute_modo", self._azimute_modo_atual())),
                min_segment_len=float(value),
                label_gms=bool(layer.customProperty("dim/label_gms", self._usar_angulos_em_gms())))
            return

        if bool(layer.customProperty("dim/angular", False)):
            layer.setCustomProperty("dim/min_angle_deg", float(value))

            self._rebuild_dim_angular(
                layer,
                use_interno=bool(layer.customProperty("dim/internal", self.checkBoxDirecao.isChecked())),
                radius_mu=float(layer.customProperty("dim/radius_mu", self.doubleSpinBoxRecuo.value())),
                min_angle_deg=float(value),
                label_gms=bool(layer.customProperty("dim/label_gms", self._usar_angulos_em_gms())))
            return

        if bool(layer.customProperty("dim/rumo", False)):
            layer.setCustomProperty("dim/min_segment_len", float(value))

            self._rebuild_dim_rumo(
                layer,
                modo=str(layer.customProperty("dim/rumo_modo", self._azimute_modo_atual())),
                min_segment_len=float(value),
                label_gms=bool(layer.customProperty("dim/label_gms", self._usar_angulos_em_gms())))
            return

        if not bool(layer.customProperty("dim/connected", False)):
            return

        src_id = layer.customProperty("dim/src_layer_id", "")
        src_layer = QgsProject.instance().mapLayer(src_id) if src_id else None

        if not isinstance(src_layer, QgsVectorLayer):
            self.mostrar_mensagem(self.tr("Camada de origem não encontrada para esta dimensão."), "Aviso")
            return

        try:
            layer.setReadOnly(False)
            prov = layer.dataProvider()

            prov.deleteFeatures([f.id() for f in layer.getFeatures()])
            self._dim_conn_links.clear()

            min_len = float(value)

            for feat in src_layer.getFeatures():
                feats_dim = self._gera_dimensoes_para_feat(
                    feat,
                    layer.crs(),
                    comprimento_min=min_len)
                ok, new_feats = prov.addFeatures(feats_dim)
                self._dim_conn_links[feat.id()] = [nf.id() for nf in new_feats]

            layer.triggerRepaint()

        finally:
            layer.setReadOnly(True)

    def _on_symbol_controls_changed(self, *_):
        """Atualiza em tempo real o estilo da dimensão quando algum controle de tamanho/recuo da UI é modificado."""
        layer = self._get_selected_dim_layer()

        if not layer:
            return

        try:
            arrow_size = float(self.doubleSpinBoxTamanho.value())
            tick_len = float(self.doubleSpinBoxAux.value())
            text_size_pt = float(self.doubleSpinBoxTexto.value())
            raio_mu = float(self.doubleSpinBoxRecuo.value())  # para angular = raio
        except Exception:
            return

        if bool(layer.customProperty("dim/azimute", False)):
            self._apply_dim_sizes(layer, arrow_size, tick_len, text_size_pt, afast_mu=raio_mu)

            self._rebuild_dim_azimute(
                layer,
                modo=str(layer.customProperty("dim/azimute_modo", self._azimute_modo_atual())),
                min_segment_len=float(layer.customProperty("dim/min_segment_len", self.doubleSpinBoxTamanhoM.value())),
                label_gms=bool(layer.customProperty("dim/label_gms", self._usar_angulos_em_gms())))
            return

        if bool(layer.customProperty("dim/rumo", False)):
            self._apply_dim_sizes(layer, arrow_size, tick_len, text_size_pt, afast_mu=raio_mu)

            self._rebuild_dim_rumo(
                layer,
                modo=str(layer.customProperty("dim/rumo_modo", self._azimute_modo_atual())),
                min_segment_len=float(layer.customProperty("dim/min_segment_len", self.doubleSpinBoxTamanhoM.value())),
                label_gms=bool(layer.customProperty("dim/label_gms", self._usar_angulos_em_gms())))
            return

        if bool(layer.customProperty("dim/angular", False)):
            self._apply_dim_sizes(layer, arrow_size, tick_len, text_size_pt, afast_mu=0.0)

            layer.setCustomProperty("dim/radius_mu", raio_mu)

            self._rebuild_dim_angular(
                layer,
                use_interno=self.checkBoxDirecao.isChecked(),
                radius_mu=raio_mu,
                min_angle_deg=float(layer.customProperty("dim/min_angle_deg", self.doubleSpinBoxTamanhoM.value())),
                label_gms=bool(layer.customProperty("dim/label_gms", self._usar_angulos_em_gms())))
            return

        self._apply_dim_sizes(layer, arrow_size, tick_len, text_size_pt, afast_mu=raio_mu)

    def _ang_on_feat_added(self, fid):
        """Cria arcos de dimensão angular quando uma nova feição é adicionada na camada de origem."""
        layer = self._ang_layer()
        src   = self._ang_conn_srcLayer
        if not layer or not src:
            return
        use_interno = bool(layer.customProperty("dim/internal", True))
        raio_mu     = float(layer.customProperty("dim/radius_mu", 0.5))
        min_deg     = float(layer.customProperty("dim/min_angle_deg", 0.0))

        feat = src.getFeature(fid)
        arcs = self._gera_dim_angular_para_feat(feat, use_interno=use_interno, radius_mu=raio_mu, min_angle_deg=min_deg)
        layer.setReadOnly(False)
        prov = layer.dataProvider()
        ok, new_feats = prov.addFeatures(arcs)
        self._ang_conn_links[fid] = [f.id() for f in new_feats]
        layer.setReadOnly(True)
        layer.triggerRepaint()

    def _ang_on_feat_deleted(self, fid):
        """Remove os arcos de dimensão angular associados quando uma feição da camada de origem é deletada."""
        layer = self._ang_layer()
        if not layer:
            return
        layer.setReadOnly(False)
        prov = layer.dataProvider()
        prov.deleteFeatures(self._ang_conn_links.pop(fid, []))
        layer.setReadOnly(True)
        layer.triggerRepaint()

    def _mm_to_mu(self, mm: float) -> float:
        """
        Converte mm (tamanho visual) aproximando para unidades do mapa (MU) conforme o canvas atual.
        Útil p/ seta/tick caso queira respeitar mm. Se preferir, fixe um fator ou trate tudo em MU.
        """
        try:
            canvas = self.iface.mapCanvas()
            mu_per_px = canvas.mapUnitsPerPixel()
            dpi = 96.0  # pode ler do Qt, mas 96 já é ok
            return mm * (dpi / 25.4) * mu_per_px
        except Exception:
            return mm  # fallback

    def _qcolor_to_rgb(self, qcol: QColor) -> tuple[int,int,int]:
        """Converte um QColor para uma tupla RGB (r, g, b)."""
        return (qcol.red(), qcol.green(), qcol.blue())

    def _circle_from_3pts(self, p1, p2, p3):
        """Retorna (cx, cy, r) do círculo pelos 3 pontos; None se colinear."""
        (x1,y1),(x2,y2),(x3,y3) = ( (p1.x(),p1.y()), (p2.x(),p2.y()), (p3.x(),p3.y()) )
        d = 2 * (x1*(y2-y3) + x2*(y3-y1) + x3*(y1-y2))
        if abs(d) < 1e-12:
            return None
        ux = ((x1**2+y1**2)*(y2-y3) + (x2**2+y2**2)*(y3-y1) + (x3**2+y3**2)*(y1-y2)) / d
        uy = ((x1**2+y1**2)*(x3-x2) + (x2**2+y2**2)*(x1-x3) + (x3**2+y3**2)*(x2-x1)) / d
        r  = math.hypot(x1-ux, y1-uy)
        return ux, uy, r

    def _angle_deg(self, cx, cy, px, py):
        """Calcula o ângulo em graus entre o centro (cx, cy) e o ponto (px, py), no intervalo [0, 360)."""
        return (math.degrees(math.atan2(py-cy, px-cx)) + 360.0) % 360.0

    def _is_ccw_triplet(self, a_start, a_mid, a_end):
        """True se indo CCW de start→end você passa por mid (mod 360)."""
        ccw = (a_end - a_start) % 360.0
        t   = (a_mid - a_start) % 360.0
        return t <= ccw

    def _add_arrow(self, msp, tip_xy, dir_angle_deg, size_mu, color=None, layer_name=None):
        """
        Desenha uma seta (triângulo) com a PONTA em 'tip_xy'.
        'dir_angle_deg' é a direção para onde a seta aponta (para dentro da cota).
        O triângulo se estende da ponta para dentro (base a +size_mu na direção).
        """
        import ezdxf
        if size_mu <= 0:
            return

        ang = math.radians(dir_angle_deg % 360.0)
        ux, uy = math.cos(ang), math.sin(ang)   # direção "para dentro"
        bx, by = -uy, ux               # perpendicular (base)

        # base no interior, a 'size_mu' da ponta
        base_cx = tip_xy[0] + ux * size_mu
        base_cy = tip_xy[1] + uy * size_mu

        w = 0.6 * size_mu  # largura da base
        p1 = (base_cx + bx * (w * 0.5), base_cy + by * (w * 0.5))
        p2 = (base_cx - bx * (w * 0.5), base_cy - by * (w * 0.5))

        attrs = {'layer': layer_name}
        if color:
            try:
                attrs['true_color'] = ezdxf.colors.rgb2int(color)
            except Exception:
                pass  # nosec B110

        # SOLID: 3 pontos (o 4º repete o 3º)
        msp.add_solid([tip_xy, p1, p2, p2], dxfattribs=attrs)

    def _usar_angulos_em_gms(self) -> bool:
        """Retorna True quando o checkBoxAngulo estiver marcado.
        Se o checkbox não existir na UI, mantém o padrão atual: graus decimais.
        """
        chk = getattr(self, "checkBoxAngulo", None) or self.findChild(QCheckBox, "checkBoxAngulo")
        return bool(chk and chk.isChecked())

    def _formatar_angulo_gms(self, angulo_graus: float, casas_segundos: int = 2) -> str:
        """Formata um ângulo decimal em GMS: 12°34'56.78\"."""
        try:
            valor = float(angulo_graus)
        except Exception:
            valor = 0.0

        sinal = "-" if valor < 0 else ""
        valor = abs(valor)

        graus = int(math.floor(valor))
        minutos_float = (valor - graus) * 60.0
        minutos = int(math.floor(minutos_float))
        segundos = round((minutos_float - minutos) * 60.0, int(casas_segundos))

        # Corrige estouro por arredondamento: 59.999 -> 60.00
        if segundos >= 60.0:
            segundos = 0.0
            minutos += 1
        if minutos >= 60:
            minutos = 0
            graus += 1

        if casas_segundos > 0:
            largura = 3 + int(casas_segundos)  # 2 dígitos + ponto + casas
            seg_txt = f"{segundos:0{largura}.{int(casas_segundos)}f}"
        else:
            seg_txt = f"{int(round(segundos)):02d}"

        return f"{sinal}{graus}°{minutos:02d}'{seg_txt}\""

    def _formatar_rotulo_angular(self, angulo_graus: float, usar_gms: bool | None = None) -> str:
        """Retorna o texto do rótulo angular conforme a opção da UI/camada."""
        if usar_gms is None:
            usar_gms = self._usar_angulos_em_gms()
        return self._formatar_angulo_gms(angulo_graus) if usar_gms else f"{float(angulo_graus):.1f}°"

    def _on_direction_changed_selected(self, *_):
        """
        Reage à mudança do checkBoxDirecao.

        - Dimensão angular: alterna interno/suplementar e reconstrói os arcos.
        - Dimensão de azimute: apenas muda o lado visual/recuo do dimensionamento.
        - Dimensão linear: mantém o comportamento padrão.
        """
        layer = self._get_selected_dim_layer()

        if not layer:
            return

        try:
            arrow = float(self.doubleSpinBoxTamanho.value())
            tick = float(self.doubleSpinBoxAux.value())
            text = float(self.doubleSpinBoxTexto.value())
            afast = float(self.doubleSpinBoxRecuo.value())
        except Exception:
            return

        if bool(layer.customProperty("dim/angular", False)):
            self._rebuild_dim_angular(
                layer,
                use_interno=self.checkBoxDirecao.isChecked(),
                radius_mu=afast,
                min_angle_deg=float(layer.customProperty("dim/min_angle_deg", self.doubleSpinBoxTamanhoM.value())),
                label_gms=bool(layer.customProperty("dim/label_gms", self._usar_angulos_em_gms())))
            return

        if bool(layer.customProperty("dim/azimute", False)):
   # atualiza o offset/recuo visual
            self._apply_dim_sizes(layer, arrow, tick, text, afast_mu=afast)

            layer.setCustomProperty("dim/recuo_ui", afast)

   # reconstrói as geometrias para manter tudo para dentro ou tudo para fora
            self._rebuild_dim_azimute(
                layer,
                modo=str(layer.customProperty("dim/azimute_modo", self._azimute_modo_atual())),
                min_segment_len=float(layer.customProperty("dim/min_segment_len", self.doubleSpinBoxTamanhoM.value())),
                label_gms=bool(layer.customProperty("dim/label_gms", self._usar_angulos_em_gms())))
            return

        if bool(layer.customProperty("dim/rumo", False)):
            self._apply_dim_sizes(layer, arrow, tick, text, afast_mu=afast)

            self._rebuild_dim_rumo(
                layer,
                modo=str(layer.customProperty("dim/rumo_modo", self._azimute_modo_atual())),
                min_segment_len=float(layer.customProperty("dim/min_segment_len", self.doubleSpinBoxTamanhoM.value())),
                label_gms=bool(layer.customProperty("dim/label_gms", self._usar_angulos_em_gms())))
            return

        self._apply_dim_sizes(layer, arrow, tick, text, afast)

    def _on_ang_format_changed_selected(self, *_):
        """Atualiza a camada angular ou de azimute quando o usuário alterna graus decimais/GMS."""
        layer = self._get_selected_dim_layer()

        if not layer:
            return

        usar_gms = self._usar_angulos_em_gms()

        if bool(layer.customProperty("dim/angular", False)):
            layer.setCustomProperty("dim/label_gms", bool(usar_gms))

            self._rebuild_dim_angular(
                layer,
                use_interno=bool(layer.customProperty("dim/internal", self.checkBoxDirecao.isChecked())),
                radius_mu=float(layer.customProperty("dim/radius_mu", self.doubleSpinBoxRecuo.value())),
                min_angle_deg=float(layer.customProperty("dim/min_angle_deg", self.doubleSpinBoxTamanhoM.value())),
                label_gms=usar_gms)
            return

        if bool(layer.customProperty("dim/azimute", False)):
            layer.setCustomProperty("dim/label_gms", bool(usar_gms))

            self._rebuild_dim_azimute(
                layer,
                modo=str(layer.customProperty("dim/azimute_modo", self._azimute_modo_atual())),
                min_segment_len=float(layer.customProperty("dim/min_segment_len", self.doubleSpinBoxTamanhoM.value())),
                label_gms=usar_gms)
            return

        if bool(layer.customProperty("dim/rumo", False)):
            layer.setCustomProperty("dim/label_gms", bool(usar_gms))

            self._rebuild_dim_rumo(
                layer,
                modo=str(layer.customProperty("dim/rumo_modo", self._azimute_modo_atual())),
                min_segment_len=float(layer.customProperty("dim/min_segment_len", self.doubleSpinBoxTamanhoM.value())),
                label_gms=usar_gms)
            return

    def _recuo_ui_para_map_units(self, crs: QgsCoordinateReferenceSystem, recuo_ui: float, ref_point: QgsPointXY | None = None) -> float:
        """
        Converte o valor da UI (tratado como metros) para unidades do mapa.
        - CRS projetado: converte metros -> unidade do CRS
        - CRS geográfico: converte metros -> graus localmente
        """
        try:
            valor_m = abs(float(recuo_ui))
        except Exception:
            valor_m = 0.0

        if valor_m <= 0:
            return 0.0

        try:
            if crs and crs.isValid() and not crs.isGeographic():
                mu_unit = crs.mapUnits()
                factor = QgsUnitTypes.fromUnitToUnitFactor(QgsUnitTypes.DistanceUnit.DistanceMeters, mu_unit)
                return valor_m * factor
        except Exception:
            pass  # nosec B110

        # CRS geográfico -> aproximação local em graus
        try:
            if ref_point is None:
                center = self.iface.mapCanvas().extent().center()
                ref_point = QgsPointXY(center.x(), center.y())
        except Exception:
            if ref_point is None:
                ref_point = QgsPointXY(0.0, 0.0)

        lat_rad = math.radians(ref_point.y())

        m_per_deg_lat = (
            111132.92
            - 559.82 * math.cos(2 * lat_rad)
            + 1.175 * math.cos(4 * lat_rad)
            - 0.0023 * math.cos(6 * lat_rad))
        m_per_deg_lon = abs(
            111412.84 * math.cos(lat_rad)
            - 93.5 * math.cos(3 * lat_rad)
            + 0.118 * math.cos(5 * lat_rad))

        # média para ficar estável visualmente
        m_per_deg = max(1e-9, (m_per_deg_lat + max(1e-9, m_per_deg_lon)) * 0.5)

        return valor_m / m_per_deg

    def _normalize_text_rotation_deg(self, rot_deg: float, *, eps: float = 0.5) -> float:
        """
        Mantém o texto 'em pé' (upright). Se a rotação ficar entre 90° e 270°,
        ajusta em -180°. Retorna no intervalo [0, 360).
        eps: pequena folga para evitar flip ao redor de 90°/270°.
        """
        a = float(rot_deg) % 360.0
        if (90.0 + eps) < a < (270.0 - eps):
            a -= 180.0
        if a < 0.0:
            a += 360.0
        return a

    def _add_mtext_centered(self, msp, text, at_xy, height_mu, rotation_deg, color=None, layer_name=None):
        """
        MTEXT centralizado com rotação normalizada e background mask ativado.
        """
        # normaliza a rotação para manter texto "em pé"
        rotation_deg = self._normalize_text_rotation_deg(rotation_deg)

        # alinhamento centralizado
        try:
            from ezdxf.enums import MTextEntityAlignment as MEA
            align_value = MEA.MIDDLE_CENTER
        except Exception:
            try:
                from ezdxf.lldxf.const import MTEXT_MIDDLE_CENTER
                align_value = MTEXT_MIDDLE_CENTER
            except Exception:
                align_value = 5  # MIDDLE_CENTER habitual

        attrs = {
            "layer": layer_name,
            "char_height": float(height_mu),
            "attachment_point": align_value}

        if color:
            try:
                attrs["true_color"] = ezdxf.colors.rgb2int(color)
            except Exception:
                pass  # nosec B110

        mt = msp.add_mtext(text, dxfattribs=attrs)

        # Background Mask / Background Color
        try:
   # Versões mais novas do ezdxf
            mt.set_bg_color("canvas", scale=1.15)
        except Exception:
            try:
       # Fallback DXF:
       # 90 / bg_fill:
       # 0 = desligado
       # 1 = cor definida
       # 2 = cor de fundo da tela/desenho
                mt.dxf.bg_fill = 2
                mt.dxf.box_fill_scale = 1.15
            except Exception:
                pass  # nosec B110

        # posicionamento + rotação
        try:
            mt.set_location(at_xy, rotation=float(rotation_deg))
        except TypeError:
            try:
                mt.set_location(at_xy)
            except Exception:
                try:
                    mt.dxf.insert = at_xy
                except Exception:
                    pass  # nosec B110

            try:
                mt.dxf.rotation = float(rotation_deg)
            except Exception:
                pass  # nosec B110

        return mt

    def _add_tick_segment(self, msp, at_xy, base_dir_deg, length_mu, *, layer_name=None, true_color=None, perpendicular=True):
        """
        Desenha um 'tick' (linha auxiliar) centrado em at_xy.
        - base_dir_deg: ângulo base em graus (da linha ou da tangente do arco).
        - perpendicular=True -> o tick é desenhado perpendicular ao ângulo base.
        """
        ang = (base_dir_deg + (90.0 if perpendicular else 0.0)) % 360.0
        th  = math.radians(ang)
        dx  = math.cos(th) * (length_mu * 0.5)
        dy  = math.sin(th) * (length_mu * 0.5)

        pA = (at_xy[0] - dx, at_xy[1] - dy)
        pB = (at_xy[0] + dx, at_xy[1] + dy)

        attrs = {'layer': layer_name}
        if true_color is not None:
            attrs['true_color'] = true_color

        msp.add_line(pA, pB, dxfattribs=attrs)

    def _crs_eh_utm_metros(self, crs: QgsCoordinateReferenceSystem) -> bool:
        """
        Verifica se o CRS parece ser UTM em metros.

        Aceita:
        - CRS projetado;
        - unidade em metros;
        - descrição contendo UTM, ou EPSG WGS84 UTM/SIRGAS UTM.
        """
        try:
            if not crs or not crs.isValid():
                return False

            if crs.isGeographic():
                return False

            if crs.mapUnits() != QgsUnitTypes.DistanceUnit.DistanceMeters:
                return False

            desc = (crs.description() or "").upper()
            auth = (crs.authid() or "").upper()

   # A descrição costuma trazer "UTM zone..." ou "UTM zona..."
            if "UTM" in desc:
                return True

   # WGS84 / UTM Norte e Sul
            if auth.startswith("EPSG:326") or auth.startswith("EPSG:327"):
                return True

   # Muitos SRC SIRGAS 2000 / UTM no Brasil usam EPSG:319xx.
   # Ainda assim, a descrição normalmente contém UTM.
            if auth.startswith("EPSG:319") and "UTM" in desc:
                return True

            return False

        except Exception:
            return False

    def _validar_crs_utm_para_dimensionamento(self, src_layer: QgsVectorLayer | None = None) -> bool:
        """
        Valida se o projeto e, quando informado, a camada selecionada estão em UTM/metros.

        Retorna True se estiver adequado.
        Retorna False e mostra mensagem se não estiver.
        """
        projeto_crs = QgsProject.instance().crs()

        if not self._crs_eh_utm_metros(projeto_crs):
            nome_crs = projeto_crs.authid() if projeto_crs and projeto_crs.isValid() else self.tr("SRC indefinido")

            self.mostrar_mensagem(self.tr("O projeto está em '{nome_crs}'. Para o dimensionamento funcionar corretamente, defina o SRC do projeto para um sistema UTM em metros.").format(nome_crs=nome_crs), "Aviso", duracao=3)

            return False

        if isinstance(src_layer, QgsVectorLayer):
            layer_crs = src_layer.crs()

            if not self._crs_eh_utm_metros(layer_crs):
                nome_crs = layer_crs.authid() if layer_crs and layer_crs.isValid() else self.tr("SRC indefinido")

                self.mostrar_mensagem(self.tr("A camada selecionada está em '{nome_crs}'. Para evitar deslocamentos incorretos, reprojete a camada para UTM em metros antes de dimensionar.").format(nome_crs=nome_crs), "Aviso", duracao=3)

                return False

        return True

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
            self,
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

    def exportar_dim_layer_para_dxf(self):
        """Exporta a camada de dimensionamento selecionada para DXF, incluindo linhas, arcos, setas, ticks e rótulos."""
        layer = self._get_selected_dim_layer()

        if not isinstance(layer, QgsVectorLayer) or layer.geometryType() != QgsWkbTypes.GeometryType.LineGeometry:
            self.mostrar_mensagem(self.tr("Selecione uma camada de dimensionamento (linhas)."), "Erro")
            return

        nome_sugestao = f"{layer.name()}_Dim.dxf" if layer.name() else self.tr("Dimensionamento.dxf")
        path = self.escolher_local_para_salvar(nome_sugestao, self.tr("Arquivos DXF (*.dxf)"))

        if not path:
            return

        doc = ezdxf.new(dxfversion="R2013")

        try:
            if layer.crs().mapUnits() == QgsUnitTypes.DistanceUnit.DistanceMeters:
                doc.units = ezdxf.units.M
            else:
                doc.units = ezdxf.units.Unitless
        except Exception:
            doc.units = ezdxf.units.Unitless

        dxf_layer_name = layer.name() or self.tr("Dimensionamento")

        color_rgb = (0, 0, 0)
        try:
            sym = layer.renderer().symbol()
            if sym and sym.symbolLayerCount() > 0:
                sll0 = sym.symbolLayer(0)
                if hasattr(sll0, "color"):
                    color_rgb = self._qcolor_to_rgb(sll0.color())
                elif hasattr(sll0, "outlineColor"):
                    color_rgb = self._qcolor_to_rgb(sll0.outlineColor())
        except Exception:
            pass  # nosec B110

        rgb_int = ezdxf.colors.rgb2int(color_rgb)

        if dxf_layer_name not in doc.layers:
            doc.layers.add(dxf_layer_name, true_color=rgb_int)

        msp = doc.modelspace()

        try:
            ui_arrow = float(self.doubleSpinBoxTamanho.value())
        except Exception:
            ui_arrow = 2.5

        try:
            ui_tick = float(self.doubleSpinBoxAux.value())
        except Exception:
            ui_tick = 4.0

        try:
            text_pt = float(self.doubleSpinBoxTexto.value())
        except Exception:
            text_pt = 8.0

        arrow_mu = 0.20 * ui_arrow
        tick_mu = 0.20 * ui_tick

        # menor que antes para coincidir melhor com o QGIS
        TEXT_SCALE = 0.020
        text_mu = text_pt * TEXT_SCALE

        is_angular = bool(layer.customProperty("dim/angular", False))
        is_azimute = bool(layer.customProperty("dim/azimute", False))
        is_rumo = bool(layer.customProperty("dim/rumo", False))

        def _layer_ref_point() -> QgsPointXY | None:
            try:
                ext = layer.extent()
                c = ext.center()
                return QgsPointXY(c.x(), c.y())
            except Exception:
                return None

        def _fallback_offset_mu() -> float:
            """
            Offset de segurança caso o símbolo não devolva offset.
            Para Azimute/Rumo, usa sempre positivo na UI e deixa a geometria
            controlar o lado visual.
            """
            try:
                recuo_ui = float(layer.customProperty("dim/recuo_ui", self.doubleSpinBoxRecuo.value()))
            except Exception:
                recuo_ui = 0.0

            if is_azimute or is_rumo:
                return abs(self._recuo_ui_para_map_units(layer.crs(), recuo_ui, _layer_ref_point()))

            sinal = -1 if (hasattr(self, "checkBoxDirecao") and self.checkBoxDirecao.isChecked()) else +1

            try:
                if layer.crs().isGeographic():
                    return self._recuo_ui_para_map_units(layer.crs(), recuo_ui, _layer_ref_point()) * sinal
            except Exception:
                pass  # nosec B110

            return float(recuo_ui) * sinal

        # offset REAL renderizado da camada
        offset_mu_real = self._get_rendered_offset_mu(layer, default_val=_fallback_offset_mu())

        # Para azimute/rumo, o lado do offset do DXF ficou invertido em relação ao canvas,
        # então exportamos com o sinal invertido.
        if is_azimute or is_rumo:
            offset_mu_export = -offset_mu_real
        else:
            offset_mu_export = offset_mu_real

        for f in layer.getFeatures():
            g = f.geometry()

            if not g or g.isEmpty():
                continue

            if not g.isMultipart():
                pts = g.asPolyline()
            else:
                parts = g.asMultiPolyline()
                pts = parts[0] if parts else []

            if len(pts) < 2:
                continue

            if is_angular and len(pts) >= 3:
                p1 = pts[0]
                pm = pts[len(pts) // 2]
                p2 = pts[-1]

                circ = self._circle_from_3pts(p1, pm, p2)

                if circ:
                    cx, cy, r = circ

                    a1 = self._angle_deg(cx, cy, p1.x(), p1.y())
                    am = self._angle_deg(cx, cy, pm.x(), pm.y())
                    a2 = self._angle_deg(cx, cy, p2.x(), p2.y())

                    ccw = self._is_ccw_triplet(a1, am, a2)
                    start_deg, end_deg = (a1, a2) if ccw else (a2, a1)

           # usa o raio REAL da geometria
                    R = r

                    msp.add_arc(
                        center=(cx, cy),
                        radius=R,
                        start_angle=start_deg,
                        end_angle=end_deg,
                        dxfattribs={
                            "layer": dxf_layer_name,
                            "true_color": rgb_int})

                    p1_xy = (
                        cx + R * math.cos(math.radians(start_deg)),
                        cy + R * math.sin(math.radians(start_deg)))
                    p2_xy = (
                        cx + R * math.cos(math.radians(end_deg)),
                        cy + R * math.sin(math.radians(end_deg)))

                    if ccw:
                        tan_start = (start_deg + 90.0) % 360.0
                        tan_end = (end_deg - 90.0) % 360.0
                    else:
                        tan_start = (start_deg - 90.0) % 360.0
                        tan_end = (end_deg + 90.0) % 360.0

                    self._add_arrow(
                        msp, p1_xy, tan_start, arrow_mu,
                        color=color_rgb, layer_name=dxf_layer_name)
                    self._add_arrow(
                        msp, p2_xy, tan_end, arrow_mu,
                        color=color_rgb, layer_name=dxf_layer_name)

                    if tick_mu > 0:
                        self._add_tick_segment(
                            msp, p1_xy, base_dir_deg=tan_start, length_mu=tick_mu,
                            layer_name=dxf_layer_name, true_color=rgb_int, perpendicular=True)
                        self._add_tick_segment(
                            msp, p2_xy, base_dir_deg=tan_end, length_mu=tick_mu,
                            layer_name=dxf_layer_name, true_color=rgb_int, perpendicular=True)

                    mid_idx = len(pts) // 2
                    if 0 < mid_idx < len(pts) - 1:
                        pb = pts[mid_idx - 1]
                        pa = pts[mid_idx + 1]
                        text_rot = math.degrees(math.atan2(pa.y() - pb.y(), pa.x() - pb.x()))
                    else:
                        if ccw:
                            sweep = (end_deg - start_deg) % 360.0
                            amid = (start_deg + sweep * 0.5) % 360.0
                            text_rot = (amid + 90.0) % 360.0
                        else:
                            sweep = (start_deg - end_deg) % 360.0
                            amid = (start_deg - sweep * 0.5) % 360.0
                            text_rot = (amid - 90.0) % 360.0

                    tx = cx + R * math.cos(math.radians(am))
                    ty = cy + R * math.sin(math.radians(am))

                    label = f.attribute("label")
                    if not label:
                        try:
                            label = f"{float(f.attribute(0)):.1f}°"
                        except Exception:
                            label = ""

                    if label:
                        self._add_mtext_centered(
                            msp, label, (tx, ty), text_mu, text_rot,
                            color=color_rgb, layer_name=dxf_layer_name)

                else:
                    msp.add_lwpolyline(
                        [(p.x(), p.y()) for p in pts],
                        dxfattribs={
                            "layer": dxf_layer_name,
                            "true_color": rgb_int})

                continue

   # LINEAR / AZIMUTE / RUMO
            p1 = pts[0]
            p2 = pts[-1]

            ang = math.degrees(math.atan2(p2.y() - p1.y(), p2.x() - p1.x()))
            ang_rad = math.radians(ang)

            nx = -math.sin(ang_rad) * offset_mu_export
            ny = math.cos(ang_rad) * offset_mu_export

            pts_off = [(p.x() + nx, p.y() + ny) for p in pts]

            msp.add_lwpolyline(
                pts_off,
                dxfattribs={
                    "layer": dxf_layer_name,
                    "true_color": rgb_int})

            p1_off = pts_off[0]
            p2_off = pts_off[-1]

            self._add_arrow(
                msp, p1_off, ang, arrow_mu,
                color=color_rgb, layer_name=dxf_layer_name)
            self._add_arrow(
                msp, p2_off, ang + 180.0, arrow_mu,
                color=color_rgb, layer_name=dxf_layer_name)

            if tick_mu > 0:
                self._add_tick_segment(
                    msp, p1_off, base_dir_deg=ang, length_mu=tick_mu,
                    layer_name=dxf_layer_name, true_color=rgb_int, perpendicular=True)
                self._add_tick_segment(
                    msp, p2_off, base_dir_deg=ang, length_mu=tick_mu,
                    layer_name=dxf_layer_name, true_color=rgb_int, perpendicular=True)

            midx = 0.5 * (p1_off[0] + p2_off[0])
            midy = 0.5 * (p1_off[1] + p2_off[1])

            label = f.attribute("label")

            if label:
                self._add_mtext_centered(
                    msp, label, (midx, midy), text_mu, ang,
                    color=color_rgb, layer_name=dxf_layer_name)

        try:
            doc.saveas(path)
        except Exception as e:
            self.mostrar_mensagem(self.tr("Falha ao salvar DXF: {error}").format(error=str(e)), "Erro")
            return

        self.mostrar_mensagem(self.tr("DXF exportado com sucesso em:\n{file_name}").format(file_name=os.path.basename(path)), "Sucesso", caminho_pasta=os.path.dirname(path), caminho_arquivo=path)

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

        # Texto (em negrito) — respeita Qt.ItemDataRole.ForegroundRole do item
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
        Remove a camada pelo ID e apaga o grupo 'Dimensionamento'
        se ele ficar sem camadas.
        """
        if group_name is None:
            group_name = QCoreApplication.translate("DimensionarVetores", "Dimensionamento")

        project = QgsProject.instance()
        layer = project.mapLayer(layer_id)
        if layer:
            project.removeMapLayer(layer_id)

        root = project.layerTreeRoot()

        # procura apenas grupos top-level com esse nome
        for child in list(root.children()):
            if isinstance(child, QgsLayerTreeGroup) and child.name() == group_name:
                # se não restou nenhuma layer dentro do grupo, remove a pasta
                if len(child.findLayers()) == 0:
                    root.removeChildNode(child)

    def editorEvent(self, event, model, option, index):
        """Detecta clique no botão 'X' da lista e remove a camada correspondente do projeto."""
        if event.type() == QEvent.Type.MouseButtonRelease:
            rect = option.rect
            icon_size = 12
            icon_margin = 6
            icon_rect = QRect(rect.left() + icon_margin,
                              rect.top() + (rect.height() - icon_size) // 2,
                              icon_size, icon_size)
            if icon_rect.contains(event.pos()):
                layer_id = index.data(Qt.ItemDataRole.UserRole)
                TreeDeleteButtonDelegate.remove_layer_and_cleanup(layer_id)
                try:
                    self.parent.iface.mapCanvas().refresh()
                except Exception:
                    pass  # nosec B110
                return True
        return super().editorEvent(event, model, option, index)