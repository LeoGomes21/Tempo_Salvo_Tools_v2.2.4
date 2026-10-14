from qgis.core import QgsProject, QgsWkbTypes, QgsVectorLayer, Qgis, QgsMessageLog, QgsMapLayer, QgsGeometry, QgsFeature, QgsPoint, QgsPointXY, QgsRectangle, QgsField
from qgis.PyQt.QtWidgets import QDialog, QCheckBox, QGraphicsScene, QGraphicsLineItem, QSpinBox, QDoubleSpinBox
from qgis.PyQt.QtGui import QPainter, QPen, QBrush, QColor, QPolygonF, QPainterPath
from qgis.PyQt.QtCore import Qt, QEvent, QPointF, QVariant, QCoreApplication
from qgis.PyQt import uic
import math
import os
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
    os.path.dirname(__file__), 'MatrizesdeVetores.ui'))

class MatrizManager(QDialog, FORM_CLASS):

    def __init__(self, parent=None, iface=None):
        """Constructor."""
        super(MatrizManager, self).__init__(parent)
        # Configura a interface do usuário a partir do Designer.
        self.setupUi(self)

        self.iface = iface    # Salva iface para uso em métodos

        # Altera o título da janela
        self.setWindowTitle(self.tr("Gerar Matrizes de Vetores"))

        # cria a cena e desenha as linhas centrais
        self._setup_preview()          

        # Validações de botões de matriz setorial
        self._update_espalhar_enabled()
        self._update_incrementoS_enabled()
        self._atualizar_estado_comboBoxCamada()
        self._ajustar_step_raioS()

        # Desliga a validação a cada tecla
        for sb in (self.spinBoxXI,
                   self.spinBoxXF,
                   self.spinBoxAngulo,
                   self.spinBoxItens):
            sb.setKeyboardTracking(False)

        # Armazena o passo padrão configurado no Qt Designer
        self._step_padrao_angulo = self.doubleSpinBoxAngulo.singleStep()

        self._layer_matriz_id = None   # id da matriz
        self._layer_matriz_ret = None  # id da matriz retangular
        self._layer_matriz_pol = None  # id da matriz polar
        self.checkBoxNova.setEnabled(False)  # Inativa inicialmente
        self._widget_msg_sucesso = None   # Guarda referência da última mensagem
        self._layer_matriz_esp = None      # id da matriz espiral

        # Preenche o comboBox com camadas de polígonos
        self.populate_combo_box()

        # Preenche o combo dos ângulos
        self.populate_combo_box_setoresA()

        # Preenche o comboBox com camadas de pontos
        self.populate_combo_box_pontos()

        # Conecta os sinais aos slots
        self.connect_signals()

        # Conecta o sinal de mudança de seleção das feições da camada atual
        self.update_layer_connections()
        self.update_layer_connections_pontos()

        self._atualizar_limite_setores()

        self._layer_matriz_set = None # id da camada setorial

    def connect_signals(self):
        # Atualiza as conexões quando muda a camada selecionada no comboBox
        self.comboBoxCamada.currentIndexChanged.connect(self.update_layer_connections)

        # Atualiza o comboBox de camadas ao adicionar, remover ou renomear camada no projeto
        QgsProject.instance().layersAdded.connect(self.populate_combo_box)
        QgsProject.instance().layersRemoved.connect(self.populate_combo_box)
        QgsProject.instance().layerWillBeRemoved.connect(self.populate_combo_box)

        # Atualiza o preview retangular ao mudar linhas, colunas, ângulo, gaps ou opções
        self.spinBoxLinha.valueChanged.connect(self.update_rectangular_preview)       # Linhas da matriz
        self.spinBoxColuna.valueChanged.connect(self.update_rectangular_preview)      # Colunas da matriz
        self.doubleSpinBoxAngulo.valueChanged.connect(self.update_rectangular_preview)  # Ângulo de rotação
        self.checkBoxAbsoluto.toggled.connect(self.update_rectangular_preview)        # Gap absoluto ou relativo
        self.doubleSpinBoxLinha.valueChanged.connect(self.update_rectangular_preview) # Gap entre linhas
        self.doubleSpinBoxColuna.valueChanged.connect(self.update_rectangular_preview) # Gap entre colunas
        self.checkBoxRotacionarF.toggled.connect(self.update_rectangular_preview)     # Rotacionar cada feição

        # Troca de modo: retangular ou polar (alterna as abas)
        self.radioButtonRetangular.toggled.connect(self.update_tab_mode)
        self.radioButtonPolar.toggled.connect(self.update_tab_mode)
        self.radioButtonSetorial.toggled.connect(self.update_tab_mode)

        # Atualiza preview e lógica de ângulo ao marcar/desmarcar quadrantes
        self.checkBoxQuadrante.toggled.connect(self.update_rectangular_preview)

        # Sincroniza radioButton com a aba ativa (tabWidget)
        self.tabWidget.currentChanged.connect(self._sincronizar_radio_com_tab)

        # Atualiza preview polar ao mudar centro X/Y
        self.spinBoxX.valueChanged.connect(self.update_polar_preview)                 # Deslocamento X
        self.spinBoxY.valueChanged.connect(self.update_polar_preview)                 # Deslocamento Y

        # Atualiza preview polar ao mudar raio, anéis, incremento
        self.doubleSpinBoxRaio.valueChanged.connect(self.update_polar_preview)        # Raio inicial
        self.spinBoxItensAneis.valueChanged.connect(self.update_polar_preview)        # Quantidade de anéis
        self.doubleSpinBoxIncremento.valueChanged.connect(self.update_polar_preview)  # Incremento do raio dos anéis

        # Atualiza preview polar ao mudar número de itens, ângulo inicial ou rotação individual
        self.spinBoxItens.valueChanged.connect(self.update_polar_preview)             # Número de itens/arcos
        self.spinBoxAngulo.valueChanged.connect(self.update_polar_preview)            # Ângulo inicial do primeiro item
        self.checkBoxRotacionar.toggled.connect(self.update_polar_preview)            # Rotacionar cada quadradinho

        # Ajusta ângulo inicial para o intervalo [XI, XF] ao finalizar edição ou ao mudar XI/XF
        self.spinBoxXI.valueChanged.connect(self._corrigir_ang_ao_final)              # Limite inferior do arco
        self.spinBoxXF.valueChanged.connect(self._corrigir_ang_ao_final)              # Limite superior do arco
        self.spinBoxAngulo.valueChanged.connect(self._enforce_ang_in_arc)             # Força o ângulo dentro do arco

        # Ajusta incremento automático ao mudar quantidade de anéis
        self.spinBoxItensAneis.valueChanged.connect(self._ajustar_incremento_aneis)   # Define incremento padrão ao criar múltiplos anéis

        # Se incremento voltar a zero, força ItensAneis para 1
        self.doubleSpinBoxIncremento.valueChanged.connect(self._ajustar_aneis_incremento)  # Mantém consistência entre incremento e anéis

        # Sempre que XI ou XF mudar, impede que XI >= XF ajustando automaticamente o outro valor
        self.spinBoxXI.valueChanged.connect(self._enforce_xi_lt_xf)
        self.spinBoxXF.valueChanged.connect(self._enforce_xi_lt_xf)

        # Executa a Criação da Matriz (Retangular e Polar"
        self.pushButtonExecutar.clicked.connect(self._executar_matriz)

        # Atualiza o estado do botão Executar caso o SRC do projeto mude
        QgsProject.instance().crsChanged.connect(self._validar_estado_projecao)

        self.pushButtonFechar.clicked.connect(self.close) # Fecha o diálogo

        # Conecta o botão de resetar
        self.pushButtonResetar.clicked.connect(self.on_pushButtonResetar_clicked)

        # Atualiza o comboBoxPontos de camadas ao adicionar, remover ou renomear no projeto
        QgsProject.instance().layersAdded.connect(self.populate_combo_box_pontos)
        QgsProject.instance().layersRemoved.connect(self.populate_combo_box_pontos)
        QgsProject.instance().layerWillBeRemoved.connect(self.populate_combo_box_pontos)

        # Atualiza o preview setorial ao mudar o raio
        self.doubleSpinBoxRaioS.valueChanged.connect(self.update_setorial_preview)
        # Atualiza o preview setorial ao mudar o número de setores
        self.spinBoxSetores.valueChanged.connect(self.update_setorial_preview)

        # Sincroniza o combo de ângulos ao mudar o número de setores
        self.spinBoxSetores.valueChanged.connect(self.on_spinBoxSetores_changed)
        # Sincroniza o número de setores ao mudar o combo de ângulos
        self.comboBoxSetoresA.currentIndexChanged.connect(self.on_comboBoxSetoresA_changed)
        # Atualiza o preview setorial ao mudar o combo de ângulos
        self.comboBoxSetoresA.currentIndexChanged.connect(self.update_setorial_preview)

        # Atualiza o preview setorial ao alternar para modo circular
        self.radioButtonCircular.toggled.connect(self.update_setorial_preview)
        # Atualiza o preview setorial ao alternar para modo geométrico
        self.radioButtonGeometrico.toggled.connect(self.update_setorial_preview)

        # Atualiza limites mínimos do spinBoxSetores ao alternar para geométrico
        self.radioButtonGeometrico.toggled.connect(self._atualizar_limite_setores)
        # Atualiza limites mínimos do spinBoxSetores ao alternar para circular
        self.radioButtonCircular.toggled.connect(self._atualizar_limite_setores)

        # Atualiza o preview setorial ao mudar a rotação inicial dos setores
        self.spinBoxRotaciona.valueChanged.connect(self.update_setorial_preview)

        # Atualiza o preview setorial ao mudar o número de anéis
        self.spinBoxItensAneisS.valueChanged.connect(self.update_setorial_preview)

        # Atualiza o preview setorial ao mudar o espalhamento dos setores
        self.doubleSpinBoxEspalhar.valueChanged.connect(self.update_setorial_preview)

        # Atualiza o preview setorial ao mudar o incremento entre anéis
        self.doubleSpinBoxIncrementoS.valueChanged.connect(self.update_setorial_preview)

        # Habilita/desabilita o espalhamento conforme o número de setores
        self.spinBoxSetores.valueChanged.connect(self._update_espalhar_enabled)
        # Habilita/desabilita incremento conforme o número de anéis
        self.spinBoxItensAneisS.valueChanged.connect(self._update_incrementoS_enabled)

        # Habilita/desabilita comboBoxCamada conforme o modo selecionado (retangular, polar, setorial)
        self.radioButtonRetangular.toggled.connect(self._atualizar_estado_comboBoxCamada)
        self.radioButtonPolar.toggled.connect(self._atualizar_estado_comboBoxCamada)
        self.radioButtonSetorial.toggled.connect(self._atualizar_estado_comboBoxCamada)

        self.radioButtonRetangular.toggled.connect(self._validar_estado_projecao)
        self.radioButtonPolar.toggled.connect(self._validar_estado_projecao)
        self.radioButtonSetorial.toggled.connect(self._validar_estado_projecao)

        # Ajusta o passo do doubleSpinBoxRaioS conforme o valor atual (step dinâmico)
        self.doubleSpinBoxRaioS.valueChanged.connect(self._ajustar_step_raioS)

        # Sempre que a seleção mudar na camada de pontos, atualiza o checkBoxSelecionaS
        self.comboBoxPontos.currentIndexChanged.connect(self.update_layer_connections_pontos)

        # Atualiza o estado do botão Executar caso o SRC do projeto mude no comboBoxPontos
        self.comboBoxPontos.currentIndexChanged.connect(self._validar_estado_projecao)

        # Atualização em tempo real para as matrizes 
        widgets_para_atualizacao = [
            # Retangular
            self.spinBoxLinha, self.spinBoxColuna, self.doubleSpinBoxAngulo,
            self.doubleSpinBoxLinha, self.doubleSpinBoxColuna,
            self.checkBoxAbsoluto, self.checkBoxRotacionarF, self.checkBoxQuadrante,
            # Polar
            self.spinBoxX, self.spinBoxY, self.doubleSpinBoxRaio,
            self.spinBoxItensAneis, self.doubleSpinBoxIncremento,
            self.spinBoxItens, self.spinBoxXI, self.spinBoxXF,
            self.spinBoxAngulo, self.checkBoxRotacionar,
            # Setorial
            self.spinBoxSetores, self.comboBoxSetoresA,
            self.spinBoxRotaciona, self.spinBoxItensAneisS,
            self.doubleSpinBoxIncrementoS, self.doubleSpinBoxRaioS,
            self.doubleSpinBoxEspalhar, self.radioButtonCircular,
            self.radioButtonGeometrico,
            # Espiral  ← NOVO
            self.spinBoxRepeticoes, self.doubleSpinBoxRadial,
            self.doubleSpinBoxAngular, self.checkBoxAbsolutoE,
            self.checkBoxDiguais,    self.checkBoxRotacionarE]

        for w in widgets_para_atualizacao:
            if isinstance(w, (QSpinBox, QDoubleSpinBox)):
                w.valueChanged.connect(self.atualizar_matriz_se_existe, Qt.ConnectionType.UniqueConnection)
            elif isinstance(w, QCheckBox):
                w.toggled.connect(self.atualizar_matriz_se_existe, Qt.ConnectionType.UniqueConnection)
            elif hasattr(w, "currentIndexChanged"):            # QComboBox
                w.currentIndexChanged.connect(self.atualizar_matriz_se_existe, Qt.ConnectionType.UniqueConnection)
            elif hasattr(w, "toggled"):                        # radioButtons
                w.toggled.connect(self.atualizar_matriz_se_existe, Qt.ConnectionType.UniqueConnection)

        # Preview da espiral: repinta quando valores mudam
        self.spinBoxRepeticoes.valueChanged.connect(self.update_espiral_preview, Qt.ConnectionType.UniqueConnection)
        self.doubleSpinBoxRadial.valueChanged.connect(self.update_espiral_preview, Qt.ConnectionType.UniqueConnection)
        self.doubleSpinBoxAngular.valueChanged.connect(self.update_espiral_preview, Qt.ConnectionType.UniqueConnection)
        self.checkBoxAbsolutoE.stateChanged.connect(self.update_espiral_preview, Qt.ConnectionType.UniqueConnection)
        self.checkBoxDiguais.stateChanged.connect(self.update_espiral_preview, Qt.ConnectionType.UniqueConnection)

        # rotacionar blocos
        self.checkBoxRotacionarE.stateChanged.connect(self.update_espiral_preview, Qt.ConnectionType.UniqueConnection)

    def tr(self, message):
        return QCoreApplication.translate("MatrizManager", message)

    def _log_message(self, message, level=Qgis.MessageLevel.Info):
        QgsMessageLog.logMessage(message, 'Matriz', level=level)

    def update_checkBoxSeleciona(self):
        """Ativa ou desativa o checkBoxSeleciona com base na seleção de feições."""
        layer = QgsProject.instance().mapLayer(self.comboBoxCamada.currentData())
        if layer:
            if layer.selectedFeatureCount() > 0:
                self.findChild(QCheckBox, 'checkBoxSeleciona').setEnabled(True)
            else:
                self.findChild(QCheckBox, 'checkBoxSeleciona').setEnabled(False)
                self.findChild(QCheckBox, 'checkBoxSeleciona').setChecked(False)

    def update_layer_connections(self):
        """Conecta o sinal selectionChanged da camada atual à função update_checkBoxSeleciona."""

        # Primeiro, desconecta qualquer conexão existente para evitar erro:
        if hasattr(self, '_layer_crs_signal'):
            try:
                self._layer_crs_signal.selectionChanged.disconnect(self.update_checkBoxSeleciona)
            except Exception:
                pass  # nosec B110 | Ignora erro se já estiver desconectado

        # Atualiza para a nova camada
        layer = QgsProject.instance().mapLayer(self.comboBoxCamada.currentData())
        if layer:
            layer.selectionChanged.connect(self.update_checkBoxSeleciona)
            self._layer_crs_signal = layer  # Atualiza a referência para camada atual
            self.update_checkBoxSeleciona()  # Atualiza imediatamente

        # Garante que o checkBoxSeleciona esteja sincronizado
        self.update_checkBoxSeleciona()

        # Valida projeção e habilita botão Executar
        self._validar_estado_projecao() # Valida a projeção do botão pushButtonExecutar

        # Se já há uma matriz em edição, marcar "Nova camada" ao trocar base
        matriz_ativa_ret = (self._layer_matriz_ret and
            QgsProject.instance().mapLayer(self._layer_matriz_ret))
        matriz_ativa_pol = (self._layer_matriz_pol and
            QgsProject.instance().mapLayer(self._layer_matriz_pol))

        # Decide com base no modo ativo
        if self.radioButtonRetangular.isChecked() and matriz_ativa_ret:
            if hasattr(self, "checkBoxNova") and not self.checkBoxNova.isChecked():
                self.checkBoxNova.blockSignals(True)
                self.checkBoxNova.setChecked(True)
                self.checkBoxNova.blockSignals(False)
                self.checkBoxNova.setEnabled(True)

        elif self.radioButtonPolar.isChecked() and matriz_ativa_pol:
            if hasattr(self, "checkBoxNova") and not self.checkBoxNova.isChecked():
                self.checkBoxNova.blockSignals(True)
                self.checkBoxNova.setChecked(True)
                self.checkBoxNova.blockSignals(False)
                self.checkBoxNova.setEnabled(True)

        # Detecta edições da camada de polígonos ———
        if hasattr(self, '_layer_edit_signal'): # Desfaz ligação antiga
            try:
                self._layer_edit_signal.geometryChanged.disconnect(self._on_layer_modified)
                self._layer_edit_signal.attributeValueChanged.disconnect(self._on_layer_modified)
                self._layer_edit_signal.featureAdded.disconnect(self._on_layer_modified)
                self._layer_edit_signal.featureDeleted.disconnect(self._on_layer_modified)
            except Exception:
                pass  # nosec B110

        # Liga a camada atual
        if layer:
            layer.geometryChanged.connect(self._on_layer_modified, Qt.ConnectionType.UniqueConnection)
            layer.attributeValueChanged.connect(self._on_layer_modified, Qt.ConnectionType.UniqueConnection)
            layer.featureAdded.connect(self._on_layer_modified, Qt.ConnectionType.UniqueConnection)
            layer.featureDeleted.connect(self._on_layer_modified, Qt.ConnectionType.UniqueConnection)
            self._layer_edit_signal = layer

    def _on_layer_modified(self, *args):
        if not self.isVisible():
            return
        # Não reage se o layer editado é justamente a matriz
        sender_layer = self.sender()
        if sender_layer and sender_layer.id() in (
                self._layer_matriz_ret, self._layer_matriz_pol, self._layer_matriz_set):
            return
        self.atualizar_matriz_se_existe()

    def showEvent(self, event):
        super(MatrizManager, self).showEvent(event)
        self.populate_combo_box()  # Atualiza o comboBoxCamada com as camadas disponíveis
        self.update_tab_mode()
        self._validar_estado_projecao() # Valida a projeção do botão pushButtonExecutar
        # Agora garanta que o checkbox reflete a seleção da camada atualmente exibida
        self.update_layer_connections()
        self.update_layer_connections_pontos()
        self.update_checkBoxSeleciona()
        self.update_checkBoxSelecionaS()

    def mostrar_mensagem(self, texto, tipo, duracao=2, caminho_pasta=None, caminho_arquivos=None):
        """
        Exibe uma mensagem na barra de mensagens do QGIS, proporcionando feedback visual ao usuário.

        Funcionalidades:
        - Suporte a mensagens do tipo "Erro", "Sucesso" ou "Aviso", exibindo ícone e cor apropriados.
        - Duração da mensagem configurável (em segundos).
        - Opção de inserir botões para abrir uma pasta ou executar um arquivo diretamente da mensagem (apenas para "Sucesso").

        Parâmetros:

        texto : str
            Texto da mensagem a ser exibida.
        tipo : str
            Tipo da mensagem: "Erro", "Sucesso" ou "Aviso".
        duracao : int, opcional
            Tempo de exibição da mensagem em segundos (padrão: 2).
        caminho_pasta : str, opcional
            Caminho de uma pasta para abrir via botão (apenas para "Sucesso").
        caminho_arquivos : str, opcional
            Caminho de um arquivo para executar via botão (apenas para "Sucesso").
        """
        bar = self.iface.messageBar()  # Obtém a barra de mensagens do QGIS

        # Remover mensagem de sucesso anterior, se existir
        if tipo == "Sucesso":
            if self._widget_msg_sucesso is not None:
                try:
                    bar.popWidget(self._widget_msg_sucesso)
                except Exception:
                    bar.clearWidgets()
                self._widget_msg_sucesso = None

        if tipo == "Erro":
            bar.pushMessage("Erro", texto, level=Qgis.MessageLevel.Critical, duration=duracao)

        elif tipo == "Sucesso":
            msg = bar.createMessage("Sucesso", texto)
            # (botões para abrir pasta/arquivo, se quiser)
            self._widget_msg_sucesso = bar.pushWidget(msg, level=Qgis.MessageLevel.Info, duration=duracao)

        elif tipo == "Aviso":
            bar.pushMessage("Aviso", texto, level=Qgis.MessageLevel.Warning, duration=duracao)

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

        #----Funciona com Camadas de linhas e polígonos--------------
        # vector_layers = [
            # layer for layer in layer_list 
            # if isinstance(layer, QgsVectorLayer) and 
               # QgsWkbTypes.geometryType(layer.wkbType()) in (
                   # QgsWkbTypes.GeometryType.PolygonGeometry, QgsWkbTypes.LineGeometry)]
        
        # for layer in vector_layers:
            # self.comboBoxCamada.addItem(layer.name(), layer.id())
            # layer.nameChanged.connect(self.update_combo_box_item)  # Mantém a conexão para atualizar nomes
        #------------------------------------------------------------

        # Restaura a camada anteriormente selecionada, se ainda existir
        if current_layer_id:
            index = self.comboBoxCamada.findData(current_layer_id)
            if index != -1:
                self.comboBoxCamada.setCurrentIndex(index)

        self.comboBoxCamada.blockSignals(False)  # Libera os sinais

        # Atualiza o estado do checkbox e a visualização
        self.update_checkBoxSeleciona()

        # Garanta que _layer_crs_signal existe e não é None
        signal = getattr(self, '_layer_crs_signal', None)
        if signal is not None:
            try:
                if not QgsProject.instance().mapLayer(signal.id()):
                    del self._layer_crs_signal
            except Exception:
                # Em caso de erro (objeto deletado), apenas remove a referência
                del self._layer_crs_signal

        # Reconecta os sinais da camada atual, garantindo que o selectionChanged esteja conectado
        self.update_layer_connections()

        self._validar_estado_projecao() # Valida a projeção do botão pushButtonExecutar

        self.checkBoxNova.setEnabled(True)  # Matem ativado ao trocar camada base

        self.update_checkBoxSeleciona()  # depois de atualizar camada e conectar sinais

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
        # Atualiza comboBoxCamada (camadas de polígonos)
        for i in range(self.comboBoxCamada.count()):
            layer_id = self.comboBoxCamada.itemData(i)
            layer = QgsProject.instance().mapLayer(layer_id)
            if layer:
                self.comboBoxCamada.setItemText(i, layer.name())

        # Atualiza comboBoxPontos (camadas de pontos)
        for i in range(self.comboBoxPontos.count()):
            layer_id = self.comboBoxPontos.itemData(i)
            layer = QgsProject.instance().mapLayer(layer_id)
            if layer:
                self.comboBoxPontos.setItemText(i, layer.name())

        self.comboBoxCamada.currentIndexChanged.connect(self._validar_estado_projecao)

    def _setup_preview(self):
        """
        Cria uma QGraphicsScene para o graphicsViewPreview e
        desenha uma cruz (linha horizontal + vertical) no centro.
        A cruz é redesenhada toda vez que a view mudar de tamanho.
        """
        view = self.graphicsViewPreview

        # Cria cena e configura antialiasing
        self._preview_scene = QGraphicsScene(view)
        view.setScene(self._preview_scene)
        # view.setRenderHints(view.renderHints() | QPainter.RenderHint.Antialiasing)
        # view.setRenderHints(view.renderHints() | QPainter.RenderHint.Antialiasing | QPainter.HighQualityAntialiasing)

        view.setRenderHints(view.renderHints() | QPainter.RenderHint.Antialiasing)

        # Captura o resizeEvent original para chamá-lo depois
        original_resize = view.resizeEvent

        # Substitui por um método que redesenha a cruz e depois chama o original
        def new_resize(event):
            self._draw_preview_axes()
            original_resize(event)
        view.resizeEvent = new_resize

        # Desenha a cruz pela primeira vez
        self._draw_preview_axes()

    def _draw_preview_axes(self):
        """Desenha (ou redesenha) as linhas de eixo centralizadas."""
        self._preview_scene.clear()
        rect = self.graphicsViewPreview.viewport().rect()
        w, h = rect.width(), rect.height()
        self._preview_scene.setSceneRect(0, 0, w, h)

        mid_x, mid_y = w / 2, h / 2
        pen = QPen(QColor("red"), 0.8, Qt.PenStyle.SolidLine)
        pen.setCosmetic(True)  # Mantém a linha fina independente do zoom
        self._preview_scene.addLine(0, mid_y, w, mid_y, pen)
        self._preview_scene.addLine(mid_x, 0, mid_x, h, pen)

    def update_rectangular_preview(self):
        """
        Desenha a pré-visualização da matriz retangular:

        • Modo normal (Quadrante desmarcado) – mesma lógica de antes.  
        • Modo “Quadrante”:
            ─ Se RotacionarF **desmarcado**  → centros já vêm girados, retângulos não giram.  
            ─ Se RotacionarF **marcado**     → centros NÃO giram; todo o bloco é girado em torno do pivô (célula 0-0).
        """
        scene = self._preview_scene
        scene.clear()
        self._draw_preview_axes()

        n_lin    = self.spinBoxLinha.value()
        n_col    = self.spinBoxColuna.value()
        if n_lin <= 0 or n_col <= 0:
            return

        # Parâmetros básicos
        box_w, box_h = 8, 6

        if self.checkBoxAbsoluto.isChecked():
            gap_col = max(0, self.doubleSpinBoxColuna.value())
            gap_lin = max(0, self.doubleSpinBoxLinha.value())
        else:
            gap_col = self.doubleSpinBoxColuna.value() or -1
            gap_lin = self.doubleSpinBoxLinha.value() or -1

        rect  = self.graphicsViewPreview.viewport().rect()
        w, h  = rect.width(), rect.height()
        mid_x, mid_y = w / 2, h / 2

        pen   = QPen(QColor("blue"), 0.5); pen.setCosmetic(True)
        brush = QBrush(QColor(0, 170, 255, 90))   # Azul translúcido
        ang_deg = self.doubleSpinBoxAngulo.value()
        rot_feats = self.checkBoxRotacionarF.isChecked()
        modo_quad = self.checkBoxQuadrante.isChecked()

        # Calcula centros
        centros = []

        if modo_quad:
            pivot_x = mid_x
            pivot_y = mid_y

            step_x = box_w + gap_col
            step_y = box_h + gap_lin

            # (a) gera grade "para NE" (sem rotação)
            for i in range(n_lin):
                for j in range(n_col):
                    cx = pivot_x + j * step_x
                    cy = pivot_y - i * step_y          # y invertido p/ quadrante
                    centros.append([cx, cy])

            # Sempre rotaciona os centros pelo ângulo da matriz
            ang_centros = ang_deg

            if ang_centros:
                cos_a = math.cos(math.radians(-ang_centros))
                sin_a = math.sin(math.radians(-ang_centros))
                for c in centros:
                    dx, dy = c[0] - pivot_x, c[1] - pivot_y
                    c[0] = cos_a * dx - sin_a * dy + pivot_x
                    c[1] = sin_a * dx + cos_a * dy + pivot_y

        else:
            # Lógica antiga (pivô = centro da view, + deslocamento)
            total_w = n_col * box_w + (n_col - 1) * gap_col
            total_h = n_lin * box_h + (n_lin - 1) * gap_lin
            start_x = mid_x - total_w / 2
            start_y = mid_y - total_h / 2

            cos_a = math.cos(math.radians(-ang_deg))
            sin_a = math.sin(math.radians(-ang_deg))

            for i in range(n_lin):
                for j in range(n_col):
                    cx = start_x + j * (box_w + gap_col) + box_w / 2
                    cy = start_y + i * (box_h + gap_lin) + box_h / 2
                    dx, dy = cx - mid_x, cy - mid_y
                    rx = cos_a * dx - sin_a * dy + mid_x
                    ry = sin_a * dx + cos_a * dy + mid_y
                    centros.append([rx, ry])

            # Opcional: deslocamento para caber no quadrante antigo
            dx_shift = dy_shift = 0
            if self.checkBoxQuadrante.isChecked():      # só entrar aqui se ligar depois
                dx_shift, dy_shift = self._deslocamento_para_quadrante(
                    ang_deg, centros, mid_x, mid_y)
            for c in centros:
                c[0] += dx_shift
                c[1] += dy_shift

        # Desenha retângulos
        for cx, cy in centros:
            r = scene.addRect(-box_w/2, -box_h/2, box_w, box_h, pen, brush)
            r.setPos(cx, cy)
            if modo_quad and rot_feats:
                # bloco inteiro gira; cada retângulo gira pelo mesmo ângulo
                r.setRotation(ang_deg)
            elif not modo_quad and rot_feats:
                # caso antigo: cada retângulo gira em torno do seu centro
                r.setRotation(ang_deg)

    def _deslocamento_para_quadrante(self, ang_deg, pontos_rot, mid_x, mid_y):
        """
        Retorna (dx, dy) que empurra todas as caixas rotacionadas para dentro
        do quadrante correto (1-4), usando o eixo central como limite.

        pontos_rot : list[(x, y)]
            Lista de centros já rotacionados.
        """
        # Bounding box do conjunto rotacionado
        xs, ys = zip(*pontos_rot)
        min_x, max_x = min(xs), max(xs)
        min_y, max_y = min(ys), max(ys)

        # Determina o quadrante trigonométrico
        ang = ang_deg % 360
        quad = 1 if   0 <= ang <  90 else \
               2 if  90 <= ang < 180 else \
               3 if 180 <= ang < 270 else 4

        dx = dy = 0
        if quad == 1:                         # superior-direito
            if min_x < mid_x: dx = mid_x - min_x          # empurra para a direita
            if max_y > mid_y: dy = mid_y - max_y          # empurra para cima
        elif quad == 2:                       # superior-esquerdo
            if max_x > mid_x: dx = mid_x - max_x          # empurra para a esquerda
            if max_y > mid_y: dy = mid_y - max_y          # empurra para cima
        elif quad == 3:                       # inferior-esquerdo
            if max_x > mid_x: dx = mid_x - max_x          # empurra para a esquerda
            if min_y < mid_y: dy = mid_y - min_y          # empurra para baixo
        else:                                 # inferior-direito
            if min_x < mid_x: dx = mid_x - min_x          # empurra para a direita
            if min_y < mid_y: dy = mid_y - min_y          # empurra para baixo

        return dx, dy

    def update_polar_preview(self):
        self._preview_scene.clear()
        self._draw_preview_axes()
        self._draw_preview_circle()

    def _draw_preview_circle(self):
        """
        Pré-visualiza anéis concêntricos e desenha os quadradinhos do modo polar.
        """
        scene = self._preview_scene
        rect  = self.graphicsViewPreview.viewport().rect()
        w, h  = rect.width(), rect.height()
        min_wh = min(w, h)

        scene.clear()
        self._draw_preview_axes()        # mantém o eixo de referência

        fator_desloc = 0.01 * min_wh
        cx = w / 2 + self.spinBoxX.value() * fator_desloc
        cy = h / 2 - self.spinBoxY.value() * fator_desloc   # y invertido

        raio_base  = max(0.0,  self.doubleSpinBoxRaio.value())
        n_aneis    = max(0,    self.spinBoxItensAneis.value())
        incremento = max(0.0,  self.doubleSpinBoxIncremento.value())

        px_por_unidade = 0.01 * min_wh     # 1 % do menor lado por unidade
        r_max_px_lim   = 0.80 * min_wh     # nunca desenhar além de 80 %

        min_px = 12   # Tamanho mínimo visível do círculo

        pen = QPen(Qt.GlobalColor.darkGreen, 0.5)
        pen.setCosmetic(True)
        pen.setCapStyle(Qt.PenCapStyle.RoundCap)
        pen.setJoinStyle(Qt.PenJoinStyle.RoundJoin)

        # Desenha anéis
        for i in range(n_aneis):
            r_val = raio_base + i * incremento
            r_px  = r_val * px_por_unidade + min_px     # sempre começa com o mínimo
            r_px  = min(r_px, r_max_px_lim)
            scene.addEllipse(cx - r_px, cy - r_px, 2 * r_px, 2 * r_px, pen)

        # Quadradinhos em todos os anéis, dentro do arco XI-XF ---
        n_quads = max(1, self.spinBoxItens.value())

        xi = self.spinBoxXI.value()
        xf = self.spinBoxXF.value()
        if xi == xf:          # arco completo
            xf = xi + 360
        ang0 = self.spinBoxAngulo.value()        # primeiro quadradinho
        rotacionar = self.checkBoxRotacionar.isChecked()

        arco = xf - xi          # amplitude em graus

        if n_quads == 1:
            angulos = [ang0]
        else:
            if arco == 360:
                passo = arco / n_quads
                angulos = [(ang0 + i * passo) % 360 for i in range(n_quads)]
            else:
                passo = (xf - ang0) / (n_quads - 1)
                angulos = [ang0 + i * passo for i in range(n_quads)]

        # Garante que o primeiro seja exatamente ang0
        while angulos[0] != ang0 and ang0 in angulos:
            angulos.append(angulos.pop(0))

        # Garante que o primeiro ângulo seja ang0 dentro do arco
        # (roda a lista até que angulos[0] == ang0)
        if ang0 in angulos:
            while angulos[0] != ang0:
                angulos.append(angulos.pop(0))

        box_w, box_h = 6, 8
        quad_pen = QPen(Qt.GlobalColor.blue, 0.5); quad_pen.setCosmetic(True)
        quad_brush = QBrush(QColor(0, 170, 255, 90))   # Azul translúcido

        for i_anel in range(n_aneis):
            r_quad_px = (raio_base + i_anel * incremento) * px_por_unidade + min_px
            for ang_deg in angulos:
                ang_rad = math.radians(ang_deg)
                qx = cx + r_quad_px * math.cos(ang_rad)
                qy = cy - r_quad_px * math.sin(ang_rad)   # anti-horário

                rect_item = scene.addRect(-box_w/2, -box_h/2, box_w, box_h, quad_pen, quad_brush)
                rect_item.setPos(qx, qy)
                rect_item.setRotation(-ang_deg if rotacionar else 0)

    def _ajustar_incremento_aneis(self):
        """
        Ajusta automaticamente o incremento dos anéis ao mudar a quantidade:
        - Se ItensAneis > 1 e incremento == 0, define incremento = 1.
        - Se ItensAneis == 1, define incremento = 0.
        - Se usuário alterar manualmente, não interfere.
        """
        n_aneis = self.spinBoxItensAneis.value()
        inc = self.doubleSpinBoxIncremento.value()

        if n_aneis > 1 and inc == 0:
            self.doubleSpinBoxIncremento.blockSignals(True)
            self.doubleSpinBoxIncremento.setValue(1)
            self.doubleSpinBoxIncremento.blockSignals(False)
        elif n_aneis == 1 and inc != 0:
            self.doubleSpinBoxIncremento.blockSignals(True)
            self.doubleSpinBoxIncremento.setValue(0)
            self.doubleSpinBoxIncremento.blockSignals(False)

        self.update_polar_preview()

    def _ajustar_aneis_incremento(self):
        """
        Se o incremento for 0 e ItensAneis > 1, força ItensAneis para 1.
        """
        inc = self.doubleSpinBoxIncremento.value()
        n_aneis = self.spinBoxItensAneis.value()
        if inc == 0 and n_aneis > 1:
            self.spinBoxItensAneis.blockSignals(True)
            self.spinBoxItensAneis.setValue(1)
            self.spinBoxItensAneis.blockSignals(False)

        self.update_polar_preview()

    def _corrigir_ang_ao_final(self):
        """
        Após editar spinBoxAngulo, garante que o valor esteja entre XI e XF.
        Se estiver fora, ajusta para o mais próximo.
        """
        xi = self.spinBoxXI.value()
        xf = self.spinBoxXF.value()
        ang = self.spinBoxAngulo.value()
        if (xf - xi) % 360 == 0:
            return  # Arco completo, qualquer valor é válido
        novo_ang = ang
        if ang < xi:
            novo_ang = xi
        elif ang > xf:
            novo_ang = xf
        if novo_ang != ang:
            self.spinBoxAngulo.blockSignals(True)
            self.spinBoxAngulo.setValue(novo_ang)
            self.spinBoxAngulo.blockSignals(False)

        # Atualiza o preview imediatamente, pois podemos ter alterado valores
        self.update_polar_preview()

    def _enforce_ang_in_arc(self):
        """
        Garante que spinBoxAngulo esteja sempre dentro do intervalo [XI, XF].
        Se estiver fora, ajusta para o mais próximo.
        """
        xi = self.spinBoxXI.value()
        xf = self.spinBoxXF.value()
        ang = self.spinBoxAngulo.value()
        # Se o arco cobre 360°, qualquer valor é válido
        if (xf - xi) % 360 == 0:
            return

        # Ajusta caso esteja fora do intervalo
        if ang < xi:
            self.spinBoxAngulo.blockSignals(True)
            self.spinBoxAngulo.setValue(xi)
            self.spinBoxAngulo.blockSignals(False)
        elif ang > xf:
            self.spinBoxAngulo.blockSignals(True)
            self.spinBoxAngulo.setValue(xf)
            self.spinBoxAngulo.blockSignals(False)

        # Atualiza preview após ajuste
        self.update_polar_preview()

    def _enforce_xi_lt_xf(self):
        """
        Garante que XI < XF:
        - Se usuário subir XI para valor >= XF, empurra XF para XI+1 (até máximo).
        - Se usuário baixar XF para valor <= XI, puxa XI para XF-1 (até mínimo).
        """
        xi = self.spinBoxXI.value()
        xf = self.spinBoxXF.value()
        passo = 1  # diferença mínima (graus)
        sender = self.sender()

        if xi >= xf:
            if sender is self.spinBoxXI:
                # Usuário subiu XI: empurra XF para frente
                novo_xf = min(self.spinBoxXF.maximum(), xi + passo)
                self.spinBoxXF.blockSignals(True)
                self.spinBoxXF.setValue(novo_xf)
                self.spinBoxXF.blockSignals(False)
            else:
                # Usuário desceu XF: puxa XI para trás
                novo_xi = max(self.spinBoxXI.minimum(), xf - passo)
                self.spinBoxXI.blockSignals(True)
                self.spinBoxXI.setValue(novo_xi)
                self.spinBoxXI.blockSignals(False)

        # Atualiza preview se necessário
        self.update_polar_preview()

    def _obter_camada_e_feats(self):
        """Devolve (camada_base, lista_de_feicoes) ou None se inválido."""
        camada = QgsProject.instance().mapLayer(self.comboBoxCamada.currentData())
        if not camada or camada.type() != QgsMapLayer.LayerType.VectorLayer:
            self.mostrar_mensagem(self.tr("Camada inválida ou não encontrada."), "Erro")
            return None, None

        seleciona = self.findChild(QCheckBox, 'checkBoxSeleciona').isChecked()
        feats = camada.selectedFeatures() if seleciona else list(camada.getFeatures())
        if not feats:
            self.mostrar_mensagem(self.tr("Nenhuma feição encontrada na camada."), "Aviso")
            return None, None
        return camada, feats

    def _centro_referencia(self, feats_src):
        """Centroide médio do conjunto de feições."""
        pts = [f.geometry().centroid().asPoint() for f in feats_src]
        return (
            sum(p.x() for p in pts) / len(pts),
            sum(p.y() for p in pts) / len(pts))

    def _centros_rotacionados(self, n_lin, n_col, cell_w, cell_h, gap_col, gap_lin, cx, cy, ang_deg):
        """Lista [(x,y)] dos centros já rotacionados."""
        ang_rad = math.radians(ang_deg)
        cos_a, sin_a = math.cos(ang_rad), math.sin(ang_rad)

        total_w = n_col * cell_w + (n_col-1)*gap_col
        total_h = n_lin * cell_h + (n_lin-1)*gap_lin
        start_x = cx - total_w/2
        start_y = cy - total_h/2

        centros = []
        for i in range(n_lin):
            for j in range(n_col):
                x = start_x + j*(cell_w+gap_col) + cell_w/2
                y = start_y + i*(cell_h+gap_lin) + cell_h/2
                dx, dy = x-cx, y-cy
                centros.append((cos_a*dx - sin_a*dy + cx, sin_a*dx + cos_a*dy + cy))
        return centros

    def _shift_por_quadrante(self, centros, cx, cy, ang_deg):
        """Calcula (dx_shift, dy_shift) conforme quadrante trigonométrico."""
        if not self.checkBoxQuadrante.isChecked():
            return 0, 0

        xs, ys = zip(*centros)
        min_x, max_x = min(xs), max(xs)
        min_y, max_y = min(ys), max(ys)

        quad = 1 if   0 <= ang_deg%360 <  90 else \
               2 if  90 <= ang_deg%360 < 180 else \
               3 if 180 <= ang_deg%360 < 270 else 4

        if   quad == 1: corner_x, corner_y = min_x, min_y   # inf-esq
        elif quad == 2: corner_x, corner_y = max_x, min_y   # inf-dir
        elif quad == 3: corner_x, corner_y = max_x, max_y   # sup-dir
        else:            corner_x, corner_y = min_x, max_y   # sup-esq

        return cx - corner_x, cy - corner_y

    def _tamanho_celula_e_gaps(self, feats_src):
        """
        Calcula (cell_w, cell_h, gap_col, gap_lin) tomando o bounding-box
        total do grupo de feições como referência.

        Modo Absoluto: cada célula tem o tamanho exato do grupo e o gap
        é o valor do spinbox (>=0).

        Modo Relativo: a célula “vale” 5% do grupo (95% de sobreposição).
          - Se spinbox == 0, gap = 0 → shift = cell_w  (5%)
          - Se spinbox  > 0, gap = spinbox - cell_w → shift = spinbox
        """
        # 1) bounding-box total do grupo
        bb_total = QgsRectangle()
        for f in feats_src:
            bb_total.combineExtentWith(f.geometry().boundingBox())
        box_w = bb_total.width()
        box_h = bb_total.height()

        if self.checkBoxAbsoluto.isChecked():
            # cada célula = tamanho do grupo; gap = spinboxes
            cell_w, cell_h = box_w, box_h
            gap_col = max(0, self.doubleSpinBoxColuna.value())
            gap_lin = max(0, self.doubleSpinBoxLinha.value())

        else:
            # modo relativo: apenas 5% visível → 95% sobreposição
            s = 0.05
            cell_w = box_w * s
            cell_h = box_h * s

            sb_col = self.doubleSpinBoxColuna.value()
            sb_lin = self.doubleSpinBoxLinha.value()

            # calcula gap de forma que shift = cell_w + gap seja:
            gap_col = max(0, sb_col - cell_w)
            gap_lin = max(0, sb_lin - cell_h)

        return cell_w, cell_h, gap_col, gap_lin

    def _gerar_feats_matriz(self, feats_src, centros, dx_shift, dy_shift, ang_deg, rotacionar_bloco, layer_fields):
        """
        Gera e retorna as feições clonadas e transformadas para compor a matriz,
        aplicando translação e rotação conforme os centros e parâmetros definidos.
        """
        feats_out = []

        # Centro do grupo original
        pts = [f.geometry().centroid().asPoint() for f in feats_src]
        cx_grp = sum(p.x() for p in pts) / len(pts)
        cy_grp = sum(p.y() for p in pts) / len(pts)

        # Geometrias relativas ao centro do grupo
        geoms_rel = []
        for f in feats_src:
            g_rel = QgsGeometry(f.geometry())
            g_rel.translate(-cx_grp, -cy_grp)
            geoms_rel.append((g_rel, f.attributes()))

        # Centro global da matriz (usado se NÃO houver ancoragem/quadrante)
        if centros:
            cx_mat = sum(pt[0] + dx_shift for pt in centros) / len(centros)
            cy_mat = sum(pt[1] + dy_shift for pt in centros) / len(centros)
        else:
            cx_mat, cy_mat = 0, 0  # fallback

        quadrante_ativo = self.checkBoxQuadrante.isChecked()

        # Ajuste: definir pivô global se ambos quadrante e rotacionarF estão ativos
        if quadrante_ativo and rotacionar_bloco:
            # Pivô global: canto de ancoragem da matriz (primeira célula)
            pivot_x = centros[0][0] + dx_shift
            pivot_y = centros[0][1] + dy_shift

        for (cx_cell, cy_cell) in centros:
            cx_cell += dx_shift
            cy_cell += dy_shift

            bloco_feats = []
            for g_rel, attrs in geoms_rel:
                g = QgsGeometry(g_rel)
                g.translate(cx_cell, cy_cell)
                bloco_feats.append((g, attrs))

            if rotacionar_bloco and ang_deg:
                if quadrante_ativo and rotacionar_bloco:
                    # Gira todas as feições em torno do pivô global (primeira célula)
                    for g, attrs in bloco_feats:
                        g.rotate(-ang_deg, QgsPointXY(pivot_x, pivot_y))
                        feat = QgsFeature(layer_fields)
                        feat.setGeometry(g)
                        feat.setAttributes(attrs)
                        feats_out.append(feat)
                else:
                    # Gira cada feição em torno do centro da célula ou do centro global
                    p_x = cx_cell if quadrante_ativo else cx_mat
                    p_y = cy_cell if quadrante_ativo else cy_mat
                    for g, attrs in bloco_feats:
                        g.rotate(-ang_deg, QgsPointXY(p_x, p_y))
                        feat = QgsFeature(layer_fields)
                        feat.setGeometry(g)
                        feat.setAttributes(attrs)
                        feats_out.append(feat)
            else:
                for g, attrs in bloco_feats:
                    feat = QgsFeature(layer_fields)
                    feat.setGeometry(g)
                    feat.setAttributes(attrs)
                    feats_out.append(feat)

        return feats_out

    def _centros_canto_ancorado(self, n_lin, n_col, cell_w, cell_h, gap_col, gap_lin, anchor_x, anchor_y, ang_deg):
        """
        Gera centros de uma matriz retangular ancorada,
        mantendo a feição de origem fixa, para qualquer ângulo.
        """

        # Pivô = feição inicial
        pivot_x, pivot_y = anchor_x, anchor_y

        # Deslocamentos “para NE”
        step_x = cell_w + gap_col
        step_y = cell_h + gap_lin

        cos_a, sin_a = math.cos(math.radians(ang_deg)), math.sin(math.radians(ang_deg))
        centros = []

        for i in range(n_lin):
            for j in range(n_col):
                # deslocamento local antes da rotação
                dx_local = j * step_x
                dy_local = i * step_y

                # aplica rotação
                rx_local =  cos_a * dx_local - sin_a * dy_local
                ry_local =  sin_a * dx_local + cos_a * dy_local

                centros.append((pivot_x + rx_local, pivot_y + ry_local))

        return centros

    def criar_matriz_retangulos_qgis(self):
        """
        Cria ou atualiza a camada de matriz retangular no QGIS,
        clonando e posicionando as feições de acordo com os parâmetros do diálogo.
        """
        camada, feats_src = self._obter_camada_e_feats()
        if not camada: return

        n_lin = self.spinBoxLinha.value()
        n_col = self.spinBoxColuna.value()
        if n_lin<=0 or n_col<=0:
            self.mostrar_mensagem(self.tr("Linhas/colunas inválidas."), "Erro")
            return

        cx, cy = self._centro_referencia(feats_src)
        cell_w, cell_h, gap_c, gap_l = self._tamanho_celula_e_gaps(feats_src)
        ang_deg = self.doubleSpinBoxAngulo.value()

        # Escolha do Conjunto de Centros
        if self.checkBoxQuadrante.isChecked():
            # ► matriz ancorada no canto / pivô fixo
            centros = self._centros_canto_ancorado(
                n_lin, n_col, cell_w, cell_h, gap_c, gap_l,
                cx, cy,
                0 if self.checkBoxRotacionarF.isChecked() else ang_deg)
            dx_shift = dy_shift = 0 # nenhum ajuste extra
        else:
            # ► lógica original (pivô no centro + deslocamento pós-rotação)
            centros = self._centros_rotacionados(
                n_lin, n_col, cell_w, cell_h, gap_c, gap_l,
                cx, cy,
                0 if self.checkBoxRotacionarF.isChecked() else ang_deg)
            dx_shift, dy_shift = self._shift_por_quadrante(
                centros, cx, cy, ang_deg)

        # Gerar feições
        feats_out = self._gerar_feats_matriz(
            feats_src, centros, dx_shift, dy_shift,
            ang_deg, rotacionar_bloco=self.checkBoxRotacionarF.isChecked(),
            layer_fields=camada.fields())

        # Verifica se está criando uma camada nova (não atualização)
        camada_era_nova = False
        if not self._layer_matriz_id or not QgsProject.instance().mapLayer(self._layer_matriz_id):
            camada_era_nova = True

        # camada_out = self._criar_layer_saida(camada, n_lin, n_col)
        camada_out = self._criar_layer_saida(camada, n_lin, n_col, modo="ret")
        camada_out.dataProvider().addFeatures(feats_out)
        camada_out.updateExtents()

        if camada_era_nova:
            self.mostrar_mensagem(self.tr("Matriz criada com {count} feições clonadas.").format(count=len(feats_out)), "Sucesso")

        # Habilita checkBoxNova após criar a matriz pela primeira vez
        if hasattr(self, "checkBoxNova"):
            self.checkBoxNova.setEnabled(True)

    def _criar_layer_saida(self, camada_base, n_lin, n_col, modo):
        """
        Cria ou retorna camada de matriz.
        `modo` deve ser "ret" ou "pol"
        """
        nome = f"{camada_base.name()}_matriz_{n_lin}x{n_col}_{'ret' if modo == 'ret' else 'pol'}"

        layer_id_attr = '_layer_matriz_ret' if modo == 'ret' else '_layer_matriz_pol'

        if hasattr(self, "checkBoxNova") and self.checkBoxNova.isChecked():
            setattr(self, layer_id_attr, None)

        layer_id = getattr(self, layer_id_attr)
        if layer_id:
            layer = QgsProject.instance().mapLayer(layer_id)
            if layer and layer.isValid():
                # Ajusta nome da camada se mudou
                if layer.name() != nome:
                    layer.setName(nome)
                layer.startEditing()
                layer.dataProvider().truncate()
                layer.commitChanges()
                return layer

        # Nova camada
        geom_type = QgsWkbTypes.displayString(camada_base.wkbType())
        crs = camada_base.crs().authid()
        layer = QgsVectorLayer(f"{geom_type}?crs={crs}", nome, "memory")
        layer.dataProvider().addAttributes(camada_base.fields())
        layer.updateFields()
        QgsProject.instance().addMapLayer(layer)
        setattr(self, layer_id_attr, layer.id())
        return layer

    def criar_matriz_polar_qgis(self):
        """Gera a matriz em modo polar (anéis)."""
        camada, feats_src = self._obter_camada_e_feats()
        if not camada:
            return

        # Parâmetros do diálogo
        n_aneis     = max(1, self.spinBoxItensAneis.value())
        n_itens     = max(1, self.spinBoxItens.value())
        raio_base   = max(0.0, self.doubleSpinBoxRaio.value())
        incremento  = max(0.0, self.doubleSpinBoxIncremento.value())
        xi          = self.spinBoxXI.value()      # início do arco
        xf          = self.spinBoxXF.value()      # fim   do arco
        ang0        = self.spinBoxAngulo.value()  # 1.º item
        rot_item    = self.checkBoxRotacionar.isChecked()

        # Se XI == XF → arco completo
        arco = (xf - xi) % 360 or 360

        # Lista de ângulos
        if n_itens == 1:
            angulos = [ang0]
        else:
            if arco == 360:
                passo = arco / n_itens
                angulos = [(ang0 + i * passo) % 360 for i in range(n_itens)]
            else:
                passo = (xf - ang0) / (n_itens - 1)
                angulos = [ang0 + i * passo for i in range(n_itens)]

        # Centro do grupo
        pts = [f.geometry().centroid().asPoint() for f in feats_src]
        cx_grp = sum(p.x() for p in pts) / len(pts)
        cy_grp = sum(p.y() for p in pts) / len(pts)

        # Offset definido pelo usuário (em metros do CRS)
        offset_x = self.spinBoxX.value()
        offset_y = self.spinBoxY.value()

        # O novo centro é deslocado por esses valores:
        cx_centro = cx_grp + offset_x
        cy_centro = cy_grp + offset_y

        # Geometrias relativas
        geoms_rel = []
        for f in feats_src:
            g_rel = QgsGeometry(f.geometry())
            g_rel.translate(-cx_grp, -cy_grp)
            geoms_rel.append((g_rel, f.attributes()))

        # Replica bloco
        feats_out = []
        layer_fields = camada.fields()

        for i_anel in range(n_aneis):
            r = raio_base + i_anel * incremento
            for ang_deg in angulos:
                ang_rad = math.radians(ang_deg)
                cx = cx_centro + r * math.cos(ang_rad)
                cy = cy_centro + r * math.sin(ang_rad)

                for g_rel, attrs in geoms_rel:
                    g = QgsGeometry(g_rel)
                    g.translate(cx, cy)                     # 1) translação

                    if self.checkBoxRotacionar.isChecked(): # 2) rotação opcional
                        g.rotate(-ang_deg, QgsPointXY(cx, cy))

                    feat = QgsFeature(layer_fields)
                    feat.setGeometry(g)
                    feat.setAttributes(attrs)
                    feats_out.append(feat)

        # Camada de saída
        camada_era_nova = not self._layer_matriz_id or not QgsProject.instance().mapLayer(self._layer_matriz_id)
        # camada_out = self._criar_layer_saida(camada, n_aneis, n_itens)  # reaproveita/limpa layer
        camada_out = self._criar_layer_saida(camada, n_aneis, n_itens, modo="pol")
        camada_out.dataProvider().addFeatures(feats_out)
        camada_out.updateExtents()

        if camada_era_nova:
            self.mostrar_mensagem(self.tr("Matriz criada com {count} feições clonadas.").format(count=len(feats_out)), "Sucesso")

        # Habilita checkBoxNova após criar a matriz pela primeira vez
        if hasattr(self, "checkBoxNova"):
            self.checkBoxNova.setEnabled(True)

    def _validar_estado_projecao(self):
        """
        Valida projeção das camadas e do projeto e atualiza o estado do botão.
        Exibe mensagem de aviso se necessário, apenas se o diálogo estiver visível.

        Agora inclui também a validação do SRC da camada de pontos em comboBoxPontos,
        quando a aba ou modo ativo utiliza pontos (ex: matriz setorial).
        """
        # Verifica se está existe camada no comboBoxPontos
        if self.radioButtonSetorial.isChecked() and self.comboBoxPontos.count() == 0:
            self.pushButtonExecutar.setEnabled(False)
            return

        # Verifica se está no modo que usa comboBoxCamada ou comboBoxPontos
        if self.radioButtonSetorial.isChecked() and self.comboBoxPontos.count() > 0:
            # Usa camada de pontos
            camada_id = self.comboBoxPontos.currentData()
            camada = QgsProject.instance().mapLayer(camada_id) if camada_id else None
            tipo = self.tr("pontos")
        else:
            # Usa camada de polígonos/linhas
            camada_id = self.comboBoxCamada.currentData()
            camada = QgsProject.instance().mapLayer(camada_id) if camada_id else None
            tipo = self.tr("camada")

        # Caso 1: Sem camada
        if not camada:
            self.pushButtonExecutar.setEnabled(False)
            return

        # Caso 2: Camada sem SRC
        if not camada.crs().isValid() or not camada.crs().authid():
            self.pushButtonExecutar.setEnabled(False)
            if self.isVisible():
                self.mostrar_mensagem(self.tr("A camada de {tipo} selecionada está sem projeção").format(tipo=tipo), "Aviso")
            return

        # Caso 3: Camada geográfica (lat/lon)
        if camada.crs().isGeographic():
            self.pushButtonExecutar.setEnabled(False)
            if self.isVisible():
                self.mostrar_mensagem(self.tr("A camada de {tipo} precisa estar na Projeção UTM").format(tipo=tipo), "Aviso")
            return

        # Caso 4: Projeto sem SRC ou em geográfica
        crs_proj = QgsProject.instance().crs()
        if not crs_proj.isValid() or not crs_proj.authid():
            self.pushButtonExecutar.setEnabled(False)
            if self.isVisible():
                self.mostrar_mensagem(self.tr("O projeto precisa estar em UTM"), "Aviso")
            return

        if crs_proj.isGeographic():
            self.pushButtonExecutar.setEnabled(False)
            if self.isVisible():
                self.mostrar_mensagem(self.tr("O projeto precisa estar em UTM"), "Aviso")
            return

        # Tudo OK
        self.pushButtonExecutar.setEnabled(True)

    def populate_combo_box_pontos(self):
        """
        Popula o comboBoxPontos com as camadas de pontos disponíveis no projeto.

        A função realiza as seguintes ações:
        - Salva a camada atualmente selecionada no comboBoxPontos.
        - Bloqueia temporariamente os sinais do comboBoxPontos para evitar atualizações desnecessárias.
        - Limpa o comboBoxPontos antes de preenchê-lo novamente.
        - Adiciona as camadas de pontos disponíveis ao comboBoxPontos.
        - Restaura a seleção da camada anterior, se possível.
        - Desbloqueia os sinais do comboBoxPontos após preenchê-lo.
        """
        old_layer_id = self.comboBoxPontos.currentData() if self.comboBoxPontos.count() else None

        self.comboBoxPontos.blockSignals(True)
        self.comboBoxPontos.clear()

        point_layers = [
            lyr for lyr in QgsProject.instance().mapLayers().values()
            if isinstance(lyr, QgsVectorLayer) and
               QgsWkbTypes.geometryType(lyr.wkbType()) == QgsWkbTypes.GeometryType.PointGeometry]

        for lyr in point_layers:
            self.comboBoxPontos.addItem(lyr.name(), lyr.id())
            # Conecta para atualizar o nome no comboBox ao renomear a camada de pontos
            try:
                lyr.nameChanged.disconnect(self.update_combo_box_item)  # evita conexões duplicadas
            except Exception:
                pass  # nosec B110
            lyr.nameChanged.connect(self.update_combo_box_item)

        if old_layer_id:
            idx = self.comboBoxPontos.findData(old_layer_id)
            if idx != -1:
                self.comboBoxPontos.setCurrentIndex(idx)

        self.comboBoxPontos.blockSignals(False)

    def populate_combo_box_setoresA(self):
        """
        Preenche comboBoxSetoresA com “--” (nenhum) + todos os divisores de 360 °.
        """
        self.comboBoxSetoresA.blockSignals(True)
        self.comboBoxSetoresA.clear()

        self.comboBoxSetoresA.addItem("--", None)          # item neutro

        divisores = [d for d in range(1, 361) if 360 % d == 0]   # 1,2,3…360
        divisores = [d for d in divisores if d >= 5]             # opcional

        for ang in sorted(divisores, reverse=True):              # 360,180,120…
            self.comboBoxSetoresA.addItem(f"{ang}°", ang)

        self.comboBoxSetoresA.setCurrentIndex(0)                 # “--”
        self.comboBoxSetoresA.blockSignals(False)

    def on_spinBoxSetores_changed(self, value):
        """
        Se ‘value’ divide 360, escolhe o passo correspondente.
        Caso contrário, seleciona “--”.
        """
        if value > 0 and 360 % value == 0:
            ang = 360 // value
            idx = self.comboBoxSetoresA.findData(ang)
            if idx != -1:
                self.comboBoxSetoresA.setCurrentIndex(idx)
        else:
            self.comboBoxSetoresA.setCurrentIndex(  # índice 0 → “--”
                self.comboBoxSetoresA.findData(None))

    def on_comboBoxSetoresA_changed(self, idx):
        """
        Sincroniza o spinBoxSetores ao alterar comboBoxSetoresA.
        """
        ang = self.comboBoxSetoresA.currentData()   # passo angular
        if ang:
            self.spinBoxSetores.blockSignals(True)
            self.spinBoxSetores.setValue(360 // ang)
            self.spinBoxSetores.blockSignals(False)
            self.update_setorial_preview()

    def _atualizar_limite_setores(self):
        """
        Define o mínimo de spinBoxSetores:
          • 3   quando radioButtonGeometrico está marcado
          • 1   nos demais casos
        Se o valor atual ficar abaixo do novo mínimo, ajusta para o mínimo.
        """
        if self.radioButtonGeometrico.isChecked():
            minimo = 3
        else:
            minimo = 1

        # Atualiza o limite
        self.spinBoxSetores.setMinimum(minimo)

        # Garante que o valor esteja dentro do novo limite
        if self.spinBoxSetores.value() < minimo:
            self.spinBoxSetores.setValue(minimo)

    def update_setorial_preview(self):
        """Atualiza o preview setorial (círculos/sectores)."""
        self._clear_setorial_scene()
        p = self._collect_setorial_params()     # ① dados geométricos
        self._draw_setorial_shape(**p)          # ② arcos / anéis

        # Só desenha raios se NÃO houver espalhamento
        if p["n_setores"] > 1 and p["offset_px"] == 0:
            self._draw_radial_divisions(**p)

    def _clear_setorial_scene(self):
        """Limpa a cena e redesenha os eixos centrais."""
        self._preview_scene.clear()
        self._draw_preview_axes()

    def _draw_radial_divisions(self, *, cx, cy, raio_px, offset_px, n_setores, ang_rot, pen_rad, **_):
        """começa em inner_px"""
        passo = 360 / n_setores
        for j in range(n_setores):
            # fecha o círculo desenhando a última linha
            ang  = ang_rot + n_setores * passo
            dx   = offset_px * math.cos(math.radians(ang))
            dy   = -offset_px * math.sin(math.radians(ang))
            x0   = cx + dx
            y0   = cy + dy
            x1   = x0 + raio_px * math.cos(math.radians(ang))
            y1   = y0 - raio_px * math.sin(math.radians(ang))
            self._preview_scene.addLine(x0, y0, x1, y1, pen_rad)

    def _sector_ring(self, cx, cy, r_in, r_out, ang0, ang1, dx=0.0, dy=0.0, n_seg=24):
        """
        QPolygonF de um setor anelar entre r_in e r_out (px),
        deslocado por (dx, dy).  Mantém as bordas curvas.
        """
        poly = QPolygonF()

        # arco externo (anti-horário)
        for k in range(n_seg + 1):
            a = math.radians(ang0 + k * (ang1 - ang0) / n_seg)
            poly.append(QPointF(cx + dx + r_out*math.cos(a), cy + dy - r_out*math.sin(a)))

        # arco interno (horário)
        for k in range(n_seg, -1, -1):
            a = math.radians(ang0 + k * (ang1 - ang0) / n_seg)
            poly.append(QPointF(cx + dx + r_in*math.cos(a), cy + dy - r_in*math.sin(a)))

        return poly

    def _sector_quad(self, cx, cy, r_in, r_out, a0_deg, a1_deg, dx=0.0, dy=0.0):
        """
        Retorna QPolygonF com 4 vértices (r_out@a0 → r_out@a1 → r_in@a1 → r_in@a0),
        já transladado por (dx, dy). Usado para anéis no modo Geométrico.
        """
        a0 = math.radians(a0_deg)
        a1 = math.radians(a1_deg)

        pts = [
            QPointF(cx + dx + r_out*math.cos(a0), cy + dy - r_out*math.sin(a0)),
            QPointF(cx + dx + r_out*math.cos(a1), cy + dy - r_out*math.sin(a1)),
            QPointF(cx + dx + r_in *math.cos(a1), cy + dy - r_in *math.sin(a1)),
            QPointF(cx + dx + r_in *math.cos(a0), cy + dy - r_in *math.sin(a0))]
        poly = QPolygonF(pts)
        poly.append(pts[0])          # fecha
        return poly

    def _draw_setorial_shape(self, *, cx, cy, raio_px, offset_px, incremento_px, n_setores, n_aneis, ang_rot, pen_fig, brush_fig, **_):
        """
        Desenha no preview a matriz setorial composta por anéis e setores,
        nos modos circular (arcos) ou geométrico (faces retas), com suporte a múltiplos anéis,
        preenchimento translúcido e deslocamento radial opcional.
        """
        passo      = 360 / n_setores
        base_alpha = 0.20

        # Largura efetiva de cada anel descontando os gaps
        if n_aneis > 0:
            espessura = (raio_px - (n_aneis - 1) * incremento_px) / n_aneis
            espessura = max(1.0, espessura)
        else:
            espessura = raio_px

        # CIRCULAR
        if self.radioButtonCircular.isChecked():
            r_in = 0
            for anel in range(1, n_aneis + 1):
                r_out = r_in + espessura
                alpha = int(255 * base_alpha * (anel / n_aneis))
                brush_ring = QBrush(QColor(0, 0, 255, alpha))

                for j in range(n_setores):
                    a0   = ang_rot + j      * passo
                    a1   = ang_rot + (j+1) * passo
                    amid = (a0 + a1) * 0.5
                    dx   = offset_px * math.cos(math.radians(amid))
                    dy   = -offset_px * math.sin(math.radians(amid))

                    poly = self._sector_ring(cx, cy, r_in, r_out, a0, a1, dx, dy)
                    self._preview_scene.addPolygon(poly, pen_fig, brush_ring)

                r_in = r_out + incremento_px  # abre o gap antes do próximo anel

        # GEOMÉTRICO
        else:
            r_in = 0
            for anel in range(1, n_aneis + 1):
                r_out = r_in + espessura
                alpha = int(255 * base_alpha * (anel / n_aneis))
                brush_ring = QBrush(QColor(0, 0, 255, alpha))

                for j in range(n_setores):
                    a0   = ang_rot + j      * passo
                    a1   = ang_rot + (j+1) * passo
                    amid = (a0 + a1) * 0.5
                    dx   = offset_px * math.cos(math.radians(amid))
                    dy   = -offset_px * math.sin(math.radians(amid))

                    poly = self._sector_quad(cx, cy, r_in, r_out, a0, a1, dx, dy)
                    self._preview_scene.addPolygon(poly, pen_fig, brush_ring)

                r_in = r_out + incremento_px  # espaço vazio antes do próximo anel

    def _collect_setorial_params(self):
        """
        Calcula todos os parâmetros geométricos e estilísticos necessários
        e devolve-os num dicionário para facilitar o desempacotamento com **kwargs.
        """
        view_rect      = self.graphicsViewPreview.viewport().rect()
        w, h           = view_rect.width(), view_rect.height()
        min_wh         = min(w, h)
        cx, cy         = w / 2, h / 2

        # Raio em pixels
        raio_m         = max(0.0, self.doubleSpinBoxRaioS.value())

        offset_m  = max(0.0, self.doubleSpinBoxEspalhar.value())   # NOVO
        offset_px = offset_m * 0.02 * min_wh

        # Número de setores
        n_setores_spin = max(1, self.spinBoxSetores.value())
        passo_ang      = self.comboBoxSetoresA.currentData() or 360
        n_setores      = (360 // passo_ang) if passo_ang != 360 else n_setores_spin

        # Outros controles
        n_aneis        = max(1, self.spinBoxItensAneisS.value())
        ang_rot        = self.spinBoxRotaciona.value()

        incremento_m = max(0.0, self.doubleSpinBoxIncrementoS.value())
        incremento_px = incremento_m * 0.02 * min_wh

        # conversões px
        fator_px      = 0.02 * min_wh
        raio_px       = raio_m * fator_px + 14
        incremento_px = incremento_m * fator_px

      # espessura pretendida
        espessura = (raio_px - (n_aneis - 1) * incremento_px) / n_aneis

        # LIMITE LOCAL (1 px)
        if espessura < 1.0 and n_aneis > 1:
            # calcula o incremento máximo que ainda deixa espessura = 1 px
            incremento_px_max = (raio_px - n_aneis * 1.0) / (n_aneis - 1)
            incremento_px_max = max(0.0, incremento_px_max)
            incremento_m_max  = incremento_px_max / fator_px

            # ajusta o spinBox silenciosamente
            self.doubleSpinBoxIncrementoS.blockSignals(True)
            self.doubleSpinBoxIncrementoS.setValue(incremento_m_max)
            self.doubleSpinBoxIncrementoS.blockSignals(False)

            # usa o novo valor
            incremento_px = incremento_px_max
            espessura     = 1.0

        # Estilos reutilizáveis
        pen_fig   = QPen(Qt.GlobalColor.blue, 0.8); pen_fig.setCosmetic(True)
        brush_fig = QBrush(QColor(0, 255, 0, int(255 * 0.50)))   # azul 20 %

        pen_rad   = QPen(Qt.GlobalColor.blue, 0.9); pen_rad.setCosmetic(True)

        return dict(cx=cx, cy=cy, raio_px=raio_px, offset_px=offset_px, incremento_px=incremento_px, n_setores=n_setores, n_aneis=n_aneis, ang_rot=ang_rot, pen_fig=pen_fig, brush_fig=brush_fig, pen_rad=pen_rad)

    def _sector_poly(self, cx, cy, r, a0_deg, a1_deg):
        """Helper: cria polígono geométrico (triangular) de setor."""
        pts = [QgsPointXY(cx, cy)]  # centro
        for ang_deg in (a0_deg, a1_deg):
            a = math.radians(ang_deg)
            pts.append(QgsPointXY(cx + r * math.cos(a), cy + r * math.sin(a)))
        pts.append(pts[0])  # fecha anel
        return QgsGeometry.fromPolygonXY([pts])

    def _gerar_setores_para_ponto(self, f, cx, cy, p, fields):
        """Cria setores para TODOS os anéis de um ponto."""
        feats = []
        n_set  = p['n_setores']
        passo  = p['passo_ang']
        n_aneis= p['n_aneis']
        inc    = p['inc_m']
        r_base = p['raio_m']
        rot0   = p['ang_rot']
        off    = p['offset_m']
        use_geom = p['use_geom']

        # Espessura de cada anel (mesma lógica do preview)
        if n_aneis > 0:
            esp = (r_base - (n_aneis-1)*inc) / n_aneis if r_base else 0
            esp = max(0.0, esp)
        else:
            esp = r_base

        for i_anel in range(n_aneis):
            r_in  = i_anel * (esp + inc)
            r_out = r_in + esp
            for j in range(n_set):
                a0_deg = rot0 + j*passo
                a1_deg = rot0 + (j+1)*passo
                a0 = math.radians(a0_deg)
                a1 = math.radians(a1_deg)

                # Escolhe geometria
                if use_geom and n_set > 1:
                    geom = self._sector_ring_geom(cx, cy, r_in, r_out, a0, a1)
                else:
                    geom = self._sector_ring_circ(cx, cy, r_in, r_out, a0, a1)

                # Espalhamento radial
                if off:
                    amid = (a0 + a1)*0.5
                    geom.translate(off*math.cos(amid), off*math.sin(amid))

                feat = QgsFeature(fields)
                feat.setGeometry(geom)
                feat.setAttributes(f.attributes())
                feats.append(feat)
        return feats

    def _sector_ring_geom(self, cx, cy, r_in, r_out, a0, a1):
        """Polígono quadrilátero (faces retas) entre dois raios."""
        pts = [
            QgsPointXY(cx + r_out*math.cos(a0), cy + r_out*math.sin(a0)),
            QgsPointXY(cx + r_out*math.cos(a1), cy + r_out*math.sin(a1)),
            QgsPointXY(cx + r_in *math.cos(a1), cy + r_in *math.sin(a1)),
            QgsPointXY(cx + r_in *math.cos(a0), cy + r_in *math.sin(a0))]
        pts.append(pts[0])
        return QgsGeometry.fromPolygonXY([pts])

    def _sector_ring_circ(self, cx, cy, r_in, r_out, a0, a1, n_sub=360):
        """Polígono curvo (duas semi-circunferências)."""
        da = (a1 - a0) / n_sub
        pts = []
        # arco externo
        for k in range(n_sub + 1):
            ang = a0 + k*da
            pts.append(QgsPointXY(cx + r_out*math.cos(ang), cy + r_out*math.sin(ang)))
        # arco interno (reverso)
        for k in range(n_sub, -1, -1):
            ang = a0 + k*da
            pts.append(QgsPointXY(cx + r_in*math.cos(ang), cy + r_in*math.sin(ang)))
        pts.append(pts[0])
        return QgsGeometry.fromPolygonXY([pts])

    def _obter_parametros(self):
        """Extrai parâmetros do formulário."""
        raio_m      = max(0.0, self.doubleSpinBoxRaioS.value())
        ang_rot     = self.spinBoxRotaciona.value()

        n_aneis     = max(1, self.spinBoxItensAneisS.value())
        inc_m       = max(0.0, self.doubleSpinBoxIncrementoS.value())

        n_set_spin  = max(1, self.spinBoxSetores.value())
        passo_combo = self.comboBoxSetoresA.currentData() or 360
        n_setores   = (360 // passo_combo) if passo_combo != 360 else n_set_spin
        passo_ang   = 360.0 / max(1, n_setores)

        offset_m    = max(0.0, self.doubleSpinBoxEspalhar.value())
        dx_offset   = self.spinBoxX.value()
        dy_offset   = self.spinBoxY.value()

        use_geom    = self.radioButtonGeometrico.isChecked()

        return {
            'raio_m': raio_m,
            'ang_rot': ang_rot,
            'n_setores': n_setores,
            'passo_ang': passo_ang,
            'offset_m': offset_m,
            'dx_offset': dx_offset,
            'dy_offset': dy_offset,
            'use_geom': use_geom,
             'n_aneis'   : n_aneis,
            'inc_m'     : inc_m}

    def criar_matriz_setorial_qgis(self):
        """Gera polígonos setoriais em torno dos pontos."""
        # 1) Obter camada de pontos e feições
        camada_pts, feats_src = self._obter_pontos_fonte()
        if not camada_pts or not feats_src:
            return

        # 2) Obter parâmetros
        params = self._obter_parametros()
        use_geom = params['use_geom']
        dx_offset = params['dx_offset']
        dy_offset = params['dy_offset']

        # 3) Criar camada de saída
        layer_out = self._criar_camada_saida(camada_pts, params)
        prov = layer_out.dataProvider()
        fields = layer_out.fields()

        # 4) Processar cada feição
        feats_out_total = []
        for f in feats_src:
            pt_src = f.geometry().asPoint()
            cx = pt_src.x() + dx_offset
            cy = pt_src.y() + dy_offset

            # feats_out_ponto = self._gerar_setores_para_ponto(f, cx, cy, params, use_geom, fields)
            feats_out_ponto = self._gerar_setores_para_ponto(f, cx, cy, params, fields)
            feats_out_total.extend(feats_out_ponto)

        # 5) Adicionar feições à camada de saída
        prov.addFeatures(feats_out_total)
        layer_out.updateExtents()
        QgsProject.instance().addMapLayer(layer_out)

        # 6) Feedback final
        self.mostrar_mensagem(self.tr("{count} feições setoriais criadas.").format(count=len(feats_out_total)), "Sucesso")

        if hasattr(self, "checkBoxNova"):
            self.checkBoxNova.setEnabled(True)
        self._layer_matriz_set = layer_out.id()

    def _ajustar_step_raioS(self):
        """
        Ajusta o passo do doubleSpinBoxRaioS conforme o valor:
          - 1 a 10   → step = 1
          - 10 a 100 → step = 10
          - 100+     → step = 100
        """
        v = self.doubleSpinBoxRaioS.value()
        if v < 10:
            self.doubleSpinBoxRaioS.setSingleStep(1)
        elif v < 100:
            self.doubleSpinBoxRaioS.setSingleStep(10)
        else:
            self.doubleSpinBoxRaioS.setSingleStep(100)

    def _update_espalhar_enabled(self):
        """Habilita/Desabilita o doubleSpinBoxEspalhar conforme spinBoxSetores > 1."""
        if self.spinBoxSetores.value() > 1:
            self.doubleSpinBoxEspalhar.setEnabled(True)
        else:
            self.doubleSpinBoxEspalhar.setValue(0)
            self.doubleSpinBoxEspalhar.setEnabled(False)

    def _update_incrementoS_enabled(self):
        """Habilita/Desabilita o doubleSpinBoxIncrementoS conforme spinBoxItensAneisS > 1."""
        if self.spinBoxItensAneisS.value() > 1:
            self.doubleSpinBoxIncrementoS.setEnabled(True)
        else:
            self.doubleSpinBoxIncrementoS.setValue(0)
            self.doubleSpinBoxIncrementoS.setEnabled(False)

    def _atualizar_estado_comboBoxCamada(self):
        """Habilita ou desabilita comboBoxCamada conforme o modo ativo."""
        if self.radioButtonSetorial.isChecked():
            self.comboBoxCamada.setEnabled(False)
        else:
            self.comboBoxCamada.setEnabled(True)

    def _criar_camada_saida(self, camada_pts, params):
        """
        Cria ou reaproveita a camada de saída setorial.
        Nome: <Orig>_setorial_<Setores>x<Anéis>_<Cir|Geo>
        """
        n_set   = params["n_setores"]
        n_aneis = params.get("n_aneis", 1)
        modo    = "Geo" if params["use_geom"] else "Cir"

        nome = f"{camada_pts.name()}_setorial_{n_set}x{n_aneis}_{modo}"

        # Lidar com 'Nova camada'
        if hasattr(self, "checkBoxNova") and self.checkBoxNova.isChecked():
            self._layer_matriz_set = None

        if self._layer_matriz_set:
            layer = QgsProject.instance().mapLayer(self._layer_matriz_set)
            if layer and layer.isValid():
                # limpa e reaproveita
                layer.setName(nome)
                layer.startEditing()
                layer.dataProvider().truncate()
                layer.commitChanges()
                return layer

        crs = camada_pts.crs().authid()
        layer = QgsVectorLayer(f"Polygon?crs={crs}", nome, "memory")
        layer.dataProvider().addAttributes(camada_pts.fields())
        layer.updateFields()
        QgsProject.instance().addMapLayer(layer)
        self._layer_matriz_set = layer.id()
        return layer

    def update_checkBoxSelecionaS(self):
        """
        Ativa ou desativa o checkBoxSelecionaS (para pontos)
        com base na seleção de feições na camada de pontos selecionada.
        """
        layer = QgsProject.instance().mapLayer(self.comboBoxPontos.currentData())
        cb = self.findChild(QCheckBox, 'checkBoxSelecionaS')
        if layer and cb:
            if layer.selectedFeatureCount() > 0:
                cb.setEnabled(True)
            else:
                cb.setEnabled(False)
                cb.setChecked(False)

    def update_layer_connections_pontos(self):
        """
        Conecta o sinal de seleção de feições da camada de pontos à atualização do checkBoxSelecionaS.
        """
        # Desconecta qualquer conexão antiga
        if hasattr(self, '_layer_pontos_signal'):
            try:
                self._layer_pontos_signal.selectionChanged.disconnect(self.update_checkBoxSelecionaS)
            except Exception:
                pass  # nosec B110

        layer = QgsProject.instance().mapLayer(self.comboBoxPontos.currentData())
        if layer:
            layer.selectionChanged.connect(self.update_checkBoxSelecionaS)
            self._layer_pontos_signal = layer  # Guarda a referência
            self.update_checkBoxSelecionaS()   # Atualiza imediatamente

    def _obter_pontos_fonte(self):
        """Obtém feições de pontos da camada selecionada."""
        camada_pts = QgsProject.instance().mapLayer(self.comboBoxPontos.currentData())
        if not camada_pts or QgsWkbTypes.geometryType(camada_pts.wkbType()) != QgsWkbTypes.GeometryType.PointGeometry:
            self.mostrar_mensagem(self.tr("Camada de pontos inválida."), "Erro")
            return None, []

        # Usa o checkBoxSelecionaS (caso exista)
        selecionar = False
        cb = self.findChild(QCheckBox, 'checkBoxSelecionaS')
        if cb is not None and cb.isChecked():
            selecionar = True

        feats_src = camada_pts.selectedFeatures() if selecionar else list(camada_pts.getFeatures())
        if not feats_src:
            self.mostrar_mensagem(self.tr("Nenhum ponto encontrado na camada."), "Aviso")
            return None, []

        return camada_pts, feats_src

    def _sincronizar_radio_com_tab(self, index):
        """
        Atualiza os radioButtons conforme a aba ativa do tabWidget.
        Essa função é chamada quando o usuário muda diretamente a aba.
        """
        if self.tabWidget.widget(index) == self.tab_retangular:
            self.radioButtonRetangular.setChecked(True)
        elif self.tabWidget.widget(index) == self.tab_polar:
            self.radioButtonPolar.setChecked(True)
        elif self.tabWidget.widget(index) == self.tab_setorial:
            self.radioButtonSetorial.setChecked(True)
        elif self.tabWidget.widget(index) == self.tab_espiral:        # NOVO
            self.radioButtonEspiral.setChecked(True)

    def update_tab_mode(self):
        """
        Atualiza a aba visível e o preview conforme o radioButton selecionado.
        """
        if self.radioButtonRetangular.isChecked():
            idx = self.tabWidget.indexOf(self.tab_retangular)
            if self.tabWidget.currentIndex() != idx:
                self.tabWidget.setCurrentIndex(idx)
            self._preview_scene.clear()
            self._draw_preview_axes()
            self.update_rectangular_preview()

        elif self.radioButtonPolar.isChecked():
            idx = self.tabWidget.indexOf(self.tab_polar)
            if self.tabWidget.currentIndex() != idx:
                self.tabWidget.setCurrentIndex(idx)
            self.update_polar_preview()

        elif self.radioButtonSetorial.isChecked():
            idx = self.tabWidget.indexOf(self.tab_setorial)
            if self.tabWidget.currentIndex() != idx:
                self.tabWidget.setCurrentIndex(idx)
            self.update_setorial_preview()  # você vai criar esse método para o preview setorial

        elif self.radioButtonEspiral.isChecked():        # NOVO
            idx = self.tabWidget.indexOf(self.tab_espiral)
            if self.tabWidget.currentIndex() != idx:
                self.tabWidget.setCurrentIndex(idx)
            self.update_espiral_preview()    # você vai criar esse método

    def atualizar_matriz_se_existe(self):
        """
        Recria automaticamente a matriz (retangular, polar, setorial ou espiral)
        se ela já existir *e* o diálogo estiver aberto.
        """
        if not self.isVisible():          # trava de segurança
            return

        # Retangular
        if self.radioButtonRetangular.isChecked():
            if (self._layer_matriz_ret
                    and QgsProject.instance().mapLayer(self._layer_matriz_ret)):
                self.criar_matriz_retangulos_qgis()

        # Polar
        elif self.radioButtonPolar.isChecked():
            if (self._layer_matriz_pol
                    and QgsProject.instance().mapLayer(self._layer_matriz_pol)):
                self.criar_matriz_polar_qgis()

        # Setorial
        elif self.radioButtonSetorial.isChecked():
            if (self._layer_matriz_set
                    and QgsProject.instance().mapLayer(self._layer_matriz_set)):
                self.criar_matriz_setorial_qgis()

        # Espiral
        layer_id = getattr(self, "_layer_matriz_esp", None)
        if layer_id and QgsProject.instance().mapLayer(layer_id):
            self.criar_matriz_Espiral_qgis()

    def _executar_matriz(self):
        """
        Executa a criação da matriz conforme o modo selecionado
        (retangular, polar, setorial ou espiral).
        """
        if self.radioButtonRetangular.isChecked():
            self.criar_matriz_retangulos_qgis()

        elif self.radioButtonPolar.isChecked():
            self.criar_matriz_polar_qgis()

        elif self.radioButtonSetorial.isChecked():
            self.criar_matriz_setorial_qgis()

        elif self.radioButtonEspiral.isChecked():          # ← NOVO
            self.criar_matriz_Espiral_qgis()

    def closeEvent(self, event):
        self._layer_matriz_ret = None
        self._layer_matriz_pol = None
        self._layer_crs_signal = None
        self._layer_matriz_set = None        # limpa referência
        self._layer_matriz_esp = None      # id da matriz espiral
        super().closeEvent(event)

    def on_pushButtonResetar_clicked(self):
        """
        Reseta os controles do modo atual (Retangular, Polar, Setorial ou Espiral)
        sem quebrar a atualização em tempo real.
        """
        # 1. Lista de widgets que vamos bloquear/desbloquear sinais
        widgets = [
            # retangulares
            self.spinBoxLinha, self.spinBoxColuna,
            self.doubleSpinBoxLinha, self.doubleSpinBoxColuna,
            self.doubleSpinBoxAngulo, self.checkBoxAbsoluto,
            self.checkBoxRotacionarF, self.checkBoxQuadrante,
            # polares
            self.spinBoxX, self.spinBoxY, self.spinBoxXI, self.spinBoxXF,
            self.spinBoxItens, self.spinBoxAngulo, self.doubleSpinBoxRaio,
            self.checkBoxRotacionar, self.spinBoxItensAneis, self.doubleSpinBoxIncremento,
            # setorial
            self.radioButtonCircular, self.radioButtonGeometrico, self.comboBoxSetoresA,
            self.spinBoxSetores, self.spinBoxRotaciona, self.doubleSpinBoxRaioS,
            self.doubleSpinBoxEspalhar, self.spinBoxItensAneisS, self.doubleSpinBoxIncrementoS,
            # espiral  ← NOVOS
            self.spinBoxRepeticoes, self.doubleSpinBoxRadial, self.doubleSpinBoxAngular,
            self.checkBoxAbsolutoE, self.checkBoxDiguais, self.checkBoxRotacionarE,
            # comum
            self.checkBoxNova]

        # 1.1 Bloqueia sinais
        for w in widgets:
            try:
                w.blockSignals(True)
            except Exception:
                pass  # nosec B110

        # 2. Reseta valores conforme o modo ativo
        if self.radioButtonRetangular.isChecked():
            self.spinBoxLinha.setValue(1)
            self.spinBoxColuna.setValue(1)
            self.doubleSpinBoxLinha.setValue(0)
            self.doubleSpinBoxColuna.setValue(0)
            self.doubleSpinBoxAngulo.setValue(0)
            self.checkBoxAbsoluto.setChecked(True)
            self.checkBoxRotacionarF.setChecked(False)
            self.checkBoxQuadrante.setChecked(False)

        elif self.radioButtonPolar.isChecked():
            self.spinBoxX.setValue(0)
            self.spinBoxY.setValue(0)
            self.spinBoxXI.setValue(0)
            self.spinBoxXF.setValue(360)
            self.spinBoxItens.setValue(1)
            self.spinBoxAngulo.setValue(0)
            self.doubleSpinBoxRaio.setValue(1)
            self.checkBoxRotacionar.setChecked(False)
            self.spinBoxItensAneis.setValue(1)
            self.doubleSpinBoxIncremento.setValue(0)

        elif self.radioButtonSetorial.isChecked():
            # circular/geométrico
            if self.radioButtonGeometrico.isChecked():
                self.radioButtonGeometrico.setChecked(True)
                self.radioButtonCircular.setChecked(False)
                self._atualizar_limite_setores()
                self.spinBoxSetores.setValue(self.spinBoxSetores.minimum())
            else:
                self.radioButtonCircular.setChecked(True)
                self.radioButtonGeometrico.setChecked(False)
                self._atualizar_limite_setores()
                self.spinBoxSetores.setValue(1)

            self.comboBoxSetoresA.setCurrentIndex(0)   # "--"
            self.spinBoxRotaciona.setValue(0)
            self.doubleSpinBoxRaioS.setValue(10)
            self._ajustar_step_raioS()
            self.doubleSpinBoxEspalhar.setValue(0)
            self.spinBoxItensAneisS.setValue(1)
            self.doubleSpinBoxIncrementoS.setValue(0)

        elif self.radioButtonEspiral.isChecked():          # ← NOVO MODO
            self.spinBoxRepeticoes.setValue(1)
            self.doubleSpinBoxRadial.setValue(0)
            self.doubleSpinBoxAngular.setValue(0)
            self.checkBoxAbsolutoE.setChecked(True)
            self.checkBoxDiguais.setChecked(False)
            self.checkBoxRotacionarE.setChecked(False)

        # Sempre desmarca “Nova camada”
        self.checkBoxNova.setChecked(False)

        # 3. Desbloqueia sinais
        for w in widgets:
            try:
                w.blockSignals(False)
            except Exception:
                pass  # nosec B110

        # 4. Atualiza pré-visualização e matriz (tempo real)
        if self.radioButtonRetangular.isChecked():
            self.update_rectangular_preview()
        elif self.radioButtonPolar.isChecked():
            self.update_polar_preview()
        elif self.radioButtonSetorial.isChecked():
            self.update_setorial_preview()
        elif self.radioButtonEspiral.isChecked():
            self.update_espiral_preview()

        self.atualizar_matriz_se_existe()   # recria se já existir
        self._update_incrementoS_enabled()
        self._update_espalhar_enabled()

    def _desenhar_blocos_espiral(self, centers: list[tuple[float, float]], rotacionar: bool, cell_w: float, cell_h: float, pen: QPen, brush: QBrush, line_pen: QPen):
        """
        Desenha a espiral de blocos no preview gráfico.

        Para cada centro em `centers`, desenha um retângulo nas dimensões indicadas.
        Se `rotacionar` for True, orienta cada bloco segundo a direção da espiral.
        Também conecta os centros com linhas para visualizar o trajeto.
        """
        scene = self._preview_scene
        n = len(centers)

        # (1) Linha de conexão entre os centros
        for (x0, y0), (x1, y1) in zip(centers, centers[1:]):
            scene.addLine(x0, y0, x1, y1, line_pen)

        # (2) Desenho de cada retângulo
        for i, (x, y) in enumerate(centers):
            item = scene.addRect(-cell_w/2, -cell_h/2, cell_w, cell_h, pen, brush)
            item.setPos(x, y)

            if rotacionar and n > 1:                    # ← proteção
                # calcula vetor tangente por diferença central
                if i == 0:
                    x_prev, y_prev = centers[i]
                    x_next, y_next = centers[i + 1]
                elif i == n - 1:
                    x_prev, y_prev = centers[i - 1]
                    x_next, y_next = centers[i]
                else:
                    x_prev, y_prev = centers[i - 1]
                    x_next, y_next = centers[i + 1]

                dx, dy = x_next - x_prev, y_next - y_prev
                if dx or dy:
                    # ângulo em relação ao eixo X
                    ang = math.degrees(math.atan2(dy, dx))
                    item.setTransformOriginPoint(0, 0)
                    item.setRotation(ang)

    def update_espiral_preview(self):
        """
        Atualiza a pré-visualização da matriz em espiral no widget gráfico.

        Esta função calcula as posições dos blocos (centros) conforme os parâmetros definidos
        na interface (número de repetições, passo radial, passo angular, modo de distância igual, etc.),
        e desenha cada bloco e suas conexões em uma cena QGraphicsScene. O resultado é um preview visual
        que reflete em tempo real as configurações da matriz espiral antes da criação efetiva no QGIS.

        Recursos:
        - Suporta pré-visualização em tempo real de todas as alterações dos parâmetros da espiral.
        - Mostra linhas conectando os centros dos blocos para melhor visualização da trajetória.
        - O tamanho e orientação dos blocos pode variar conforme os controles de rotação e modo de distância.
        """
        scene = self._preview_scene
        scene.clear()
        self._draw_preview_axes()

        n_rep        = self.spinBoxRepeticoes.value()
        step_r       = self.doubleSpinBoxRadial.value()
        step_a       = self.doubleSpinBoxAngular.value()
        abs_ok       = self.checkBoxAbsolutoE.isChecked()
        dist_iguais  = self.checkBoxDiguais.isChecked()
        rotacionar   = self.checkBoxRotacionarE.isChecked()      # << NOVO

        if n_rep < 1 or step_r < 0:
            return

        # centro
        rect = self.graphicsViewPreview.viewport().rect()
        w, h = rect.width(), rect.height()
        cx, cy = w / 2, h / 2

        cell_w, cell_h = 8, 6
        pen   = QPen(Qt.GlobalColor.blue, 0.6);       pen.setCosmetic(True)
        brush = QBrush(QColor(255, 170, 0, 100))
        line_pen = QPen(Qt.GlobalColor.darkGray, 0.4); line_pen.setCosmetic(True)

        # 2.1  Calcula a lista de centros (points) de acordo com o modo.
        centers = []

        if dist_iguais:
            # ESPIRAL COM DISTÂNCIA IGUAL
            a = 0
            b = step_r / math.radians(step_a) if step_a != 0 else step_r / 0.01
            ang, r = 0.0, a

            for i in range(n_rep):
                x = cx + r * math.cos(ang)
                y = cy - r * math.sin(ang)
                centers.append((x, y))

                if i < n_rep - 1:
                    delta_theta = step_r / max(1e-9, math.sqrt(r**2 + b**2))
                    ang += delta_theta
                    r = a + b * ang
        else:
            # MODO PADRÃO
            passo_px = (cell_w + step_r) if abs_ok else (0.05 * cell_w + step_r)

            for i in range(n_rep):
                r   = i * passo_px
                ang = math.radians(i * step_a)
                x   = cx + r * math.cos(ang)
                y   = cy - r * math.sin(ang)
                centers.append((x, y))

        # 2.2  Desenha
        if centers:
            self._desenhar_blocos_espiral(centers, rotacionar, cell_w, cell_h, pen, brush, line_pen)

    def criar_matriz_Espiral_qgis(self):
        """
        Gera uma matriz do tipo ESPIRAL clonando as feições da camada escolhida
        no comboBoxCamada.  Respeita todos os parâmetros da UI e grava o
        resultado numa camada de memória (editável).
        """
        # 1) parâmetros da UI
        n_rep       = self.spinBoxRepeticoes.value()
        step_r      = self.doubleSpinBoxRadial.value()
        step_a      = self.doubleSpinBoxAngular.value()
        abs_ok      = self.checkBoxAbsolutoE.isChecked()
        dist_iguais = self.checkBoxDiguais.isChecked()
        rotacionar  = self.checkBoxRotacionarE.isChecked()

        if n_rep < 1 or step_r < 0:
            self.mostrar_mensagem(self.tr("Parâmetros da espiral inválidos."), "Aviso")
            return

        # 2) camada-fonte
        src_layer = QgsProject.instance().mapLayer(self.comboBoxCamada.currentData())
        if not src_layer or src_layer.type() != QgsMapLayer.LayerType.VectorLayer:
            self.mostrar_mensagem(self.tr("Camada inválida ou não encontrada."), "Erro")
            return

        feats_src = (src_layer.selectedFeatures()
                     if self.findChild(QCheckBox, 'checkBoxSeleciona').isChecked()
                     else list(src_layer.getFeatures()))
        if not feats_src:
            self.mostrar_mensagem(self.tr("Nenhuma feição para clonar."), "Aviso")
            return

        # 3) bounding box dos blocos
        bbox = QgsGeometry.unaryUnion([f.geometry() for f in feats_src]).boundingBox()
        cell_w, cell_h = bbox.width(), bbox.height()
        if cell_w == 0 or cell_h == 0:
            self.mostrar_mensagem(self.tr("Feições sem dimensão espacial."), "Erro")
            return

        # 4) calcula centros
        cx0, cy0 = bbox.center().x(), bbox.center().y()
        centers  = []

        if dist_iguais:
            a = 0
            b = step_r / math.radians(step_a) if step_a else step_r / 0.01
            ang, r = 0.0, a
            for i in range(n_rep):
                x = cx0 + r * math.cos(ang)
                y = cy0 + r * math.sin(ang)
                centers.append((x, y))
                if i < n_rep - 1:
                    delta_theta = step_r / max(1e-9, math.sqrt(r**2 + b**2))
                    ang += delta_theta
                    r   = a + b * ang
        else:
            passo_r = (cell_w + step_r) if abs_ok else (0.05*cell_w + step_r)
            for i in range(n_rep):
                r   = i * passo_r
                ang = math.radians(i * step_a)
                x   = cx0 + r * math.cos(ang)
                y   = cy0 + r * math.sin(ang)
                centers.append((x, y))

        # 5) cria / obtém camada-destino
        proj = QgsProject.instance()
        layer_id = getattr(self, "_layer_matriz_esp", None)
        layer_esp = proj.mapLayer(layer_id) if layer_id else None
        invalid = layer_esp is None or not layer_esp.isValid()

        nome_base = src_layer.name()
        nome_espiral = f"{nome_base}_espiral_x{n_rep}"

        # Se checkBoxNova estiver marcado, sempre cria nova camada
        if hasattr(self, "checkBoxNova") and self.checkBoxNova.isChecked():
            self._layer_matriz_esp = None
            layer_esp = None
            invalid = True

        if invalid or layer_esp.wkbType() != src_layer.wkbType():
            uri = (f"{QgsWkbTypes.displayString(src_layer.wkbType())}"
                   f"?crs={src_layer.crs().authid()}")
            layer_esp = QgsVectorLayer(uri, nome_espiral, "memory")
            layer_esp.dataProvider().addAttributes(src_layer.fields())
            layer_esp.updateFields()
            proj.addMapLayer(layer_esp)
        else:
            # Atualiza nome ao alterar n_rep
            if layer_esp.name() != nome_espiral:
                layer_esp.setName(nome_espiral)
            layer_esp.startEditing()
            layer_esp.dataProvider().truncate()
            layer_esp.commitChanges()

        # self._layer_matriz_esp = layer_esp   # guarda ponteiro válido
        self._layer_matriz_esp = layer_esp.id()       # guarda somente o ID
        dst_layer = layer_esp

        # 6) clona & posiciona feições
        dst_layer.startEditing()
        feats_out   = []
        n_centers   = len(centers)

        for i, (cx, cy) in enumerate(centers):

            # ângulo tangente (igual ao preview)
            dx = dy = 0.0

            if rotacionar and n_centers > 1:
                if i == 0:
                    px, py = centers[0]
                    nx, ny = centers[1]
                elif i == n_centers - 1:
                    px, py = centers[-2]
                    nx, ny = centers[-1]
                else:
                    px, py = centers[i - 1]
                    nx, ny = centers[i + 1]

                dx, dy = nx - px, ny - py
                ang_deg = math.degrees(math.atan2(-dy, dx))
            else:
                ang_deg = 0.0

            # clona cada feição-origem
            for feat in feats_src:
                new_feat = QgsFeature(dst_layer.fields())
                g        = QgsGeometry(feat.geometry())

                # desloca clone
                g.translate(cx - cx0, cy - cy0)

                # gira em torno do centroide, se necessário
                if rotacionar and (dx or dy):
                    c_xy = QgsPointXY(g.centroid().asPoint())
                    g.rotate(ang_deg, center=c_xy)

                new_feat.setGeometry(g)
                new_feat.setAttributes(feat.attributes())
                feats_out.append(new_feat)

        dst_layer.dataProvider().addFeatures(feats_out)
        dst_layer.commitChanges()
        dst_layer.updateExtents()

        # 7) feedback
        self.mostrar_mensagem(self.tr("Matriz espiral criada com {centers_count} × {source_count} = {output_count} feições.").format(centers_count=len(centers), source_count=len(feats_src), output_count=len(feats_out)), "Sucesso")

        # Habilita checkBoxNova após criar a matriz espiral pela primeira vez
        if hasattr(self, "checkBoxNova"):
            self.checkBoxNova.setEnabled(True)