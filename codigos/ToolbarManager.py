from qgis.PyQt.QtCore import QSettings, QTimer
from qgis.PyQt.QtWidgets import QAction

try:
    from .DialogoContatoFormSubmit import DialogoContatoFormSubmit
except ImportError:
    from DialogoContatoFormSubmit import DialogoContatoFormSubmit

CHAVE_PUSHBUTTONQ_VISTO = "TempoSalvoTools/Contato/pushButtonQ_visto"

class ToolbarManager:
    def __init__(self, iface, dialog):
        """
        Inicializa o gerenciador de toolbar.

        :param iface: A interface do QGIS.
        :param dialog: O diálogo que contém os checkboxes.
        """
        self.iface = iface
        self.dialog = dialog
        self.settings = QSettings()

        self._pushButtonQ_timer = None
        self._pushButtonQ_step = 0
        self._pushButtonQ_original_style = ""

        # Nome das configurações e checkboxes associadas
        self.checkbox_mapping = {
            'checkBox_setasraster': 'add_to_toolbar_setasraster',
            'checkBox_curvas': 'add_to_toolbar_curvas',
            'checkBox_fotos_kmz': 'add_to_toolbar_fotos_kmz',
            'checkBox_linha_poligono': 'add_to_toolbar_linha_poligono',
            'checkBox_grade_utm_geo': 'add_to_toolbar_grade_utm_geo',
            'checkBox_cotasraster': 'add_to_toolbar_cotasraster',
            'checkBox_poligono_linha': 'add_to_toolbar_poligono_linha',
            'checkBox_op_linhas': 'add_to_toolbar_operacoeslinhas',
            'checkBox_linhas_dentro_poligonos': 'add_to_toolbar_dentrolinhas',
            'checkBox_cria_malhas': 'add_to_toolbar_malha',
            'checkBox_rasterizar_malhas': 'add_to_toolbar_rasterizar_malha',
            'checkBox_converter_para_malhas': 'add_to_toolbar_converte_malha',
            'checkBox_criar_plato': 'add_to_toolbar_plato_mdt',
            'checkBox_calculos_volume': 'add_to_toolbar_volume_mdt',
            'checkBox_grafico_talude': 'add_to_toolbar_grafico_PyQt',
            'checkBox_grafico_perfis': 'add_to_toolbar_grafico_perfil',
            'checkBox_grafico_estruturas': 'add_to_toolbar_grafico_estruturas',
            'checkBox_imagens_kmz': 'add_to_toolbar_imagens_kmz',
            'checkBox_XLS_ODS': 'add_to_toolbar_pontos_xls',
            'checkBox_matrizes': 'add_to_toolbar_matrizes',
            'checkBox_geopoligonos': 'add_to_toolbar_geoprocessar_poligonos',
            'checkBox_dimensionar': 'add_to_toolbar_dimensionar',
            'checkBox_notas': 'add_to_toolbar_notas',
            'checkBox_drenagem': 'add_to_toolbar_redes_drenagem',
            'checkBox_tabelas': 'add_to_toolbar_tabelas',
        }

        # Carrega as configurações iniciais
        self.load_settings()

        # Conecta o botão de contato/suporte
        self.configurar_pushButtonQ()

        # # Conecta os checkboxes às funções de salvamento e atualização da toolbar
        self.dialog.checkBox_setasraster.stateChanged.connect(lambda state: self.save_setting('checkBox_setasraster', state))
        self.dialog.checkBox_curvas.stateChanged.connect(lambda state: self.save_setting('checkBox_curvas', state))
        self.dialog.checkBox_fotos_kmz.stateChanged.connect(lambda state: self.save_setting('checkBox_fotos_kmz', state))
        self.dialog.checkBox_linha_poligono.stateChanged.connect( lambda state: self.save_setting('checkBox_linha_poligono', state))
        self.dialog.checkBox_grade_utm_geo.stateChanged.connect(lambda state: self.save_setting('checkBox_grade_utm_geo', state))
        self.dialog.checkBox_cotasraster.stateChanged.connect(lambda state: self.save_setting('checkBox_cotasraster', state))
        self.dialog.checkBox_poligono_linha.stateChanged.connect( lambda state: self.save_setting('checkBox_poligono_linha', state))
        self.dialog.checkBox_op_linhas.stateChanged.connect(lambda state: self.save_setting('checkBox_op_linhas', state))
        self.dialog.checkBox_linhas_dentro_poligonos.stateChanged.connect(lambda state: self.save_setting('checkBox_linhas_dentro_poligonos', state))
        self.dialog.checkBox_cria_malhas.stateChanged.connect(lambda state: self.save_setting('checkBox_cria_malhas', state))
        self.dialog.checkBox_rasterizar_malhas.stateChanged.connect(lambda state: self.save_setting('checkBox_rasterizar_malhas', state))
        self.dialog.checkBox_converter_para_malhas.stateChanged.connect(lambda state: self.save_setting('checkBox_converter_para_malhas', state))
        self.dialog.checkBox_criar_plato.stateChanged.connect(lambda state: self.save_setting('checkBox_criar_plato', state))
        self.dialog.checkBox_calculos_volume.stateChanged.connect(lambda state: self.save_setting('checkBox_calculos_volume', state))
        self.dialog.checkBox_grafico_talude.stateChanged.connect(lambda state: self.save_setting('checkBox_grafico_talude', state))
        self.dialog.checkBox_grafico_perfis.stateChanged.connect(lambda state: self.save_setting('checkBox_grafico_perfis', state))
        self.dialog.checkBox_grafico_estruturas.stateChanged.connect(lambda state: self.save_setting('checkBox_grafico_estruturas', state))
        self.dialog.checkBox_imagens_kmz.stateChanged.connect(lambda state: self.save_setting('checkBox_imagens_kmz', state))
        self.dialog.checkBox_XLS_ODS.stateChanged.connect(lambda state: self.save_setting('checkBox_XLS_ODS', state))
        self.dialog.checkBox_matrizes.stateChanged.connect(lambda state: self.save_setting('checkBox_matrizes', state))
        self.dialog.checkBox_geopoligonos.stateChanged.connect(lambda state: self.save_setting('checkBox_geopoligonos', state))
        self.dialog.checkBox_dimensionar.stateChanged.connect(lambda state: self.save_setting('checkBox_dimensionar', state))
        self.dialog.checkBox_notas.stateChanged.connect(lambda state: self.save_setting('checkBox_notas', state))
        self.dialog.checkBox_drenagem.stateChanged.connect(lambda state: self.save_setting('checkBox_drenagem', state))
        self.dialog.checkBox_tabelas.stateChanged.connect(lambda state: self.save_setting('checkBox_tabelas', state))

    def tr(self, message):
        """Traduz os textos deste gerenciador."""
        return self.dialog.tr(message)

    def configurar_pushButtonQ(self):
        """
        Configura o pushButtonQ para abrir o diálogo de contato e exibir
        uma animação visual apenas enquanto o usuário ainda não clicou nele.
        """
        if not hasattr(self.dialog, "pushButtonQ"):
            return

        botao = self.dialog.pushButtonQ

        try:
            botao.clicked.disconnect(self.abrir_dialogo_contato)
        except (TypeError, RuntimeError):
            pass  # nosec B110

        self._pushButtonQ_original_style = botao.styleSheet() or ""

        botao.setToolTip(self.tr("Enviar mensagem ao criador do Plugin Tempo Salvo Tools"))
        botao.clicked.connect(self.abrir_dialogo_contato)

        ja_visto = self.settings.value(CHAVE_PUSHBUTTONQ_VISTO, False, type=bool)

        if ja_visto:
            self._parar_animacao_pushButtonQ()
        else:
            self._iniciar_animacao_pushButtonQ()

    def _iniciar_animacao_pushButtonQ(self):
        """
        Inicia uma animação de borda no pushButtonQ.
        A borda alterna entre azul, vermelho e verde, com efeito de giro.
        """
        if not hasattr(self.dialog, "pushButtonQ"):
            return

        if self._pushButtonQ_timer is not None:
            if self._pushButtonQ_timer.isActive():
                return

        self._pushButtonQ_step = 0
        self._pushButtonQ_timer = QTimer(self.dialog)
        self._pushButtonQ_timer.timeout.connect(self._animar_pushButtonQ)
        self._pushButtonQ_timer.start(180)

        self._animar_pushButtonQ()

    def _parar_animacao_pushButtonQ(self):
        """
        Para a animação e restaura o estilo original do pushButtonQ.
        """
        if self._pushButtonQ_timer is not None:
            self._pushButtonQ_timer.stop()
            self._pushButtonQ_timer.deleteLater()
            self._pushButtonQ_timer = None

        if hasattr(self.dialog, "pushButtonQ"):
            self.dialog.pushButtonQ.setStyleSheet(
                self._pushButtonQ_original_style)

    def _animar_pushButtonQ(self):
        """
        Cria uma borda animada com azul, vermelho e verde aparecendo
        simultaneamente, girando ao redor do pushButtonQ.
        """
        if not hasattr(self.dialog, "pushButtonQ"):
            return

        botao = self.dialog.pushButtonQ

        azul = "#1a73e8"
        vermelho = "#d93025"
        verde = "#188038"

        esquemas = [
            [azul, vermelho, verde, azul],
            [azul, azul, vermelho, verde],
            [verde, azul, azul, vermelho],
            [vermelho, verde, azul, azul]]

        bordas = esquemas[self._pushButtonQ_step % len(esquemas)]

        cor_topo = bordas[0]
        cor_direita = bordas[1]
        cor_baixo = bordas[2]
        cor_esquerda = bordas[3]

        raio = max(1, min(botao.width(), botao.height()) // 2)

        botao.setStyleSheet(f"""
            QPushButton {{
                border-top: 3px solid {cor_topo};
                border-right: 3px solid {cor_direita};
                border-bottom: 3px solid {cor_baixo};
                border-left: 3px solid {cor_esquerda};
                border-radius: {raio}px;
                background-color: #ffffff;
                padding: 2px 2px;
            }}

            QPushButton:hover {{
                background-color: #f3f7ff;
            }}
        """)

        self._pushButtonQ_step += 1

    def abrir_dialogo_contato(self):
        """
        Abre o diálogo de contato e desativa definitivamente a animação
        do pushButtonQ para este perfil do QGIS.
        """
        self.settings.setValue(CHAVE_PUSHBUTTONQ_VISTO, True)
        self._parar_animacao_pushButtonQ()

        dlg = DialogoContatoFormSubmit(
            iface=self.iface,
            parent=self.dialog)

        dlg.exec()

    def load_settings(self):
        """
        Carrega as configurações armazenadas para os checkboxes.
        """
        for checkbox, setting_key in self.checkbox_mapping.items():
            state = self.settings.value(setting_key, False, type=bool)
            getattr(self.dialog, checkbox).setChecked(state)

    def save_setting(self, checkbox, state):
        """
        Salva o estado do checkbox nas configurações e atualiza a barra de ferramentas.

        :param checkbox: O nome do checkbox.
        :param state: O estado do checkbox (0 para não marcado, 2 para marcado).
        """
        setting_key = self.checkbox_mapping[checkbox]
        should_add = state == 2
        self.settings.setValue(setting_key, should_add)

        # Atualiza a barra de ferramentas imediatamente
        action = self.get_action_for_checkbox(checkbox)
        if action:
            if should_add:
                self.iface.addToolBarIcon(action)
            else:
                self.iface.removeToolBarIcon(action)

    def should_add_to_toolbar(self, setting_key):
        """
        Verifica se a ação deve ser adicionada à barra de ferramentas.

        :param setting_key: A chave de configuração associada à ação.
        :return: True se a ação deve ser adicionada à barra de ferramentas, False caso contrário.
        """
        return self.settings.value(setting_key, False, type=bool)

    def get_action_for_checkbox(self, checkbox):
        """
        Retorna a ação associada ao checkbox para que ela possa ser adicionada/removida da toolbar.

        :param checkbox: O nome do checkbox.
        :return: A QAction correspondente.
        """
        # Retorne a ação correspondente ao checkbox
        if checkbox == 'checkBox_setasraster':
            return self.iface.mainWindow().findChild(QAction, 'setasraster_action')
        elif checkbox == 'checkBox_curvas':
            return self.iface.mainWindow().findChild(QAction, 'curvas_action')  # Retorna a ação para curvas
        elif checkbox == 'checkBox_fotos_kmz':
            return self.iface.mainWindow().findChild(QAction, 'fotos_action')  # Retorna a ação para fotos_kmz
        elif checkbox == 'checkBox_linha_poligono':
            return self.iface.mainWindow().findChild(QAction, 'linha_poligono_action')  # Retorna a ação para linha_poligono
        elif checkbox == 'checkBox_grade_utm_geo':
            return self.iface.mainWindow().findChild(QAction, 'grade_utm_geo_action')  # Retorna a ação para grade_utm_geo
        elif checkbox == 'checkBox_cotasraster':
            return self.iface.mainWindow().findChild(QAction, 'cotasraster_action')  # Retorna a ação para cotasraster
        elif checkbox == 'checkBox_poligono_linha':
            return self.iface.mainWindow().findChild(QAction, 'poligono_linha_action')  # Retorna a ação para poligono_linha
        elif checkbox == 'checkBox_op_linhas':
            return self.iface.mainWindow().findChild(QAction, 'operacoeslinhas_action')
        elif checkbox == 'checkBox_linhas_dentro_poligonos':
            return self.iface.mainWindow().findChild(QAction, 'dentrolinhas_action')
        elif checkbox == 'checkBox_cria_malhas':
            return self.iface.mainWindow().findChild(QAction, 'malha_action')
        elif checkbox == 'checkBox_rasterizar_malhas':
            return self.iface.mainWindow().findChild(QAction, 'rasterizarmalha_action')
        elif checkbox == 'checkBox_converter_para_malhas':
            return self.iface.mainWindow().findChild(QAction, 'malhaconverte_action')
        elif checkbox == 'checkBox_criar_plato':
            return self.iface.mainWindow().findChild(QAction, 'plato_mdt_action')
        elif checkbox == 'checkBox_calculos_volume':
            return self.iface.mainWindow().findChild(QAction, 'volume_mdt_action')
        elif checkbox == 'checkBox_grafico_talude':
            return self.iface.mainWindow().findChild(QAction, 'grafico_PyQt_action')
        elif checkbox == 'checkBox_grafico_perfis':
            return self.iface.mainWindow().findChild(QAction, 'grafico_perfil_action')
        elif checkbox == 'checkBox_grafico_estruturas':
            return self.iface.mainWindow().findChild(QAction, 'grafico_estruturas_action')
        elif checkbox == 'checkBox_imagens_kmz':
            return self.iface.mainWindow().findChild(QAction, 'imagens_action')
        elif checkbox == 'checkBox_XLS_ODS':
            return self.iface.mainWindow().findChild(QAction, 'pontos_xls_action')
        elif checkbox == 'checkBox_matrizes':
            return self.iface.mainWindow().findChild(QAction, 'matrizes_action')
        elif checkbox == 'checkBox_geopoligonos':
            return self.iface.mainWindow().findChild(QAction, 'geoprocessar_poligonos_action')
        elif checkbox == 'checkBox_dimensionar':
            return self.iface.mainWindow().findChild(QAction, 'dimensionar_action')
        elif checkbox == 'checkBox_notas':
            return self.iface.mainWindow().findChild(QAction, 'notas_action')
        elif checkbox == 'checkBox_drenagem':
            return self.iface.mainWindow().findChild(QAction, 'redes_drenagem_action')
        elif checkbox == 'checkBox_tabelas':
            return self.iface.mainWindow().findChild(QAction, 'tabelas_action')
        return None