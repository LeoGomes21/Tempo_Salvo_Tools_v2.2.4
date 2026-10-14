from qgis.core import QgsProject, QgsVectorLayer, QgsWkbTypes, QgsField, QgsFeature, QgsGeometry, Qgis, QgsPoint, QgsLineSymbol, QgsDistanceArea, QgsFields, QgsPalLayerSettings, QgsVectorLayerSimpleLabeling, QgsTextFormat
from qgis.PyQt.QtWidgets import QDialog, QCheckBox, QPushButton, QColorDialog, QHBoxLayout, QProgressBar
from qgis.gui import QgsProjectionSelectionDialog
from qgis.PyQt.QtGui import QColor
from qgis.PyQt.QtCore import Qt, QMetaType, QCoreApplication
from qgis.PyQt import uic
import processing
import time
import os
import re

FORM_CLASS, _ = uic.loadUiType(os.path.join(
    os.path.dirname(__file__), 'PoligonoLinha.ui'))
"""
Carrega a interface do usuário a partir de um arquivo .ui gerado pelo Qt Designer.

Parâmetros:
- Nenhum parâmetro explícito é passado diretamente para essa linha, mas a função uic.loadUiType é chamada com o caminho para o arquivo .ui.

A linha realiza as seguintes ações:
- Usa a função uic.loadUiType para carregar a definição da interface do usuário a partir de um arquivo .ui.
- O caminho para o arquivo .ui é construído usando os.path.join e os.path.dirname para garantir que o caminho seja relativo ao diretório atual do arquivo de código.
- A função uic.loadUiType retorna uma tupla contendo a classe do formulário (FORM_CLASS) e um objeto de base (ignorado com _).
"""

class PoligonoManager(QDialog, FORM_CLASS):
    """
    A classe PoligonoManager gerencia a interface gráfica e funcionalidades para a conversão de polígonos em linhas no QGIS.

    Herança:
    QDialog : QWidget
        Interface de diálogo do Qt.
    FORM_CLASS : QWidget
        Interface carregada a partir do arquivo .ui gerado no Qt Designer.

    Atributos:
    iface : objeto
        Interface do QGIS para interação com a aplicação.
    parent : QWidget, opcional
        O widget pai (se houver).
    FORM_CLASS : QWidget
        A interface do arquivo .ui carregado.

    A função realiza as seguintes ações:
    - Carrega a interface do arquivo .ui e inicializa a janela de diálogo para o usuário.
    """

    def __init__(self, iface, parent=None):
        """
        Construtor da classe PoligonoManager, responsável por inicializar a interface e os widgets.

        Parâmetros:
        self : objeto
            Referência à instância atual da classe.
        iface : objeto
            Interface do QGIS, usada para interagir com a aplicação QGIS.
        parent : QWidget, opcional
            O widget pai, se houver (por padrão, é None).

        A função realiza as seguintes ações:
        - Inicializa a interface com base no arquivo .ui gerado pelo Qt Designer.
        - Configura os widgets e elementos da interface, como comboBoxCamada, lineEditNome e botões.
        - Conecta os sinais aos seus slots (funções de resposta).
        - Preenche o comboBoxCamada com as camadas disponíveis no projeto.
        - Atualiza o lineEditNome com o nome da camada inicialmente selecionada.
        - Configura o comportamento de atualização automática do comboBox quando camadas são adicionadas ou removidas.
        """
        super(PoligonoManager, self).__init__(parent)  # Inicializa a classe base QDialog
        
        self.iface = iface  # Armazena a referência da interface QGIS
        
        # Configura a interface do usuário a partir do Designer.
        self.setupUi(self)

        # Altera o título da janela
        self.setWindowTitle(self.tr("Converte Polígonos para Linhas"))

        # Inicializa os widgets do diálogo
        self.comboBoxCamada = self.comboBoxCamada  # Referência ao comboBoxCamada
        self.lineEditNome = self.lineEditNome  # Referência ao lineEditNome
        self.pushButtonConverter = self.pushButtonConverter  # Referência ao botão de conversão
        self.pushButtonFechar = self.pushButtonFechar  # Referência ao botão de fechar

        # Configura o doubleSpinBoxEspessura com valor padrão
        self.doubleSpinBoxEspessura = self.doubleSpinBoxEspessura  # Referência ao spinBox de espessura
        self.doubleSpinBoxEspessura.setValue(0.50)  # Define o valor padrão para a espessura da linha

        # Adiciona o botão de deletar texto ao lineEditNome
        self.clear_button = QPushButton("✖", self.lineEditNome)
        self.clear_button.setCursor(Qt.CursorShape.ArrowCursor)
        self.clear_button.setStyleSheet("""
            QPushButton {
                border: none; 
                padding: 0px; 
                color: gray; 
                background-color: white; 
                border-radius: 10px;
                font-weight: bold;
            }
            QPushButton:hover {
                background-color: #ffcccc;
            }
        """)
        self.clear_button.setFixedSize(15, 15)
        self.clear_button.hide()
        self.clear_button.clicked.connect(self.clear_poligono_edit)

        layout = QHBoxLayout(self.lineEditNome)
        layout.addStretch()
        layout.addWidget(self.clear_button)
        layout.setContentsMargins(0, 0, 0, 0)
        self.lineEditNome.setLayout(layout)

        self.selected_crs = None  # Armazena o CRS selecionado pelo usuário

        self._connected_layer = None
        self.selected_color = None

        # Conecta os sinais aos slots
        self.connect_signals()

        # Preenche o comboBox com camadas de linha
        self.populate_combo_box()

        # Atualiza o lineEditNome com a camada selecionada inicialmente
        self.update_poligono_edit_nome()

        # Conecta sinais do projeto para atualizar comboBox quando camadas forem adicionadas, removidas ou renomeadas
        QgsProject.instance().layersAdded.connect(self.populate_combo_box)
        QgsProject.instance().layersRemoved.connect(self.populate_combo_box)
        QgsProject.instance().layerWillBeRemoved.connect(self.populate_combo_box)

        # Armazena o estilo padrão do botão de cor
        self.pushButtonCor_default_style = self.pushButtonCor.styleSheet()
        self.pushButtonCorRotulo_default_style = self.pushButtonCorRotulo.styleSheet()

        # Configura o lineEditSRC para ser não editável, mas selecionável
        self.lineEditSRC = self.lineEditSRC
        self.lineEditSRC.setReadOnly(True)
        # self.lineEditSRC.setStyleSheet("QLineEdit { background-color: #f0f0f0; }")
        self.lineEditSRC.setToolTip(self.tr("Projeção da camada Convertida"))

        # Adiciona a funcionalidade para o pushButtonCorRotulo
        self.pushButtonCorRotulo.clicked.connect(self.choose_label_color)

        # Variável para armazenar a cor selecionada para o rótulo
        self.selected_label_color = None

    def tr(self, message):
        """
        Traduz textos deste diálogo.
        O contexto precisa ser estável para o Qt Linguist encontrar as traduções.
        """
        return QCoreApplication.translate("PoligonoManager", message)

    def connect_signals(self):
        """
        Conecta os sinais dos widgets da interface aos seus respectivos slots (funções de resposta).

        Parâmetros:
        self : objeto
            Referência à instância atual da classe.

        A função realiza as seguintes ações:
        - Conecta as mudanças de seleção no comboBoxCamada para atualizar os campos e widgets relacionados.
        - Conecta os checkboxes de atributos para atualizar o comboBoxRotulagem e a seleção de atributos.
        - Conecta o botão de conversão (pushButtonConverter) à função que realiza a conversão de feições.
        - Conecta o botão de cor (pushButtonCor) ao diálogo de seleção de cor.
        - Conecta o doubleSpinBoxEspessura à função que ajusta a espessura do botão de cor em tempo real.
        - Conecta o botão de fechar (pushButtonFechar) à função que fecha o diálogo.
        - Conecta o lineEditNome à função que valida o nome do polígono.
        - Conecta o botão de projeção (pushButtonProjecao) ao diálogo de escolha de CRS.
        - Conecta o comboBoxRotulagem para atualizar o estado do botão de cor do rótulo (pushButtonCorRotulo).
        - Conecta as mudanças de seleção no comboBoxCamada para atualizar os estados dos botões de conversão e projeção.
        - Conecta a seleção de feições na camada atual para atualizar o checkBoxSeleciona.
        """
        # Conecta a mudança de seleção no comboBoxCamada para atualizar o lineEditNome
        self.comboBoxCamada.currentIndexChanged.connect(self.update_layer_connections)

        # Conecta a mudança de seleção no comboBoxCamada para atualizar o lineEditNome
        self.comboBoxCamada.currentIndexChanged.connect(self.update_poligono_edit_nome)

        # Conectar mudanças de seleção no comboBoxCamada para atualizar o comboBoxRotulagem
        self.comboBoxCamada.currentIndexChanged.connect(self.populate_comboBoxRotulagem)

        # Conectar mudanças nos checkboxes para atualizar o comboBoxRotulagem
        self.findChild(QCheckBox, 'checkBoxID').stateChanged.connect(self.populate_comboBoxRotulagem)
        self.findChild(QCheckBox, 'checkBoxComprimento').stateChanged.connect(self.populate_comboBoxRotulagem)
        self.findChild(QCheckBox, 'checkBoxRemover').stateChanged.connect(self.populate_comboBoxRotulagem)

        # Conecta o clique do botão de conversão à função de conversão
        self.pushButtonConverter.clicked.connect(self.convert_and_process_layer)

        # Conecta o checkBoxAdicionar para selecionar ou desmarcar os outros checkboxes
        self.findChild(QCheckBox, 'checkBoxAdicionar').stateChanged.connect(self.toggle_attribute_checkboxes)

        # Conecta os outros checkboxes para atualizar o checkBoxAdicionar
        self.findChild(QCheckBox, 'checkBoxID').stateChanged.connect(self.update_adicionar_checkbox)

        self.findChild(QCheckBox, 'checkBoxComprimento').stateChanged.connect(self.update_adicionar_checkbox)

        # Conecta o pushButtonCor para abrir o diálogo de seleção de cor
        self.pushButtonCor.clicked.connect(self.choose_color)

        # Conecta o doubleSpinBoxEspessura para atualizar a espessura do botão em tempo real
        self.doubleSpinBoxEspessura.valueChanged.connect(self.update_button_thickness)

        # Conecta o pushButtonFechar para fechar o diálogo
        self.pushButtonFechar.clicked.connect(self.close_dialog)

        # Conecta o lineEditNome para validar o texto
        self.lineEditNome.textChanged.connect(self.validate_poligono_edit)

        # Conecta o pushButtonProjecao para abrir o diálogo de escolha de CRS
        self.pushButtonProjecao.clicked.connect(self.choose_projection)

        # Conecta o comboBoxRotulagem para atualizar o estado do botão pushButtonCorRotulo
        self.comboBoxRotulagem.currentIndexChanged.connect(self.update_pushButtonCorRotulo_state)

        # Conecta a mudança de seleção no comboBoxCamada para atualizar os botões de conversão e projeção
        self.comboBoxCamada.currentIndexChanged.connect(self.update_pushButtonConverter_state)
        self.comboBoxCamada.currentIndexChanged.connect(self.update_pushButtonProjecao_state)

        # Conecta o sinal de mudança de seleção das feições da camada atual
        self.update_layer_connections()

       # Conecta a mudança de seleção no comboBoxCamada para atualizar o checkBoxSeleciona
        self.comboBoxCamada.currentIndexChanged.connect(self.update_checkBoxSeleciona)

    def closeEvent(self, event):
        """Desconecta os sinais antes de fechar o diálogo."""
        project = QgsProject.instance()

        for signal in (project.layersAdded, project.layersRemoved, project.layerWillBeRemoved):
            try:
                signal.disconnect(self.populate_combo_box)
            except (TypeError, RuntimeError):
                pass  # nosec B110

        connected_layer = getattr(self, "_connected_layer", None)
        if connected_layer is not None:
            try:
                connected_layer.selectionChanged.disconnect(self.update_checkBoxSeleciona)
            except (TypeError, RuntimeError):
                pass  # nosec B110

        self._connected_layer = None

        for layer in project.mapLayers().values():
            try:
                layer.nameChanged.disconnect(self.update_combo_box_item)
            except (TypeError, RuntimeError):
                pass  # nosec B110

        parent = self.parent()
        if parent is not None:
            parent.poligono_linha_dlg = None

        super().closeEvent(event)

    def showEvent(self, event):
        """
        Sobrescreve o método showEvent para realizar ações personalizadas quando o diálogo é exibido.

        Parâmetros:
        event : QShowEvent
            Evento que contém informações sobre a ação de exibir o diálogo.

        A função realiza as seguintes ações:
        - Chama o método 'showEvent' da classe base para garantir o comportamento padrão de exibição.
        - Reseta os componentes da interface ao exibir o diálogo.
        - Atualiza o comboBoxCamada com as camadas disponíveis.
        - Atualiza o nome do polígono no campo de edição.
        - Atualiza o estado do checkBoxSeleciona com base nas feições selecionadas.
        - Conecta os sinais da camada atual.
        - Atualiza o comboBoxRotulagem com os campos disponíveis.
        - Verifica o estado do comboBoxCamada e atualiza os botões relevantes.
        """
        super(PoligonoManager, self).showEvent(event)  # Chama o método showEvent da classe base para garantir o comportamento padrão

        # Chama a função para resetar os componentes da interface
        self.resetar_componentes()

        # Realiza outras ações que precisam ser feitas ao mostrar o diálogo
        self.populate_combo_box()  # Atualiza o comboBoxCamada com as camadas disponíveis
        self.update_poligono_edit_nome()  # Atualiza o campo de nome do polígono
        self.update_checkBoxSeleciona()  # Atualiza o estado do checkBoxSeleciona com base nas feições selecionadas
        self.update_layer_connections()  # Conecta os sinais da camada atual

        # Atualiza o comboBoxRotulagem com os campos disponíveis
        self.populate_comboBoxRotulagem()

        # Verifica o status do comboBoxCamada e atualiza os botões Converter e Projeção
        self.update_pushButtonConverter_state()  # Atualiza o estado do botão de conversão
        self.update_pushButtonProjecao_state()  # Atualiza o estado do botão de projeção

    def resetar_componentes(self):
        """
        Reseta os componentes do diálogo para seus estados iniciais, garantindo que a interface seja restaurada corretamente.

        Parâmetros:
        self : objeto
            Referência à instância atual da classe.

        A função realiza as seguintes ações:
        - Reseta a seleção do comboBoxCamada para o primeiro item.
        - Limpa o campo de texto do lineEditNome.
        - Desmarca os checkboxes relacionados aos campos ID, Comprimento, Adicionar, Deletar e Remover.
        - Esconde o botão de limpar texto associado ao campo de nome.
        - Reseta a variável que controla se o botão de cor foi acionado.
        - Define as cores padrão da borda e do preenchimento.
        - Restaura o estilo e o texto padrão dos botões de seleção de cor e cor do rótulo.
        - Limpa o campo de CRS (lineEditSRC) e define o estilo e texto padrão.
        - Reseta a variável do CRS selecionado.
        """
        self.comboBoxCamada.setCurrentIndex(0)  # Reseta a seleção do ComboBoxCamada para o primeiro item
        self.lineEditNome.clear()  # Limpa o campo de texto do lineEditNome

        self.findChild(QCheckBox, 'checkBoxID').setChecked(False)  # Desmarca o checkbox ID
        self.findChild(QCheckBox, 'checkBoxComprimento').setChecked(False)  # Desmarca o checkbox Comprimento

        self.findChild(QCheckBox, 'checkBoxAdicionar').setChecked(False)  # Desmarca o checkbox Adicionar
        self.findChild(QCheckBox, 'checkBoxDel').setChecked(False)
        self.findChild(QCheckBox, 'checkBoxRemover').setChecked(False)  # Desmarca o checkbox Remover

        self.clear_button.hide()  # Esconde o botão de limpar texto
        self.selected_color = None
        self.selected_label_color = None

        # Restaura o estilo e o texto padrão do botão de cor definido no Qt Designer
        self.pushButtonCor.setStyleSheet(self.pushButtonCor_default_style)
        self.pushButtonCor.setText(self.tr("Cor"))  # Substitua "Escolher Cor" pelo texto original definido no QtDesigner
        self.pushButtonCorRotulo.setStyleSheet(self.pushButtonCorRotulo_default_style) # Restaura o estilo do botão de cor do rótulo

        # Reseta o campo de CRS (lineEditSRC)
        self.lineEditSRC.clear()  # Limpa o texto do lineEditSRC
        self.lineEditSRC.setStyleSheet("color: black;")  # Define a cor do texto como preto
        self.lineEditSRC.setText(self.tr("Sem Projeção"))  # Define o texto padrão como "Sem Projeção"
        self.selected_crs = None  # Reseta a variável do CRS selecionado

    def populate_combo_box(self, *args):
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
        - Atualiza o estado dos botões pushButtonConverter e pushButtonProjecao.
        - Atualiza o campo de nome do polígono com base na nova seleção.
        - Preenche o comboBoxRotulagem com os campos da camada selecionada.
        - Ativa ou desativa o botão pushButtonConverter com base na presença de camadas no comboBoxCamada.
        """
        current_layer_id = self.comboBoxCamada.currentData()  # Salva a camada atualmente selecionada
        self.comboBoxCamada.blockSignals(True)  # Bloqueia os sinais para evitar chamadas desnecessárias a update_poligono_edit_nome
        self.comboBoxCamada.clear()  # Limpa o comboBox antes de preencher

        layer_list = QgsProject.instance().mapLayers().values()
        for layer in layer_list:
            if isinstance(layer, QgsVectorLayer) and QgsWkbTypes.geometryType(layer.wkbType()) == QgsWkbTypes.GeometryType.PolygonGeometry:
                self.comboBoxCamada.addItem(layer.name(), layer.id())
                try:
                    layer.nameChanged.disconnect(self.update_combo_box_item)
                except (TypeError, RuntimeError):
                    pass  # nosec B110

                layer.nameChanged.connect(self.update_combo_box_item)

        # Restaura a seleção anterior, se possível
        if current_layer_id:
            index = self.comboBoxCamada.findData(current_layer_id) # Tenta encontrar a camada selecionada anteriormente
            if index != -1:
                self.comboBoxCamada.setCurrentIndex(index) # Restaura a seleção anterior

        self.comboBoxCamada.blockSignals(False)  # Desbloqueia os sinais

        # Após preencher o comboBox, atualiza o estado dos botões pushButtonConverter e pushButtonProjecao
        self.update_pushButtonConverter_state()
        self.update_pushButtonProjecao_state()

        # Atualiza o lineEditNome após atualizar o comboBox
        self.update_poligono_edit_nome()

        # Atualiza o comboBoxRotulagem com base na nova camada selecionada
        self.populate_comboBoxRotulagem()

        # Ativa ou desativa o botão pushButtonConverter com base na presença de camadas no comboBoxCamada
        self.pushButtonConverter.setEnabled(self.comboBoxCamada.count() > 0) 

    def update_combo_box_item(self, *args):
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
            
        # Atualiza o lineEditNome após atualizar o comboBox
        self.update_poligono_edit_nome()

    def update_adicionar_checkbox(self):
        """
        Atualiza o estado do checkBoxAdicionar com base no estado dos outros checkboxes (ID e Comprimento).

        Parâmetros:
        self : objeto
            Referência à instância atual da classe.

        A função realiza as seguintes ações:
        - Verifica se algum dos checkboxes de atributos (ID ou Comprimento) está marcado.
        - Se algum checkbox estiver marcado, marca o checkBoxAdicionar.
        - Se nenhum checkbox estiver marcado, desmarca o checkBoxAdicionar.
        - Bloqueia os sinais do checkBoxAdicionar durante a atualização para evitar loops de sinal.
        """
        
        checkboxes = ['checkBoxID', 'checkBoxComprimento']  # Lista dos checkboxes de atributos
        any_checked = any(self.findChild(QCheckBox, name).isChecked() for name in checkboxes)  # Verifica se algum checkbox está marcado
        self.findChild(QCheckBox, 'checkBoxAdicionar').blockSignals(True)  # Bloqueia os sinais do checkBoxAdicionar
        self.findChild(QCheckBox, 'checkBoxAdicionar').setChecked(any_checked)  # Define o estado do checkBoxAdicionar com base nos checkboxes de atributos
        self.findChild(QCheckBox, 'checkBoxAdicionar').blockSignals(False)  # Desbloqueia os sinais do checkBoxAdicionar

    def validate_poligono_edit(self):
        """
        Valida o texto inserido no lineEditNome e ajusta a interface com base na validade do texto.

        Parâmetros:
        self : objeto
            Referência à instância atual da classe.

        A função realiza as seguintes ações:
        - Verifica se o texto inserido no lineEditNome contém caracteres inválidos.
        - Se houver caracteres inválidos, altera a cor do texto para vermelho e desabilita o botão pushButtonConverter.
        - Se o texto for válido, altera a cor do texto para azul e habilita o botão pushButtonConverter.
        - Mostra ou esconde o botão "X" de limpeza de texto com base na presença de texto no lineEditNome.
        """

        text = self.lineEditNome.text()  # Obtém o texto atual do lineEditNome
        if re.search(r'[\/:*?\'"|]', text):  # Verifica se o texto contém caracteres inválidos
            self.lineEditNome.setStyleSheet("color: red;")  # Altera a cor do texto para vermelho se houver caracteres inválidos
            self.pushButtonConverter.setEnabled(False)  # Desabilita o botão Converter se o texto for inválido
        else:
            self.lineEditNome.setStyleSheet("color: blue;")  # Altera a cor do texto para azul se o texto for válido
            self.pushButtonConverter.setEnabled(True)  # Habilita o botão Converter se o texto for válido

        # Mostrar ou esconder o botão "X" baseado na presença de texto no lineEditNome
        self.clear_button.setVisible(bool(text))  # Exibe o botão "X" se houver texto, ou esconde se estiver vazio

    def clear_poligono_edit(self):
        """
        Limpa o conteúdo do campo de texto lineEditNome.

        Parâmetros:
        self : objeto
            Referência à instância atual da classe.

        A função realiza as seguintes ações:
        - Remove todo o texto presente no lineEditNome.
        """
        self.lineEditNome.clear()  # Limpa o conteúdo do lineEditNome

    def mostrar_mensagem(self, texto, tipo, duracao=3):
        """
        Exibe uma mensagem na barra de mensagens da interface do QGIS com base no tipo e duração especificados.

        Parâmetros:
        self : objeto
            Referência à instância atual da classe.
        texto : str
            A mensagem de texto que será exibida.
        tipo : str
            O tipo da mensagem (pode ser "Erro" ou "Sucesso").
        duracao : int, opcional
            O tempo, em segundos, que a mensagem será exibida. O padrão é 3 segundos.

        A função realiza as seguintes ações:
        - Obtém a barra de mensagens da interface do QGIS.
        - Exibe uma mensagem de erro com um ícone crítico, se o tipo for "Erro".
        - Exibe uma mensagem de sucesso com um ícone informativo, se o tipo for "Sucesso".
        """
        # Obtém a barra de mensagens da interface do QGIS
        bar = self.iface.messageBar()  # Acessa a barra de mensagens da interface do QGIS

        # Exibe a mensagem com o nível apropriado baseado no tipo
        if tipo == "Erro":
            # Mostra uma mensagem de erro na barra de mensagens com um ícone crítico e a duração especificada
            bar.pushMessage(self.tr("Erro"), texto, level=Qgis.MessageLevel.Critical, duration=duracao)
        elif tipo == "Sucesso":
            # Mostra uma mensagem de sucesso na barra de mensagens com um ícone informativo e a duração especificada
            bar.pushMessage(self.tr("Sucesso"), texto, level=Qgis.MessageLevel.Info, duration=duracao)

    def iniciar_progress_bar(self, total_steps):
        """
        Inicializa e exibe uma barra de progresso para o processo de conversão de polígonos para linhas.

        Parâmetros:
        self : objeto
            Referência à instância atual da classe.
        total_steps : int
            O número total de etapas do processo, que define o valor máximo da barra de progresso.

        A função realiza as seguintes ações:
        - Cria uma mensagem informativa na barra de mensagens da interface QGIS.
        - Cria uma barra de progresso (QProgressBar) e define seu alinhamento e formato.
        - Estiliza a barra de progresso, definindo bordas, cores de fundo e de preenchimento.
        - Adiciona a barra de progresso à barra de mensagens e a exibe na interface.
        - Define o valor máximo da barra de progresso com base no número total de etapas do processo.
        - Retorna a barra de progresso e a barra de mensagens para controle posterior.
        """
        progressMessageBar = self.iface.messageBar().createMessage(self.tr("Convertendo a camada de Polígonos para uma Camada de Linhas"))
        progressBar = QProgressBar()  # Cria uma instância da QProgressBar
        progressBar.setAlignment(Qt.AlignmentFlag.AlignLeft | Qt.AlignmentFlag.AlignVCenter)  # Alinha a barra de progresso à esquerda e verticalmente ao centro
        progressBar.setFormat(self.tr("%p% - %v de %m etapas concluídas"))  # Define o formato da barra de progresso
        progressBar.setMinimumWidth(300)  # Define a largura mínima da barra de progresso

        # Estiliza a barra de progresso
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
                min-height: 5px;}""")

        # Adiciona a progressBar ao layout da progressMessageBar e exibe na interface
        progressMessageBar.layout().addWidget(progressBar)
        self.iface.messageBar().pushWidget(progressMessageBar, Qgis.MessageLevel.Info)

        # Define o valor máximo da barra de progresso com base no número total de etapas
        progressBar.setMaximum(total_steps)

        return progressBar, progressMessageBar

    def close_dialog(self):
        """Fecha o diálogo."""
        self.close()

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
        """Reconecta selectionChanged somente à camada atualmente selecionada."""
        old_layer = getattr(self, "_connected_layer", None)

        if old_layer is not None:
            try:
                old_layer.selectionChanged.disconnect(self.update_checkBoxSeleciona)
            except (TypeError, RuntimeError):
                pass  # nosec B110

        self._connected_layer = None

        layer_id = self.comboBoxCamada.currentData()
        layer = QgsProject.instance().mapLayer(layer_id) if layer_id else None

        if isinstance(layer, QgsVectorLayer):
            layer.selectionChanged.connect(self.update_checkBoxSeleciona)
            self._connected_layer = layer

        self.update_checkBoxSeleciona()

    def choose_projection(self):
        """
        Abre o diálogo de seleção de CRS (Sistema de Referência de Coordenadas) e atualiza a interface
        com a projeção escolhida pelo usuário.

        Parâmetros:
        self : objeto
            Referência à instância atual da classe.

        A função realiza as seguintes ações:
        - Verifica se há uma camada selecionada no comboBoxCamada.
        - Exibe uma mensagem de erro se nenhuma camada estiver selecionada.
        - Abre o diálogo de seleção de CRS.
        - Se um CRS válido for selecionado, compara-o com o CRS original da camada.
        - Atualiza o campo lineEditSRC com o nome da projeção e altera sua cor com base na mudança de CRS.
        - Armazena o CRS selecionado para uso posterior.
        - Se nenhum CRS válido for selecionado, exibe "Sem Projeção" no campo de CRS e reseta a cor para preto.
        """
        # Verifica se há uma camada selecionada no comboBoxCamada
        layer = QgsProject.instance().mapLayer(self.comboBoxCamada.currentData())
        if not layer:  # Verifica se a camada é válida
            self.mostrar_mensagem(self.tr("Nenhuma Camada Selecionada."), "Erro")  # Exibe a mensagem de erro
            return  # Sai da função, pois não há camada válida

        crs_dialog = QgsProjectionSelectionDialog()  # Abre o diálogo de seleção de projeção (CRS)
        if crs_dialog.exec():  # Se o usuário selecionar uma projeção e confirmar
            crs = crs_dialog.crs()  # Obtém o CRS selecionado
            if crs.isValid():  # Verifica se o CRS selecionado é válido
                # Compara o CRS selecionado com o CRS original da camada
                original_crs = layer.crs()  # Obtém o CRS da camada original
                if crs != original_crs:  # Se o CRS selecionado for diferente do original
                    self.lineEditSRC.setStyleSheet("color: magenta;")  # Altera a cor do campo CRS para magenta
                else:  # Se o CRS selecionado for o mesmo que o original
                    self.lineEditSRC.setStyleSheet("color: black;")  # Volta a cor do campo CRS para preto

                self.lineEditSRC.setText(crs.description())  # Exibe o nome completo da projeção selecionada
                self.selected_crs = crs  # Armazena o CRS selecionado para uso posterior
            else:  # Se o CRS selecionado não for válido
                self.lineEditSRC.setText(self.tr("Sem Projeção"))  # Exibe "Sem Projeção" no campo CRS
                self.lineEditSRC.setStyleSheet("color: black;")  # Reseta a cor do campo CRS para preto

    def choose_color(self):
        """
        Abre o diálogo de seleção de cores e aplica a cor escolhida ao botão de cor (pushButtonCor).

        Parâmetros:
        self : objeto
            Referência à instância atual da classe.

        A função realiza as seguintes ações:
        - Abre o diálogo de seleção de cores para o usuário escolher uma cor.
        - Verifica se a cor escolhida é válida.
        - Obtém o valor atual da espessura da linha do doubleSpinBoxEspessura.
        - Atualiza o estilo do botão pushButtonCor com a cor selecionada e a espessura da linha.
        - Remove o texto do botão para mostrar apenas a cor.
        - Armazena a cor selecionada para uso posterior.
        """
        color = QColorDialog.getColor(QColor(Qt.GlobalColor.black), self, self.tr("Selecione uma cor")) # Abre o diálogo de seleção de cores

        if color.isValid():  # Verifica se a cor selecionada é válida
            # Obtém o valor da espessura da linha do doubleSpinBoxEspessura
            line_thickness = self.doubleSpinBoxEspessura.value()

            # Atualiza o estilo do botão para mostrar uma linha fina com a cor selecionada
            self.pushButtonCor.setStyleSheet(f"""
                QPushButton {{
                    background-color: {color.name()};
                    border: none;
                    height: {line_thickness}px;
                    max-height: {line_thickness}px;
                    min-height: {line_thickness}px;
                    margin: 0;
                    padding: 0;
                }}
            """)
            self.pushButtonCor.setText("")  # Remove o texto do botão para exibir apenas a cor
            self.selected_color = color  # Armazena a cor selecionada para uso posterior

    def update_button_thickness(self):
        """
        Atualiza a espessura do botão pushButtonCor com base no valor atual do doubleSpinBoxEspessura.

        Parâmetros:
        self : objeto
            Referência à instância atual da classe.

        A função realiza as seguintes ações:
        - Verifica se a cor foi previamente selecionada (armazenada em self.selected_color).
        - Obtém o valor atual da espessura da linha do doubleSpinBoxEspessura.
        - Atualiza o estilo do botão pushButtonCor para refletir a nova espessura e a cor selecionada.
        - Remove o texto do botão para exibir apenas a cor e o novo estilo.
        """
        
        if hasattr(self, 'selected_color') and self.selected_color:  # Verifica se a cor foi selecionada
            # Obtém a espessura da linha do doubleSpinBoxEspessura
            line_thickness = self.doubleSpinBoxEspessura.value()

            # Atualiza o estilo do botão para refletir a nova espessura e a cor selecionada
            self.pushButtonCor.setStyleSheet(f"""
                QPushButton {{
                    background-color: {self.selected_color.name()};
                    border: none;
                    height: {line_thickness}px;
                    max-height: {line_thickness}px;
                    min-height: {line_thickness}px;
                    margin: 0;
                    padding: 0;
                }}
            """)
            self.pushButtonCor.setText("")  # Remove o texto do botão para exibir apenas a cor e o novo estilo

    def apply_color_to_layer(self, layer):
        """
        Aplica a cor selecionada e a espessura da linha à camada fornecida.

        Parâmetros:
        self : objeto
            Referência à instância atual da classe.
        layer : QgsVectorLayer
            A camada de linhas à qual serão aplicadas a cor e a espessura selecionadas.

        A função realiza as seguintes ações:
        - Verifica se uma cor foi selecionada.
        - Obtém a espessura da linha a partir do valor atual do doubleSpinBoxEspessura.
        - Configura o estilo da camada para utilizar a cor e a espessura da linha selecionadas.
        - Aplica as alterações à camada e força seu redesenho.
        """

        if hasattr(self, 'selected_color') and self.selected_color:  # Verifica se uma cor foi selecionada
            # Obtém a espessura da linha do doubleSpinBoxEspessura
            line_thickness = self.doubleSpinBoxEspessura.value()

            # Configura o estilo da camada para usar a cor e espessura selecionadas
            symbol = QgsLineSymbol.createSimple({
                'color': self.selected_color.name(),  # Define a cor selecionada
                'width': str(line_thickness)  # Define a espessura da linha
            })
            layer.renderer().setSymbol(symbol)  # Aplica o símbolo com a nova cor e espessura à camada
            layer.triggerRepaint()  # Força o redesenho da camada para refletir as alterações

    def add_attributes(self, feature, line_geometry, crs):
        """
        Adiciona atributos de ID e Comprimento a uma feição, dependendo das opções selecionadas.

        Parâmetros:
        self : objeto
            Referência à instância atual da classe.
        feature : QgsFeature
            A feição para a qual os atributos serão adicionados.
        line_geometry : QgsGeometry
            A geometria da linha que será utilizada para calcular o comprimento.
        crs : QgsCoordinateReferenceSystem
            O sistema de referência de coordenadas da camada.

        A função realiza as seguintes ações:
        - Adiciona o ID da feição aos atributos se o checkbox correspondente estiver marcado.
        - Calcula o comprimento da linha e adiciona aos atributos, ajustando para coordenadas geográficas se necessário.
        - Retorna a lista de atributos com ID e Comprimento (se aplicável).
        """
        attrs = []  # Lista para armazenar os atributos

        # Adiciona o ID da feição, se o checkbox de ID estiver marcado
        if self.findChild(QCheckBox, 'checkBoxID').isChecked():
            attrs.append(feature.id())  # Adiciona o ID da feição

        # Calcula e adiciona o comprimento da feição, se o checkbox de Comprimento estiver marcado
        if self.findChild(QCheckBox, 'checkBoxComprimento').isChecked():
            d = QgsDistanceArea()  # Instancia o objeto para calcular distâncias e áreas
            if crs.isGeographic():  # Verifica se o CRS é geográfico
                d.setSourceCrs(crs, QgsProject.instance().transformContext())  # Define o CRS de origem
                d.setEllipsoid(QgsProject.instance().ellipsoid())  # Define o elipsóide para cálculos geográficos
                length = round(d.measureLength(line_geometry), 3)  # Calcula o comprimento da linha no sistema geográfico
            else:
                length = round(line_geometry.length(), 3)  # Calcula o comprimento da linha no sistema projetado
            attrs.append(length)  # Adiciona o comprimento aos atributos

        return attrs  # Retorna a lista de atributos

    def convert_features_to_lines(self, layer, output_name):
        """
        Converte feições de uma camada de polígonos para uma nova camada de linhas, adicionando atributos conforme necessário.

        Parâmetros:
        self : objeto
            Referência à instância atual da classe.
        layer : QgsVectorLayer
            A camada de polígonos que será convertida para linhas.
        output_name : str
            O nome da nova camada de linhas.

        A função realiza as seguintes ações:
        - Cria uma nova camada de linhas com o CRS da camada original.
        - Adiciona campos da camada original ou apenas os campos de ID e Comprimento, dependendo das opções selecionadas.
        - Verifica se deve converter todas as feições ou apenas as selecionadas.
        - Itera sobre as feições da camada original, convertendo a geometria de polígonos para linhas.
        - Adiciona atributos (ID e Comprimento) às feições convertidas, conforme as opções selecionadas.
        - Retorna a nova camada de linhas.
        """

        # Cria uma nova camada de linhas com o nome definido
        new_layer = QgsVectorLayer(f"LineString?crs={layer.crs().authid()}", output_name, "memory")
        
        # Verifica se deve remover os atributos existentes
        if not self.findChild(QCheckBox, 'checkBoxRemover').isChecked():
            # Adiciona os campos da camada original, se o checkBoxRemover não estiver marcado
            new_layer_data = new_layer.dataProvider()
            fields = layer.fields()

             # Adiciona o campo de ID se o checkbox correspondente estiver marcado
            if self.findChild(QCheckBox, 'checkBoxID').isChecked():
                fields.append(QgsField("ID", QMetaType.Type.Int))

            # Adiciona o campo de Comprimento se o checkbox correspondente estiver marcado
            if self.findChild(QCheckBox, 'checkBoxComprimento').isChecked():
                fields.append(QgsField("Comprimento", QMetaType.Type.Double))

            new_layer_data.addAttributes(fields)  # Adiciona os campos à nova camada
            new_layer.updateFields()  # Atualiza os campos na nova camada
        else:
            # Apenas adiciona os campos para ID e Comprimento se o checkBoxRemover estiver marcado
            new_layer_data = new_layer.dataProvider()
            fields = QgsFields()

            if self.findChild(QCheckBox, 'checkBoxID').isChecked():
                fields.append(QgsField("ID", QMetaType.Type.Int))

            if self.findChild(QCheckBox, 'checkBoxComprimento').isChecked():
                fields.append(QgsField("Comprimento", QMetaType.Type.Double))

            new_layer_data.addAttributes(fields)
            new_layer.updateFields()

        # Verifica se deve converter apenas as feições selecionadas
        if self.findChild(QCheckBox, 'checkBoxSeleciona').isChecked() and layer.selectedFeatureCount() > 0:
            features = layer.selectedFeatures()
        else:
            features = layer.getFeatures()

        crs = layer.crs()

        # Itere sobre as feições da camada de polígonos e converta para linhas
        for feature in features:
            geom = feature.geometry()
            if geom.isMultipart():
                polygons = geom.asMultiPolygon() # Se a feição for multipart, obtém as partes
            else:
                polygons = [geom.asPolygon()] # Caso contrário, trata como uma única parte

            for polygon in polygons:
                for ring in polygon:
                    if len(ring) < 2:
                        continue

                    line_feature = QgsFeature(new_layer.fields())
                    line_geometry = QgsGeometry.fromPolyline(
                        [QgsPoint(point.x(), point.y()) for point in ring])

                    if self.findChild(QCheckBox, "checkBoxRemover").isChecked():
                        attributes = self.add_attributes(feature, line_geometry, crs)
                    else:
                        attributes = feature.attributes() + self.add_attributes(
                            feature, line_geometry, crs)

                    line_feature.setAttributes(attributes)
                    line_feature.setGeometry(line_geometry)
                    new_layer_data.addFeature(line_feature)

        return new_layer  # Retorna a nova camada de linhas

    def toggle_attribute_checkboxes(self, state):
        """
        Ativa ou desativa todos os checkboxes de atributos com base no estado do checkBoxAdicionar e atualiza o comboBoxRotulagem.

        Parâmetros:
        self : objeto
            Referência à instância atual da classe.
        state : Qt.State
            O estado do checkBoxAdicionar (Qt.Checked ou Qt.Unchecked).

        A função realiza as seguintes ações:
        - Define uma lista de checkboxes de atributos (como checkBoxID e checkBoxComprimento).
        - Itera sobre cada checkbox, bloqueando temporariamente os sinais para evitar loops de sinal.
        - Define o estado de cada checkbox com base no estado do checkBoxAdicionar (marcado ou desmarcado).
        - Desbloqueia os sinais após modificar o estado dos checkboxes.
        - Atualiza o comboBoxRotulagem após alterar o estado dos checkboxes.
        """
        checkboxes = ['checkBoxID', 'checkBoxComprimento']  # Lista de nomes dos checkboxes de atributos
        for name in checkboxes:  # Itera sobre cada checkbox
            checkbox = self.findChild(QCheckBox, name)  # Obtém o checkbox com base no nome
            checkbox.blockSignals(True)  # Bloqueia temporariamente os sinais para evitar loops de sinal
            checkbox.setChecked(state == Qt.CheckState.Checked)  # Define o estado do checkbox com base no estado do checkBoxAdicionar
            checkbox.blockSignals(False)  # Desbloqueia os sinais após a modificação

        self.populate_comboBoxRotulagem()  # Atualiza o comboBoxRotulagem após alterar os checkboxes

    def update_pushButtonCorRotulo_state(self):
        """
        Atualiza o estado do botão pushButtonCorRotulo com base na seleção atual do comboBoxRotulagem.

        Parâmetros:
        self : objeto
            Referência à instância atual da classe.

        A função realiza as seguintes ações:
        - Verifica se o comboBoxRotulagem está configurado para "Rótulos: Opcional" ou está desabilitado.
        - Se estiver configurado como "Rótulos: Opcional" ou desabilitado, desativa o botão pushButtonCorRotulo.
        - Caso contrário, ativa o botão pushButtonCorRotulo.
        """
        
        # Verifica se o comboBoxRotulagem está configurado como "Rótulos: Opcional" ou se está desabilitado
        if self.comboBoxRotulagem.currentIndex() == 0 or not self.comboBoxRotulagem.isEnabled():
            self.pushButtonCorRotulo.setEnabled(False)  # Desativa o botão pushButtonCorRotulo
        else:
            self.pushButtonCorRotulo.setEnabled(True)  # Ativa o botão pushButtonCorRotulo

    def choose_label_color(self):
        """
        Abre o diálogo de seleção de cores e aplica a cor escolhida ao botão pushButtonCorRotulo.

        Parâmetros:
        self : objeto
            Referência à instância atual da classe.

        A função realiza as seguintes ações:
        - Abre o diálogo de seleção de cores para o usuário escolher uma cor.
        - Se uma cor válida for selecionada, armazena a cor e atualiza o estilo do botão pushButtonCorRotulo com a cor escolhida.
        - Se nenhuma cor válida for selecionada, reseta a cor selecionada e volta ao estilo padrão do botão.
        """
        color = QColorDialog.getColor(QColor(Qt.GlobalColor.black), self, self.tr("Selecione a cor do rótulo"))  # Abre o diálogo de seleção de cores

        if color.isValid():  # Verifica se a cor selecionada é válida
            # Armazena a cor selecionada
            self.selected_label_color = color
            # Atualiza o estilo do botão para indicar a cor selecionada
            self.pushButtonCorRotulo.setStyleSheet(f"background-color: {color.name()};")
        else:
            # Reseta a cor se nenhuma cor válida for selecionada
            self.selected_label_color = None
            self.pushButtonCorRotulo.setStyleSheet("")  # Volta ao estilo padrão do botão

    def apply_labeling_to_layer(self, layer):
        """
        Aplica a rotulagem à camada de linha baseada no campo selecionado no comboBoxRotulagem.

        Parâmetros:
        self : objeto
            Referência à instância atual da classe.
        layer : QgsVectorLayer
            A camada de linhas à qual será aplicada a rotulagem.

        A função realiza as seguintes ações:
        - Verifica se o campo selecionado no comboBoxRotulagem é válido para rotulagem.
        - Configura as definições de rotulagem (campo, posição e estado).
        - Se uma cor de rótulo foi selecionada, configura a cor do texto do rótulo.
        - Aplica a rotulagem configurada à camada de linhas e habilita os rótulos.
        - Força o redesenho da camada para refletir a rotulagem.
        """
        selected_field = self.comboBoxRotulagem.currentText()  # Obtém o campo selecionado no comboBoxRotulagem

        if self.comboBoxRotulagem.currentIndex() != 0 and selected_field != "":  # Verifica se o campo selecionado é válido
            settings = QgsPalLayerSettings()  # Instancia as configurações de rotulagem
            settings.fieldName = selected_field  # Define o campo para rotulagem
            settings.placement = Qgis.LabelPlacement.Line  # Ajusta a posição da rotulagem para linhas
            settings.enabled = True  # Habilita a rotulagem

            # Configura a cor do texto se uma cor tiver sido selecionada
            if self.selected_label_color:
                text_format = QgsTextFormat()  # Instancia o formato do texto
                text_format.setColor(QColor(self.selected_label_color))  # Define a cor do texto
                settings.setFormat(text_format)  # Aplica o formato de texto às configurações de rotulagem

            labeling = QgsVectorLayerSimpleLabeling(settings)  # Cria a rotulagem simples baseada nas configurações
            layer.setLabeling(labeling)  # Aplica a rotulagem à camada
            layer.setLabelsEnabled(True)  # Habilita os rótulos na camada
            layer.triggerRepaint()  # Força o redesenho da camada para refletir as alterações

    def populate_comboBoxRotulagem(self):
        """
        Preenche o comboBoxRotulagem com os campos da camada selecionada e adiciona campos extras como ID e Comprimento se necessário.

        Parâmetros:
        self : objeto
            Referência à instância atual da classe.

        A função realiza as seguintes ações:
        - Limpa o comboBoxRotulagem e adiciona a opção inicial "Rótulos: Opcional".
        - Obtém a camada selecionada no comboBoxCamada.
        - Adiciona os campos originais da camada ao comboBoxRotulagem, se o checkBoxRemover não estiver marcado.
        - Adiciona campos extras como ID e Comprimento, se o checkBoxAdicionar estiver marcado.
        - Habilita ou desabilita o comboBoxRotulagem com base nos campos disponíveis.
        - Tenta restaurar a seleção anterior do comboBoxRotulagem, se possível.
        """
        current_label = self.comboBoxRotulagem.currentText()  # Armazena o campo de rótulo atualmente selecionado

        self.comboBoxRotulagem.clear()  # Limpa o comboBoxRotulagem
        self.comboBoxRotulagem.addItem(self.tr("Rótulos: Opcional"))  # Adiciona o item inicial
        self.comboBoxRotulagem.setToolTip(self.tr("Escolha um rótulo (Opcional)"))  # Define o tooltip

        # Obtém a camada selecionada no comboBoxCamada
        index = self.comboBoxCamada.currentIndex()
        if index >= 0:
            layer_id = self.comboBoxCamada.itemData(index)
            layer = QgsProject.instance().mapLayer(layer_id)

            if layer:
                # Lista para armazenar os nomes de campo já adicionados, evitando duplicados
                added_fields = set()

                # Verifica se checkBoxRemover está selecionado
                if not self.findChild(QCheckBox, 'checkBoxRemover').isChecked():
                    # Adiciona os campos originais da camada ao comboBoxRotulagem
                    for field in layer.fields():
                        field_name = field.name()
                        if field_name not in added_fields:
                            self.comboBoxRotulagem.addItem(field_name)
                            added_fields.add(field_name)

                # Verifica se checkBoxAdicionar está selecionado e adiciona campos extras
                if self.findChild(QCheckBox, 'checkBoxAdicionar').isChecked():
                    if self.findChild(QCheckBox, 'checkBoxID').isChecked() and "ID" not in added_fields:
                        self.comboBoxRotulagem.addItem("ID")
                        added_fields.add("ID")
                    if self.findChild(QCheckBox, 'checkBoxComprimento').isChecked() and "Comprimento" not in added_fields:
                        self.comboBoxRotulagem.addItem("Comprimento")
                        added_fields.add("Comprimento")

        # Verifica se o comboBoxRotulagem está vazio além da opção inicial
        if self.comboBoxRotulagem.count() == 1:
            self.comboBoxRotulagem.setEnabled(False)  # Desativa se não houver outros campos
        else:
            self.comboBoxRotulagem.setEnabled(True)  # Ativa se houver campos para selecionar

        # Tenta restaurar a seleção do campo de rótulo anteriormente escolhido
        index = self.comboBoxRotulagem.findText(current_label)
        if index != -1:
            self.comboBoxRotulagem.setCurrentIndex(index) # Restaura a seleção anterior

    def convert_and_process_layer(self):
        """
        Converte uma camada de polígonos para uma nova camada de linhas, processa as feições e aplica as configurações de cor e rotulagem.

        Parâmetros:
        self : objeto
            Referência à instância atual da classe.

        A função realiza as seguintes ações:
        - Obtém a camada de polígonos selecionada no comboBoxCamada.
        - Verifica se a camada selecionada é válida e contém polígonos.
        - Define o nome da nova camada de linhas, adicionando um sufixo se o nome já existir.
        - Inicia uma barra de progresso com base no número total de feições da camada.
        - Converte as feições de polígonos para linhas e reprojeta a camada se necessário.
        - Processa cada feição da camada de origem e atualiza a barra de progresso.
        - Adiciona a nova camada de linhas ao projeto.
        - Aplica a cor e a rotulagem selecionadas à nova camada.
        - Fecha a barra de progresso e exibe uma mensagem de sucesso.
        - Se o checkBoxDel estiver marcado, remove a camada de polígonos original do projeto.
        """
        start_time = time.time()  # Inicia a contagem do tempo de execução

        # Obtenha a camada de polígonos selecionada
        layer_id = self.comboBoxCamada.currentData()
        layer = QgsProject.instance().mapLayer(layer_id)
        
        if not layer or layer.geometryType() != QgsWkbTypes.GeometryType.PolygonGeometry:
            self.mostrar_mensagem(self.tr("Nenhuma camada de polígonos válida selecionada."), "Erro")
            return
        
        # Definir o nome da nova camada de linha
        output_name = self.lineEditNome.text().strip()
        if not output_name:
            output_name = layer.name()  # Usa o nome da camada original se lineEditNome estiver vazio
        
        # Verifica se o nome já existe e adiciona sufixo se necessário
        existing_layer_names = [lyr.name() for lyr in QgsProject.instance().mapLayers().values()]
        if output_name in existing_layer_names:
            base_name = output_name
            counter = 1
            while output_name in existing_layer_names:
                output_name = f"{base_name}_{counter}"
                counter += 1
        
        # Inicia a barra de progresso
        total_features = layer.featureCount()
        progressBar, progressMessageBar = self.iniciar_progress_bar(total_features)
        
        # Converte as feições para linhas
        new_layer = self.convert_features_to_lines(layer, output_name)
        
        # Reprojeta a camada se necessário
        final_layer = self.reproject_layer_if_needed(new_layer, layer, output_name)

        # Atualiza a barra de progresso conforme as feições são processadas
        progressBar.setValue(total_features)

        # Adicione a nova camada de linhas ao projeto
        QgsProject.instance().addMapLayer(final_layer)

        # Aplica a cor selecionada à camada final
        self.apply_color_to_layer(final_layer)

        # Aplica a rotulagem à camada final
        self.apply_labeling_to_layer(final_layer)

        # Fecha a barra de progresso
        self.iface.messageBar().clearWidgets()

        # Calcula o tempo total de execução
        end_time = time.time()
        elapsed_time = end_time - start_time

        # Mostra a mensagem de conclusão com o tempo de execução
        self.mostrar_mensagem(self.tr("Conversão concluída com sucesso em {elapsed_time:.2f} segundos!").format(elapsed_time=elapsed_time), "Sucesso")

        # Verifique se o checkBoxDel está marcado
        if self.findChild(QCheckBox, 'checkBoxDel').isChecked():
            # Remove a camada de polígonos do projeto
            QgsProject.instance().removeMapLayer(layer_id)
            self.mostrar_mensagem(self.tr("A camada de polígonos foi deletada do projeto."), "Sucesso")

    def update_pushButtonConverter_state(self):
        """
        Atualiza o estado do botão pushButtonConverter com base na seleção atual do comboBoxCamada.

        Parâmetros:
        self : objeto
            Referência à instância atual da classe.

        A função realiza as seguintes ações:
        - Verifica se há uma camada selecionada no comboBoxCamada.
        - Se não houver nenhuma camada selecionada, desativa o botão pushButtonConverter.
        - Se houver uma camada selecionada, ativa o botão pushButtonConverter.
        """
        if self.comboBoxCamada.currentIndex() == -1:  # Se não houver camada selecionada
            self.pushButtonConverter.setEnabled(False)  # Desativa o botão pushButtonConverter
        else:
            self.pushButtonConverter.setEnabled(True)  # Ativa o botão pushButtonConverter

    def update_pushButtonProjecao_state(self):
        """
        Atualiza o estado do botão pushButtonProjecao com base na seleção atual do comboBoxCamada.

        Parâmetros:
        self : objeto
            Referência à instância atual da classe.

        A função realiza as seguintes ações:
        - Verifica se há uma camada selecionada no comboBoxCamada.
        - Se não houver nenhuma camada selecionada, desativa o botão pushButtonProjecao.
        - Se houver uma camada selecionada, ativa o botão pushButtonProjecao.
        """
        if self.comboBoxCamada.currentIndex() == -1:  # Se não houver camada selecionada
            self.pushButtonProjecao.setEnabled(False)  # Desativa o botão pushButtonProjecao
        else:
            self.pushButtonProjecao.setEnabled(True)  # Ativa o botão pushButtonProjecao

    def update_poligono_edit_nome(self):
        """
        Atualiza os campos lineEditNome e lineEditSRC com base na camada selecionada no comboBoxCamada.

        Parâmetros:
        self : objeto
            Referência à instância atual da classe.

        A função realiza as seguintes ações:
        - Obtém a camada selecionada no comboBoxCamada e atualiza o campo lineEditNome com o nome da camada.
        - Se um CRS foi previamente selecionado (selected_crs), compara-o com o CRS da camada.
        - Se o CRS selecionado for diferente do CRS original, altera a cor do lineEditSRC para magenta.
        - Se o CRS for o mesmo que o original ou não tiver sido selecionado, mantém ou reseta a cor para preto.
        - Atualiza o campo lineEditSRC com a descrição do CRS da camada ou exibe "Sem Projeção" se não for válido.
        - Se não houver camada selecionada, limpa o campo lineEditNome e atualiza o lineEditSRC com a mensagem apropriada.
        - Valida o texto do lineEditNome após a atualização.
        """
        index = self.comboBoxCamada.currentIndex()  # Obtém o índice da camada selecionada
        if index >= 0:  # Verifica se há uma camada selecionada
            layer_id = self.comboBoxCamada.itemData(index)  # Obtém o ID da camada selecionada
            layer = QgsProject.instance().mapLayer(layer_id)  # Obtém a camada correspondente ao ID
            if layer:
                self.lineEditNome.setText(layer.name())  # Atualiza o lineEditNome com o nome da camada

                # Não altere o lineEditSRC se um CRS foi selecionado anteriormente
                if self.selected_crs:
                    # Compara o CRS selecionado com o CRS original
                    original_crs = layer.crs()
                    if self.selected_crs != original_crs:  # Se o CRS selecionado for diferente do original
                        self.lineEditSRC.setStyleSheet("color: magenta;")  # Altera a cor para magenta
                    else:
                        self.lineEditSRC.setStyleSheet("color: black;")  # Reseta a cor para preto se for o CRS original

                    self.lineEditSRC.setText(self.selected_crs.description())  # Atualiza o lineEditSRC com a descrição do CRS selecionado
                else:
                    # Obtém a projeção da camada e atualiza o lineEditSRC
                    crs = layer.crs()
                    if crs.isValid():
                        self.lineEditSRC.setText(crs.description())  # Exibe o nome completo da projeção
                        self.lineEditSRC.setStyleSheet("color: black;")  # Define a cor do texto como preto
                    else:
                        self.lineEditSRC.setText(self.tr("Sem Projeção"))  # Exibe "Sem Projeção" se o CRS não for válido
                        self.lineEditSRC.setStyleSheet("color: black;")  # Define a cor do texto como preto
        else:
            self.lineEditNome.clear()  # Limpa o campo lineEditNome se não houver camada selecionada
            self.lineEditSRC.setText(self.tr("Nenhuma camada selecionada")) # Exibe "Nenhuma camada selecionada"
            self.lineEditSRC.setStyleSheet("color: red;")  # Define a cor do texto para vermelho

        # Valida o texto do lineEditNome após atualizar
        self.validate_poligono_edit()

    def reproject_layer_if_needed(self, new_layer, original_layer, output_name):
        """
        Reprojeta a camada para o CRS escolhido, se necessário, e retorna a camada reprojetada.

        Parâmetros:
        self : objeto
            Referência à instância atual da classe.
        new_layer : QgsVectorLayer
            A nova camada de linhas que foi criada.
        original_layer : QgsVectorLayer
            A camada original de polígonos da qual a nova camada foi criada.
        output_name : str
            O nome da nova camada de linhas.

        A função realiza as seguintes ações:
        - Verifica se um CRS foi selecionado, se ele é válido e se é diferente do CRS da camada original.
        - Se for necessário reprojetar, utiliza o algoritmo `qgis:reprojectlayer` para reprojetar a nova camada.
        - Define o nome da camada reprojetada e remove a camada original.
        - Se o CRS não precisar ser alterado, retorna a nova camada sem reprojetar.
        """
        
        # Verifica se o CRS foi selecionado, é válido e diferente do CRS original
        if self.selected_crs and self.selected_crs.isValid() and self.selected_crs != original_layer.crs():
            # Reprojetar a camada convertida para o CRS escolhido
            params = {
                'INPUT': new_layer,  # A nova camada a ser reprojetada
                'TARGET_CRS': self.selected_crs,  # O CRS selecionado
                'OUTPUT': 'memory:'  # Salva o resultado na memória
            }
            resultado = processing.run('qgis:reprojectlayer', params)  # Executa o algoritmo de reprojeção
            reprojetada_layer = resultado['OUTPUT']  # Obtém a camada reprojetada
            
            # Define o nome da camada reprojetada
            reprojetada_layer.setName(output_name)
            
            # Remove a camada original e retorna a camada reprojetada
            QgsProject.instance().removeMapLayer(new_layer.id())
            return reprojetada_layer
        
        # Retorna a nova camada sem reprojetar se o CRS não foi alterado ou não foi selecionado
        return new_layer