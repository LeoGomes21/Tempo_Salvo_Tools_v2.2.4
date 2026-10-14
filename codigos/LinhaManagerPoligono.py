from qgis.core import QgsProject, QgsVectorLayer, QgsWkbTypes, QgsField, QgsFeature, QgsGeometry, Qgis, QgsDefaultValue, QgsFillSymbol, QgsCoordinateTransform, QgsCoordinateReferenceSystem, QgsPalLayerSettings, QgsTextFormat, QgsVectorLayerSimpleLabeling
from qgis.PyQt.QtWidgets import QDialog, QCheckBox, QPushButton, QColorDialog, QToolTip, QHBoxLayout, QProgressBar
from qgis.gui import QgsProjectionSelectionDialog
from qgis.PyQt.QtGui import QColor, QCursor
from qgis.PyQt.QtCore import Qt, QMetaType, QCoreApplication
from qgis.PyQt import uic
import processing
import time
import os
import re

FORM_CLASS, _ = uic.loadUiType(os.path.join(
    os.path.dirname(__file__), 'LinhaPoligono.ui'))
"""
Carrega a interface do usuário a partir de um arquivo .ui gerado pelo Qt Designer.

Parâmetros:
- Nenhum parâmetro explícito é passado diretamente para essa linha, mas a função uic.loadUiType é chamada com o caminho para o arquivo .ui.

A linha realiza as seguintes ações:
- Usa a função uic.loadUiType para carregar a definição da interface do usuário a partir de um arquivo .ui.
- O caminho para o arquivo .ui é construído usando os.path.join e os.path.dirname para garantir que o caminho seja relativo ao diretório atual do arquivo de código.
- A função uic.loadUiType retorna uma tupla contendo a classe do formulário (FORM_CLASS) e um objeto de base (ignorado com _).
"""

class LinhaManager(QDialog, FORM_CLASS):
    """
    Classe responsável por gerenciar o diálogo de conversão de linhas em polígonos.

    Herda:
    - QDialog: classe base para janelas de diálogo no PyQt.
    - FORM_CLASS: classe gerada automaticamente a partir do arquivo .ui do Qt Designer.

    A classe realiza as seguintes ações:
    - Configura e gerencia a interface gráfica para a conversão de camadas de linha para polígonos.
    - Implementa a lógica de interação entre os elementos da interface e a manipulação de dados geoespaciais no QGIS.
    """
    def __init__(self, iface, parent=None):
        """
        Construtor da classe LinhaManager.

        A função realiza as seguintes ações:
        - Inicializa a classe base QDialog e o layout da interface do usuário definido no arquivo 'LinhaPoligono.ui'.
        - Armazena a referência da interface QGIS.
        - Configura a interface do usuário a partir do Designer.
        - Altera o título da janela.
        - Inicializa os widgets do diálogo.
        - Adiciona o botão de deletar texto ao lineEditNome com estilo e funcionalidade.
        - Configura as variáveis de instância para armazenar as cores da borda e preenchimento.
        - Desativa inicialmente o QScrollBar.
        - Conecta os sinais aos slots.
        - Preenche o comboBox com camadas de linha.
        - Atualiza o lineEditNome com a camada selecionada inicialmente.
        - Conecta sinais do projeto para atualizar comboBox quando camadas forem adicionadas, removidas ou renomeadas.
        """
        super(LinhaManager, self).__init__(parent)  # Inicializa a classe base QDialog
        
        self.iface = iface  # Armazena a referência da interface QGIS
        
        # Configura a interface do usuário a partir do Designer.
        self.setupUi(self)
        
        # Altera o título da janela
        self.setWindowTitle(self.tr("Converte Linhas para Polígonos"))

        # Inicializa o self.current_layer como None
        self.current_layer = None  # Variável para armazenar a camada atual
        self.selection_changed_connection = None  # Conexão para o sinal selectionChanged

        # Armazena o estilo padrão do botão de cor
        self.pushButtonCor_default_style = self.pushButtonCor.styleSheet()
        self.pushButtonCorRotulo_default_style = self.pushButtonCorRotulo.styleSheet()

        # Adiciona o botão de deletar texto ao lineEditNome
        self.clear_button = QPushButton("✖", self.lineEditNome)  # Botão de deletar texto
        self.clear_button.setCursor(Qt.CursorShape.ArrowCursor)  # Define o cursor do botão
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
        """)  # Define o estilo do botão
        self.clear_button.setFixedSize(15, 15)  # Define o tamanho fixo do botão
        self.clear_button.hide()  # Esconde o botão inicialmente
        self.clear_button.clicked.connect(self.clear_line_edit)  # Conecta o clique do botão à função clear_line_edit

        layout = QHBoxLayout(self.lineEditNome)  # Cria um layout horizontal para o lineEditNome
        layout.addStretch()  # Adiciona um espaçamento elástico
        layout.addWidget(self.clear_button)  # Adiciona o botão clear_button ao layout
        layout.setContentsMargins(0, 0, 0, 0)  # Define as margens do layout
        self.lineEditNome.setLayout(layout)  # Define o layout do lineEditNome

        # Variáveis de instância para armazenar as cores da borda e preenchimento
        self.borda_cor = None  # Cor da borda inicializada como None
        self.preenchimento_cor = None  # Cor de preenchimento inicializada como None
        self.acao_pushButtonCor = False  # Variável para armazenar se o botão foi acionado
        self.borda_espessura = 0.26  # Espessura inicial da borda

        # Desativa o QScrollBar inicialmente
        self.horizontalScrollBarTransparency.setEnabled(False)  # Desativa a barra de rolagem horizontal

        self.comboBoxRotulagem.addItem(self.tr("Rótulos: Opcional"))  # Texto inicial do comboBox
        self.comboBoxRotulagem.setToolTip(self.tr("Escolha um rótulo (Opcional)"))  # Dica de ferramenta para o comboBox

        self.pushButtonCorRotulo.clicked.connect(self.choose_label_color)  # Conecta o clique do botão à função de escolha de cor

        # Variável para armazenar a cor do rótulo
        self.label_color = QColor(Qt.GlobalColor.black)  # Cor padrão do rótulo

        # Conecta os sinais aos slots
        self.connect_signals()  # Conecta os sinais aos slots

        # Preenche o comboBox com camadas de linha
        self.populate_combo_box()  # Preenche o comboBoxCamada com camadas de linha

        # Atualiza o lineEditNome com a camada selecionada inicialmente
        self.update_line_edit_nome()  # Atualiza o lineEditNome com a camada selecionada

        # Conecta sinais do projeto para atualizar comboBox quando camadas forem adicionadas, removidas ou renomeadas
        QgsProject.instance().layersAdded.connect(self.populate_combo_box)  # Conecta o sinal layersAdded à função populate_combo_box
        QgsProject.instance().layersRemoved.connect(self.populate_combo_box)  # Conecta o sinal layersRemoved à função populate_combo_box
        QgsProject.instance().layerWillBeRemoved.connect(self.populate_combo_box)  # Conecta o sinal layerWillBeRemoved à função populate_combo_box

        # Configura o lineEditSRC para ser não editável, mas selecionável
        self.lineEditSRC.setReadOnly(True)
        self.lineEditSRC.setToolTip(self.tr("Projeção da camada Convertida"))

    def tr(self, message):
        return QCoreApplication.translate("LinhaManager", message)

    def closeEvent(self, event):
        """Desconecta sinais antes de destruir o diálogo."""
        project = QgsProject.instance()

        if self.current_layer and self.selection_changed_connection:
            try:
                self.current_layer.selectionChanged.disconnect(self.on_layer_selection_changed)
            except (TypeError, RuntimeError):
                pass  # nosec B110

        self.current_layer = None
        self.selection_changed_connection = False

        for signal in (project.layersAdded, project.layersRemoved, project.layerWillBeRemoved):
            try:
                signal.disconnect(self.populate_combo_box)
            except (TypeError, RuntimeError):
                pass  # nosec B110

        for layer in project.mapLayers().values():
            try:
                layer.nameChanged.disconnect(self.update_combo_box_item)
            except (TypeError, RuntimeError):
                pass  # nosec B110

        parent = self.parent()
        if parent is not None:
            parent.linha_poligono_dlg = None

        super().closeEvent(event)

    def connect_signals(self):
        """
        Conecta os sinais dos widgets aos seus respectivos slots para manipulação de eventos.

        Parâmetros:
        self : objeto
            Referência à instância atual da classe.

        A função realiza as seguintes conexões:
        - Conecta a mudança de seleção no comboBoxCamada para atualizar o lineEditNome.
        - Conecta o clique do botão de conversão à função de conversão.
        - Conecta o checkBoxAdicionar para selecionar ou desmarcar os outros checkboxes.
        - Conecta os outros checkboxes para atualizar o estado do checkBoxAdicionar.
        - Conecta o pushButtonCor para definir as cores da camada de polígono.
        - Conecta a scrollbar de transparência para atualizar a transparência do preenchimento.
        - Conecta o doubleSpinBoxBorda para atualizar a espessura da borda.
        - Conecta o pushButtonFechar para fechar o diálogo.
        - Conecta o lineEditNome para validar o texto.
        """
        # Conecta a mudança de seleção no comboBoxCamada para atualizar o lineEditNome
        self.comboBoxCamada.currentIndexChanged.connect(self.update_line_edit_nome)
        # Conecta o clique do botão de conversão à função de conversão
        self.pushButtonConverter.clicked.connect(self.convert_lines_to_polygons)
        # Conecta o checkBoxAdicionar para selecionar ou desmarcar os outros checkboxes
        self.findChild(QCheckBox, 'checkBoxAdicionar').toggled.connect(self.toggle_attribute_checkboxes)
        # Conecta os outros checkboxes para atualizar o checkBoxAdicionar
        self.findChild(QCheckBox, 'checkBoxID').stateChanged.connect(self.update_adicionar_checkbox)
        self.findChild(QCheckBox, 'checkBoxArea').stateChanged.connect(self.update_adicionar_checkbox)
        self.findChild(QCheckBox, 'checkBoxPerim').stateChanged.connect(self.update_adicionar_checkbox)

        # Conecta o pushButtonCor para definir as cores da camada de polígono
        self.findChild(QPushButton, 'pushButtonCor').clicked.connect(self.aplicar_cores)

        # Conecta a scrollbar de transparência para atualizar a transparência do preenchimento
        self.horizontalScrollBarTransparency.valueChanged.connect(self.update_transparency)

        # Conecta o doubleSpinBoxBorda para atualizar a espessura da borda
        self.doubleSpinBoxBorda.valueChanged.connect(self.update_borda_espessura)

        # Conecta o pushButtonFechar para fechar o diálogo
        self.pushButtonFechar.clicked.connect(self.close_dialog)

        # Conecta o lineEditNome para validar o texto
        self.lineEditNome.textChanged.connect(self.validate_line_edit)

        # Conecta a mudança de seleção no comboBoxCamada para atualizar o lineEditNome e as conexões de sinal
        self.comboBoxCamada.currentIndexChanged.connect(self.on_combobox_layer_changed)

        # Conectar o botão de projeção ao método de escolha de CRS
        self.pushButtonProjecao.clicked.connect(self.choose_projection)

        # Conecta a mudança de checkboxes para atualizar o comboBoxRotulagem em tempo real
        self.findChild(QCheckBox, 'checkBoxRemover').stateChanged.connect(self.update_combo_box_rotulagem)
        self.findChild(QCheckBox, 'checkBoxID').stateChanged.connect(self.update_combo_box_rotulagem)
        self.findChild(QCheckBox, 'checkBoxArea').stateChanged.connect(self.update_combo_box_rotulagem)
        self.findChild(QCheckBox, 'checkBoxPerim').stateChanged.connect(self.update_combo_box_rotulagem)
        self.findChild(QCheckBox, 'checkBoxAdicionar').stateChanged.connect(self.update_combo_box_rotulagem)

    def populate_combo_box(self, *args):
        """
        Preenche o comboBoxCamada com camadas de linha do QGIS e restaura a seleção anterior, se possível.

        Parâmetros:
        self : objeto
            Referência à instância atual da classe.

        A função realiza as seguintes ações:
        - Salva a camada atualmente selecionada no comboBoxCamada.
        - Bloqueia os sinais do comboBox para evitar chamadas desnecessárias à função update_line_edit_nome.
        - Limpa o comboBox antes de preenchê-lo.
        - Obtém a lista de camadas do projeto e adiciona ao comboBox apenas as camadas de vetor do tipo linha.
        - Conecta o sinal nameChanged de cada camada de linha à função update_combo_box_item.
        - Restaura a seleção anterior no comboBox, se possível.
        - Desbloqueia os sinais do comboBox.
        - Atualiza o lineEditNome após atualizar o comboBox.
        - Ativa ou desativa o botão pushButtonConverter com base na presença de camadas no comboBoxCamada.
        """
        current_layer_id = self.comboBoxCamada.currentData()  # Salva a camada atualmente selecionada
        self.comboBoxCamada.blockSignals(True)  # Bloqueia os sinais para evitar chamadas desnecessárias a update_line_edit_nome
        self.comboBoxCamada.clear()  # Limpa o comboBox antes de preenchê-lo

        layer_list = QgsProject.instance().mapLayers().values()  # Obtém a lista de todas as camadas no projeto
        for layer in layer_list:
            if isinstance(layer, QgsVectorLayer) and layer.geometryType() == Qgis.GeometryType.Line:
                self.comboBoxCamada.addItem(layer.name(), layer.id())  # Adiciona camadas de vetor do tipo linha ao comboBox
                try:
                    layer.nameChanged.disconnect(self.update_combo_box_item)
                except (TypeError, RuntimeError):
                    pass  # nosec B110

                layer.nameChanged.connect(self.update_combo_box_item)

        # Restaura a seleção anterior, se possível
        if current_layer_id:
            index = self.comboBoxCamada.findData(current_layer_id)  # Encontra o índice da camada anteriormente selecionada
            if index != -1:
                self.comboBoxCamada.setCurrentIndex(index)  # Restaura a seleção no comboBox

        self.comboBoxCamada.blockSignals(False)  # Desbloqueia os sinais

        # Chama on_combobox_layer_changed para atualizar lineEditNome e lineEditSRC
        self.on_combobox_layer_changed()

        # Atualiza o lineEditNome após atualizar o comboBox
        self.update_line_edit_nome()

        # Atualiza o comboBoxRotulagem com base na nova camada selecionada
        self.update_combo_box_rotulagem()

        # Ativa ou desativa o botão pushButtonConverter com base na presença de camadas no comboBoxCamada
        self.pushButtonConverter.setEnabled(self.comboBoxCamada.count() > 0) 

    def update_combo_box_item(self, *args):
        """
        Atualiza os itens do comboBoxCamada com os nomes das camadas do projeto.

        Parâmetros:
        self : objeto
            Referência à instância atual da classe.

        A função realiza as seguintes ações:
        - Itera sobre todos os itens no comboBoxCamada.
        - Obtém a ID da camada associada a cada item no comboBox.
        - Obtém a camada correspondente à ID no projeto.
        - Atualiza o texto do item no comboBox com o nome atual da camada.
        - Atualiza o lineEditNome após atualizar o comboBox.
        """
        for i in range(self.comboBoxCamada.count()):
            layer_id = self.comboBoxCamada.itemData(i)  # Obtém a ID da camada associada ao item no comboBox
            layer = QgsProject.instance().mapLayer(layer_id)  # Obtém a camada correspondente à ID no projeto
            if layer:
                self.comboBoxCamada.setItemText(i, layer.name())  # Atualiza o texto do item no comboBox com o nome atual da camada
        
        # Atualiza o lineEditNome após atualizar o comboBox
        self.update_line_edit_nome()

    def toggle_attribute_checkboxes(self, checked):
        checkboxes = ['checkBoxID', 'checkBoxArea', 'checkBoxPerim']

        for name in checkboxes:
            checkbox = self.findChild(QCheckBox, name)
            checkbox.blockSignals(True)
            checkbox.setChecked(checked)
            checkbox.blockSignals(False)

    def update_adicionar_checkbox(self):
        """
        Atualiza o estado do checkBoxAdicionar com base no estado dos outros checkboxes de atributos.

        Parâmetros:
        self : objeto
            Referência à instância atual da classe.

        A função realiza as seguintes ações:
        - Define uma lista de nomes de checkboxes de atributos.
        - Verifica se algum dos checkboxes de atributos está selecionado.
        - Bloqueia os sinais do checkBoxAdicionar para evitar chamadas desnecessárias.
        - Define o estado do checkBoxAdicionar como selecionado se qualquer checkbox de atributos estiver selecionado.
        - Desbloqueia os sinais do checkBoxAdicionar.
        """
        checkboxes = ['checkBoxID', 'checkBoxArea', 'checkBoxPerim']  # Lista de nomes de checkboxes de atributos
        # Verifica se algum dos checkboxes de atributos está selecionado
        any_checked = any(self.findChild(QCheckBox, name).isChecked() for name in checkboxes)
        checkBoxAdicionar = self.findChild(QCheckBox, 'checkBoxAdicionar')  # Encontra o checkBoxAdicionar
        checkBoxAdicionar.blockSignals(True)  # Bloqueia os sinais do checkBoxAdicionar para evitar chamadas desnecessárias
        checkBoxAdicionar.setChecked(any_checked)  # Define o estado do checkBoxAdicionar com base no estado dos outros checkboxes
        checkBoxAdicionar.blockSignals(False)  # Desbloqueia os sinais do checkBoxAdicionar

    def validate_line_edit(self):
        """
        Valida o texto inserido no lineEditNome e atualiza o estilo e estado dos botões.

        Parâmetros:
        self : objeto
            Referência à instância atual da classe.

        A função realiza as seguintes ações:
        - Obtém o texto atual do lineEditNome.
        - Verifica se o texto contém caracteres inválidos usando uma expressão regular.
        - Atualiza a cor do texto no lineEditNome para vermelho se houver caracteres inválidos e desativa o botão pushButtonConverter.
        - Caso contrário, atualiza a cor do texto no lineEditNome para azul e ativa o botão pushButtonConverter.
        - Mostra ou esconde o botão "X" (clear_button) com base na presença de texto no lineEditNome.
        """
        text = self.lineEditNome.text()  # Obtém o texto atual do lineEditNome
        if re.search(r'[\/:*?\'"|]', text):  # Verifica se o texto contém caracteres inválidos
            self.lineEditNome.setStyleSheet("color: red;")  # Atualiza a cor do texto para vermelho
            self.pushButtonConverter.setEnabled(False)  # Desativa o botão pushButtonConverter
        else:
            self.lineEditNome.setStyleSheet("color: blue;")  # Atualiza a cor do texto para azul
            self.pushButtonConverter.setEnabled(True)  # Ativa o botão pushButtonConverter

        # Mostrar ou esconder o botão "X" baseado se há texto no lineEditNome
        self.clear_button.setVisible(bool(text))  # Mostra o botão clear_button se houver texto, caso contrário esconde

    def clear_line_edit(self):
        """
        Limpa o texto inserido no lineEditNome.

        Parâmetros:
        self : objeto
            Referência à instância atual da classe.

        A função realiza as seguintes ações:
        - Limpa o texto atualmente inserido no lineEditNome.
        """
        self.lineEditNome.clear()  # Limpa o texto do lineEditNome

    def update_line_edit_nome(self):
        """
        Atualiza o texto do lineEditNome com o nome da camada selecionada no comboBoxCamada.

        Parâmetros:
        self : objeto
            Referência à instância atual da classe.

        A função realiza as seguintes ações:
        - Obtém o índice da camada atualmente selecionada no comboBoxCamada.
        - Se o índice é válido (>= 0), obtém a ID da camada associada ao índice.
        - Obtém a camada correspondente à ID no projeto.
        - Se a camada existe, define o texto do lineEditNome com o nome da camada.
        - Se o índice não é válido, limpa o texto do lineEditNome.
        - Valida o texto do lineEditNome após a atualização.
        """
        index = self.comboBoxCamada.currentIndex()  # Obtém o índice da camada atualmente selecionada no comboBoxCamada
        if index >= 0:  # Verifica se o índice é válido
            layer_id = self.comboBoxCamada.itemData(index)  # Obtém a ID da camada associada ao índice
            layer = QgsProject.instance().mapLayer(layer_id)  # Obtém a camada correspondente à ID no projeto
            if layer:  # Verifica se a camada existe
                self.lineEditNome.setText(layer.name())  # Define o texto do lineEditNome com o nome da camada
        else:
            self.lineEditNome.clear()  # Limpa o texto do lineEditNome se o índice não for válido

        # Valida o texto do lineEditNome após atualizar
        self.validate_line_edit()  # Chama a função validate_line_edit para validar o texto do lineEditNome

    def mostrar_mensagem(self, texto, tipo, duracao=3):
        """
        Exibe uma mensagem na barra de mensagens do QGIS com o nível apropriado baseado no tipo.

        Parâmetros:
        self : objeto
            Referência à instância atual da classe.
        texto : str
            A mensagem a ser exibida.
        tipo : str
            O tipo de mensagem ("Erro" ou "Sucesso").
        duracao : int, opcional
            A duração da mensagem em segundos (padrão é 3 segundos).

        A função realiza as seguintes ações:
        - Obtém a barra de mensagens da interface do QGIS.
        - Exibe uma mensagem com o nível apropriado baseado no tipo ("Erro" ou "Sucesso").
        """
        # Obtém a barra de mensagens da interface do QGIS
        bar = self.iface.messageBar()  # Acessa a barra de mensagens da interface do QGIS

        # Exibe a mensagem com o nível apropriado baseado no tipo
        if tipo == "Erro":
            # Mostra uma mensagem de erro na barra de mensagens com um ícone crítico e a duração especificada
            bar.pushMessage(self.tr("Erro"), texto, level=Qgis.MessageLevel.Critical, duration=duracao)

        elif tipo == "Aviso":
            bar.pushMessage(self.tr("Aviso"), texto, level=Qgis.MessageLevel.Warning, duration=duracao)

        elif tipo == "Sucesso":
            # Mostra uma mensagem de sucesso na barra de mensagens com um ícone informativo e a duração especificada
            bar.pushMessage(self.tr("Sucesso"), texto, level=Qgis.MessageLevel.Info, duration=duracao)

    def get_utm_crs(self, geometry):
        """
        Retorna o CRS UTM correspondente à posição da geometria.
        """
        if geometry is None or geometry.isNull() or geometry.isEmpty():
            return None

        centroid_geom = geometry.centroid()

        if centroid_geom.isNull() or centroid_geom.isEmpty():
            return None

        centroid = centroid_geom.asPoint()

        zone = max(1, min(60, int((centroid.x() + 180) / 6) + 1))

        if centroid.y() >= 0:
            epsg_code = 32600 + zone
        else:
            epsg_code = 32700 + zone

        return QgsCoordinateReferenceSystem(f'EPSG:{epsg_code}')

    def add_attributes(self, feature, polygon, is_geographic, source_crs):
        """
        Adiciona atributos de ID, Área e Perímetro a uma feição com base nos checkboxes selecionados.

        Parâmetros:
        self : objeto
            Referência à instância atual da classe.
        feature : QgsFeature
            A feição original da camada de linhas.
        polygon : QgsGeometry
            A geometria do polígono para calcular área e perímetro.
        is_geographic : bool
            Indica se o CRS da camada é geográfico.
        source_crs : QgsCoordinateReferenceSystem
            O sistema de referência de coordenadas (CRS) da camada de origem.

        Retorna:
        list
            Uma lista de atributos a serem adicionados à nova feição.

        A função realiza as seguintes ações:
        - Inicializa uma lista para armazenar os atributos.
        - Adiciona o ID da feição original se o checkbox correspondente estiver selecionado.
        - Calcula a área e o perímetro da geometria do polígono, transformando para CRS UTM se necessário.
        - Adiciona a área e o perímetro à lista de atributos se os checkboxes correspondentes estiverem selecionados.
        - Retorna a lista de atributos.
        """
        attrs = []  # Inicializa uma lista para armazenar os atributos

        # Adiciona o ID da feição original se o checkbox correspondente estiver selecionado
        if self.findChild(QCheckBox, 'checkBoxID').isChecked():
            attrs.append(feature.id())

        # Calcula a área e o perímetro da geometria do polígono, transformando para CRS UTM se necessário
        if self.findChild(QCheckBox, 'checkBoxArea').isChecked() or self.findChild(QCheckBox, 'checkBoxPerim').isChecked():
            if is_geographic:
                utm_crs = self.get_utm_crs(polygon)

                if utm_crs is None:
                    area = 0.0
                    perimeter = 0.0
                else:
                    transformed_geom = QgsGeometry(polygon)
                    transformed_geom.transform(QgsCoordinateTransform(source_crs, utm_crs, QgsProject.instance().transformContext()))
                    area = transformed_geom.area()
                    perimeter = transformed_geom.length()
            else:
                area = polygon.area()  # Calcula a área da geometria do polígono
                perimeter = polygon.length()  # Calcula o perímetro da geometria do polígono

            # Adiciona a área à lista de atributos se o checkbox correspondente estiver selecionado
            if self.findChild(QCheckBox, 'checkBoxArea').isChecked():
                attrs.append(round(area, 3))

            # Adiciona o perímetro à lista de atributos se o checkbox correspondente estiver selecionado
            if self.findChild(QCheckBox, 'checkBoxPerim').isChecked():
                attrs.append(round(perimeter, 3))

        return attrs  # Retorna a lista de atributos

    def get_unique_layer_name(self, base_name):
        """
        Gera um nome de camada único, adicionando um sufixo numérico se o nome base já existir no projeto.

        Parâmetros:
        self : objeto
            Referência à instância atual da classe.
        base_name : str
            O nome base para a nova camada.

        Retorno:
        unique_name : str
            O nome único gerado para a camada.

        A função realiza as seguintes ações:
        - Obtém uma lista de todos os nomes de camadas existentes no projeto atual.
        - Verifica se o nome base já existe.
        - Se o nome base já existir, adiciona um sufixo numérico ao nome até que um nome único seja encontrado.
        - Retorna o nome único gerado.
        """
        # Obtém todos os nomes de camadas existentes no projeto
        existing_names = [layer.name() for layer in QgsProject.instance().mapLayers().values()]  
        
        unique_name = base_name  # Inicializa o nome único com o nome base
        counter = 1  # Inicializa o contador para o sufixo numérico

        # Adiciona um sufixo numérico ao nome enquanto ele já existir entre as camadas
        while unique_name in existing_names:
            unique_name = f"{base_name}_{counter}"  # Gera um nome com o sufixo numérico
            counter += 1  # Incrementa o contador

        return unique_name  # Retorna o nome único gerado

    def choose_projection(self):
        """
        Abre o diálogo de escolha de CRS e atualiza o lineEditSRC com o CRS selecionado pelo usuário.

        Parâmetros:
        self : objeto
            Referência à instância atual da classe.

        A função realiza as seguintes ações:
        - Abre o diálogo de seleção de sistema de referência de coordenadas (CRS).
        - Verifica se o CRS selecionado é válido.
        - Obtém a camada selecionada no comboBoxCamada.
        - Compara o CRS selecionado com o CRS original da camada.
        - Se os CRS forem diferentes, altera a cor do lineEditSRC para magenta, caso contrário, reseta para preto.
        - Atualiza o lineEditSRC com a descrição do CRS selecionado.
        - Armazena o CRS selecionado para uso posterior.
        - Exibe mensagens de erro se nenhuma camada for selecionada ou se a camada não for encontrada no projeto.
        """
        crs_dialog = QgsProjectionSelectionDialog()
        if crs_dialog.exec():
            crs = crs_dialog.crs()
            if crs.isValid():
                # Obtém a camada selecionada no comboBoxCamada
                selected_layer_id = self.comboBoxCamada.currentData()
                if selected_layer_id:
                    original_layer = QgsProject.instance().mapLayer(selected_layer_id)
                    if original_layer:
                        original_crs = original_layer.crs()  # Obtém o CRS original da camada
                        # Compara o CRS selecionado com o CRS original
                        if crs != original_crs:
                            self.lineEditSRC.setStyleSheet("color: magenta;")  # Altera a cor para magenta
                        else:
                            self.lineEditSRC.setStyleSheet("color: black;")  # Volta para a cor padrão

                        self.lineEditSRC.setText(crs.description())  # Exibe o nome completo da projeção
                        self.selected_crs = crs  # Armazena o CRS escolhido para uso posterior
                    else:
                        self.mostrar_mensagem(self.tr("Camada selecionada não foi encontrada no projeto."), "Erro")
                else:
                    self.mostrar_mensagem(self.tr("Nenhuma camada selecionada."), "Erro")
            else:
                self.lineEditSRC.setText(self.tr("Sem Projeção")) # Exibe "Sem Projeção" se o CRS for inválido
                self.lineEditSRC.setStyleSheet("color: black;")  # Também reseta para preto

    def reproject_layer_if_needed(self, new_layer, original_layer, output_name):
        """
        Reprojeta a camada para o CRS escolhido, se necessário, e retorna a camada reprojetada.

        Parâmetros:
        self : objeto
            Referência à instância atual da classe.
        new_layer : QgsVectorLayer
            A nova camada de linhas ou polígonos que foi criada.
        original_layer : QgsVectorLayer
            A camada original da qual a nova camada foi criada.
        output_name : str
            O nome da nova camada reprojetada.

        Retorno:
        QgsVectorLayer
            A camada reprojetada ou a nova camada original, caso não seja necessária a reprojeção.

        A função realiza as seguintes ações:
        - Verifica se um CRS foi selecionado, se é válido e se é diferente do CRS da camada original.
        - Se for necessário reprojetar, utiliza o algoritmo `qgis:reprojectlayer` para reprojetar a nova camada.
        - Define o nome da camada reprojetada e remove a camada original.
        - Retorna a nova camada reprojetada ou a camada original sem alterações se não for necessário reprojetar.
        """
        # Verifica se o CRS foi selecionado, é válido e diferente do CRS original      
        if hasattr(self, 'selected_crs') and self.selected_crs is not None and self.selected_crs.isValid() and self.selected_crs != original_layer.crs():
            # Reprojetar a camada convertida para o CRS escolhido
            params = {
                'INPUT': new_layer,
                'TARGET_CRS': self.selected_crs,
                'OUTPUT': 'memory:'}  # Salva o resultado na memória

            resultado = processing.run("native:reprojectlayer", params)
            reprojetada_layer = resultado['OUTPUT']

            # Define o nome da camada reprojetada
            reprojetada_layer.setName(output_name)

            return reprojetada_layer

        # Retorna a nova camada sem reprojetar se o CRS não foi alterado ou não foi selecionado
        return new_layer

    def convert_lines_to_polygons(self):
        """
        Converte uma camada de linhas em uma nova camada de polígonos, aplicando atributos, cores, e projeção, se necessário.

        Parâmetros:
        self : objeto
            Referência à instância atual da classe.

        A função realiza as seguintes ações:
        - Obtém a camada de linha selecionada no comboBoxCamada.
        - Verifica se as linhas são fechadas para poderem ser convertidas em polígonos.
        - Cria uma nova camada de polígonos e adiciona os campos de atributos conforme as configurações do usuário.
        - Pré-processar cada feição para “fechar” a linha se ela estiver aberta
        - Converte cada linha fechada em um polígono.
        - Aplica atributos como área, perímetro, e ID se selecionado.
        - Adiciona a nova camada ao projeto e aplica cores e rótulos, se definidos.
        - Reprojeta a camada, se necessário, e apaga a camada original de linhas se o usuário optar por isso.
        """
        index = self.comboBoxCamada.currentIndex()  # Obtém o índice da camada selecionada no comboBoxCamada
        if index < 0:
            self.mostrar_mensagem(self.tr("Nenhuma camada selecionada."), "Erro")
            return

        layer_id = self.comboBoxCamada.itemData(index)  
        line_layer = QgsProject.instance().mapLayer(layer_id)
        if not line_layer:
            self.mostrar_mensagem(self.tr("Não foi possível encontrar a camada selecionada."), "Erro")
            return

        source_crs = line_layer.crs()  
        is_geographic = source_crs.isGeographic()

        # Se estiver marcado para converter somente feições selecionadas, mas não houver seleção
        if self.findChild(QCheckBox, 'checkBoxSeleciona').isChecked():
            features = line_layer.selectedFeatures()
            if not features:
                self.mostrar_mensagem(self.tr("Nenhuma feição selecionada. Convertendo todas as feições."), "Aviso")
                features = line_layer.getFeatures()
        else:
            features = line_layer.getFeatures()

        # reinicializamos pois o getFeatures() é um gerador
        features = list(features)  # convertemos para lista para iterar mais de uma vez
        for feature in features:
            geom = feature.geometry()

            if (geom is None
                or geom.isNull()
                or geom.isEmpty()):
                continue

            # Se for multipart
            if geom.isMultipart():
                multiline = geom.asMultiPolyline()
                nova_multiline = []

                for line in multiline:
                    if not line:
                        continue
                    # Verifica se o último vértice é igual ao primeiro
                    if line[-1] != line[0]:
                        # Calcula distância entre o primeiro e último ponto
                        dist = QgsGeometry.fromPointXY(line[0]).distance(QgsGeometry.fromPointXY(line[-1]))
                        # Se dist <= 0.1, força o último a ser igual ao primeiro
                        if dist <= 0.1:
                            line[-1] = line[0]
                        else:
                            # Se quiser apenas fechar, use:
                            line.append(line[0])
                            # Ou, se quiser lançar erro, pode ajustar conforme necessidade
                    nova_multiline.append(line)

                # Atualiza a geometria do feature
                geom = QgsGeometry.fromMultiPolylineXY(nova_multiline)
                feature.setGeometry(geom)

            # Se for singlepart
            else:
                singleline = geom.asPolyline()
                if not singleline:
                    continue

                if singleline[-1] != singleline[0]:
                    dist = QgsGeometry.fromPointXY(singleline[0]).distance(QgsGeometry.fromPointXY(singleline[-1]))
                    if dist <= 0.1:
                        singleline[-1] = singleline[0]
                    else:
                        # se quiser simplesmente fechar, use:
                        singleline.append(singleline[0])
                        # caso contrário, aqui poderia optar por lançar um erro

                geom = QgsGeometry.fromPolylineXY(singleline)
                feature.setGeometry(geom)

        layer_name = self.lineEditNome.text() if self.lineEditNome.text() else "Polígonos"
        layer_name = self.get_unique_layer_name(layer_name)  # Garante nome único

        polygon_layer = QgsVectorLayer('Polygon?crs=' + line_layer.crs().authid(), layer_name, 'memory')
        provider = polygon_layer.dataProvider()

        total_steps = len(features) + 2  # +2 etapas extras
        progressBar, progressMessageBar = self.iniciar_progress_bar(total_steps)

        # Adiciona campos
        fields = line_layer.fields()
        new_fields = []
        if self.findChild(QCheckBox, 'checkBoxID').isChecked():
            new_fields.append(QgsField("ID", QMetaType.Type.Int))
        if self.findChild(QCheckBox, 'checkBoxArea').isChecked():
            new_fields.append(QgsField("Área", QMetaType.Type.Double, len=10, prec=3))
        if self.findChild(QCheckBox, 'checkBoxPerim').isChecked():
            new_fields.append(QgsField("Perímetro", QMetaType.Type.Double, len=10, prec=3))

        if not self.findChild(QCheckBox, 'checkBoxRemover').isChecked():
            new_fields += fields.toList()

        start_time = time.time()
        provider.addAttributes(new_fields)
        polygon_layer.updateFields()
        progressBar.setValue(1)

        step = 1
        step_increment = 1 if total_steps <= 10000 else 100

        # Agora criamos os polígonos (agora todas as linhas devem estar fechadas)
        for feature in features:
            geom = feature.geometry()

            if (geom is None
                or geom.isNull()
                or geom.isEmpty()):
                continue

            if geom.isMultipart():
                multiline = geom.asMultiPolyline()
                for line in multiline:
                    if (not line
                        or len(line) < 4
                        or len({(p.x(), p.y()) for p in line[:-1]}) < 3):
                        continue

                    polygon = QgsGeometry.fromPolygonXY([line])

                    if polygon.isNull() or polygon.isEmpty():
                        continue

                    new_feature = QgsFeature()
                    new_feature.setGeometry(polygon)
                    attrs = self.add_attributes(feature, polygon, is_geographic, source_crs)
                    if not self.findChild(QCheckBox, 'checkBoxRemover').isChecked():
                        attrs += feature.attributes()
                    new_feature.setAttributes(attrs)
                    provider.addFeature(new_feature)
            else:
                line = geom.asPolyline()

                if (not line
                    or len(line) < 4
                    or len({(p.x(), p.y()) for p in line[:-1]}) < 3):
                    continue
                polygon = QgsGeometry.fromPolygonXY([line])

                if polygon.isNull() or polygon.isEmpty():
                    continue

                new_feature = QgsFeature()
                new_feature.setGeometry(polygon)
                attrs = self.add_attributes(feature, polygon, is_geographic, source_crs)
                if not self.findChild(QCheckBox, 'checkBoxRemover').isChecked():
                    attrs += feature.attributes()
                new_feature.setAttributes(attrs)
                provider.addFeature(new_feature)

            step += 1
            if step % step_increment == 0 or step == total_steps:
                progressBar.setValue(step)

        end_time = time.time()
        duration = end_time - start_time

        final_layer = self.reproject_layer_if_needed(polygon_layer, line_layer, layer_name)

        if (not isinstance(final_layer, QgsVectorLayer)
            or not final_layer.isValid()):

            self.iface.messageBar().popWidget(progressMessageBar)
            self.mostrar_mensagem(self.tr("Não foi possível criar a camada de polígonos."), "Erro")
            return

        if isinstance(final_layer, QgsVectorLayer):
            self.setup_field_calculations(final_layer)

            try:
                final_layer.geometryChanged.disconnect(self.on_geometry_changed)
            except (TypeError, RuntimeError):
                pass  # nosec B110

            final_layer.geometryChanged.connect(self.on_geometry_changed)

        # Aplica cores se usuário definiu
        if self.acao_pushButtonCor:
            simbolo = QgsFillSymbol.createSimple({
                'color': self.preenchimento_cor.name(QColor.NameFormat.HexArgb),
                'outline_color': self.borda_cor.name(QColor.NameFormat.HexArgb),
                'outline_width': str(self.borda_espessura)})
            final_layer.renderer().setSymbol(simbolo)
            final_layer.triggerRepaint()
            self.iface.layerTreeView().refreshLayerSymbology(final_layer.id())

        QgsProject.instance().addMapLayer(final_layer)

        if isinstance(final_layer, QgsVectorLayer):
            self.apply_labels_to_layer(final_layer)
        else:
            self.mostrar_mensagem(self.tr("Erro ao aplicar rótulos: Camada convertida inválida."), "Erro")

        self.mostrar_mensagem(self.tr("Linhas convertidas para polígonos e camada adicionada ao projeto em {duration:.2f} segundos.").format(duration=duration), "Sucesso")

        if self.findChild(QCheckBox, 'checkBoxDel').isChecked():
            QgsProject.instance().removeMapLayer(line_layer.id())
            self.mostrar_mensagem(self.tr("Camada de linha original deletada."), "Sucesso")

        self.iface.messageBar().popWidget(progressMessageBar)

    def update_layer_connections(self):
        """
        Atualiza as conexões da camada atual, desconectando os sinais da camada anterior e conectando a nova camada selecionada.

        Parâmetros:
        self : objeto
            Referência à instância atual da classe.

        A função realiza as seguintes ações:
        - Desconecta o sinal selectionChanged da camada anterior, se houver.
        - Obtém a nova camada selecionada no comboBoxCamada.
        - Conecta o sinal selectionChanged da nova camada para monitorar a seleção de feições.
        - Atualiza o estado do checkBoxSeleciona com base na camada atual.
        """
        # Desconecta o sinal da camada anterior, se houver
        try:
            if self.current_layer and self.selection_changed_connection:
                # Desconecta o sinal selectionChanged da camada anterior
                self.current_layer.selectionChanged.disconnect(self.on_layer_selection_changed)
                self.selection_changed_connection = False  # Reseta o sinal de conexão
        except (RuntimeError, AttributeError, TypeError):
            # O sinal já estava desconectado ou a camada foi deletada
            self.current_layer = None
            self.selection_changed_connection = False

        # Obtém a nova camada selecionada
        index = self.comboBoxCamada.currentIndex()  # Obtém o índice da camada selecionada no comboBoxCamada
        if index >= 0:  # Verifica se o índice é válido
            layer_id = self.comboBoxCamada.itemData(index)  # Obtém o ID da camada selecionada
            self.current_layer = QgsProject.instance().mapLayer(layer_id)  # Obtém a camada correspondente à ID
        else:
            self.current_layer = None  # Se não houver camada selecionada, reseta current_layer para None

        # Conecta ao sinal selectionChanged da nova camada, se válido
        if self.current_layer:  # Se houver uma nova camada selecionada
            try:
                # Conecta o sinal selectionChanged da nova camada
                self.current_layer.selectionChanged.connect(self.on_layer_selection_changed)
                self.selection_changed_connection = True  # Sinaliza que a conexão foi estabelecida
            except (RuntimeError, AttributeError, TypeError):
                self.selection_changed_connection = False  # Se houver um erro, reseta o sinal de conexão
        else:
            self.selection_changed_connection = False  # Se não houver camada, reseta o sinal de conexão

        # Atualiza o estado do checkBoxSeleciona com base na camada atual
        self.update_checkbox_seleciona_state()

    def on_layer_selection_changed(self, selected, deselected, clear_and_select):
        """
        Atualiza o estado do checkBoxSeleciona sempre que a seleção de feições na camada muda.

        Parâmetros:
        self : objeto
            Referência à instância atual da classe.
        selected : lista
            Lista de feições selecionadas.
        deselected : lista
            Lista de feições desmarcadas (deselecionadas).
        clear_and_select : bool
            Booleano que indica se a seleção foi limpa antes de selecionar novas feições.

        A função realiza as seguintes ações:
        - Atualiza o estado do checkBoxSeleciona com base na seleção de feições.
        """
        
        # Chamada sempre que a seleção na camada muda
        self.update_checkbox_seleciona_state()  # Atualiza o estado do checkBoxSeleciona

    def update_checkbox_seleciona_state(self):
        """
        Atualiza o estado do checkBoxSeleciona com base na seleção de feições da camada atual.

        Parâmetros:
        self : objeto
            Referência à instância atual da classe.

        A função realiza as seguintes ações:
        - Habilita o checkBoxSeleciona se a camada atual tiver feições selecionadas.
        - Desabilita e desmarca o checkBoxSeleciona se não houver feições selecionadas ou se não houver uma camada válida.
        """
        
        checkBoxSeleciona = self.findChild(QCheckBox, 'checkBoxSeleciona')  # Obtém a referência ao checkBoxSeleciona
        if self.current_layer and self.current_layer.selectedFeatureCount() > 0:  # Verifica se há uma camada válida e se há feições selecionadas
            checkBoxSeleciona.setEnabled(True)  # Habilita o checkBoxSeleciona se houver seleção de feições
        else:
            checkBoxSeleciona.setEnabled(False)  # Desabilita o checkBoxSeleciona se não houver seleção ou camada
            checkBoxSeleciona.setChecked(False)  # Desmarca o checkBoxSeleciona se ele estiver desabilitado

    def on_combobox_layer_changed(self):
        """
        Executa ações quando a seleção no comboBoxCamada é alterada.

        Parâmetros:
        self : objeto
            Referência à instância atual da classe.

        A função realiza as seguintes ações:
        - Atualiza o lineEditNome com o nome da camada selecionada.
        - Obtém a camada selecionada no comboBoxCamada e verifica se há um CRS já escolhido.
        - Se não houver CRS escolhido pelo usuário, atualiza o lineEditSRC com o CRS da camada.
        - Se não houver uma camada selecionada, exibe uma mensagem de "Nenhuma camada selecionada" no lineEditSRC.
        - Atualiza as conexões de sinais da nova camada selecionada.
        - Atualiza o comboBoxRotulagem com base na nova camada selecionada.
        """
        # Atualiza o lineEditNome com base na camada selecionada
        self.update_line_edit_nome()

        # Obtém a camada selecionada no comboBoxCamada
        selected_layer_id = self.comboBoxCamada.currentData()
        if selected_layer_id:
            selected_layer = QgsProject.instance().mapLayer(selected_layer_id)
            if selected_layer:
                original_crs = selected_layer.crs()  # Obtém o CRS original da camada
                if not hasattr(self, 'selected_crs') or self.selected_crs is None:
                    # Se o usuário não tiver escolhido um CRS, atualiza o lineEditSRC com o CRS da camada
                    self.lineEditSRC.setText(original_crs.description()) # Exibe a descrição do CRS original
                    self.lineEditSRC.setStyleSheet("color: black;") # Define a cor do texto para preto
                # Caso contrário, mantém o CRS que o usuário escolheu e apenas atualiza o estilo do SRC
            else:
                # Se a camada não for encontrada, atualiza o lineEditSRC para mostrar que nenhuma camada
                self.lineEditSRC.setText(self.tr("Nenhuma camada selecionada."))
                self.lineEditSRC.setStyleSheet("color: red;")
        else:
            # Se nenhum ID de camada for selecionado, exibe a mensagem de "Nenhuma camada selecionada"
            self.lineEditSRC.setText(self.tr("Nenhuma camada selecionada."))
            self.lineEditSRC.setStyleSheet("color: red;")

        # Atualiza as conexões de sinal para a nova camada
        self.update_layer_connections()

        # Atualiza o comboBoxRotulagem com base na nova camada selecionada
        self.update_combo_box_rotulagem()

    def setup_field_calculations(self, polygon_layer):
        """Configura valores padrão usando os índices reais dos campos."""
        if not isinstance(polygon_layer, QgsVectorLayer):
            return

        index_area = polygon_layer.fields().indexOf("Área")
        index_perimetro = polygon_layer.fields().indexOf("Perímetro")

        if not polygon_layer.crs().isGeographic():
            if index_area != -1:
                polygon_layer.setDefaultValueDefinition(
                    index_area,
                    QgsDefaultValue("$area"))

            if index_perimetro != -1:
                polygon_layer.setDefaultValueDefinition(
                    index_perimetro,
                    QgsDefaultValue("$perimeter"))

    def atualizar_valores_poligono(self, camada, fid, geom_override=None):
        """Atualiza Área e Perímetro após uma alteração de geometria."""
        if not isinstance(camada, QgsVectorLayer):
            return

        index_perimetro = camada.fields().indexOf("Perímetro")
        index_area = camada.fields().indexOf("Área")

        if index_perimetro == -1 and index_area == -1:
            return

        if geom_override is not None:
            geometry = QgsGeometry(geom_override)
        else:
            feature = camada.getFeature(fid)
            if not feature.isValid() or not feature.geometry() or feature.geometry().isEmpty():
                return
            geometry = QgsGeometry(feature.geometry())

        if geometry.isEmpty():
            return

        if camada.crs().isGeographic():
            utm_crs = self.get_utm_crs(geometry)

            if utm_crs is None:
                return

            transform = QgsCoordinateTransform(
                camada.crs(),
                utm_crs,
                QgsProject.instance().transformContext())

            geometry.transform(transform)

        area = round(geometry.area(), 3)
        perimetro = round(geometry.length(), 3)

        if index_area != -1:
            camada.changeAttributeValue(fid, index_area, area)

        if index_perimetro != -1:
            camada.changeAttributeValue(fid, index_perimetro, perimetro)

    def on_geometry_changed(self, fid, geometry):
        """Atualiza os atributos da camada que realmente emitiu o sinal."""
        layer = self.sender()

        if isinstance(layer, QgsVectorLayer):
            self.atualizar_valores_poligono(layer, fid, geom_override=geometry)

    def update_borda_espessura(self, value):
        """
        Atualiza a espessura da borda com base no valor fornecido pelo QDoubleSpinBox.

        Parâmetros:
        self : objeto
            Referência à instância atual da classe.
        value : float
            O valor da espessura da borda, obtido do QDoubleSpinBox.

        A função realiza as seguintes ações:
        - Atualiza o atributo `borda_espessura` com o valor fornecido pelo QDoubleSpinBox.
        """
        
        self.borda_espessura = value  # Define a espessura da borda com o valor fornecido

    def iniciar_progress_bar(self, total_steps):
        """
        Inicia e configura uma barra de progresso na interface do QGIS.

        Parâmetros:
        self : objeto
            Referência à instância atual da classe.
        total_steps : int
            Número total de etapas para a barra de progresso.

        Retorna:
        tuple
            Uma tupla contendo a barra de progresso (QProgressBar) e a barra de mensagens (QgsMessageBar).

        A função realiza as seguintes ações:
        - Cria uma mensagem na barra de mensagens da interface do QGIS.
        - Cria uma instância de QProgressBar.
        - Configura o alinhamento, formato e largura mínima da barra de progresso.
        - Aplica estilo à barra de progresso.
        - Adiciona a barra de progresso à barra de mensagens e exibe na interface.
        - Define o valor máximo da barra de progresso com base no número total de etapas.
        - Retorna a barra de progresso e a barra de mensagens.
        """
        progressMessageBar = self.iface.messageBar().createMessage(self.tr("Convertendo uma Camada de Linhas para uma Camada de Polígonos"))
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

    def aplicar_cores(self):
        """
        Abre diálogos de seleção de cores para definir as cores da borda e do preenchimento,
        e atualiza a interface para refletir as cores selecionadas.

        Parâmetros:
        self : objeto
            Referência à instância atual da classe.

        A função realiza as seguintes ações:
        - Marca que o botão de cores foi acionado.
        - Abre um diálogo de seleção de cores para a borda e define a cor da borda.
        - Abre um diálogo de seleção de cores para o preenchimento e define a cor do preenchimento.
        - Atualiza o valor do QScrollBar baseado na transparência selecionada.
        - Ativa o QScrollBar.
        - Atualiza o estilo do botão para refletir as cores selecionadas.
        """
        self.acao_pushButtonCor = True  # Marca que o botão foi acionado

        # Abre o diálogo de cores para escolher a cor da borda
        self.borda_cor = QColorDialog.getColor(QColor(Qt.GlobalColor.black), self, self.tr("Selecione a cor da borda"))
        if not self.borda_cor.isValid():
            self.borda_cor = QColor(255, 255, 255, 0)  # Define a borda como transparente se nenhuma cor for selecionada

        # Abre o diálogo de cores para escolher a cor do preenchimento
        self.preenchimento_cor = QColorDialog.getColor(QColor(Qt.GlobalColor.white), self, self.tr("Selecione a cor do preenchimento"))
        if not self.preenchimento_cor.isValid():
            self.preenchimento_cor = QColor(255, 255, 255, 0)  # Define o preenchimento como transparente se nenhuma cor for selecionada

        # Atualiza o valor do QScrollBar baseado na transparência selecionada
        self.horizontalScrollBarTransparency.setValue(100 - int(self.preenchimento_cor.alpha() / 255 * 100))
        self.horizontalScrollBarTransparency.setEnabled(True)  # Ativa o QScrollBar

        # Atualiza o estilo do botão para refletir as cores selecionadas
        self.update_button_style()

    def close_dialog(self):
        """Fecha o diálogo."""
        self.close()

    def update_button_style(self):
        """
        Atualiza o estilo do botão pushButtonCor para refletir as cores selecionadas e a transparência configurada.

        Parâmetros:
        self : objeto
            Referência à instância atual da classe.

        A função realiza as seguintes ações:
        - Obtém a referência ao botão pushButtonCor.
        - Atualiza a transparência da cor de preenchimento com base no valor do QScrollBar.
        - Constrói as strings de cores para o preenchimento e a borda, levando em consideração a transparência.
        - Atualiza o estilo do botão para refletir as cores e a transparência selecionadas.
        """
        button = self.findChild(QPushButton, 'pushButtonCor')  # Obtém a referência ao botão pushButtonCor
        preenchimento = self.preenchimento_cor  # Obtém a cor de preenchimento selecionada

        # Atualiza a transparência do preenchimento com base no valor do QScrollBar
        valor_transparencia = self.horizontalScrollBarTransparency.value()  # Obtém o valor do QScrollBar de transparência
        transparencia = 255 - int(valor_transparencia / 100 * 255)  # Calcula a transparência (0 a 255)
        preenchimento.setAlpha(transparencia)  # Define a transparência na cor de preenchimento

        # Constrói as strings de cores para o preenchimento e a borda
        preenchimento_str = preenchimento.name(QColor.NameFormat.HexArgb) if transparencia != 0 else 'transparent'
        borda = self.borda_cor.name() if self.borda_cor.alpha() != 0 else 'transparent'

        # Atualiza o estilo do botão para refletir as cores e a transparência selecionadas
        button.setStyleSheet(f"""
            background-color: {preenchimento_str};
            border: 2px solid {borda};
            font-weight: bold;
            font-style: italic;
        """)

    def update_transparency(self):
        """
        Atualiza a transparência da cor de preenchimento com base no valor do QScrollBar
        e atualiza o estilo do botão pushButtonCor em tempo real.

        Parâmetros:
        self : objeto
            Referência à instância atual da classe.

        A função realiza as seguintes ações:
        - Obtém o valor atual do QScrollBar de transparência.
        - Calcula a transparência correspondente (0 a 255).
        - Define a transparência na cor de preenchimento.
        - Atualiza a dica de ferramenta do QScrollBar para refletir a transparência atual.
        - Exibe uma dica de ferramenta temporária na posição do cursor com a transparência atual.
        - Chama a função update_button_style para atualizar o estilo do botão pushButtonCor em tempo real.
        """
        valor_transparencia = self.horizontalScrollBarTransparency.value()  # Obtém o valor atual do QScrollBar de transparência
        transparencia = 255 - int(valor_transparencia / 100 * 255)  # Calcula a transparência correspondente (0 a 255)
        self.preenchimento_cor.setAlpha(transparencia)  # Define a transparência na cor de preenchimento

        # Atualiza a dica de ferramenta do QScrollBar para refletir a transparência atual
        tooltip_text = self.tr("Transparência: {value}%").format(value=valor_transparencia)

        # Exibe uma dica de ferramenta temporária na posição do cursor com a transparência atual
        self.horizontalScrollBarTransparency.setToolTip(tooltip_text)
        QToolTip.showText(QCursor.pos(), tooltip_text, self.horizontalScrollBarTransparency)

        # Chama a função para atualizar o estilo do botão em tempo real
        self.update_button_style()

    def showEvent(self, event):
        """
        Executa ações necessárias ao exibir o diálogo.

        Parâmetros:
        self : objeto
            Referência à instância atual da classe.
        event : QShowEvent
            O evento de exibição da janela.

        A função realiza as seguintes ações:
        - Chama a função da classe base `showEvent` para garantir o comportamento padrão.
        - Reseta os componentes da interface para os valores iniciais.
        - Popula o comboBoxCamada com as camadas disponíveis no projeto.
        - Atualiza o lineEditNome com o nome da camada selecionada.
        - Atualiza as conexões de sinais da camada atual.
        - Chama o método `on_combobox_layer_changed` para realizar atualizações com base na camada selecionada.
        - Atualiza o comboBoxRotulagem com os campos da camada selecionada.
        - Atualiza o estado do botão Converter com base na camada selecionada.
        """
        super(LinhaManager, self).showEvent(event)  # Chama o método showEvent da classe base para garantir o comportamento padrão
        
        # Chama a função para resetar os componentes da interface
        self.resetar_componentes()

        # Realiza outras ações que precisam ser feitas ao mostrar o diálogo
        self.populate_combo_box()  # Popula o comboBoxCamada com as camadas disponíveis
        self.update_line_edit_nome()  # Atualiza o lineEditNome com a camada selecionada

        # Atualiza o estado do botão Converter com base na camada selecionada
        self.update_pushButtonConverter_state()

    def resetar_componentes(self):
        """
        Reseta os componentes do diálogo para seus estados iniciais.

        Parâmetros:
        self : objeto
            Referência à instância atual da classe.

        A função realiza as seguintes ações:
        - Reseta os valores dos widgets, como comboBoxCamada, lineEditNome, checkboxes e spinboxes.
        - Desativa o botão Converter e o scrollbar de transparência.
        - Esconde o botão de limpar texto.
        - Reseta as cores de borda e preenchimento, bem como o CRS selecionado.
        - Restaura os estilos dos botões de cor para os valores definidos no Qt Designer.
        - Desativa e desmarca o checkBoxSeleciona.
        - Reseta a camada atual e a conexão de seleção de feições.
        """
        self.comboBoxCamada.setCurrentIndex(0)  # Reseta a seleção do ComboBoxCamada para o primeiro item
        self.lineEditNome.clear()  # Limpa o campo de texto do lineEditNome
        self.pushButtonConverter.setEnabled(False)  # Desativa o botão Converter
        self.horizontalScrollBarTransparency.setValue(0)  # Reseta o scrollbar de transparência
        self.horizontalScrollBarTransparency.setEnabled(False)  # Desativa o scrollbar de transparência
        self.findChild(QCheckBox, 'checkBoxID').setChecked(False)  # Desmarca o checkbox ID
        self.findChild(QCheckBox, 'checkBoxArea').setChecked(False)  # Desmarca o checkbox Área
        self.findChild(QCheckBox, 'checkBoxPerim').setChecked(False)  # Desmarca o checkbox Perímetro
        self.findChild(QCheckBox, 'checkBoxAdicionar').setChecked(False)  # Desmarca o checkbox Adicionar
        self.findChild(QCheckBox, 'checkBoxDel').setChecked(False)
        self.findChild(QCheckBox, 'checkBoxRemover').setChecked(False)
        self.doubleSpinBoxBorda.setValue(0.26) # Define um valor padrão para o doubleSpinBoxBorda
        self.clear_button.hide()  # Esconde o botão de limpar texto
        self.acao_pushButtonCor = False  # Reseta a variável que controla se o botão de cor foi acionado
        self.label_color = QColor(Qt.GlobalColor.black)
        self.borda_cor = None  # Define a cor da borda como preto (GlobalColor)
        self.preenchimento_cor = None  # Define a cor de preenchimento como branco (GlobalColor)
        self.selected_crs = None  # Reseta o CRS selecionado

        # Restaura o estilo padrão do botão de cor definido no Qt Designer
        self.pushButtonCor.setStyleSheet(self.pushButtonCor_default_style)
        self.pushButtonCorRotulo.setStyleSheet(self.pushButtonCorRotulo_default_style)
        # Reseta o checkBoxSeleciona
        checkBoxSeleciona = self.findChild(QCheckBox, 'checkBoxSeleciona')
        checkBoxSeleciona.setChecked(False)  # Desmarca o checkBoxSeleciona
        checkBoxSeleciona.setEnabled(False)  # Desativa o checkBoxSeleciona

        # Reseta a camada atual e as conexões
        self.current_layer = None  # Reseta a camada atual
        self.selection_changed_connection = None  # Reseta a conexão do sinal

    def choose_label_color(self):
        """
        Abre o diálogo de escolha de cores para definir a cor do rótulo.

        Parâmetros:
        self : objeto
            Referência à instância atual da classe.

        A função realiza as seguintes ações:
        - Abre um diálogo de escolha de cores.
        - Verifica se a cor escolhida pelo usuário é válida.
        - Se for válida, armazena a cor escolhida no atributo `label_color`.
        - Atualiza o estilo do botão `pushButtonCorRotulo` para refletir a cor escolhida.
        """
        
        # Abre o diálogo de escolha de cores, usando a cor atual do rótulo como cor inicial
        color = QColorDialog.getColor(self.label_color, self, self.tr("Escolha a cor do rótulo"))
        
        if color.isValid():  # Verifica se a cor escolhida é válida
            self.label_color = color  # Armazena a cor escolhida
            # Atualiza o estilo do botão para refletir a cor selecionada
            self.pushButtonCorRotulo.setStyleSheet(f"background-color: {color.name()};")

    def update_pushButtonConverter_state(self):
        """
        Ativa ou desativa o botão pushButtonConverter com base na presença de uma camada no comboBoxCamada.

        Parâmetros:
        self : objeto
            Referência à instância atual da classe.

        A função realiza as seguintes ações:
        - Verifica se há camadas disponíveis no comboBoxCamada.
        - Se houver camadas e uma camada estiver selecionada, ativa o botão Converter.
        - Se não houver camadas ou nenhuma camada estiver selecionada, desativa o botão Converter.
        """
        
        # Verifica se há camadas no comboBoxCamada e se alguma está selecionada
        if self.comboBoxCamada.count() > 0 and self.comboBoxCamada.currentIndex() >= 0:
            self.pushButtonConverter.setEnabled(True)  # Ativa o botão se houver camada selecionada
        else:
            self.pushButtonConverter.setEnabled(False)  # Desativa o botão se não houver camada selecionada

    def update_combo_box_rotulagem(self):
        """
        Atualiza o comboBoxRotulagem com base nos campos da camada selecionada no comboBoxCamada e nas configurações de checkbox.

        Parâmetros:
        self : objeto
            Referência à instância atual da classe.

        A função realiza as seguintes ações:
        - Limpa o comboBoxRotulagem e adiciona a opção padrão "Rótulos: Opcional".
        - Verifica se uma camada está selecionada no comboBoxCamada.
        - Adiciona os campos da camada selecionada ao comboBoxRotulagem.
        - Adiciona campos extras (ID, Área, Perímetro) se os checkboxes correspondentes estiverem marcados.
        - Verifica se o comboBoxRotulagem está vazio além da opção inicial, desativando-o se necessário.
        - Restaura a seleção do campo de rótulo anteriormente escolhido, se possível.
        """
        current_label = self.comboBoxRotulagem.currentText()  # Armazena o campo de rótulo atualmente selecionado

        self.comboBoxRotulagem.clear()  # Limpa o comboBoxRotulagem
        self.comboBoxRotulagem.addItem(self.tr("Rótulos: Opcional"))  # Adiciona o item inicial
        self.comboBoxRotulagem.setToolTip(self.tr("Escolha um rótulo (Opcional)"))  # Define o tooltip

        # Obtém a camada selecionada
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
                        self.comboBoxRotulagem.addItem("ID") # Adiciona o campo "ID" se o checkbox estiver marcado
                        added_fields.add("ID")
                    if self.findChild(QCheckBox, 'checkBoxArea').isChecked() and "Área" not in added_fields:
                        self.comboBoxRotulagem.addItem("Área") # Adiciona o campo "Área" se o checkbox estiver marcado
                        added_fields.add("Área")
                    if self.findChild(QCheckBox, 'checkBoxPerim').isChecked() and "Perímetro" not in added_fields:
                        self.comboBoxRotulagem.addItem("Perímetro") # Adiciona o campo "Perímetro" se o checkbox estiver marcado
                        added_fields.add("Perímetro")

        # Verifica se o comboBox está vazio além da opção inicial
        if self.comboBoxRotulagem.count() == 1:
            self.comboBoxRotulagem.setEnabled(False)
        else:
            self.comboBoxRotulagem.setEnabled(True)

        # Tenta restaurar a seleção do campo de rótulo anteriormente escolhido
        index = self.comboBoxRotulagem.findText(current_label)
        if index != -1: # Se o campo for encontrado
            self.comboBoxRotulagem.setCurrentIndex(index) # Define o campo como o selecionado

    def apply_labels_to_layer(self, layer):
        """
        Aplica rótulos à camada selecionada com base no campo de rotulagem escolhido no comboBoxRotulagem.

        Parâmetros:
        self : objeto
            Referência à instância atual da classe.
        layer : QgsVectorLayer
            A camada na qual os rótulos serão aplicados.

        A função realiza as seguintes ações:
        - Verifica se a camada é válida e do tipo QgsVectorLayer.
        - Obtém o campo de rotulagem selecionado no comboBoxRotulagem.
        - Configura as definições de rotulagem com base no campo selecionado.
        - Define o formato de texto do rótulo, como a cor.
        - Aplica as configurações de rotulagem à camada e ativa os rótulos.
        - Recarrega a camada para aplicar as mudanças de rotulagem.
        """
       # Verifica se a camada é válida e do tipo QgsVectorLayer
        if not isinstance(layer, QgsVectorLayer):
            return  # Sai da função se a camada não for válida

        # Obtém o campo selecionado para rotulagem
        label_field = self.comboBoxRotulagem.currentText()

        if self.comboBoxRotulagem.currentIndex() == 0:
            return

        # Configura o provedor de rótulos
        label_settings = QgsPalLayerSettings()  # Cria uma instância das configurações de rótulos
        label_settings.fieldName = label_field  # Define o nome do campo de rotulagem
        label_settings.placement = Qgis.LabelPlacement.OverPoint  # Define a posição dos rótulos (sobre pontos)
        label_settings.enabled = True  # Ativa a rotulagem

        # Define a cor do rótulo
        text_format = QgsTextFormat()  # Cria uma instância de formato de texto
        text_format.setColor(self.label_color)  # Define a cor do rótulo
        label_settings.setFormat(text_format)  # Aplica o formato de texto às configurações de rotulagem

        # Aplica os rótulos à camada
        labeling = QgsVectorLayerSimpleLabeling(label_settings)  # Cria uma instância de rotulagem simples
        layer.setLabeling(labeling)  # Aplica a configuração de rotulagem à camada
        layer.setLabelsEnabled(True)  # Ativa os rótulos na camada
        layer.triggerRepaint()  # Recarrega a camada para aplicar as mudanças