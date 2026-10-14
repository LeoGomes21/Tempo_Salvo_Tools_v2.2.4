from qgis.core import QgsProject, QgsMessageLog, Qgis, QgsVectorLayer, QgsWkbTypes, QgsProcessingFeatureSourceDefinition, QgsProcessing, QgsCoordinateReferenceSystem, QgsProcessingContext, QgsMeshLayer, QgsMapSettings, QgsMapRendererCustomPainterJob, QgsGeometry, QgsPointXY
from qgis.PyQt.QtWidgets import QDialog, QCheckBox, QProgressBar, QComboBox, QGraphicsScene, QFileDialog, QTextBrowser, QVBoxLayout, QHBoxLayout, QPushButton
from qgis.PyQt.QtCore import Qt, QSize, QSettings, QCoreApplication
from qgis.PyQt.QtGui import QImage, QPainter, QColor, QPixmap
from qgis.gui import QgsProjectionSelectionDialog
from qgis.PyQt import uic
import processing
import time
import math
import os

FORM_CLASS, _ = uic.loadUiType(os.path.join(
    os.path.dirname(__file__), 'CriaMalhas.ui'))

class MalhaManager(QDialog, FORM_CLASS):
    def __init__(self, iface, plugin, parent=None):
        """Constructor."""
        super(MalhaManager, self).__init__(parent)
        # Configura a interface do usuário a partir do Designer.
        self.setupUi(self)

        self.iface = iface  # Armazena a referência da interface QGIS
        self.plugin = plugin        # Guarda a referência ao plugin principal (CriarVetor)

        # Inicializa a cena gráfica
        self.scene = QGraphicsScene(self)
        self.graphicsViewPontos.setScene(self.scene)

        # Altera o título da janela
        self.setWindowTitle(self.tr("Criação de Malhas"))

        # Preenche o comboBox com camadas de pontos
        self.populate_combo_box()

        # Preenche o comboBox com os campos
        self.populate_combo_box_z()

        # Conecta os sinais aos slots
        self.connect_signals()

        self.display_point_layer()

        self.selection_color = QColor(Qt.GlobalColor.yellow)  # Cor personalizável
        
        # Inicializa os LineEdits com valores padrão e estilo
        self.lineEditFeicoes.setReadOnly(True)
        self.lineEditSelecionados.setReadOnly(True)
        self.lineEditFeicoes.setStyleSheet("color: silver;")
        self.lineEditSelecionados.setStyleSheet("color: silver;")
        # self.lineEditFeicoes.setText("Total/Feições: 0")
        # self.lineEditSelecionados.setText("Selecionados: 0")

        self.output_path = None  # Variável para armazenar o caminho

        self.lineEditSalvar.setReadOnly(True)
        self.lineEditSalvar.setText(self.tr("[Salvar em arquivo temporário]"))
        self.lineEditSalvar.setStyleSheet("color: silver;")

        # Configuração do ajuste do contorno externo da malha
        self.doubleSpinBoxALPHA.setDecimals(2)
        self.doubleSpinBoxALPHA.setRange(0.00, 1.00)
        self.doubleSpinBoxALPHA.setSingleStep(0.05)
        self.doubleSpinBoxALPHA.setValue(0.15)
        self.doubleSpinBoxALPHA.setEnabled(self.checkBoxRebarbas.isChecked())

    def tr(self, message):
        """
        Traduz textos deste diálogo.
        O contexto precisa ser estável para o Qt Linguist encontrar as traduções.
        """
        return QCoreApplication.translate("MalhaManager", message)

    def connect_signals(self):

        # Conecta a mudança de seleção no comboBoxCamada para atualizar o checkBoxSeleciona
        self.comboBoxCamada.currentIndexChanged.connect(self.update_checkBoxSeleciona)

        # Conecta sinais para atualizar contagens de feições
        self.comboBoxCamada.currentIndexChanged.connect(self.update_feature_counts)

        # Conecta sinais do projeto para atualizar comboBox quando camadas forem adicionadas, removidas ou renomeadas
        QgsProject.instance().layersAdded.connect(self.populate_combo_box)
        QgsProject.instance().layersRemoved.connect(self.populate_combo_box)
        QgsProject.instance().layerWillBeRemoved.connect(self.populate_combo_box)

        # Conecta a mudança de seleção no comboBoxCamada para atualizar o comboBoxZ
        self.comboBoxCamada.currentIndexChanged.connect(self.populate_combo_box_z)
        # Conecta a mudança de seleção no comboBoxCamada para atualizar o checkBoxZ
        self.comboBoxCamada.currentIndexChanged.connect(self.update_checkBoxZ)

        # Conecta o clique do botão pushButtonExecutar para executar o cálculo da malha
        self.pushButtonExecutar.clicked.connect(self.execute_mesh_calculation)

        self.comboBoxCamada.currentIndexChanged.connect(self.display_point_layer)

        # Conecta sinais de seleção e modificação de feições
        self.comboBoxCamada.currentIndexChanged.connect(self.update_layer_connections)

        # Conectar o botão para definir o salvamento
        self.pushButtonSalvar.clicked.connect(self.definir_local_salvamento)

        # Conecta sinais para atualizar o estado do botão pushButtonExecutar
        self.comboBoxCamada.currentIndexChanged.connect(self.update_button_state)
        self.comboBoxZ.currentIndexChanged.connect(self.update_button_state)
        QgsProject.instance().layersAdded.connect(self.update_button_state)
        QgsProject.instance().layersRemoved.connect(self.update_button_state)

        # Conecta sinais de adição/remoção de camadas para atualizar o checkBoxZ
        QgsProject.instance().layersAdded.connect(self.update_checkBoxZ)
        QgsProject.instance().layersRemoved.connect(self.update_checkBoxZ)

        # Conecta o sinal stateChanged do checkBoxZ para atualizar o estado do comboBoxZ
        self.checkBoxZ.stateChanged.connect(self.update_combo_box_z_state)

        # Conecta o botão Fechar ao slot de fechar o diálogo
        self.pushButtonFechar.clicked.connect(self.hide)

        # Ao clicar no pushButtonRasterizar, chama o método rasterizar_malha
        self.pushButtonRasterizar.clicked.connect(self.abrir_dialogo_rasterizar)

        # atualiza o botão pushButtonRasterizar cm base na existência de Camadas de malhas
        QgsProject.instance().layersAdded.connect(self.update_rasterizar_button_state)
        QgsProject.instance().layersRemoved.connect(self.update_rasterizar_button_state)
        QgsProject.instance().layerWillBeRemoved.connect(self.update_rasterizar_button_state)

        # Habilita o controle ALPHA somente quando o ajuste automático do contorno estiver ativo
        self.checkBoxRebarbas.toggled.connect(self._atualizar_estado_alpha)

        # Abre as orientações de uso da ferramenta
        self.pushButtonUsar.clicked.connect(self.abrir_ajuda_uso)

    def _atualizar_estado_alpha(self):
        """
        Habilita o valor ALPHA somente quando o ajuste
        automático do contorno da malha estiver ativo.
        """
        self.doubleSpinBoxALPHA.setEnabled(self.checkBoxRebarbas.isChecked())

    def showEvent(self, event):
        """
        Sobrescreve o evento de exibição do diálogo para resetar os Widgets.
        """
        super(MalhaManager, self).showEvent(event)

        self.populate_combo_box()  # Atualiza o comboBoxCamada com as camadas disponíveis

        self.update_checkBoxSeleciona()  # Atualiza o estado do checkBoxSeleciona com base nas feições selecionadas

        self.update_layer_connections()  # Conecta os sinais da camada atual

        self.update_checkBoxZ()  # Conecta os sinais da camada com Z

        self.display_point_layer()  # Atualiza a visualização ao abrir

        self.update_feature_counts()  # Atualiza as contagens de feições

        # Atualiza o estado do botão pushButtonExecutar
        self.update_button_state()

        # Atualiza o estado inicial do comboBoxZ com base no checkBoxZ
        self.update_combo_box_z_state()

        # Atualiza o estado do botão pushButtonRasterizar
        self.update_rasterizar_button_state()

        # Atualiza o estado do controle ALPHA
        self._atualizar_estado_alpha()

    def _log_message(self, message, level=Qgis.MessageLevel.Info):
        QgsMessageLog.logMessage(message, 'Malha', level=level)

    def iniciar_progress_bar(self, total_steps):
        """
        Inicia e exibe uma barra de progresso na interface do usuário para o processo de exportação.

        Parâmetros:
        - total_steps (int): O número total de etapas a serem concluídas no processo de exportação.

        Funcionalidades:
        - Cria uma mensagem personalizada na barra de mensagens para acompanhar o progresso.
        - Configura e estiliza uma barra de progresso.
        - Adiciona a barra de progresso à barra de mensagens e a exibe na interface do usuário.
        - Define o valor máximo da barra de progresso com base no número total de etapas.
        - Retorna os widgets de barra de progresso e de mensagem para que possam ser atualizados durante a exportação.
        """
        progressMessageBar = self.iface.messageBar().createMessage(self.tr("Gerando a Camada de Malha"))
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
        # Obtém a barra de mensagens da interface do QGIS
        bar = self.iface.messageBar()  # Acessa a barra de mensagens da interface do QGIS

        # Exibe a mensagem com o nível apropriado baseado no tipo
        if tipo == "Erro":
            # Mostra uma mensagem de erro na barra de mensagens com um ícone crítico e a duração especificada
            bar.pushMessage("Erro", texto, level=Qgis.MessageLevel.Critical, duration=duracao)
        elif tipo == "Sucesso":
            msg = bar.createMessage("Sucesso", texto)
            bar.pushWidget(msg, level=Qgis.MessageLevel.Info, duration=duracao)

        elif tipo == "Aviso":
            bar.pushMessage("Aviso", texto, level=Qgis.MessageLevel.Warning, duration=duracao)

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
        self.comboBoxCamada.blockSignals(True)  # Bloqueia os sinais para evitar chamadas desnecessárias a update_poligono_edit_nome
        self.comboBoxCamada.clear()  # Limpa o comboBox antes de preencher

        layer_list = QgsProject.instance().mapLayers().values()
        for layer in layer_list:
            if isinstance(layer, QgsVectorLayer) and QgsWkbTypes.geometryType(layer.wkbType()) == QgsWkbTypes.GeometryType.PointGeometry:
                self.comboBoxCamada.addItem(layer.name(), layer.id())
                layer.nameChanged.connect(self.update_combo_box_item)  # Conecta o sinal nameChanged à função update_combo_box_item

        # Restaura a seleção anterior, se possível
        if current_layer_id:
            index = self.comboBoxCamada.findData(current_layer_id) # Tenta encontrar a camada selecionada anteriormente
            if index != -1:
                self.comboBoxCamada.setCurrentIndex(index) # Restaura a seleção anterior

        self.comboBoxCamada.blockSignals(False)  # Desbloqueia os sinais

        self.update_feature_counts()  # Atualiza as contagens após preencher o comboBox

        # Garante que o comboBoxZ seja atualizado mesmo quando não há camadas
        self.populate_combo_box_z()

        self.update_layer_connections()  # Atualiza conexões com a nova camada

        self.display_point_layer()  # Atualiza após mudanças nas camadas

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

    def populate_combo_box_z(self):
        """
        Popula o comboBoxZ com os campos numéricos da camada atualmente selecionada no comboBoxCamada,
        excluindo campos que se referem às coordenadas das feições.
        """
        self.comboBoxZ.clear()  # Limpa o comboBoxZ antes de preencher
        layer_id = self.comboBoxCamada.currentData()  # Obtém o ID da camada selecionada
        if layer_id:
            layer = QgsProject.instance().mapLayer(layer_id)
            if layer:
                # Lista de nomes de campos que geralmente representam coordenadas
                coordinate_field_names = {'id', 'x', 'y', 'coord_x', 'coord_y', 'xcoord', 'ycoord', 'longitude', 'latitude'}

                # Itera sobre os campos da camada e adiciona apenas os numéricos que não são coordenadas
                for field in layer.fields():
                    if field.isNumeric():
                        # Verifica se o nome do campo está na lista de nomes de coordenadas (case-insensitive)
                        if field.name().lower() not in coordinate_field_names:
                            self.comboBoxZ.addItem(field.name(), field.name())

        # Atualiza o estado do botão após preencher o comboBoxZ
        self.update_button_state()

    def update_checkBoxZ(self):
        """
        Atualiza o estado do checkBoxZ para que fique ativo apenas se a camada de pontos
        selecionada possuir dimensão Z (ou seja, for uma camada 3D).
        """
        layer_id = self.comboBoxCamada.currentData()  # Obtém o ID da camada selecionada
        checkBoxZ = self.findChild(QCheckBox, 'checkBoxZ')
        if layer_id:
            layer = QgsProject.instance().mapLayer(layer_id)
            # Verifica se a camada existe e se possui dimensão Z
            if layer and QgsWkbTypes.hasZ(layer.wkbType()):
                checkBoxZ.setEnabled(True)
                checkBoxZ.setChecked(False)
            else:
                checkBoxZ.setEnabled(False)
                checkBoxZ.setChecked(False) # Desmarca o checkBoxZ se a camada não tiver geometria Z
        else:
            checkBoxZ.setEnabled(False)
            checkBoxZ.setChecked(False) # Desativa e desmarca o checkBoxZ se nenhuma camada estiver selecionada

    def resizeEvent(self, event):
        super(MalhaManager, self).resizeEvent(event)
        self.display_point_layer()

    def display_point_layer(self):
        """
        Renderiza a camada de pontos com destaque para a seleção do QGIS, sem alterar o estado da seleção.
        """

        # Verifica se o diálogo está visível
        if not self.isVisible():
            return
        
        # Restante do código original
        self.scene.clear()

        layer_id = self.comboBoxCamada.currentData()
        if not layer_id:
            return

        layer = QgsProject.instance().mapLayer(layer_id)
        if not layer or not isinstance(layer, QgsVectorLayer):
            return

        # Configurações do mapa com renderização da seleção
        map_settings = QgsMapSettings()
        map_settings.setLayers([layer])  # Usa a camada original
        map_settings.setBackgroundColor(QColor(255, 255, 255))
        map_settings.setDestinationCrs(QgsProject.instance().crs())
        map_settings.setFlag(QgsMapSettings.Flag.DrawSelection, True)  # Renderiza seleção do QGIS
        map_settings.setExtent(layer.extent())

        # Define o tamanho da imagem
        width = self.graphicsViewPontos.viewport().width()
        height = self.graphicsViewPontos.viewport().height()
        map_settings.setOutputSize(QSize(width, height))

        # Renderiza a camada com seleção
        image = QImage(width, height, QImage.Format.Format_ARGB32)
        painter = QPainter(image)
        renderer = QgsMapRendererCustomPainterJob(map_settings, painter)
        renderer.start()
        renderer.waitForFinished()
        painter.end()

        # Exibe a imagem no QGraphicsView
        pixmap = QPixmap.fromImage(image)
        self.scene.addPixmap(pixmap)
        self.graphicsViewPontos.setScene(self.scene)
        self.graphicsViewPontos.fitInView(self.scene.sceneRect(), Qt.AspectRatioMode.KeepAspectRatio)

    def update_layer_connections(self):
        """
        Conecta os sinais da camada para atualizar a visualização em tempo real.
        """

        layer_id = self.comboBoxCamada.currentData()
        if layer_id:
            layer = QgsProject.instance().mapLayer(layer_id)
            if layer:
                # Conecta o sinal de seleção para atualizar o graphicsViewPontos
                layer.selectionChanged.connect(self.display_point_layer)
                # Desconecta sinais anteriores (evita múltiplas conexões)
                try:
                    layer.featureAdded.disconnect()
                    layer.featureDeleted.disconnect()
                    layer.attributeValueChanged.disconnect()
                    layer.styleChanged.disconnect()
                except TypeError:
                    pass  # nosec B110 | Ignora se não estava conectado

                # Conecta sinais de modificação de feições
                layer.selectionChanged.connect(self.display_point_layer)
                layer.featureAdded.connect(self.update_feature_counts)
                layer.featureDeleted.connect(self.update_feature_counts)
                layer.selectionChanged.connect(self.update_feature_counts)

                # Conecta sinais de modificação da camada
                layer.featureAdded.connect(self.display_point_layer)
                layer.featureDeleted.connect(self.display_point_layer)
                layer.attributeValueChanged.connect(self.display_point_layer)
                layer.styleChanged.connect(self.display_point_layer)

                # Mantém a conexão com seleção (já existente)
                layer.selectionChanged.connect(self.update_checkBoxSeleciona)
                self.update_checkBoxSeleciona()

                # Atualiza imediatamente as contagens
                self.update_feature_counts()

        else:
            self.update_checkBoxSeleciona()
            self.update_feature_counts()  # Limpa os campos se não houver camada

    def update_feature_counts(self):
        """
        Atualiza os valores dos lineEditFeicoes e lineEditSelecionados com base na camada selecionada.
        Configura os campos com prefixos e define a cor do texto como prata.
        """
        # Configura os lineEdits como somente leitura e define a cor do texto como prata
        self.lineEditFeicoes.setReadOnly(True)
        self.lineEditSelecionados.setReadOnly(True)
        self.lineEditFeicoes.setStyleSheet("color: silver;")
        self.lineEditSelecionados.setStyleSheet("color: silver;")

        # Obtém a camada selecionada
        layer_id = self.comboBoxCamada.currentData()
        if layer_id:
            layer = QgsProject.instance().mapLayer(layer_id)
            if layer and isinstance(layer, QgsVectorLayer):
                # Total de feições
                total_features = layer.featureCount()
                self.lineEditFeicoes.setText(f"{total_features}")
                
                # Feições selecionadas (apenas para a camada selecionada)
                selected_features = layer.selectedFeatureCount()
                self.lineEditSelecionados.setText(f"{selected_features}")
            else:
                # Limpa os campos se não houver camada válida
                self.lineEditFeicoes.setText(self.tr("Nenhuma"))
                self.lineEditSelecionados.setText(self.tr("Nenhuma"))
        else:
            # Limpa os campos se não houver camada selecionada
            self.lineEditFeicoes.setText(self.tr("Nenhuma"))
            self.lineEditSelecionados.setText(self.tr("Nenhuma"))

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
        fileName, _ = QFileDialog.getSaveFileName(self, self.tr("Salvar Camada"), nome_completo_proposto, tipo_arquivo)

        # Adicionar verificação de permissão de escrita
        if fileName and not os.access(os.path.dirname(fileName), os.W_OK):
            self.mostrar_mensagem(self.tr("Sem permissão para escrever em: {folder_path}").format(folder_path=os.path.dirname(fileName)), "Erro")
            return None

        return fileName  # Retorna o caminho completo do arquivo escolhido ou None se cancelado

    def abrir_ajuda_uso(self):
        """
        Abre uma janela com orientações de uso
        do módulo de criação de malhas.
        """
        dialog_existente = getattr(self, "_dialogo_ajuda_uso", None)

        if (dialog_existente is not None
            and dialog_existente.isVisible()):

            dialog_existente.raise_()
            dialog_existente.activateWindow()
            return

        dialog = QDialog(self)
        self._dialogo_ajuda_uso = dialog

        dialog.setWindowTitle(self.tr("Como usar - Criação de Malhas"))
        dialog.setWindowModality(Qt.WindowModality.NonModal)

        dialog.resize(650, 600)
        dialog.setMinimumSize(540, 450)

        layout = QVBoxLayout(dialog)
        layout.setContentsMargins(10, 10, 10, 10)
        layout.setSpacing(8)

        texto = QTextBrowser(dialog)
        texto.setOpenExternalLinks(True)

        partes = [
            f"<h2>{self.tr('Criação de Malhas')}</h2>",

            f"<p>{self.tr('Esta ferramenta permite gerar uma malha TIN a partir de uma camada de pontos, utilizando a coordenada Z da geometria ou um campo numérico como valor de elevação.')}</p>",

            f"<hr><h3>{self.tr('Como utilizar')}</h3>",

            "<ol>",

            f"<li><b>{self.tr('Selecione a camada de pontos')}</b><br>"
            f"{self.tr('Escolha a camada que contém os pontos que serão utilizados para gerar a superfície TIN.')}</li><br>",

            f"<li><b>{self.tr('Defina o valor do vértice')}</b><br>"
            f"{self.tr('Se a camada possuir geometria 3D, marque Z para utilizar diretamente a coordenada Z dos pontos. Caso contrário, selecione no campo ao lado o atributo que contém as cotas.')}</li><br>",

            f"<li><b>{self.tr('Utilize somente feições selecionadas, quando necessário')}</b><br>"
            f"{self.tr('Marque Apenas Feições selecionadas para gerar a malha somente com os pontos atualmente selecionados na camada.')}</li><br>",

            f"<li><b>{self.tr('Ajuste o contorno externo, quando necessário')}</b><br>"
            f"{self.tr('A opção Autoajustar contorno da malha cria um limite côncavo baseado na distribuição dos pontos e remove faces da TIN que ultrapassem esse limite. Essa opção é útil para evitar grandes triângulos externos em áreas côncavas ou irregulares.')}</li><br>",

            f"<li><b>{self.tr('Defina o valor de concavidade')}</b><br>"
            f"{self.tr('O valor ALPHA controla o quanto o contorno externo acompanha a distribuição dos pontos. Valores menores produzem um contorno mais aderente e côncavo. Valores maiores produzem um contorno mais aberto e próximo do casco convexo. O valor padrão é 0,15.')}</li><br>",

            f"<li><b>{self.tr('Defina o local de salvamento, se desejar')}</b><br>"
            f"{self.tr('O botão Salvar permite escolher um arquivo de destino. Se nenhum local for informado, a malha será criada como arquivo temporário.')}</li><br>",

            f"<li><b>{self.tr('Execute a geração')}</b><br>"
            f"{self.tr('Clique em Executar para criar a malha TIN. Depois de criada, a camada será adicionada automaticamente ao projeto.')}</li>",

            "</ol>",

            f"<hr><h3>{self.tr('Ajuste do contorno')}</h3>",

            f"<p><b>ALPHA 0,05 - 0,10:</b> "
            f"{self.tr('contorno bastante aderente aos pontos. Pode ser útil em áreas com concavidades pronunciadas, mas pode recortar demais em distribuições irregulares.')}</p>",

            f"<p><b>ALPHA 0,15:</b> "
            f"{self.tr('valor inicial recomendado para o ajuste do contorno.')}</p>",

            f"<p><b>ALPHA 0,20 - 0,40:</b> "
            f"{self.tr('contorno progressivamente mais aberto, preservando áreas maiores entre os pontos.')}</p>",

            f"<p><b>ALPHA 0,50 - 1,00:</b> "
            f"{self.tr('contorno cada vez menos côncavo e mais próximo de um envoltório externo geral dos pontos.')}</p>",

            f"<hr><h3>{self.tr('Dicas importantes')}</h3>",

            "<ul>",

            f"<li>{self.tr('Se aparecerem grandes triângulos ligando regiões que deveriam permanecer separadas, tente reduzir o valor ALPHA.')}</li>",

            f"<li>{self.tr('Se partes válidas da superfície forem recortadas, aumente gradualmente o valor ALPHA.')}</li>",

            f"<li>{self.tr('O ajuste do contorno considera a distribuição XY dos pontos. As cotas Z não determinam o limite externo da malha.')}</li>",

            f"<li>{self.tr('Quando o ajuste automático estiver desativado, a malha utiliza diretamente a triangulação TIN padrão.')}</li>",

            "</ul>",

            f"<hr><p><b>{self.tr('Resumo:')}</b> "
            f"{self.tr('Pontos → Cota Z → Seleção opcional → Ajuste do contorno/ALPHA → Gerar TIN → Rasterizar, quando necessário.')}</p>"]

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

    def execute_mesh_calculation(self):
        # Validação da camada de pontos
        layer_id = self.comboBoxCamada.currentData()

        if not layer_id:
            self.mostrar_mensagem(self.tr("Selecione uma camada de pontos válida."), "Erro")
            return

        layer = QgsProject.instance().mapLayer(layer_id)

        if (not layer
            or layer.geometryType()
            != QgsWkbTypes.GeometryType.PointGeometry):
            self.mostrar_mensagem(self.tr("Camada inválida ou não é do tipo ponto."), "Erro")
            return

        # Seleção do SRC da malha de saída
        dlg_crs = QgsProjectionSelectionDialog(self)

        dlg_crs.setWindowTitle(self.tr("Selecionar SRC da Malha"))

        # Usa preferencialmente o SRC
        # da camada de pontos
        crs_inicial = layer.crs()

        # Fallback para o SRC do projeto
        if not crs_inicial.isValid():
            crs_inicial = QgsProject.instance().crs()

        if crs_inicial.isValid():
            dlg_crs.setCrs(crs_inicial)

        if (dlg_crs.exec()
            != QDialog.DialogCode.Accepted):
            self.mostrar_mensagem(self.tr("A criação da malha foi cancelada porque o SRC não foi definido."), "Aviso")
            return

        crs_saida = dlg_crs.crs()

        if not crs_saida.isValid():
            self.mostrar_mensagem(self.tr("O SRC selecionado não é válido."), "Erro")
            return

        # Validação de seleção
        use_selected = self.checkBoxSeleciona.isChecked()

        if (use_selected
            and layer.selectedFeatureCount() == 0):
            self.mostrar_mensagem(
                self.tr("Não há feições selecionadas."), "Erro")
            return

        # Configuração do uso de Z
        use_z = self.checkBoxZ.isChecked()
        z_field_index = -1  # Valor padrão para usar geometria Z
        if use_z:
            if not QgsWkbTypes.hasZ(layer.wkbType()):
                self.mostrar_mensagem(self.tr("A camada selecionada não possui dimensão Z."), "Erro")
                return
        else:
            # Se checkBoxZ não está marcado, usa o campo Z do comboBoxZ
            z_field_name = self.comboBoxZ.currentData()
            if z_field_name:
                z_field_index = layer.fields().indexFromName(z_field_name)
            else:
                self.mostrar_mensagem(self.tr("Selecione um campo Z válido ou marque 'Usar Z da Geometria'."), "Erro")
                return

        # Preparação dos dados
        try:
            # Cria camada temporária para seleção (se necessário)
            temp_layer = None
            if use_selected:
                temp_layer = QgsVectorLayer(f"Point?crs={layer.crs().authid()}", "selected_points", "memory")
                temp_layer.dataProvider().addAttributes(layer.fields())
                temp_layer.updateFields()
                temp_layer.dataProvider().addFeatures([f for f in layer.getSelectedFeatures()])
                temp_layer.updateExtents()

                # Adiciona a camada temporária ao projeto
                QgsProject.instance().addMapLayer(temp_layer)
                source_layer = temp_layer
            else:
                source_layer = layer

            # Configuração da barra de progresso
            progress_bar, progress_msg = self.iniciar_progress_bar(1)

            # Configuração do parâmetro SOURCE_DATA
            source_data = [{
                'source': source_layer.id(),
                'type': 2,  # Pontos para vértices TIN
                'attributeIndex': z_field_index}]  # Para geometria Z ou índice do campo

            # Prepara saída
            caminho_saida = (self.output_path           # se o usuário escolheu
                             if getattr(self, "output_path", None)
                             else 'TEMPORARY_OUTPUT')   # caso contrário, temporário

            # Executa o algoritmo
            result = processing.run(
                "native:tinmeshcreation",
                {'SOURCE_DATA': source_data,
                    'MESH_FORMAT': 0,
                    'CRS_OUTPUT': crs_saida,
                    'OUTPUT_MESH': caminho_saida})

            # Será justamente esse arquivo.
            mesh_path = result['OUTPUT_MESH']

            # Remove triângulos externos com arestas anormalmente longas.
            if self.checkBoxRebarbas.isChecked():
                alpha = self.doubleSpinBoxALPHA.value()

                mesh_path = self._remover_rebarbas_externas_malha(mesh_path, source_layer, alpha)

            # Define nome único baseado na camada de pontos
            base_mesh_name = f"{layer.name()}_TIN"

            mesh_name = self._nome_unico_no_projeto(base_mesh_name)
            mesh_layer = QgsMeshLayer(mesh_path, mesh_name, "mdal")

            if not mesh_layer.isValid():
                raise Exception(self.tr("Falha ao carregar a malha gerada"))

            # Garante o SRC na QgsMeshLayer.
            # Alguns formatos MDAL podem não preservar
            # o SRC dentro do próprio arquivo.
            mesh_layer.setCrs(crs_saida)

            # Adiciona ao projeto
            QgsProject.instance().addMapLayer(mesh_layer)

            self.mostrar_mensagem(self.tr("Malha TIN gerada com sucesso!"), "Sucesso", caminho_pasta=QgsProject.instance().homePath())

        except Exception as e:
            self.mostrar_mensagem(self.tr("Erro: {error}").format(error=str(e)), "Erro")
        finally:
            # Limpeza
            if temp_layer is not None:
                QgsProject.instance().removeMapLayer(temp_layer.id())  # Remove a camada temporária
            if progress_msg is not None:
                self.iface.messageBar().popWidget(progress_msg)

    def _remover_rebarbas_externas_malha(self, mesh_path, source_layer, alpha):
        """
        Remove somente faces da TIN que ultrapassam o contorno
        côncavo definido pela própria distribuição dos pontos.
        """
        if not mesh_path or not os.path.exists(mesh_path):
            return mesh_path

        if not source_layer or not source_layer.isValid():
            return mesh_path

        # 1. Cria o contorno côncavo dos pontos
        try:
            resultado_contorno = processing.run(
                "native:concavehull",
                {
                    "INPUT": source_layer,
                    "ALPHA": float(alpha),
                    "HOLES": False,
                    "NO_MULTIGEOMETRY": False,
                    "OUTPUT": "TEMPORARY_OUTPUT"})

            camada_contorno = resultado_contorno["OUTPUT"]

        except Exception as e:
            QgsMessageLog.logMessage(self.tr("Não foi possível criar o contorno para remover triângulos externos: {error}").format(error=str(e)), "Tempo Salvo Tools", Qgis.MessageLevel.Warning)

            return mesh_path

        if not camada_contorno or not camada_contorno.isValid():
            return mesh_path

        geometrias_contorno = [feature.geometry()
            for feature in camada_contorno.getFeatures()
            if feature.geometry()
            and not feature.geometry().isEmpty()]

        if not geometrias_contorno:
            return mesh_path

        geom_limite = QgsGeometry.unaryUnion(geometrias_contorno)

        if not geom_limite or geom_limite.isEmpty():
            return mesh_path

        # 2. Lê vértices e faces da malha 2DM
        try:
            with open(mesh_path, "r", encoding="utf-8",
                errors="ignore") as arquivo:

                linhas = arquivo.readlines()

        except OSError as e:
            QgsMessageLog.logMessage(self.tr("Não foi possível ler a malha para remover triângulos externos: {error}").format(error=str(e)), "Tempo Salvo Tools", Qgis.MessageLevel.Warning)

            return mesh_path

        vertices = {}
        faces = []

        for indice_linha, linha in enumerate(linhas):
            partes = linha.strip().split()

            if not partes:
                continue

            tipo = partes[0].upper()

            if tipo == "ND" and len(partes) >= 5:
                try:
                    node_id = int(partes[1])

                    vertices[node_id] = (
                        float(partes[2]),
                        float(partes[3]),
                        float(partes[4]))

                except (TypeError, ValueError):
                    continue

            elif tipo == "E3T" and len(partes) >= 5:
                try:
                    faces.append({"linha": indice_linha,
                        "nos": (
                            int(partes[2]),
                            int(partes[3]),
                            int(partes[4]))})

                except (TypeError, ValueError):
                    continue

        if not vertices or not faces:
            return mesh_path

        # 3. Verifica cada triângulo contra o contorno
        linhas_remover = set()

        for face in faces:
            n1, n2, n3 = face["nos"]

            if (n1 not in vertices
                or n2 not in vertices
                or n3 not in vertices):
                continue

            p1 = vertices[n1]
            p2 = vertices[n2]
            p3 = vertices[n3]

            triangulo = QgsGeometry.fromPolygonXY([[
                QgsPointXY(p1[0], p1[1]),
                QgsPointXY(p2[0], p2[1]),
                QgsPointXY(p3[0], p3[1]),
                QgsPointXY(p1[0], p1[1])]])

            area_triangulo = triangulo.area()

            if area_triangulo <= 1e-12:
                linhas_remover.add(face["linha"])
                continue

            try:
                intersecao = triangulo.intersection(geom_limite)

            except Exception as e:
                QgsMessageLog.logMessage(self.tr("Falha ao verificar um triângulo contra o contorno: {error}").format(error=str(e)), "Tempo Salvo Tools", Qgis.MessageLevel.Warning)

                continue

            if not intersecao or intersecao.isEmpty():
                linhas_remover.add(face["linha"])
                continue

            proporcao = (intersecao.area() / area_triangulo)

            # Mesmo princípio usado no CriarPlatoManager:
            # a face precisa estar praticamente inteira
            # dentro do contorno.
            if proporcao < 0.98:
                linhas_remover.add(face["linha"])

        if not linhas_remover:
            return mesh_path

        # 4. Regrava somente retirando as faces externas
        linhas_finais = [linha
            for indice, linha in enumerate(linhas)
            if indice not in linhas_remover]

        try:
            with open(mesh_path, "w",
                encoding="utf-8",
                newline="\n") as arquivo:

                arquivo.writelines(linhas_finais)

        except OSError as e:
            QgsMessageLog.logMessage(self.tr("Não foi possível gravar a malha sem triângulos externos: {error}").format(error=str(e)), "Tempo Salvo Tools", Qgis.MessageLevel.Warning)

            return mesh_path

        QgsMessageLog.logMessage(self.tr("Triângulos externos removidos: {count}.").format(count=len(linhas_remover)), "Tempo Salvo Tools", Qgis.MessageLevel.Info)

        return mesh_path

    def _distancia_referencia_vertices_malha(self, vertices):
        """
        Calcula a mediana da distância de cada vértice ao seu
        vizinho mais próximo.

        Essa distância representa aproximadamente o espaçamento
        normal dos pontos usados para gerar a malha.
        """
        pontos = list(vertices.values())

        if len(pontos) < 2:
            return 0.0

        distancias_minimas = []

        for i, ponto1 in enumerate(pontos):
            menor = None

            for j, ponto2 in enumerate(pontos):
                if i == j:
                    continue

                distancia = self._comprimento_aresta_malha(ponto1, ponto2)

                if distancia <= 1e-12:
                    continue

                if menor is None or distancia < menor:
                    menor = distancia

            if menor is not None:
                distancias_minimas.append(menor)

        if not distancias_minimas:
            return 0.0

        distancias_minimas.sort()

        quantidade = len(distancias_minimas)
        meio = quantidade // 2

        if quantidade % 2:
            return distancias_minimas[meio]

        return (distancias_minimas[meio - 1]
            + distancias_minimas[meio]) / 2.0

    def _comprimento_aresta_malha(self, ponto1, ponto2):
        """
        Retorna o comprimento 2D entre dois vértices da malha.
        """
        return math.hypot(
            ponto2[0] - ponto1[0],
            ponto2[1] - ponto1[1])

    def _podar_faces_externas_delgadas(self, vertices, faces, compactacao_min=0.035, razao_max=12.0, iteracoes_max=50):
        """
        Remove iterativamente triângulos de borda muito finos.
        Isso elimina 'agulhas' e rebarbas externas sem atacar o miolo da malha.
        """
        faces_ativas = list(faces)

        for _ in range(iteracoes_max):
            contagem_arestas = {}

            for _, n1, n2, n3, _ in faces_ativas:
                for a, b in ((n1, n2), (n2, n3), (n3, n1)):
                    aresta = tuple(sorted((a, b)))
                    contagem_arestas[aresta] = contagem_arestas.get(aresta, 0) + 1

            indices_remover = set()

            for indice, face in enumerate(faces_ativas):
                _, n1, n2, n3, _ = face

                arestas = [
                    tuple(sorted((n1, n2))),
                    tuple(sorted((n2, n3))),
                    tuple(sorted((n3, n1)))]

                qtd_arestas_borda = sum(1
                    for aresta in arestas
                    if contagem_arestas.get(aresta, 0) == 1)

                if qtd_arestas_borda == 0:
                    continue

                compactacao, razao, area = self._metricas_triangulo_2dm(
                    vertices[n1],
                    vertices[n2],
                    vertices[n3])

                if area <= 0:
                    indices_remover.add(indice)
                    continue

                # Remove pontas muito finas
                if qtd_arestas_borda >= 2 and razao > 4.0:
                    indices_remover.add(indice)
                    continue

                # Remove triângulos externos muito delgados
                if compactacao < compactacao_min and razao > razao_max:
                    indices_remover.add(indice)

            if not indices_remover:
                break

            faces_ativas = [face
                for indice, face in enumerate(faces_ativas)
                if indice not in indices_remover]

            if len(faces_ativas) < 3:
                break

        return faces_ativas

    def _metricas_triangulo_2dm(self, v1, v2, v3):
        """
        Retorna:
        - compactação: 1.0 ~ equilátero; próximo de 0 = muito fino
        - razão entre maior e menor lado
        - área 2D
        """
        x1, y1, _ = v1
        x2, y2, _ = v2
        x3, y3, _ = v3

        l1 = math.hypot(x2 - x1, y2 - y1)
        l2 = math.hypot(x3 - x2, y3 - y2)
        l3 = math.hypot(x1 - x3, y1 - y3)

        menor = min(l1, l2, l3)
        maior = max(l1, l2, l3)

        area = abs((x2 - x1) * (y3 - y1) - (y2 - y1) * (x3 - x1)) * 0.5

        if menor <= 1e-12:
            return 0.0, float("inf"), area

        soma_quadrados = l1 * l1 + l2 * l2 + l3 * l3

        if soma_quadrados <= 1e-12:
            return 0.0, float("inf"), area

        compactacao = (4.0 * math.sqrt(3.0) * area) / soma_quadrados
        razao = maior / menor

        return compactacao, razao, area

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

    def definir_local_salvamento(self):
        # nome padrão baseado na camada
        layer_id = self.comboBoxCamada.currentData()
        layer = QgsProject.instance().mapLayer(layer_id) if layer_id else None
        base_name = layer.name() if layer else self.tr("Malha")
        default_filename = f"{base_name}_TIN.mesh"

        caminho = self.escolher_local_para_salvar(default_filename, "MDAL Mesh (*.mesh)")
        if caminho:
            self.output_path = caminho # GUARDA O CAMINHO
            self.lineEditSalvar.setText(caminho)
            self.lineEditSalvar.setStyleSheet("color: black;")
        else:
            self.output_path = None # LIMPA SE CANCELAR
            self.lineEditSalvar.setText(self.tr("[Salvar em arquivo temporário]"))
            self.lineEditSalvar.setStyleSheet("color: silver;")

    def update_button_state(self):
        """
        Atualiza o estado do botão pushButtonExecutar com base nas condições:
        - A camada deve ter geometria Z ou pelo menos um campo numérico no comboBoxZ.
        """
        # Obtém a camada selecionada
        layer_id = self.comboBoxCamada.currentData()
        if not layer_id:
            self.pushButtonExecutar.setEnabled(False)
            return

        layer = QgsProject.instance().mapLayer(layer_id)
        if not layer or not isinstance(layer, QgsVectorLayer):
            self.pushButtonExecutar.setEnabled(False)
            return

        # Verifica se a camada tem geometria Z
        has_z_geometry = QgsWkbTypes.hasZ(layer.wkbType())

        # Verifica se há campos numéricos no comboBoxZ
        has_numeric_fields = self.comboBoxZ.count() > 0

        # Habilita o botão se pelo menos uma das condições for verdadeira
        if has_z_geometry or has_numeric_fields:
            self.pushButtonExecutar.setEnabled(True)
        else:
            self.pushButtonExecutar.setEnabled(False)

    def update_combo_box_z_state(self):
        """
        Atualiza o estado do comboBoxZ com base na seleção do checkBoxZ.
        - Se checkBoxZ estiver marcado, desativa o comboBoxZ.
        - Se checkBoxZ não estiver marcado, ativa o comboBoxZ.
        """
        is_checked = self.checkBoxZ.isChecked()
        self.comboBoxZ.setEnabled(not is_checked)

    def abrir_dialogo_rasterizar(self):
        """
        Chama o método run_rasterizarmalha do plugin principal para abrir o diálogo de Rasterização.
        """
        if hasattr(self.plugin, 'run_rasterizarmalha'):
            self.plugin.run_rasterizarmalha()
        else:
            self.mostrar_mensagem(self.tr("Não foi possível abrir o diálogo Rasterizar Malha."), "Erro")

    def update_rasterizar_button_state(self):
        """
        Atualiza o estado do botão pushButtonRasterizar.
        O botão será habilitado se existir pelo menos uma camada de malha (QgsMeshLayer) no projeto;
        caso contrário, ficará desativado.
        """
        mesh_exists = False
        for lyr in QgsProject.instance().mapLayers().values():
            if isinstance(lyr, QgsMeshLayer):
                mesh_exists = True
                break
        self.pushButtonRasterizar.setEnabled(mesh_exists)

    def closeEvent(self, event):
        # Em vez de fazer a limpeza completa, apenas oculta o diálogo
        self.hide()
        event.ignore()
