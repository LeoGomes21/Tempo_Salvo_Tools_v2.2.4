from qgis.core import QgsProject, QgsMapRendererCustomPainterJob, QgsMessageLog, QgsRasterLayer, QgsVectorLayer, QgsCoordinateReferenceSystem, QgsCoordinateTransform, QgsMapSettings, QgsColorRampShader, QgsRendererRange, QgsGraduatedSymbolRenderer, QgsFillSymbol, Qgis, QgsField, QgsPointXY, QgsRaster, QgsPoint, QgsFeature, QgsGeometry, QgsRectangle, QgsRasterBandStats
from qgis.PyQt.QtWidgets import QDialog, QCheckBox, QComboBox, QPushButton, QGraphicsView, QGraphicsScene, QGraphicsPixmapItem, QLineEdit, QMessageBox, QProgressBar, QApplication
from qgis.PyQt.QtGui import QImage, QPainter, QPixmap, QColor
from qgis.PyQt.QtCore import Qt, QRectF, QPointF, QSize, QVariant, QMetaType, QCoreApplication
from qgis.gui import QgsMapCanvas
from qgis.utils import iface
from qgis.PyQt import uic, sip
import time
import os

FORM_CLASS, _ = uic.loadUiType(os.path.join(
    os.path.dirname(__file__), 'ExtrairCotasMDT.ui'))

class CotasManager(QDialog, FORM_CLASS):
    def __init__(self, parent=None):
        """
        Inicializa a janela de extração de cotas de um raster.
        
        Parâmetros:
        - parent (opcional): O widget pai desta janela de diálogo, se houver.
        
        Funcionalidades:
        - Configura a interface do usuário (UI) criada no Designer.
        - Ajusta a janela e os campos de entrada com placeholders.
        - Conecta botões e sinais a funções.
        - Inicializa o ComboBox com as camadas raster do projeto atual.
        """
        super(CotasManager, self).__init__(parent)
        # Configura a interface do usuário a partir do Designer.
        self.setupUi(self)

        self.iface = iface

        # Altera o título da janela
        self.setWindowTitle(self.tr("Extrair Cotas de Raster"))

        # Cria uma cena gráfica para o QGraphicsView
        self.scene = QGraphicsScene()
        self.graphicsViewRaster.setScene(self.scene)

        self.lineEditSistemaReferencia.setPlaceholderText(self.tr("Sistema de referência:"))  # Texto de placeholder
        self.lineEditSistemaReferencia.setReadOnly(True)  # Campo somente leitura

        self.lineEditResolucao.setPlaceholderText(self.tr("Resolução do Pixel:"))  # Texto de placeholder
        self.lineEditResolucao.setReadOnly(True)  # Campo somente leitura

        self.lineEditQuantidade.setPlaceholderText(self.tr("Total de Pixel:"))  # Texto de placeholder
        self.lineEditQuantidade.setReadOnly(True)  # Campo somente leitura

        self.lineEditAreaRaster.setPlaceholderText(self.tr("Área do Raster:"))  # Texto de placeholder
        self.lineEditAreaRaster.setReadOnly(True) # Campo somente leitura

        # Conecta para executar a extração das cotas do Raster
        self.okButton.clicked.connect(self.extrair_cotas)

        self.cancelButton.clicked.connect(self.reject)  # Conecta o clique do botão à função reject

        # Inicializa o ComboBox de Raster
        self.init_combo_box_raster()

        # Conecta os sinais aos slots
        self.connect_signals()

    def tr(self, message):
        """
        Traduz textos deste diálogo.
        O contexto precisa ser estável para o Qt Linguist encontrar as traduções.
        """
        return QCoreApplication.translate("CotasManager", message)

    def limpar_informacoes_camada(self):
        """
        Limpa os campos de entrada relacionados às informações da camada raster (resolução, total de pixels e sistema de referência).

        Funcionalidades:
        - Limpa o texto exibido nos campos de entrada para resolução, total de pixels e sistema de referência.
        - Remove o estilo customizado dos campos de entrada, voltando ao padrão.

        Parâmetros:
        - Nenhum.

        Retorna:
        - None.
        """
        # Limpa o campo de texto da resolução do pixel e redefine o estilo
        self.lineEditResolucao.clear()  # Remove o texto da linha de edição de resolução
        self.lineEditResolucao.setStyleSheet("")  # Remove qualquer estilo aplicado (cor, bordas, etc.)

        # Limpa o campo de texto do total de pixels e redefine o estilo
        self.lineEditQuantidade.clear()  # Remove o texto da linha de edição do total de pixels
        self.lineEditQuantidade.setStyleSheet("")  # Remove qualquer estilo aplicado

        # Limpa o campo de texto do sistema de referência e redefine o estilo
        self.lineEditSistemaReferencia.clear()  # Remove o texto da linha de edição do sistema de referência
        self.lineEditSistemaReferencia.setStyleSheet("")  # Remove qualquer estilo aplicado

    def init_combo_box_raster(self):
        """
        Inicializa o ComboBox com as camadas raster disponíveis no projeto atual.

        Funcionalidades:
        - Obtém todas as camadas carregadas no projeto e filtra apenas as camadas raster.
        - Limpa o ComboBox e o preenche com os nomes e IDs das camadas raster.
        - Seleciona automaticamente a primeira camada raster disponível (se houver) e exibe a visualização da mesma.

        Parâmetros:
        - Nenhum.

        Retorna:
        - None.
        """
        # Obtém todas as camadas do projeto atual
        layers = QgsProject.instance().mapLayers().values()
        
        # Filtra apenas camadas raster
        raster_layers = [layer for layer in layers if layer.type() == layer.RasterLayer]
        
        # Limpa o ComboBox antes de adicionar itens
        self.comboBoxRaster.clear()
        
        # Adiciona as camadas raster ao ComboBox
        for raster_layer in raster_layers:
            self.comboBoxRaster.addItem(raster_layer.name(), raster_layer.id())

        # Seleciona a primeira camada raster, se existir
        if raster_layers:
            self.comboBoxRaster.setCurrentIndex(0) # Seleciona o primeiro item da lista no ComboBox
            self.display_raster() # Chama a função para exibir a visualização da camada selecionada

    def connect_signals(self):
        """
        Conecta os sinais de eventos da interface gráfica aos seus respectivos slots (funções) para gerenciar o comportamento
        da aplicação quando eventos específicos ocorrem.

        Funcionalidades:
        - Conecta a mudança de índice do ComboBox às funções de atualização da visualização raster.
        - Conecta os sinais de adição, remoção e alteração de camadas no projeto QGIS à atualização do ComboBox.
        - Conecta as mudanças de estado dos checkboxes à função que habilita ou desabilita o botão "OK".

        Parâmetros:
        - Nenhum.

        Retorna:
        - None.
        """
        # Conecta o evento de mudança de índice do ComboBox (quando o usuário escolhe outra camada) à função de exibir o raster correspondente
        self.comboBoxRaster.currentIndexChanged.connect(self.display_raster)

        # Conecta o sinal de remoção de camada ao método que atualiza o ComboBox
        QgsProject.instance().layersRemoved.connect(self.update_combo_box)

        # Conecta o sinal de adição de camada ao método que lida com a adição de novas camadas
        QgsProject.instance().layersAdded.connect(self.handle_layers_added)

        # Para cada camada no projeto, conecta o sinal de mudança de nome ao método que atualiza o ComboBox
        for layer in QgsProject.instance().mapLayers().values():
            layer.nameChanged.connect(self.update_combo_box)

        # Conecta o evento de mudança de índice do ComboBox novamente a uma função que atualiza informações específicas da camada raster
        self.comboBoxRaster.currentIndexChanged.connect(self.on_combo_box_raster_changed)

        # Conecta as mudanças de estado dos checkboxes (marcado/desmarcado) à função que verifica se o botão "OK" deve ser habilitado
        self.checkboxPontos.stateChanged.connect(self.verificar_estado_componentes_checkboxes)
        self.checkboxPoligonos.stateChanged.connect(self.verificar_estado_componentes_checkboxes)
        self.checkboxEstilizada.stateChanged.connect(self.verificar_estado_componentes_checkboxes)
        self.checkboxAtribuida.stateChanged.connect(self.verificar_estado_componentes_checkboxes)

    def update_combo_box(self):
        """
        Atualiza o ComboBox de camadas raster quando há mudanças no projeto, como adição, remoção ou renomeação de camadas.
        
        Funcionalidades:
        - Atualiza o ComboBox para refletir as camadas raster disponíveis no projeto.
        - Restaura a seleção anterior no ComboBox, se possível.
        - Caso a camada anteriormente selecionada tenha sido removida, seleciona a primeira camada disponível.

        Parâmetros:
        - Nenhum.

        Retorna:
        - None.
        """
        # Armazena o índice atual do ComboBox e o ID da camada selecionada para restaurar depois da atualização
        current_index = self.comboBoxRaster.currentIndex()  # Índice atual do ComboBox
        current_layer_id = self.comboBoxRaster.itemData(current_index)  # ID da camada raster atualmente selecionada

        # Atualiza o ComboBox com as camadas raster disponíveis (recarrega o ComboBox)
        self.init_combo_box_raster()

        # Tenta restaurar a seleção anterior com base no ID da camada
        if current_layer_id:
            index = self.comboBoxRaster.findData(current_layer_id)  # Encontra o índice do item que corresponde ao ID da camada anterior
            if index != -1:
                self.comboBoxRaster.setCurrentIndex(index)  # Se o índice for encontrado, restaura a seleção anterior
            else:
                # Se a camada anteriormente selecionada não existir mais, seleciona a primeira camada disponível no ComboBox
                if self.comboBoxRaster.count() > 0:
                    self.comboBoxRaster.setCurrentIndex(0)  # Seleciona o primeiro item do ComboBox
                    self.display_raster()  # Exibe o raster correspondente à nova seleção

    def display_raster(self):
        """
        Exibe a camada raster selecionada no QGraphicsView, renderizando uma visualização do raster.

        Funcionalidades:
        - Limpa a cena gráfica antes de adicionar um novo item.
        - Obtém o ID da camada raster selecionada no ComboBox.
        - Configura as definições de mapa e renderiza a camada raster como uma imagem.
        - Adiciona a imagem renderizada ao QGraphicsView e ajusta a visualização para manter a proporção.

        Parâmetros:
        - Nenhum.

        Retorna:
        - None.
        """
        # Limpa a cena antes de adicionar um novo item
        self.scene.clear()  # Remove todos os itens da cena atual

        # Obtém o ID da camada raster selecionada no ComboBox
        selected_raster_id = self.comboBoxRaster.currentData()  # Coleta o ID da camada raster selecionada

        # Busca a camada raster no projeto pelo seu ID
        selected_layer = QgsProject.instance().mapLayer(selected_raster_id)  # Localiza a camada raster no projeto

        # Verifica se a camada selecionada é uma camada raster
        if isinstance(selected_layer, QgsRasterLayer):
            # Define as informações da camada e verifica o estado dos checkboxes
            self.set_informacoes_camada(selected_layer)

            # Configura as definições do mapa
            map_settings = QgsMapSettings()  # Cria uma instância de QgsMapSettings para configurar a renderização do mapa
            map_settings.setLayers([selected_layer])  # Define a camada raster como a única camada a ser renderizada
            map_settings.setBackgroundColor(QColor(255, 255, 255))  # Define a cor de fundo como branco

            # Define o tamanho da imagem a ser renderizada com base no tamanho da área de visualização (QGraphicsView)
            width = self.graphicsViewRaster.viewport().width()  # Largura da área de visualização
            height = self.graphicsViewRaster.viewport().height()  # Altura da área de visualização
            map_settings.setOutputSize(QSize(width, height))  # Define o tamanho da imagem a ser gerada

            # Define a extensão do mapa para corresponder à extensão da camada raster
            map_settings.setExtent(selected_layer.extent())  # Ajusta a extensão da visualização para cobrir a área do raster

            # Cria uma imagem transparente para renderizar o raster
            image = QImage(width, height, QImage.Format.Format_ARGB32)  # Cria uma imagem no formato ARGB (com transparência)
            image.fill(Qt.GlobalColor.transparent)  # Preenche a imagem com transparência

            # Configura o pintor (QPainter) para renderizar a imagem
            painter = QPainter(image)  # Cria um pintor para desenhar na imagem
            render_job = QgsMapRendererCustomPainterJob(map_settings, painter)  # Define um trabalho de renderização personalizado

            # Executa o trabalho de renderização
            render_job.start()  # Inicia a renderização da imagem
            render_job.waitForFinished()  # Aguarda a conclusão da renderização
            painter.end()  # Finaliza o pintor

            # Cria um QPixmap a partir da imagem renderizada
            pixmap = QPixmap.fromImage(image)  # Converte a imagem renderizada para um QPixmap
            pixmap_item = QGraphicsPixmapItem(pixmap)  # Cria um item gráfico para o pixmap

            # Adiciona o item à cena gráfica
            self.scene.addItem(pixmap_item)  # Insere o pixmap na cena do QGraphicsView

            # Ajusta a cena ao QGraphicsView, garantindo que a proporção seja preservada
            self.graphicsViewRaster.setSceneRect(pixmap_item.boundingRect())  # Define os limites da cena com base no tamanho do pixmap
            self.graphicsViewRaster.fitInView(self.scene.sceneRect(), Qt.AspectRatioMode.KeepAspectRatio)  # Ajusta a visualização para manter a proporção da imagem

    def showEvent(self, event):
        """
        Evento chamado quando a janela de diálogo é mostrada.
        
        Funcionalidades:
        - Reseta os componentes do diálogo para o estado inicial.
        - Ajusta a visualização do raster selecionado no QGraphicsView.
        - Verifica o estado inicial dos checkboxes e do botão "OK".
        - Atualiza as informações da camada selecionada no ComboBox.

        Parâmetros:
        - event: O evento de exibição da janela, do tipo QShowEvent.

        Retorna:
        - None.
        """
        # Chama o método da classe base (QDialog) para garantir que o evento seja tratado corretamente
        super(CotasManager, self).showEvent(event)

        # Reseta os componentes (checkboxes, campos de texto, etc.) ao mostrar o diálogo
        self.resetar_componentes()

        # Ajusta a visualização do raster quando o diálogo é mostrado
        self.display_raster()

        # Verifica o estado inicial dos checkboxes e habilita/desabilita componentes conforme necessário
        self.verificar_estado_inicial()

        # Atualiza as informações da camada selecionada no ComboBox, garantindo que os dados estejam corretos
        self.on_combo_box_raster_changed()

    def handle_layers_added(self, layers):
        """
        Atualiza o ComboBox somente quando uma camada raster é adicionada.
        Camadas vetoriais criadas pela própria ferramenta não precisam
        provocar nova renderização da pré-visualização.
        """
        if not layers:
            return

        possui_raster = any(
            isinstance(layer, QgsRasterLayer)
            for layer in layers)

        if not possui_raster:
            return

        self.update_combo_box()

    def closeEvent(self, event):
        """
        Evento chamado quando a janela de diálogo é fechada.

        Funcionalidades:
        - Define a variável `cotas_dlg` do pai (se existir) como `None`, indicando que o diálogo foi fechado.
        - Chama o método `closeEvent` da classe base para garantir o fechamento adequado da janela.

        Parâmetros:
        - event: O evento de fechamento da janela, do tipo QCloseEvent.

        Retorna:
        - None.
        """
        # Obtém o widget pai do diálogo
        parent = self.parent()  # Obtém o pai (se existir)

        # Se o pai existir, define o atributo cotas_dlg do pai como None
        if parent:
            parent.cotas_dlg = None  # Sinaliza que o diálogo de cotas foi fechado

        # Chama o método closeEvent da classe base (QDialog) para continuar o processo padrão de fechamento
        super(CotasManager, self).closeEvent(event)

    def mostrar_mensagem(self, texto, tipo, duracao=3):
        """
        Exibe uma mensagem na barra de mensagens da interface do QGIS, proporcionando feedback ao usuário.

        Funcionalidades:
        - Exibe uma mensagem de erro ou sucesso na barra de mensagens com um nível e duração apropriados.
        - A mensagem pode ser de dois tipos: "Erro" (nível crítico) ou "Sucesso" (nível informativo).
        - O tempo de exibição da mensagem pode ser ajustado.

        Parâmetros:
        - texto: O texto da mensagem a ser exibida.
        - tipo: O tipo da mensagem ("Erro" ou "Sucesso") que determina o estilo e ícone da mensagem.
        - duracao: Duração em segundos durante a qual a mensagem será exibida (padrão é 3 segundos).

        Retorna:
        - None.
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
        progressMessageBar = self.iface.messageBar().createMessage(self.tr("Extraindo cotas do Raster"))
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

    def set_informacoes_camada(self, layer):
        """
        Define a camada e verifica os checkboxes.

        Passos detalhados:
        1. Define a camada selecionada como um atributo da instância.

        Parâmetros:
        - layer: Camada selecionada.
        """
        self.layer = layer  # Define a camada selecionada como um atributo da instância

        # Conectar o sinal de mudança de renderização à função display_raster
        self.layer.rendererChanged.connect(self.display_raster)

    def atualizar_informacoes_camada(self):
        """
        Atualiza as informações da camada raster selecionada, como resolução do pixel, total de pixels e sistema de referência.
        
        Funcionalidades:
        - Verifica se a camada é válida e se tem dimensões adequadas.
        - Calcula a resolução do pixel em X e Y.
        - Verifica se a camada está em coordenadas geográficas e realiza transformações, se necessário.
        - Atualiza os campos de texto na interface com a resolução do pixel, total de pixels e sistema de referência.

        Parâmetros:
        - Nenhum.

        Retorna:
        - None.
        """
        if not self.layer:
            return  # Ou mostre uma mensagem de erro para o usuário

        provider = self.layer.dataProvider()  # Obtém o provedor de dados da camada
        extent = self.layer.extent()  # Obtém a extensão da camada
        width = provider.xSize()  # Calcula a largura da camada raster em pixels
        height = provider.ySize()  # Calcula a altura da camada raster em pixels

        # Chama a função para habilitar ou desabilitar checkboxes e botão "OK"
        self.verificar_estado_componentes(width, height)

        if width == 0 or height == 0:
            return  # Sai da função, já que a camada é inválida

        # Verifica se a camada está em coordenadas geográficas
        if self.layer.crs().isGeographic():
            # Cria uma transformação de coordenadas para um sistema de coordenadas projetadas (por exemplo, UTM)
            target_crs = QgsCoordinateReferenceSystem(3857)  # EPSG:3857 - Pseudo-Mercator
            transform = QgsCoordinateTransform(self.layer.crs(), target_crs, QgsProject.instance())
            transformed_extent = transform.transformBoundingBox(extent)
            pixelSizeX = transformed_extent.width() / width  # Calcula a resolução do pixel em X
            pixelSizeY = transformed_extent.height() / height  # Calcula a resolução do pixel em Y
        else:
            pixelSizeX = extent.width() / width  # Calcula a resolução do pixel em X
            pixelSizeY = extent.height() / height  # Calcula a resolução do pixel em Y

        # Atualiza o campo de texto da resolução do pixel
        self.lineEditResolucao.setText(f"{pixelSizeX:.3f} x {pixelSizeY:.3f} Pixels")
        self.lineEditResolucao.setStyleSheet("color: green;")  # Define a cor do texto como verde

        # Atualiza o campo de texto do total de pixels
        self.lineEditQuantidade.setText(f"{width * height} Pixels")
        self.lineEditQuantidade.setStyleSheet("color: red;")  # Define a cor do texto como vermelho

        crs = self.layer.crs()  # Obtém o sistema de referência da camada
        crs_description = f"{crs.authid()} - {crs.description()}"  # Obtém a descrição completa do sistema de referência
        # Atualiza o campo de texto do sistema de referência
        self.lineEditSistemaReferencia.setText(crs_description)
        self.lineEditSistemaReferencia.setStyleSheet("color: blue;")  # Define a cor do texto como azul

        # Calcular e exibir a área do raster e área apenas p/ rasters locais
        provider      = self.layer.dataProvider()
        provider_key  = self.layer.providerType().lower()      # ex.: 'gdal', 'wms', 'xyz'
        remote_keys   = {'wms', 'wcs', 'xyz', 'arcgismapserver', 'arcgisrest'}

        if provider_key in remote_keys:
            # Camada de serviço → não calcula área
            self.lineEditAreaRaster.setText(self.tr("Área Raster: N/A (camada de serviço)"))
            self.lineEditAreaRaster.setStyleSheet("color: magenta;")
            return                 # sai, deixando os demais campos já atualizados

        # Se chegou aqui é um raster local → calcula área apenas de células válidas
        width, height = provider.xSize(), provider.ySize()

        # 1) Número de células válidas (ignora NoData)
        stats = provider.bandStatistics(
            1,  # banda
            QgsRasterBandStats.Stats.All,  # calcula todas as estatísticas (inclusive contagem)
            self.layer.extent())
        valid_cells = stats.elementCount

        # 2) Área de um pixel em m²
        crs = self.layer.crs()
        if crs.isGeographic():
            tr = QgsCoordinateTransform(
                crs, QgsCoordinateReferenceSystem("EPSG:3857"), QgsProject.instance())
            ext_proj   = tr.transformBoundingBox(self.layer.extent())
            pixel_area = (ext_proj.width() / width) * (ext_proj.height() / height)
        else:
            pixel_area = (self.layer.extent().width()  / width * self.layer.extent().height() / height)

        # 3) Área total apenas das células válidas
        area_valid_m2 = valid_cells * pixel_area

        # 4) Exibe resultado
        self.lineEditAreaRaster.setText(self.tr("Área Raster: {area_valid_m2:,.2f} m²").format(area_valid_m2=area_valid_m2))
        self.lineEditAreaRaster.setStyleSheet("color: magenta;")

    def verificar_estado_componentes(self, width, height):
        """
        Verifica o estado da camada selecionada e habilita ou desabilita os checkboxes e o botão "OK"
        com base no tamanho da camada raster (width e height).

        Funcionalidades:
        - Se a camada tiver tamanho inválido (width ou height = 0), limpa os campos de texto e desabilita os checkboxes e o botão "OK".
        - Se a camada for válida, habilita os checkboxes e controla o botão "OK" com base no estado dos checkboxes.

        Parâmetros:
        - width: Largura da camada raster em pixels.
        - height: Altura da camada raster em pixels.

        Retorna:
        - None.
        """
        # Verifica se a largura ou altura da camada é 0 (camada inválida)
        if width == 0 or height == 0:
            # Limpa os campos de texto e remove qualquer estilo customizado
            self.lineEditResolucao.clear()  # Limpa o campo de resolução de pixel
            self.lineEditResolucao.setStyleSheet("")  # Remove o estilo customizado do campo de resolução
            self.lineEditQuantidade.clear()  # Limpa o campo de quantidade de pixels
            self.lineEditQuantidade.setStyleSheet("")  # Remove o estilo customizado do campo de quantidade
            self.lineEditSistemaReferencia.clear()  # Limpa o campo do sistema de referência
            self.lineEditSistemaReferencia.setStyleSheet("")  # Remove o estilo customizado do campo de sistema de referência
            self.lineEditAreaRaster.clear()
            self.lineEditAreaRaster.setStyleSheet("")

            # Desativa os checkboxes e desmarca todos
            self.checkboxPontos.setChecked(False)  # Desmarca o checkbox de pontos
            self.checkboxPoligonos.setChecked(False)  # Desmarca o checkbox de polígonos
            self.checkboxEstilizada.setChecked(False)  # Desmarca o checkbox de estilo
            self.checkboxAtribuida.setChecked(False)  # Desmarca o checkbox de atribuição
            self.checkboxPontos.setEnabled(False)  # Desativa o checkbox de pontos
            self.checkboxPoligonos.setEnabled(False)  # Desativa o checkbox de polígonos
            self.checkboxEstilizada.setEnabled(False)  # Desativa o checkbox de estilo
            self.checkboxAtribuida.setEnabled(False)  # Desativa o checkbox de atribuição

            # Desativa o botão "OK"
            self.okButton.setEnabled(False)  # Desativa o botão "OK"
        
        else:
            # Habilita todos os checkboxes, já que a camada é válida
            self.checkboxPontos.setEnabled(True)  # Habilita o checkbox de pontos
            self.checkboxPoligonos.setEnabled(True)  # Habilita o checkbox de polígonos
            self.checkboxEstilizada.setEnabled(True)  # Habilita o checkbox de estilo
            self.checkboxAtribuida.setEnabled(True)  # Habilita o checkbox de atribuição

            # Ativa o botão "OK" apenas se pelo menos um checkbox estiver marcado
            if (self.checkboxPontos.isChecked() or 
                self.checkboxPoligonos.isChecked() or 
                self.checkboxEstilizada.isChecked() or 
                self.checkboxAtribuida.isChecked()):
                self.okButton.setEnabled(True)  # Ativa o botão "OK" se algum checkbox estiver marcado
            else:
                self.okButton.setEnabled(False)  # Desativa o botão "OK" se nenhum checkbox estiver marcado

    def verificar_estado_componentes_checkboxes(self):
        """
        Verifica se pelo menos um checkbox está marcado para ativar o botão "OK".
        
        Funcionalidades:
        - Ativa o botão "OK" se qualquer um dos checkboxes estiver marcado.
        - Desativa o botão "OK" se nenhum checkbox estiver marcado.
        
        Este método deve ser chamado sempre que o estado de um checkbox mudar, 
        para garantir que o botão "OK" só esteja ativo quando há uma opção selecionada.

        Parâmetros:
        - Nenhum.

        Retorna:
        - None.
        """
        # Verifica se pelo menos um dos checkboxes está marcado
        if (self.checkboxPontos.isChecked() or  # Verifica se o checkbox de pontos está marcado
            self.checkboxPoligonos.isChecked() or  # Verifica se o checkbox de polígonos está marcado
            self.checkboxEstilizada.isChecked() or  # Verifica se o checkbox de estilização está marcado
            self.checkboxAtribuida.isChecked()):  # Verifica se o checkbox de atribuição está marcado
            self.okButton.setEnabled(True)  # Ativa o botão "OK" se qualquer um dos checkboxes estiver marcado
        else:
            self.okButton.setEnabled(False)  # Desativa o botão "OK" se nenhum checkbox estiver marcado

    def on_combo_box_raster_changed(self):
        """
        Atualiza a camada raster selecionada e suas informações associadas quando o ComboBox é alterado.
        
        Funcionalidades:
        - Obtém a camada raster selecionada com base no ID atual do ComboBox.
        - Atualiza as informações associadas à camada (como resolução, sistema de referência, etc.).
        
        Este método é chamado sempre que o usuário seleciona uma nova camada raster no ComboBox.

        Parâmetros:
        - Nenhum.

        Retorna:
        - None.
        """
        # Obtém o ID da camada raster atualmente selecionada no ComboBox
        selected_layer_id = self.comboBoxRaster.currentData()  # Coleta o ID da camada selecionada no ComboBox

        # Atualiza a camada selecionada no projeto com base no ID
        self.layer = QgsProject.instance().mapLayer(selected_layer_id)  # Obtém a camada raster associada ao ID no projeto

        # Atualiza as informações associadas à camada selecionada (resolução, total de pixels, sistema de referência, etc.)
        self.atualizar_informacoes_camada()  # Chama o método para atualizar as informações da camada

    def verificar_estado_inicial(self):
        """
        Verifica o estado inicial da camada selecionada no diálogo e ajusta os componentes (checkboxes e botão "OK").

        Funcionalidades:
        - Obtém a camada raster selecionada no ComboBox ao iniciar o diálogo.
        - Verifica as dimensões da camada (largura e altura).
        - Habilita ou desabilita os checkboxes e o botão "OK" com base nas dimensões da camada.
        - Se não houver camada selecionada, desativa os componentes.

        Parâmetros:
        - Nenhum.

        Retorna:
        - None.
        """
        # Obtém o ID da camada raster selecionada no ComboBox
        selected_layer_id = self.comboBoxRaster.currentData()  # Coleta o ID da camada selecionada no ComboBox

        # Obtém a camada raster associada ao ID selecionado
        self.layer = QgsProject.instance().mapLayer(selected_layer_id)  # Carrega a camada raster no projeto com base no ID

        # Verifica se a camada existe
        if self.layer:
            # Obtém o provedor de dados da camada
            provider = self.layer.dataProvider()  # Coleta o provedor de dados da camada raster

            # Obtém a largura e altura da camada raster em pixels
            width = provider.xSize()  # Obtém a largura em pixels da camada raster
            height = provider.ySize()  # Obtém a altura em pixels da camada raster

            # Habilita ou desabilita os checkboxes e o botão "OK" com base nas dimensões da camada
            self.verificar_estado_componentes(width, height)  # Chama a função para verificar o estado dos componentes
        else:
            # Se não houver uma camada selecionada, desativa todos os componentes
            self.verificar_estado_componentes(0, 0)  # Passa dimensões 0 para desativar os componentes

    def resetar_componentes(self):
        """
        Reseta o estado dos checkboxes e do botão "OK" ao abrir o diálogo.
        
        Funcionalidades:
        - Desmarca todos os checkboxes.
        - Desativa todos os checkboxes.
        - Desativa o botão "OK".
        
        Esse método é útil para garantir que, ao abrir o diálogo, os componentes estejam em seu estado inicial.

        Parâmetros:
        - Nenhum.

        Retorna:
        - None.
        """
        # Desmarca todos os checkboxes
        self.checkboxPontos.setChecked(False)  # Desmarca o checkbox de pontos
        self.checkboxPoligonos.setChecked(False)  # Desmarca o checkbox de polígonos
        self.checkboxEstilizada.setChecked(False)  # Desmarca o checkbox de estilo
        self.checkboxAtribuida.setChecked(False)  # Desmarca o checkbox de atribuição

        # Desativa todos os checkboxes
        self.checkboxPontos.setEnabled(False)  # Desativa o checkbox de pontos
        self.checkboxPoligonos.setEnabled(False)  # Desativa o checkbox de polígonos
        self.checkboxEstilizada.setEnabled(False)  # Desativa o checkbox de estilo
        self.checkboxAtribuida.setEnabled(False)  # Desativa o checkbox de atribuição

        # Desativa o botão "OK"
        self.okButton.setEnabled(False)  # Desativa o botão "OK"

    def aplicar_estilo_poligono(self, camada_poligono, colormap):
        """
        Aplica um estilo graduado a uma camada de polígonos com base em uma colormap.

        Passos detalhados:
        1. Cria uma lista para armazenar os intervalos de renderização.
        2. Itera sobre os itens da colormap para criar símbolos e intervalos de renderização.
        3. Adiciona o primeiro intervalo com valor mínimo infinito.
        4. Adiciona os intervalos subsequentes com base nos valores anteriores e atuais.
        5. Remove o intervalo adicional de infinito, se presente.
        6. Cria um renderizador graduado com base nos intervalos de valores e aplica à camada de polígonos.

        Parâmetros:
        - camada_poligono: Camada de polígonos a ser estilizada.
        - colormap: Lista de itens da colormap contendo valores e cores.

        Retorna:
        - None
        """
        ranges = []  # Lista para armazenar os intervalos de renderização

        for i in range(len(colormap)):  # Itera sobre os itens da colormap
            item = colormap[i]  # Obtém o item atual da colormap
            if i == 0:
                # Primeiro intervalo
                symbol = QgsFillSymbol.createSimple({'color': item.color.name(), 'outline_color': item.color.name()})  # Cria um símbolo de preenchimento
                renderer_range = QgsRendererRange(float('-inf'), item.value, symbol, f"<= {item.value:.3f}")  # Cria um intervalo de renderização
            else:
                prev_item = colormap[i - 1]  # Obtém o item anterior da colormap
                symbol = QgsFillSymbol.createSimple({'color': item.color.name(), 'outline_color': item.color.name()})  # Cria um símbolo de preenchimento
                renderer_range = QgsRendererRange(prev_item.value, item.value, symbol, f"{prev_item.value:.3f} - {item.value:.3f}")  # Cria um intervalo de renderização

            ranges.append(renderer_range)  # Adiciona o intervalo de renderização à lista

        # Remover o intervalo adicional de "inf"
        if len(ranges) > 1 and ranges[-1].upperValue == float('inf'):  # Verifica se há um intervalo adicional de infinito
            ranges.pop()  # Remove o intervalo adicional

        renderer = QgsGraduatedSymbolRenderer('Value', ranges)  # Cria um renderizador graduado com base nos intervalos de valores
        camada_poligono.setRenderer(renderer)  # Aplica o renderizador à camada de polígonos

    def gerar_colormap_cinza(self, min_value, max_value, num_graduacoes=10):
        """
        Gera uma colormap em escala de cinza para um intervalo de valores.

        Passos detalhados:
        1. Inicializa uma lista para armazenar os itens da colormap.
        2. Calcula o tamanho do passo entre cada graduação de valor.
        3. Itera sobre o número de graduações para gerar valores e cores em escala de cinza.
        4. Cria itens da colormap com valores e cores correspondentes.
        5. Adiciona um item final para cobrir valores maiores que o valor máximo, com cor cinza clara.
        6. Retorna a lista de itens da colormap.

        Parâmetros:
        - min_value: Valor mínimo do intervalo.
        - max_value: Valor máximo do intervalo.
        - num_graduacoes: Número de graduações na colormap (padrão é 10).

        Retorna:
        - colormap: Lista de itens da colormap em escala de cinza.
        """
        colormap = []  # Inicializa a lista para armazenar os itens da colormap
        step = (max_value - min_value) / (num_graduacoes - 1)  # Calcula o tamanho do passo entre cada graduação de valor
        for i in range(num_graduacoes):  # Itera sobre o número de graduações
            value = min_value + i * step  # Calcula o valor atual
            gray_value = int(255 * (i / (num_graduacoes - 1)))  # Valor em escala de cinza entre 0 e 255
            color = QColor(gray_value, gray_value, gray_value)  # Cria a cor correspondente em escala de cinza
            colormap.append(QgsColorRampShader.ColorRampItem(value, color))  # Adiciona o item à colormap

        # Adicionar um último item para cobrir valores maiores que o valor máximo
        gray_value = 240  # Última cor em escala de cinza (totalmente branca)
        color = QColor(gray_value, gray_value, gray_value)  # Cria a cor cinza clara
        colormap[-1] = QgsColorRampShader.ColorRampItem(max_value, color)  # Substitui o último item na colormap

        return colormap  # Retorna a lista de itens da colormap

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
        ranges.append(QgsRendererRange(0.0001, float('inf'), symbol_positive, "> 0"))  # Intervalo para pixels positivos
        ranges.append(QgsRendererRange(float('-inf'), -0.0001, symbol_negative, "< 0"))  # Intervalo para pixels negativos
        ranges.append(QgsRendererRange(-0.0001, 0.0001, symbol_zero, "= 0"))  # Intervalo para pixels nulos

        renderer = QgsGraduatedSymbolRenderer('Value', ranges)  # Cria um renderizador graduado com base nos intervalos de valores
        camada_poligono.setRenderer(renderer)  # Aplica o renderizador à camada de polígonos

    def criar_camadas_poligonos_unicas(self, raster_layer):
        """
        Cria uma camada de polígonos única com um nome exclusivo, adicionando sufixos numéricos, se necessário.

        Parâmetros:
        - raster_layer: A camada raster de origem para criar a camada de polígonos.

        Retorna:
        - A camada de polígonos criada.
        """
        # Base do nome da camada
        base_name = raster_layer.name() + "_Poligonos"
        layer_name = base_name

        # Verificar se uma camada com o mesmo nome já existe
        layers = QgsProject.instance().mapLayersByName(layer_name)
        count = 1
        while layers:
            layer_name = f"{base_name}_{count}"
            layers = QgsProject.instance().mapLayersByName(layer_name)
            count += 1

        # Criar a camada de polígonos com um nome exclusivo
        camada_poligono = QgsVectorLayer(f"Polygon?crs={raster_layer.crs().authid()}", layer_name, "memory")
        return camada_poligono

    def processar_cotas_poligonos(self, raster_layer, estilizar=False, atribuir=False):
        """
        Processa uma camada raster para extrair cotas em polígonos e cria uma camada de polígonos no QGIS,
        utilizando leitura em bloco para maior desempenho.

        Passos detalhados:
        1. Captura o tempo de início do processo.
        2. Obtém o provedor de dados, extensão e dimensões do raster.
        3. Cria uma camada de polígonos temporária ("memory") com campos "ID" e "Value".
        4. Calcula o tamanho do pixel (resolução em X e Y).
        5. Cria e exibe a barra de progresso.
        6. Lê todos os valores da banda do raster de uma só vez usando block(), armazenando-os em um QgsRasterBlock.
        7. Para cada pixel do raster:
            a. Atualiza a barra de progresso a cada 1000 pixels.
            b. Obtém o valor do pixel a partir do bloco.
            c. Ignora pixels nulos (NoData ou NaN).
            d. Calcula os limites do pixel (xmin, xmax, ymin, ymax).
            e. Cria um polígono (retângulo) correspondente ao pixel.
            f. Cria a feature, atribui ID e valor do pixel, e armazena numa lista.
            g. Adiciona o valor do pixel na lista para possíveis graduações.
        8. Adiciona todas as features à camada de uma só vez.
        9. Adiciona a camada de polígonos ao projeto QGIS.
        10. Obtém ou gera a colormap, e aplica o estilo graduado se solicitado.
        11. Aplica estilo de atribuição se solicitado.
        12. Atualiza a barra de progresso para 100%.
        13. Calcula e exibe o tempo total de execução.
        14. Remove a barra de progresso da interface.
        """
        start_time = time.time()  # 1. Tempo de início

        # 2. Informações do raster
        provider = raster_layer.dataProvider()
        extent = provider.extent()
        width = provider.xSize()
        height = provider.ySize()
        band = 1

        # 3. Cria camada de polígonos com nome único e campos
        camada_poligono = self.criar_camadas_poligonos_unicas(raster_layer)
        pr = camada_poligono.dataProvider()
        pr.addAttributes([QgsField("ID", QMetaType.Type.Int), QgsField("Value", QMetaType.Type.Double)])
        camada_poligono.updateFields()

        # 4. Resolução do pixel
        pixelSizeX = extent.width() / width
        pixelSizeY = extent.height() / height

        # 5. Barra de progresso
        total_steps = width * height
        progress_bar, progress_message_bar = self.iniciar_progress_bar(total_steps)

        # 6. Lê bloco inteiro do raster
        raster_block = provider.block(band, extent, width, height)

        features = []
        valores_pixel = []
        id_count = 0
        update_interval = 1000

        # 7. Loop para todos os pixels
        for row in range(height):
            for col in range(width):
                id_count += 1

                # 7a. Atualiza barra de progresso periodicamente
                if id_count % update_interval == 0:
                    progress_bar.setValue(id_count)

                # 7b. Valor do pixel a partir do bloco
                valor_pixel = raster_block.value(row, col)
                if valor_pixel is None or valor_pixel != valor_pixel:  # 7c. Ignora NoData/NaN
                    continue

                # 7d. Limites do pixel (retângulo)
                xMin = extent.xMinimum() + col * pixelSizeX
                xMax = extent.xMinimum() + (col + 1) * pixelSizeX
                yMax = extent.yMaximum() - row * pixelSizeY
                yMin = extent.yMaximum() - (row + 1) * pixelSizeY

                # 7e. Cria polígono retângulo do pixel
                poligono = QgsGeometry.fromRect(QgsRectangle(xMin, yMin, xMax, yMax))

                # 7f. Cria feature, define geometria e atributos
                feature = QgsFeature()
                feature.setGeometry(poligono)
                feature.setAttributes([id_count, valor_pixel])
                features.append(feature)

                # 7g. Armazena valor do pixel
                valores_pixel.append(valor_pixel)

        # 8. Adiciona todas features de uma só vez
        pr.addFeatures(features)
        camada_poligono.updateExtents()

        # 9. Adiciona camada ao projeto
        QgsProject.instance().addMapLayer(camada_poligono)

        # 10. Obtém ou gera colormap e aplica estilo graduado se necessário
        renderer = raster_layer.renderer()
        colormap = []
        if hasattr(renderer, 'shader'):
            shader = renderer.shader()
            color_ramp_shader = shader.rasterShaderFunction()
            if isinstance(color_ramp_shader, QgsColorRampShader):
                colormap = color_ramp_shader.colorRampItemList()

        # Gera colormap cinza se necessário
        if estilizar and not colormap and valores_pixel:
            min_value = min(valores_pixel)
            max_value = max(valores_pixel)
            colormap = self.gerar_colormap_cinza(min_value, max_value, 10)

        # 11. Aplica estilos, se solicitado
        if estilizar and colormap:
            self.aplicar_estilo_poligono(camada_poligono, colormap)
        if atribuir:
            self.aplicar_estilo_atribuido(camada_poligono)

        # 12. Atualiza barra de progresso para 100%
        progress_bar.setValue(total_steps)

        # 13. Tempo de execução
        execution_time = time.time() - start_time

        # 14. Limpa barra de progresso e exibe mensagem de sucesso
        self.iface.messageBar().clearWidgets()
        self.mostrar_mensagem(self.tr("Camada de Polígonos Criada com sucesso em {execution_time:.2f} segundos.").format(execution_time=execution_time), "Sucesso")

    def processar_cotas_pontos(self, raster_layer):
        """
        Processa uma camada raster para extrair cotas em pontos e cria uma camada de pontos no QGIS
        de forma otimizada usando leitura em bloco (block).

        Passos detalhados do processo:
        1. Captura o tempo de início para medir o desempenho da extração.
        2. Obtém o SRC (Sistema de Referência de Coordenadas) da camada raster.
        3. Cria uma camada de pontos temporária ("memory") com geometria 3D (PointZ) e adiciona os campos:
            - ID: identificador sequencial para cada ponto.
            - X: coordenada X do ponto.
            - Y: coordenada Y do ponto.
            - Z: valor da cota (elevação) extraída do raster.
        4. Obtém as informações do raster:
            - Provedor de dados.
            - Extensão espacial (extent).
            - Dimensões (largura e altura em pixels).
            - Banda a ser processada (normalmente banda 1 para MDT).
        5. Calcula a resolução do pixel em X e Y.
        6. Cria e exibe uma barra de progresso para o usuário acompanhar o andamento da extração.
        7. Lê todos os valores da banda do raster de uma só vez usando o método block(), armazenando os valores em uma matriz (QgsRasterBlock).
        8. Percorre todos os pixels do raster (duplo loop: linha e coluna):
            a. Atualiza a barra de progresso a cada 1000 pixels.
            b. Obtém o valor do pixel diretamente do bloco (z).
            c. Ignora valores nulos (NoData ou NaN).
            d. Calcula a coordenada do centro do pixel (x, y).
            e. Cria uma feature (ponto 3D) para cada pixel válido e atribui os valores de ID, X, Y, Z.
            f. Armazena todas as features em uma lista.
        9. Adiciona todas as features de uma vez na camada de pontos (mais eficiente).
        10. Atualiza a extensão da camada de pontos.
        11. Adiciona a camada ao projeto QGIS.
        12. Atualiza a barra de progresso para 100% ao final.
        13. Calcula e exibe o tempo total de execução do processo ao usuário.
        14. Remove a barra de progresso da interface.

        Retorna:
        - None
        """
        start_time = time.time()  # 1. Captura o tempo de início

        self._cancelar_extracao_pontos = False
        self._finalizando_extracao_pontos = False

        # 2. Obtém o SRC do raster
        raster_crs = raster_layer.crs().authid()

        # 3. Cria a camada de pontos e adiciona campos
        camada_pontos = QgsVectorLayer(
            f"PointZ?crs={raster_layer.crs().authid()}",
            raster_layer.name() + self.tr("_Pontos"),
            "memory")
        pr = camada_pontos.dataProvider()
        pr.addAttributes([
            QgsField("ID", QMetaType.Type.Int),
            QgsField("X", QMetaType.Type.Double),
            QgsField("Y", QMetaType.Type.Double),
            QgsField("Z", QMetaType.Type.Double)])

        camada_pontos.updateFields()

        # 4. Informações do raster
        provider = raster_layer.dataProvider()
        extent = raster_layer.extent()
        width = provider.xSize()
        height = provider.ySize()
        band = 1  # Banda 1

        # 5. Resolução dos pixels
        xres = extent.width() / width
        yres = extent.height() / height

        # 6. Barra de progresso
        total_steps = width * height
        progress_bar, progress_message_bar = self.iniciar_progress_bar(total_steps)

        progress_message_bar.destroyed.connect(lambda: setattr(self, "_cancelar_extracao_pontos",
                not self._finalizando_extracao_pontos))

        # 7. Leitura em bloco
        raster_block = provider.block(band, extent, width, height)

        features = []
        id_count = 0
        feature_id = 0
        update_interval = 1000
        batch_size = 10000

        # 8. Loop de extração dos pontos
        for row in range(height):
            for col in range(width):
                id_count += 1

                if id_count % update_interval == 0:
                    QApplication.processEvents()

                    # Se o usuário fechou a barra pelo X, aborta a extração
                    if self._cancelar_extracao_pontos:
                        features.clear()
                        return

                    if progress_bar is not None and not sip.isdeleted(progress_bar):
                        progress_bar.setValue(id_count)

                # Ignora corretamente pixels NoData
                if raster_block.isNoData(row, col):
                    continue

                z = raster_block.value(row, col)

                if z is None or z != z:
                    continue

                x = extent.xMinimum() + xres * (col + 0.5)
                y = extent.yMaximum() - yres * (row + 0.5)

                feature_id += 1

                feature = QgsFeature(camada_pontos.fields())
                feature.setGeometry(QgsGeometry(QgsPoint(x, y, z)))
                feature.setAttributes([
                    feature_id,
                    round(x, 3),
                    round(y, 3),
                    round(z, 5)])

                features.append(feature)

                # Grava em lotes para não acumular milhões de features na memória
                if len(features) >= batch_size:
                    pr.addFeatures(features)
                    features.clear()

        if features:
            pr.addFeatures(features)
            features.clear()

        QApplication.processEvents()

        if self._cancelar_extracao_pontos:
            return

        # 10. Atualiza extensão da camada
        camada_pontos.updateExtents()

        # A extração terminou
        if progress_bar is not None and not sip.isdeleted(progress_bar):
            progress_bar.setValue(total_steps)

        QApplication.processEvents()

        if self._cancelar_extracao_pontos:
            return

        execution_time = time.time() - start_time

        # A partir daqui o fechamento da barra é normal, não é cancelamento
        self._finalizando_extracao_pontos = True

        self.iface.messageBar().clearWidgets()
        QApplication.processEvents()

        # Adiciona ao projeto sem inserir automaticamente na legenda/canvas
        project = QgsProject.instance()

        # Registra a camada sem disparar todos os slots conectados a layersAdded
        estado_sinais = project.blockSignals(True)

        try:
            project.addMapLayer(camada_pontos, False)
        finally:
            project.blockSignals(estado_sinais)

        # Agora adiciona manualmente na árvore de camadas
        node = project.layerTreeRoot().insertLayer(0, camada_pontos)

        if node is not None:
            node.setItemVisibilityChecked(False)

        QApplication.processEvents()

        self.mostrar_mensagem(self.tr("Camada de Pontos Criada com sucesso em {execution_time:.2f} segundos.").format(execution_time=execution_time), "Sucesso")

    def extrair_cotas(self):
        """
        Executa a extração de cotas (pontos ou polígonos) de uma camada raster selecionada no ComboBox.

        Funcionalidades:
        - Verifica se há uma camada raster selecionada e válida.
        - Executa a extração de cotas de pontos se o checkbox de pontos estiver marcado.
        - Executa a extração de cotas de polígonos, simples, estilizada ou atribuída, se os checkboxes correspondentes estiverem marcados.

        Parâmetros:
        - Nenhum.

        Retorna:
        - None.
        """
        # Verifica se alguma camada está selecionada no ComboBox
        selected_raster_id = self.comboBoxRaster.currentData()  # Obtém o ID da camada raster selecionada
        if not selected_raster_id:
            # Se não houver camada selecionada, exibe uma mensagem de erro e interrompe o processo
            self.mostrar_mensagem(self.tr("Nenhuma camada raster selecionada."), "Erro")
            return  # Sai da função se não houver camada

        # Obtém a camada selecionada no projeto usando o ID do ComboBox
        layer = QgsProject.instance().mapLayer(selected_raster_id)  # Obtém a camada raster associada ao ID
        if not layer:
            # Se a camada for inválida, exibe uma mensagem de erro e interrompe o processo
            self.mostrar_mensagem(self.tr("Camada raster inválida."), "Erro")
            return  # Sai da função se a camada for inválida

        # Processa a extração de cotas de pontos se o checkbox de pontos estiver marcado
        if self.checkboxPontos.isChecked():
            self.processar_cotas_pontos(layer)  # Chama o método para processar cotas de pontos

        # Processa a extração de cotas de polígonos (simples, estilizada ou atribuída) conforme o estado dos checkboxes
        if self.checkboxPoligonos.isChecked() or self.checkboxEstilizada.isChecked() or self.checkboxAtribuida.isChecked():
            estilizar = self.checkboxEstilizada.isChecked()  # Verifica se o checkbox de estilo está marcado
            atribuir = self.checkboxAtribuida.isChecked()  # Verifica se o checkbox de atribuição está marcado
            self.processar_cotas_poligonos(layer, estilizar=estilizar, atribuir=atribuir)  # Chama o método para processar cotas de polígonos