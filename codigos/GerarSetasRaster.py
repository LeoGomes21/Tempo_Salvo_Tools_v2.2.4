from qgis.core import QgsProject, QgsRasterLayer, QgsMapSettings, QgsMapRendererCustomPainterJob, Qgis, QgsMessageLog, QgsWkbTypes, QgsVectorLayer, QgsFeature, QgsGeometry, QgsCoordinateTransform, QgsCoordinateReferenceSystem, QgsField, QgsPointXY, QgsRaster, QgsLineSymbol, QgsPalLayerSettings, QgsTextFormat, QgsVectorLayerSimpleLabeling, QgsTextBackgroundSettings, QgsProperty, QgsRuleBasedRenderer
from qgis.PyQt.QtWidgets import QDialog, QCheckBox, QComboBox, QPushButton, QGraphicsView, QGraphicsScene, QGraphicsPixmapItem, QColorDialog, QRadioButton, QProgressBar, QFileDialog
from qgis.PyQt.QtCore import Qt, QRectF, QPointF, QSize, QVariant, QSettings, QMetaType, QCoreApplication, QUrl
from qgis.PyQt.QtGui import QImage, QPainter, QPixmap, QColor, QFont, QDesktopServices
from qgis.utils import iface
from qgis.PyQt import uic
import math
import time
import os

FORM_CLASS, _ = uic.loadUiType(os.path.join(
    os.path.dirname(__file__), 'GerarSetasRaster.ui'))

class SetasManager(QDialog, FORM_CLASS):
    def __init__(self, parent=None):
        """
        Inicializa o diálogo SetasManager, configurando a interface gráfica, conectando sinais aos slots
        e configurando elementos da interface.

        Parâmetros:
        - parent (QWidget): O widget pai, caso haja. O padrão é None.

        A função realiza as seguintes ações:
        - Configura a interface gráfica usando o Qt Designer.
        - Define o título da janela.
        - Armazena a referência da interface do QGIS.
        - Inicializa e configura a cena gráfica para exibição de rasters.
        - Inicializa ComboBox de seleção de camadas raster e camadas de linha.
        - Conecta os sinais aos respectivos slots para manipulação de eventos.
        - Define valores padrões para alguns elementos da interface, como a seleção de radio buttons e spin boxes.
        - Conecta o botão de seleção de cor ao método de escolha de cor.
        """
        super(SetasManager, self).__init__(parent)
        # Configura a interface do usuário a partir do Designer.
        self.setupUi(self)

        # Altera o título da janela
        self.setWindowTitle(self.tr("Gerar Setas Sobre o MDT"))

        self.iface = iface  # Armazena a referência da interface QGIS

        # Cria uma cena gráfica para o QGraphicsView
        self.scene = QGraphicsScene()
        self.graphicsViewRaster.setScene(self.scene)

        # Inicializa o ComboBox de Raster
        self.init_combo_box_raster()

        # Inicializa o ComboBox de Linhas
        self.init_combo_box_linhas()

        # Conecta os sinais aos slots
        self.connect_signals()

        # Configura o radioButtonSimples como selecionado por padrão
        self.radioButtonSimples.setChecked(True)
       
        # Chama a função para definir o limite inicial do spinBoxAbertura
        self.atualizar_spinBoxAbertura()

        # Conecta o sinal de mudança de seleção da camada de linhas
        self.verificar_selecao_linhas()

        # Cor padrão para as setas
        self.cor_seta = None

        # Armazena o estilo padrão do botão de cor
        self.pushButtonCor_default_style = self.pushButtonCor.styleSheet()

        # Conecta o botão de seleção de cor ao método
        self.pushButtonCor.clicked.connect(self.escolher_cor)

    def tr(self, message):
        """
        Traduz textos deste diálogo.
        O contexto precisa ser estável para o Qt Linguist encontrar as traduções.
        """
        return QCoreApplication.translate("SetasManager", message)

    def connect_signals(self):
        """
        Conecta os sinais (eventos) dos elementos da interface gráfica aos métodos (slots) correspondentes.

        A função realiza as seguintes ações:
        - Conecta os sinais de mudança de seleção nos ComboBoxes (Raster e Linhas) aos métodos que atualizam a visualização,
          tooltips, e verificam o estado dos botões.
        - Conecta sinais de adição e remoção de camadas ao método de atualização do ComboBox, para garantir que a lista de
          camadas esteja sempre atualizada.
        - Conecta o evento de alteração do nome de qualquer camada à atualização dos ComboBoxes.
        - Verifica o estado inicial do botão "Gerar Setas".
        - Conecta o botão "Gerar Setas" ao método que gera as setas com base nas camadas selecionadas.
        - Conecta o botão "Cancelar" ao método de fechamento do diálogo.
        """
        # Conecta o sinal de mudança de índice (seleção) do comboBoxRaster ao método display_raster
        self.comboBoxRaster.currentIndexChanged.connect(self.display_raster)

        # Conecta a mudança de índice do comboBoxRaster ao método atualizar_tooltip_comboBoxRaster para atualizar a tooltip
        self.comboBoxRaster.currentIndexChanged.connect(self.atualizar_tooltip_comboBoxRaster)

        # Conecta a mudança de índice do comboBoxRaster ao método verificar_estado_pushButtonGerar para ativar/desativar o botão
        self.comboBoxRaster.currentIndexChanged.connect(self.verificar_estado_pushButtonGerar)

        # Conecta a mudança de índice do comboBoxLinhas ao método verificar_estado_pushButtonGerar para ativar/desativar o botão
        self.comboBoxLinhas.currentIndexChanged.connect(self.verificar_estado_pushButtonGerar)

        # Conecta a mudança de índice do comboBoxLinhas ao método verificar_selecao_linhas para verificar a seleção de feições
        self.comboBoxLinhas.currentIndexChanged.connect(self.verificar_selecao_linhas)

        # Conecta a mudança de índice do comboBoxLinhas ao método atualizar_tooltip_comboBoxLinhas para atualizar a tooltip
        self.comboBoxLinhas.currentIndexChanged.connect(self.atualizar_tooltip_comboBoxLinhas)

        # Conecta a mudança de índice do comboBoxRaster ao método check_push_button_setas_status para verificar o status do botão
        self.comboBoxRaster.currentIndexChanged.connect(self.check_push_button_setas_status)

        # Conecta o sinal de remoção de camada do projeto ao método update_combo_box para atualizar os ComboBoxes
        QgsProject.instance().layersRemoved.connect(self.update_combo_box)

        # Conecta o sinal de adição de camada ao projeto ao método handle_layers_added para atualizar os ComboBoxes
        QgsProject.instance().layersAdded.connect(self.handle_layers_added)

        # Conecta o sinal de alteração do nome de cada camada ao método update_combo_box para garantir que a interface esteja atualizada
        for layer in QgsProject.instance().mapLayers().values():
            layer.nameChanged.connect(self.update_combo_box)

        # Verifica o estado inicial do botão "Gerar Setas", ativando ou desativando conforme necessário
        self.verificar_estado_pushButtonGerar()

        # Conecta o botão "Gerar Setas" ao método gerar_setas, que inicia o processo de criação das setas
        self.pushButtonGerar.clicked.connect(self.gerar_setas)

        # Conecta o botão "Cancelar" ao método close_dialog, que fecha o diálogo
        self.pushButtonCancelar.clicked.connect(self.close_dialog)

        # Conecta o sinal de mudança de valor do spinBoxCabeca
        self.spinBoxCabeca.valueChanged.connect(self.atualizar_spinBoxAbertura)

        # pushButtonExportarDXF
        self.pushButtonExportarDXF.clicked.connect(self.exportar_para_dxf)

        # Detecta se a camada foi removida
        QgsProject.instance().layersRemoved.connect(self.handle_layers_removed)

    def handle_layers_removed(self, layer_ids):
        """
        Verifica se a camada gerada pelo pushButtonGerar foi removida do projeto.
        Se a camada estiver entre as removidas ou já não for válida, limpa a referência e desativa o botão pushButtonExportarDXF.
        
        :param layer_ids: Lista de IDs das camadas removidas.
        """
        # Só executa se o diálogo ainda estiver visível
        if not self.isVisible():
            return

        try:
            # Verifica se o atributo exploded_layer já existe
            if not hasattr(self, 'exploded_layer') or self.exploded_layer is None or not self.exploded_layer.isValid():
                self.exploded_layer = None
                self.atualizar_estado_pushButtonExportarDXF()
                return

            # Verifica se o ID da camada está entre os removidos
            if self.exploded_layer.id() in layer_ids:
                self.exploded_layer = None
                self.atualizar_estado_pushButtonExportarDXF()
        except RuntimeError:
            self.exploded_layer = None
            self.atualizar_estado_pushButtonExportarDXF()

    def atualizar_estado_checkbox(self):
        """
        Atualiza o estado (habilitado ou desabilitado) do checkbox que permite selecionar feições
        específicas, com base na camada de linhas atualmente selecionada.

        Parâmetros:
        - self: Referência para a instância atual da classe (implícito), utilizada para acessar os atributos e métodos da classe.

        A função realiza as seguintes ações:
        - Obtém a camada de linhas atualmente selecionada no ComboBox de Linhas.
        - Verifica se a camada selecionada contém feições selecionadas.
        - Se houver feições selecionadas, o checkbox para seleção de feições é habilitado.
        - Se não houver feições selecionadas ou se não existir uma camada válida, o checkbox é desabilitado.
        
        Retorno:
        - Nenhum retorno explícito. O estado do checkbox é atualizado diretamente na interface gráfica.
        """
        # Obtém o ID da camada de linhas atualmente selecionada no comboBoxLinhas
        selected_line_id = self.comboBoxLinhas.currentData()
        
        # Obtém a camada de linhas do projeto pelo seu ID
        selected_layer = QgsProject.instance().mapLayer(selected_line_id)

        # Verifica se a camada selecionada é válida e possui feições selecionadas
        if selected_layer and selected_layer.selectedFeatureCount() > 0:
            # Habilita o checkboxSeleciona se houver feições selecionadas
            self.checkBoxSeleciona.setEnabled(True)
        else:
            # Desabilita o checkboxSeleciona se não houver feições selecionadas
            self.checkBoxSeleciona.setEnabled(False)

    def init_combo_box_linhas(self):
        """
        Inicializa o ComboBox de Linhas, preenchendo-o com todas as camadas de linhas disponíveis no projeto atual.

        Parâmetros:
        - self: Referência para a instância atual da classe (implícito), utilizada para acessar os atributos e métodos da classe.

        A função realiza as seguintes ações:
        - Obtém todas as camadas do projeto atual.
        - Filtra apenas as camadas do tipo linha (geometria de linhas).
        - Limpa o ComboBox de Linhas antes de preencher com as camadas filtradas.
        - Adiciona as camadas de linhas ao ComboBox.
        - Se houver camadas de linhas, a primeira camada da lista é automaticamente selecionada.
        - Atualiza a tooltip do ComboBox de Linhas para refletir a camada selecionada.

        Retorno:
        - Nenhum retorno explícito. A função atualiza diretamente o estado do ComboBox de Linhas e seu conteúdo.
        """
        # Obtém todas as camadas do projeto atual
        layers = QgsProject.instance().mapLayers().values()

        # Filtra apenas camadas de linhas, verificando se são camadas vetoriais com geometria de linha
        line_layers = [layer for layer in layers if layer.type() == layer.VectorLayer and layer.geometryType() == QgsWkbTypes.GeometryType.LineGeometry]

        # Limpa o ComboBox de Linhas antes de adicionar as novas camadas
        self.comboBoxLinhas.clear()

        # Adiciona as camadas de linhas ao ComboBox, associando o nome da camada ao seu ID
        for line_layer in line_layers:
            self.comboBoxLinhas.addItem(line_layer.name(), line_layer.id())

        # Se houver camadas de linhas disponíveis, seleciona a primeira camada automaticamente
        if line_layers:
            self.comboBoxLinhas.setCurrentIndex(0)

        # Atualiza a tooltip do ComboBox para exibir informações sobre a camada selecionada
        self.atualizar_tooltip_comboBoxLinhas()

    def init_combo_box_raster(self):
        """
        Inicializa o ComboBox de Raster, preenchendo-o com todas as camadas raster disponíveis no projeto atual.

        Parâmetros:
        - self: Referência para a instância atual da classe (implícito), utilizada para acessar os atributos e métodos da classe.

        A função realiza as seguintes ações:
        - Obtém todas as camadas do projeto atual.
        - Filtra apenas as camadas do tipo raster.
        - Limpa o ComboBox de Raster antes de preenchê-lo com as camadas filtradas.
        - Adiciona as camadas raster ao ComboBox.
        - Se houver camadas raster, a primeira camada é selecionada e o ComboBox é habilitado.
        - Se não houver camadas raster, o ComboBox e o botão de gerar setas são desativados.
        - Atualiza a tooltip do ComboBox de Raster para refletir a camada selecionada.

        Retorno:
        - Nenhum retorno explícito. A função atualiza diretamente o estado do ComboBox de Raster e seu conteúdo.
        """
        # Obtém todas as camadas do projeto atual
        layers = QgsProject.instance().mapLayers().values()

        # Filtra apenas camadas raster, verificando se o tipo da camada é RasterLayer
        raster_layers = [layer for layer in layers if layer.type() == layer.RasterLayer]

        # Limpa o ComboBox de Raster antes de adicionar novas camadas
        self.comboBoxRaster.clear()

        # Adiciona as camadas raster ao ComboBox, associando o nome da camada ao seu ID
        for raster_layer in raster_layers:
            self.comboBoxRaster.addItem(raster_layer.name(), raster_layer.id())

        # Se houver camadas raster disponíveis, seleciona a primeira camada e habilita o ComboBox
        if raster_layers:
            self.comboBoxRaster.setCurrentIndex(0)
            self.comboBoxRaster.setEnabled(True)
            # Verifica o estado do botão de gerar setas e exibe o raster
            self.check_push_button_setas_status()
            self.display_raster()
        else:
            # Se não houver camadas raster, desativa o ComboBox e o botão de gerar setas
            self.comboBoxRaster.setEnabled(False)
            self.pushButtonGerar.setEnabled(False)

        # Atualiza a tooltip do ComboBox de Raster para refletir a camada selecionada
        self.atualizar_tooltip_comboBoxRaster()

    def check_push_button_setas_status(self):
        """
        Verifica se o botão 'Gerar Setas' (pushButtonGerar) deve estar ativo ou não, 
        com base na camada raster atualmente selecionada.

        Parâmetros:
        - self: Referência para a instância atual da classe (implícito), utilizada para acessar os atributos e métodos da classe.

        A função realiza as seguintes ações:
        - Obtém a camada raster atualmente selecionada no ComboBox de Raster.
        - Verifica se a camada selecionada é válida (não nula) e se é uma camada raster.
        - Verifica se a camada raster provém de um provedor específico (como WMS, XYZ, WCS, etc.).
        - Se a camada for de um provedor incompatível ou inválida, o botão de gerar setas é desativado.
        - Caso contrário, o botão é ativado.

        Retorno:
        - Nenhum retorno explícito. A função ativa ou desativa o botão 'Gerar Setas' diretamente na interface gráfica.
        """
        # Obtém o ID da camada raster atualmente selecionada no comboBoxRaster
        selected_raster_id = self.comboBoxRaster.currentData()

        # Obtém a camada raster do projeto pelo seu ID
        selected_layer = QgsProject.instance().mapLayer(selected_raster_id)

        # Se a camada selecionada for inválida (None), desativa o botão "Gerar Setas"
        if selected_layer is None:
            self.pushButtonGerar.setEnabled(False)
            return

        # Verifica se a camada selecionada é uma QgsRasterLayer
        if isinstance(selected_layer, QgsRasterLayer):
            # Obtém o nome do provedor da camada raster
            provider_name = selected_layer.providerType().lower()

            # Verifica se a camada é proveniente de um provedor incompatível (como WMS, XYZ, WCS, etc.)
            if provider_name in ['wms', 'xyz', 'wcs', 'arcgisrest', 'google', 'bing']:
                # Desativa o botão se for um provedor que não permite a operação
                self.pushButtonGerar.setEnabled(False)
            else:
                # Ativa o botão se a camada for válida e não for de um provedor incompatível
                self.pushButtonGerar.setEnabled(True)
        else:
            # Desativa o botão se a camada não for uma camada raster
            self.pushButtonGerar.setEnabled(False)

    def display_raster(self):
        """
        Renderiza a camada raster atualmente selecionada no QGraphicsView da interface gráfica.

        Parâmetros:
        - self: Referência para a instância atual da classe (implícito), utilizada para acessar os atributos e métodos da classe.

        A função realiza as seguintes ações:
        - Limpa a cena gráfica antes de renderizar uma nova camada raster.
        - Obtém a camada raster atualmente selecionada no ComboBox de Raster.
        - Verifica se a camada selecionada é válida (do tipo QgsRasterLayer).
        - Configura o mapa e renderiza a camada raster, criando uma imagem com as dimensões corretas.
        - Adiciona a imagem renderizada à cena gráfica e ajusta o QGraphicsView para exibir a imagem, preservando a proporção.

        Retorno:
        - Nenhum retorno explícito. A função atualiza diretamente a cena gráfica e exibe a camada raster no QGraphicsView.
        """
        # Limpa a cena antes de adicionar um novo item (remove qualquer conteúdo anterior)
        self.scene.clear()

        # Obtém o ID da camada raster selecionada
        selected_raster_id = self.comboBoxRaster.currentData()

        # Busca a camada raster pelo ID
        selected_layer = QgsProject.instance().mapLayer(selected_raster_id)

        # Verifica se a camada selecionada é uma camada raster (QgsRasterLayer)
        if isinstance(selected_layer, QgsRasterLayer):
            # Configurações do mapa
            map_settings = QgsMapSettings()
            map_settings.setLayers([selected_layer])  # Definimos a camada a ser renderizada
            map_settings.setBackgroundColor(QColor(255, 255, 255))
            
            # Define o tamanho da imagem a ser renderizada
            width = self.graphicsViewRaster.viewport().width()
            height = self.graphicsViewRaster.viewport().height()
            map_settings.setOutputSize(QSize(width, height))
            
            # Define a extensão do mapa (extensão do raster)
            map_settings.setExtent(selected_layer.extent())

            # Cria a imagem para renderizar
            image = QImage(width, height, QImage.Format.Format_ARGB32)
            image.fill(Qt.GlobalColor.transparent)

            # Configura o pintor e a tarefa de renderização
            painter = QPainter(image)
            render_job = QgsMapRendererCustomPainterJob(map_settings, painter)

            # Executa a renderização
            render_job.start()
            render_job.waitForFinished()
            painter.end()

            # Cria um pixmap a partir da imagem renderizada
            pixmap = QPixmap.fromImage(image)
            pixmap_item = QGraphicsPixmapItem(pixmap)

            # Adiciona o item à cena
            self.scene.addItem(pixmap_item)

            # Ajusta a cena ao QGraphicsView, garantindo que o modo de ajuste preserve a proporção
            self.graphicsViewRaster.setSceneRect(pixmap_item.boundingRect())
            self.graphicsViewRaster.fitInView(self.scene.sceneRect(), Qt.AspectRatioMode.KeepAspectRatio)

    def showEvent(self, event):
        """
        Sobrescreve o evento 'showEvent' do diálogo, que é disparado quando a janela é exibida.
        O método realiza ações específicas para resetar os componentes e ajustar a visualização do raster.

        Parâmetros:
        - self: Referência para a instância atual da classe (implícito), utilizada para acessar os atributos e métodos da classe.
        - event: O evento 'showEvent' que contém informações sobre a exibição do diálogo.

        A função realiza as seguintes ações:
        - Chama a função base 'showEvent' para garantir que o comportamento padrão do evento seja executado.
        - Chama o método 'resetar_componentes' para restaurar os elementos da interface para seus estados iniciais.
        - Chama o método 'display_raster' para ajustar e renderizar a camada raster no QGraphicsView.

        Retorno:
        - Nenhum retorno explícito. A função executa ações diretamente na interface gráfica quando o diálogo é exibido.
        """
        # Chama o método original 'showEvent' da superclasse (QDialog) para manter o comportamento padrão
        super(SetasManager, self).showEvent(event)
        
        # Chama a função para resetar os componentes da interface (como valores de ComboBoxes, spinBoxes, etc.)
        self.resetar_componentes()

        # Ajusta a visualização da camada raster no QGraphicsView quando o diálogo é exibido
        self.display_raster()

        # Atualiza o estado do botão de exportação para DXF
        self.atualizar_estado_pushButtonExportarDXF()

    def resetar_componentes(self):
        """
        Reseta os componentes do diálogo para seus estados iniciais, restaurando valores padrão e
        desmarcando checkboxes e botões de rádio.

        Parâmetros:
        - self: Referência para a instância atual da classe (implícito), utilizada para acessar os atributos e métodos da classe.

        A função realiza as seguintes ações:
        - Reseta a seleção dos ComboBoxes (Raster e Linhas) para o primeiro item.
        - Marca o radioButtonSimples como selecionado.
        - Define valores padrão para os spinBoxes (Cabeça e Abertura).
        - Desmarca o checkboxSeleciona e o desabilita, se necessário.
        - Reseta a cor das setas (cor_seta) para None.
        - Restaura o estilo padrão do botão de seleção de cor.
        - Verifica se a camada de linhas selecionada possui feições e habilita o checkboxSeleciona, se houver feições selecionadas.

        Retorno:
        - Nenhum retorno explícito. A função altera o estado dos componentes diretamente na interface gráfica.
        """
        self.comboBoxRaster.setCurrentIndex(0)  # Reseta a seleção do ComboBoxRaster para o primeiro item
        self.comboBoxLinhas.setCurrentIndex(0)  # Reseta a seleção do ComboBoxLinhas para o primeiro item
        self.radioButtonSimples.setChecked(True)  # Marca o radioButtonSimples como selecionado
        self.spinBoxCabeca.setValue(5)  # Define um valor padrão para o spinBoxCabeca
        self.spinBoxAbertura.setValue(0)  # Define um valor padrão para o spinBoxAbertura
        self.checkBoxSeleciona.setChecked(False)  # Desmarca o checkboxSeleciona
        self.cor_seta = None  # Reseta a cor das setas para None
        # Restaura o estilo padrão do botão de cor definido no Qt Designer
        self.pushButtonCor.setStyleSheet(self.pushButtonCor_default_style)

        # Verifica se a camada de linhas selecionada possui feições selecionadas
        selected_line_id = self.comboBoxLinhas.currentData()
        selected_layer = QgsProject.instance().mapLayer(selected_line_id)

        # Se a camada de linhas selecionada tiver feições selecionadas, habilita o checkboxSeleciona
        if selected_layer and selected_layer.selectedFeatureCount() > 0:
            self.checkBoxSeleciona.setEnabled(True)
            self.checkBoxSeleciona.setChecked(False)  # Marca o checkbox se houver feições selecionadas
        else:
            # Se não houver feições selecionadas, desabilita o checkboxSeleciona
            self.checkBoxSeleciona.setEnabled(False)
            self.checkBoxSeleciona.setChecked(False)

    def handle_layers_added(self, layers):
        """
        Método que é chamado quando novas camadas são adicionadas ao projeto. Atualiza os ComboBoxes
        de raster e linhas para incluir as novas camadas.

        Parâmetros:
        - self: Referência para a instância atual da classe (implícito), utilizada para acessar os atributos e métodos da classe.
        - layers: Lista de camadas recém-adicionadas ao projeto (não utilizada diretamente neste método, mas pode ser usada para filtragem futura).

        A função realiza as seguintes ações:
        - Chama o método 'update_combo_box' para atualizar os ComboBoxes de raster e linhas.

        Retorno:
        - Nenhum retorno explícito. A função apenas atualiza os ComboBoxes na interface gráfica.
        """
        # Chama a função de atualização dos ComboBoxes de raster e linhas quando novas camadas são adicionadas
        self.update_combo_box()

    def update_combo_box(self):
        """
        Atualiza os ComboBoxes de Raster e Linhas quando há adição ou remoção de camadas no projeto.
        A função tenta restaurar a seleção anterior após a atualização.

        Parâmetros:
        - self: Referência para a instância atual da classe (implícito), utilizada para acessar os atributos e métodos da classe.

        A função realiza as seguintes ações:
        - Armazena o índice e o ID da camada raster e de linhas atualmente selecionadas para restaurar após a atualização.
        - Recarrega os ComboBoxes de Raster e Linhas chamando os métodos 'init_combo_box_raster' e 'init_combo_box_linhas'.
        - Tenta restaurar a seleção de camadas anteriormente selecionadas. Caso a camada anterior não esteja mais disponível,
          a função seleciona a primeira camada da lista, se houver.

        Retorno:
        - Nenhum retorno explícito. A função altera diretamente os ComboBoxes na interface gráfica.
        """
        # Armazena a seleção atual do ComboBoxRaster (índice e ID da camada selecionada)
        current_raster_index = self.comboBoxRaster.currentIndex()
        current_raster_id = self.comboBoxRaster.itemData(current_raster_index)
        
        # Armazena a seleção atual do ComboBoxLinhas (índice e ID da camada selecionada)
        current_line_index = self.comboBoxLinhas.currentIndex()
        current_line_id = self.comboBoxLinhas.itemData(current_line_index)

        # Atualiza o ComboBox de Raster e Linhas com as camadas atualmente disponíveis no projeto
        self.init_combo_box_raster()
        self.init_combo_box_linhas()

        # Tenta restaurar a seleção anterior no ComboBoxRaster
        if current_raster_id:
            raster_index = self.comboBoxRaster.findData(current_raster_id)  # Busca o índice correspondente ao ID da camada anterior
            if raster_index != -1:
                # Se encontrar o ID da camada anterior, restaura a seleção
                self.comboBoxRaster.setCurrentIndex(raster_index)
            else:
                # Se a camada anterior não estiver disponível, seleciona a primeira camada da lista, se houver
                if self.comboBoxRaster.count() > 0:
                    self.comboBoxRaster.setCurrentIndex(0)
                    self.display_raster()  # Exibe o raster da primeira camada

        # Tenta restaurar a seleção anterior no ComboBoxLinhas
        if current_line_id:
            line_index = self.comboBoxLinhas.findData(current_line_id)  # Busca o índice correspondente ao ID da camada anterior
            if line_index != -1:
                # Se encontrar o ID da camada anterior, restaura a seleção
                self.comboBoxLinhas.setCurrentIndex(line_index)

    def gerar_camadas_pontos(self, exploded_layer, original_layer):
        """
        Gera uma nova camada de pontos a partir de uma camada de linhas explodida, coletando os valores de elevação
        (cotas) do raster para os vértices inicial e final de cada segmento de linha. Adiciona os valores de elevação
        à camada de pontos e calcula a inclinação para a camada de linhas explodida.

        Parâmetros:
        - self: Referência para a instância atual da classe (implícito), utilizada para acessar os atributos e métodos da classe.
        - exploded_layer (QgsVectorLayer): A camada de linhas explodida, onde cada segmento de linha será processado para obter
          os valores de elevação (cotas) de seus pontos.
        - original_layer (QgsVectorLayer): A camada de linhas original, usada para referência.

        A função realiza as seguintes ações:
        - Obtém a camada raster atualmente selecionada no ComboBox de Raster.
        - Verifica se a camada raster é válida e é do tipo QgsRasterLayer.
        - Cria uma nova camada de pontos com o mesmo sistema de referência da camada de linhas explodida.
        - Adiciona os pontos correspondentes aos vértices inicial e final de cada segmento de linha à nova camada de pontos,
          coletando os valores de elevação do raster no ponto inicial e final.
        - Armazena as cotas (elevação) dos pontos no dicionário 'cota_inicial_final' para posterior cálculo da inclinação.
        - Calcula a inclinação da camada de linhas explodida chamando a função '_calcular_inclinacao'.

        Retorno:
        - Nenhum retorno explícito. A função adiciona diretamente a camada de pontos ao projeto e atualiza a camada de linhas
          explodida com a inclinação calculada.
        """
        # Obtém o ID da camada raster selecionada no comboBoxRaster
        selected_raster_id = self.comboBoxRaster.currentData()
        # Busca a camada raster no projeto pelo seu ID
        selected_raster = QgsProject.instance().mapLayer(selected_raster_id)

        # Verifica se a camada raster selecionada é válida e se é do tipo QgsRasterLayer
        if not selected_raster or not isinstance(selected_raster, QgsRasterLayer):
            self.mostrar_mensagem(self.tr("Nenhuma camada raster válida foi selecionada"), "Erro")
            return

        # Cria a nova camada de pontos com o mesmo SRC da camada de linhas explodida
        point_layer = QgsVectorLayer(f"Point?crs={exploded_layer.crs().authid()}", f"{exploded_layer.name()}_points", "memory")
        point_layer_data = point_layer.dataProvider()

        # Adiciona o campo "ValorRaster" à camada de pontos
        point_layer_data.addAttributes([
            QgsField("ID", QMetaType.Type.Int),
            QgsField("ValorRaster", QMetaType.Type.Double)
        ])
        point_layer.updateFields()

        # Dicionário para armazenar as cotas dos pontos iniciais e finais por segmento de linha
        cota_inicial_final = {}

        point_id = 1
        for feature in exploded_layer.getFeatures():
            geom = feature.geometry()
            if geom:
                vertices = list(geom.vertices())
                if len(vertices) >= 2:
                    # Converte o primeiro e último vértice de QgsPoint para QgsPointXY
                    start_vertex_xy = QgsPointXY(vertices[0])
                    end_vertex_xy = QgsPointXY(vertices[-1])

                    # Coleta a cota do MDT no ponto inicial
                    ident_start = selected_raster.dataProvider().identify(start_vertex_xy, QgsRaster.IdentifyFormat.IdentifyFormatValue)
                    cota_start = ident_start.results().get(1, None)

                    # Coleta a cota do MDT no ponto final
                    ident_end = selected_raster.dataProvider().identify(end_vertex_xy, QgsRaster.IdentifyFormat.IdentifyFormatValue)
                    cota_end = ident_end.results().get(1, None)

                    # Armazena as cotas no dicionário
                    cota_inicial_final[feature.id()] = (cota_start, cota_end)

                    # Cria as feições de pontos e as adiciona à camada de pontos
                    for vertex_xy, cota in [(start_vertex_xy, cota_start), (end_vertex_xy, cota_end)]:
                        point_feat = QgsFeature(point_layer.fields())
                        point_geom = QgsGeometry.fromPointXY(vertex_xy)
                        point_feat.setGeometry(point_geom)
                        point_feat.setAttributes([point_id, cota])
                        point_layer_data.addFeature(point_feat)
                        point_id += 1

        # Adiciona a nova camada de pontos ao projeto
        # QgsProject.instance().addMapLayer(point_layer)

        # Calcula a inclinação e atualiza a camada de linhas explodida
        self._calcular_inclinacao(exploded_layer, cota_inicial_final)

    def _calcular_inclinacao(self, exploded_layer, cota_inicial_final):
        """
        Calcula a inclinação para cada segmento de linha na camada explodida com base nas cotas (elevação)
        dos pontos inicial e final. A inclinação é armazenada como um novo atributo na camada.

        Parâmetros:
        - self: Referência para a instância atual da classe (implícito), utilizada para acessar os atributos e métodos da classe.
        - exploded_layer (QgsVectorLayer): A camada de linhas explodida, onde cada segmento de linha será atualizado com o valor de inclinação.
        - cota_inicial_final (dict): Dicionário que contém as cotas (elevação) inicial e final de cada segmento de linha.
          A chave é o ID da feição, e o valor é uma tupla (cota_start, cota_end).

        A função realiza as seguintes ações:
        - Inicia a edição da camada de linhas explodida.
        - Para cada segmento de linha, obtém as cotas inicial e final.
        - Calcula a inclinação usando a fórmula: (cota_end - cota_start) / comprimento * 100.
        - Armazena o valor da inclinação como um novo atributo na camada.
        - Se a cota inicial ou final for nula, define a inclinação como None.
        - Finaliza as alterações na camada ao chamar 'commitChanges'.

        Retorno:
        - Nenhum retorno explícito. A função atualiza diretamente os valores de inclinação na camada de linhas explodida.
        """
        # Inicia o modo de edição da camada de linhas explodida
        exploded_layer.startEditing()

        # Itera sobre cada feição da camada explodida
        for feature in exploded_layer.getFeatures():
            # Obtém as cotas inicial e final para a feição atual a partir do dicionário 'cota_inicial_final'
            cota_start, cota_end = cota_inicial_final.get(feature.id(), (None, None))

            # Verifica se as cotas inicial e final estão definidas
            if cota_start is not None and cota_end is not None:
                # Calcula o comprimento do segmento de linha
                length = feature.geometry().length()
                if length > 0:
                    # Calcula a inclinação como a variação de cota dividida pelo comprimento, multiplicada por 100 para obter a porcentagem
                    inclinacao = round(((cota_end - cota_start) / length) * 100, 3)
                else:
                    # Define a inclinação como None se o comprimento for 0 (linha inválida)
                    inclinacao = None
            else:
                # Define a inclinação como None se qualquer uma das cotas for nula
                inclinacao = None

            # Atualiza o valor do campo "Inclinacao" na feição atual
            exploded_layer.changeAttributeValue(feature.id(), exploded_layer.fields().indexFromName("Inclinacao"), inclinacao)

        # Confirma as alterações feitas na camada
        exploded_layer.commitChanges()

    def atualizar_spinBoxAbertura(self):
        """
        Atualiza o valor máximo do spinBoxAbertura com base no valor atual do spinBoxCabeca.
        O valor máximo de abertura é definido como a metade do valor de "Cabeca".

        Parâmetros:
        - self: Referência para a instância atual da classe (implícito), utilizada para acessar os atributos e métodos da classe.

        A função realiza as seguintes ações:
        - Obtém o valor atual do spinBoxCabeca.
        - Calcula o valor máximo permitido para o spinBoxAbertura (metade do valor de "Cabeca").
        - Define o valor máximo do spinBoxAbertura.

        Retorno:
        - Nenhum retorno explícito. A função altera diretamente o valor máximo do spinBoxAbertura na interface gráfica.
        """
        # Define o valor máximo de spinBoxAbertura como metade do valor atual de spinBoxCabeca
        max_value = int(self.spinBoxCabeca.value() / 2)  # Converte o valor para inteiro
        self.spinBoxAbertura.setMaximum(max_value)  # Define o valor máximo para o spinBoxAbertura

    def explodir_linhas(self, selected_layer):
        """
        Explode as feições de uma camada de linhas em segmentos individuais e cria uma nova camada de linhas com esses segmentos.
        Cada segmento de linha na nova camada é tratado como uma feição independente, e a inclinação e o comprimento são calculados.

        Parâmetros:
        - self: Referência para a instância atual da classe (implícito), utilizada para acessar os atributos e métodos da classe.
        - selected_layer (QgsVectorLayer): A camada de linhas selecionada que será explodida em segmentos individuais.

        A função realiza as seguintes ações:
        - Verifica se a camada de linhas selecionada é válida.
        - Determina se o usuário deseja explodir apenas as feições selecionadas ou todas as feições.
        - Gera um nome único para a nova camada de linhas explodidas.
        - Cria uma nova camada de linhas em memória, adicionando campos para armazenar o comprimento e a inclinação de cada segmento.
        - Se a camada tiver um SRC geográfico, transforma as coordenadas para um CRS projetado (WGS 84 / Pseudo-Mercator).
        - Para cada feição da camada original, divide as linhas em segmentos individuais e adiciona-os à nova camada.
        - Retorna a nova camada de linhas explodida.

        Retorno:
        - exploded_layer (QgsVectorLayer): A nova camada de linhas contendo os segmentos explodidos, ou None se a camada original for inválida.
        """
        # Verifica se a camada de linhas selecionada é válida
        if not selected_layer:
            self.mostrar_mensagem(self.tr("Nenhuma camada de linhas válida foi encontrada."), "Erro")
            return None

        # Verifica se o checkBoxSeleciona está marcado
        if self.checkBoxSeleciona.isChecked():
            features = selected_layer.selectedFeatures()
        else:
            features = selected_layer.getFeatures()

        # Gera um nome único para a nova camada
        base_name = f"{selected_layer.name()}_Setas"
        layer_name = base_name
        suffix = 1

        # Verifica se já existe uma camada com o mesmo nome
        while QgsProject.instance().mapLayersByName(layer_name):
            layer_name = f"{base_name}_{suffix}"
            suffix += 1

        # Cria uma nova camada para armazenar as linhas explodidas, usando o mesmo SRC da camada original
        exploded_layer = QgsVectorLayer(f"LineString?crs={selected_layer.crs().authid()}", layer_name, "memory")
        exploded_layer_data = exploded_layer.dataProvider()

        # Adiciona os campos "ID", "Comprimento" e "Inclinação" à nova camada
        exploded_layer_data.addAttributes([
            QgsField("ID", QMetaType.Type.Int),
            QgsField("Comprimento", QMetaType.Type.Double),
            QgsField("Inclinacao", QMetaType.Type.Double)
        ])
        exploded_layer.updateFields()

        # Verifica se o SRC da camada é geográfico
        is_geographic = selected_layer.crs().isGeographic()
        transform = None
        if is_geographic:
            dest_crs = QgsCoordinateReferenceSystem('EPSG:3857')  # Usa o CRS projetado WGS 84 / Pseudo-Mercator
            transform = QgsCoordinateTransform(selected_layer.crs(), dest_crs, QgsProject.instance())

        # Itera sobre as feições e realiza a explosão das linhas
        segment_id = 1
        for feature in features:
            geom = feature.geometry()
            # Verifica se a geometria é multipart (várias partes em uma única feição)
            if geom and geom.isMultipart():
                for single_line in geom.asMultiPolyline():
                    new_feat = QgsFeature(exploded_layer.fields())
                    new_geom = QgsGeometry.fromPolylineXY(single_line)
                    if is_geographic:
                        # Transforma as coordenadas para o CRS projetado se necessário
                        new_geom.transform(transform)
                    length = round(new_geom.length(), 3)
                    # Define a geometria e os atributos (ID, comprimento, inclinação)
                    new_feat.setGeometry(new_geom)
                    new_feat.setAttributes([segment_id, length, None])
                    exploded_layer_data.addFeature(new_feat)
                    segment_id += 1
            elif geom:
                # Trata linhas simples (não multipart)
                single_polyline = geom.asPolyline()
                for i in range(len(single_polyline) - 1):
                    new_feat = QgsFeature(exploded_layer.fields())
                    new_geom = QgsGeometry.fromPolylineXY([single_polyline[i], single_polyline[i + 1]])
                    if is_geographic:
                        new_geom.transform(transform)
                    length = round(new_geom.length(), 3)
                    new_feat.setGeometry(new_geom)
                    new_feat.setAttributes([segment_id, length, None])
                    exploded_layer_data.addFeature(new_feat)
                    segment_id += 1

        # Retorna a nova camada de linhas explodida
        return exploded_layer

    def iniciar_progress_bar(self, layer):
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
        # Cria uma mensagem personalizada na barra de progresso
        progressMessageBar = self.iface.messageBar().createMessage(self.tr("Exportando camada para DXF: {layer_name}").format(layer_name=layer.name()))
        progressBar = QProgressBar()  # Cria uma instância da QProgressBar
        progressBar.setAlignment(Qt.AlignmentFlag.AlignLeft | Qt.AlignmentFlag.AlignVCenter)  # Alinha a barra de progresso à esquerda e verticalmente ao centro
        progressBar.setFormat(self.tr("%p% - %v de %m Feições processadas"))  # Define o formato da barra de progresso
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

        # Define o valor máximo da barra de progresso com base no número de feições da camada
        feature_count = layer.featureCount()
        progressBar.setMaximum(feature_count)

        # Retorna o progressBar e o progressMessageBar para que possam ser atualizados durante o processo de exportação
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
            # Cria o item da mensagem
            msg = bar.createMessage("Sucesso", texto)
            
            # Se o caminho da pasta for fornecido, adiciona um botão para abrir a pasta
            if caminho_pasta:
                botao_abrir_pasta = QPushButton(self.tr("Abrir Pasta"))
                botao_abrir_pasta.clicked.connect(
                    lambda _checked=False, caminho=caminho_pasta:
                        QDesktopServices.openUrl(
                            QUrl.fromLocalFile(
                                os.path.abspath(os.fspath(caminho)))))
                msg.layout().insertWidget(1, botao_abrir_pasta)  # Adiciona o botão à esquerda do texto
            
            # Se o caminho do arquivo for fornecido, adiciona um botão para executar o arquivo
            if caminho_arquivo:
                botao_executar = QPushButton(self.tr("Executar"))
                botao_executar.clicked.connect(
                    lambda _checked=False, caminho=caminho_arquivo:
                        QDesktopServices.openUrl(
                            QUrl.fromLocalFile(
                                os.path.abspath(os.fspath(caminho)))))
                msg.layout().insertWidget(2, botao_executar)  # Adiciona o botão à esquerda do texto
            
            # Adiciona a mensagem à barra com o nível informativo e a duração especificada
            bar.pushWidget(msg, level=Qgis.MessageLevel.Info, duration=duracao)

    def gerar_setas(self):
        """
        Gera setas sobre uma camada de linhas com base em uma camada raster selecionada, calculando a inclinação 
        e aplicando o estilo configurado. O processo envolve a explosão de linhas em segmentos, cálculo de inclinação
        a partir da camada raster, e a criação de setas estilizadas.

        Parâmetros:
        - self: Referência para a instância atual da classe (implícito), utilizada para acessar os atributos e métodos da classe.

        A função realiza as seguintes ações:
        - Verifica a camada de linhas e raster selecionadas.
        - Verifica se ambas as camadas possuem projeções geográficas válidas.
        - Explode a camada de linhas em segmentos e calcula as inclinações dos segmentos usando a camada raster.
        - Aplica o estilo de seta configurado na camada de linhas.
        - Exibe uma barra de progresso durante o processo.
        - Exibe uma mensagem de sucesso ao final do processo.

        Retorno:
        - Nenhum retorno explícito. A função atualiza diretamente o projeto QGIS e exibe as setas na camada de linhas.
        """
        # Obtém o ID da camada de linhas selecionada no comboBoxLinhas
        selected_line_id = self.comboBoxLinhas.currentData()

        # Busca a camada de linhas pelo ID
        selected_layer = QgsProject.instance().mapLayer(selected_line_id)

        if not selected_layer:
            self.mostrar_mensagem(self.tr("Nenhuma camada de linhas foi encontrada"), "Erro")
            return

        if selected_layer.geometryType() != QgsWkbTypes.GeometryType.LineGeometry:
            self.mostrar_mensagem(self.tr("A camada selecionada não é do tipo linha"), "Erro")
            return

        # Obtém o ID da camada raster selecionada
        selected_raster_id = self.comboBoxRaster.currentData()
        selected_raster_layer = QgsProject.instance().mapLayer(selected_raster_id)

        if not selected_raster_layer:
            self.mostrar_mensagem(self.tr("Nenhuma camada raster foi encontrada"), "Erro")
            return

        # Verifica se as camadas são geográficas (não projetadas)
        is_line_geographic = selected_layer.crs().isGeographic()
        is_raster_geographic = selected_raster_layer.crs().isGeographic()

        # Se alguma das camadas for geográfica, exibe uma mensagem de erro
        if is_line_geographic or is_raster_geographic:
            nomes_geograficos = []
            if is_line_geographic:
                nomes_geograficos.append(selected_layer.name())
            if is_raster_geographic:
                nomes_geograficos.append(selected_raster_layer.name())

            if len(nomes_geograficos) == 1:
                mensagem = self.tr("A camada {layer_name} é geográfica, modifique a projeção para UTM.").format(layer_name=nomes_geograficos[0])
            else:
                mensagem = self.tr("As camadas {layer_names} são geográficas, modifique as projeções para UTM.").format(layer_names=self.tr(" e ").join(nomes_geograficos))

            self.mostrar_mensagem(mensagem, "Erro")
            return

        # Inicia o contador de tempo
        start_time = time.time()

        # Inicia a barra de progresso
        progressBar, progressMessageBar = self.iniciar_progress_bar(selected_layer)

        # Explode as linhas
        exploded_layer = self.explodir_linhas(selected_layer)

        # Armazena a camada gerada para uso posterior (por exemplo, na exportação para DXF)
        self.exploded_layer = exploded_layer
        
        # Marca a camada com uma propriedade customizada que identifica sua origem
        exploded_layer.setCustomProperty("gerado_por", "pushButtonGerar")

        # Atualiza a barra de progresso
        progressBar.setValue(progressBar.maximum() // 2)

        # Adiciona a camada explodida ao projeto
        QgsProject.instance().addMapLayer(exploded_layer)

        # Gera a camada de pontos e calcula a inclinação
        self.gerar_camadas_pontos(exploded_layer, selected_layer)

        # Processa as setas na camada de linhas com o estilo selecionado
        self.gerar_setas_com_estilo(exploded_layer)

        # Finaliza a barra de progresso
        progressBar.setValue(progressBar.maximum())
        QgsMessageLog.logMessage(self.tr("Processo concluído."), 'SetasManager', Qgis.MessageLevel.Info)
        self.iface.messageBar().popWidget(progressMessageBar)

        # Calcula o tempo total de execução
        elapsed_time = time.time() - start_time

        # Exibe a mensagem de sucesso
        self.mostrar_mensagem(self.tr("Setas geradas com sucesso em {elapsed_time:.2f}.").format(elapsed_time=elapsed_time), "Sucesso")

        # Habilita ou desabilita o pushButtonExportarDXF
        self.atualizar_estado_pushButtonExportarDXF()

    def gerar_setas_com_estilo(self, exploded_layer):
        """
        Gera setas na camada de linhas explodida com base no estilo selecionado pelo usuário. 
        O estilo de setas pode ser simples ou proporcional, dependendo da seleção dos radio buttons.
        Após aplicar o estilo, o rótulo de inclinação é exibido.

        Parâmetros:
        - self: Referência para a instância atual da classe (implícito), utilizada para acessar os atributos e métodos da classe.
        - exploded_layer (QgsVectorLayer): A camada de linhas explodida que será estilizada com setas.

        A função realiza as seguintes ações:
        - Verifica qual estilo de seta foi selecionado pelo usuário (Simples ou Proporcional).
        - Chama a função correspondente ao estilo selecionado para aplicar o estilo de setas.
        - Exibe os rótulos de inclinação após aplicar o estilo.

        Retorno:
        - Nenhum retorno explícito. A função aplica o estilo de setas e exibe os rótulos diretamente na camada de linhas.
        """
        # Verifica qual estilo de seta foi selecionado nos radio buttons
        if self.radioButtonSimples.isChecked():
            # Se o estilo Simples foi selecionado, processa as setas simples
            self.processar_setas_simples(exploded_layer)
        elif self.radioButtonProporcional.isChecked():
            # Se o estilo Proporcional foi selecionado, processa as setas proporcionais
            self.processar_setas_proporcionais(exploded_layer)
        else:
            # Caso nenhum estilo de seta esteja selecionado, exibe uma mensagem de erro
            self.mostrar_mensagem(self.tr("Nenhum estilo de seta selecionado."), "Erro")

        # Exibe o rótulo de "Inclinação" na camada e aplica a cor correspondente
        self.exibir_rotulo_inclinacao(exploded_layer)

    def processar_setas_simples(self, exploded_layer):
        """
        Processa a camada de linhas explodida para adicionar setas simples. O estilo da seta é baseado nos valores
        definidos pelos spin boxes de espessura e tamanho da cabeça. As setas são adicionadas a cada linha da camada explodida.

        Parâmetros:
        - self: Referência para a instância atual da classe (implícito), utilizada para acessar os atributos e métodos da classe.
        - exploded_layer (QgsVectorLayer): A camada de linhas explodida, onde cada segmento de linha será atualizado para exibir setas.

        A função realiza as seguintes ações:
        - Obtém os valores de espessura e tamanho da cabeça da seta a partir dos spin boxes.
        - Itera sobre cada feição da camada de linhas explodida.
        - Calcula as coordenadas para desenhar a seta, incluindo a linha principal e a cabeça.
        - Combina as geometrias da seta e atualiza a geometria da feição.
        - Aplica a cor das setas e exibe os rótulos de inclinação na camada.

        Retorno:
        - Nenhum retorno explícito. A função altera diretamente a geometria da camada de linhas e aplica a cor e rótulo das setas.
        """
        # Obtém os valores dos spin boxes para a espessura e o tamanho da cabeça da seta
        thickness = self.spinBoxAbertura.value()  # Define a espessura da linha conforme o valor do spinBoxAbertura
        head_length = self.spinBoxCabeca.value()  # Define o tamanho da cabeça da seta conforme o valor do spinBoxCabeca

        # Inicia o modo de edição na camada de linhas explodida
        exploded_layer.startEditing()

        # Itera sobre cada feição na camada de linhas explodida
        for feature in exploded_layer.getFeatures():
            geom = feature.geometry()
            if not geom or geom.isEmpty():
                continue

            # Obtém a linha como uma lista de pontos (QgsPointXY)
            line = geom.asPolyline()
            if len(line) < 2:
                continue

            # Cálculo do comprimento da linha, tamanho da cabeça da seta e espessura
            length = geom.length()

            # Definição dos pontos inicial, médio e final da linha
            start_point = QgsPointXY(line[0])
            mid_point = QgsPointXY(line[int(len(line) / 2)])
            end_point = QgsPointXY(line[-1])

            # Cálculo do ângulo da linha
            dx = end_point.x() - start_point.x()
            dy = end_point.y() - start_point.y()
            angle = math.atan2(dy, dx)

            # Cálculo dos pontos da cabeça da seta
            arrow_head_point1 = QgsPointXY(end_point.x() - head_length * math.cos(angle + math.pi / 6),
                                           end_point.y() - head_length * math.sin(angle + math.pi / 6))
            arrow_head_point2 = QgsPointXY(end_point.x() - head_length * math.cos(angle - math.pi / 6),
                                           end_point.y() - head_length * math.sin(angle - math.pi / 6))

            # Cálculo dos pontos de fechamento da cabeça da seta
            arrow_closure_point1 = QgsPointXY(arrow_head_point1.x() + thickness * math.cos(angle + math.pi / 2),
                                              arrow_head_point1.y() + thickness * math.sin(angle + math.pi / 2))
            arrow_closure_point2 = QgsPointXY(arrow_head_point2.x() - thickness * math.cos(angle + math.pi / 2),
                                              arrow_head_point2.y() - thickness * math.sin(angle + math.pi / 2))

            # Construção das geometrias da seta (linha principal e cabeça)
            arrow_geom = QgsGeometry.fromPolylineXY([start_point, end_point])
            arrow_head_geom1 = QgsGeometry.fromPolylineXY([end_point, arrow_head_point1])
            arrow_head_geom2 = QgsGeometry.fromPolylineXY([end_point, arrow_head_point2])
            arrow_closure_geom1 = QgsGeometry.fromPolylineXY([arrow_head_point1, arrow_closure_point1])
            arrow_closure_geom2 = QgsGeometry.fromPolylineXY([arrow_head_point2, arrow_closure_point2])

            # Combinação das geometrias da seta e cabeça em uma única geometria
            combined_geom = arrow_geom.combine(arrow_head_geom1).combine(arrow_head_geom2).combine(arrow_closure_geom1).combine(arrow_closure_geom2)

            # Atualizando a geometria da feição
            exploded_layer.changeGeometry(feature.id(), combined_geom)

        # Finaliza a edição da camada
        exploded_layer.commitChanges()

        # Aplica a cor às setas da camada de linhas
        self.aplicar_cor_setas(exploded_layer)

        # Exibe uma mensagem de sucesso ao final do processamento
        self.mostrar_mensagem(self.tr("Setas simples processadas e camada de linhas atualizada."), "Sucesso")

        # Exibe o rótulo de inclinação para cada feição da camada
        self.exibir_rotulo_inclinacao(exploded_layer)

    def exibir_rotulo_inclinacao(self, layer):
        """
        Configura os rótulos para o campo 'Inclinacao' na camada de linhas, exibindo a inclinação como porcentagem 
        com setas indicativas de subida (⬆) ou descida (⬇) e formatação condicional de cores.

        Parâmetros:
        - self: Referência para a instância atual da classe (implícito), utilizada para acessar os atributos e métodos da classe.
        - layer (QgsVectorLayer): A camada de linhas onde os rótulos de inclinação serão exibidos.

        A função realiza as seguintes ações:
        - Configura a exibição de rótulos para o campo 'Inclinacao', mostrando o valor como porcentagem.
        - Exibe setas ⬆, ⬇ ou →, dependendo se a inclinação é positiva, negativa ou zero.
        - Aplica formatação condicional de cores: vermelho para inclinações negativas, azul para positivas e preto para zero.
        - Se o usuário escolher uma cor personalizada, ela será aplicada ao texto dos rótulos.
        
        Retorno:
        - Nenhum retorno explícito. A função configura a exibição de rótulos diretamente na camada de linhas.
        """
        # Configurações para exibir rótulos
        layer_settings = QgsPalLayerSettings()
        text_format = QgsTextFormat()

        # Configurações básicas do rótulo
        layer_settings.isExpression = True  # Definimos como expressão para incluir setas
        layer_settings.fieldName = """
            CASE 
                WHEN "Inclinacao" < 0 THEN '⬇' || abs(round("Inclinacao", 3)) || '%'
                WHEN "Inclinacao" > 0 THEN '⬆' || round("Inclinacao", 3) || '%'
                ELSE '→' || round("Inclinacao", 3) || '%' 
            END
        """  # Exibe setas baseadas no valor de inclinação
        
        layer_settings.placement = QgsPalLayerSettings.Placement.Line  # Rótulos ao longo da linha

        # Configurações do texto do rótulo
        font = QFont("Arial", 11)
        font.setBold(True)
        font.setItalic(True)
        text_format.setFont(font)
        text_format.setSize(11)

        # Configuração do fundo amarelo para o rótulo
        background = QgsTextBackgroundSettings()
        background.setEnabled(False)
        background.setFillColor(QColor(255, 255, 0))  # Cor de fundo amarela
        text_format.setBackground(background)

        if self.cor_seta:
            # Se uma cor foi escolhida, aplica essa cor aos rótulos
            text_format.setColor(self.cor_seta)
        else:
            # Adiciona formatação condicional (vermelho para negativo, azul para positivo, preto para zero)
            color_expression = """
                CASE
                    WHEN "Inclinacao" < 0 THEN '255,0,0'  -- Vermelho para inclinações negativas
                    WHEN "Inclinacao" > 0 THEN '0,0,255'  -- Azul para inclinações positivas
                    ELSE '0,0,0'  -- Preto para zero
                END
            """

            # Definir as propriedades dos rótulos (cor)
            properties = layer_settings.dataDefinedProperties()
            properties.setProperty(QgsPalLayerSettings.Property.Color, QgsProperty.fromExpression(color_expression))
            layer_settings.setDataDefinedProperties(properties)

        # Aplicar o formato de texto ao rótulo
        layer_settings.setFormat(text_format)

        # Definir a rotulagem na camada
        labeling = QgsVectorLayerSimpleLabeling(layer_settings)
        layer.setLabeling(labeling)
        layer.setLabelsEnabled(True)

        # Atualiza a camada para exibir os rótulos
        layer.triggerRepaint()

    def gerar_nome_unico(self, base_name):
        """
        Gera um nome único para uma camada, incrementando um sufixo numérico caso o nome já exista no projeto.
        A função garante que cada camada criada tenha um nome distinto.

        Parâmetros:
        - self: Referência para a instância atual da classe (implícito), utilizada para acessar os atributos e métodos da classe.
        - base_name (str): O nome base que será usado como ponto de partida para gerar o nome único.

        A função realiza as seguintes ações:
        - Inicializa um sufixo numérico começando em 1.
        - Combina o nome base com o sufixo para formar o nome da camada.
        - Verifica se já existe uma camada com esse nome no projeto.
        - Se o nome já existir, incrementa o sufixo e repete o processo até encontrar um nome que não esteja em uso.

        Retorno:
        - nome_unico (str): O nome único gerado para a camada, que não colide com nomes existentes no projeto.
        """
        sufixo = 1
        nome_unico = f"{base_name}_{sufixo}"  # Combina o nome base com o sufixo para formar o nome único

        # Loop para verificar se o nome já está em uso e gerar um novo se necessário
        while QgsProject.instance().mapLayersByName(nome_unico):
            sufixo += 1  # Incrementa o sufixo numérico
            nome_unico = f"{base_name}_{sufixo}"  # Gera o próximo nome único

        return nome_unico  # Retorna o nome gerado

    def aplicar_cor_setas(self, layer):
        """
        Aplica a cor das setas com base na escolha do usuário ou, caso nenhuma cor tenha sido escolhida, aplica cores padrão 
        baseadas na inclinação. Também atualiza a legenda da camada para refletir a inclinação.

        Parâmetros:
        - self: Referência para a instância atual da classe (implícito), utilizada para acessar os atributos e métodos da classe.
        - layer (QgsVectorLayer): A camada de linhas onde as setas serão estilizadas com base nas cores definidas.

        A função realiza as seguintes ações:
        - Aplica a cor personalizada selecionada pelo usuário ou usa cores padrão (vermelho, azul, preto) com base na inclinação.
        - Define a legenda da camada, associando rótulos às diferentes regras de estilo.
        - Gera um nome único para a camada estilizada para evitar conflitos de nomes no projeto.

        Retorno:
        - Nenhum retorno explícito. A função altera diretamente a simbologia e o nome da camada no projeto QGIS.
        """
        # Obtém o nome original da camada
        base_name = layer.name()
        
        # Gera um nome único para a camada
        nome_unico = self.gerar_nome_unico(base_name)

        if self.cor_seta:
            # Se uma cor foi escolhida pelo usuário, aplica essa cor a todas as feições
            symbol = QgsLineSymbol.createSimple({'color': self.cor_seta.name()})
            layer.renderer().setSymbol(symbol)
            
            # Atualiza o nome da camada com o nome único gerado
            layer.setName(nome_unico)
        else:
            # Se nenhuma cor foi escolhida, aplica cores padrão com base na inclinação:
            # vermelho para inclinação negativa, azul para positiva e preto para zero

            # Cria símbolos de cores para cada tipo de inclinação
            symbol_negativo = QgsLineSymbol.createSimple({'color': 'red'})  # Vermelho para inclinação negativa
            symbol_positivo = QgsLineSymbol.createSimple({'color': 'blue'})  # Azul para inclinação positiva
            symbol_zero = QgsLineSymbol.createSimple({'color': 'black'})  # Preto para inclinação zero

            # Define regras baseadas na expressão de inclinação e rótulos para a legenda
            rule_negativo = QgsRuleBasedRenderer.Rule(symbol_negativo)
            rule_negativo.setFilterExpression('"Inclinacao" < 0')  # Expressão para inclinação negativa
            rule_negativo.setLabel(self.tr("Inclinação negativa"))  # Rótulo para a legenda

            rule_positivo = QgsRuleBasedRenderer.Rule(symbol_positivo)
            rule_positivo.setFilterExpression('"Inclinacao" > 0')  # Expressão para inclinação positiva
            rule_positivo.setLabel(self.tr("Inclinação positiva"))  # Rótulo para a legenda

            rule_zero = QgsRuleBasedRenderer.Rule(symbol_zero)
            rule_zero.setFilterExpression('"Inclinacao" = 0')  # Expressão para inclinação zero
            rule_zero.setLabel(self.tr("Sem inclinação"))  # Rótulo para a legenda

            # Cria uma regra raiz e adiciona as regras de inclinação como filhos
            root_rule = QgsRuleBasedRenderer.Rule(None)
            root_rule.appendChild(rule_negativo)
            root_rule.appendChild(rule_positivo)
            root_rule.appendChild(rule_zero)

            # Aplica o renderizador baseado nas regras definidas
            renderer = QgsRuleBasedRenderer(root_rule)
            layer.setRenderer(renderer)

            # Atualiza o nome da camada com o nome único gerado
            layer.setName(nome_unico)

        # Reaplica a simbologia e força a atualização da camada
        layer.triggerRepaint()

        # Atualiza a simbologia da camada na árvore de camadas do QGIS
        self.iface.layerTreeView().refreshLayerSymbology(layer.id())

    def escolher_cor(self):
        """
        Abre um diálogo para o usuário escolher uma cor para as setas. Se uma cor válida for escolhida, 
        essa cor será aplicada ao botão de seleção de cor e armazenada. Se o diálogo for cancelado, a cor será resetada.

        Parâmetros:
        - self: Referência para a instância atual da classe (implícito), utilizada para acessar os atributos e métodos da classe.

        A função realiza as seguintes ações:
        - Abre uma caixa de diálogo para o usuário escolher uma cor.
        - Se uma cor for selecionada, ela é armazenada e aplicada ao botão de cor.
        - Se o usuário cancelar a escolha, a cor é resetada para o estado padrão.

        Retorno:
        - Nenhum retorno explícito. A função altera diretamente o estado da cor e a aparência do botão de cor na interface.
        """
        # Abre o diálogo de seleção de cor, definindo uma cor inicial (a cor escolhida anteriormente ou preto)
        cor = QColorDialog.getColor(initial=self.cor_seta if self.cor_seta else QColor(0, 0, 0), parent=self, title=self.tr("Escolha a cor para as setas"))

        # Verifica se uma cor válida foi escolhida no diálogo
        if cor.isValid():
            # Armazena a cor escolhida
            self.cor_seta = cor
            
            # Aplica a cor ao botão de seleção de cor (estilo de fundo)
            self.pushButtonCor.setStyleSheet(f"background-color: {self.cor_seta.name()}")
        else:
            # Se o usuário cancelar ou não selecionar uma cor válida, reseta a cor
            self.cor_seta = None
            
            # Reseta o estilo do botão de seleção de cor para o estado padrão (sem cor de fundo)
            self.pushButtonCor.setStyleSheet("")

    def processar_setas_proporcionais(self, exploded_layer):
        """
        Processa a camada de linhas explodida para adicionar setas proporcionais ao comprimento da linha.
        O tamanho da cabeça e a espessura das setas são ajustados proporcionalmente ao comprimento de cada segmento de linha.

        Parâmetros:
        - self: Referência para a instância atual da classe (implícito), utilizada para acessar os atributos e métodos da classe.
        - exploded_layer (QgsVectorLayer): A camada de linhas explodida, onde cada segmento de linha será atualizado para exibir setas proporcionais.

        A função realiza as seguintes ações:
        - Obtém os valores de espessura e tamanho da cabeça das setas a partir dos spin boxes.
        - Itera sobre cada feição da camada de linhas explodida.
        - Calcula as coordenadas para desenhar a seta proporcional ao comprimento da linha.
        - Combina as geometrias da seta e atualiza a geometria da feição.
        - Aplica a cor das setas e finaliza as alterações.

        Retorno:
        - Nenhum retorno explícito. A função altera diretamente a geometria da camada de linhas e aplica as cores e setas.
        """
        # Obtém os valores dos spin boxes para a espessura e o tamanho da cabeça da seta
        spin_thickness = self.spinBoxAbertura.value()  # Define a espessura da linha conforme o valor do spinBoxAbertura
        spin_head_length = self.spinBoxCabeca.value()  # Define o tamanho da cabeça da seta conforme o valor do spinBoxCabeca

        # Inicia o modo de edição na camada de linhas explodida
        exploded_layer.startEditing()

        # Itera sobre cada feição na camada de linhas explodida
        for feature in exploded_layer.getFeatures():
            geom = feature.geometry()
            if not geom or geom.isEmpty():
                continue

            # Obtém a linha como uma lista de pontos (QgsPointXY)
            line = geom.asPolyline()
            if len(line) < 2:
                continue

            # Cálculo do comprimento da linha, tamanho da cabeça da seta e espessura
            length = geom.length()
            head_length = spin_head_length * length / 100 # Ajusta o tamanho da cabeça da seta proporcional ao comprimento da linha
            thickness = spin_thickness * length / 100 # Ajusta a espessura proporcional ao comprimento da linha

            # Definição dos pontos inicial, médio e final da linha
            start_point = QgsPointXY(line[0])
            mid_point = QgsPointXY(line[int(len(line) / 2)])
            end_point = QgsPointXY(line[-1])

            # Cálculo do ângulo da linha
            dx = end_point.x() - start_point.x()
            dy = end_point.y() - start_point.y()
            angle = math.atan2(dy, dx)

            # Cálculo dos pontos da cabeça da seta
            arrow_head_point1 = QgsPointXY(mid_point.x() - head_length * math.cos(angle + math.pi / 6),
                                           mid_point.y() - head_length * math.sin(angle + math.pi / 6))
            arrow_head_point2 = QgsPointXY(mid_point.x() - head_length * math.cos(angle - math.pi / 6),
                                           mid_point.y() - head_length * math.sin(angle - math.pi / 6))

            # Cálculo dos pontos de fechamento da cabeça da seta
            arrow_closure_point1 = QgsPointXY(arrow_head_point1.x() + thickness * math.cos(angle + math.pi / 2),
                                              arrow_head_point1.y() + thickness * math.sin(angle + math.pi / 2))
            arrow_closure_point2 = QgsPointXY(arrow_head_point2.x() - thickness * math.cos(angle + math.pi / 2),
                                              arrow_head_point2.y() - thickness * math.sin(angle + math.pi / 2))

            # Construção das geometrias da seta e fechamento da cabeça da seta
            arrow_geom = QgsGeometry.fromPolylineXY([start_point, mid_point, end_point])
            arrow_head_geom1 = QgsGeometry.fromPolylineXY([mid_point, arrow_head_point1])
            arrow_head_geom2 = QgsGeometry.fromPolylineXY([mid_point, arrow_head_point2])
            arrow_closure_geom1 = QgsGeometry.fromPolylineXY([arrow_head_point1, arrow_closure_point1])
            arrow_closure_geom2 = QgsGeometry.fromPolylineXY([arrow_head_point2, arrow_closure_point2])

            # Combinando as geometrias
            combined_geom = arrow_geom.combine(arrow_head_geom1).combine(arrow_head_geom2).combine(arrow_closure_geom1).combine(arrow_closure_geom2)

            # Atualiza a geometria da feição na camada de linhas explodida
            exploded_layer.changeGeometry(feature.id(), combined_geom)

        # Finaliza a edição da camada
        exploded_layer.commitChanges()

        # Aplica a cor às setas da camada de linhas
        self.aplicar_cor_setas(exploded_layer)

    def verificar_estado_pushButtonGerar(self):
        """
        Verifica o estado das camadas raster e de linhas para habilitar ou desabilitar o botão "Gerar". 
        O botão será ativado somente se uma camada raster e uma camada de linhas válidas estiverem selecionadas.

        Parâmetros:
        - self: Referência para a instância atual da classe (implícito), utilizada para acessar os atributos e métodos da classe.

        A função realiza as seguintes ações:
        - Verifica se uma camada raster válida está selecionada no ComboBox.
        - Verifica se a camada raster selecionada não é um serviço de mapa (WMS, XYZ, etc.).
        - Verifica se uma camada de linhas válida, com feições, está selecionada no ComboBox.
        - Habilita o botão "Gerar" apenas se todas as condições forem satisfeitas, caso contrário, o botão é desabilitado.

        Retorno:
        - Nenhum retorno explícito. A função habilita ou desabilita o botão "Gerar" diretamente na interface.
        """
        # Verifica a camada raster selecionada no ComboBox
        selected_raster_id = self.comboBoxRaster.currentData()  # Obtém o ID da camada raster selecionada
        selected_raster_layer = QgsProject.instance().mapLayer(selected_raster_id)  # Busca a camada raster pelo ID

        # Verifica se a camada raster existe e é do tipo QgsRasterLayer
        if not selected_raster_layer or not isinstance(selected_raster_layer, QgsRasterLayer):
            self.pushButtonGerar.setEnabled(False)  # Desabilita o botão se a camada raster não for válida
            return

        # Verifica se a camada raster é um serviço de mapa (como WMS, XYZ, etc.)
        provider_name = selected_raster_layer.providerType().lower()
        if provider_name in ['wms', 'xyz', 'wcs', 'arcgisrest', 'google', 'bing']:
            self.pushButtonGerar.setEnabled(False)  # Desabilita o botão para camadas de serviço de mapa
            return

        # Verifica a camada de linhas selecionada no ComboBox
        selected_line_id = self.comboBoxLinhas.currentData()  # Obtém o ID da camada de linhas selecionada
        selected_line_layer = QgsProject.instance().mapLayer(selected_line_id)  # Busca a camada de linhas pelo ID

        # Verifica se a camada de linhas existe e contém feições
        if not selected_line_layer or selected_line_layer.featureCount() == 0:
            self.pushButtonGerar.setEnabled(False)  # Desabilita o botão se a camada de linhas não for válida ou não tiver feições
            return

        # Se todas as condições forem satisfeitas, habilita o botão "Gerar"
        self.pushButtonGerar.setEnabled(True)

    def verificar_selecao_linhas(self):
        """
        Verifica o estado da camada de linhas selecionada e ajusta o estado do botão "Gerar" e do checkbox de seleção.
        A função verifica se uma camada de linhas válida está selecionada e conecta sinais para atualizar o estado 
        conforme as feições são adicionadas, removidas ou selecionadas.

        Parâmetros:
        - self: Referência para a instância atual da classe (implícito), utilizada para acessar os atributos e métodos da classe.

        A função realiza as seguintes ações:
        - Obtém o ID da camada de linhas selecionada e verifica se é válido.
        - Verifica se a camada de linhas possui feições.
        - Conecta os sinais de seleção e alteração de feições para atualizar dinamicamente o estado do botão "Gerar" e do checkbox de seleção.
        
        Retorno:
        - Nenhum retorno explícito. A função altera diretamente o estado do botão "Gerar" e do checkbox de seleção na interface.
        """
        # Obtém o ID da camada de linhas selecionada
        selected_line_id = self.comboBoxLinhas.currentData()  # Obtém o ID da camada de linhas selecionada

        # Verifica se um ID de camada de linhas foi selecionado
        if not selected_line_id:
            # Se não houver uma camada de linhas válida, desabilita o botão "Gerar" e o checkbox de seleção
            self.pushButtonGerar.setEnabled(False)
            self.checkBoxSeleciona.setEnabled(False)
            return

        # Busca a camada de linhas pelo ID
        selected_layer = QgsProject.instance().mapLayer(selected_line_id)

        # Verifica se a camada de linhas existe
        if selected_layer is None:
            # Se a camada não existir, desabilita o botão "Gerar" e o checkbox de seleção
            self.pushButtonGerar.setEnabled(False)
            self.checkBoxSeleciona.setEnabled(False)
            return

        # Tenta desconectar o sinal anterior de mudança de seleção para evitar múltiplas conexões
        try:
            selected_layer.selectionChanged.disconnect(self.atualizar_estado_checkbox)
        except TypeError:
            pass  # nosec B110 | Nenhum sinal estava conectado anteriormente, então podemos continuar

        # Conecta o sinal de mudança de seleção de feições à função 'atualizar_estado_checkbox'
        selected_layer.selectionChanged.connect(self.atualizar_estado_checkbox)

        # Verifica se a camada de linhas contém feições
        if selected_layer.featureCount() == 0:
            # Se não houver feições na camada, desabilita o botão "Gerar" e o checkbox de seleção
            self.pushButtonGerar.setEnabled(False)
            self.checkBoxSeleciona.setEnabled(False)
        else:
            # Se houver feições, atualiza o estado do checkbox de seleção e do botão "Gerar"
            self.atualizar_estado_checkbox()

        # Conecta os sinais de adição e remoção de feições para atualizar o estado do botão "Gerar"
        selected_layer.featureAdded.connect(self.verificar_estado_pushButtonGerar)
        selected_layer.featureDeleted.connect(self.verificar_estado_pushButtonGerar)

    def atualizar_tooltip_comboBoxRaster(self):
        """
        Atualiza o tooltip (dica de ferramenta) do comboBox de camadas raster, exibindo o sistema de referência de coordenadas (SRC)
        da camada raster selecionada. Se nenhuma camada válida estiver selecionada, um aviso será exibido no tooltip.

        Parâmetros:
        - self: Referência para a instância atual da classe (implícito), utilizada para acessar os atributos e métodos da classe.

        A função realiza as seguintes ações:
        - Obtém a camada raster atualmente selecionada no ComboBox.
        - Se a camada for válida, exibe o código e a descrição do SRC (Sistema de Referência de Coordenadas).
        - Se a camada não for válida, exibe uma mensagem padrão informando que nenhuma camada raster foi selecionada.

        Retorno:
        - Nenhum retorno explícito. A função altera diretamente o tooltip do ComboBox de camadas raster na interface.
        """
        # Obtém o ID da camada raster selecionada no ComboBox
        selected_raster_id = self.comboBoxRaster.currentData()

        # Busca a camada raster pelo ID
        selected_raster_layer = QgsProject.instance().mapLayer(selected_raster_id)

        # Verifica se a camada raster foi encontrada
        if selected_raster_layer:
            # Obtém o SRC da camada raster (Sistema de Referência de Coordenadas)
            crs = selected_raster_layer.crs()

            # Atualiza o tooltip com o código do SRC e a descrição
            self.comboBoxRaster.setToolTip(self.tr("SRC: {authid} - {description}").format(authid=crs.authid(), description=crs.description()))
        else:
            # Se nenhuma camada válida foi selecionada, exibe uma mensagem padrão
            self.comboBoxRaster.setToolTip(self.tr("Nenhuma camada raster selecionada"))

    def atualizar_tooltip_comboBoxLinhas(self):
        """
        Atualiza o tooltip (dica de ferramenta) do comboBox de camadas de linhas, exibindo o sistema de referência de coordenadas (SRC)
        da camada de linhas selecionada. Se nenhuma camada válida estiver selecionada, um aviso será exibido no tooltip.

        Parâmetros:
        - self: Referência para a instância atual da classe (implícito), utilizada para acessar os atributos e métodos da classe.

        A função realiza as seguintes ações:
        - Obtém a camada de linhas atualmente selecionada no ComboBox.
        - Se a camada for válida, exibe o código e a descrição do SRC (Sistema de Referência de Coordenadas).
        - Se a camada não for válida, exibe uma mensagem padrão informando que nenhuma camada de linhas foi selecionada.

        Retorno:
        - Nenhum retorno explícito. A função altera diretamente o tooltip do ComboBox de camadas de linhas na interface.
        """
        # Obtém o ID da camada de linhas selecionada no ComboBox
        selected_line_id = self.comboBoxLinhas.currentData()

        # Busca a camada de linhas pelo ID
        selected_line_layer = QgsProject.instance().mapLayer(selected_line_id)

        # Verifica se a camada de linhas foi encontrada
        if selected_line_layer:
            # Obtém o SRC da camada de linhas (Sistema de Referência de Coordenadas)
            crs = selected_line_layer.crs()

            # Atualiza o tooltip com o código do SRC e a descrição
            self.comboBoxLinhas.setToolTip(self.tr("SRC: {authid} - {description}").format(authid=crs.authid(), description=crs.description()))
        else:
            # Se nenhuma camada válida foi selecionada, exibe uma mensagem padrão
            self.comboBoxLinhas.setToolTip(self.tr("Nenhuma camada de linhas selecionada"))

    def closeEvent(self, event):
        """
        Sobrescreve o método `closeEvent` para garantir que, ao fechar o diálogo, a referência para o mesmo seja removida
        do widget pai, evitando problemas de múltiplas instâncias abertas.

        Parâmetros:
        - self: Referência para a instância atual da classe (implícito), utilizada para acessar os atributos e métodos da classe.
        - event (QCloseEvent): O evento de fechamento da janela (gerado automaticamente pelo sistema quando o diálogo é fechado).

        A função realiza as seguintes ações:
        - Obtém o widget pai, se houver, e define sua referência para o diálogo de setas como `None`.
        - Chama o método `closeEvent` da superclasse para garantir o comportamento normal de fechamento do diálogo.

        Retorno:
        - Nenhum retorno explícito. A função trata o fechamento da janela e a limpeza de referências para evitar duplicações.
        """
        # Obtém o widget pai, se houver
        parent = self.parent()

        # Se houver um widget pai, remove a referência do diálogo setasraster_dlg
        if parent:
            parent.setasraster_dlg = None

        # Chama o método closeEvent da superclasse (QDialog) para garantir o comportamento padrão de fechamento
        super(SetasManager, self).closeEvent(event)

    def close_dialog(self):
        """
        Fecha o diálogo de maneira programática, chamando o método `close` da instância do diálogo.

        Parâmetros:
        - self: Referência para a instância atual da classe (implícito), utilizada para acessar os atributos e métodos da classe.

        A função realiza as seguintes ações:
        - Chama o método `close` da instância do diálogo, encerrando a exibição do diálogo e disparando o evento de fechamento.

        Retorno:
        - Nenhum retorno explícito. A função apenas encerra a exibição do diálogo chamando o método `close`.
        """
        # Fecha o diálogo chamando o método close
        self.close()

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
            "Salvar Camada",
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

    def exportar_rotulo_feature(self, msp, feature, current_scale):
        """
        Adiciona um rótulo exportado para o DXF (usando MTEXT com fonte Arial) para a feição,
        calculando o tamanho (0,1% da escala), posição e rotação com base no segmento de maior comprimento.
        O texto do rótulo é definido a partir do atributo "Inclinacao" (sem setas) e a cor é determinada conforme o padrão.
        O rótulo será posicionado acima da linha, garantindo que o deslocamento tenha componente Y positiva.
        """
        geom = feature.geometry()
        if not geom or geom.isEmpty():
            return

        # Seleciona o segmento de maior comprimento:
        if geom.isMultipart():
            polylines = geom.asMultiPolyline()
            longest_line = None
            max_length = 0
            for line in polylines:
                if len(line) < 2:
                    continue
                line_geom = QgsGeometry.fromPolylineXY(line)
                length = line_geom.length()
                if length > max_length:
                    max_length = length
                    longest_line = line
        else:
            longest_line = geom.asPolyline()

        if not longest_line or len(longest_line) < 2:
            return

        # Calcula o ponto médio do segmento de maior comprimento:
        total_length = 0
        segments = []
        for i in range(len(longest_line) - 1):
            seg_length = QgsGeometry.fromPolylineXY([longest_line[i], longest_line[i+1]]).length()
            segments.append(seg_length)
            total_length += seg_length

        midpoint_distance = total_length / 2.0
        cum_length = 0
        seg_index = 0
        for i, seg in enumerate(segments):
            cum_length += seg
            if cum_length >= midpoint_distance:
                seg_index = i
                break

        pt1 = longest_line[seg_index]
        pt2 = longest_line[seg_index + 1]
        # Ponto médio do segmento selecionado
        mid_point = ((pt1.x() + pt2.x()) / 2.0, (pt1.y() + pt2.y()) / 2.0)

        # Calcula o vetor do segmento e o ângulo para a rotação
        dx = pt2.x() - pt1.x()
        dy = pt2.y() - pt1.y()
        angle_rad = math.atan2(dy, dx)
        angle_deg = math.degrees(angle_rad)
        # Ajusta o ângulo para manter o texto legível:
        if angle_deg > 90:
            angle_deg -= 180
        elif angle_deg < -90:
            angle_deg += 180

        # Calcula o vetor normal à esquerda (relativo à direção do segmento)
        length = math.hypot(dx, dy)
        if length != 0:
            normal = (-dy / length, dx / length)
        else:
            normal = (0, 0)

        # Força o vetor normal a ter componente Y positiva, garantindo que o rótulo fique "acima" da linha
        if normal[1] < 0:
            normal = (-normal[0], -normal[1])

        # Define o tamanho do texto: 0,1% da escala atual 
        char_height = current_scale * 0.003
        # Define um deslocamento (por exemplo, 1.2 vezes o tamanho do caractere) para posicionar o texto acima da linha
        offset_distance = char_height * 1.2
        # Calcula a nova posição, deslocando o ponto médio pelo vetor normal
        new_mid_point = (mid_point[0] + normal[0] * offset_distance, mid_point[1] + normal[1] * offset_distance)

        # Determina o texto do rótulo com base na "Inclinacao" (sem setas)
        try:
            inclinacao = float(feature["Inclinacao"])
        except (TypeError, ValueError):
            inclinacao = 0.0
        label_text = f"{round(inclinacao, 3)}%"

        # Define a cor para o texto:
        if self.cor_seta:
            color = self.cor_seta
            true_color = (color.red() << 16) | (color.green() << 8) | color.blue()
        else:
            if inclinacao < 0:
                true_color = 0xFF0000  # Vermelho
            elif inclinacao > 0:
                true_color = 0x0000FF  # Azul
            else:
                true_color = 0x000000  # Preto

        # Adiciona a entidade MTEXT usando o atributo "char_height" e o estilo "Arial"
        mtext = msp.add_mtext(label_text, dxfattribs={
            'layer': 'SETAS',
            'char_height': char_height,
            'true_color': true_color,
            'style': 'Arial'})
        mtext.set_location(new_mid_point)
        mtext.dxf.rotation = angle_deg

    def exportar_para_dxf(self):
        """
        Exporta a camada de linha gerada (armazenada em self.exploded_layer) para um arquivo DXF,
        utilizando ezdxf para criar o desenho. As polilinhas são exportadas com a cor definida e os rótulos
        (MTEXT em Arial) são posicionados e rotacionados com base no segmento de maior comprimento de cada feição,
        com tamanho definido como 0,1% da escala atual.
        """
        # Verifica se a camada gerada existe e foi criada pelo pushButtonGerar
        if not hasattr(self, 'exploded_layer') or self.exploded_layer is None:
            self.mostrar_mensagem(self.tr("Nenhuma camada de linha gerada para exportação."), "Erro")
            return

        if self.exploded_layer.customProperty("gerado_por") != "pushButtonGerar":
            self.mostrar_mensagem(self.tr("A camada selecionada não foi gerada pelo pushButtonGerar."), "Erro")
            return

        # Define o nome padrão e o filtro para arquivos DXF
        nome_padrao = self.exploded_layer.name() + ".dxf"
        tipo_arquivo = self.tr("Arquivos DXF (*.dxf)")

        fileName = self.escolher_local_para_salvar(nome_padrao, tipo_arquivo)
        if not fileName:
            return  # Usuário cancelou a operação

        try:
            import ezdxf
        except ImportError:
            self.mostrar_mensagem(self.tr("Biblioteca ezdxf não encontrada. Verifique sua instalação."), "Erro")
            return

        # Cria um novo desenho DXF no padrão R2010
        doc = ezdxf.new('R2013')

        # Garante que o estilo "Arial" esteja definido; use dxfattribs para definir a fonte:
        if "Arial" not in doc.styles:
            doc.styles.new("Arial", dxfattribs={"font": "arial.ttf"})

        msp = doc.modelspace()

        # Cria (ou garante) a camada DXF "SETAS"
        dxf_layer_name = self.tr("SETAS")
        if dxf_layer_name not in doc.layers:
            doc.layers.new(dxf_layer_name, dxfattribs={'color': 7})

        progressBar, progressMessageBar = self.iniciar_progress_bar(self.exploded_layer)
        current = 0

        # Exporta as polilinhas
        for feature in self.exploded_layer.getFeatures():
            geom = feature.geometry()
            if not geom or geom.isEmpty():
                continue

            if geom.isMultipart():
                polylines = geom.asMultiPolyline()
            else:
                polylines = [geom.asPolyline()]

            # Define a cor para a linha (usando a mesma lógica dos rótulos)
            if self.cor_seta:
                color = self.cor_seta
                true_color = (color.red() << 16) | (color.green() << 8) | color.blue()
            else:
                try:
                    inclinacao = float(feature["Inclinacao"])
                except (TypeError, ValueError):
                    inclinacao = 0.0
                if inclinacao < 0:
                    true_color = 0xFF0000
                elif inclinacao > 0:
                    true_color = 0x0000FF
                else:
                    true_color = 0x000000

            for line in polylines:
                points = [(pt.x(), pt.y()) for pt in line]
                if len(points) < 2:
                    continue
                msp.add_lwpolyline(points, dxfattribs={'layer': dxf_layer_name, 'true_color': true_color})

            current += 1
            progressBar.setValue(current)

        progressBar.setValue(progressBar.maximum())
        self.iface.messageBar().popWidget(progressMessageBar)

        # Obtém a escala atual para definir o tamanho dos rótulos
        current_scale = self.iface.mapCanvas().scale()

        # Exporta os rótulos para cada feição usando a função dedicada
        for feature in self.exploded_layer.getFeatures():
            self.exportar_rotulo_feature(msp, feature, current_scale)

        try:
            doc.saveas(fileName)
            pasta = os.path.dirname(fileName)
            self.mostrar_mensagem(self.tr("Camada exportada com sucesso para DXF."), "Sucesso", caminho_pasta=pasta, caminho_arquivo=fileName)

        except Exception as e:
            self.mostrar_mensagem(self.tr("Erro ao salvar o arquivo DXF: {error}").format(error=str(e)), "Erro")

    def atualizar_estado_pushButtonExportarDXF(self):
        """
        Habilita o pushButtonExportarDXF somente se a camada gerada pelo pushButtonGerar existir
        e tiver a propriedade custom 'gerado_por' definida corretamente.
        """
        if (hasattr(self, 'exploded_layer') and 
            self.exploded_layer is not None and 
            self.exploded_layer.customProperty("gerado_por") == "pushButtonGerar"):
            self.pushButtonExportarDXF.setEnabled(True)
        else:
            self.pushButtonExportarDXF.setEnabled(False)