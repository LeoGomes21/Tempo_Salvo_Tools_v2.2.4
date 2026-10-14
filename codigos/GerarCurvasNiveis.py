from qgis.core import QgsProject, QgsRasterLayer, QgsMapSettings, QgsMapRendererCustomPainterJob, Qgis, QgsMessageLog, QgsVectorLayer, QgsField, QgsSymbol, QgsRendererCategory, QgsCategorizedSymbolRenderer, QgsPalLayerSettings, QgsVectorLayerSimpleLabeling, QgsTextFormat, QgsProperty, QgsFeature, QgsWkbTypes, QgsProcessingFeedback, QgsPoint, QgsGeometry, QgsCoordinateReferenceSystem, QgsFields, QgsPropertyCollection, QgsCoordinateTransform, QgsPointXY
from qgis.PyQt.QtWidgets import QDialog, QCheckBox, QComboBox, QPushButton, QGraphicsView, QGraphicsScene, QGraphicsPixmapItem, QSpinBox, QFileDialog, QMenu, QAction, QProgressBar, QLabel, QVBoxLayout
from qgis.PyQt.QtCore import Qt, QRectF, QPointF, QSize, QVariant, QSettings, QMetaType, QCoreApplication, QUrl
from qgis.PyQt.QtGui import QImage, QPainter, QPixmap, QColor, QDesktopServices
from qgis.PyQt import QtCore, QtGui, QtWidgets, uic
from qgis.gui import QgsMapCanvas
from qgis.utils import iface
import processing
import tempfile
import ezdxf
import time
import math
import os

FORM_CLASS, _ = uic.loadUiType(os.path.join(
    os.path.dirname(__file__), 'GerarCurvas.ui'))

class CurvasManager(QDialog, FORM_CLASS):
    def __init__(self, parent=None):
        """
        Construtor da classe CurvasManager.

        Parâmetros:
        - parent (QWidget, opcional): O widget pai para este diálogo, padrão é None.

        Funcionalidades:
        - Inicializa a interface do usuário a partir do Designer.
        - Define o título da janela como "Gerar Curvas de Níveis 3D".
        - Cria uma cena gráfica para exibir o raster no QGraphicsView.
        - Inicializa o ComboBox de seleção de camada raster.
        - Inicializa o SpinBox para definir a escala.
        - Conecta sinais a slots para responder a eventos da interface.
        - Define valores padrão para as configurações de curvas de nível, como cores, posição de rótulos, desnível, tamanho e repetição.
        """
        super(CurvasManager, self).__init__(parent)

        # Configura a interface do usuário a partir do Designer.
        self.setupUi(self)

        # Altera o título da janela
        self.setWindowTitle(self.tr("Gerar Curvas de Níveis 3D"))

        # Armazena a referência da interface QGIS
        self.iface = iface

        # Cria uma cena gráfica para o QGraphicsView
        self.scene = QGraphicsScene()
        self.graphicsViewRaster.setScene(self.scene)

        # Inicializa o ComboBox de Raster
        self.init_combo_box_raster()

        # Inicializa o SpinBox de Escala
        self.init_spin_box_escala()

        # Conecta os sinais aos slots
        self.connect_signals()

        # Inicializa as configurações com valores padrão
        self.selected_colors = {}
        self.selected_position = 'Centro'  # Posição padrão do rótulo (Centro)
        self.desnivel_m = 5  # Desnível Mestre padrão
        self.desnivel_s = 0.5  # Desnível Simples padrão
        self.tamanho = 8  # Tamanho padrão do texto
        self.repeticao = 100  # Repetição padrão dos rótulos

        self.curves_layer_id = None  # guarda só o ID da camada de curvas

        # Mantém referência da última mensagem exibida por este diálogo.
        self._mensagem_atual = None

    def tr(self, message):
        """
        Traduz textos deste diálogo.
        O contexto precisa ser estável para o Qt Linguist encontrar as traduções.
        """
        return QtCore.QCoreApplication.translate("CurvasManager", message)

    def closeEvent(self, event):
        """
        Evento acionado quando o diálogo é fechado.

        Parâmetros:
        - event (QCloseEvent): O evento de fechamento que será tratado.

        Funcionalidades:
        - Verifica se há um widget pai associado e, se houver, define a referência 
          do diálogo de curvas no pai como None.
        - Chama o método closeEvent da superclasse para garantir que o evento de fechamento 
          seja corretamente processado.
        """
        # Verifica se existe um widget pai associado ao diálogo
        parent = self.parent()

        # Se o widget pai existir, redefine a referência do diálogo de curvas para None
        if parent:
            parent.curvas_dlg = None

        # Chama o evento de fechamento da superclasse para garantir o fechamento correto
        super(CurvasManager, self).closeEvent(event)

    def connect_signals(self):
        """
        Conecta os sinais (eventos) da interface do usuário aos respectivos slots (funções de resposta).

        Funcionalidades:
        - Conecta as mudanças de seleção no ComboBox de raster para atualizar a exibição do raster e o status do botão de curvas.
        - Conecta o evento de remoção de camada no QGIS para atualizar o ComboBox de camadas.
        - Conecta o evento de adição de camada no QGIS para lidar com novas camadas adicionadas ao projeto.
        - Conecta o evento de mudança de escala no QGIS para atualizar o valor do SpinBox de escala.
        - Conecta o SpinBox de escala para atualizar a escala no QGIS quando alterado.
        - Conecta o botão de gerar curvas de nível ao método de geração de curvas.
        - Conecta o botão de exportação para DXF ao método de exportação.
        - Conecta o botão de cancelar para fechar o diálogo.
        - Conecta o botão de configurações para abrir o diálogo de configuração.
        - Conecta o sinal de alteração de nome das camadas para atualizar o ComboBox de camadas quando uma camada for renomeada.
        """
        # Conecta a mudança de seleção no ComboBox de raster para atualizar o raster exibido
        self.comboBoxRaster.currentIndexChanged.connect(self.display_raster)
        self.comboBoxRaster.currentIndexChanged.connect(self.check_push_button_curvas_status)

        # Conecta o sinal de remoção de camadas para atualizar o ComboBox
        QgsProject.instance().layersRemoved.connect(self.update_combo_box)

        # Conecta o sinal de adição de camadas para atualizar o ComboBox
        QgsProject.instance().layersAdded.connect(self.handle_layers_added)

        # Conecta o evento de mudança de escala no QGIS para atualizar o SpinBox de escala
        iface.mapCanvas().scaleChanged.connect(self.update_spin_box_from_scale)

        # Conecta a mudança no SpinBox de escala para atualizar a escala do QGIS
        self.spinBoxEscala.valueChanged.connect(self.update_scale_from_spin_box)

        # Conecta o botão de gerar curvas de nível ao método de geração de curvas
        self.pushButtonCurvas.clicked.connect(self.generate_contour_lines)

        # Conecta o botão de exportar para DXF ao método de exportação para DXF
        self.pushButtonDXF.clicked.connect(self.export_to_dxf)

        # Conecta o botão de cancelamento ao fechamento do diálogo
        self.pushButtonCancelar.clicked.connect(self.close)

        # Conecta o botão de configuração ao método que abre o diálogo de configurações
        self.pushButtonConfig.clicked.connect(self.open_config_dialog)

        # Conecta o sinal de alteração de nome de camada para atualizar o ComboBox quando o nome da camada mudar
        for layer in QgsProject.instance().mapLayers().values():
            layer.nameChanged.connect(self.update_combo_box)

    def update_combo_box(self):
        """
        Atualiza o ComboBox de camadas raster quando camadas são adicionadas, removidas ou renomeadas.

        Parâmetros:
        - Nenhum parâmetro explícito é passado diretamente para esta função, mas ela acessa e manipula os seguintes atributos da classe:
          - self.comboBoxRaster: O ComboBox que contém as camadas raster disponíveis no projeto.
          - self.init_combo_box_raster(): Função que inicializa ou reinicializa o ComboBox com as camadas raster atuais.
          - self.display_raster(): Função que atualiza a exibição gráfica do raster selecionado no QGraphicsView.
          - self.check_push_button_dxf_status(): Função que verifica se o botão de exportação para DXF deve ser habilitado.

        Funcionalidades:
        - Armazena o índice e ID da camada raster atualmente selecionada.
        - Atualiza a lista de camadas no ComboBox de raster.
        - Tenta restaurar a seleção anterior após a atualização.
        - Se a camada selecionada anteriormente não estiver disponível, seleciona a primeira camada disponível.
        - Atualiza a exibição do raster e verifica o status do botão de exportação para DXF.
        """
        # Armazena o índice e o ID da camada atualmente selecionada no ComboBox
        current_index = self.comboBoxRaster.currentIndex()
        current_layer_id = self.comboBoxRaster.itemData(current_index)

        # Atualiza o ComboBox de raster quando camadas são adicionadas ou removidas
        self.init_combo_box_raster()

        # Tenta restaurar a seleção anterior após a atualização
        if current_layer_id:
            index = self.comboBoxRaster.findData(current_layer_id)
            if index != -1:
                # Restaura a seleção anterior se a camada ainda estiver presente
                self.comboBoxRaster.setCurrentIndex(index)
            else:
                # Se a camada não existir mais, seleciona a primeira disponível no ComboBox
                if self.comboBoxRaster.count() > 0:
                    self.comboBoxRaster.setCurrentIndex(0)
                    self.display_raster()

        # Verifica o status do botão DXF, ativando ou desativando-o conforme necessário
        self.check_push_button_dxf_status()

    def init_combo_box_raster(self):
        """
        Inicializa o ComboBox de camadas raster disponíveis no projeto.

        Parâmetros:
        - Nenhum parâmetro explícito é passado diretamente para esta função, mas ela acessa e manipula os seguintes atributos da classe:
          - self.comboBoxRaster: O ComboBox que contém as camadas raster disponíveis no projeto.
          - self.check_push_button_curvas_status(): Função que verifica se o botão de geração de curvas deve ser habilitado.
          - self.display_raster(): Função que atualiza a exibição gráfica do raster selecionado no QGraphicsView.
          - self.pushButtonCurvas: O botão que inicia a geração de curvas de nível.
          - self.check_push_button_dxf_status(): Função que verifica se o botão de exportação para DXF deve ser habilitado.

        Funcionalidades:
        - Obtém todas as camadas do projeto atual e filtra apenas as camadas raster.
        - Limpa o ComboBox de camadas raster e adiciona as camadas filtradas.
        - Se houver camadas raster disponíveis, ativa o ComboBox e o botão de curvas e exibe o raster selecionado.
        - Se não houver camadas raster, desativa o ComboBox e o botão de curvas.
        - Verifica se a camada "Curva de Níveis 3D" está presente para habilitar ou desabilitar o botão de exportação para DXF.
        """
        # Obtém todas as camadas do projeto atual
        layers = QgsProject.instance().mapLayers().values()
        
        # Filtra apenas as camadas do tipo raster
        raster_layers = [layer for layer in layers if layer.type() == Qgis.LayerType.Raster]
        
        # Limpa o ComboBox antes de adicionar as camadas raster
        self.comboBoxRaster.clear()

        # Adiciona as camadas raster disponíveis ao ComboBox
        for raster_layer in raster_layers:
            self.comboBoxRaster.addItem(raster_layer.name(), raster_layer.id())

        # Verifica se há camadas raster disponíveis
        if raster_layers:
            # Define a primeira camada como selecionada e ativa o ComboBox
            self.comboBoxRaster.setCurrentIndex(0)
            self.comboBoxRaster.setEnabled(True)

            # Verifica o status do botão de curvas e exibe o raster selecionado
            self.check_push_button_curvas_status()
            self.display_raster()
        else:
            # Desativa o ComboBox e o botão de curvas se não houver camadas raster
            self.comboBoxRaster.setEnabled(False)
            self.pushButtonCurvas.setEnabled(False)

        # Verifica a presença da camada "Curva de Níveis 3D" para habilitar o botão de exportação para DXF
        self.check_push_button_dxf_status()

    def check_push_button_curvas_status(self):
        """
        Verifica se o botão de geração de curvas de nível (pushButtonCurvas) deve estar habilitado ou desabilitado.

        Parâmetros:
        - Nenhum parâmetro explícito é passado diretamente para esta função, mas ela acessa e manipula os seguintes atributos da classe:
          - self.comboBoxRaster: ComboBox que contém as camadas raster do projeto.
          - self.pushButtonCurvas: O botão responsável por iniciar a geração de curvas de nível.

        Funcionalidades:
        - Obtém a camada raster atualmente selecionada no ComboBox.
        - Verifica se a camada selecionada é válida e se é uma camada raster suportada.
        - Desabilita o botão de curvas de nível caso a camada não seja válida ou seja proveniente de fontes de imagens como WMS, XYZ, Google, Bing, etc.
        - Habilita o botão de curvas de nível para camadas raster locais ou suportadas.
        """
        # Obtém o ID da camada raster selecionada no ComboBox
        selected_raster_id = self.comboBoxRaster.currentData()
        selected_layer = QgsProject.instance().mapLayer(selected_raster_id)

        # Se não houver nenhuma camada selecionada, desabilita o botão de curvas
        if selected_layer is None:
            self.pushButtonCurvas.setEnabled(False)
            return

        # Verifica se a camada selecionada é do tipo QgsRasterLayer (camada raster)
        if isinstance(selected_layer, QgsRasterLayer):
            provider_name = selected_layer.providerType().lower()

            # Desabilita o botão de curvas para camadas provenientes de fontes online como WMS, XYZ, etc.
            if provider_name in ['wms', 'xyz', 'wcs', 'arcgisrest', 'google', 'bing']:  # Adaptável conforme necessário
                self.pushButtonCurvas.setEnabled(False)
            else:
                # Habilita o botão de curvas para camadas raster locais ou suportadas
                self.pushButtonCurvas.setEnabled(True)
        else:
            # Se a camada selecionada não for do tipo raster, desabilita o botão de curvas
            self.pushButtonCurvas.setEnabled(False)

    def check_push_button_dxf_status(self):
        """
        Verifica se o botão de exportação para DXF (pushButtonDXF) deve estar habilitado ou desabilitado.

        Parâmetros:
        - Nenhum parâmetro explícito é passado diretamente para esta função, mas ela acessa e manipula os seguintes atributos da classe:
          - self.pushButtonDXF: O botão que permite a exportação da camada "Curva de Níveis 3D" para o formato DXF.

        Funcionalidades:
        - Verifica se existe uma camada chamada "Curva de Niveis 3D" no projeto atual.
        - Se a camada "Curva de Niveis 3D" for encontrada, o botão de exportação para DXF é habilitado.
        - Caso contrário, o botão de exportação para DXF é desabilitado.
        """
        # Nome da camada de curvas de nível 3D que será verificada
        layer_name = self.tr("Curva de Niveis 3D")

        # Verifica se existe uma camada com o nome "Curva de Niveis 3D" no projeto
        layer_found = any(layer.name() == layer_name for layer in QgsProject.instance().mapLayers().values())

        # Habilita o botão DXF se a camada for encontrada, caso contrário, desabilita
        if layer_found:
            self.pushButtonDXF.setEnabled(True)
        else:
            self.pushButtonDXF.setEnabled(False)

    def display_raster(self):
        """
        Renderiza a camada raster selecionada no QGraphicsView.

        Parâmetros:
        - Nenhum parâmetro explícito é passado diretamente para esta função, mas ela acessa e manipula os seguintes atributos da classe:
          - self.comboBoxRaster: O ComboBox que contém as camadas raster disponíveis no projeto.
          - self.scene: A cena gráfica (QGraphicsScene) usada para exibir o raster no QGraphicsView.
          - self.graphicsViewRaster: O widget QGraphicsView onde o raster será renderizado.

        Funcionalidades:
        - Limpa a cena gráfica antes de adicionar um novo item.
        - Obtém a camada raster selecionada no ComboBox e, se válida, configura as definições de mapa e de renderização.
        - Define o tamanho da imagem a ser renderizada com base nas dimensões do QGraphicsView.
        - Renderiza a camada raster como uma imagem e a adiciona à cena gráfica.
        - Ajusta a visualização da cena no QGraphicsView, preservando a proporção do raster.
        """
        # Limpa a cena antes de adicionar um novo item
        self.scene.clear()

        # Obtém o ID da camada raster selecionada
        selected_raster_id = self.comboBoxRaster.currentData()

        # Busca a camada raster pelo ID
        selected_layer = QgsProject.instance().mapLayer(selected_raster_id)
        
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
        Método acionado quando o diálogo é exibido pela primeira vez.

        Parâmetros:
        - event (QShowEvent): O evento de exibição que será tratado quando o diálogo for mostrado.

        Funcionalidades:
        - Chama o método `showEvent` da superclasse para garantir o comportamento padrão.
        - Ajusta a visualização do raster quando o diálogo é exibido, garantindo que o raster seja renderizado corretamente na interface.
        """
        # Chama o evento showEvent da superclasse para manter o comportamento padrão de exibição
        super(CurvasManager, self).showEvent(event)

        # Ajusta a visualização do raster quando o diálogo é mostrado
        self.display_raster()

    def handle_layers_added(self, layers):
        """
        Manipula o evento de adição de novas camadas no projeto.

        Parâmetros:
        - layers (list): Lista de camadas que foram adicionadas ao projeto.

        Funcionalidades:
        - Quando novas camadas são adicionadas ao projeto, esta função chama o método `update_combo_box` 
          para atualizar o ComboBox de seleção de camadas raster, garantindo que as novas camadas sejam incluídas.
        """
        # Chama a função de atualização do ComboBox quando novas camadas são adicionadas
        self.update_combo_box()

    def init_spin_box_escala(self):
        """
        Inicializa o SpinBox de escala, configurando seus limites e valor inicial com base na escala atual do projeto.

        Parâmetros:
        - Nenhum parâmetro explícito é passado diretamente para esta função, mas ela acessa e manipula os seguintes atributos da classe:
          - self.spinBoxEscala: O SpinBox responsável por ajustar a escala do mapa.

        Funcionalidades:
        - Define os limites de valor mínimo e máximo para o SpinBox de escala.
        - Define o incremento do SpinBox para facilitar o ajuste de valores.
        - Obtém a escala atual do projeto e configura o valor inicial do SpinBox com base nessa escala.
        - Bloqueia e desbloqueia sinais temporariamente para evitar loops de atualização desnecessários ao definir o valor inicial.
        """
        # Define os limites do spinBoxEscala (mínimo de 1 e máximo de 1.000.000)
        self.spinBoxEscala.setRange(1, 1000000)  # Ajuste conforme a necessidade do projeto

        # Define o incremento (passo) do SpinBox para 100 unidades
        self.spinBoxEscala.setSingleStep(100)

        # Obtém a escala atual do projeto
        current_scale = self.get_current_scale()

        # Configura o valor inicial do SpinBox com a escala atual do projeto
        self.spinBoxEscala.setValue(current_scale)

        # Bloqueia sinais para evitar loops de atualização ao definir o valor
        self.spinBoxEscala.blockSignals(True)
        self.spinBoxEscala.setValue(current_scale)
        self.spinBoxEscala.blockSignals(False)  # Desbloqueia os sinais após definir o valor

    def get_current_scale(self):
        """
        Obtém a escala atual do mapa exibido no QGIS.

        Parâmetros:
        - Nenhum parâmetro explícito é passado diretamente para esta função.

        Retorno:
        - int: A escala atual do mapa como um valor inteiro.

        Funcionalidades:
        - Utiliza a interface do QGIS (iface) para acessar o canvas do mapa e retornar o valor da escala atual.
        """
        # Retorna a escala atual do mapa como um valor inteiro
        return int(iface.mapCanvas().scale())

    def update_spin_box_from_scale(self):
        """
        Atualiza o valor do SpinBox de escala com base na escala atual do mapa no QGIS.

        Parâmetros:
        - Nenhum parâmetro explícito é passado diretamente para esta função, mas ela acessa e manipula os seguintes atributos da classe:
          - self.spinBoxEscala: O SpinBox que exibe e ajusta a escala do mapa.

        Funcionalidades:
        - Obtém a escala atual do QGIS e atualiza o SpinBox para refletir esse valor.
        - Bloqueia temporariamente os sinais do SpinBox para evitar loops de atualização ao ajustar o valor.
        """
        # Obtém a escala atual do mapa no QGIS
        current_scale = self.get_current_scale()

        # Bloqueia os sinais do SpinBox para evitar loops de atualização
        self.spinBoxEscala.blockSignals(True)

        # Atualiza o valor do SpinBox com a escala atual do mapa
        self.spinBoxEscala.setValue(current_scale)

        # Desbloqueia os sinais após a atualização do valor
        self.spinBoxEscala.blockSignals(False)

    def update_scale_from_spin_box(self):
        """
        Atualiza a escala do mapa no QGIS com base no valor do SpinBox de escala.

        Parâmetros:
        - Nenhum parâmetro explícito é passado diretamente para esta função, mas ela acessa e manipula os seguintes atributos da classe:
          - self.spinBoxEscala: O SpinBox que contém o valor da nova escala para o mapa.

        Funcionalidades:
        - Obtém o valor atual do SpinBox de escala e o compara com a escala atual do mapa no QGIS.
        - Aplica lógica de inversão de escala quando necessário (para evitar valores inválidos de escala).
        - Atualiza a escala do mapa no QGIS, se o novo valor for diferente do valor atual e maior que 0.
        """
        # Obtém o novo valor de escala do SpinBox
        new_scale = self.spinBoxEscala.value()

        # Obtém a escala atual do mapa no QGIS
        current_scale = self.get_current_scale()

        # Lógica para inverter a escala corretamente
        if new_scale == 1 and current_scale != 1:
            # Quando o valor no SpinBox é 1, ajusta para 100 vezes o valor atual
            new_scale = current_scale * 100
        elif current_scale == 1 and new_scale != 1:
            # Se a escala atual é 1, ajusta para evitar a escala 1:0 (inválida)
            new_scale = new_scale // 100 if new_scale >= 100 else 1

        # Atualiza a escala do mapa, evitando atualizações desnecessárias
        if new_scale != current_scale and new_scale > 0:
            iface.mapCanvas().zoomScale(new_scale)

    def create_memory_layer(self, layer_name, geometry_type, crs, is_3d=False):
        """
        Cria e retorna uma camada vetorial em memória, com a opção de incluir geometria 3D.

        Parâmetros:
        - layer_name (str): O nome da camada que será criada.
        - geometry_type (str): O tipo de geometria da camada, como 'Point', 'LineString', ou 'Polygon'.
        - crs (str): O sistema de referência de coordenadas (SRC) da camada, especificado como um identificador (ex. 'EPSG:4326').
        - is_3d (bool, opcional): Indica se a geometria da camada deve incluir coordenadas Z (3D). O padrão é False.

        Retorno:
        - QgsVectorLayer: A camada em memória criada com o tipo de geometria e SRC especificados.

        Funcionalidades:
        - Cria uma camada vetorial em memória no formato especificado (2D ou 3D).
        - Define explicitamente o sistema de referência de coordenadas (SRC) da nova camada.
        """
        # Define o sufixo 'Z' para a geometria caso a camada seja 3D
        geometry_with_z = 'Z' if is_3d else ''

        # Cria a camada vetorial em memória com o tipo de geometria e SRC especificados
        layer = QgsVectorLayer(f"{geometry_type}{geometry_with_z}?crs={crs}", layer_name, "memory")
        
        # Define explicitamente o SRC da camada usando o sistema de referência fornecido
        layer.setCrs(QgsCoordinateReferenceSystem(crs))
        
        # Retorna a camada criada
        return layer

    def generate_contour_lines(self):
        """
        Gera curvas de nível a partir da camada raster selecionada e aplica personalizações.

        Parâmetros:
        - Nenhum parâmetro explícito é passado diretamente para esta função, mas ela acessa e manipula os seguintes atributos da classe:
          - self.comboBoxRaster: O ComboBox que contém as camadas raster disponíveis no projeto.
          - self.desnivel_s: O intervalo de desnível para gerar as curvas de nível.
          - self.iface: A interface QGIS para exibir mensagens e barras de progresso.
          - self.mostrar_mensagem(): Método para exibir mensagens ao usuário.

        Funcionalidades:
        - Verifica se uma camada raster válida está selecionada no ComboBox.
        - Configura e executa o algoritmo de geração de curvas de nível com base na camada raster selecionada.
        - Exibe uma barra de progresso enquanto as curvas de nível são geradas.
        - Se a geração for bem-sucedida, cria e adiciona uma camada de curvas de nível ao projeto.
        - Aplica configurações adicionais e personalizadas à nova camada.
        - Exibe mensagens ao usuário sobre o progresso e o resultado da operação.
        """
        # Obtém o ID da camada raster selecionada no ComboBox
        selected_raster_id = self.comboBoxRaster.currentData()
        selected_layer = QgsProject.instance().mapLayer(selected_raster_id)

        # Verifica se a camada selecionada é uma camada raster válida
        if not isinstance(selected_layer, QgsRasterLayer):
            self.mostrar_mensagem(self.tr("Nenhuma camada raster selecionada ou a camada não é um raster."),  "Erro")
            return

        # Configurações para a geração de curvas de nível
        contour_interval = self.desnivel_s  # Usa o valor armazenado do spinBoxDmestras
        output_layer_name = self.tr("Curvas de Nível - {layer_name}").format(layer_name=selected_layer.name())

        # Cria o parâmetro para o processamento
        params = {
            'INPUT': selected_layer,   # <— evita problemas com fontes/VSIs
            'BAND': 1,
            'INTERVAL': self.desnivel_s,
            'FIELD_NAME': 'ELEV',
            'OUTPUT': 'TEMPORARY_OUTPUT'}  # Configura a saída para um arquivo temporário

        # Medir o tempo de início
        start_time = time.time()

        # Executa a ferramenta de curvas de nível com feedback
        try:
            feedback = QgsProcessingFeedback()
            result = processing.run("gdal:contour", params, feedback=feedback)
        except Exception as e:
            self.mostrar_mensagem(self.tr("Erro ao gerar curvas de nível: {error}").format(error=str(e)), tipo="Erro")
            return

        # Extrai o caminho do arquivo temporário do resultado
        temp_file_path = result['OUTPUT']
        original_layer = QgsVectorLayer(temp_file_path, output_layer_name, "ogr")
        if not original_layer.isValid():
            self.mostrar_mensagem(self.tr("Falha ao criar a camada de curvas de nível."), "Erro")
            return

        # QgsProject.instance().addMapLayer(original_layer)
        layer_tree = QgsProject.instance().layerTreeRoot().findLayer(original_layer.id())
        if layer_tree:
            layer_tree.setItemVisibilityChecked(False)

        # Início da Cópia para a camada customizada com a barra de progresso
        crs = original_layer.crs().authid()
        memory_layer = self.create_memory_layer(self.tr("Curva de Niveis 3D"), "LineString", crs, is_3d=True)
        self.copy_elev_attribute(original_layer, memory_layer)

        # Tolerância de simplificação baseada no tamanho do pixel do raster
        px = abs(selected_layer.rasterUnitsPerPixelX())
        py = abs(selected_layer.rasterUnitsPerPixelY())
        base_tol = max(px, py)

        # Muito pouca simplificação, mais segura
        if selected_layer.crs().isGeographic():
            factor = 0.02  # 2% do tamanho do pixel em graus
        else:
            factor = 0.04   # 5% do tamanho do pixel em metros

        simplify_tol = base_tol * factor

        # Barra de progresso
        progressBar, progressMessageBar = self.iniciar_progress_bar(original_layer)
        self.simplify_and_copy_features(original_layer, memory_layer, progressBar, simplify_tol)
        self.iface.messageBar().popWidget(progressMessageBar)

        self.set_layer_symbology(memory_layer)
        self.set_labeling(memory_layer)
        QgsProject.instance().addMapLayer(memory_layer)

        # guarda apenas o ID da camada
        self.curves_layer_id = memory_layer.id()

        # Tempo de execução
        elapsed_time = time.time() - start_time
        self.mostrar_mensagem(self.tr("Curvas de nível geradas com sucesso em {elapsed_time:.2f} segundos!").format(elapsed_time=elapsed_time), tipo="Sucesso")

    def simplify_and_copy_features(self, source_layer, target_layer, progressBar=None, simplify_tol=0.0):
        """
        Simplifica as geometrias e copia as feições da camada de origem para a camada de destino,
        adicionando coordenadas Z, se aplicável.

        :param source_layer: camada de origem
        :param target_layer: camada de destino
        :param progressBar: QProgressBar (opcional)
        :param simplify_tol: tolerância de simplificação (em unidades do CRS). Se 0, não simplifica.
        """
        # Inicia o modo de edição na camada de destino
        target_layer.startEditing()

        count = 0
        total = source_layer.featureCount()

        for feature in source_layer.getFeatures():
            new_feature = QgsFeature()

            geom = feature.geometry()
            # usa a tolerância, se > 0
            if simplify_tol and simplify_tol > 0:
                simple_geom = geom.simplify(simplify_tol)
            else:
                simple_geom = geom

            # Se a camada destino for 3D, adiciona Z
            if QgsWkbTypes.hasZ(target_layer.wkbType()):
                z_value = feature['ELEV']
                points_3d = [QgsPoint(p.x(), p.y(), z_value) for p in simple_geom.vertices()]
                simple_geom = QgsGeometry.fromPolyline(points_3d)

            new_feature.setGeometry(simple_geom)
            new_feature.setAttributes([feature['ELEV']])
            target_layer.addFeature(new_feature)

            count += 1
            if progressBar:
                progressBar.setValue(count)

        target_layer.commitChanges()

    def create_line_labels(self, msp, points, text_value, label_rgb, dist_repeat, position_mode, text_size, scale_factor, layer_crs):
        """
        Cria rótulos (MTEXT) ao longo de uma lista de pontos (x, y, z), repetidos a cada 'dist_repeat' unidades.
        
        Parâmetros:
        - msp: O modelspace do documento DXF onde os rótulos serão adicionados.
        - points (list): Lista de tuplas (x, y, z) representando os pontos da polyline.
        - text_value (str): Texto que será exibido em cada rótulo (geralmente o valor de 'ELEV').
        - label_rgb (tuple): Tupla (R, G, B) definindo a cor do rótulo.
        - dist_repeat (float): Distância em que os rótulos serão repetidos ao longo da linha.
        - position_mode (str): Determina a posição do rótulo em relação à linha ('Acima', 'Abaixo' ou 'Centro').
        - text_size (float): Tamanho base do texto (char_height) antes do ajuste pela escala.
        - scale_factor (float): Fator de escala calculado a partir da escala atual do QGIS e uma escala base.
        """
        try:
            color_int = ezdxf.rgb2int(label_rgb)
        except Exception:
            color_int = 0

        # Helpers 2D no plano (usados sempre no espaço "de trabalho")
        def segment_length_2d(p1, p2):
            dx = p2[0] - p1[0]; dy = p2[1] - p1[1]
            return math.hypot(dx, dy)

        def angle_of_segment_2d(p1, p2):
            dx = p2[0] - p1[0]; dy = p2[1] - p1[1]
            return math.degrees(math.atan2(dy, dx))

        def offset_point(px, py, angle_deg, offset_dist):
            alpha = math.radians(angle_deg + 90)
            return px + offset_dist*math.cos(alpha), py + offset_dist*math.sin(alpha)

        # Escolhe espaço de trabalho
        is_geo = layer_crs.isGeographic()
        to_work = from_work = None
        if is_geo:
            work_crs = QgsCoordinateReferenceSystem("EPSG:3857")  # metros
            to_work = QgsCoordinateTransform(layer_crs, work_crs, QgsProject.instance().transformContext())
            from_work = QgsCoordinateTransform(work_crs, layer_crs, QgsProject.instance().transformContext())

            pts_work = [to_work.transform(QgsPointXY(x, y)) for (x, y, _z) in points]
            pts_work = [(p.x(), p.y()) for p in pts_work]
        else:
            pts_work = [(x, y) for (x, y, _z) in points]

        # Calcula posições a cada dist_repeat (em METROS no espaço de trabalho)
        if len(pts_work) < 2:
            return

        label_positions_work = []
        dist_to_next = max(float(dist_repeat), 0.0)
        p1 = (pts_work[0][0], pts_work[0][1])
        for i in range(1, len(pts_work)):
            p2 = (pts_work[i][0], pts_work[i][1])
            seg_len = segment_length_2d(p1, p2)
            while seg_len >= dist_to_next and dist_to_next > 0:
                t = dist_to_next / seg_len
                x = p1[0] + t*(p2[0]-p1[0]); y = p1[1] + t*(p2[1]-p1[1])
                ang = angle_of_segment_2d(p1, p2)
                label_positions_work.append((x, y, ang))
                p1 = (x, y)
                seg_len -= dist_to_next
                dist_to_next = float(dist_repeat)
            dist_to_next -= seg_len
            p1 = p2

        if not label_positions_work:
            # um rótulo no meio
            mid = len(pts_work)//2
            if len(pts_work) >= 2:
                p1 = pts_work[mid-1]; p2 = pts_work[mid]
                x = (p1[0]+p2[0])/2; y = (p1[1]+p2[1])/2
                ang = angle_of_segment_2d(p1, p2)
            else:
                x, y = pts_work[0]; ang = 0
            label_positions_work.append((x, y, ang))

        # Offset perpendicular em METROS no espaço de trabalho
        adjusted_text_size = text_size * scale_factor
        if position_mode == 'Acima':
            off = 1.5 * adjusted_text_size
        elif position_mode == 'Abaixo':
            off = -1.5 * adjusted_text_size
        else:
            off = 0.0

        for (xw, yw, ang) in label_positions_work:
            xo, yo = offset_point(xw, yw, ang, off)

            # Volta para o CRS original se necessário
            if is_geo:
                pt_deg = from_work.transform(QgsPointXY(xo, yo))
                x_final, y_final = pt_deg.x(), pt_deg.y()
            else:
                x_final, y_final = xo, yo

            mtext = msp.add_mtext(
                text=text_value,
                dxfattribs={
                    'char_height': adjusted_text_size,
                    'rotation': ang,          # ângulo calculado no espaço de trabalho
                    'true_color': color_int})

            # Background Mask / Background Color no MTEXT
            try:
                # Versões mais novas do ezdxf
                mtext.set_bg_color("canvas", scale=1.15)
            except Exception:
                try:
                    # Fallback DXF:
                    # 0 = desligado
                    # 1 = cor definida
                    # 2 = cor de fundo da tela/desenho
                    mtext.dxf.bg_fill = 2
                    mtext.dxf.box_fill_scale = 1.15
                except Exception:
                    pass  # nosec B110

            mtext.set_location(insert=(x_final, y_final), attachment_point=5)

    def create_and_add_custom_layer(self, source_layer):
        """
        Cria uma nova camada em memória a partir de uma camada de curvas
        de nível existente e aplica configurações personalizadas.
        """
        crs = source_layer.crs().authid()

        memory_layer = self.create_memory_layer(self.tr("Curva de Niveis 3D"), "LineString", crs, is_3d=True)

        self.copy_elev_attribute(source_layer, memory_layer)

        progressBar, progressMessageBar = self.iniciar_progress_bar(source_layer)

        self.simplify_and_copy_features(source_layer, memory_layer, progressBar)

        self.iface.messageBar().popWidget(progressMessageBar)

        self.set_layer_symbology(memory_layer)
        self.set_labeling(memory_layer)

        QgsProject.instance().addMapLayer(memory_layer)

    def copy_elev_attribute(self, source_layer, target_layer):
        """
        Copia a coluna 'ELEV' da camada de origem para a camada de destino.

        Parâmetros:
        - source_layer (QgsVectorLayer): A camada de origem que contém o campo 'ELEV'.
        - target_layer (QgsVectorLayer): A camada de destino, para a qual o campo 'ELEV' será copiado.

        Funcionalidades:
        - Verifica se a camada de origem possui um campo chamado 'ELEV'.
        - Se o campo 'ELEV' for encontrado, ele é adicionado à camada de destino como um atributo.
        - Atualiza os campos da camada de destino para refletir a adição do novo atributo.
        """
        # Obtém o provedor de dados da camada de destino
        provider = target_layer.dataProvider()

        # Itera sobre os campos da camada de origem
        for field in source_layer.fields():
            # Verifica se o campo é o 'ELEV'
            if field.name() == 'ELEV':
                # Adiciona o campo 'ELEV' à camada de destino
                provider.addAttributes([QgsField('ELEV', QMetaType.Type.Double)])

        # Atualiza os campos da camada de destino
        target_layer.updateFields()

    def set_layer_symbology(self, layer):
        """
        Define a simbologia da camada com base em uma expressão condicional que diferencia curvas simples e mestras.

        Parâmetros:
        - layer (QgsVectorLayer): A camada à qual será aplicada a simbologia personalizada.

        Funcionalidades:
        - Obtém as cores selecionadas nos combo boxes da interface do usuário.
        - Define a simbologia para as curvas simples com a cor correspondente ao campo 'cor2'.
        - Define a simbologia para as curvas mestras, que são múltiplos de um valor definido, com a cor correspondente ao campo 'cor1'.
        - Cria uma expressão condicional para distinguir curvas simples de mestras.
        - Aplica a simbologia categorizada à camada com base na expressão condicional.
        """
        # Obtém as cores selecionadas nos combo boxes
        color_curvas_simples = QColor(self.selected_colors.get('cor2', '#FFFF00'))  # Cor das curvas simples (padrão: amarelo)
        color_curvas_mestras = QColor(self.selected_colors.get('cor1', '#FF0000'))  # Cor das curvas mestras (padrão: vermelho)

        # Define o símbolo padrão para as curvas simples
        default_symbol = QgsSymbol.defaultSymbol(layer.geometryType())
        default_symbol.setColor(color_curvas_simples)

        # Define o símbolo para as curvas mestras (múltiplas de desnivel_m)
        symbol_mul_desnivel = QgsSymbol.defaultSymbol(layer.geometryType())
        symbol_mul_desnivel.setColor(color_curvas_mestras)

        # Cria uma expressão para identificar curvas mestras (múltiplos de desnivel_m)
        expression_mul_desnivel = f'CASE WHEN "ELEV" % {self.desnivel_m} = 0 THEN 1 ELSE 0 END'

        # Cria as categorias de renderização para curvas simples e mestras
        categories = [
            QgsRendererCategory(1, symbol_mul_desnivel, self.tr("Curvas Mestras")),  # Categoria para curvas mestras
            QgsRendererCategory(0, default_symbol, self.tr("Curvas Simples"))]  # Categoria para curvas simples

        # Cria e configura o renderizador categorizado com base na expressão
        renderer = QgsCategorizedSymbolRenderer(expression_mul_desnivel, categories)

        # Aplica o renderizador categorizado à camada
        layer.setRenderer(renderer)

        # Redesenha a camada para aplicar a nova simbologia
        layer.triggerRepaint()

    def set_labeling(self, layer):
        """
        Configura a rotulagem da camada, alinhando e centralizando os rótulos ao longo das linhas, com base nas opções selecionadas pelo usuário.

        Parâmetros:
        - layer (QgsVectorLayer): A camada à qual os rótulos personalizados serão aplicados.

        Funcionalidades:
        - Define o campo 'ELEV' como o valor de rótulo.
        - Configura o posicionamento do rótulo com base na posição selecionada pelo usuário (Centro, Acima, Abaixo).
        - Define a repetição dos rótulos ao longo das linhas com base na configuração de repetição.
        - Aplica uma expressão condicional para colorir os rótulos, diferenciando curvas simples e mestras.
        - Aplica o formato de texto e ativa a rotulagem na camada.
        """
        # Configurações básicas de rótulo (campo 'ELEV' será o valor do rótulo)
        label_settings = QgsPalLayerSettings()
        label_settings.fieldName = "ELEV"

        # Configura o posicionamento do rótulo
        if self.selected_position == "Centro":
            label_settings.placement = Qgis.LabelPlacement.Line
            label_settings.placementFlags = (
                Qgis.LabelLinePlacementFlag.OnLine)

        elif self.selected_position == "Acima":
            label_settings.placement = Qgis.LabelPlacement.Line
            label_settings.placementFlags = (
                Qgis.LabelLinePlacementFlag.AboveLine)

        elif self.selected_position == "Abaixo":
            label_settings.placement = Qgis.LabelPlacement.Line
            label_settings.placementFlags = (
                Qgis.LabelLinePlacementFlag.BelowLine)

        # Configura a repetição dos rótulos em milímetros.
        label_settings.repeatDistance = self.repeticao
        label_settings.repeatDistanceUnit = Qgis.RenderUnit.Millimeters

        # Configuração da cor do rótulo com base nas curvas simples e mestras
        color1 = self.selected_colors.get('cor3', '255,0,0')  # Cor das curvas mestras
        color2 = self.selected_colors.get('cor4', '255,255,0')  # Cor das curvas simples

        # Expressão condicional para determinar a cor dos rótulos
        color_expression = f"""CASE
                                WHEN "ELEV" % {self.desnivel_m} = 0 THEN '{color1}'
                                ELSE '{color2}'
                              END"""

        # Aplica a expressão de cor aos rótulos
        properties = label_settings.dataDefinedProperties()
        properties.setProperty(QgsPalLayerSettings.Property.Color, QgsProperty.fromExpression(color_expression))
        label_settings.setDataDefinedProperties(properties)

        # Configuração do formato do texto do rótulo
        text_format = QgsTextFormat()
        text_format.setSize(self.tamanho)  # Usa o tamanho definido pelo usuário
        text_format.setColor(QColor(0, 0, 0))  # Cor preta para o texto por padrão
        label_settings.setFormat(text_format)

        # Ativa a rotulagem para a camada
        layer.setLabelsEnabled(True)

        # Aplica a configuração de rotulagem à camada
        layer.setLabeling(QgsVectorLayerSimpleLabeling(label_settings))

        # Redesenha a camada para aplicar as alterações de rotulagem
        layer.triggerRepaint()

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

    def get_curves_layer(self):
        """
        Retorna a camada 'Curva de Niveis 3D' se existir no projeto.
        Usa o ID guardado; se não achar, procura pelo nome.
        """
        # tenta primeiro pelo ID guardado
        if getattr(self, "curves_layer_id", None):
            lyr = QgsProject.instance().mapLayer(self.curves_layer_id)
            if lyr is not None:
                return lyr

        # fallback: procura pelo nome
        layer_name = self.tr("Curva de Niveis 3D")
        for layer in QgsProject.instance().mapLayers().values():
            if layer.name() == layer_name:
                # atualiza o ID guardado
                self.curves_layer_id = layer.id()
                return layer

        return None

    def open_config_dialog(self):
        """
        Abre o diálogo de configuração e atualiza as curvas existentes
        assim que o usuário confirmar (OK).
        """
        config_dialog = ConfigDialog(self)

        # Pré-preenche com as configurações atuais
        # Cores
        try:
            if self.selected_colors:
                m = self.selected_colors
                idx = config_dialog.comboBoxCor1.findData(m.get('cor1', 'Red'))
                if idx != -1:
                    config_dialog.comboBoxCor1.setCurrentIndex(idx)

                idx = config_dialog.comboBoxCor2.findData(m.get('cor2', 'Yellow'))
                if idx != -1:
                    config_dialog.comboBoxCor2.setCurrentIndex(idx)

                idx = config_dialog.comboBoxCor3.findData(m.get('cor3', 'Red'))
                if idx != -1:
                    config_dialog.comboBoxCor3.setCurrentIndex(idx)

                idx = config_dialog.comboBoxCor4.findData(m.get('cor4', 'Yellow'))
                if idx != -1:
                    config_dialog.comboBoxCor4.setCurrentIndex(idx)

        except Exception:
            pass  # nosec B110 | se der algo errado aqui, usa os defaults do diálogo

        # Posição dos rótulos
        if self.selected_position == 'Centro':
            config_dialog.radioButtonCentro.setChecked(True)
        elif self.selected_position == 'Acima':
            config_dialog.radioButtonAcima.setChecked(True)
        elif self.selected_position == 'Abaixo':
            config_dialog.radioButtonAbaixo.setChecked(True)

        # Desníveis, tamanho, repetição
        config_dialog.spinBoxDmestras.setValue(int(self.desnivel_m))
        config_dialog.doubleSpinBoxDsimples.setValue(float(self.desnivel_s))
        config_dialog.spinBoxTamanho.setValue(int(self.tamanho))
        config_dialog.spinBoxRepete.setValue(int(self.repeticao))

        # Abre o diálogo
        if config_dialog.exec():
            # Lê as configurações do diálogo
            self.selected_colors = config_dialog.selected_colors
            self.selected_position = config_dialog.selected_position
            self.desnivel_m = config_dialog.desnivel_m
            self.desnivel_s = config_dialog.desnivel_s
            self.tamanho = config_dialog.tamanho
            self.repeticao = config_dialog.repeticao

            # Atualiza em tempo real a camada de curvas já gerada, se existir
            curves_layer = self.get_curves_layer()
            if curves_layer is not None:
                self.set_layer_symbology(curves_layer)
                self.set_labeling(curves_layer)

    def mostrar_mensagem(self, texto, tipo, duracao=3, caminho_pasta=None, caminho_arquivo=None):
        """
        Exibe apenas uma mensagem deste módulo por vez.
        A mensagem anterior é removida imediatamente antes da próxima.
        """
        bar = self.iface.messageBar()

        mensagem_anterior = getattr(self, "_mensagem_atual", None)

        if mensagem_anterior is not None:
            try:
                bar.popWidget(mensagem_anterior)
            except (RuntimeError, TypeError):
                pass  # A mensagem pode já ter expirado automaticamente.

            self._mensagem_atual = None

        if tipo == "Erro":
            titulo = self.tr("Erro")
            nivel = Qgis.MessageLevel.Critical

        elif tipo == "Aviso":
            titulo = self.tr("Aviso")
            nivel = Qgis.MessageLevel.Warning

        elif tipo == "Sucesso":
            titulo = self.tr("Sucesso")
            nivel = Qgis.MessageLevel.Info  # Mantém o fundo azul.

        else:
            titulo = self.tr("Info")
            nivel = Qgis.MessageLevel.Info

        mensagem = bar.createMessage(titulo, texto)
        posicao_botao = 1

        if tipo == "Sucesso" and caminho_pasta:
            botao_abrir_pasta = QPushButton(self.tr("Abrir Pasta"))
            botao_abrir_pasta.clicked.connect(
                lambda _checked=False, caminho=caminho_pasta:
                    QDesktopServices.openUrl(
                        QUrl.fromLocalFile(
                            os.path.abspath(os.fspath(caminho)))))

            mensagem.layout().insertWidget(posicao_botao, botao_abrir_pasta)
            posicao_botao += 1

        if tipo == "Sucesso" and caminho_arquivo:
            botao_executar = QPushButton(self.tr("Executar"))
            botao_executar.clicked.connect(
                lambda _checked=False, caminho=caminho_arquivo:
                    QDesktopServices.openUrl(
                        QUrl.fromLocalFile(
                            os.path.abspath(os.fspath(caminho)))))

            mensagem.layout().insertWidget(posicao_botao, botao_executar)

        bar.pushWidget(mensagem, level=nivel, duration=duracao)
        self._mensagem_atual = mensagem

    def iniciar_progress_bar(self, layer):
        """
        Inicia e exibe uma barra de progresso na interface do usuário para o processo de exportação de uma camada para DXF.

        Parâmetros:
        - layer (QgsVectorLayer): A camada que está sendo exportada, usada para determinar o número total de feições e para exibir o nome da camada na barra de progresso.

        Funcionalidades:
        - Cria uma mensagem personalizada na barra de mensagens do QGIS para acompanhar o progresso da exportação.
        - Configura e estiliza uma barra de progresso que indica a porcentagem e o número de feições processadas.
        - Define o valor máximo da barra de progresso com base no número total de feições da camada.
        - Retorna os widgets de barra de progresso e de mensagem para que possam ser atualizados durante o processo de exportação.
        """
        # Cria uma mensagem personalizada na barra de progresso
        progressMessageBar = self.iface.messageBar().createMessage(self.tr("Exportando camada para DXF: {layer_name}").format(layer_name=layer.name()))
        progressBar = QProgressBar()  # Cria uma instância da QProgressBar
        progressBar.setAlignment(Qt.AlignmentFlag.AlignLeft | Qt.AlignmentFlag.AlignVCenter)  # Alinha a barra de progresso à esquerda e verticalmente ao centro
        progressBar.setFormat(self.tr("%p% - %v de %m Feições processadas")) # Define o formato da barra de progresso
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

    def export_to_dxf(self):
        """
        Exporta a camada "Curva de Niveis 3D" para um arquivo DXF.

        Se a camada estiver em coordenadas geográficas (lat/long), as geometrias são
        reprojetadas para um sistema UTM adequado (WGS84 / UTM zona N ou S) antes da
        exportação, de forma que o DXF fique em metros.
        """
        # 1. Busca a camada "Curva de Niveis 3D"
        layer_name = self.tr("Curva de Niveis 3D")
        target_layer = None
        for layer in QgsProject.instance().mapLayers().values():
            if layer.name() == layer_name:
                target_layer = layer
                break

        if target_layer is None:
            self.mostrar_mensagem(self.tr("Camada '{layer_name}' não encontrada para exportação.").format(layer_name=layer_name), "Erro")
            return

        original_crs = target_layer.crs()     # CRS real da camada no QGIS
        dxf_crs = original_crs               # CRS que será usado no DXF
        coord_transform = None               # Transformação opcional p/ UTM

        # Se estiver em coordenadas geográficas, escolhe um UTM automático p/ exportar
        if original_crs.isGeographic():
            extent = target_layer.extent()
            if extent.isEmpty():
                self.mostrar_mensagem(self.tr("Extensão da camada inválida para calcular UTM."), "Erro")
                return

            center_x = (extent.xMinimum() + extent.xMaximum()) / 2.0  # longitude média
            center_y = (extent.yMinimum() + extent.yMaximum()) / 2.0  # latitude média

            # Cálculo padrão de zona UTM
            utm_zone = int((center_x + 180.0) / 6.0) + 1
            # Norte ou sul
            if center_y >= 0:
                epsg_code = 32600 + utm_zone   # WGS84 / UTM zona XXN
            else:
                epsg_code = 32700 + utm_zone   # WGS84 / UTM zona XXS

            utm_crs = QgsCoordinateReferenceSystem(f"EPSG:{epsg_code}")
            if utm_crs.isValid():
                dxf_crs = utm_crs
                coord_transform = QgsCoordinateTransform(
                    original_crs, dxf_crs, QgsProject.instance().transformContext())
            else:
                # Fallback: se por algum motivo não criou o CRS, segue no CRS original
                dxf_crs = original_crs
                coord_transform = None

        # 2. Solicita ao usuário o caminho para salvar o arquivo DXF
        file_path = self.escolher_local_para_salvar(self.tr("Curva_de_Niveis_3D.dxf"), self.tr("Arquivos DXF (*.dxf)"))

        if not file_path:
            return

        # 3. Calcula o fator de escala
        current_scale = self.spinBoxEscala.value()   # escala atual (ex.: 500, 1000)
        base_scale = self.tamanho                    # tamanho base do texto (ex.: 8)
        scale_factor = current_scale * base_scale / 30000.0

        # 4. Cria um novo documento DXF e o modelspace
        doc = ezdxf.new(dxfversion='R2010')
        msp = doc.modelspace()

        # Cria a camada DXF "Curvas de Níveis 3D" se ela ainda não existir
        dxf_layer_name = self.tr("Curvas de Níveis 3D")
        if not doc.layers.has_entry(dxf_layer_name):
            doc.layers.new(dxf_layer_name, dxfattribs={'color': 7})  # branco

        # Mapeamento de cores
        color_mapping = {
            'Red': (255, 0, 0),
            'Yellow': (255, 255, 0),
            'Green': (0, 255, 0),
            'Cyan': (0, 255, 255),
            'Blue': (0, 0, 255),
            'Magenta': (255, 0, 255),
            'Gray': (180, 180, 180)}

        # Helper para transformar XY para o CRS do DXF (UTM ou original)
        def transform_xy(x, y):
            if coord_transform is None:
                return x, y
            pt = coord_transform.transform(QgsPointXY(x, y))
            return pt.x(), pt.y()

        # Barra de progresso
        progressBar, progressMessageBar = self.iniciar_progress_bar(target_layer)
        total = target_layer.featureCount()
        count = 0

        # 5. Itera sobre cada feição da camada para criar as polilinhas 3D e os rótulos
        for feature in target_layer.getFeatures():
            geom = feature.geometry()
            z_value = feature['ELEV']

            # Cores de linha / rótulo conforme curva mestra ou simples
            if z_value % self.desnivel_m == 0:
                line_color_name = self.selected_colors.get('cor1', 'Red')
                label_color_name = self.selected_colors.get('cor3', 'Red')
            else:
                line_color_name = self.selected_colors.get('cor2', 'Yellow')
                label_color_name = self.selected_colors.get('cor4', 'Yellow')

            line_rgb = color_mapping.get(line_color_name, (255, 0, 0))
            label_rgb = color_mapping.get(label_color_name, (255, 0, 0))

            # Multipart x single
            if geom.isMultipart():
                multiline = geom.asMultiPolyline()
                for poly in multiline:
                    # Transforma os pontos para o CRS do DXF (UTM se for o caso)
                    points = []
                    for pt in poly:
                        x, y = transform_xy(pt.x(), pt.y())
                        points.append((x, y, z_value))

                    polyline = msp.add_polyline3d(points)
                    polyline.dxf.true_color = ezdxf.rgb2int(line_rgb)
                    polyline.dxf.layer = dxf_layer_name

                    # Cria rótulos usando o CRS do DXF
                    self.create_line_labels(
                        msp, points, str(z_value), label_rgb,
                        self.repeticao, self.selected_position,
                        self.tamanho, scale_factor, dxf_crs)
            else:
                poly = geom.asPolyline()
                if poly:
                    points = []
                    for pt in poly:
                        x, y = transform_xy(pt.x(), pt.y())
                        points.append((x, y, z_value))

                    polyline = msp.add_polyline3d(points)
                    polyline.dxf.true_color = ezdxf.rgb2int(line_rgb)
                    polyline.dxf.layer = dxf_layer_name

                    self.create_line_labels(
                        msp, points, str(z_value), label_rgb,
                        self.repeticao, self.selected_position,
                        self.tamanho, scale_factor, dxf_crs)

            count += 1
            progressBar.setValue(count)

        # Remove barra
        self.iface.messageBar().popWidget(progressMessageBar)

        # 6. Salva o DXF
        try:
            doc.saveas(file_path)
            pasta = os.path.dirname(file_path)
            self.mostrar_mensagem(self.tr(
                "Arquivo DXF exportado com sucesso!"),
                "Sucesso",
                duracao=3,
                caminho_pasta=pasta,
                caminho_arquivo=file_path)
        except Exception as e:
            self.mostrar_mensagem(self.tr("Erro ao exportar DXF: {error}").format(error=str(e)), "Erro")

class ConfigDialog(QDialog):
    """
    Classe que define o diálogo de configurações de exportação.

    Herda de:
    - QDialog: Classe base para criar uma janela de diálogo no PyQt.

    Funcionalidades:
    - Apresenta ao usuário uma interface gráfica para ajustar as configurações de exportação, como cores, desníveis, 
      tamanho do rótulo e repetição de rótulos.
    """

    def __init__(self, parent=None):
        """
        Inicializa o diálogo de configurações de exportação.

        Parâmetros:
        - parent (QWidget, opcional): O widget pai da janela de diálogo. Pode ser None para criar uma janela independente.

        Funcionalidades:
        - Chama o método de inicialização da superclasse (QDialog) para configurar o diálogo como uma janela de diálogo.
        - Configura a interface gráfica da janela usando o método setupUi().
        - Altera o título da janela para "Configurações de Exportação".
        """
        # Chama o construtor da superclasse (QDialog)
        super().__init__(parent)

        # Configura a interface do usuário (presumivelmente definida em Qt Designer)
        self.setupUi(self)

        # Altera o título da janela de diálogo
        self.setWindowTitle(self.tr("Configurações de Exportação"))

    def tr(self, message):
        return QtCore.QCoreApplication.translate("ConfigDialog", message)

    def setupUi(self, Dialog):
        """
        Configura a interface do usuário para o diálogo de configuração de exportação.

        Parâmetros:
        - Dialog (QDialog): O diálogo onde a interface será configurada.

        Funcionalidades:
        - Define a estrutura da interface, como o layout, botões, labels, spin boxes, e combo boxes.
        - Define valores padrão para vários widgets, como cores, tamanhos e desníveis.
        - Conecta sinais e slots, permitindo a interação entre os elementos da interface e a lógica subjacente.
        """
        # Configura o nome do diálogo e suas dimensões máximas
        Dialog.setObjectName("ConfigDialog")
        Dialog.resize(315, 299)
        Dialog.setMaximumSize(QtCore.QSize(315, 299))

        # Layout principal da interface do diálogo
        self.gridLayout_21 = QtWidgets.QGridLayout(Dialog)
        self.gridLayout_21.setObjectName("gridLayout_21")

        # Criação e configuração dos frames e layouts da interface
        self.gridLayout_20 = QtWidgets.QGridLayout()
        self.gridLayout_20.setObjectName("gridLayout_20")
        self.frame_3 = QtWidgets.QFrame(Dialog)
        self.frame_3.setFrameShape(QtWidgets.QFrame.Shape.Box)
        self.frame_3.setFrameShadow(QtWidgets.QFrame.Shadow.Raised)
        self.frame_3.setObjectName("frame_3")
        self.gridLayout_18 = QtWidgets.QGridLayout(self.frame_3)
        self.gridLayout_18.setObjectName("gridLayout_18")
        self.gridLayout_16 = QtWidgets.QGridLayout()
        self.gridLayout_16.setObjectName("gridLayout_16")
        self.label_6 = QtWidgets.QLabel(self.frame_3)
        self.label_6.setObjectName("label_6")
        self.gridLayout_16.addWidget(self.label_6, 0, 0, 1, 1)

        # Criação do frame principal e configuração do layout da interface
        self.frame = QtWidgets.QFrame(self.frame_3)
        self.frame.setFrameShape(QtWidgets.QFrame.Shape.Box)
        self.frame.setFrameShadow(QtWidgets.QFrame.Shadow.Sunken)
        self.frame.setObjectName("frame")
        self.gridLayout = QtWidgets.QGridLayout(self.frame)
        self.gridLayout.setObjectName("gridLayout")

        # Configuração dos combo boxes para seleção de cores
        self.gridLayout_7 = QtWidgets.QGridLayout()
        self.gridLayout_7.setObjectName("gridLayout_7")
        self.gridLayout_2 = QtWidgets.QGridLayout()
        self.gridLayout_2.setObjectName("gridLayout_2")
        self.label_2 = QtWidgets.QLabel(self.frame)
        self.label_2.setObjectName("label_2")
        self.gridLayout_2.addWidget(self.label_2, 0, 0, 1, 1)
        self.comboBoxCor3 = QtWidgets.QComboBox(self.frame)
        self.comboBoxCor3.setMaximumSize(QtCore.QSize(35, 20))
        self.comboBoxCor3.setObjectName("comboBoxCor3")
        self.gridLayout_2.addWidget(self.comboBoxCor3, 0, 1, 1, 1)
        self.gridLayout_7.addLayout(self.gridLayout_2, 0, 0, 1, 1)

        # Configurações para a segunda cor
        self.gridLayout_6 = QtWidgets.QGridLayout()
        self.gridLayout_6.setObjectName("gridLayout_6")
        self.comboBoxCor4 = QtWidgets.QComboBox(self.frame)
        self.comboBoxCor4.setMaximumSize(QtCore.QSize(35, 20))
        self.comboBoxCor4.setObjectName("comboBoxCor4")
        self.gridLayout_6.addWidget(self.comboBoxCor4, 0, 1, 1, 1)
        self.label_7 = QtWidgets.QLabel(self.frame)
        self.label_7.setObjectName("label_7")
        self.gridLayout_6.addWidget(self.label_7, 0, 0, 1, 1)
        self.gridLayout_7.addLayout(self.gridLayout_6, 0, 1, 1, 1)

        # Criação dos botões de radio para seleção de posição dos rótulos
        self.gridLayout_3 = QtWidgets.QGridLayout()
        self.gridLayout_3.setObjectName("gridLayout_3")
        self.radioButtonCentro = QtWidgets.QRadioButton(self.frame)
        self.radioButtonCentro.setObjectName("radioButtonCentro")
        self.gridLayout_3.addWidget(self.radioButtonCentro, 0, 2, 1, 1)
        self.label_3 = QtWidgets.QLabel(self.frame)
        self.label_3.setObjectName("label_3")
        self.gridLayout_3.addWidget(self.label_3, 0, 0, 1, 1)
        self.radioButtonAcima = QtWidgets.QRadioButton(self.frame)
        self.radioButtonAcima.setObjectName("radioButtonAcima")
        self.gridLayout_3.addWidget(self.radioButtonAcima, 0, 1, 1, 1)
        self.radioButtonAbaixo = QtWidgets.QRadioButton(self.frame)
        self.radioButtonAbaixo.setObjectName("radioButtonAbaixo")
        self.gridLayout_3.addWidget(self.radioButtonAbaixo, 0, 3, 1, 1)
        self.gridLayout_7.addLayout(self.gridLayout_3, 1, 0, 1, 2)

        # Configurações de layout para spin boxes (tamanho do rótulo e repetição)
        self.gridLayout_4 = QtWidgets.QGridLayout()
        self.gridLayout_4.setObjectName("gridLayout_4")
        self.spinBoxTamanho = QtWidgets.QSpinBox(self.frame)
        self.spinBoxTamanho.setMaximumSize(QtCore.QSize(40, 20))
        self.spinBoxTamanho.setObjectName("spinBoxTamanho")
        self.gridLayout_4.addWidget(self.spinBoxTamanho, 0, 1, 1, 1)
        self.label_4 = QtWidgets.QLabel(self.frame)
        self.label_4.setObjectName("label_4")
        self.gridLayout_4.addWidget(self.label_4, 0, 0, 1, 1)
        self.gridLayout_7.addLayout(self.gridLayout_4, 2, 0, 1, 1)

        # Configurações de layout para spin boxes (tamanho do rótulo e repetição)
        self.gridLayout_5 = QtWidgets.QGridLayout()
        self.gridLayout_5.setObjectName("gridLayout_5")
        self.label_5 = QtWidgets.QLabel(self.frame)
        self.label_5.setObjectName("label_5")
        self.gridLayout_5.addWidget(self.label_5, 0, 0, 1, 1)
        self.spinBoxRepete = QtWidgets.QSpinBox(self.frame)
        self.spinBoxRepete.setMaximumSize(QtCore.QSize(45, 20))
        self.spinBoxRepete.setObjectName("spinBoxRepete")
        self.gridLayout_5.addWidget(self.spinBoxRepete, 0, 1, 1, 1)
        self.gridLayout_7.addLayout(self.gridLayout_5, 2, 1, 1, 1)
        self.gridLayout.addLayout(self.gridLayout_7, 0, 0, 1, 1)
        self.gridLayout_16.addWidget(self.frame, 1, 0, 1, 1)
        self.gridLayout_18.addLayout(self.gridLayout_16, 0, 0, 1, 1)
        self.gridLayout_17 = QtWidgets.QGridLayout()
        self.gridLayout_17.setObjectName("gridLayout_17")
        self.frame_2 = QtWidgets.QFrame(self.frame_3)
        self.frame_2.setFrameShape(QtWidgets.QFrame.Shape.Box)
        self.frame_2.setFrameShadow(QtWidgets.QFrame.Shadow.Sunken)
        self.frame_2.setObjectName("frame_2")
        self.gridLayout_15 = QtWidgets.QGridLayout(self.frame_2)
        self.gridLayout_15.setObjectName("gridLayout_15")
        self.gridLayout_14 = QtWidgets.QGridLayout()
        self.gridLayout_14.setObjectName("gridLayout_14")
        self.gridLayout_12 = QtWidgets.QGridLayout()
        self.gridLayout_12.setObjectName("gridLayout_12")
        self.gridLayout_9 = QtWidgets.QGridLayout()
        self.gridLayout_9.setObjectName("gridLayout_9")
        self.label = QtWidgets.QLabel(self.frame_2)
        self.label.setObjectName("label")
        self.gridLayout_9.addWidget(self.label, 0, 0, 1, 1)
        self.comboBoxCor1 = QtWidgets.QComboBox(self.frame_2)
        self.comboBoxCor1.setMaximumSize(QtCore.QSize(35, 20))
        self.comboBoxCor1.setObjectName("comboBoxCor1")
        self.gridLayout_9.addWidget(self.comboBoxCor1, 0, 1, 1, 1)
        self.gridLayout_12.addLayout(self.gridLayout_9, 0, 0, 1, 1)
        self.gridLayout_11 = QtWidgets.QGridLayout()
        self.gridLayout_11.setObjectName("gridLayout_11")
        self.label_11 = QtWidgets.QLabel(self.frame_2)
        self.label_11.setObjectName("label_11")
        self.gridLayout_11.addWidget(self.label_11, 0, 0, 1, 1)
        self.spinBoxDmestras = QtWidgets.QSpinBox(self.frame_2)
        self.spinBoxDmestras.setObjectName("spinBoxDmestras")
        self.gridLayout_11.addWidget(self.spinBoxDmestras, 0, 1, 1, 1)
        self.gridLayout_12.addLayout(self.gridLayout_11, 1, 0, 1, 1)
        self.gridLayout_14.addLayout(self.gridLayout_12, 0, 0, 1, 1)
        self.gridLayout_13 = QtWidgets.QGridLayout()
        self.gridLayout_13.setObjectName("gridLayout_13")
        self.gridLayout_8 = QtWidgets.QGridLayout()
        self.gridLayout_8.setObjectName("gridLayout_8")
        self.label_8 = QtWidgets.QLabel(self.frame_2)
        self.label_8.setObjectName("label_8")
        self.gridLayout_8.addWidget(self.label_8, 0, 0, 1, 1)
        self.comboBoxCor2 = QtWidgets.QComboBox(self.frame_2)
        self.comboBoxCor2.setMaximumSize(QtCore.QSize(35, 20))
        self.comboBoxCor2.setObjectName("comboBoxCor2")
        self.gridLayout_8.addWidget(self.comboBoxCor2, 0, 1, 1, 1)
        self.gridLayout_13.addLayout(self.gridLayout_8, 0, 0, 1, 1)
        self.gridLayout_10 = QtWidgets.QGridLayout()
        self.gridLayout_10.setObjectName("gridLayout_10")
        self.label_10 = QtWidgets.QLabel(self.frame_2)
        self.label_10.setObjectName("label_10")
        self.gridLayout_10.addWidget(self.label_10, 0, 0, 1, 1)
        self.doubleSpinBoxDsimples = QtWidgets.QDoubleSpinBox(self.frame_2)
        self.doubleSpinBoxDsimples.setObjectName("doubleSpinBoxDsimples")
        self.gridLayout_10.addWidget(self.doubleSpinBoxDsimples, 0, 1, 1, 1)
        self.gridLayout_13.addLayout(self.gridLayout_10, 1, 0, 1, 1)
        self.gridLayout_14.addLayout(self.gridLayout_13, 0, 1, 1, 1)
        self.gridLayout_15.addLayout(self.gridLayout_14, 0, 0, 1, 1)
        self.gridLayout_17.addWidget(self.frame_2, 1, 0, 1, 1)
        self.label_9 = QtWidgets.QLabel(self.frame_3)
        self.label_9.setObjectName("label_9")
        self.gridLayout_17.addWidget(self.label_9, 0, 0, 1, 1)
        self.gridLayout_18.addLayout(self.gridLayout_17, 1, 0, 1, 1)
        self.gridLayout_20.addWidget(self.frame_3, 0, 0, 1, 1)
        self.gridLayout_19 = QtWidgets.QGridLayout()
        self.gridLayout_19.setObjectName("gridLayout_19")
        self.pushButtonOK = QtWidgets.QPushButton(Dialog)
        self.pushButtonOK.setObjectName("pushButtonOK")
        self.gridLayout_19.addWidget(self.pushButtonOK, 0, 0, 1, 1)
        self.pushButtonFechar = QtWidgets.QPushButton(Dialog)
        self.pushButtonFechar.setObjectName("pushButtonFechar")
        self.gridLayout_19.addWidget(self.pushButtonFechar, 0, 1, 1, 1)
        self.gridLayout_20.addLayout(self.gridLayout_19, 1, 0, 1, 1)
        self.gridLayout_21.addLayout(self.gridLayout_20, 0, 0, 1, 1)

        self.retranslateUi(Dialog)
        QtCore.QMetaObject.connectSlotsByName(Dialog)

        self.config_botoes() #configura os botões da configuração

        # Define cores padrão
        self.comboBoxCor3.setCurrentIndex(self.comboBoxCor3.findData("Red"))
        self.comboBoxCor4.setCurrentIndex(self.comboBoxCor4.findData("Yellow"))
        self.comboBoxCor1.setCurrentIndex(self.comboBoxCor1.findData("Red"))
        self.comboBoxCor2.setCurrentIndex(self.comboBoxCor2.findData("Yellow"))

        # Seleciona o radioButtonCentro como padrão
        self.radioButtonCentro.setChecked(True)

        # Define valores padrão para spinBoxDmestras e doubleSpinBoxDsimples
        self.spinBoxDmestras.setValue(5)
        self.doubleSpinBoxDsimples.setValue(0.5)

        # Define valores padrão para spinBoxTamanho e spinBoxRepete
        self.spinBoxTamanho.setValue(8)
        self.spinBoxRepete.setValue(100)

        # Configurações do spinBoxDmestras
        self.spinBoxDmestras.setRange(1, 50)
        self.spinBoxDmestras.setSingleStep(1)
        self.spinBoxDmestras.setValue(5)

        # Configurações do doubleSpinBoxDsimples
        self.doubleSpinBoxDsimples.setRange(0.1, 10.0)
        self.doubleSpinBoxDsimples.setSingleStep(0.5)
        self.doubleSpinBoxDsimples.setValue(0.5)

        # Configurações do spinBoxTamanho
        self.spinBoxTamanho.setRange(1, 15)
        self.spinBoxTamanho.setSingleStep(1)
        self.spinBoxTamanho.setValue(8)

        # Configurações do spinBoxRepete
        self.spinBoxRepete.setRange(10, 1000)
        self.spinBoxRepete.setSingleStep(50)
        self.spinBoxRepete.setValue(100)

        # Conecta o botão OK para salvar as configurações
        self.pushButtonOK.clicked.connect(self.save_configurations)
        
        self.spinBoxDmestras.valueChanged.connect(self.update_double_spin_box_range)

        self.pushButtonFechar.clicked.connect(self.close_dialog)  # Conecte o botão para fechar o diálogo

    def close_dialog(self):
        """
        Fecha o diálogo de configuração.

        Funcionalidades:
        - Chama o método `close()` para fechar a janela de diálogo atual.
        - Não salva nenhuma alteração feita pelo usuário, apenas fecha a interface sem aplicar mudanças.
        """

        # Fecha o diálogo
        self.close()

    def update_double_spin_box_range(self):
        """
        Atualiza o limite máximo do doubleSpinBoxDsimples com base no valor de spinBoxDmestras e no valor máximo fixo.

        Funcionalidades:
        - Calcula o novo valor máximo do `doubleSpinBoxDsimples` com base no valor atual de `spinBoxDmestras`.
        - Garante que o valor máximo de `doubleSpinBoxDsimples` nunca seja maior que o valor de `spinBoxDmestras` menos 0.5, 
          com um limite superior de 10.0.
        - Se o valor atual de `doubleSpinBoxDsimples` for maior que o novo limite máximo, ele é ajustado para o valor máximo permitido.
        """
        # Calcula o novo valor máximo para o doubleSpinBoxDsimples
        max_value = min(self.spinBoxDmestras.value() - 0.5, 10.0)  # O valor máximo é limitado a 10.0 ou o valor de spinBoxDmestras - 0.5
        self.doubleSpinBoxDsimples.setMaximum(max_value)  # Define o novo valor máximo para o doubleSpinBoxDsimples

        # Verifica se o valor atual de doubleSpinBoxDsimples excede o novo valor máximo e ajusta, se necessário
        if self.doubleSpinBoxDsimples.value() >= max_value:
            self.doubleSpinBoxDsimples.setValue(max_value)  # Ajusta o valor atual para o novo valor máximo, se for maior

    def save_configurations(self):
        """
        Armazena as cores, posição e valores dos spin boxes selecionados para uso posterior.

        Funcionalidades:
        - Armazena as cores selecionadas pelos combo boxes `comboBoxCor1`, `comboBoxCor2`, `comboBoxCor3`, e `comboBoxCor4` 
          em um dicionário chamado `selected_colors`.
        - Determina a posição selecionada pelos radio buttons (`Centro`, `Acima`, `Abaixo`) e armazena em `selected_position`.
        - Armazena os valores dos spin boxes para desníveis (`spinBoxDmestras`, `doubleSpinBoxDsimples`), tamanho dos rótulos
          (`spinBoxTamanho`), e repetição de rótulos (`spinBoxRepete`).
        - Após salvar as configurações, o diálogo é fechado com `accept()`, sinalizando que as alterações foram confirmadas.
        """
        # Armazena as cores selecionadas pelos combo boxes em um dicionário
        self.selected_colors = {
            'cor1': self.comboBoxCor1.currentData(),
            'cor2': self.comboBoxCor2.currentData(),
            'cor3': self.comboBoxCor3.currentData(),
            'cor4': self.comboBoxCor4.currentData()}

        # Verifica qual dos radio buttons está marcado e armazena a posição dos rótulos
        if self.radioButtonCentro.isChecked():
            self.selected_position = 'Centro'
        elif self.radioButtonAcima.isChecked():
            self.selected_position = 'Acima'
        elif self.radioButtonAbaixo.isChecked():
            self.selected_position = 'Abaixo'

        # Armazena os valores dos spin boxes (desníveis, tamanho do texto, repetição)
        self.desnivel_m = self.spinBoxDmestras.value()       # Desnível mestre
        self.desnivel_s = self.doubleSpinBoxDsimples.value()  # Desnível simples
        self.tamanho = self.spinBoxTamanho.value()            # Tamanho do texto dos rótulos
        self.repeticao = self.spinBoxRepete.value()           # Distância de repetição dos rótulos

        # Fecha o diálogo, confirmando que as configurações foram salvas
        self.accept()

    def config_botoes(self):
        """
        Configura os botões de seleção de cor com menus personalizados.

        Funcionalidades:
        - Chama a função `setup_color_combobox()` para cada combo box de seleção de cor (comboBoxCor1, comboBoxCor2, comboBoxCor3, comboBoxCor4).
        - Cada combo box é configurado para exibir uma lista personalizada de cores, permitindo ao usuário selecionar a cor desejada para diferentes itens.
        """
        # Configura os combo boxes de seleção de cor utilizando a função setup_color_combobox
        self.setup_color_combobox(self.comboBoxCor1)  # Configura o comboBoxCor1
        self.setup_color_combobox(self.comboBoxCor2)  # Configura o comboBoxCor2
        self.setup_color_combobox(self.comboBoxCor3)  # Configura o comboBoxCor3
        self.setup_color_combobox(self.comboBoxCor4)  # Configura o comboBoxCor4

    def setup_color_combobox(self, combobox):
        """
        Adiciona as cores com texto traduzido, mantendo uma chave interna
        estável em inglês para a simbologia e para a exportação DXF.
        """
        colors = [
            ("Red", self.tr("Red"), 255, 0, 0),
            ("Yellow", self.tr("Yellow"), 255, 255, 0),
            ("Green", self.tr("Green"), 0, 255, 0),
            ("Cyan", self.tr("Cyan"), 0, 255, 255),
            ("Blue", self.tr("Blue"), 0, 0, 255),
            ("Magenta", self.tr("Magenta"), 255, 0, 255),
            ("Gray", self.tr("Gray"), 180, 180, 180)]

        combobox.clear()

        for chave, texto, r, g, b in colors:
            icon = self.create_color_icon(r, g, b)
            combobox.addItem(icon, texto, chave)

    def create_color_icon(self, r, g, b):
        """
        Cria um ícone quadrado colorido de 20x20 pixels com base nos valores RGB fornecidos.

        Parâmetros:
        - r (int): O valor de vermelho (Red) no código de cor RGB.
        - g (int): O valor de verde (Green) no código de cor RGB.
        - b (int): O valor de azul (Blue) no código de cor RGB.

        Funcionalidades:
        - Cria um `QPixmap` de 20x20 pixels.
        - Preenche o pixmap com a cor especificada pelos valores RGB.
        - Converte o pixmap em um ícone (`QIcon`) para ser usado em combo boxes ou outros widgets de interface.
        
        Retorno:
        - `QIcon`: O ícone colorido correspondente aos valores RGB fornecidos.
        """
        # Cria um QPixmap de 20x20 pixels
        pixmap = QtGui.QPixmap(20, 20)
        
        # Preenche o pixmap com a cor especificada pelos valores RGB
        pixmap.fill(QtGui.QColor(r, g, b))
        
        # Converte o pixmap em um ícone e retorna
        return QtGui.QIcon(pixmap)

    def retranslateUi(self, Dialog):
        """
        Atualiza os textos da interface gráfica para garantir a compatibilidade com diferentes idiomas.

        Parâmetros:
        - Dialog (QDialog): A janela de diálogo onde os textos serão atualizados.
        """
        Dialog.setWindowTitle(self.tr("Configurações de Exportação"))

        # Títulos e labels
        self.label_6.setText(self.tr("Configuração dos Rótulos das Curvas de Níveis"))
        self.label_2.setText(self.tr("Curvas Mestras"))
        self.label_7.setText(self.tr("Curvas Simples"))
        self.label_3.setText(self.tr("Posição:"))
        self.label_4.setText(self.tr("Tamanho:"))
        self.label_5.setText(self.tr("Repetição:"))

        self.label_9.setText(self.tr("Configuração das Curvas de Níveis"))
        self.label.setText(self.tr("Curvas Mestras"))
        self.label_11.setText(self.tr("Desníveis M"))
        self.label_8.setText(self.tr("Curvas Simples"))
        self.label_10.setText(self.tr("Desníveis S"))

        # Radio buttons
        self.radioButtonAcima.setText(self.tr("Acima"))
        self.radioButtonCentro.setText(self.tr("Centro"))
        self.radioButtonAbaixo.setText(self.tr("Abaixo"))

        # Botões
        self.pushButtonOK.setText(self.tr("OK"))
        self.pushButtonFechar.setText(self.tr("Fechar"))
