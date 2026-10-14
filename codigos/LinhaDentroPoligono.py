from qgis.core import QgsProject, QgsMessageLog, Qgis, QgsVectorLayer, QgsWkbTypes, QgsMapSettings, QgsMapRendererCustomPainterJob, QgsGeometry, QgsPointXY, QgsFeature, QgsLineSymbol, QgsCoordinateReferenceSystem, QgsCoordinateTransform
from qgis.PyQt.QtWidgets import QDialog, QCheckBox, QGraphicsScene, QGraphicsPixmapItem, QToolTip, QGraphicsLineItem, QColorDialog, QProgressBar, QApplication, QPushButton
from qgis.PyQt.QtGui import QImage, QPainter, QPixmap, QColor, QPen, QIntValidator, QCursor, QDesktopServices
from qgis.PyQt.QtCore import Qt, QSize, QDateTime, QCoreApplication, QUrl
from qgis.utils import iface
from qgis.PyQt import uic
import math
import os

FORM_CLASS, _ = uic.loadUiType(os.path.join(
    os.path.dirname(__file__), 'LinhasdentroPoligono.ui'))

class DentroManager(QDialog, FORM_CLASS):
    def __init__(self, parent=None):
        """Constructor."""
        super(DentroManager, self).__init__(parent)
        # Configura a interface do usuário a partir do Designer.
        self.setupUi(self)

        self.iface = iface

        # Inicializa o atributo de cor (nenhuma cor definida inicialmente)
        self.linha_cor = None

        # Configuração do lineEditAngulo: cor cinza e texto centralizado
        self.lineEditAngulo.setValidator(QIntValidator(0, 360, self))
        self.lineEditAngulo.setStyleSheet("background-color: lightgray;")
        self.lineEditAngulo.setAlignment(Qt.AlignmentFlag.AlignCenter)
        
        # Define um tooltip inicial e duração para o horizontalSlider.
        self.horizontalSlider.setToolTip(self.tr("Ângulo: {angle}°").format(angle=self.horizontalSlider.value()))
        self.horizontalSlider.setToolTipDuration(3000)

        self.scenePoligono = QGraphicsScene()
        self.graphicsView.setScene(self.scenePoligono)

        # Altera o título da janela
        self.setWindowTitle(self.tr("Linhas Dentro de Polígonos"))

        # Preenche o comboBox com camadas de linha
        self.populate_combo_box()

        # Conecta os sinais aos slots
        self.connect_signals()

    def tr(self, message):
        """
        Traduz textos deste diálogo.
        O contexto precisa ser estável para o Qt Linguist encontrar as traduções.
        """
        return QCoreApplication.translate("DentroManager", message)

    def connect_signals(self):

       # Conecta a mudança de seleção no comboBoxCamada para atualizar o checkBoxSeleciona
        self.comboBoxCamada.currentIndexChanged.connect(self.update_checkBoxSeleciona)
        self.comboBoxCamada.currentIndexChanged.connect(self.display_polygon)  # Conexão para atualizar o graphicsView

        # Conecta também para atualizar os sinais da camada (selectionChanged)
        self.comboBoxCamada.currentIndexChanged.connect(self.update_layer_connections)

        # Conecta o horizontalSlider para atualizar o tooltip e o lineEditAngulo
        self.horizontalSlider.valueChanged.connect(self.atualizar_angulo)

        # Conecta o lineEditAngulo para atualizar o horizontalSlider imediatamente
        self.lineEditAngulo.textChanged.connect(self.atualizar_slider_pelo_lineEdit)
        self.lineEditAngulo.editingFinished.connect(self.atualizar_slider_pelo_lineEdit)

        # Conecta o clique do botão pushButtonExecutar para executar
        self.pushButtonExecutar.clicked.connect(self.executar)

        # Conecta sinais do projeto para atualizar comboBox quando camadas forem adicionadas, removidas ou renomeadas
        QgsProject.instance().layersAdded.connect(self.populate_combo_box)
        QgsProject.instance().layersRemoved.connect(self.populate_combo_box)
        QgsProject.instance().layerWillBeRemoved.connect(self.populate_combo_box)

        # Conecta a alteração do lineEditAngulo para atualizar o horizontalSlider
        self.lineEditAngulo.editingFinished.connect(self.atualizar_slider_pelo_lineEdit)

        # Conecta o pushButtonCor ao método para selecionar a cor
        self.pushButtonCor.clicked.connect(self.selecionar_cor)

        # Atualiza o estado do pushButtonExecutar quando a camada muda
        self.comboBoxCamada.currentIndexChanged.connect(self.update_pushButtonExecutar)
        
        # Conecta o doubleSpinBoxEspassamento para atualizar o estado do botão
        self.doubleSpinBoxEspassamento.valueChanged.connect(self.update_pushButtonExecutar)

        # Conecta o botão pushButtonFechar
        self.pushButtonFechar.clicked.connect(self.close)

        #  Deleta a camada de linhas com segurança
        QgsProject.instance().layerWillBeRemoved.connect(self._on_layer_removed)

    def showEvent(self, event):
        """
        Sobrescreve o evento de exibição do diálogo para resetar os Widgets.
        """
        super(DentroManager, self).showEvent(event)

        # Reset do checkBoxSeleciona
        checkBox = self.findChild(QCheckBox, 'checkBoxSeleciona')
        if checkBox:
            checkBox.setChecked(False)
            checkBox.setEnabled(False)
        
        # Reset do horizontalSlider para 0 (ou valor padrão desejado)
        self.horizontalSlider.setValue(0)
        
        # Reset do lineEditAngulo para "0"
        self.lineEditAngulo.setText("0")
        
        # Reset do doubleSpinBoxEspassamento para 10 (ou outro valor padrão)
        self.doubleSpinBoxEspassamento.setValue(10)
        
        # Reset do pushButtonCor para o estilo padrão e variável interna
        self.pushButtonCor.setStyleSheet("")
        self.linha_cor = None

        self.populate_combo_box()  # Atualiza o comboBoxCamada com as camadas disponíveis

        self.update_checkBoxSeleciona()  # Atualiza o estado do checkBoxSeleciona com base nas feições selecionadas

        self.display_polygon() # Ajusta a visualização quando o diálogo é mostrado

        self.update_pushButtonExecutar()  # Atualiza o estado do botão executar

        self.update_layer_connections()  # Conecta os sinais da camada atual

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
        progressMessageBar = self.iface.messageBar().createMessage(self.tr("Gerando Camadas de Pontos de Apoio..."))
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

        if tipo == "Sucesso":
            msg = bar.createMessage(self.tr("Sucesso"), texto)

            if caminho_pasta:
                botao_abrir_pasta = QPushButton(self.tr("Abrir Pasta"))
                botao_abrir_pasta.clicked.connect(
                    lambda _checked=False, caminho=caminho_pasta:
                        QDesktopServices.openUrl(
                            QUrl.fromLocalFile(
                                os.path.abspath(os.fspath(caminho)))))
                msg.layout().insertWidget(1, botao_abrir_pasta)

            if caminho_arquivo:
                botao_abrir_arquivo = QPushButton(self.tr("Abrir Arquivo"))
                botao_abrir_arquivo.clicked.connect(
                    lambda _checked=False, caminho=caminho_arquivo:
                        QDesktopServices.openUrl(
                            QUrl.fromLocalFile(
                                os.path.abspath(os.fspath(caminho)))))
                msg.layout().insertWidget(2, botao_abrir_arquivo)

            bar.pushWidget(msg, level=Qgis.MessageLevel.Success, duration=duracao )

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
        layer_id = self.comboBoxCamada.currentData()  # Obtém o ID da camada atualmente selecionada no comboBoxCamada
        if layer_id:  # Verifica se há uma camada selecionada
            layer = QgsProject.instance().mapLayer(layer_id)  # Obtém a camada correspondente ao ID
            if layer:  # Verifica se a camada existe
                layer.selectionChanged.connect(self.update_checkBoxSeleciona)  # Conecta o sinal selectionChanged à função update_checkBoxSeleciona
                layer.selectionChanged.connect(self.display_polygon)
                self.update_checkBoxSeleciona()  # Atualiza o estado do checkBoxSeleciona imediatamente
        else:  # Se não houver uma camada selecionada, desativa o checkBoxSeleciona
            self.update_checkBoxSeleciona()  # Chama a função para desativar o checkBoxSeleciona

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

        # Atualiza o estado do checkbox e a visualização
        self.update_checkBoxSeleciona()
        self.display_polygon()
        
        # Reconecta os sinais da camada atual, garantindo que o selectionChanged esteja conectado
        self.update_layer_connections()
        self.update_pushButtonExecutar()  # Atualiza o estado do botão

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

    def display_polygon(self):
        """
        Atualiza a exibição do(s) polígono(s) no QGraphicsView.
        - Se houver feições selecionadas, exibe e aproxima para elas.
        - Caso contrário, exibe todos os polígonos da camada.
        """
        self.scenePoligono.clear()
        layer_id = self.comboBoxCamada.currentData()
        layer = QgsProject.instance().mapLayer(layer_id)

        if not layer or not isinstance(layer, QgsVectorLayer):
            return

        # Filtra apenas polígonos
        feats = [f for f in layer.getFeatures() if f.geometry().type() == QgsWkbTypes.GeometryType.PolygonGeometry]
        if not feats:
            if self.isVisible():
                self.mostrar_mensagem(self.tr("A camada de polígono não contém feições."), "Erro")
            return

        selected = layer.selectedFeatures()
        if selected:
            # Unifica os polígonos selecionados
            geom = QgsGeometry.unaryUnion([f.geometry() for f in selected])
            bounding_box = geom.boundingBox()
        else:
            # Unifica todos os polígonos da camada
            geom = QgsGeometry.unaryUnion([f.geometry() for f in feats])
            bounding_box = geom.boundingBox()

        if geom is None or geom.isEmpty() or bounding_box.isNull():
            if self.isVisible():
                self.mostrar_mensagem(self.tr("A geometria não contém dados válidos."), "Erro")
            return

        # Configuração do renderizador
        map_settings = QgsMapSettings()
        map_settings.setLayers([layer])
        map_settings.setBackgroundColor(QColor(255, 255, 255))
        width = self.graphicsView.viewport().width()
        height = self.graphicsView.viewport().height()
        map_settings.setOutputSize(QSize(width, height))
        map_settings.setExtent(bounding_box)

        # Renderiza a imagem
        image = QImage(width, height, QImage.Format.Format_ARGB32)
        image.fill(Qt.GlobalColor.transparent)
        painter = QPainter(image)
        render_job = QgsMapRendererCustomPainterJob(map_settings, painter)
        render_job.start()
        render_job.waitForFinished()
        painter.end()

        # Exibe no QGraphicsView
        pixmap = QPixmap.fromImage(image)
        pixmap_item = QGraphicsPixmapItem(pixmap)
        self.scenePoligono.addItem(pixmap_item)
        self.graphicsView.setSceneRect(pixmap_item.boundingRect())
        self.graphicsView.fitInView(self.scenePoligono.sceneRect(), Qt.AspectRatioMode.KeepAspectRatio)

    def atualizar_angulo(self, value):
        """
        Atualiza o tooltip do horizontalSlider, o texto do lineEditAngulo e exibe o tooltip
        próximo à posição atual do cursor enquanto o slider é movido.
        """
        tooltip = self.tr("Ângulo: {angle}°").format(angle=value)
        self.horizontalSlider.setToolTip(tooltip)
        if self.lineEditAngulo.text() != str(value):
            self.lineEditAngulo.setText(str(value))
        # Exibe o tooltip próximo ao cursor enquanto o slider é movido
        QToolTip.showText(QCursor.pos(), tooltip, self.horizontalSlider)

    def atualizar_slider_pelo_lineEdit(self, text=None):
        """
        Atualiza o horizontalSlider com base no valor inserido no lineEditAngulo.
        Essa função é chamada sempre que o texto mudar ou quando a edição for finalizada.
        """
        if text is None:
            text = self.lineEditAngulo.text()
        if text == '':
            return
        try:
            value = int(text)
        except ValueError:
            return
        # Garante que o valor esteja dentro do intervalo (0 a 360)
        value = max(min(value, self.horizontalSlider.maximum()), self.horizontalSlider.minimum())
        if self.horizontalSlider.value() != value:
            self.horizontalSlider.setValue(value)

    def executar(self):
        """
        Gera uma camada de linhas dentro dos polígonos da camada selecionada.
        
        Se o checkBoxSeleciona estiver marcado, usa apenas as feições selecionadas;
        caso contrário, utiliza todas as feições da camada.
        
        As linhas são geradas com a direção definida pelo horizontalSlider (ângulo em graus)
        e com espaçamento definido pelo doubleSpinBoxEspassamento, utilizando uma abordagem
        que funciona mesmo se a camada de polígonos estiver em coordenadas geográficas.
        
        Se o CRS for geográfico, as geometrias serão reprojetadas para um CRS projetado (zona UTM),
        os cálculos ocorrerão em unidades lineares e, ao final, as linhas serão transformadas de volta.
        
        Uma barra de progresso é exibida durante o processamento.
        A camada resultante é adicionada ao projeto.
        """
        # Obtém a camada de polígonos selecionada
        polygon_layer_id = self.comboBoxCamada.currentData()
        if not polygon_layer_id:
            self.mostrar_mensagem(self.tr("Nenhuma camada de polígono selecionada."), "Erro")
            return

        polygon_layer = QgsProject.instance().mapLayer(polygon_layer_id)
        if not polygon_layer:
            self.mostrar_mensagem(self.tr("A camada selecionada não é válida."), "Erro")
            return

        # Determina se usará as feições selecionadas ou todas as feições da camada
        checkBoxSeleciona = self.findChild(QCheckBox, 'checkBoxSeleciona')
        if checkBoxSeleciona and checkBoxSeleciona.isChecked():
            polygon_features = polygon_layer.selectedFeatures()
            if not polygon_features:
                self.mostrar_mensagem(self.tr("Nenhuma feição selecionada na camada."), "Erro")
                return
        else:
            polygon_features = list(polygon_layer.getFeatures())
            if not polygon_features:
                self.mostrar_mensagem(self.tr("A camada não contém feições."), "Erro")
                return

        spacing = self.doubleSpinBoxEspassamento.value()
        angle_deg = self.horizontalSlider.value()  # Ângulo em graus (0 a 360)
        angle_rad = math.radians(angle_deg)
        d_x = math.cos(angle_rad)
        d_y = math.sin(angle_rad)
        p_x = -math.sin(angle_rad)
        p_y = math.cos(angle_rad)

        # Se o CRS da camada de polígonos for geográfico, converte para um CRS projetado.
        source_crs = polygon_layer.crs()
        if source_crs.isGeographic():
            # Usa o centro do primeiro polígono para determinar a zona UTM
            first_geom = polygon_features[0].geometry()
            center = first_geom.centroid().asPoint()
            lon = center.x()
            lat = center.y()
            utm_zone = int((lon + 180) / 6) + 1
            if lat >= 0:
                epsg_code = 32600 + utm_zone
            else:
                epsg_code = 32700 + utm_zone
            proj_crs = QgsCoordinateReferenceSystem(epsg_code)
            transform_to_proj = QgsCoordinateTransform(source_crs, proj_crs, QgsProject.instance())
            transform_to_source = QgsCoordinateTransform(proj_crs, source_crs, QgsProject.instance())
        else:
            transform_to_proj = None
            transform_to_source = None

        # Inicia a barra de progresso: cada polígono é uma etapa
        progressBar, progressMessageBar = self.iniciar_progress_bar(total_steps=len(polygon_features))
        features_list = []
        processed = 0

        for polygon_feature in polygon_features:
            processed += 1
            progressBar.setValue(processed)
            QApplication.processEvents()

            polygon_geom = polygon_feature.geometry()
            if polygon_geom.isEmpty():
                continue

            # Trabalha com uma cópia da geometria
            polygon_geom_work = QgsGeometry.fromWkt(polygon_geom.asWkt())
            if transform_to_proj:
                polygon_geom_work.transform(transform_to_proj)

            bbox = polygon_geom_work.boundingBox()
            # Para gerar as linhas inclinadas, usamos os cantos do bounding box
            corners = [
                QgsPointXY(bbox.xMinimum(), bbox.yMinimum()),
                QgsPointXY(bbox.xMinimum(), bbox.yMaximum()),
                QgsPointXY(bbox.xMaximum(), bbox.yMinimum()),
                QgsPointXY(bbox.xMaximum(), bbox.yMaximum())]
            offsets = [pt.x() * p_x + pt.y() * p_y for pt in corners]
            offset_min = min(offsets)
            offset_max = max(offsets)

            # Define o centro do bbox para servir de referência
            center = QgsPointXY((bbox.xMinimum() + bbox.xMaximum()) / 2, (bbox.yMinimum() + bbox.yMaximum()) / 2)
            center_proj = center.x() * p_x + center.y() * p_y

            current_offset = offset_max
            while current_offset >= offset_min:
                delta = current_offset - center_proj
                base = QgsPointXY(center.x() + delta * p_x, center.y() + delta * p_y)
                L = math.sqrt(bbox.width()**2 + bbox.height()**2) * 2
                start = QgsPointXY(base.x() - d_x * L, base.y() - d_y * L)
                end = QgsPointXY(base.x() + d_x * L, base.y() + d_y * L)
                linha = QgsGeometry.fromPolylineXY([start, end])
                intersec = polygon_geom_work.intersection(linha)
                if not intersec.isEmpty():
                    if intersec.type() == QgsWkbTypes.GeometryType.LineGeometry:
                        if intersec.isMultipart():
                            for parte in intersec.asMultiPolyline():
                                if parte:
                                    parte_ordenada = sorted(parte, key=lambda pt: pt.x() * d_x + pt.y() * d_y)
                                    feat = QgsFeature()
                                    geom_line = QgsGeometry.fromPolylineXY(parte_ordenada)
                                    # Transforma de volta para o CRS original, se necessário
                                    if transform_to_source:
                                        geom_line.transform(transform_to_source)
                                    feat.setGeometry(geom_line)
                                    features_list.append(feat)
                        else:
                            pts = intersec.asPolyline()
                            if pts:
                                pts_ordenados = sorted(pts, key=lambda pt: pt.x() * d_x + pt.y() * d_y)
                                feat = QgsFeature()
                                geom_line = QgsGeometry.fromPolylineXY(pts_ordenados)
                                if transform_to_source:
                                    geom_line.transform(transform_to_source)
                                feat.setGeometry(geom_line)
                                features_list.append(feat)
                current_offset -= spacing

        self.iface.messageBar().popWidget(progressMessageBar)

        if not features_list:
            self.mostrar_mensagem(self.tr("Não foi possível gerar linhas dentro dos polígonos."), "Erro")
            return

        # Gera as features
        feats = self._gerar_linhas(polygon_features, spacing, angle_deg, transform_to_proj, transform_to_source)

        # Gera as features
        feats = self._gerar_linhas(polygon_features, spacing, angle_deg, transform_to_proj, transform_to_source)

        if not feats:
            self.mostrar_mensagem(self.tr("Não foi possível gerar linhas."), "Erro")
            return

        crs = polygon_layer.crs()

        nome_poligono = self.comboBoxCamada.currentText()
        nome_base = self.tr("LinhasDentro_{nome_poligono}").format(nome_poligono=nome_poligono)
        nome = self._gerar_nome_unico(nome_base)

        uri = f"LineString?crs={crs.authid()}"
        layer = QgsVectorLayer(uri, nome, "memory")
        layer.dataProvider().addFeatures(feats)
        layer.updateExtents()

        if self.linha_cor:
            sym = QgsLineSymbol.createSimple({'color': self.linha_cor.name()})
            layer.renderer().setSymbol(sym)
        QgsProject.instance().addMapLayer(layer)
        self._layer_linhas_id = layer.id()   # ← sempre guarda o id da nova

        self.mostrar_mensagem(self.tr("Camada de linhas criada."), "Sucesso")

        # Atualização automática só será ativada para essa camada nova
        self._desconectar_atualizacao_automatica()
        if not getattr(self, "_rt_connected", False):
            self.horizontalSlider.valueChanged.connect(self.atualizar_linhas_rt)
            self.lineEditAngulo.editingFinished.connect(self.atualizar_linhas_rt)
            self.doubleSpinBoxEspassamento.valueChanged.connect(self.atualizar_linhas_rt)
            self._rt_connected = True

    def _gerar_nome_unico(self, nome_base):
        """Gera nome único para camada, evitando duplicidade no projeto."""
        layers_names = [layer.name() for layer in QgsProject.instance().mapLayers().values()]
        nome = nome_base
        contador = 1
        while nome in layers_names:
            nome = f"{nome_base}_{contador}"
            contador += 1
        return nome

    def _get_layer_linhas(self):
        """
        Recupera a camada de linhas pelo ID salvo, garantindo que seja válida.
        Parâmetros:
            Nenhum (usa atributo interno da classe).
        Retorno:
            QgsVectorLayer ou None: Retorna a camada de linhas se existir e for válida;
            caso contrário, retorna None.
        """
        layer_id = getattr(self, "_layer_linhas_id", None)  # Obtém o ID salvo da camada
        if not layer_id:
            return None
        layer = QgsProject.instance().mapLayer(layer_id)    # Busca a camada pelo ID no projeto
        return layer if layer and layer.isValid() else None # Retorna a camada válida, senão None

    def _on_layer_removed(self, layer_id):
        """
        Remove o atributo interno de ID da camada de linhas se a camada for removida do projeto.
        Parâmetros:
            layer_id (str): ID da camada removida do QGIS.
        Retorno:
            None
        """
        # Se o ID removido for o da camada de linhas, limpa o atributo salvo
        if getattr(self, "_layer_linhas_id", None) == layer_id:
            delattr(self, "_layer_linhas_id")

    def _gerar_linhas(self, polygon_features, spacing, angle_deg, transform_to_proj, transform_to_source):
        """
        Gera uma lista de linhas (QgsFeature) preenchendo polígonos conforme o ângulo e espaçamento definidos.

        Parâmetros:
            polygon_features (list): Lista de feições poligonais de entrada.
            spacing (float): Espaçamento entre as linhas geradas.
            angle_deg (float): Ângulo das linhas em graus.
            transform_to_proj (QgsCoordinateTransform or None): Transformação para CRS projetado, se necessário.
            transform_to_source (QgsCoordinateTransform or None): Transformação de volta para o CRS original, se necessário.

        Retorno:
            list: Lista de QgsFeature (linhas) geradas dentro dos polígonos.
        """
        feats_out = []
        angle_rad = math.radians(angle_deg)                # Converte ângulo para radianos
        d_x, d_y  = math.cos(angle_rad), math.sin(angle_rad)
        p_x, p_y  = -d_y, d_x                             # Vetor perpendicular

        for polygon_geom in (f.geometry() for f in polygon_features):
            if polygon_geom.isEmpty():
                continue

            geom_work = QgsGeometry(polygon_geom)          # Faz uma cópia da geometria
            if transform_to_proj:
                geom_work.transform(transform_to_proj)     # Transforma para CRS projetado, se necessário

            bbox = geom_work.boundingBox()                 # Calcula bounding box do polígono
            L = math.hypot(bbox.width(), bbox.height()) * 2

            # Calcula os cantos do bounding box
            corners = [
                QgsPointXY(bbox.xMinimum(), bbox.yMinimum()),
                QgsPointXY(bbox.xMinimum(), bbox.yMaximum()),
                QgsPointXY(bbox.xMaximum(), bbox.yMinimum()),
                QgsPointXY(bbox.xMaximum(), bbox.yMaximum())]
            offsets = [pt.x()*p_x + pt.y()*p_y for pt in corners]
            o_min, o_max = min(offsets), max(offsets)

            # Centro do bbox serve de referência
            center = QgsPointXY((bbox.xMinimum()+bbox.xMaximum())/2,
                                (bbox.yMinimum()+bbox.yMaximum())/2)
            o_center = center.x()*p_x + center.y()*p_y

            off = o_max
            while off >= o_min:
                delta = off - o_center
                base  = QgsPointXY(center.x() + delta*p_x, center.y() + delta*p_y)
                start = QgsPointXY(base.x() - d_x*L, base.y() - d_y*L)
                end   = QgsPointXY(base.x() + d_x*L, base.y() + d_y*L)
                linha = QgsGeometry.fromPolylineXY([start, end])
                inter = geom_work.intersection(linha)

                # Se intersectar e for linha, processa cada segmento
                if not inter.isEmpty() and inter.type() == QgsWkbTypes.GeometryType.LineGeometry:
                    if inter.isMultipart():
                        segmentos = inter.asMultiPolyline()
                    else:
                        segmentos = [inter.asPolyline()]

                    for seg in segmentos:
                        if not seg:
                            continue
                        seg = sorted(seg, key=lambda p: p.x()*d_x + p.y()*d_y)   # Ordena pontos do segmento
                        g   = QgsGeometry.fromPolylineXY(seg)
                        if transform_to_source:
                            g.transform(transform_to_source)                      # Volta ao SRC original, se preciso
                        f = QgsFeature()
                        f.setGeometry(g)
                        feats_out.append(f)
                off -= spacing
        return feats_out

    def atualizar_linhas_rt(self, *_):
        """
        Atualiza dinamicamente as linhas dentro dos polígonos quando o usuário altera
        o ângulo ou o espaçamento.

        Parâmetros:
            *_: Aceita argumentos opcionais (padrão dos sinais Qt). Não são utilizados.

        Retorno:
            None. (A função atua diretamente sobre a camada de linhas existente.)

        Funcionalidades:
        - Recupera a camada de linhas pelo ID salvo.
        - Obtém a camada de polígonos selecionada no comboBox.
        - Usa apenas feições selecionadas se o checkBoxSeleciona estiver marcado.
        - Calcula os parâmetros de projeção, ângulo e espaçamento atuais.
        - Gera as linhas conforme os parâmetros definidos pelo usuário.
        - Substitui as feições da camada de linhas por novas, refletindo as alterações.
        - Atualiza a visualização da camada de linhas no QGIS em tempo real.
        """
        layer = self._get_layer_linhas()
        if not layer:
            return  # Não há camada de linhas para atualizar

        # Obtém a camada de polígonos selecionada
        polygon_layer_id = self.comboBoxCamada.currentData()
        polygon_layer = QgsProject.instance().mapLayer(polygon_layer_id)
        if not polygon_layer:
            return  # Sem camada de polígonos, não atualiza

        # Usa apenas selecionados se checkbox estiver marcado; senão, todas as feições
        checkSel = self.findChild(QCheckBox, 'checkBoxSeleciona')
        polys = (polygon_layer.selectedFeatures()
                 if checkSel and checkSel.isChecked()
                 else list(polygon_layer.getFeatures()))
        if not polys:
            return  # Sem feições para processar

        spacing = self.doubleSpinBoxEspassamento.value()    # Espaçamento atual
        angle_deg = self.horizontalSlider.value()           # Ângulo atual

        # Define transformação para CRS projetado se necessário
        src_crs = polygon_layer.crs()
        if src_crs.isGeographic():
            first = polys[0].geometry()
            lon = first.centroid().asPoint().x()
            lat = first.centroid().asPoint().y()
            zona = int((lon + 180) / 6) + 1
            epsg = 32600 + zona if lat >= 0 else 32700 + zona
            proj = QgsCoordinateReferenceSystem(epsg)
            to_p = QgsCoordinateTransform(src_crs, proj, QgsProject.instance())
            to_s = QgsCoordinateTransform(proj, src_crs, QgsProject.instance())
        else:
            to_p = to_s = None

        # Gera as linhas atualizadas
        feats = self._gerar_linhas(polys, spacing, angle_deg, to_p, to_s)

        pr = layer.dataProvider()
        pr.truncate()             # Limpa feições antigas
        pr.addFeatures(feats)     # Adiciona novas feições
        layer.updateExtents()     # Atualiza extensão da camada
        layer.triggerRepaint()    # Atualiza visualização no QGIS

    def selecionar_cor(self):
        """
        Abre um diálogo para escolher a cor da linha.
        
        Funcionalidades:
        - Solicita ao usuário a escolha de uma cor via QColorDialog.
        - Atualiza a aparência do pushButtonCor para refletir a cor escolhida.
        - Armazena a cor escolhida em self.linha_cor.
        - Se já existir uma camada de linhas, aplica a nova cor imediatamente ao símbolo da camada e atualiza a visualização no mapa.
        - Não altera nada se o usuário cancelar o diálogo de cor.
        """
        color = QColorDialog.getColor(initial=self.linha_cor or QColor())  # Abre o diálogo de cor
        if not color.isValid():
            return  # Sai se o usuário cancelar a seleção

        self.linha_cor = color  # Salva a cor selecionada

        # Atualiza a aparência do botão para mostrar a cor escolhida
        self.pushButtonCor.setStyleSheet(f"QPushButton {{ background-color: {color.name()}; }}")

        # Se a camada de linhas já existe, aplica a nova cor imediatamente
        layer = self._get_layer_linhas()
        if layer:
            sym = layer.renderer().symbol().clone()  # Clona o símbolo atual
            sym.setColor(color)                      # Atualiza a cor do símbolo
            layer.renderer().setSymbol(sym)          # Aplica o novo símbolo
            layer.triggerRepaint()                   # Atualiza a visualização no QGIS

    def update_pushButtonExecutar(self):
        """
        Habilita o pushButtonExecutar somente se:
          - O comboBoxCamada tiver pelo menos uma camada;
          - O valor do doubleSpinBoxEspassamento for diferente de 0.
        Caso contrário, o botão é desabilitado.
        """
        tem_camadas = self.comboBoxCamada.count() > 0
        espassamento_valido = self.doubleSpinBoxEspassamento.value() != 0
        self.pushButtonExecutar.setEnabled(tem_camadas and espassamento_valido)

    def closeEvent(self, event):
        """Desconecta atualização automática ao fechar o diálogo."""
        self._desconectar_atualizacao_automatica()
        super().closeEvent(event)

    def _desconectar_atualizacao_automatica(self):
        """Desconecta os sinais de atualização automática se estavam conectados."""
        if getattr(self, "_rt_connected", False):
            try:
                self.horizontalSlider.valueChanged.disconnect(self.atualizar_linhas_rt)
            except Exception:
                pass  # nosec B110
            try:
                self.lineEditAngulo.editingFinished.disconnect(self.atualizar_linhas_rt)
            except Exception:
                pass  # nosec B110
            try:
                self.doubleSpinBoxEspassamento.valueChanged.disconnect(self.atualizar_linhas_rt)
            except Exception:
                pass  # nosec B110
            self._rt_connected = False