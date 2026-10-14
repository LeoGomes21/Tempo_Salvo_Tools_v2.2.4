from qgis.core import QgsProject, QgsMessageLog, Qgis, QgsVectorLayer, QgsWkbTypes, QgsPointXY, QgsFeature, QgsFields, QgsField, QgsGeometry, QgsCoordinateTransform, QgsCoordinateReferenceSystem
from qgis.PyQt.QtWidgets import QDialog, QCheckBox, QRadioButton, QApplication, QProgressBar
from qgis.PyQt.QtCore import Qt, QMetaType, QCoreApplication
from qgis.utils import iface
from qgis.PyQt import uic
import time
import math
import os

FORM_CLASS, _ = uic.loadUiType(os.path.join(
    os.path.dirname(__file__), 'OpLinhas.ui'))

class LinhasManager(QDialog, FORM_CLASS):
    def __init__(self, parent=None):
        """Constructor."""
        super(LinhasManager, self).__init__(parent)
        # Configura a interface do usuário a partir do Designer.
        self.setupUi(self)

        self.iface = iface # Armazena a referência da interface QGIS

        # Altera o título da janela
        self.setWindowTitle(self.tr("Operações Sobre Linhas"))

        self._connected_layer = None

        self._default_espacamento = self.doubleSpinBoxEspacamento.value()
        self._default_segmentos = self.doubleSpinBoxSegmentos.value()
        self._default_espacamento2 = self.doubleSpinBoxEspacamento2.value()

        # Conecta os sinais aos slots
        self.connect_signals()

    def tr(self, message):
        """
        Traduz textos deste diálogo.
        O contexto precisa ser estável para o Qt Linguist encontrar as traduções.
        """
        return QCoreApplication.translate("LinhasManager", message)

    def connect_signals(self):

       # Conecta a mudança de seleção no comboBoxCamada para atualizar o checkBoxSeleciona
        self.comboBoxCamada.currentIndexChanged.connect(self.update_checkBoxSeleciona)
        self.comboBoxCamada.currentIndexChanged.connect(self.update_layer_connections)

        # Conecta sinais do projeto para atualizar comboBox quando camadas forem adicionadas, removidas ou renomeadas
        QgsProject.instance().layersAdded.connect(self.populate_combo_box)
        QgsProject.instance().layersRemoved.connect(self.populate_combo_box)
        QgsProject.instance().layerWillBeRemoved.connect(self.populate_combo_box)

        # Conecta o botão de executar à função on_executar
        self.pushButtonExecutar.clicked.connect(self.on_executar)

        # Conecta o sinal toggled do checkBoxLinhas
        self.checkBoxLinhas.toggled.connect(self.update_lin_controls)

        # Conecte o sinal toggled do checkBoxSegmentar
        self.checkBoxSegmentar.toggled.connect(self.update_seg_controls)

        # Conecte o sinal toggled do checkBoxPoliLinhas
        self.checkBoxPoliLinhas.toggled.connect(self.update_poly_controls)

        # Conecte o sinal toggled do pushButtonExecutar
        self.checkBoxLinhas.toggled.connect(self.update_execute_button)
        self.checkBoxSegmentar.toggled.connect(self.update_execute_button)
        self.checkBoxPoliLinhas.toggled.connect(self.update_execute_button)
        
        # Fecha o Diálogo
        self.pushButtonFechar.clicked.connect(self.close)

        self.comboBoxCamada.currentIndexChanged.connect(self.update_execute_button)

        # Conecta o sinal toggled do checkBoxExplodir
        self.checkBoxExplodir.toggled.connect(self.update_execute_button)

    def showEvent(self, event):
        """
        Sobrescreve o evento de exibição do diálogo para resetar os Widgets.
        """
        super(LinhasManager, self).showEvent(event)

        self.populate_combo_box()  # Atualiza o comboBoxCamada com as camadas disponíveis

        self.update_checkBoxSeleciona()  # Atualiza o estado do checkBoxSeleciona com base nas feições selecionadas

        self.update_layer_connections()  # Conecta os sinais da camada atual

        self.update_lin_controls() # Atualiza o estado ao iniciar do checkBoxLinhas

        self.update_seg_controls() # Atualiza o estado ao iniciar do checkBoxSegmentar
        
        self.update_poly_controls() # Atualiza o estado ao iniciar do checkBoxPoliLinhas

        self.update_execute_button() # Atualiza o estado ao iniciar do pushButtonExecutar

        self.reset_controls()                # Reseta os controles para o estado padrão

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
        progressMessageBar = self.iface.messageBar().createMessage(self.tr("Gerando Camada(as) solicitada(as)..."))
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
        bar = self.iface.messageBar()
        t = (tipo or "").strip().lower()

        if t in ("erro", "error", "critical"):
            bar.pushMessage(self.tr("Erro"), texto, level=Qgis.MessageLevel.Critical, duration=duracao)

        elif t in ("aviso", "warning", "warn"):
            bar.pushMessage(self.tr("Aviso"), texto, level=Qgis.MessageLevel.Warning, duration=duracao)

        elif t in ("sucesso", "success", "ok"):
            bar.pushMessage(self.tr("Sucesso"), texto, level=Qgis.MessageLevel.Info, duration=duracao)

        else:
            bar.pushMessage(self.tr("Info"), texto, level=Qgis.MessageLevel.Info, duration=duracao)

    def update_checkBoxSeleciona(self):
        layer_id = self.comboBoxCamada.currentData()
        cb = self.findChild(QCheckBox, 'checkBoxSeleciona')

        if not cb:
            return

        if layer_id:
            layer = QgsProject.instance().mapLayer(layer_id)
            if layer:
                selected_features = layer.selectedFeatureCount()
                if selected_features > 0:
                    cb.setEnabled(True)
                else:
                    cb.setEnabled(False)
                    cb.setChecked(False)
                return

        cb.setEnabled(False)
        cb.setChecked(False)

    def update_layer_connections(self, *args):
        # desconecta a camada anterior
        if self._connected_layer is not None:
            try:
                self._connected_layer.selectionChanged.disconnect(self.update_checkBoxSeleciona)
            except Exception:
                pass  # nosec B110
            self._connected_layer = None

        layer_id = self.comboBoxCamada.currentData()
        if layer_id:
            layer = QgsProject.instance().mapLayer(layer_id)
            if layer:
                try:
                    layer.selectionChanged.connect(self.update_checkBoxSeleciona, Qt.ConnectionType.UniqueConnection)
                except Exception:
                    try:
                        layer.selectionChanged.connect(self.update_checkBoxSeleciona)
                    except Exception:
                        pass  # nosec B110
                self._connected_layer = layer

        self.update_checkBoxSeleciona()

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
        - Preenche o comboBoxRotulagem com os campos da camada selecionada.
        - Ativa ou desativa o botão pushButtonConverter com base na presença de camadas no comboBoxCamada.
        """
        current_layer_id = self.comboBoxCamada.currentData()
        self.comboBoxCamada.blockSignals(True)
        self.comboBoxCamada.clear()

        for layer in QgsProject.instance().mapLayers().values():
            if isinstance(layer, QgsVectorLayer) and QgsWkbTypes.geometryType(layer.wkbType()) == QgsWkbTypes.GeometryType.LineGeometry:
                self.comboBoxCamada.addItem(layer.name(), layer.id())
                try:
                    layer.nameChanged.disconnect(self.update_combo_box_item)
                except (TypeError, RuntimeError):
                    pass  # nosec B110

                layer.nameChanged.connect(self.update_combo_box_item)

        if current_layer_id:
            index = self.comboBoxCamada.findData(current_layer_id)
            if index != -1:
                self.comboBoxCamada.setCurrentIndex(index)

        self.comboBoxCamada.blockSignals(False)
        self.update_execute_button()

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

    def on_executar(self, *args):
        """
        Método principal chamado ao clicar no botão "Executar".
        Verifica quais checkboxes/radiobuttons estão selecionados,
        checa se a camada está em CRS geográfico e, se necessário,
        prepara a reprojeção para UTM. Em seguida, chama as funções
        correspondentes.
        """
        # Obtém a camada selecionada do comboBox
        layer_id = self.comboBoxCamada.currentData()
        if not layer_id:
            self.mostrar_mensagem(self.tr("Nenhuma camada selecionada."), "Erro")
            return

        line_layer = QgsProject.instance().mapLayer(layer_id)
        if not line_layer:
            self.mostrar_mensagem(self.tr("Camada inválida."), "Erro")
            return

        # Verifica se a camada está em coordenadas geográficas (latitude/longitude)
        source_crs = line_layer.crs()
        needs_reprojection = source_crs.isGeographic()
        self.transform = None
        self.inverse_transform = None

        if needs_reprojection:
            # Obtém a extensão da camada
            extent = line_layer.extent()
            # Se a extensão não for válida, utiliza a extensão da primeira feição
            if extent.isEmpty() or math.isnan(extent.xMinimum()):
                # Como neste ponto ainda não processamos as feições, obtemos a lista completa
                features = list(line_layer.getFeatures())
                if features:
                    first_feat = features[0]
                    extent = first_feat.geometry().boundingBox()
                else:
                    self.mostrar_mensagem(self.tr("Camada sem feições válidas."), "Erro")
                    return

            center = extent.center()
            # Calcula a zona UTM usando o centro da extensão
            zone = max(1, min(60, int((center.x() + 180) / 6) + 1))
            # Define o EPSG conforme o hemisfério
            if center.y() >= 0:
                utm_epsg = 32600 + zone
            else:
                utm_epsg = 32700 + zone

            target_crs = QgsCoordinateReferenceSystem.fromEpsgId(utm_epsg)
            self.transform = QgsCoordinateTransform(source_crs, target_crs, QgsProject.instance())
            self.inverse_transform = QgsCoordinateTransform(target_crs, source_crs, QgsProject.instance())
            self.mostrar_mensagem(self.tr("Reprojeção para UTM (EPSG:{utm_epsg}) aplicada.").format(utm_epsg=utm_epsg), "Info", duracao=3)

        # Chama as funções de operação conforme os checkboxes selecionados
        if self.checkBoxLinhas.isChecked():
            self.generate_points_along_lines()  # A função deve verificar self.transform se não for None

        if self.checkBoxSegmentar.isChecked():
            self.segment_lines()  # Idem, se a reprojeção for necessária

        if self.checkBoxPoliLinhas.isChecked():
            self.generate_polygons_along_lines()  # Também considerar a reprojeção se necessário

        if self.checkBoxExplodir.isChecked():
            self.explodir_em_segmentos()

    def generate_points_along_lines(self):
        """
        Gera pontos ao longo de uma camada de linhas, considerando:
          - Espaçamento definido por doubleSpinBoxEspacamento;
          - Uso de feições selecionadas, se indicado;
          - Inclusão dos vértices, de modo que, na interpolação por segmento,
            cada vértice (exceto o último) tem um ponto associado, e o último
            vértice só receberá ponto se checkBoxPFinal estiver selecionado;
          - Se checkBoxIgnoraV estiver marcado, gera somente pontos interpolados.
        
        A camada de saída incluirá os campos:
          - ID: identificador sequencial
          - X: coordenada X do ponto
          - Y: coordenada Y do ponto

        Durante o processo, é exibida uma barra de progresso e, ao final, é exibida
        uma mensagem informando que a camada foi criada com sucesso, indicando também a
        duração total do processamento.
        
        Se a camada foi reprojetada (através de self.transform e self.inverse_transform), o processamento
        ocorre no CRS métrico e os resultados são revertidos para o CRS original.
        """
        start_time = time.time()  # Inicia a contagem do tempo

        # Obtém a camada selecionada
        layer_id = self.comboBoxCamada.currentData()
        if not layer_id:
            self.mostrar_mensagem(self.tr("Nenhuma camada selecionada."), "Erro")
            return

        line_layer = QgsProject.instance().mapLayer(layer_id)
        if not line_layer:
            self.mostrar_mensagem(self.tr("Camada inválida."), "Erro")
            return

        # Obtém o valor do espaçamento
        spacing = self.doubleSpinBoxEspacamento.value()
        if spacing <= 0:
            self.mostrar_mensagem(self.tr("O espaçamento deve ser maior que zero."), "Erro")
            return

        # Determina se usa feições selecionadas ou todas
        if self.findChild(QCheckBox, 'checkBoxSeleciona').isChecked():
            features = list(line_layer.selectedFeatures())
            if not features:
                self.mostrar_mensagem(self.tr("Nenhuma feição selecionada na camada."), "Erro")
                return
        else:
            features = list(line_layer.getFeatures())

        # Flags de opções
        ignora_vertices = self.findChild(QCheckBox, 'checkBoxIgnoraV').isChecked()
        adiciona_final = self.findChild(QCheckBox, 'checkBoxPFinal').isChecked()

        # Cria camada em memória para pontos
        crs = line_layer.crs().authid()

        # Nome base: <NomeDaCamada>_Pontos
        base_name = self.tr("{layer_name}_Pontos").format(layer_name=line_layer.name())

        # Se já existir, vira <NomeDaCamada>_Pontos_1, depois _2, _3...
        existing_names = {lyr.name() for lyr in QgsProject.instance().mapLayers().values()}
        out_name = base_name
        i = 1
        while out_name in existing_names:
            out_name = f"{base_name}_{i}"
            i += 1
        
        point_layer = QgsVectorLayer(f"Point?crs={crs}", out_name, "memory")

        pr = point_layer.dataProvider()

        # Define os campos: ID (inteiro), X e Y (double)
        fields = QgsFields()
        fields.append(QgsField("ID", QMetaType.Type.Int))
        fields.append(QgsField("X", QMetaType.Type.Double, len=10, prec=3))
        fields.append(QgsField("Y", QMetaType.Type.Double, len=10, prec=3))
        pr.addAttributes(fields)
        point_layer.updateFields()

        new_features = []

        # Função auxiliar para obter os pontos de uma linha.
        # Se (ignora_vertices ou adiciona_final) é verdadeiro, utiliza interpolação contínua;
        # caso contrário, realiza interpolação por segmento, reiniciando o espaçamento a cada vértice,
        # e adiciona o vértice final do segmento somente se não for o último vértice da linha.
        def get_points_for_line(line):
            """
            Retorna uma lista de QgsGeometry (pontos) para a linha dada, obedecendo:
            - ignora_vertices=True: só pontos interpolados contínuos (sem vértices). Se adiciona_final=True, inclui o ponto final da linha.
            - ignora_vertices=False: interpolação por segmento, incluindo vértices; o último vértice só entra se adiciona_final=True.
            """
            if ignora_vertices:
                # MODO CONTÍNUO: sem vértices
                pts = []
                line_geom = QgsGeometry.fromPolylineXY(line)
                length = line_geom.length()

                d = spacing
                while d < length:
                    pts.append(line_geom.interpolate(d))
                    d += spacing

                if adiciona_final:
                    end_pt = line_geom.interpolate(length)
                    pts.append(end_pt)
                return pts

            else:
                # MODO POR SEGMENTO: com vértices
                pts = []
                if len(line) < 2:
                    return pts

                # adiciona o primeiro vértice
                pts.append(QgsGeometry.fromPointXY(line[0]))

                for i in range(len(line) - 1):
                    p0 = line[i]
                    p1 = line[i + 1]

                    seg_geom = QgsGeometry.fromPolylineXY([p0, p1])
                    seg_length = seg_geom.length()
                    if seg_length <= 0:
                        # se o segmento é degenerado, pule
                        if i < len(line) - 2:
                            # ainda assim, adicione o vértice intermediário (caso não seja o último)
                            pts.append(QgsGeometry.fromPointXY(line[i + 1]))
                        continue

                    # pontos interpolados dentro do segmento (reinicia em cada segmento)
                    d = spacing
                    while d < seg_length:
                        ratio = d / seg_length
                        new_x = p0.x() + ratio * (p1.x() - p0.x())
                        new_y = p0.y() + ratio * (p1.y() - p0.y())
                        pts.append(QgsGeometry.fromPointXY(QgsPointXY(new_x, new_y)))
                        d += spacing

                    # adiciona o vértice final do segmento somente se NÃO for o último vértice da linha
                    if i < len(line) - 2:
                        pts.append(QgsGeometry.fromPointXY(line[i + 1]))

                # opcionalmente adiciona o último vértice da linha
                if adiciona_final:
                    pts.append(QgsGeometry.fromPointXY(line[-1]))

                return pts

        # Primeiro laço: contar o total de pontos (para configurar a barra de progresso)
        total_points = 0
        for feat in features:
            geom = feat.geometry()
            if geom.isEmpty():
                continue
            # Se necessário, transforma a geometria para o CRS métrico
            geom_proc = QgsGeometry(geom)
            if self.transform is not None:
                geom_proc.transform(self.transform)
            if geom_proc.isMultipart():
                parts = geom_proc.asMultiPolyline()
            else:
                parts = [geom_proc.asPolyline()]
            for line in parts:
                if len(line) < 2:
                    continue
                pts = get_points_for_line(line)
                total_points += len(pts)

        # Inicia a barra de progresso (usa a função iniciar_progress_bar)
        progressBar, progressMessageBar = self.iniciar_progress_bar(total_points)
        current_step = 0
        point_id = 1  # contador para o campo ID

        # Segundo laço: gera os pontos e atualiza a barra de progresso
        for feat in features:
            geom = feat.geometry()
            if geom.isEmpty():
                continue
            geom_proc = QgsGeometry(geom)
            if self.transform is not None:
                geom_proc.transform(self.transform)
            if geom_proc.isMultipart():
                parts = geom_proc.asMultiPolyline()
            else:
                parts = [geom_proc.asPolyline()]
            for line in parts:
                if len(line) < 2:
                    continue
                pts = get_points_for_line(line)
                for pt in pts:
                    # Se a geometria foi processada em UTM, transforma o ponto de volta para o CRS original
                    pt_final = QgsGeometry(pt)  # cópia da geometria do ponto
                    if self.inverse_transform is not None:
                        pt_final.transform(self.inverse_transform)
                    new_feat = QgsFeature()
                    new_feat.setGeometry(pt_final)
                    pt_point = pt_final.asPoint()
                    new_feat.setAttributes([point_id, round(pt_point.x(), 3), round(pt_point.y(), 3)])
                    point_id += 1
                    new_features.append(new_feat)
                    current_step += 1
                    progressBar.setValue(current_step)
                    QApplication.processEvents()  # Atualiza a interface

        # Adiciona as novas feições à camada e insere no projeto
        pr.addFeatures(new_features)
        point_layer.updateExtents()
        QgsProject.instance().addMapLayer(point_layer)

        # Fecha a barra de progresso (remove os widgets)
        try:
            self.iface.messageBar().popWidget(progressMessageBar)
        except (TypeError, RuntimeError):
            pass  # nosec B110

        # Calcula a duração e exibe uma mensagem final com o tempo de execução
        duration = time.time() - start_time
        final_message = self.tr("Camada de pontos gerada com sucesso. Duração: {duration:.2f} segundos.").format(duration=duration)
        self.mostrar_mensagem(final_message, "Sucesso", duracao=2)

    def segment_lines(self):
        """
        Segmenta as linhas da camada selecionada conforme o modo escolhido:
          - Modo "Partes": divide cada feição em um número fixo de partes (valor de spinBoxPartes);
          - Modo "Comprimento": divide cada trecho entre vértices em segmentos de comprimento fixo
             (valor de doubleSpinBoxSegmentos), mas, se o trecho final entre dois vértices for menor,
             utiliza esse comprimento restante antes de reiniciar a contagem a partir do vértice.
        
        Durante o processamento, é exibida uma barra de progresso e, ao final, uma mensagem com a
        duração do processamento é mostrada.
        
        Se a camada estiver em CRS geográfico, o processamento será realizado reprojetando para um CRS
        métrico (UTM) e, ao final, os segmentos serão convertidos de volta para o CRS original.

        Cada feição criada recebe um ID sequencial.
        """
        start_time = time.time()
        
        # Obtém a camada de linhas
        layer_id = self.comboBoxCamada.currentData()
        if not layer_id:
            self.mostrar_mensagem(self.tr("Nenhuma camada selecionada para segmentar."), "Erro")
            return

        line_layer = QgsProject.instance().mapLayer(layer_id)
        if not line_layer:
            self.mostrar_mensagem(self.tr("Camada inválida."), "Erro")
            return

        # Usa feições selecionadas se o checkBoxSeleciona estiver marcado; senão, todas
        if self.findChild(QCheckBox, 'checkBoxSeleciona').isChecked():
            features = list(line_layer.selectedFeatures())
            if not features:
                self.mostrar_mensagem(self.tr("Nenhuma feição selecionada na camada para segmentar."), "Erro")
                return
        else:
            features = list(line_layer.getFeatures())

        # Verifica qual modo de segmentação foi selecionado
        by_parts = self.findChild(QRadioButton, 'radioButtonPartes').isChecked()
        by_length = self.findChild(QRadioButton, 'radioButtonComprimento').isChecked()

        if not by_parts and not by_length:
            self.mostrar_mensagem(self.tr("Selecione 'Partes' ou 'Comprimento' para segmentar."), "Erro")
            return

        new_features = []

        def _subline_from_points(pts, d0: float, d1: float, eps: float = 1e-9) -> QgsGeometry:
            """
            Extrai um subtrecho da polilinha (lista de vértices) entre as distâncias d0..d1
            ao longo da linha, PRESERVANDO o contorno (vértices intermediários).
            """
            if not pts or len(pts) < 2:
                return QgsGeometry()

            d0 = float(d0)
            d1 = float(d1)
            if d1 <= d0 + eps:
                return QgsGeometry()

            out = []
            dist = 0.0
            started = False

            for i in range(len(pts) - 1):
                a = QgsPointXY(pts[i])
                b = QgsPointXY(pts[i + 1])

                seg = a.distance(b)
                if seg <= eps:
                    continue

                seg_start = dist
                seg_end = dist + seg

                # define ponto inicial (quando entrar no intervalo)
                if not started:
                    if d0 <= seg_start + eps:
                        out.append(QgsPointXY(a))
                        started = True
                    elif d0 < seg_end - eps:
                        t = (d0 - seg_start) / seg
                        out.append(QgsPointXY(a.x() + t * (b.x() - a.x()), a.y() + t * (b.y() - a.y())))
                        started = True
                    elif abs(d0 - seg_end) <= eps:
                        out.append(QgsPointXY(b))
                        started = True

                if started:
                    # fecha quando d1 cair dentro do segmento atual
                    if d1 < seg_end - eps:
                        t = (d1 - seg_start) / seg
                        endpt = QgsPointXY(a.x() + t * (b.x() - a.x()),
                                           a.y() + t * (b.y() - a.y()))
                        if not out or out[-1].distance(endpt) > eps:
                            out.append(endpt)
                        return QgsGeometry.fromPolylineXY(out)

                    # d1 bate exatamente no fim do segmento
                    if abs(d1 - seg_end) <= eps:
                        if out[-1].distance(b) > eps:
                            out.append(QgsPointXY(b))
                        return QgsGeometry.fromPolylineXY(out)

                    # segmento inteiro dentro do intervalo: adiciona o vértice final
                    if out[-1].distance(b) > eps:
                        out.append(QgsPointXY(b))

                dist = seg_end

            # se d1 passar do fim, fecha no último vértice
            if started and out:
                last = QgsPointXY(pts[-1])
                if out[-1].distance(last) > eps:
                    out.append(last)
                return QgsGeometry.fromPolylineXY(out)

            return QgsGeometry()

        def _polyline_length(pts, eps=1e-9) -> float:
            if not pts or len(pts) < 2:
                return 0.0
            tot = 0.0
            for i in range(len(pts) - 1):
                a = QgsPointXY(pts[i])
                b = QgsPointXY(pts[i + 1])
                d = a.distance(b)
                if d > eps:
                    tot += d
            return tot

        # Cria camada em memória para as linhas segmentadas
        crs = line_layer.crs().authid()

        # Nome base: <NomeDaCamada>_Pontos
        base_name = self.tr("{layer_name}_Segmentos").format(layer_name=line_layer.name())

        # Se já existir, vira <NomeDaCamada>_Pontos_1, depois _2, _3...
        existing_names = {lyr.name() for lyr in QgsProject.instance().mapLayers().values()}
        out_name = base_name
        i = 1
        while out_name in existing_names:
            out_name = f"{base_name}_{i}"
            i += 1
        segmented_layer = QgsVectorLayer(f"LineString?crs={crs}", out_name, "memory")
        pr = segmented_layer.dataProvider()

        # Adiciona o campo ID
        pr.addAttributes([QgsField("ID", QMetaType.Type.Int)])
        segmented_layer.updateFields()

        # Verificação da projeção
        source_crs = line_layer.crs()
        needs_reprojection = source_crs.isGeographic()
        transform = None
        inverse_transform = None
        if needs_reprojection:
            extent = line_layer.extent()
            if extent.isEmpty() or math.isnan(extent.xMinimum()):
                features_all = list(line_layer.getFeatures())
                if features_all:
                    first_feat = features_all[0]
                    extent = first_feat.geometry().boundingBox()
                else:
                    self.mostrar_mensagem(self.tr("Camada sem feições válidas."), "Erro")
                    return
            center = extent.center()
            zone = max(1, min(60, int((center.x() + 180) / 6) + 1))
            if center.y() >= 0:
                utm_epsg = 32600 + zone
            else:
                utm_epsg = 32700 + zone
            target_crs = QgsCoordinateReferenceSystem.fromEpsgId(utm_epsg)
            transform = QgsCoordinateTransform(source_crs, target_crs, QgsProject.instance())
            inverse_transform = QgsCoordinateTransform(target_crs, source_crs, QgsProject.instance())
            # Opcional: informar ao usuário que a reprojeção está sendo aplicada
            self.mostrar_mensagem(self.tr("Reprojeção para UTM (EPSG:{utm_epsg}) aplicada.").format(utm_epsg=utm_epsg), "Info", duracao=3)

        # Primeiro: contar o total de segmentos a serem gerados (para a barra de progresso)
        total_segments = 0
        eps = 1e-9

        if by_parts:
            n_parts = self.spinBoxPartes.value()
            for feat in features:
                geom = feat.geometry()
                if geom.isEmpty():
                    continue
                geom_proc = QgsGeometry(geom)
                if transform is not None:
                    geom_proc.transform(transform)

                parts = geom_proc.asMultiPolyline() if geom_proc.isMultipart() else [geom_proc.asPolyline()]
                for line in parts:
                    if len(line) < 2:
                        continue
                    # cada parte gera n_parts segmentos
                    if n_parts > 0:
                        total_segments += n_parts

        else:
            seg_length = self.doubleSpinBoxSegmentos.value()
            if seg_length <= 0:
                self.mostrar_mensagem(self.tr("O comprimento do segmento deve ser maior que zero."), "Erro")
                return

            eps = 1e-9

            for feat in features:
                geom = feat.geometry()
                if geom.isEmpty():
                    continue

                geom_proc = QgsGeometry(geom)
                if transform is not None:
                    geom_proc.transform(transform)

                parts = geom_proc.asMultiPolyline() if geom_proc.isMultipart() else [geom_proc.asPolyline()]
                for line in parts:
                    L = _polyline_length(line, eps=eps)
                    if L <= eps:
                        continue
                    n = int(L // seg_length)
                    if L - n * seg_length > eps:
                        n += 1
                    total_segments += max(1, n)

        # Inicia a barra de progresso
        progressBar, progressMessageBar = self.iniciar_progress_bar(total_segments)
        current_step = 0

        # Contador de ID
        id_counter = 1

        if by_parts:
            n_parts = self.spinBoxPartes.value()

            for feat in features:
                geom = feat.geometry()
                if geom.isEmpty():
                    continue

                geom_proc = QgsGeometry(geom)
                if transform is not None:
                    geom_proc.transform(transform)

                parts = geom_proc.asMultiPolyline() if geom_proc.isMultipart() else [geom_proc.asPolyline()]
                for line in parts:
                    if len(line) < 2:
                        continue

                    line_geom = QgsGeometry.fromPolylineXY(line)
                    total_length = line_geom.length()
                    if total_length <= 0 or n_parts <= 0:
                        continue

                    step = total_length / float(n_parts)
                    start_dist = 0.0

                    for i in range(n_parts):
                        end_dist = total_length if i == n_parts - 1 else (start_dist + step)

                        segment_geom = _subline_from_points(line, start_dist, end_dist)
                        start_dist = end_dist

                        if segment_geom.isEmpty():
                            continue

                        if inverse_transform is not None:
                            segment_geom.transform(inverse_transform)

                        new_feat = QgsFeature(segmented_layer.fields())
                        new_feat.setGeometry(segment_geom)
                        new_feat.setAttribute("ID", id_counter)
                        id_counter += 1
                        new_features.append(new_feat)

                        current_step += 1
                        progressBar.setValue(current_step)
                        QApplication.processEvents()

        else:
            seg_length = self.doubleSpinBoxSegmentos.value()
            eps = 1e-9

            for feat in features:
                geom = feat.geometry()
                if geom.isEmpty():
                    continue

                geom_proc = QgsGeometry(geom)
                if transform is not None:
                    geom_proc.transform(transform)

                parts = geom_proc.asMultiPolyline() if geom_proc.isMultipart() else [geom_proc.asPolyline()]
                for line in parts:
                    if len(line) < 2:
                        continue

                    L = _polyline_length(line, eps=eps)
                    if L <= eps:
                        continue

                    d0 = 0.0 # distância acumulada ao longo da parte
                    while d0 < L - eps:
                        d1 = min(d0 + seg_length, L)  # ✅ sobra só no final
                        segment_geom = _subline_from_points(line, d0, d1)  # preserva contorno

                        d0 = d1  # avança contínuo (não reinicia no vértice)

                        if segment_geom.isEmpty():
                            continue

                        if inverse_transform is not None:
                            segment_geom.transform(inverse_transform)

                        new_feat = QgsFeature(segmented_layer.fields())
                        new_feat.setGeometry(segment_geom)
                        new_feat.setAttribute("ID", id_counter)
                        id_counter += 1
                        new_features.append(new_feat)

                        current_step += 1
                        progressBar.setValue(current_step)
                        QApplication.processEvents()

        # Salva camada
        pr.addFeatures(new_features)
        segmented_layer.updateExtents()
        QgsProject.instance().addMapLayer(segmented_layer)

        # Fecha a barra de progresso
        try:
            self.iface.messageBar().popWidget(progressMessageBar)
        except (TypeError, RuntimeError):
            pass  # nosec B110

        duration = time.time() - start_time
        final_message = self.tr("Linhas segmentadas com sucesso. Duração: {duration:.2f} segundos.").format(duration=duration)
        self.mostrar_mensagem(final_message, "Sucesso", duracao=2)

    def generate_polygons_along_lines(self):
        """
        Cria polígonos (quadrados, círculos ou hexágonos) ao longo das linhas,
        com espaçamento definido por doubleSpinBoxEspacamento2 e tamanho definido
        por doubleSpinBoxTamanho. Garante também que cada vértice da linha receba um polígono.
        O processamento é feito em unidades métricas se a camada estiver em CRS geográfico,
        utilizando a reprojeção para UTM e, ao final, os polígonos são convertidos de volta para o CRS original.

        Além disso, cria um campo 'ID' para cada polígono gerado.
        """
        # 1) Verifica camada de linha selecionada
        layer_id = self.comboBoxCamada.currentData()
        if not layer_id:
            self.mostrar_mensagem(self.tr("Nenhuma camada de linha selecionada."), "Erro")
            return

        line_layer = QgsProject.instance().mapLayer(layer_id)
        if not line_layer:
            self.mostrar_mensagem(self.tr("Camada inválida."), "Erro")
            return

        # 2) Lê parâmetros da GUI
        spacing = self.doubleSpinBoxEspacamento2.value()
        if spacing <= 0:
            self.mostrar_mensagem(self.tr("O espaçamento deve ser maior que zero."), "Erro")
            return

        poly_size = self.doubleSpinBoxTamanho.value()
        if poly_size <= 0:
            self.mostrar_mensagem(self.tr("O tamanho do polígono deve ser maior que zero."), "Erro")
            return

        # Verifica qual radiobutton está selecionado
        if self.radioButtonQuadrados.isChecked():
            shape_type = "Quadrado"
        elif self.radioButtonCirculos.isChecked():
            shape_type = "Circulo"
        elif self.radioButtonHexagonos.isChecked():
            shape_type = "Hexagono"
        else:
            self.mostrar_mensagem(self.tr("Selecione Quadrado, Círculo ou Hexágono."), "Erro")
            return

        # 3) Se checkBoxSeleciona estiver marcado, pega feições selecionadas
        if self.checkBoxSeleciona.isChecked():
            features = list(line_layer.selectedFeatures())
            if not features:
                self.mostrar_mensagem(self.tr("Não há feições selecionadas na camada."), "Erro")
                return
        else:
            features = list(line_layer.getFeatures())

        # 3.1) Verifica se a camada está em CRS geográfico e prepara a reprojeção
        source_crs = line_layer.crs()
        needs_reprojection = source_crs.isGeographic()
        transform = None
        inverse_transform = None
        if needs_reprojection:
            extent = line_layer.extent()
            if extent.isEmpty() or math.isnan(extent.xMinimum()):
                if features:
                    extent = features[0].geometry().boundingBox()
                else:
                    self.mostrar_mensagem(self.tr("Camada sem feições válidas."), "Erro")
                    return
            center = extent.center()
            zone = max(1, min(60, int((center.x() + 180) / 6) + 1))
            if center.y() >= 0:
                utm_epsg = 32600 + zone
            else:
                utm_epsg = 32700 + zone
            target_crs = QgsCoordinateReferenceSystem.fromEpsgId(utm_epsg)
            transform = QgsCoordinateTransform(source_crs, target_crs, QgsProject.instance())
            inverse_transform = QgsCoordinateTransform(target_crs, source_crs, QgsProject.instance())

            self.mostrar_mensagem(self.tr("Reprojeção para UTM (EPSG:{utm_epsg}) aplicada.").format(utm_epsg=utm_epsg), "Info", duracao=3)

        # 4) Cria camada em memória para receber os polígonos
        crs = line_layer.crs().authid()

        # Nome base: <NomeDaCamada>_Pontos
        base_name = self.tr("{layer_name}_PoligonosLinhas").format(layer_name=line_layer.name())

        # Se já existir, vira <NomeDaCamada>_Pontos_1, depois _2, _3...
        existing_names = {lyr.name() for lyr in QgsProject.instance().mapLayers().values()}
        out_name = base_name
        i = 1
        while out_name in existing_names:
            out_name = f"{base_name}_{i}"
            i += 1

        polygon_layer = QgsVectorLayer(f"Polygon?crs={crs}", out_name, "memory")
        pr = polygon_layer.dataProvider()

        # Adiciona o campo ID ao provedor de dados
        pr.addAttributes([QgsField("ID", QMetaType.Type.Int)])
        polygon_layer.updateFields()

        new_features = []
        id_counter = 1  # Contador para o atributo ID

        # 5) Função auxiliar para construir cada polígono
        def create_polygon_geometry(center: QgsPointXY, shape: str, size: float) -> QgsGeometry:
            """
            Retorna uma QgsGeometry do tipo Polígono em torno de 'center',
            baseado no 'shape' (Quadrado, Circulo ou Hexagono) e no 'size'.
            Obs: os polígonos são criados alinhados aos eixos X/Y.
            """
            if shape == "Quadrado":
                half = size / 2.0
                ring = [
                    QgsPointXY(center.x() - half, center.y() - half),
                    QgsPointXY(center.x() + half, center.y() - half),
                    QgsPointXY(center.x() + half, center.y() + half),
                    QgsPointXY(center.x() - half, center.y() + half),
                    QgsPointXY(center.x() - half, center.y() - half)]  # fecha polígono

                return QgsGeometry.fromPolygonXY([ring])

            elif shape == "Circulo":
                pt = QgsGeometry.fromPointXY(center)
                radius = size / 2.0
                return pt.buffer(radius, 36)  # 36 segmentos para uma boa aproximação

            elif shape == "Hexagono":
                ring = []
                for i in range(6):
                    angle_rad = math.radians(60 * i)
                    x = center.x() + size * math.cos(angle_rad)
                    y = center.y() + size * math.sin(angle_rad)
                    ring.append(QgsPointXY(x, y))
                ring.append(ring[0])  # fecha o hexágono
                return QgsGeometry.fromPolygonXY([ring])
            else:
                return None

        # 6) Percorre cada feição (cada linha) e gera polígonos ao longo dela
        for feat in features:
            geom = feat.geometry()
            if geom.isEmpty():
                continue

            # Se necessário, transforma a geometria para o CRS métrico
            geom_proc = QgsGeometry(geom)
            if transform is not None:
                geom_proc.transform(transform)

            # Trata geometria multipart ou single
            if geom_proc.isMultipart():
                parts = geom_proc.asMultiPolyline()
            else:
                parts = [geom_proc.asPolyline()]

            for line in parts:
                if len(line) < 2:
                    continue

                line_geom = QgsGeometry.fromPolylineXY(line)
                length = line_geom.length()

                # Lista para armazenar os pontos onde já foi criado um polígono
                polygon_centers = []

                # Gera polígonos ao longo da linha com base no espaçamento
                d = 0.0
                while d <= length:
                    center_pt = line_geom.interpolate(d).asPoint()
                    polygon_centers.append(center_pt)
                    poly_geom = create_polygon_geometry(QgsPointXY(center_pt), shape_type, poly_size)
                    # Se houve reprojeção, retorna o polígono para o CRS original
                    if inverse_transform is not None and poly_geom is not None:
                        poly_geom.transform(inverse_transform)

                    if poly_geom:
                        f = QgsFeature(polygon_layer.fields())  # Usa o schema de campos da camada
                        f.setGeometry(poly_geom)
                        # Define o ID e incrementa
                        f.setAttribute("ID", id_counter)
                        id_counter += 1
                        new_features.append(f)
                    d += spacing

                # Garante que cada vértice da linha receba um polígono (caso ainda não exista um próximo)
                tol = 1e-6  # tolerância para comparação de coordenadas
                for vertex in line:
                    vertex_point = QgsPointXY(vertex)
                    if not any(vertex_point.distance(p) < tol for p in polygon_centers):
                        polygon_centers.append(vertex_point)
                        poly_geom = create_polygon_geometry(vertex_point, shape_type, poly_size)
                        if inverse_transform is not None and poly_geom is not None:
                            poly_geom.transform(inverse_transform)
                        if poly_geom:
                            f = QgsFeature(polygon_layer.fields())
                            f.setGeometry(poly_geom)
                            f.setAttribute("ID", id_counter)
                            id_counter += 1
                            new_features.append(f)

        # 7) Adiciona as novas feições à camada de polígonos e insere no projeto
        pr.addFeatures(new_features)
        polygon_layer.updateExtents()
        QgsProject.instance().addMapLayer(polygon_layer)

        self.mostrar_mensagem(self.tr("Polígonos gerados com sucesso."), "Sucesso")

    def update_lin_controls(self, *args):
        # Ativa os controles apenas se checkBoxLinhas estiver marcado
        active = self.checkBoxLinhas.isChecked()
        self.doubleSpinBoxEspacamento.setEnabled(active)
        self.checkBoxPFinal.setEnabled(active)
        self.checkBoxIgnoraV.setEnabled(active)

    def update_seg_controls(self, *args):
        # Ativa os controles apenas se checkBoxSegmentar estiver marcado
        active = self.checkBoxSegmentar.isChecked()
        self.radioButtonPartes.setEnabled(active)
        self.spinBoxPartes.setEnabled(active)
        self.radioButtonComprimento.setEnabled(active)
        self.doubleSpinBoxSegmentos.setEnabled(active)
        
        # Se estiver ativo, define o radioButtonComprimento como selecionado imediatamente
        if active:
            self.radioButtonComprimento.setChecked(True)

    def update_poly_controls(self, *args):
        # Ativa os controles se checkBoxPoliLinhas estiver marcado
        active = self.checkBoxPoliLinhas.isChecked()
        self.radioButtonQuadrados.setEnabled(active)
        self.radioButtonCirculos.setEnabled(active)
        self.radioButtonHexagonos.setEnabled(active)
        self.doubleSpinBoxEspacamento2.setEnabled(active)
        self.doubleSpinBoxTamanho.setEnabled(active)
        # Se estiver ativo, marca o radioButtonQuadrados
        if active:
            self.radioButtonQuadrados.setChecked(True)

    def explodir_em_segmentos(self):
        """
        Explode a(s) linha(s) em segmentos entre vértices (estilo CAD):
        cada trecho entre dois vértices consecutivos vira uma feição LineString.
        Preserva atributos.
        """
        start_time = time.time()

        layer_id = self.comboBoxCamada.currentData()
        if not layer_id:
            self.mostrar_mensagem(self.tr("Nenhuma camada selecionada para explodir."), "Erro")
            return

        line_layer = QgsProject.instance().mapLayer(layer_id)
        if not line_layer or not isinstance(line_layer, QgsVectorLayer):
            self.mostrar_mensagem(self.tr("Camada inválida."), "Erro")
            return

        # selecionadas ou todas
        if self.checkBoxSeleciona.isChecked():
            features = list(line_layer.selectedFeatures())
            if not features:
                self.mostrar_mensagem(self.tr("Nenhuma feição selecionada na camada."), "Erro")
                return
        else:
            features = list(line_layer.getFeatures())

        # tipo de saída (preserva Z/M)
        wkb_in = line_layer.wkbType()
        wkb_out = QgsWkbTypes.Type.LineString
        if QgsWkbTypes.hasZ(wkb_in):
            wkb_out = QgsWkbTypes.addZ(wkb_out)
        if QgsWkbTypes.hasM(wkb_in):
            wkb_out = QgsWkbTypes.addM(wkb_out)

        geom_str = QgsWkbTypes.displayString(wkb_out)
        crs = line_layer.crs().authid()

        out_name = self.tr("{layer_name}_Explodida").format(layer_name=line_layer.name())
        out_layer = QgsVectorLayer(f"{geom_str}?crs={crs}", out_name, "memory")
        pr = out_layer.dataProvider()

        # copia campos da camada original
        pr.addAttributes(list(line_layer.fields()))
        # Campo novo: Comprimentos
        pr.addAttributes([QgsField("Comprimentos", QMetaType.Type.Double, "double", 20, 3)])
        out_layer.updateFields()
        idx_len = out_layer.fields().indexOf("Comprimentos")

        # contar segmentos (progress)
        total = 0
        for feat in features:
            g = feat.geometry()
            if not g or g.isEmpty():
                continue

            # asPolyline/asMultiPolyline (para linhas)
            if g.isMultipart():
                parts = g.asMultiPolyline()
            else:
                parts = [g.asPolyline()]

            for line in parts:
                if len(line) >= 2:
                    total += (len(line) - 1)

        if total == 0:
            self.mostrar_mensagem(self.tr("Nada para explodir (linhas sem vértices suficientes)."), "Aviso", duracao=3)
            return

        progressBar, progressMessageBar = self.iniciar_progress_bar(total)
        current = 0

        source_crs = line_layer.crs()
        needs_reprojection = source_crs.isGeographic()
        to_m = None

        if needs_reprojection:
            extent = line_layer.extent()
            if extent.isEmpty() or math.isnan(extent.xMinimum()):
                feats_all = list(line_layer.getFeatures())
                if feats_all:
                    extent = feats_all[0].geometry().boundingBox()
            center = extent.center()
            zone = max(1, min(60, int((center.x() + 180) / 6) + 1))
            utm_epsg = (32600 + zone) if center.y() >= 0 else (32700 + zone)
            target_crs = QgsCoordinateReferenceSystem.fromEpsgId(utm_epsg)
            to_m = QgsCoordinateTransform(source_crs, target_crs, QgsProject.instance())

        new_feats = []
        for feat in features:
            g = feat.geometry()
            if not g or g.isEmpty():
                continue

            if g.isMultipart():
                parts = g.asMultiPolyline()
            else:
                parts = [g.asPolyline()]

            for line in parts:
                if len(line) < 2:
                    continue

                for i in range(len(line) - 1):
                    p0 = QgsPointXY(line[i])
                    p1 = QgsPointXY(line[i + 1])
                    seg_geom = QgsGeometry.fromPolylineXY([p0, p1])

                    # comprimento (em metros se for geográfico; senão em unidades do CRS)
                    if to_m is not None:
                        p0m = to_m.transform(p0)
                        p1m = to_m.transform(p1)
                        comp = p0m.distance(p1m)
                    else:
                        comp = p0.distance(p1)

                    attrs_in = feat.attributes()
                    # monta lista de atributos com o MESMO tamanho da camada de saída
                    # (atributos originais + 1 slot pro campo Comprimentos)
                    attrs_out = list(attrs_in) + [None]
                    nf = QgsFeature(out_layer.fields())
                    nf.setAttributes(attrs_out)          # copia atributos originais certinho
                    nf.setGeometry(seg_geom)
                    nf.setAttribute(idx_len, round(comp, 3))  # preenche Comprimentos
                    new_feats.append(nf)

                    current += 1
                    progressBar.setValue(current)
                    QApplication.processEvents()

        pr.addFeatures(new_feats)
        out_layer.updateExtents()

        QgsProject.instance().addMapLayer(out_layer)

        try:
            self.iface.messageBar().popWidget(progressMessageBar)
        except (TypeError, RuntimeError):
            pass  # nosec B110

        dt = time.time() - start_time
        self.mostrar_mensagem(self.tr("Explodido em segmentos: {out_name} ({feature_count} feições). {duration:.2f}s").format(out_name=out_name, feature_count=len(new_feats), duration=dt), "Sucesso", duracao=2)

    def update_execute_button(self, *args):
        # Se o comboBox estiver vazio, desativa o botão de executar
        if self.comboBoxCamada.count() == 0:
            self.pushButtonExecutar.setEnabled(False)
            return

        # Caso haja camadas, verifica se pelo menos um dos checkboxes está marcado
        enable = (self.checkBoxLinhas.isChecked() or 
                  self.checkBoxSegmentar.isChecked() or 
                  self.checkBoxPoliLinhas.isChecked() or
                  self.checkBoxExplodir.isChecked())
        self.pushButtonExecutar.setEnabled(enable)

    def reset_controls(self):
        # Reseta os controles relacionados às linhas
        self.checkBoxLinhas.setChecked(False)
        # Aqui você pode definir um valor padrão para o doubleSpinBoxEspacamento
        self.checkBoxPFinal.setChecked(False)
        self.checkBoxIgnoraV.setChecked(False)
        self.checkBoxExplodir.setChecked(False)

        # Reseta os controles de segmentação
        self.checkBoxSegmentar.setChecked(False)
        self.radioButtonPartes.setChecked(False)
        self.spinBoxPartes.setValue(self.spinBoxPartes.minimum())
        self.radioButtonComprimento.setChecked(False)

        # Reseta os controles para os polígonos (ou "Pontos de Linhas")
        self.checkBoxPoliLinhas.setChecked(False)  # ou se o nome for checkBoxPoliLinhas, use esse
        # Inicia os radioButtons de polígonos: inicia com o radioButtonQuadrados marcado
        self.radioButtonQuadrados.setChecked(False)
        self.radioButtonCirculos.setChecked(False)
        self.radioButtonHexagonos.setChecked(False)

        self.doubleSpinBoxTamanho.setValue(self.doubleSpinBoxTamanho.minimum())

        self.doubleSpinBoxEspacamento.setValue(self._default_espacamento)
        self.doubleSpinBoxSegmentos.setValue(self._default_segmentos)
        self.doubleSpinBoxEspacamento2.setValue(self._default_espacamento2)

        # Atualiza os estados (ativar/desativar) de cada grupo de controles, conforme suas lógicas
        self.update_lin_controls()
        self.update_seg_controls()
        self.update_poly_controls()

        # Atualiza também o botão de executar, se necessário
        self.update_execute_button()