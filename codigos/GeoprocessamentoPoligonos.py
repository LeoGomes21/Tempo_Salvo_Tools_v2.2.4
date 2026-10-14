from qgis.core import QgsProject, QgsMessageLog, Qgis, QgsVectorLayer, QgsWkbTypes, QgsMapSettings, QgsMapRendererCustomPainterJob, QgsGeometry, QgsFeature, QgsFeatureRequest, QgsField, QgsDefaultValue, QgsDistanceArea, QgsEditorWidgetSetup, QgsRectangle, QgsFieldConstraints
from qgis.PyQt.QtWidgets import QDialog, QCheckBox, QGraphicsScene, QGraphicsPixmapItem, QGraphicsLineItem, QPushButton
from qgis.PyQt.QtGui import QImage, QPainter, QPixmap, QColor, QPen, QDesktopServices
from qgis.PyQt.QtCore import Qt, QSize, QTimer, QVariant, QMetaType, QCoreApplication, QUrl
from qgis.utils import iface
from qgis.PyQt import uic
import math
import os


FORM_CLASS, _ = uic.loadUiType(os.path.join(
    os.path.dirname(__file__), 'GeoprocessarPoligonosReal.ui'))

class GeoPoligonosManager(QDialog, FORM_CLASS):
    def __init__(self, parent=None):
        """Constructor."""
        super(GeoPoligonosManager, self).__init__(parent)
        # Configura a interface do usuário a partir do Designer.
        self.setupUi(self)

        # Altera o título da janela
        self.setWindowTitle(self.tr("Geoprocessamento de Polígonos"))

        self.iface = iface

        self.scenePoligono = QGraphicsScene()
        self.graphicsView.setScene(self.scenePoligono)

        self.sceneSobrep = QGraphicsScene()
        self.graphicsView2.setScene(self.sceneSobrep)

        self._orig_geoms = {}  # Inicialize aqui!

        self._recorte_history = []  # lista de tuplas: (dict de orig_geoms, geometria atual de cada feição)

        # Preenche o comboBox com camadas de linha
        self.populate_combo_boxes()

        # Sempre que uma feição for adicionada, removida ou modificada na camada ativa
        self._camada_signal_connections = []
        self._sobrep_signal_connections = []

        self._camada_layer_conectado = None
        self._sobrep_layer_conectado = None

        self.update_layer_connections()

        self._resultado_signal_connections = {}  # layer_id -> (layer, slot_added, slot_geom)

        self._orig_offsets = {}       # fid -> (dx, dy) acumulado de movimento
        self._last_result_geom = {}   # fid -> QgsGeometry do último resultado (para medir o delta do próximo arrasto)

        # Conecta os sinais aos slots
        self.connect_signals()

    def tr(self, message):
        """
        Traduz textos deste diálogo.
        O contexto precisa ser estável para o Qt Linguist encontrar as traduções.
        """
        return QCoreApplication.translate("GeoPoligonosManager", message)

    def connect_signals(self):

       # Conecta a mudança de seleção no comboBoxCamada para atualizar o checkBoxSeleciona
        self.comboBoxCamada.currentIndexChanged.connect(self.update_checkBoxSeleciona)
        self.comboBoxCamada.currentIndexChanged.connect(self.display_polygon)  # Conexão para atualizar o graphicsView
        self.comboBoxCamadaSobrep.currentIndexChanged.connect(self.display_polygon_sobrep)

        # Conecta também para atualizar os sinais da camada (selectionChanged)
        self.comboBoxCamada.currentIndexChanged.connect(self.update_layer_connections)

        # Conecta o clique do botão pushButtonExecutar para executar
        self.pushButtonExecutar.clicked.connect(self.executar_recorte)

        # Conecta sinais do projeto para atualizar comboBox quando camadas forem adicionadas, removidas ou renomeadas
        QgsProject.instance().layersAdded.connect(self.populate_combo_boxes)
        QgsProject.instance().layersRemoved.connect(self.populate_combo_boxes)
        QgsProject.instance().layerWillBeRemoved.connect(self.populate_combo_boxes)

        # Sinais para atualizar um ao mudar o outro
        self.comboBoxCamada.currentIndexChanged.connect(self.update_comboBoxCamadaSobrep)
        self.comboBoxCamadaSobrep.currentIndexChanged.connect(self.update_comboBoxCamada)

        # Atualiza o checkbox sobreposição ao mudar a camada sobreposição
        self.comboBoxCamadaSobrep.currentIndexChanged.connect(self.update_checkBoxSelecionaSobrepos)

        # Conecta o botão pushButtonFechar
        self.pushButtonFechar.clicked.connect(self.close)

        QgsProject.instance().layerWillBeRemoved.connect(self._on_layer_removida)

        self.comboBoxCamadaSobrep.currentIndexChanged.connect(self.update_layer_connections_sobrep)

        self.comboBoxCamada.currentIndexChanged.connect(self._atualiza_estado_botao_executar)
        self.comboBoxCamadaSobrep.currentIndexChanged.connect(self._atualiza_estado_botao_executar)
        self.radioButtonDiferenca.toggled.connect(self._atualiza_estado_botao_executar)
        self.radioButtonItersecao.toggled.connect(self._atualiza_estado_botao_executar)
        self.radioButtonUniao.toggled.connect(self._atualiza_estado_botao_executar)
        QgsProject.instance().layersAdded.connect(self._atualiza_estado_botao_executar)
        QgsProject.instance().layersRemoved.connect(self._atualiza_estado_botao_executar)

        # Atualiza ao adicionar/remover camada
        QgsProject.instance().layersAdded.connect(lambda layers: self.display_polygon())
        QgsProject.instance().layersRemoved.connect(lambda layer_ids: self.display_polygon())
        QgsProject.instance().layersAdded.connect(lambda layers: self.display_polygon_sobrep())
        QgsProject.instance().layersRemoved.connect(lambda layer_ids: self.display_polygon_sobrep())

    def showEvent(self, event):
        """
        Sobrescreve o evento de exibição do diálogo para resetar os Widgets.
        """
        super(GeoPoligonosManager, self).showEvent(event)

        # Reset do checkBoxSeleciona
        checkBox = self.findChild(QCheckBox, 'checkBoxSeleciona')
        if checkBox:
            checkBox.setChecked(False)
            checkBox.setEnabled(False)

        checkbox = self.findChild(QCheckBox, 'checkBoxSelecionaSobrepos')
        if checkbox:
            checkbox.setChecked(False)
            checkbox.setEnabled(False)

        self.populate_combo_boxes()  # Atualiza o comboBoxCamada com as camadas disponíveis

        # Atualiza o estado do checkBoxSeleciona com base nas feições selecionadas
        self.update_checkBoxSeleciona()
        self.update_checkBoxSelecionaSobrepos()
        self.update_layer_connections_sobrep()

        self.display_polygon() # Ajusta a visualização
        self.display_polygon_sobrep()

        self.update_layer_connections()  # Conecta os sinais da camada atual

        self._atualiza_estado_botao_executar()

    def _log_message(self, message, level=Qgis.MessageLevel.Info):
        QgsMessageLog.logMessage(message, 'RECORTE', level=level)

    def mostrar_mensagem(self, texto, tipo, duracao=3, caminho_pasta=None, caminho_arquivos=None):
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
            Tempo de exibição da mensagem em segundos (padrão: 3).
        caminho_pasta : str, opcional
            Caminho de uma pasta para abrir via botão (apenas para "Sucesso").
        caminho_arquivos : str, opcional
            Caminho de um arquivo para executar via botão (apenas para "Sucesso").
        """
        bar = self.iface.messageBar()  # Obtém a barra de mensagens do QGIS

        if tipo == "Erro":
            # Exibe mensagem de erro (ícone vermelho)
            bar.pushMessage("Erro", texto, level=Qgis.MessageLevel.Critical, duration=duracao)

        elif tipo == "Sucesso":
            # Cria mensagem de sucesso (ícone azul/informativo)
            msg = bar.createMessage("Sucesso", texto)

            # Adiciona botão para abrir pasta, se informado
            if caminho_pasta:
                botao_abrir_pasta = QPushButton(self.tr("Abrir Pasta"))
                botao_abrir_pasta.clicked.connect(
                    lambda _checked=False, caminho=caminho_pasta:
                        QDesktopServices.openUrl(
                            QUrl.fromLocalFile(
                                os.path.abspath(os.fspath(caminho)))))
                msg.layout().insertWidget(1, botao_abrir_pasta)  # Insere botão à esquerda do texto

            # Adiciona botão para executar arquivo, se informado
            if caminho_arquivos:
                botao_executar = QPushButton(self.tr("Executar"))
                botao_executar.clicked.connect(
                    lambda _checked=False, caminho=caminho_arquivos:
                        QDesktopServices.openUrl(
                            QUrl.fromLocalFile(
                                os.path.abspath(os.fspath(caminho)))))
                msg.layout().insertWidget(2, botao_executar)

            # Exibe a mensagem na barra
            bar.pushWidget(msg, level=Qgis.MessageLevel.Info, duration=duracao)

        elif tipo == "Aviso":
            # Exibe mensagem de aviso (ícone amarelo)
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

    def _atualizar_valores_por_layer_id(self, layer_id, fid, geom_override=None):
        """
        Atualiza Area/Perimetro com segurança buscando a layer pelo ID.
        Assim não quebra se a layer tiver sido removida.
        """
        lyr = QgsProject.instance().mapLayer(layer_id)
        if lyr and isinstance(lyr, QgsVectorLayer):
            self.atualizar_valores_poligono(lyr, fid, geom_override=geom_override)

    def _conectar_sinais_resultado(self, layer: QgsVectorLayer):
        """
        Conecta featureAdded/geometryChanged na layer de resultado
        guardando os slots para permitir disconnect correto depois.
        """
        if not layer:
            return

        lid = layer.id()

        # evita duplicar conexão no mesmo layer_id
        if lid in self._resultado_signal_connections:
            old_layer, old_added, old_geom = self._resultado_signal_connections[lid]
            try:
                old_layer.featureAdded.disconnect(old_added)
            except Exception:
                pass  # nosec B110
            try:
                old_layer.geometryChanged.disconnect(old_geom)
            except Exception:
                pass  # nosec B110

        def _on_added(fid, _lid=lid):
            self._atualizar_valores_por_layer_id(_lid, fid)

        def _on_geom_changed(fid, geom, _lid=lid):
            # geom já vem pronto do sinal, dá para usar como override
            self._atualizar_valores_por_layer_id(_lid, fid, geom_override=geom)

        layer.featureAdded.connect(_on_added)
        layer.geometryChanged.connect(_on_geom_changed)

        self._resultado_signal_connections[lid] = (layer, _on_added, _on_geom_changed)

    def _desconectar_sinais_resultado(self):
        """
        Desconecta todos os sinais guardados das camadas de resultado.
        Importante para não deixar callback preso quando o diálogo fecha.
        """
        for lid, (layer, slot_added, slot_geom) in list(getattr(self, "_resultado_signal_connections", {}).items()):
            try:
                layer.featureAdded.disconnect(slot_added)
            except Exception:
                pass  # nosec B110
            try:
                layer.geometryChanged.disconnect(slot_geom)
            except Exception:
                pass  # nosec B110
        self._resultado_signal_connections = {}

    def update_layer_connections(self):
        """
        Conecta os sinais da camada selecionada no comboBoxCamada para garantir que 
        a interface (incluindo o graphicsView e checkBoxSeleciona) seja atualizada 
        sempre que houver mudanças na seleção ou nas feições (adição, remoção, alteração).

        Correção: evita acumular conexões em selectionChanged ao trocar de camada.
        """
        # 1) Desconecta selectionChanged do layer anterior (evita múltiplas conexões)
        old_layer = getattr(self, "_camada_layer_conectado", None)
        if old_layer:
            try:
                old_layer.selectionChanged.disconnect(self.update_checkBoxSeleciona)
            except Exception:
                pass  # nosec B110
            try:
                old_layer.selectionChanged.disconnect(self.display_polygon)
            except Exception:
                pass  # nosec B110

        # 2) Desconecta handlers antigos de featureAdded/featureDeleted/geometryChanged
        for old_signal in getattr(self, "_camada_signal_connections", []):
            try:
                old_signal[0].featureAdded.disconnect(old_signal[1])
                old_signal[0].featureDeleted.disconnect(old_signal[2])
                old_signal[0].geometryChanged.disconnect(old_signal[3])
            except Exception:
                pass  # nosec B110
        self._camada_signal_connections = []
        self._camada_layer_conectado = None

        # 3) Conecta no layer atual
        layer_id = self.comboBoxCamada.currentData()
        if layer_id:
            layer = QgsProject.instance().mapLayer(layer_id)
            if layer and isinstance(layer, QgsVectorLayer):
                # Conecta sinais relevantes para atualizar o graphicsView
                def on_feature_added(fid): 
                    self.display_polygon()

                def on_feature_deleted(fid): 
                    self.display_polygon()

                def on_geometry_changed(fid, geom): 
                    self.display_polygon()

                layer.featureAdded.connect(on_feature_added)
                layer.featureDeleted.connect(on_feature_deleted)
                layer.geometryChanged.connect(on_geometry_changed)

                self._camada_signal_connections.append((layer, on_feature_added, on_feature_deleted, on_geometry_changed))

                # Conecta selectionChanged (agora sem acúmulo)
                layer.selectionChanged.connect(self.update_checkBoxSeleciona)
                layer.selectionChanged.connect(self.display_polygon)

                self._camada_layer_conectado = layer

                # Atualiza estado inicial
                self.update_checkBoxSeleciona()
                self.display_polygon()
                return

        # fallback se não houver layer válido
        self.update_checkBoxSeleciona()

    def _atualiza_estado_botao_executar(self):
        # Checa se um radiobutton está selecionado
        algum_radio = (
            self.radioButtonDiferenca.isChecked() or
            self.radioButtonItersecao.isChecked() or
            self.radioButtonUniao.isChecked())
        # Checa se há camadas nos combos
        camada_id  = self.comboBoxCamada.currentData()
        sobrep_id  = self.comboBoxCamadaSobrep.currentData()
        camada     = QgsProject.instance().mapLayer(camada_id) if camada_id else None
        sobrep     = QgsProject.instance().mapLayer(sobrep_id) if sobrep_id else None
        camadas_ok = camada is not None and sobrep is not None

        # SRC iguais?
        src_iguais = camadas_ok and camada.crs() == sobrep.crs()

        # Mensagem se SRC diferentes
        if camadas_ok and not src_iguais:
            self.mostrar_mensagem(self.tr("As camadas selecionadas possuem sistemas de referência (SRC) diferentes. "
                "Operações podem gerar resultados inesperados."),
                "Aviso", duracao=3)

        # Ativa botão apenas se tudo ok
        self.pushButtonExecutar.setEnabled(algum_radio and camadas_ok and src_iguais)

    def display_polygon(self):
        """
        Atualiza a exibição do(s) polígono(s) no QGraphicsView.
        - Se houver feições selecionadas, aproxima para elas.
        - Caso contrário, aproxima para todas as feições de polígono.
        (Otimizado: bbox sem unaryUnion)
        """
        self.scenePoligono.clear()
        layer_id = self.comboBoxCamada.currentData()
        layer = QgsProject.instance().mapLayer(layer_id)

        if not layer or not isinstance(layer, QgsVectorLayer):
            return

        # pega feições válidas de polígono
        feats = []
        for f in layer.getFeatures():
            g = f.geometry()
            if g and not g.isEmpty() and g.type() == QgsWkbTypes.GeometryType.PolygonGeometry:
                feats.append(f)

        if not feats:
            if self.isVisible():
                self.mostrar_mensagem(self.tr("A camada de polígono não contém feições."), "Erro")
            return

        selected = layer.selectedFeatures()
        alvo = selected if selected else feats

        # bbox por iteração (bem mais leve que unaryUnion)
        bbox = None
        for f in alvo:
            g = f.geometry()
            if not g or g.isEmpty():
                continue
            b = g.boundingBox()
            if bbox is None:
                bbox = QgsRectangle(b)
            else:
                bbox.combineExtentWith(b)

        if bbox is None or bbox.isNull():
            if self.isVisible():
                self.mostrar_mensagem(self.tr("A geometria não contém dados válidos."), "Erro")
            return

        map_settings = QgsMapSettings()
        map_settings.setLayers([layer])
        map_settings.setBackgroundColor(QColor(255, 255, 255))

        width = self.graphicsView.viewport().width()
        height = self.graphicsView.viewport().height()
        map_settings.setOutputSize(QSize(width, height))
        map_settings.setExtent(bbox)

        image = QImage(width, height, QImage.Format.Format_ARGB32)
        image.fill(Qt.GlobalColor.transparent)
        painter = QPainter(image)
        render_job = QgsMapRendererCustomPainterJob(map_settings, painter)
        render_job.start()
        render_job.waitForFinished()
        painter.end()

        pixmap = QPixmap.fromImage(image)
        pixmap_item = QGraphicsPixmapItem(pixmap)
        self.scenePoligono.addItem(pixmap_item)
        self.graphicsView.setSceneRect(pixmap_item.boundingRect())
        self.graphicsView.fitInView(self.scenePoligono.sceneRect(), Qt.AspectRatioMode.KeepAspectRatio)

    def _display_polygon_in_view(self, layer_id, scene, graphics_view):
        """
        Renderiza uma camada poligonal em um QGraphicsView.
        - Se houver feições selecionadas, aproxima para elas.
        - Caso contrário, aproxima para todas as feições válidas.
        """
        scene.clear()

        layer = QgsProject.instance().mapLayer(layer_id)
        if not layer or not isinstance(layer, QgsVectorLayer):
            return

        feats = []
        for f in layer.getFeatures():
            g = f.geometry()
            if g and not g.isEmpty() and g.type() == QgsWkbTypes.GeometryType.PolygonGeometry:
                feats.append(f)

        if not feats:
            return

        selected = layer.selectedFeatures()
        alvo = selected if selected else feats

        bbox = None
        for f in alvo:
            g = f.geometry()
            if not g or g.isEmpty():
                continue
            b = g.boundingBox()
            if bbox is None:
                bbox = QgsRectangle(b)
            else:
                bbox.combineExtentWith(b)

        if bbox is None or bbox.isNull():
            return

        map_settings = QgsMapSettings()
        map_settings.setLayers([layer])
        map_settings.setBackgroundColor(QColor(255, 255, 255))

        width = graphics_view.viewport().width()
        height = graphics_view.viewport().height()
        map_settings.setOutputSize(QSize(width, height))
        map_settings.setExtent(bbox)

        image = QImage(width, height, QImage.Format.Format_ARGB32)
        image.fill(Qt.GlobalColor.transparent)

        painter = QPainter(image)
        render_job = QgsMapRendererCustomPainterJob(map_settings, painter)
        render_job.start()
        render_job.waitForFinished()
        painter.end()

        pixmap = QPixmap.fromImage(image)
        pixmap_item = QGraphicsPixmapItem(pixmap)
        scene.addItem(pixmap_item)

        graphics_view.setSceneRect(pixmap_item.boundingRect())
        graphics_view.fitInView(scene.sceneRect(), Qt.AspectRatioMode.KeepAspectRatio)

    def display_polygon_sobrep(self):
        """
        Atualiza a exibição da camada de sobreposição no graphicsView2.
        """
        layer_id = self.comboBoxCamadaSobrep.currentData()
        self._display_polygon_in_view(layer_id, self.sceneSobrep, self.graphicsView2)

    def update_layer_connections_sobrep(self):
        """
        Conecta os sinais da camada selecionada no comboBoxCamadaSobrep para garantir que
        o graphicsView2 e o checkBoxSelecionaSobrepos sejam atualizados sempre que houver
        mudanças na seleção ou nas feições.
        """
        old_layer = getattr(self, "_sobrep_layer_conectado", None)
        if old_layer:
            try:
                old_layer.selectionChanged.disconnect(self.update_checkBoxSelecionaSobrepos)
            except Exception:
                pass  # nosec B110
            try:
                old_layer.selectionChanged.disconnect(self.display_polygon_sobrep)
            except Exception:
                pass  # nosec B110

        for old_signal in getattr(self, "_sobrep_signal_connections", []):
            try:
                old_signal[0].featureAdded.disconnect(old_signal[1])
                old_signal[0].featureDeleted.disconnect(old_signal[2])
                old_signal[0].geometryChanged.disconnect(old_signal[3])
            except Exception:
                pass  # nosec B110

        self._sobrep_signal_connections = []
        self._sobrep_layer_conectado = None

        layer_id = self.comboBoxCamadaSobrep.currentData()
        if layer_id:
            layer = QgsProject.instance().mapLayer(layer_id)
            if layer and isinstance(layer, QgsVectorLayer):

                def on_feature_added(fid):
                    self.display_polygon_sobrep()

                def on_feature_deleted(fid):
                    self.display_polygon_sobrep()

                def on_geometry_changed(fid, geom):
                    self.display_polygon_sobrep()

                layer.featureAdded.connect(on_feature_added)
                layer.featureDeleted.connect(on_feature_deleted)
                layer.geometryChanged.connect(on_geometry_changed)

                self._sobrep_signal_connections.append(
                    (layer, on_feature_added, on_feature_deleted, on_geometry_changed))

                layer.selectionChanged.connect(self.update_checkBoxSelecionaSobrepos)
                layer.selectionChanged.connect(self.display_polygon_sobrep)

                self._sobrep_layer_conectado = layer

                self.update_checkBoxSelecionaSobrepos()
                self.display_polygon_sobrep()
                return

        self.update_checkBoxSelecionaSobrepos()
        if hasattr(self, "sceneSobrep"):
            self.sceneSobrep.clear()

    def update_comboBoxCamada(self):
        """
        Atualiza comboBoxCamada para não permitir seleção igual à do comboBoxCamadaSobrep.
        (Opcional: caso queira evitar a inversão)
        """
        sobrep_id = self.comboBoxCamadaSobrep.currentData()
        current_id = self.comboBoxCamada.currentData()
        if current_id == sobrep_id:
            # Seleciona outra camada, se possível
            for i in range(self.comboBoxCamada.count()):
                if self.comboBoxCamada.itemData(i) != sobrep_id:
                    self.comboBoxCamada.setCurrentIndex(i)
                    break

    def update_checkBoxSelecionaSobrepos(self):
        """
        Atualiza o estado do checkBoxSelecionaSobrepos com base na seleção de feições
        da camada atualmente selecionada no comboBoxCamadaSobrep.
        """
        layer_id = self.comboBoxCamadaSobrep.currentData()  # ID da camada de sobreposição
        checkbox = self.findChild(QCheckBox, 'checkBoxSelecionaSobrepos')
        if layer_id and checkbox:
            layer = QgsProject.instance().mapLayer(layer_id)
            if layer:
                selected_features = layer.selectedFeatureCount()
                if selected_features > 0:
                    checkbox.setEnabled(True)
                else:
                    checkbox.setEnabled(False)
                    checkbox.setChecked(False)
            else:
                checkbox.setEnabled(False)
                checkbox.setChecked(False)
        else:
            if checkbox:
                checkbox.setEnabled(False)
                checkbox.setChecked(False)

    def populate_combo_boxes(self):
        """
        Atualiza as opções dos comboBoxCamada e comboBoxCamadaSobrep, listando todas as camadas de polígonos disponíveis no projeto e preservando a seleção atual sempre que possível.
        """
        # Desconecta nameChanged antigos
        if hasattr(self, "_layer_name_change_connections"):
            for lyr, slot in self._layer_name_change_connections:
                try:
                    lyr.nameChanged.disconnect(slot)
                except Exception:
                    pass  # nosec B110
        self._layer_name_change_connections = []

        current_layer_id  = self.comboBoxCamada.currentData()
        current_sobrep_id = self.comboBoxCamadaSobrep.currentData()

        layer_list = QgsProject.instance().mapLayers().values()
        polygon_layers = [
            layer for layer in layer_list
            if isinstance(layer, QgsVectorLayer)
            and QgsWkbTypes.geometryType(layer.wkbType()) == QgsWkbTypes.GeometryType.PolygonGeometry]

        # Repovoa comboBoxCamada
        self.comboBoxCamada.blockSignals(True)
        self.comboBoxCamada.clear()
        for layer in polygon_layers:
            self.comboBoxCamada.addItem(layer.name(), layer.id())
        if current_layer_id:
            idx = self.comboBoxCamada.findData(current_layer_id)
            if idx != -1:
                self.comboBoxCamada.setCurrentIndex(idx)
        self.comboBoxCamada.blockSignals(False)

        # Repovoa comboBoxCamadaSobrep
        self.update_comboBoxCamadaSobrep()   # já cuida de excluir camada repetida

        # Conecta nameChanged de cada camada
        def _refresh():       # slot simples que repovoa tudo
            self.populate_combo_boxes()

        for layer in polygon_layers:
            layer.nameChanged.connect(_refresh)
            self._layer_name_change_connections.append((layer, _refresh))

    def update_comboBoxCamadaSobrep(self):
        """
        Atualiza as opções do comboBoxCamadaSobrep, exibindo apenas camadas de polígono diferentes da camada selecionada no comboBoxCamada.
        Mantém a seleção atual sempre que possível.
        """
        camada_id = self.comboBoxCamada.currentData()
        current_sobrep_id = self.comboBoxCamadaSobrep.currentData()

        layer_list = QgsProject.instance().mapLayers().values()
        polygon_layers = [
            layer for layer in layer_list 
            if isinstance(layer, QgsVectorLayer) 
            and QgsWkbTypes.geometryType(layer.wkbType()) == QgsWkbTypes.GeometryType.PolygonGeometry
            and layer.id() != camada_id]

        # Remove a camada usada diretamente para edição caso checkboxNova esteja desmarcado
        if not self.checkBoxNova.isChecked():
            if current_sobrep_id in [layer.id() for layer in polygon_layers]:
                polygon_layers = [layer for layer in polygon_layers if layer.id() != current_sobrep_id]

        self.comboBoxCamadaSobrep.blockSignals(True)
        self.comboBoxCamadaSobrep.clear()
        for layer in polygon_layers:
            self.comboBoxCamadaSobrep.addItem(layer.name(), layer.id())
        self.comboBoxCamadaSobrep.blockSignals(False)

        if self.comboBoxCamadaSobrep.count() > 0:
            if current_sobrep_id:
                idx = self.comboBoxCamadaSobrep.findData(current_sobrep_id)
                self.comboBoxCamadaSobrep.setCurrentIndex(idx if idx != -1 else 0)
            else:
                self.comboBoxCamadaSobrep.setCurrentIndex(0)

        # Garante que o checkbox reflita a seleção da NOVA camada
        self.update_layer_connections_sobrep()

    def _desativa_atualizacao_ao_vivo(self):
        """
        Desconecta todos os sinais de atualização em tempo real e limpa referências.
        """
        try:
            if getattr(self, "recorte_layer", None):
                self.recorte_layer.geometryChanged.disconnect(self._on_recorte_geom_changed)
                self.recorte_layer.featureAdded.disconnect(self._on_recorte_feat_added)
                self.recorte_layer.featureDeleted.disconnect(self._on_recorte_feat_deleted)
            if getattr(self, "mascara_layer", None):
                self.mascara_layer.geometryChanged.disconnect(self._on_mascara_alterada)
                self.mascara_layer.featureAdded.disconnect(self._on_mascara_alterada)
                self.mascara_layer.featureDeleted.disconnect(self._on_mascara_alterada)
        except Exception:
            pass  # nosec B110

        # Desconecte estes também!
        self._desconectar_sinais_resultado()

        self.recorte_layer = None
        self.mascara_layer = None
        self._union_mascara = None
        self._orig_geoms = {}
        self._recorte_history = []
        self._orig_offsets = {}
        self._last_result_geom = {}

    def _ativa_atualizacao_ao_vivo(self):
        """
        Liga/desliga sinais para atualização em tempo real após criar a camada Recorte.
        """
        # evita múltiplas conexões
        try:
            self.recorte_layer.geometryChanged.disconnect(self._on_recorte_geom_changed)
            self.mascara_layer.geometryChanged.disconnect(self._on_mascara_alterada)
            self.mascara_layer.featureAdded.disconnect(self._on_mascara_alterada)
            self.mascara_layer.featureDeleted.disconnect(self._on_mascara_alterada)
        except Exception:
            pass  # nosec B110

        # pré-calcula a união da máscara
        self._union_mascara = QgsGeometry.unaryUnion(
            [f.geometry() for f in self.mascara_layer.getFeatures()])

        # conecta sinais
        self.recorte_layer.geometryChanged.connect(self._on_recorte_geom_changed)

        self.mascara_layer.geometryChanged.connect(self._on_mascara_alterada)
        self.mascara_layer.featureAdded.connect(self._on_mascara_alterada)
        self.mascara_layer.featureDeleted.connect(self._on_mascara_alterada)

        self.recorte_layer.featureAdded.connect(self._on_recorte_feat_added) #novo
        self.recorte_layer.featureDeleted.connect(self._on_recorte_feat_deleted)

    def _on_recorte_feat_deleted(self, fid):
        """
        Remove a referência à geometria original da feição deletada da camada de recorte.
        Garante que o dicionário _orig_geoms não fique com dados órfãos.
        """
        self._orig_geoms.pop(fid, None)
        self._orig_offsets.pop(fid, None)
        self._last_result_geom.pop(fid, None)

    def _coletar_parametros_recorte(self):
        """
        Coleta e valida todos os parâmetros necessários para o recorte.
        Retorna tuple de dados prontos ou None se erro.
        """
        entrada_id = self.comboBoxCamada.currentData()
        sobrep_id = self.comboBoxCamadaSobrep.currentData()

        camada_entrada = QgsProject.instance().mapLayer(entrada_id)
        camada_sobrep = QgsProject.instance().mapLayer(sobrep_id)

        if not camada_entrada or not camada_sobrep:
            self.mostrar_mensagem(self.tr("Selecione corretamente as camadas."), "Erro")
            return None

        feats_entrada = (
            camada_entrada.selectedFeatures()
            if self.checkBoxSeleciona.isChecked()
            else list(camada_entrada.getFeatures()))

        feats_sobrep = (
            camada_sobrep.selectedFeatures()
            if self.checkBoxSelecionaSobrepos.isChecked()
            else list(camada_sobrep.getFeatures()))

        if not feats_entrada or not feats_sobrep:
            self.mostrar_mensagem(self.tr("Necessário ao menos uma feição de cada camada."), "Erro")
            return None

        geom_sobrep = QgsGeometry.unaryUnion([f.geometry() for f in feats_sobrep])

        if not geom_sobrep or geom_sobrep.isEmpty():
            self.mostrar_mensagem(self.tr("Geometria inválida para sobreposição."), "Erro")
            return None

        fid_to_original_geom = {feat.id(): QgsGeometry(feat.geometry()) for feat in feats_entrada}

        return (camada_entrada, camada_sobrep, feats_entrada, feats_sobrep, geom_sobrep, fid_to_original_geom)

    def _normalizar_geometria_uniao(self, geom):
        """
        Valida/corrige a geometria final da união antes de salvar.
        Retorna None se a geometria continuar inválida ou vazia.
        """
        if not geom or geom.isEmpty():
            return None

        try:
            if not geom.isGeosValid():
                geom = geom.makeValid()
        except Exception:
            pass  # nosec B110

        if not geom or geom.isEmpty():
            return None

        try:
            if QgsWkbTypes.geometryType(geom.wkbType()) != QgsWkbTypes.GeometryType.PolygonGeometry:
                return None
        except Exception:
            return None

        return geom

    def _gerar_geometria_uniao_unica(self, feats_entrada, feats_sobrep):
        """
        Gera uma única geometria de união a partir das feições da camada
        de entrada e da camada de sobreposição.
        """
        geoms = []

        for feat in feats_entrada:
            g = feat.geometry()
            if g and not g.isEmpty():
                geoms.append(QgsGeometry(g))

        for feat in feats_sobrep:
            g = feat.geometry()
            if g and not g.isEmpty():
                geoms.append(QgsGeometry(g))

        if not geoms:
            return None

        geom_uniao = QgsGeometry.unaryUnion(geoms)
        return self._normalizar_geometria_uniao(geom_uniao)

    def _salvar_resultado_uniao_unica(self, resultado_layer, camada_entrada, geom_uniao, feat_modelo=None):
        """
        Salva uma única feição contendo a geometria final da união.
        Copia atributos apenas quando fizer sentido por nome de campo.
        """
        if not resultado_layer.isEditable():
            resultado_layer.startEditing()

        nova_feat = QgsFeature(resultado_layer.fields())
        nova_feat.setGeometry(geom_uniao)

        if feat_modelo:
            for fld in resultado_layer.fields():
                nome = fld.name()

                if nome == "orig_fid":
                    nova_feat.setAttribute(nome, feat_modelo.id())
                elif camada_entrada.fields().indexOf(nome) != -1:
                    try:
                        nova_feat.setAttribute(nome, feat_modelo[nome])
                    except Exception:
                        pass  # nosec B110
        else:
            idx_orig = resultado_layer.fields().indexOf("orig_fid")
            if idx_orig != -1:
                nova_feat.setAttribute(idx_orig, -1)

        idx_area = resultado_layer.fields().indexOf("Area")
        idx_perimetro = resultado_layer.fields().indexOf("Perimetro")

        if idx_area != -1 or idx_perimetro != -1:
            d = QgsDistanceArea()
            d.setSourceCrs(resultado_layer.crs(), QgsProject.instance().transformContext())
            d.setEllipsoid(QgsProject.instance().crs().ellipsoidAcronym())

            if resultado_layer.crs().isGeographic():
                perimetro = round(d.measurePerimeter(geom_uniao), 3)
                area = round(d.measureArea(geom_uniao), 3)
            else:
                perimetro = round(geom_uniao.length(), 3)
                area = round(geom_uniao.area(), 3)

            if idx_perimetro != -1:
                nova_feat.setAttribute(idx_perimetro, perimetro)
            if idx_area != -1:
                nova_feat.setAttribute(idx_area, area)

        ok = resultado_layer.addFeature(nova_feat)
        if not ok:
            return False

        resultado_layer.commitChanges()
        resultado_layer.triggerRepaint()
        return True

    def closeEvent(self, event):
        # ao fechar, desativa atualizações
        self._desativa_atualizacao_ao_vivo()
        super().closeEvent(event)

    def _on_layer_removida(self, layer_id):
        """Desconecta os sinais se a camada recorte ou máscara for removida."""
        if hasattr(self, "recorte_layer") and self.recorte_layer:
            if self.recorte_layer.id() == layer_id:
                self._desativa_atualizacao_ao_vivo()
        if hasattr(self, "mascara_layer") and self.mascara_layer:
            if self.mascara_layer.id() == layer_id:
                self._desativa_atualizacao_ao_vivo()

    def executar_recorte(self):
        """
        Executa a operação selecionada (diferença, interseção ou união) entre as camadas escolhidas.
        Valida parâmetros, processa a operação e ativa ou desativa atualizações dinâmicas conforme necessário.
        """
        # Identifica a operação escolhida
        if self.radioButtonDiferenca.isChecked():
            operacao = 'diferenca'
        elif self.radioButtonItersecao.isChecked():
            operacao = 'intersecao'
        elif self.radioButtonUniao.isChecked():
            operacao = 'uniao'
        else:
            self.mostrar_mensagem(self.tr("Selecione o modo de operação (Recortar, Diferença, Interseção ou União)."), "Aviso")
            return

        # Coleta parâmetros
        params = self._coletar_parametros_recorte()
        if params is None:
            return

        camada_entrada, camada_sobrep, feats_entrada, feats_sobrep, geom_sobrep, fid_to_original_geom = params

        # Executa operação
        resultado_layer = self._processar_recorte_operacao(
            operacao,
            camada_entrada,
            camada_sobrep,
            feats_entrada,
            feats_sobrep,
            geom_sobrep,
            fid_to_original_geom)

        if not resultado_layer:
            return

        # Pós-processamento
        self.recorte_layer = resultado_layer
        self.mascara_layer = camada_sobrep

        if operacao in ('diferenca', 'intersecao'):
            self._operacao_atual = operacao

            # Se NÃO é nova camada, recorte_layer == mascara_layer -> risco de loop/resultado estranho
            if not self.checkBoxNova.isChecked():
                self.mostrar_mensagem(self.tr("No modo 'Atualizar camada', a atualização ao vivo é desativada para evitar conflitos (recorte e máscara ficam na mesma camada). Use 'Nova camada' para modo ao vivo."), "Aviso", duracao=3)

                self._desativa_atualizacao_ao_vivo()
            else:
                self._ativa_atualizacao_ao_vivo()
        else:
            self._desativa_atualizacao_ao_vivo()

    def _on_mascara_alterada(self, *args):
        """
        Atualiza a geometria das feições da camada de recorte quando a máscara (camada de sobreposição) é alterada.
        Regenera o resultado a partir da geometria original (_orig_geoms) + offset acumulado (_orig_offsets),
        evitando perda progressiva (principalmente na interseção).
        """
        # Camadas ainda existem?
        if (not getattr(self, "recorte_layer", None) or
            not QgsProject.instance().mapLayer(self.recorte_layer.id())):
            self._desativa_atualizacao_ao_vivo()
            return

        if (not getattr(self, "mascara_layer", None) or
            not QgsProject.instance().mapLayer(self.mascara_layer.id())):
            self._desativa_atualizacao_ao_vivo()
            return

        # Garante edição (changeGeometry exige edição)
        if not self.recorte_layer.isEditable():
            self.recorte_layer.startEditing()

        # Recalcula união da máscara (filtrando geometrias válidas)
        geoms_masc = []
        for f in self.mascara_layer.getFeatures():
            g = f.geometry()
            if g and not g.isEmpty():
                geoms_masc.append(g)

        if not geoms_masc:
            # máscara sem geometria útil -> nada a aplicar
            self._union_mascara = None
            return

        self._union_mascara = QgsGeometry.unaryUnion(geoms_masc)
        if not self._union_mascara or self._union_mascara.isEmpty():
            return

        operacao = getattr(self, "_operacao_atual", "diferenca")

        # Coletores para evitar mexer no iterator enquanto percorre
        ids_para_deletar = []
        updates_last_geom = {}

        try:
            self.recorte_layer.blockSignals(True)

            for feat in self.recorte_layer.getFeatures():
                fid = feat.id()

                orig = self._orig_geoms.get(fid)
                if not orig or orig.isEmpty():
                    continue

                # Offset acumulado (recomendado)
                if hasattr(self, "_orig_offsets") and fid in self._orig_offsets:
                    offx, offy = self._orig_offsets.get(fid, (0.0, 0.0))
                else:
                    # Fallback: tenta estimar deslocamento comparando bbox atual com bbox do original
                    try:
                        bb_o = orig.boundingBox()
                        bb_c = feat.geometry().boundingBox() if feat.geometry() else None
                        if bb_c and (not bb_o.isNull()) and (not bb_c.isNull()):
                            c1 = bb_o.center()
                            c2 = bb_c.center()
                            offx = c2.x() - c1.x()
                            offy = c2.y() - c1.y()
                        else:
                            offx = offy = 0.0
                    except Exception:
                        offx = offy = 0.0

                # Recria geometria base a partir do ORIGINAL (regeneração)
                geom_base = QgsGeometry(orig)
                if offx or offy:
                    geom_base.translate(offx, offy)

                # Aplica operação
                if operacao == "intersecao":
                    nova_geom = geom_base.intersection(self._union_mascara)
                else:
                    nova_geom = geom_base.difference(self._union_mascara)

                # Se ficou vazia, remove a feição do resultado
                if (not nova_geom) or nova_geom.isEmpty():
                    ids_para_deletar.append(fid)
                    continue

                # Grava geometria e atualiza atributos
                self.recorte_layer.changeGeometry(fid, nova_geom)
                self.atualizar_valores_poligono(self.recorte_layer, fid, geom_override=nova_geom)

                # guarda last geom (se você estiver usando esse controle)
                updates_last_geom[fid] = QgsGeometry(nova_geom)

            # Deleta depois do loop (seguro)
            if ids_para_deletar:
                self.recorte_layer.deleteFeatures(ids_para_deletar)
                # limpa rastros também
                for fid in ids_para_deletar:
                    self._orig_geoms.pop(fid, None)
                    if hasattr(self, "_orig_offsets"):
                        self._orig_offsets.pop(fid, None)
                    if hasattr(self, "_last_result_geom"):
                        self._last_result_geom.pop(fid, None)

        finally:
            self.recorte_layer.blockSignals(False)

        # Atualiza last_result_geom fora do bloco (opcional)
        if hasattr(self, "_last_result_geom"):
            self._last_result_geom.update(updates_last_geom)

    def _on_recorte_geom_changed(self, fid, nova_geom):
        """
        Diferença/interseção ao vivo.
        NOVA REGRA (interseção): se o polígono sair 100% da máscara (interseção vazia),
        a feição é DELETADA e NÃO se recupera ao retornar.
        """
        operacao = getattr(self, "_operacao_atual", "diferenca")

        if not getattr(self, "recorte_layer", None):
            return
        if not QgsProject.instance().mapLayer(self.recorte_layer.id()):
            self._desativa_atualizacao_ao_vivo()
            return

        orig = self._orig_geoms.get(fid)
        if not orig or orig.isEmpty():
            return
        if not getattr(self, "_union_mascara", None) or self._union_mascara.isEmpty():
            return
        if not nova_geom or nova_geom.isEmpty():
            return

        # 1) Delta do arrasto medido pelo bbox do último resultado
        last = self._last_result_geom.get(fid)
        dx = dy = 0.0
        if last and (not last.isEmpty()):
            bb_last = last.boundingBox()
            bb_new = nova_geom.boundingBox()
            if (not bb_last.isNull()) and (not bb_new.isNull()):
                c1 = bb_last.center()
                c2 = bb_new.center()
                dx = c2.x() - c1.x()
                dy = c2.y() - c1.y()

        # 2) Acumula offset total
        offx, offy = self._orig_offsets.get(fid, (0.0, 0.0))
        offx += dx
        offy += dy
        self._orig_offsets[fid] = (offx, offy)

        # 3) Reaplica operação a partir do ORIGINAL traduzido
        geom_base = QgsGeometry(orig)
        if offx or offy:
            geom_base.translate(offx, offy)

        if operacao == "intersecao":
            nova_geom_final = geom_base.intersection(self._union_mascara)

            # ✅ REGRA NOVA: saiu totalmente da máscara -> apaga e não recupera
            if (not nova_geom_final) or nova_geom_final.isEmpty():
                layer_id = self.recorte_layer.id()

                # limpa rastros já (mesmo se a layer sumir depois)
                self._orig_geoms.pop(fid, None)
                self._orig_offsets.pop(fid, None)
                self._last_result_geom.pop(fid, None)

                def _delete_later(_lid=layer_id, _fid=fid):
                    lyr = QgsProject.instance().mapLayer(_lid)
                    if not lyr:
                        return
                    if not lyr.isEditable():
                        lyr.startEditing()
                    lyr.blockSignals(True)
                    try:
                        lyr.deleteFeatures([_fid])
                    finally:
                        lyr.blockSignals(False)

                QTimer.singleShot(0, _delete_later)
                return

        else:
            # diferença (mantém seu comportamento atual)
            nova_geom_final = geom_base.difference(self._union_mascara)
            if (not nova_geom_final) or nova_geom_final.isEmpty():
                return

        # 4) Atualiza geometria + atributos e guarda o último resultado
        self.recorte_layer.blockSignals(True)
        try:
            self.recorte_layer.changeGeometry(fid, nova_geom_final)
        finally:
            self.recorte_layer.blockSignals(False)

        self._last_result_geom[fid] = QgsGeometry(nova_geom_final)

        def delayed_update():
            if self.recorte_layer and QgsProject.instance().mapLayer(self.recorte_layer.id()):
                self.atualizar_valores_poligono(self.recorte_layer, fid)

        QTimer.singleShot(0, delayed_update)

    def _on_recorte_feat_added(self, fid):
        """
        Ajusta a geometria da feição adicionada conforme a operação (diferença/interseção),
        SEM commitar (preserva undo/redo) e inicializa tracking para regeneração.
        """
        # Camada ainda existe?
        if (not getattr(self, "recorte_layer", None) or
            not QgsProject.instance().mapLayer(self.recorte_layer.id())):
            self._desativa_atualizacao_ao_vivo()
            return

        # Garante edição (changeGeometry/deleteFeatures exigem edição)
        if not self.recorte_layer.isEditable():
            self.recorte_layer.startEditing()

        # Busca feição recém-criada
        try:
            feat = next(self.recorte_layer.getFeatures(QgsFeatureRequest(fid)), None)
        except Exception:
            feat = None

        if not feat:
            return

        g0 = feat.geometry()
        if not g0 or g0.isEmpty():
            return

        # Guarda original e inicializa tracking ANTES de qualquer modificação
        self._orig_geoms[fid] = QgsGeometry(g0)
        self._orig_offsets[fid] = (0.0, 0.0)

        # Garante máscara unida
        if not getattr(self, "_union_mascara", None) or self._union_mascara.isEmpty():
            if getattr(self, "mascara_layer", None) and QgsProject.instance().mapLayer(self.mascara_layer.id()):
                geoms_m = []
                for f in self.mascara_layer.getFeatures():
                    gm = f.geometry()
                    if gm and not gm.isEmpty():
                        geoms_m.append(gm)
                self._union_mascara = QgsGeometry.unaryUnion(geoms_m) if geoms_m else None

        if not self._union_mascara or self._union_mascara.isEmpty():
            # Sem máscara válida: não tem o que recortar/intersectar, mas mantém tracking
            self._last_result_geom[fid] = QgsGeometry(g0)
            return

        operacao = getattr(self, "_operacao_atual", "diferenca")

        # Aplica operação
        try:
            if operacao == "intersecao":
                geom_rec = g0.intersection(self._union_mascara)
            else:
                geom_rec = g0.difference(self._union_mascara)
        except Exception:
            geom_rec = None

        # Se resultado ficou vazio: remove a feição recém-criada (evita “fantasma”)
        if (not geom_rec) or geom_rec.isEmpty():
            self.recorte_layer.blockSignals(True)
            try:
                self.recorte_layer.deleteFeatures([fid])
            finally:
                self.recorte_layer.blockSignals(False)

            # limpa rastros
            self._orig_geoms.pop(fid, None)
            self._orig_offsets.pop(fid, None)
            self._last_result_geom.pop(fid, None)
            return

        # Grava geometria resultante sem disparar loop
        self.recorte_layer.blockSignals(True)
        try:
            self.recorte_layer.changeGeometry(fid, geom_rec)
        finally:
            self.recorte_layer.blockSignals(False)

        # Guarda "último resultado" para medir delta do próximo arrasto
        self._last_result_geom[fid] = QgsGeometry(geom_rec)

        # Atualiza área/perímetro (sem depender de commit)
        def delayed_update():
            if self.recorte_layer and QgsProject.instance().mapLayer(self.recorte_layer.id()):
                self.atualizar_valores_poligono(self.recorte_layer, fid, geom_override=geom_rec)

        QTimer.singleShot(0, delayed_update)

    def _processar_recorte_operacao(self, operacao, camada_entrada, camada_sobrep, feats_entrada, feats_sobrep, geom_sobrep, fid_to_original_geom):
        """
        Processa a operação geométrica (diferença, interseção, união).
        Retorna a camada resultado (memory ou camada de sobreposição).
        """
        nome_base = camada_entrada.name()

        if operacao == 'diferenca':
            nome_resultado = f"{nome_base}_diferenca"
        elif operacao == 'intersecao':
            nome_resultado = f"{nome_base}_interseção"
        elif operacao == 'uniao':
            nome_resultado = f"{nome_base}_uniao"
        else:
            nome_resultado = f"{nome_base}_resultado"

        # UNIÃO: geometria única
        if operacao == 'uniao':
            geom_uniao = self._gerar_geometria_uniao_unica(feats_entrada, feats_sobrep)
            if not geom_uniao:
                self.mostrar_mensagem(self.tr("Não foi possível gerar uma geometria válida para a união."), "Erro")
                return None

            feat_modelo = feats_entrada[0] if feats_entrada else None

            if self.checkBoxNova.isChecked():
                resultado_layer = self._criar_camada_resultado(operacao, camada_entrada, nome_resultado)

                ok = self._salvar_resultado_uniao_unica(
                    resultado_layer,
                    camada_entrada,
                    geom_uniao,
                    feat_modelo=feat_modelo)
                if not ok:
                    self.mostrar_mensagem(self.tr("Falha ao salvar a geometria de união."), "Erro")
                    return None

                QgsProject.instance().addMapLayer(resultado_layer)
                self._mensagem_sucesso_operacao(operacao)
                return resultado_layer

            else:
                resultado_layer = camada_sobrep

                self.mostrar_mensagem(self.tr("Modo 'Atualizar camada' irá substituir as feições de: {layer_name} (você pode desfazer enquanto estiver em edição).").format(layer_name=resultado_layer.name()), "Aviso", duracao=2)

                if not resultado_layer.isEditable():
                    resultado_layer.startEditing()

                if resultado_layer.fields().indexOf("orig_fid") == -1:
                    resultado_layer.dataProvider().addAttributes([QgsField("orig_fid", QMetaType.Type.Int)])
                    resultado_layer.updateFields()

                self.configura_campos(resultado_layer)

                ids_existentes = [f.id() for f in resultado_layer.getFeatures()]
                if ids_existentes:
                    resultado_layer.deleteFeatures(ids_existentes)

                ok = self._salvar_resultado_uniao_unica(
                    resultado_layer,
                    camada_entrada,
                    geom_uniao,
                    feat_modelo=feat_modelo)
                if not ok:
                    self.mostrar_mensagem(self.tr("Falha ao atualizar a camada com a união."), "Erro")
                    return None

                self._mensagem_sucesso_operacao(operacao, sobreposicao=True)
                return resultado_layer

        # DIFERENÇA / INTERSEÇÃO
        if self.checkBoxNova.isChecked():
            resultado_layer = self._criar_camada_resultado(operacao, camada_entrada, nome_resultado)

            self._adicionar_feicoes_resultado(
                resultado_layer, operacao, feats_entrada, geom_sobrep, camada_entrada, fid_to_original_geom)

            QgsProject.instance().addMapLayer(resultado_layer)
            self._mensagem_sucesso_operacao(operacao)
            return resultado_layer

        else:
            resultado_layer = camada_sobrep

            self.mostrar_mensagem(self.tr("Modo 'Atualizar camada' irá substituir as feições de: {layer_name} (você pode desfazer enquanto estiver em edição).").format(layer_name=resultado_layer.name()), "Aviso", duracao=2)

            if not resultado_layer.isEditable():
                resultado_layer.startEditing()

            if resultado_layer.fields().indexOf("orig_fid") == -1:
                resultado_layer.dataProvider().addAttributes([QgsField("orig_fid", QMetaType.Type.Int)])
                resultado_layer.updateFields()

            self.configura_campos(resultado_layer)

            ids_existentes = [f.id() for f in resultado_layer.getFeatures()]
            if ids_existentes:
                resultado_layer.deleteFeatures(ids_existentes)

            idx_area = resultado_layer.fields().indexOf("Area")
            idx_per = resultado_layer.fields().indexOf("Perimetro")
            tem_area_per = (idx_area != -1) or (idx_per != -1)

            d = None
            if tem_area_per:
                d = QgsDistanceArea()
                d.setSourceCrs(resultado_layer.crs(), QgsProject.instance().transformContext())
                d.setEllipsoid(QgsProject.instance().crs().ellipsoidAcronym())

            novas = []
            for feat in feats_entrada:
                nova_geom = self._calcular_geometria_operacao(operacao, feat.geometry(), geom_sobrep)
                if not nova_geom or nova_geom.isEmpty():
                    continue

                nf = QgsFeature(resultado_layer.fields())
                nf.setGeometry(nova_geom)

                for fld in resultado_layer.fields():
                    nm = fld.name()
                    if nm == "orig_fid":
                        nf.setAttribute("orig_fid", feat.id())
                    else:
                        if camada_entrada.fields().indexOf(nm) != -1:
                            nf.setAttribute(nm, feat[nm])

                if tem_area_per:
                    if resultado_layer.crs().isGeographic():
                        perimetro = round(d.measurePerimeter(nova_geom), 3)
                        area = round(d.measureArea(nova_geom), 3)
                    else:
                        perimetro = round(nova_geom.length(), 3)
                        area = round(nova_geom.area(), 3)
                    if idx_per != -1:
                        nf.setAttribute(idx_per, perimetro)
                    if idx_area != -1:
                        nf.setAttribute(idx_area, area)

                novas.append(nf)

            if novas:
                resultado_layer.addFeatures(novas)

            resultado_layer.commitChanges()

            self._orig_geoms = {}
            for f in resultado_layer.getFeatures():
                try:
                    orig_fid = f["orig_fid"]
                except Exception:
                    orig_fid = None
                if orig_fid is None:
                    continue
                if orig_fid in fid_to_original_geom:
                    self._orig_geoms[f.id()] = QgsGeometry(fid_to_original_geom[orig_fid])

            resultado_layer.triggerRepaint()
            self._mensagem_sucesso_operacao(operacao, sobreposicao=True)
            return resultado_layer

    def _criar_camada_resultado(self, operacao, camada_entrada, nome_resultado):
        """
        Cria e configura uma nova camada de memória para armazenar o resultado da operação de geoprocessamento.
        Define campos necessários, adiciona campos de área, perímetro e orig_fid, e conecta sinais para atualização de atributos.
        """
        epsg = camada_entrada.crs().authid()

        # Sempre usar MultiPolygon para operações de geoprocessamento
        geom_type = "MultiPolygon"
        uri = f"{geom_type}?crs={epsg}"

        resultado_layer = QgsVectorLayer(uri, nome_resultado, "memory")
        resultado_layer.startEditing()
        campos = camada_entrada.fields().toList()
        campos.append(QgsField('orig_fid', QMetaType.Type.Int))
        resultado_layer.dataProvider().addAttributes(campos)
        resultado_layer.updateFields()

        self.configura_campos(resultado_layer)
        self._conectar_sinais_resultado(resultado_layer)

        return resultado_layer

    def _on_feature_added_resultado(self, fid):
        """
        Callback para atualizar área e perímetro quando uma nova feição é adicionada à camada de resultado.
        """
        if hasattr(self, "recorte_layer") and self.recorte_layer:
            self.atualizar_valores_poligono(self.recorte_layer, fid)

    def _on_geometry_changed_resultado(self, fid, geom):
        """
        Callback para atualizar área e perímetro quando a geometria de uma feição na camada de resultado é alterada.
        """
        if hasattr(self, "recorte_layer") and self.recorte_layer:
            self.atualizar_valores_poligono(self.recorte_layer, fid)

    def _adicionar_feicoes_resultado(self, resultado_layer, operacao, feats_entrada, geom_sobrep, camada_entrada, fid_to_original_geom):
        """
        Adiciona as feições resultantes da operação na camada de saída.
        """
        for feat in feats_entrada:
            nova_geom = self._calcular_geometria_operacao(operacao, feat.geometry(), geom_sobrep)
            if nova_geom and not nova_geom.isEmpty():
                nova_feat = self._criar_feat_resultado(resultado_layer, camada_entrada, feat, nova_geom)
                resultado_layer.addFeature(nova_feat)

        resultado_layer.commitChanges()
        self._orig_geoms = {}
        for f in resultado_layer.getFeatures():
            orig_fid = f['orig_fid']
            self._orig_geoms[f.id()] = QgsGeometry(fid_to_original_geom[orig_fid])

        # Inicializa controle de movimento para regeneração
        self._orig_offsets = {}
        self._last_result_geom = {}
        for f in resultado_layer.getFeatures():
            self._orig_offsets[f.id()] = (0.0, 0.0)
            self._last_result_geom[f.id()] = QgsGeometry(f.geometry())

        # Atualiza área/perímetro de todas as feições
        for feat in resultado_layer.getFeatures():
            self.atualizar_valores_poligono(resultado_layer, feat.id())

    def _calcular_geometria_operacao(self, operacao, geom, geom_sobrep):
        """
        Realiza a operação geométrica correta entre a geometria e a máscara.
        """
        if operacao == 'diferenca':
            return geom.difference(geom_sobrep)
        elif operacao == 'intersecao':
            return geom.intersection(geom_sobrep)
        elif operacao == 'uniao':
            return geom.combine(geom_sobrep)
        else:
            return None

    def _mensagem_sucesso_operacao(self, operacao, sobreposicao=False):
        """
        Exibe mensagem de sucesso adequada ao tipo de operação.
        """
        if operacao == 'diferenca':
            msg = self.tr("Camada de diferença criada.") if not sobreposicao else self.tr("Camada de sobreposição atualizada com diferença.")
        elif operacao == 'intersecao':
            msg = self.tr("Camada de interseção criada.") if not sobreposicao else self.tr("Camada de sobreposição atualizada com interseção.")
        elif operacao == 'uniao':
            msg = self.tr("Camada de união criada.") if not sobreposicao else self.tr("Camada de sobreposição atualizada com união.")
        else:
            msg = self.tr("Operação concluída.")
        self.mostrar_mensagem(msg, "Sucesso")

    def configura_campos(self, camada):
        """
        Garante que a camada possua os campos 'ID', 'Perimetro' e 'Area'.
        Se já existem, apenas atualiza restrições e widgets. Se não, adiciona.
        """
        prov = camada.dataProvider()
        fields_to_add = []

        # Verifica campos existentes
        idx_id = camada.fields().indexOf("ID")
        idx_perimetro = camada.fields().indexOf("Perimetro")
        idx_area = camada.fields().indexOf("Area")

        # Campos que faltam são adicionados
        if idx_id == -1:
            id_field = QgsField("ID", QMetaType.Type.Int)
            # Restrições
            constraints = QgsFieldConstraints()
            constraints.setConstraint(QgsFieldConstraints.Constraint.ConstraintUnique)
            constraints.setConstraint(QgsFieldConstraints.Constraint.ConstraintNotNull)
            id_field.setConstraints(constraints)
            fields_to_add.append(id_field)
        if idx_perimetro == -1:
            perimetro_field = QgsField("Perimetro", QMetaType.Type.Double, "double", 20, 3)
            fields_to_add.append(perimetro_field)
        if idx_area == -1:
            area_field = QgsField("Area", QMetaType.Type.Double, "double", 20, 3)
            fields_to_add.append(area_field)

        # Adiciona campos que faltam
        if fields_to_add:
            prov.addAttributes(fields_to_add)
            camada.updateFields()

        # Atualiza índices após possível adição
        idx_id = camada.fields().indexOf("ID")
        idx_perimetro = camada.fields().indexOf("Perimetro")
        idx_area = camada.fields().indexOf("Area")

        # Configura valor default do ID sequencial
        if idx_id != -1:
            expr = 'coalesce(maximum("ID"),0) + 1'
            camada.setDefaultValueDefinition(idx_id, QgsDefaultValue(expr))

        # Oculta Perímetro e Área (editor widget)
        widget_setup_oculto = QgsEditorWidgetSetup("Hidden", {})
        if idx_perimetro != -1:
            camada.setEditorWidgetSetup(idx_perimetro, widget_setup_oculto)
        if idx_area != -1:
            camada.setEditorWidgetSetup(idx_area, widget_setup_oculto)

    def _criar_feat_resultado(self, resultado_layer, camada_entrada, feat, nova_geom):
        """
        Cria a feição de saída, preenchendo atributos necessários.
        Calcula área e perímetro a partir da geometria recortada.
        """
        nova_feat = QgsFeature(resultado_layer.fields())
        for field in camada_entrada.fields():
            nova_feat.setAttribute(field.name(), feat[field.name()])
        nova_feat.setAttribute('orig_fid', feat.id())
        nova_feat.setGeometry(nova_geom)

        # Calcula área e perímetro da nova geometria
        idx_area = resultado_layer.fields().indexOf("Area")
        idx_perimetro = resultado_layer.fields().indexOf("Perimetro")
        if idx_area != -1 or idx_perimetro != -1:
            d = QgsDistanceArea()
            d.setSourceCrs(resultado_layer.crs(), QgsProject.instance().transformContext())
            d.setEllipsoid(QgsProject.instance().crs().ellipsoidAcronym())
            if resultado_layer.crs().isGeographic():
                perimetro = round(d.measurePerimeter(nova_geom), 3)
                area = round(d.measureArea(nova_geom), 3)
            else:
                perimetro = round(nova_geom.length(), 3)
                area = round(nova_geom.area(), 3)
            if idx_perimetro != -1:
                nova_feat.setAttribute(idx_perimetro, perimetro)
            if idx_area != -1:
                nova_feat.setAttribute(idx_area, area)

        return nova_feat

    def atualizar_valores_poligono(self, camada: QgsVectorLayer, fid: int, geom_override=None):
        """
        Atualiza os valores de 'Perimetro' e 'Area' de um polígono quando ele é adicionado ou sua geometria é alterada.
        Considera cálculos específicos caso o sistema de referência seja geográfico.
        """
        idx_perimetro = camada.fields().indexOf("Perimetro")
        idx_area = camada.fields().indexOf("Area")
        if idx_perimetro == -1 or idx_area == -1:
            return

        if geom_override is not None:
            geom = geom_override
        else:
            feature = camada.getFeature(fid)
            if not (feature.isValid() and feature.geometry() and not feature.geometry().isEmpty()):
                return
            geom = feature.geometry()

        d = QgsDistanceArea()
        d.setSourceCrs(camada.crs(), QgsProject.instance().transformContext())
        d.setEllipsoid(QgsProject.instance().crs().ellipsoidAcronym())
        if camada.crs().isGeographic():
            perimetro = round(d.measurePerimeter(geom), 3)
            area = round(d.measureArea(geom), 3)
        else:
            perimetro = round(geom.length(), 3)
            area = round(geom.area(), 3)

        camada.changeAttributeValue(fid, idx_perimetro, perimetro)
        camada.changeAttributeValue(fid, idx_area, area)