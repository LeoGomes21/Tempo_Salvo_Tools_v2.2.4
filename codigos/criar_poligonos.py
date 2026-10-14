from qgis.core import (QgsField, QgsProject, QgsVectorLayer, QgsWkbTypes, QgsFieldConstraints, QgsEditorWidgetSetup, QgsTextFormat, QgsTextBufferSettings, QgsVectorLayerSimpleLabeling, QgsPalLayerSettings, QgsTextBackgroundSettings, QgsDistanceArea, QgsDefaultValue, Qgis, QgsEditFormConfig)
from qgis.PyQt.QtGui import QFont, QColor
from qgis.PyQt.QtCore import QVariant, QMetaType, QCoreApplication, QTimer
from typing import Optional

class CamadaPoligonosManager:
    """
    Gerencia a criação e a manutenção de camadas temporárias de polígonos,
    atualizando perímetro/área automaticamente e configurando rótulos.
    """
    def __init__(self, iface):
        """
        :param iface: instância da interface QGIS (iface)
        """
        self.iface = iface
        # internas de edição/Undo/Redo do QGIS.
        self._atualizacoes_pendentes = set()

    def tr(self, message):
        """
        Traduz textos deste diálogo.
        O contexto precisa ser estável para o Qt Linguist encontrar as traduções.
        """
        return QCoreApplication.translate("CamadaPoligonosManager", message)

    def criar_camada_poligonos(self, nome_camada: Optional[str] = None, suprimir_formulario: bool = False):
        """
        Cria e adiciona uma nova camada temporária de polígonos ao projeto,
        já pronta para edição.

        :param nome_camada: Nome desejado; se None, será gerado automaticamente.
        :return: QgsVectorLayer criada
        """
        crs_projeto = QgsProject.instance().crs().authid()
        nome_camada = nome_camada or self.gera_nome_camada(self.tr("Polígonos Temporários"))

        # 1) Cria a camada em memória
        vl = QgsVectorLayer(f"Polygon?crs={crs_projeto}", nome_camada, "memory")
        if not vl or not vl.isValid():
            try:
                self.iface.messageBar().pushCritical(self.tr("Tempo Salvo Tools"), self.tr("Falha ao criar camada temporária de polígonos (camada inválida)."))
            except Exception:
                pass  # nosec B110
            return None

        # 2) Configura campos e rótulos (só depois de validar)
        self.configura_campos(vl)
        self.configura_etiquetas(vl)

        # 3) Adiciona ao projeto e inicia edição
        proj = QgsProject.instance()
        proj.addMapLayer(vl, False)
        proj.layerTreeRoot().insertLayer(0, vl)

        vl.startEditing()

        # 4) Conecta sinais (agora a layer já está no projeto, mais seguro)
        self.conectar_sinais(vl)

        # Configura a abertura do formulário de atributos
        try:
            cfg = vl.editFormConfig()

            try:
                estado = ( Qgis.AttributeFormSuppression.On
                    if suprimir_formulario
                    else Qgis.AttributeFormSuppression.Off)
                cfg.setSuppress(estado)

            except Exception:
                estado = (QgsEditFormConfig.FeatureFormSuppress.SuppressOn
                    if suprimir_formulario
                    else QgsEditFormConfig.FeatureFormSuppress.SuppressOff)
                cfg.setSuppress(estado)

            vl.setEditFormConfig(cfg)

        except Exception:
            pass  # nosec B110

        # 5) Ativa a camada e aciona "Adicionar feição"
        self.iface.setActiveLayer(vl)
        action = self.iface.actionAddFeature()
        if action:
            action.trigger()

        return vl

    def gera_nome_camada(self, nome_base: str) -> str:
        """
        Esta função gera um nome único para uma camada com base em um nome base fornecido.
        Ela faz isso adicionando um contador ao nome base e incrementando-o até que um nome único seja encontrado.
        """
        contador = 1
        nome_camada = f"{nome_base} {contador}"  # Começa a contagem a partir de 1
        while QgsProject.instance().mapLayersByName(nome_camada): # Verifica se o nome já existe
            contador += 1
            nome_camada = f"{nome_base} {contador}"  # Atualiza o nome da camada com o novo contador
        return nome_camada # Retorna o nome único

    def conectar_sinais(self, camada: QgsVectorLayer):
        """
        Atualiza perímetro e área durante a edição, mas evita novas
        alterações no buffer enquanto a camada está sendo salva.
        """
        layer_id = camada.id()
        camada.setCustomProperty("ts_em_commit", False)

        camada.featureAdded.connect(
            lambda fid, _id=layer_id:
            self._atualizar_valores_por_layer_id(_id, fid))

        camada.geometryChanged.connect(
            lambda fid, _geom, _id=layer_id:
            self._atualizar_valores_por_layer_id(_id, fid))

        camada.beforeCommitChanges.connect(
            lambda _stop, lyr=camada:
            lyr.setCustomProperty("ts_em_commit", True))

        camada.afterCommitChanges.connect(
            lambda lyr=camada:
            lyr.setCustomProperty("ts_em_commit", False))

        camada.afterRollBack.connect(
            lambda lyr=camada:
            lyr.setCustomProperty("ts_em_commit", False))

    def _agendar_atualizacao(self, layer_id: str, fid: int):
        """
        Agenda a atualização para o próximo ciclo
        da interface do QGIS.

        Evita alterar atributos enquanto o QGIS
        ainda está executando uma operação de
        edição, Undo ou Redo.
        """
        chave = (layer_id, int(fid))

        if chave in self._atualizacoes_pendentes:
            return

        self._atualizacoes_pendentes.add(chave)

        def executar():
            self._atualizacoes_pendentes.discard(chave)
            layer = QgsProject.instance().mapLayer(layer_id)

            if (not isinstance(layer, QgsVectorLayer)
                or not layer.isValid()
                or not layer.isEditable()):
                return

            feature = layer.getFeature(fid)

            # Muito importante para Ctrl+Z:
            # se a feição acabou de ser desfeita,
            # ela já não existe mais.
            if (not feature
                or not feature.isValid()):
                return

            geom = feature.geometry()

            if (geom is None
                or geom.isEmpty()):
                return

            self.atualizar_valores_poligono(layer, fid)

        QTimer.singleShot(0, executar)

    def _atualizar_valores_por_layer_id(self, layer_id: str, fid: int):
        layer = QgsProject.instance().mapLayer(layer_id)

        if not isinstance(layer, QgsVectorLayer) or not layer.isValid():
            return

        if layer.customProperty("ts_em_commit", False):
            return

        self.atualizar_valores_poligono(layer, fid)

    def atualizar_valores_poligono(self, camada: QgsVectorLayer, fid: int):
        """
        Esta função atualiza os valores de 'Perimetro' e 'Area' de um polígono quando ele é adicionado ou sua geometria é alterada.
        Considera cálculos específicos caso o sistema de referência seja geográfico.
        """
        if not camada or not camada.isValid():
            return
        if not camada.isEditable():
            return

        index_perimetro = camada.fields().indexOf("Perimetro")
        index_area = camada.fields().indexOf("Area")
        if index_perimetro == -1 or index_area == -1:
            return

        feature = camada.getFeature(fid)
        if not feature.isValid():
            return
        if not feature.geometry() or feature.geometry().isEmpty():
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

        camada.changeAttributeValue(fid, index_perimetro, perimetro)
        camada.changeAttributeValue(fid, index_area, area)

    def configura_campos(self, camada):
        """
        Esta função configura os campos de uma camada.
        Ela adiciona campos para 'ID', 'Perimetro' e 'Area', e configura suas restrições e widgets.
        """
        id_field = QgsField("ID", QMetaType.Type.Int) # Cria um campo 'ID'
        perimetro_field = QgsField("Perimetro", QMetaType.Type.Double, "double", 20, 3)  # 20 dígitos, 3 decimais
        area_field = QgsField("Area", QMetaType.Type.Double, "double", 20, 3) # Cria um campo 'Area'

        constraints = QgsFieldConstraints() # Cria um novo objeto de restrições
        constraints.setConstraint(QgsFieldConstraints.Constraint.ConstraintUnique) # Define a restrição 'Unique'
        constraints.setConstraint( QgsFieldConstraints.Constraint.ConstraintNotNull) # Define a restrição 'NotNull'
        id_field.setConstraints(constraints) # Aplica as restrições ao campo 'ID'

        # Adiciona campos à camada
        camada.dataProvider().addAttributes([id_field, perimetro_field, area_field])
        camada.updateFields() # Atualiza os campos da camada

        idx_id = camada.fields().indexOf("ID")
        if idx_id != -1:
            expr = 'coalesce(maximum("ID"),0) + 1'
            camada.setDefaultValueDefinition(idx_id, QgsDefaultValue(expr))

        widget_setup_oculto = QgsEditorWidgetSetup("Hidden", {})

        idx_per = camada.fields().indexOf("Perimetro")
        if idx_per != -1:
            camada.setEditorWidgetSetup(idx_per, widget_setup_oculto)
            camada.setFieldAlias(idx_per, QCoreApplication.translate("CamadaPoligonosManager", "Perímetro"))

        idx_area = camada.fields().indexOf("Area")
        if idx_area != -1:
            camada.setEditorWidgetSetup(idx_area, widget_setup_oculto)
            camada.setFieldAlias(idx_area, QCoreApplication.translate("CamadaPoligonosManager", "Área"))

    def configura_etiquetas(self, camada: QgsVectorLayer):
        """
        Esta função configura as etiquetas de uma camada.
        Ela habilita as etiquetas, define o campo de etiqueta para 'ID' e configura o formato das etiquetas.
        """
        settings_etiqueta = QgsPalLayerSettings() # Cria um novo objeto de configurações de etiqueta
        settings_etiqueta.fieldName = "ID" # Define o campo de etiqueta para 'ID'
        settings_etiqueta.enabled = True # Habilita as etiquetas

        text_format = QgsTextFormat() # Cria um novo objeto de formato de texto
        text_format.setColor(QColor(0, 0, 255)) # Define a cor do texto para azul
        fonte_etiqueta = QFont("Arial", 14, QFont.Weight.Bold, True)  # Cria uma nova fonte para as etiquetas, negrito e itálico
        text_format.setFont(fonte_etiqueta) # Define a fonte das etiquetas

        background_settings = QgsTextBackgroundSettings() # Cria um novo objeto de configurações de fundo
        background_settings.setEnabled(True) # Habilita o fundo
        background_settings.setFillColor(QColor(255, 255, 255)) # Define a cor de preenchimento do fundo para branco
        text_format.setBackground(background_settings) 

        settings_etiqueta.setFormat(text_format) # Aplica o formato de texto às configurações de etiqueta
        camada.setLabelsEnabled(True) # Habilita as etiquetas na camada
        camada.setLabeling(QgsVectorLayerSimpleLabeling(settings_etiqueta)) # Aplica as configurações de etiqueta à camada