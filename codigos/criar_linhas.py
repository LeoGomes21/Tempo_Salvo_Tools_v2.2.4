from qgis.core import QgsField, QgsProject, QgsVectorLayer, QgsFieldConstraints, QgsEditorWidgetSetup, QgsPalLayerSettings, QgsTextFormat, QgsVectorLayerSimpleLabeling, QgsUnitTypes, QgsDistanceArea, QgsSingleSymbolRenderer, QgsCategorizedSymbolRenderer, QgsEditFormConfig, QgsDefaultValue, QgsExpression, QgsTextBackgroundSettings, QgsTextBufferSettings, QgsCoordinateReferenceSystem
from qgis.PyQt.QtGui import QFont, QColor
from qgis.PyQt.QtCore import QVariant, Qt, QSizeF, QMetaType, QTimer, QCoreApplication
import functools
import os

class CamadaLinhasManager:
    def __init__(self, iface):
        """
        :param iface: instância do QGIS Interface (iface)
        """
        self.iface = iface

        # evita reconectar sinais na mesma camada e evita acumular lixo
        self._conn_layers = set() # {layer_id}
        self._conn_slots = {}  # {layer_id: (slot_added, slot_geom)}

        # limpa caches quando layers forem removidas
        proj = QgsProject.instance()
        try:
            proj.layersWillBeRemoved.connect(self._on_layers_will_be_removed, Qt.ConnectionType.UniqueConnection)
        except TypeError:
            try:
                proj.layersWillBeRemoved.connect(self._on_layers_will_be_removed)
            except Exception:
                pass  # nosec B110

    def tr(self, message):
        """
        Traduz textos deste diálogo.
        O contexto precisa ser estável para o Qt Linguist encontrar as traduções.
        """
        return QCoreApplication.translate("CamadaLinhasManager", message)

    def conectar_sinais(self, camada: QgsVectorLayer):
        """Conecta sinais relevantes para atualizações automáticas na camada."""
        if not camada or not camada.isValid():
            return

        lid = camada.id()
        if lid in self._conn_layers:
            return

        slot_added = functools.partial(self._on_feature_added, camada)
        slot_geom  = functools.partial(self._on_geometry_changed, camada)

        camada.featureAdded.connect(slot_added)
        camada.geometryChanged.connect(slot_geom)

        self._conn_layers.add(lid)
        self._conn_slots[lid] = (slot_added, slot_geom)

    def _on_feature_added(self, camada: QgsVectorLayer, fid: int):
        self.atualizar_comprimento_linha(camada, fid, _retry=False)

    def _on_geometry_changed(self, camada: QgsVectorLayer, fid: int, geom):
        self.atualizar_comprimento_linha(camada, fid, _retry=False)

    def _on_layers_will_be_removed(self, layer_ids):
        try:
            ids = list(layer_ids)
        except Exception:
            ids = [layer_ids]

        for lid in ids:
            lid = str(lid)
            self._conn_layers.discard(lid)
            self._conn_slots.pop(lid, None)

    def criar_camada_linhas(self, nome_camada=None, cor: QColor = None, crs: str = None) -> QgsVectorLayer:
        """Cria e configura uma nova camada de linhas temporária, adicionando-a ao painel de camadas do QGIS."""
        proj = QgsProject.instance()

        # 1) CRS (robusto)
        if crs is None:
            crs = self.obter_crs_projeto_atual()

        # garante string tipo "EPSG:4326"
        try:
            crs_obj = QgsCoordinateReferenceSystem(crs)
            if not crs_obj.isValid():
                crs_obj = proj.crs()
            crs_authid = crs_obj.authid() or proj.crs().authid()
        except Exception:
            crs_authid = proj.crs().authid()

        # 2) Nome (sempre único, mesmo se usuário passar um já existente)
        base_nome = self.gerar_nome_camada(nome_camada)  # se None, gera "Linha Temp i"
        nome = base_nome
        if proj.mapLayersByName(nome):
            i = 1
            while proj.mapLayersByName(f"{base_nome}_{i}"):
                i += 1
            nome = f"{base_nome}_{i}"

        # 3) Criação base
        camada = self.criar_camada_vectorial(nome, crs_authid)
        if not camada or not camada.isValid():
            return None

        # 4) Campos + ocultação
        self.adicionar_campos(camada)
        self.configurar_campo_oculto(camada, "Comprimento")

        # 5) Renderer / cor opcional (antes do add ao projeto está ok)
        if cor is not None:
            renderer = camada.renderer()
            try:
                if isinstance(renderer, QgsSingleSymbolRenderer):
                    renderer.symbol().setColor(cor)
                elif isinstance(renderer, QgsCategorizedSymbolRenderer):
                    for cat in renderer.categories():
                        cat.symbol().setColor(cor)
            except Exception:
                pass  # nosec B110

        # 6) Adiciona no TOPO da lista (sem grupos)
        proj.addMapLayer(camada, False)                 # evita inserir automático
        proj.layerTreeRoot().insertLayer(0, camada)     # topo do root

        # 7) Garante edição e conecta sinais (na ordem certa para não perder eventos)
        if not camada.isEditable():
            camada.startEditing()
        self.conectar_sinais(camada)

        # 8) Ativa a camada e seleciona no painel
        self.iface.setActiveLayer(camada)
        try:
            self.iface.layerTreeView().setCurrentLayer(camada)
        except Exception:
            pass  # nosec B110

        # 9) Força a UI “assentar” a camada ativa antes de entrar no modo de desenho
        QCoreApplication.processEvents()

        # 10) Aciona ferramenta de adicionar feição (linha)
        action = self.iface.actionAddFeature()
        if action:
            action.trigger()

        # 11) Refresh leve
        try:
            camada.triggerRepaint()
            self.iface.mapCanvas().refresh()
        except Exception:
            pass  # nosec B110

        return camada

    def obter_crs_projeto_atual(self) -> str:
        """Obtém o Sistema de Referência de Coordenadas (SRC) do projeto atual."""
        return QgsProject.instance().crs().authid()

    def gerar_nome_camada(self, nome: str) -> str:
        """Gera um nome único para a camada se nenhum for fornecido."""
        if not nome:
            base = self.tr("Linhas Temporárias")
            i = 1
            while QgsProject.instance().mapLayersByName(f"{base} {i}"):
                i += 1
            return f"{base} {i}"
        return nome

    def criar_camada_vectorial(self, nome: str, crs: str) -> QgsVectorLayer:
        """Cria uma nova camada vectorial de linhas temporária."""
        uri = f"LineString?crs={crs}"
        return QgsVectorLayer(uri, nome, "memory")

    def adicionar_campos(self, camada: QgsVectorLayer):
        """Adiciona campos ID e Comprimento; ID é autoincremental."""
        id_field   = QgsField("ID", QMetaType.Type.Int)
        comp_field = QgsField("Comprimento", QMetaType.Type.Double, "double", 20, 3)

        camada.dataProvider().addAttributes([id_field, comp_field])
        camada.updateFields()

        idx_comp = camada.fields().indexOf("Comprimento")

        if idx_comp >= 0:
            camada.setFieldAlias(idx_comp,
                QCoreApplication.translate("CamadaLinhasManager", "Comprimento"))

        idx_id = camada.fields().indexOf("ID")
        if idx_id != -1:
            # constraints (quando disponível)
            try:
                camada.setFieldConstraint(idx_id, QgsFieldConstraints.Constraint.ConstraintNotNull, QgsFieldConstraints.ConstraintStrength.ConstraintStrengthHard)
                camada.setFieldConstraint(idx_id, QgsFieldConstraints.Constraint.ConstraintUnique, QgsFieldConstraints.ConstraintStrength.ConstraintStrengthHard)
            except Exception:
                pass  # nosec B110

            # Default: max(ID) + 1 (robusto). Fallback se parser não aceitar.
            expr1 = "coalesce(aggregate(@layer,'max',\"ID\"),0) + 1"
            expr2 = "coalesce(maximum(\"ID\"),0) + 1"

            e1 = QgsExpression(expr1)
            expr = expr1 if not e1.hasParserError() else expr2

            camada.setDefaultValueDefinition(idx_id, QgsDefaultValue(expr))

    def constraints_com_incremente(self) -> QgsFieldConstraints:
        """Define restrições para o campo de incremento."""
        c = QgsFieldConstraints()
        c.setConstraint(QgsFieldConstraints.Constraint.ConstraintUnique)
        c.setConstraint(QgsFieldConstraints.Constraint.ConstraintNotNull)
        return c

    def configurar_campo_oculto(self, camada: QgsVectorLayer, nome_campo: str):
        """Configura um campo da camada para ser oculto na interface."""
        idx = camada.fields().indexOf(nome_campo)
        if idx == -1:
            return
        setup = QgsEditorWidgetSetup("Hidden", {})
        camada.setEditorWidgetSetup(idx, setup)

    def atualizar_comprimento_linha(self, camada: QgsVectorLayer, fid: int, _retry: bool = False):
        """Atualiza o comprimento da linha adicionada e configura etiquetas."""
        if not camada or not camada.isValid():
            return

        idx = camada.fields().indexOf("Comprimento")
        if idx == -1:
            return

        # se não estiver em edição, não tenta gravar atributo
        if not camada.isEditable():
            return

        feat = camada.getFeature(fid)
        if (not feat) or (not feat.hasGeometry()) or feat.geometry().isEmpty():
            # primeira feição recém-criada pode ainda não ter geometria no featureAdded
            if not _retry:
                QTimer.singleShot(0, lambda: self.atualizar_comprimento_linha(camada, fid, _retry=True))
            return

        geom = feat.geometry()

        # mede
        if camada.crs().isGeographic():
            project = QgsProject.instance()
            medida = QgsDistanceArea()
            medida.setSourceCrs(camada.crs(), project.transformContext())
            try:
                ell = project.ellipsoid()  # quando disponível
            except Exception:
                ell = project.crs().ellipsoidAcronym()
            if ell:
                medida.setEllipsoid(ell)
            comp = round(medida.measureLength(geom), 3)
        else:
            comp = round(geom.length(), 3)

        camada.changeAttributeValue(fid, idx, comp)

        # Reaplica etiquetas quando necessário (ex.: você mudou o estilo no código)
        STYLE_V = 2  # aumente este número quando mudar o estilo do rótulo
        if camada.customProperty("etiquetas_style_v", 0) != STYLE_V:
            self.configurar_etiquetas(camada)
            camada.setCustomProperty("etiquetas_style_v", STYLE_V)

        camada.triggerRepaint()

    def configurar_etiquetas(self, camada: QgsVectorLayer):
        """Configura as etiquetas para a camada."""
        labels = QgsPalLayerSettings()
        labels.enabled = True

        # 🔒 Segurança: se por algum motivo o ID vier vazio, ao menos mostra $id
        labels.fieldName = 'coalesce("ID", $id)'
        labels.isExpression = True

        labels.setFormat(self.formato_texto_etiqueta())

        geom = camada.geometryType()  # 0=point, 1=line, 2=polygon

        # placement conforme geometria (principalmente linhas)
        try:
            if hasattr(QgsPalLayerSettings, "Placement"):
                P = QgsPalLayerSettings.Placement
                if geom == 1:  # LineGeometry
                    labels.placement = getattr(P, "Line", getattr(P, "Curved", P.OverPoint))
                else:
                    labels.placement = P.OverPoint
            else:
                if geom == 1 and hasattr(QgsPalLayerSettings, "Line"):
                    labels.placement = QgsPalLayerSettings.Placement.Line
                else:
                    labels.placement = QgsPalLayerSettings.Placement.OverPoint
        except Exception:
            # fallback seguro
            try:
                labels.placement = QgsPalLayerSettings.Placement.OverPoint
            except Exception:
                pass  # nosec B110

        camada.setLabeling(QgsVectorLayerSimpleLabeling(labels))
        camada.setLabelsEnabled(True)
        camada.triggerRepaint()

    def formato_texto_etiqueta(self) -> QgsTextFormat:
        """Formato do rótulo com fundo branco bem colado ao texto e fonte maior."""
        fmt = QgsTextFormat()

        # Rótulo maior
        font = QFont("Arial")
        font.setBold(True)
        font.setItalic(False)
        fmt.setFont(font)
        fmt.setSize(10)  # antes 12; ajuste para 13/14/15 conforme seu gosto

        fmt.setColor(QColor("blue"))

        # Desliga buffer (halo)
        buf = QgsTextBufferSettings()
        buf.setEnabled(False)
        fmt.setBuffer(buf)

        # Fundo branco "colado" no texto
        bg = QgsTextBackgroundSettings()
        bg.setEnabled(True)

        if hasattr(QgsTextBackgroundSettings, "ShapeRectangle"):
            bg.setType(QgsTextBackgroundSettings.ShapeType.ShapeRectangle)

        bg.setFillColor(QColor("white"))
        bg.setStrokeColor(QColor("white"))
        bg.setStrokeWidth(0)  # sem borda, sem “inflar” o retângulo

        # Padding mínimo
        if hasattr(bg, "setSizeType") and hasattr(QgsTextBackgroundSettings, "SizeBuffer"):
            bg.setSizeType(QgsTextBackgroundSettings.SizeType.SizeBuffer)

        if hasattr(bg, "setSize"):
            # quanto menor, mais colado (tente 0.8 / 0.6 se ainda estiver largo)
            bg.setSize(QSizeF(0.0, 0.0))

        fmt.setBackground(bg)
        return fmt