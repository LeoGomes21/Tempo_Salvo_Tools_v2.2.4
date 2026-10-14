from qgis.core import (QgsField, QgsProject, QgsVectorLayer, QgsWkbTypes, QgsFieldConstraints, QgsEditorWidgetSetup,
                       QgsTextFormat, QgsTextBufferSettings,
                       QgsVectorLayerSimpleLabeling, QgsPalLayerSettings,
                       QgsTextBackgroundSettings, QgsDefaultValue, QgsCoordinateReferenceSystem, QgsEditFormConfig)
from qgis.PyQt.QtGui import QFont, QColor
from qgis.PyQt.QtCore import QVariant, QMetaType, QCoreApplication

class CamadaPontosManager:
    """
    Cria e gerencia camadas temporárias de pontos, atualizando campos X/Y
    (e DMS, se o CRS for geográfico) e rótulos de ID automaticamente.
    """
    def __init__(self, iface):
        self.iface = iface
        self._conns = {}  # {layer_id: {"added": func, "geom": func}}

        # Desconecta quando a camada for removida do projeto
        QgsProject.instance().layerWillBeRemoved.connect(self._on_layer_will_be_removed)

    def tr(self, message):
        """
        Traduz textos deste diálogo.
        O contexto precisa ser estável para o Qt Linguist encontrar as traduções.
        """
        return QCoreApplication.translate("UiManager", message)

    def _on_layer_will_be_removed(self, layer_id: str):
        """
        Desconecta com segurança os sinais associados a uma camada que está
        prestes a ser removida do projeto.

        Objetivo:
        - Evitar callbacks dispararem depois que a camada foi destruída,
          prevenindo erros do tipo "wrapped C/C++ object ... has been deleted".
        """
        conns = self._conns.pop(layer_id, None)  # remove e recupera as conexões guardadas
        if not conns:
            return  # nada para desconectar

        lyr = QgsProject.instance().mapLayer(layer_id)  # tenta pegar a camada ainda viva
        if not lyr:
            return  # já não existe no projeto (ou já foi destruída)

        # Desconecta o sinal featureAdded (se ainda estiver conectado)
        try:
            lyr.featureAdded.disconnect(conns["added"])
        except Exception:
            pass  # nosec B110

        # Desconecta o sinal geometryChanged (se ainda estiver conectado)
        try:
            lyr.geometryChanged.disconnect(conns["geom"])
        except Exception:
            pass  # nosec B110

    def _conectar_sinais(self, camada: QgsVectorLayer, is_geografico: bool):
        """
        Conecta os sinais da camada para manter X/Y (e DMS) atualizados.

        Estratégia:
        - Guarda callbacks nomeados (não usa lambda) para permitir disconnect depois.
        - Usa o layer_id e re-resolve a camada via QgsProject para evitar ponteiros
          inválidos caso a camada seja removida.
        - Evita conexões duplicadas se por acaso este método for chamado duas vezes
          para a mesma camada.
        """
        layer_id = camada.id()  # ID único da camada no projeto

        def on_added(fid, lid=layer_id, geo=is_geografico):
            # Re-resolve a camada pelo ID (evita usar referência morta)
            lyr = QgsProject.instance().mapLayer(lid)
            if not isinstance(lyr, QgsVectorLayer) or not lyr.isValid():
                return
            self._atualizar_valores_ponto(lyr, fid, geo)  # atualiza X/Y/DMS ao adicionar

        def on_geom(fid, _geom, lid=layer_id, geo=is_geografico):
            # Re-resolve a camada pelo ID (evita usar referência morta)
            lyr = QgsProject.instance().mapLayer(lid)
            if not isinstance(lyr, QgsVectorLayer) or not lyr.isValid():
                return
            self._atualizar_valores_ponto(lyr, fid, geo) # atualiza X/Y/DMS ao mover/editar

        # Evita conexão duplicada se alguém chamar isso duas vezes para a mesma layer
        if layer_id in self._conns:
            self._on_layer_will_be_removed(layer_id) # desconecta antes de reconectar

        # Conecta sinais principais de edição
        camada.featureAdded.connect(on_added) # disparado quando cria ponto novo
        camada.geometryChanged.connect(on_geom) # disparado quando altera geometria

        # Guarda callbacks para permitir desconectar depois
        self._conns[layer_id] = {"added": on_added, "geom": on_geom}

    def criar_camada_pontos(self, nome_camada: str | None = None, cor_preenchimento: QColor | None = None, cor_borda: QColor | None = None, crs=None):
        """
        Cria uma camada temporária de pontos em memória.

        Parâmetros:
        - nome_camada: nome opcional da camada;
        - cor: QColor opcional para o símbolo dos pontos;
        - crs: QgsCoordinateReferenceSystem, string EPSG ou None.

        Se a cor ou o SRC não forem informados, utiliza os padrões
        do QGIS e do projeto atual.
        """
        projeto = QgsProject.instance()

        # Define o SRC da camada
        if isinstance(crs, QgsCoordinateReferenceSystem):
            crs_camada = QgsCoordinateReferenceSystem(crs)

        elif crs:
            crs_camada = QgsCoordinateReferenceSystem(str(crs))

        else:
            crs_camada = projeto.crs()

        # Fallback caso o SRC informado seja inválido
        if not crs_camada.isValid():
            crs_camada = projeto.crs()

        is_geografico = crs_camada.isGeographic()

        # Define um nome válido e único
        if nome_camada and nome_camada.strip():
            nome_base = nome_camada.strip()
            nome_final = nome_base

            contador = 1
            while projeto.mapLayersByName(nome_final):
                nome_final = f"{nome_base}_{contador}"
                contador += 1

            nome_camada = nome_final

        else:
            nome_camada = self._gera_nome_camada(self.tr("Pontos Temporários"))

        # Cria a camada
        authid = crs_camada.authid()

        if authid:
            vl = QgsVectorLayer(
                f"Point?crs={authid}",
                nome_camada,
                "memory")
        else:
            # Compatibilidade com SRC personalizado sem AUTHID
            vl = QgsVectorLayer(
                "Point",
                nome_camada,
                "memory")

            if vl.isValid():
                vl.setCrs(crs_camada)

        if not vl.isValid():
            return None

        # Configura campos, etiquetas e sinais
        self._configura_campos(vl, is_geografico)

        self._configura_etiquetas(vl)

        self._conectar_sinais(
            vl,
            is_geografico)

        # Aplica as cores opcionais de preenchimento e borda
        try:
            renderer = vl.renderer()
            symbol = renderer.symbol() if renderer is not None else None

            if symbol is not None:
                for i in range(symbol.symbolLayerCount()):
                    symbol_layer = symbol.symbolLayer(i)

                    # Cor de preenchimento
                    if (isinstance(cor_preenchimento, QColor)
                        and cor_preenchimento.isValid()):
                        try:
                            symbol_layer.setColor(QColor(cor_preenchimento))
                        except Exception:
                            try:
                                symbol_layer.setFillColor( QColor(cor_preenchimento))
                            except Exception:
                                pass  # nosec B110

                    # Cor da borda
                    if (isinstance(cor_borda, QColor)
                        and cor_borda.isValid()):
                        try:
                            symbol_layer.setStrokeColor(QColor(cor_borda))
                        except Exception:
                            try:
                                symbol_layer.setOutlineColor(QColor(cor_borda))
                            except Exception:
                                pass  # nosec B110

                vl.triggerRepaint()

        except Exception:
            pass  # nosec B110

        # Adiciona a camada no topo
        projeto.addMapLayer(vl, False)

        projeto.layerTreeRoot().insertLayer(0, vl)

        # Ativa edição e seleciona a camada
        if not vl.isEditable():
            vl.startEditing()

        try:
            self.iface.setActiveLayer(vl)
            self.iface.layerTreeView().setCurrentLayer(vl)
        except Exception:
            pass  # nosec B110

        # A ferramenta Adicionar Ponto será ativada pelo UiManagerT,
        # depois que o diálogo de nome/cor/SRC for fechado.

        return vl

    def _gera_nome_camada(self, nome_base: str) -> str:
        """
        Gera um nome de camada único baseado em um nome base.

        Esta rotina realiza os seguintes passos:
        1. Inicializa um contador em 1.
        2. Constrói o nome da camada concatenando o nome base e o contador.
        3. Enquanto já existir alguma camada no projeto com o mesmo nome:
           a. Incrementa o contador em 1.
           b. Reconstrói o nome usando o novo contador.
        4. Retorna o nome que não conflita com nenhuma camada existente.

        :param nome_base: Texto inicial para a camada (sem número).
        :return:         Nome único, ex.: "Ponto Temp 1", "Ponto Temp 2", etc.
        """
        contador = 1                                           # começa a contagem em 1
        nome = f"{nome_base} {contador}"                       # monta o primeiro nome
        # verifica se já existe camada com este nome
        while QgsProject.instance().mapLayersByName(nome):
            contador += 1                                      # incrementa contador
            nome = f"{nome_base} {contador}"                   # atualiza nome com novo número
        return nome                                             # devolve o nome único

    def _configura_campos(self, camada: QgsVectorLayer, is_geografico: bool):
        """
        Cria e configura os campos da camada de pontos.

        - Adiciona os campos: ID (int), X/Y (double) com precisão dinâmica.
        - Se o CRS for geográfico, adiciona também X_DMS e Y_DMS (texto).
        - Aplica restrições no ID (único e não-nulo) e define autoincremento.
        - Oculta os campos de coordenadas na interface de edição para manter a UI limpa.
        """
        # Precisão: 6 casas em geográfico (lat/long), 3 em projetado (metros)
        prec_xy = 6 if is_geografico else 3

        # Campo inteiro de identificação
        id_field = QgsField("ID", QMetaType.Type.Int)

        # Campos numéricos de coordenadas com precisão conforme o CRS
        x_field = QgsField("X", QMetaType.Type.Double, "double", 20, prec_xy)  # X com precisão dinâmica
        y_field = QgsField("Y", QMetaType.Type.Double, "double", 20, prec_xy)  # Y com precisão dinâmica

        # Restrições do campo ID: único e obrigatório
        cons = QgsFieldConstraints()
        cons.setConstraint(QgsFieldConstraints.Constraint.ConstraintUnique)   # impede IDs duplicados
        cons.setConstraint(QgsFieldConstraints.Constraint.ConstraintNotNull)  # impede ID vazio
        id_field.setConstraints(cons)                              # aplica restrições no campo

        # Lista base de campos
        campos = [id_field, x_field, y_field]

        # Se CRS geográfico, adiciona campos DMS (texto)
        if is_geografico:
            campos += [
                QgsField("X_GMS", QMetaType.Type.QString, len=20),  # longitude em DMS
                QgsField("Y_GMS", QMetaType.Type.QString, len=20)]   # latitude em DMS

        # Adiciona campos no provider e atualiza metadados da camada
        camada.dataProvider().addAttributes(campos)  # efetiva criação dos campos
        camada.updateFields()                        # atualiza lista de campos na camada

        # Define autoincremento do ID (máximo atual + 1)
        idx_id = camada.fields().indexOf("ID")       # índice do campo ID
        expr = 'coalesce(maximum("ID"),0) + 1'       # expressão de incremento
        camada.setDefaultValueDefinition(idx_id, QgsDefaultValue(expr))  # aplica default

        # Oculta campos de coordenadas na UI (o usuário normalmente não precisa editar manualmente)
        hidden = QgsEditorWidgetSetup("Hidden", {})
        for nome in ("X", "Y", "X_GMS", "Y_GMS"):
            idx = camada.fields().indexOf(nome)      # índice do campo
            if idx != -1:
                camada.setEditorWidgetSetup(idx, hidden)  # esconde o campo no formulário

    def _configura_etiquetas(self, camada: QgsVectorLayer):
        """
        Configura o rótulo de feição para o campo "ID", aplicando:
        1. Ativação do label layer-wide.
        2. Uso do campo "ID" como fonte do texto.
        3. Cor do texto em azul (RGB 0,0,255).
        4. Fonte Arial tamanho 12.
        5. Fundo branco para o texto (para melhorar legibilidade).
        6. Aplica as definições ao provedor de labels da camada.
        
        :param camada: Instância de QgsVectorLayer que receberá as configurações de label.
        """
        pal = QgsPalLayerSettings()                                # cria objeto de configurações de label
        pal.fieldName = "ID"                                       # define o campo que alimenta o texto
        pal.enabled = True                                         # habilita rótulos para esta camada

        fmt = QgsTextFormat()                                      # objeto para formatar o texto
        fmt.setColor(QColor(0, 0, 255))                            # define a cor do texto como azul
        fmt.setFont(QFont("Arial", 12))                            # define a fonte e o tamanho do texto

        bg = QgsTextBackgroundSettings()                           # configurações de fundo do texto
        bg.setEnabled(True)                                        # ativa o fundo
        bg.setFillColor(QColor(255, 255, 255))                     # cor de preenchimento do fundo: branco
        fmt.setBackground(bg)                                      # associa o fundo à formatação de texto

        pal.setFormat(fmt)                                         # aplica o formato ao objeto de settings
        camada.setLabelsEnabled(True)                              # habilita labels na camada (global)
        camada.setLabeling(QgsVectorLayerSimpleLabeling(pal))      # define o esquema de labeling na camada

    def _atualizar_valores_ponto(self, camada: QgsVectorLayer, fid: int, is_geografico: bool):
        """
        Atualiza automaticamente os atributos de coordenadas (X/Y) de uma feição de ponto
        sempre que ela é criada ou tem sua geometria alterada.

        - Grava X e Y arredondados (6 casas em CRS geográfico, 3 em CRS projetado).
        - Se o CRS for geográfico, também atualiza X_DMS e Y_DMS (graus/min/seg).
        - Faz validações para evitar erros quando a camada/feição/geometria não estão prontas.
        """
        # Segurança: camada precisa existir e estar válida
        if not camada or not camada.isValid():
            return

        # Só altera atributos se a camada estiver em modo de edição
        if not camada.isEditable():
            return

        # Busca índices dos campos X/Y (se não existirem, aborta)
        idx_x = camada.fields().indexOf("X")  # índice do campo X
        idx_y = camada.fields().indexOf("Y")  # índice do campo Y
        if idx_x < 0 or idx_y < 0:
            return

        # Recupera a feição pelo fid e valida
        feat = camada.getFeature(fid)  # obtém a feição alvo
        if not (feat and feat.isValid()):
            return

        # Valida geometria
        geom = feat.geometry()  # pega a geometria atual da feição
        if not geom or geom.isEmpty():
            return

        # Pega um ponto "seguro": suporta point e multipoint
        try:
            if geom.isMultipart():  # caso multiponto
                pts = geom.asMultiPoint()
                if not pts:
                    return
                pt = pts[0]  # usa o primeiro ponto
            else:
                pt = geom.asPoint()  # ponto simples
        except Exception:
            return

        # Define precisão: geográfico precisa de mais casas decimais
        casas = 6 if is_geografico else 3
        x_val = round(pt.x(), casas)  # arredonda X
        y_val = round(pt.y(), casas)  # arredonda Y

        # Atualiza atributos X/Y
        camada.changeAttributeValue(fid, idx_x, x_val)  # grava X
        camada.changeAttributeValue(fid, idx_y, y_val)  # grava Y

        # Se CRS for geográfico, também atualiza DMS (se os campos existirem)
        if is_geografico:
            idx_xd = camada.fields().indexOf("X_GMS") # índice do campo X_GMS
            idx_yd = camada.fields().indexOf("Y_GMS") # índice do campo Y_GMS

            if idx_xd >= 0:
                camada.changeAttributeValue(fid, idx_xd, self._dec_to_dms(pt.x()))  # grava longitude em DMS
            if idx_yd >= 0:
                camada.changeAttributeValue(fid, idx_yd, self._dec_to_dms(pt.y()))  # grava latitude em DMS

    @staticmethod
    def _dec_to_dms(valor: float) -> str:
        """
        Converte coordenada decimal em string de graus, minutos e segundos (DMS).

        Passos realizados:
        1. Determina o sinal (“–” se negativo, vazio se positivo).
        2. Trabalha com o valor absoluto para cálculo de graus, minutos e segundos.
        3. Extrai a parte inteira como graus.
        4. Converte a parte decimal em minutos.
        5. Converte o restante em segundos.
        6. Formata o resultado como "SINALgraus° minutos' segundos\"".

        :param valor: Valor decimal da coordenada (positivo ou negativo).
        :return:      Representação DMS, ex.: "-23° 33' 45.67\""
        """
        sinal = "-" if valor < 0 else "" # 1) define sinal conforme valor
        valor = abs(valor) # 2) usa valor absoluto para cálculos
        graus = int(valor) # 3) parte inteira → graus
        minutos = int((valor - graus) * 60) # 4) parte decimal × 60 → minutos
        segundos = (valor - graus - minutos / 60) * 3600 # 5) restante × 3600 → segundos
        return f"{sinal}{graus}° {minutos}' {segundos:.2f}\"" # 6) formata string DMS

