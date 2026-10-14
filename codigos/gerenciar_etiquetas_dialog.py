from qgis.core import QgsPalLayerSettings, QgsVectorLayerSimpleLabeling, QgsTextFormat, QgsTextBufferSettings, Qgis, QgsWkbTypes, QgsExpression
from qgis.PyQt.QtWidgets import QDialog, QVBoxLayout, QScrollArea, QSizePolicy, QWidget, QHBoxLayout, QCheckBox, QPushButton, QColorDialog
from qgis.PyQt.QtGui import QColor
from qgis.PyQt.QtCore import Qt, QCoreApplication
import functools

class GerenciarEtiquetasDialog(QDialog):
    """
    Esta classe cria um diálogo para gerenciar as etiquetas de uma camada no QGIS, oferecendo funcionalidades para selecionar campos, ajustar suas cores e definir a visibilidade das etiquetas.

    Atributos:
    - layer: Referência à camada do QGIS para a qual as configurações de etiquetas serão aplicadas.
    - fieldColors: Um dicionário que mapeia os nomes dos campos às suas cores selecionadas para a etiqueta.
    - fieldVisibility: Um dicionário que mapeia os nomes dos campos à sua visibilidade (True para visível, False para oculto).
    - iface: Uma referência à interface do QGIS, permitindo interações com o ambiente do QGIS.

    Processo:
    1. Inicializa o diálogo com os valores padrão e configurações recebidas.
    2. Configura a interface do usuário chamando `setupUi`, que constrói todos os elementos gráficos necessários.
    3. Define os tamanhos mínimo e máximo do diálogo para garantir uma apresentação adequada dos elementos da interface.
    
    Detalhes:
    - A janela do diálogo é intitulada "Selecionar Campos para Etiquetas", refletindo seu propósito de permitir a seleção e personalização das etiquetas da camada.
    - A interface do diálogo é construída para ser intuitiva, com checkboxes para a seleção de campos e botões para a escolha de cores, facilitando a personalização das etiquetas pelo usuário.
    """
    def __init__(self, layer, fieldColors, fieldVisibility, iface, parent=None):
        super().__init__(parent)
        self.layer = layer  # A camada do QGIS que será manipulada
        self.fieldColors = fieldColors # Mapeamento dos campos para suas cores de etiqueta
        self.fieldVisibility = fieldVisibility # Mapeamento dos campos para a visibilidade da etiqueta
        self.iface = iface # Interface do QGIS para interações com o ambiente
        self.setWindowTitle(self.tr("Selecionar Campos para Etiquetas"))
        self.setupUi() # Chama a função para configurar a interface do usuário
        self.setMinimumSize(225, 150)  # Define o tamanho mínimo do diálogo para 600x400
        self.setMaximumSize(400, 300)  # Define o tamanho máximo do diálogo
        self.update_buttons_state()

    def tr(self, message):
        """
        Traduz textos deste diálogo.
        O contexto precisa ser estável para o Qt Linguist encontrar as traduções.
        """
        return QCoreApplication.translate("GerenciarEtiquetasDialog", message)

    def setupUi(self):
        """
        Esta função configura a interface do usuário para um diálogo personalizado de configuração de etiquetas em camadas GIS.
        Ela faz o seguinte:
        1. Cria um layout vertical principal para organizar os widgets.
        2. Adiciona uma área de rolagem (QScrollArea) ao layout para acomodar muitos campos.
        3. Configura um container dentro da área de rolagem para conter todos os widgets de configuração de campo.
        4. Itera sobre todos os campos da camada, criando um layout horizontal para cada campo com um checkbox e um botão de seleção de cor.
        5. Mapeia o estado do checkbox ao botão de seleção de cor, habilitando-o somente se o checkbox estiver marcado.
        6. Adiciona botões para aplicar configurações de etiqueta HTML ou Simples.
        """
        layout = QVBoxLayout(self) # Cria um layout vertical para organizar os elementos da UI

        # Cria uma QScrollArea
        scrollArea = QScrollArea(self)
        scrollArea.setWidgetResizable(True)

        # Pode ajustar o tamanho da QScrollArea conforme necessário, ou deixá-la expansível
        scrollArea.setSizePolicy(QSizePolicy.Policy.Expanding, QSizePolicy.Policy.Expanding)

        container = QWidget() # Widget que conterá todos os campos e botões
        containerLayout = QVBoxLayout(container) # Define o layout do contêiner como vertical.

        self.fieldColorMapping = {} # Dicionário para mapear os campos aos seus respectivos widgets de UI
        
        # Itera sobre os campos da camada, criando widgets para cada um
        for field in self.layer.fields():
            field_name = field.name()

            fieldLayout = QHBoxLayout()
            checkBox = QCheckBox(field_name)

            # Visibilidade inicial (vem do dict local do diálogo)
            checkBox.setChecked(bool(self.fieldVisibility.get(field_name, False)))
            checkBox.stateChanged.connect(self.update_buttons_state)

            fieldLayout.addWidget(checkBox)

            colorButton = QPushButton(self.tr("Cor"))
            colorButton.setEnabled(checkBox.isChecked())

            checkBox.stateChanged.connect(functools.partial(self.toggle_color_button, checkBox=checkBox, colorButton=colorButton))
            colorButton.clicked.connect(functools.partial(self.abrir_seletor_de_cor, fieldName=field_name, colorButton=colorButton))

            # Cor inicial (vem do dict local do diálogo)
            colorName = self.fieldColors.get(field_name)
            if colorName:
                qcol = QColor(colorName)
                if qcol.isValid():
                    colorButton.setStyleSheet(f"background-color: {qcol.name()};")
                    colorButton.color = qcol

            fieldLayout.addWidget(colorButton)

            self.fieldColorMapping[field_name] = (checkBox, colorButton)
            containerLayout.addLayout(fieldLayout)

        scrollArea.setWidget(container) # Define o container como o widget da QScrollArea
        layout.addWidget(scrollArea) # Adiciona a QScrollArea ao layout principal

        # Cria e configura botões para aplicação de etiquetas HTML ou Simples
        buttonsLayout = QHBoxLayout()
        self.btnHtml = QPushButton(self.tr("HTML"))
        self.btnSimples = QPushButton(self.tr("Simples"))
        self.btnSimples.clicked.connect(self.on_btn_simples_clicked) # Conecta ao slot para config simples
        self.btnHtml.clicked.connect(self.on_btn_html_clicked) # Conecta ao slot para configuração HTML
        buttonsLayout.addWidget(self.btnHtml)
        buttonsLayout.addWidget(self.btnSimples)
        layout.addLayout(buttonsLayout)

        # Botão "Cancelar" abaixo dos outros
        btnCancelar = QPushButton(self.tr("Cancelar"))
        btnCancelar.clicked.connect(self.reject)
        layout.addWidget(btnCancelar)
        
        self.setLayout(layout)
        self.update_buttons_state()  # Atualiza o estado dos botões ao iniciar

    def update_buttons_state(self):
        """
        Atualiza o estado dos botões "HTML" e "Simples" com base na seleção dos checkboxes.
        
        Processo:
        - Verifica se algum checkbox está selecionado.
        - Habilita ou desabilita os botões "HTML" e "Simples" dependendo da seleção.
        """
        # Verifica se há algum checkbox selecionado para habilitar ou desabilitar os botões.
        any_checked = any(checkBox.isChecked() for checkBox, _ in self.fieldColorMapping.values())
        
        # Habilita ou desabilita o botão "HTML" com base na variável 'any_checked'.
        self.btnHtml.setEnabled(any_checked)
        
        # Habilita ou desabilita o botão "Simples" com base na variável 'any_checked'.
        self.btnSimples.setEnabled(any_checked)

    def abrir_seletor_de_cor(self, fieldName, colorButton):
        """
        Abre um diálogo de seleção de cor para o usuário escolher uma cor, e aplica essa cor ao botão de cor correspondente a um campo da camada.
        """
        color = QColorDialog.getColor(parent=self)
        if not color.isValid():
            return

        colorName = color.name()  # padrão #RRGGBB (estável e compatível)
        colorButton.setStyleSheet(f"""
            background-color: {colorName};
            border: 1px solid {colorName};
            border-radius: 5px;
            width: 50px;
            height: 20px;
            text-align: center;
        """)
        colorButton.color = color

        # Atualiza apenas o dict local do diálogo
        self.fieldColors[fieldName] = colorName

    def toggle_color_button(self, state, checkBox, colorButton):
        """
        Alterna a habilitação do botão de seleção de cor com base no estado de uma caixa de seleção associada e atualiza o dicionário de visibilidade de campos.

        Processo:
        1. Habilita ou desabilita o botão de seleção de cor com base no estado da caixa de seleção (marcada ou não).
        2. Obtém o nome do campo a partir do texto da caixa de seleção.
        3. Atualiza o dicionário `fieldVisibility`, registrando o estado atual (marcado ou não) da caixa de seleção para o campo correspondente.

        Parâmetros:
        - state: O estado atual da caixa de seleção (Qt.Checked se estiver marcada).
        - checkBox: A caixa de seleção que determina a habilitação do botão de cor.
        - colorButton: O botão de seleção de cor cuja habilitação é controlada pela caixa de seleção.
        """
        # 1. Habilita o botão de seleção de cor se a caixa de seleção estiver marcada, caso contrário, desabilita.
        colorButton.setEnabled(state == Qt.CheckState.Checked)
        fieldName = checkBox.text() # 2. Obtém o nome do campo a partir do texto da caixa de seleção.
        # 3. Atualiza o dicionário `fieldVisibility`, definindo o estado de visibilidade do campo com base no estado da caixa de seleção.
        self.fieldVisibility[fieldName] = checkBox.isChecked()
        self.update_checkboxes()  # Atualiza a habilitação dos checkboxes cada vez que um é marcado ou desmarcado.

    def update_checkboxes(self):
        """
        Atualiza a habilitação das caixas de seleção com base no número total de caixas marcadas, limitando o número máximo de caixas que podem ser marcadas simultaneamente.

        Processo:
        - Calcula o número total de caixas de seleção marcadas.
        - Percorre todas as caixas de seleção.
        - Desabilita caixas de seleção não marcadas se o limite de caixas marcadas for atingido; caso contrário, todas as caixas de seleção permanecem habilitadas.

        Detalhes:
        - O limite máximo de caixas de seleção que podem ser marcadas simultaneamente é definido como 5.
        - As caixas de seleção marcadas permanecem sempre habilitadas, garantindo que o usuário possa desmarcar uma opção caso deseje selecionar outra.
        """
        # Conta o número total de caixas de seleção que estão atualmente marcadas.
        selected_count = sum(1 for checkBox, _ in self.fieldColorMapping.values() if checkBox.isChecked())

        # Itera sobre cada caixa de seleção e seu respectivo botão de cor no mapeamento.
        for fieldName, (checkBox, colorButton) in self.fieldColorMapping.items():
            # Habilita a caixa de seleção se menos de 5 estiverem marcadas ou se a própria caixa já estiver marcada; 
            checkBox.setEnabled(selected_count < 5 or checkBox.isChecked())

            # Isso garante que o botão de cor só possa ser interagido quando o checkbox está marcado.
            colorButton.setEnabled(checkBox.isChecked())

    def on_btn_simples_clicked(self):
        """
        Manipula o evento de clique no botão "Simples", iniciando o processo de reconfiguração das etiquetas da camada para um formato de exibição simples.

        Processo:
        1. Chama a função `reconfigurar_etiquetas_simples` para ajustar a configuração das etiquetas da camada selecionada.

        Detalhes:
        - Este manipulador de eventos é vinculado ao botão "Simples" na interface do usuário.
        - Ao ser acionado, inicia o processo de ajuste das etiquetas de acordo com os campos selecionados e as preferências de cores definidas pelo usuário, se aplicável.
        - O ajuste é feito para simplificar a visualização das etiquetas, focando na exibição dos valores dos campos sem formatação HTML avançada.
        """
        # Chama a função que reconfigura as etiquetas para o modo simples.
        self.reconfigurar_etiquetas_simples()

    def on_btn_html_clicked(self):
        """
        Este método é chamado quando o usuário clica no botão "HTML". Ele inicia o processo de reconfiguração das etiquetas da camada para usar formatação HTML, permitindo um estilo mais complexo e visualmente atraente nas etiquetas.

        Processo:
        1. Invoca a função `reconfigurar_etiquetas_HTML` que ajusta as configurações de etiquetas da camada selecionada para utilizar expressões HTML.
        
        Detalhes:
        - Este método é conectado ao evento de clique no botão "HTML" na interface gráfica do usuário.
        - A função `reconfigurar_etiquetas_HTML` é projetada para permitir que informações adicionais e estilos personalizados sejam aplicados às etiquetas, usando a linguagem de marcação HTML.
        - Isso possibilita a inclusão de cores, tamanhos de fonte variados, e outras customizações visuais que melhoram a apresentação dos dados na camada.
        """
        # Chama a função que configura as etiquetas da camada para usar expressões HTML,
        self.reconfigurar_etiquetas_HTML()

    def _aplicar_posicionamento_por_geometria(self, settings: QgsPalLayerSettings):
        """
        Define placement conforme geometria:
        - Ponto: OffsetFromPoint + Quadrant AboveRight (canto superior direito)
        - Linha: Line/Curved
        - Polígono: OverPoint (fallback)
        """
        geom = self.layer.geometryType()  # 0=Point, 1=Line, 2=Polygon

        # PONTOS: canto superior direito
        if geom == 0:
            # placement
            if hasattr(QgsPalLayerSettings, "Placement"):
                P = QgsPalLayerSettings.Placement
                settings.placement = getattr(P, "OffsetFromPoint", getattr(P, "AroundPoint", P.OverPoint))
            else:
                settings.placement = getattr(QgsPalLayerSettings, "OffsetFromPoint", QgsPalLayerSettings.Placement.OverPoint)

            # quadrante superior direito
            if hasattr(QgsPalLayerSettings, "QuadrantPosition"):
                settings.quadOffset = QgsPalLayerSettings.QuadrantPosition.AboveRight
            else:
                # fallback para versões antigas (se existir)
                settings.quadOffset = getattr(QgsPalLayerSettings, "AboveRight", 0)

            # offsets (em mm) bem colados ao ponto
            try:
                settings.xOffset = 0.0
                settings.yOffset = 0.0
            except Exception:
                pass  # nosec B110

            return

        # LINHAS
        if geom == 1:
            if hasattr(QgsPalLayerSettings, "Placement"):
                P = QgsPalLayerSettings.Placement
                settings.placement = getattr(P, "Line", getattr(P, "Curved", P.OverPoint))
            else:
                settings.placement = getattr(QgsPalLayerSettings, "Line", QgsPalLayerSettings.Placement.OverPoint)
            return

        # POLÍGONOS (fallback simples)
        if hasattr(QgsPalLayerSettings, "Placement"):
            settings.placement = QgsPalLayerSettings.Placement.OverPoint
        else:
            settings.placement = QgsPalLayerSettings.Placement.OverPoint

    def reconfigurar_etiquetas_HTML(self):
        """
        Configura rótulos com HTML:
        - Monta expressão HTML com os campos marcados e suas cores;
        - Ativa 'Permitir formatação HTML';
        - Ajusta placement conforme geometria (principalmente linhas);
        - Valida expressão antes de aplicar (evita apagar rótulos existentes).
        """
        # 1) Campos selecionados
        selected = []
        for fieldName, (checkBox, colorButton) in self.fieldColorMapping.items():
            if checkBox.isChecked():
                selected.append((fieldName, colorButton))

        if not selected:
            return  # não aplica nada

        # 2) Constrói expressão HTML em blocos, um abaixo do outro
        parts = []
        for fieldName, colorButton in selected:
            color = colorButton.color.name() if hasattr(colorButton, "color") else "#000000"
            parts.append(
                f"'<div style=\"color:{color}; margin:0; padding:0;\">' "
                f"|| coalesce(to_string(\"{fieldName}\"), '') || "
                f"'</div>'")

        label_expression = " || ".join(parts) if parts else "''"

        # 3) Valida expressão ANTES de aplicar (evita “apagar” rótulos existentes)
        expr = QgsExpression(label_expression)
        if expr.hasParserError():
            # se quiser, aqui você pode mostrar uma mensagem ao usuário
            # QMessageBox.warning(self, "Erro", f"Expressão inválida: {expr.parserErrorString()}")
            return

        # 4) Settings base
        settings = QgsPalLayerSettings()
        settings.fieldName = label_expression
        settings.isExpression = True
        settings.enabled = True

        # 5) Placement conforme geometria
        self._aplicar_posicionamento_por_geometria(settings)

        # 6) Formato de texto com HTML ligado
        text_format = QgsTextFormat()
        text_format.setAllowHtmlFormatting(True)
        # opcional:
        # text_format.setSize(10)

        buffer_settings = QgsTextBufferSettings()
        buffer_settings.setEnabled(False)
        text_format.setBuffer(buffer_settings)

        settings.setFormat(text_format)

        # 7) Aplica na camada
        self.layer.setLabeling(QgsVectorLayerSimpleLabeling(settings))
        self.layer.setLabelsEnabled(True)
        self.layer.triggerRepaint()

        # Fecha o diálogo
        self.accept()

    def reconfigurar_etiquetas_simples(self):
        """
        Configura rótulos simples (sem HTML) na camada atual a partir dos campos
        marcados no diálogo.

        Ajustes aplicados:
        - No modo simples existe APENAS 1 cor de texto para todo o rótulo.
          (Antes o loop setava várias vezes e ficava só a última cor.)
        - Se houver 1 campo selecionado e existir cor definida, usa essa cor.
          Se houver mais de 1 campo, usa preto (#000000) por consistência.
        - Placement ajustado conforme geometria (evita sumiço em linhas).
        """
        # Filtra os campos que estão marcados nos checkboxes.
        selected_fields = [field for field, (checkBox, _) in self.fieldColorMapping.items() if checkBox.isChecked()]
        if not selected_fields:
            return

        # Expressão concatenada com quebras de linha
        expression = " || '\\n' || ".join([f"\"{field}\"" for field in selected_fields])

        settings = QgsPalLayerSettings()
        settings.fieldName = expression
        settings.isExpression = True
        settings.enabled = True

        # Formato de texto
        text_format = QgsTextFormat()
        text_format.setSize(10)

        buffer_settings = QgsTextBufferSettings()
        buffer_settings.setEnabled(False)
        buffer_settings.setSize(1)
        buffer_settings.setColor(QColor("white"))
        text_format.setBuffer(buffer_settings)

        # Modo simples = 1 cor só (não há cor por campo aqui)
        text_format.setColor(QColor("#000000"))
        if len(selected_fields) == 1:
            field0 = selected_fields[0]
            cb, colorButton = self.fieldColorMapping.get(field0, (None, None))
            if colorButton is not None and hasattr(colorButton, "color"):
                try:
                    c = colorButton.color
                    if isinstance(c, QColor) and c.isValid():
                        text_format.setColor(c)
                except Exception:
                    pass  # nosec B110

        settings.setFormat(text_format)

        # Placement conforme geometria
        self._aplicar_posicionamento_por_geometria(settings)

        # Aplica na camada
        self.layer.setLabeling(QgsVectorLayerSimpleLabeling(settings))
        self.layer.setLabelsEnabled(True)
        self.layer.triggerRepaint()

        # Fecha o diálogo e atualiza a interface do usuário
        self.accept()
        self.iface.mapCanvas().refreshAllLayers()
        self.iface.showLayerProperties(self.layer)