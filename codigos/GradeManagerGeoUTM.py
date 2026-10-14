from qgis.core import (QgsProject, QgsVectorLayer, QgsPointXY, QgsField, QgsFeature, QgsGeometry, QgsPalLayerSettings, QgsVectorLayerSimpleLabeling, QgsCoordinateReferenceSystem, Qgis, QgsMapLayer, QgsRectangle, QgsWkbTypes, QgsCoordinateTransform)
from qgis.PyQt.QtWidgets import QDialog, QProgressBar, QApplication, QFileDialog, QPushButton
from qgis.PyQt.QtCore import QVariant, Qt, QSettings, QMetaType, QCoreApplication, QUrl
from qgis.PyQt.QtGui import QDesktopServices
from qgis.utils import iface
from qgis.PyQt import uic
import ezdxf
import math
import os

FORM_CLASS, _ = uic.loadUiType(os.path.join(
    os.path.dirname(__file__), 'GradeUtmGeo.ui'))

class GradeManager(QDialog, FORM_CLASS):
    def __init__(self, parent=None):
        """
        Construtor da classe GradeManager.

        Parâmetros:
        - parent (QWidget, opcional): O widget pai do diálogo. Se não for especificado, o diálogo não terá um pai.

        Funcionalidades:
        - Inicializa a interface do usuário e as conexões dos botões do diálogo.
        - Define o título da janela do diálogo.
        - Conecta os botões a seus respectivos métodos.
        - Armazena os valores iniciais dos spinBoxes definidos no QtDesigner, que serão usados para resetar os valores posteriormente.

        Retorno:
        - Nenhum. O construtor apenas inicializa o diálogo.
        """
        # Chama o construtor da classe pai (`QDialog`) para inicializar o diálogo
        super(GradeManager, self).__init__(parent)

        # Configura a interface gráfica do usuário (UI) definida no QtDesigner
        self.setupUi(self)

        # Referência para a interface principal do QGIS
        self.iface = iface

        # Define o título do diálogo como "Gerar Grade UTM/GEO"
        self.setWindowTitle(self.tr("Gerar Grade UTM/GEO"))

        # Atualiza imediatamente o estado do botão
        self.updatePushButtonDXFState()

        self.lineEditSRC.setReadOnly(True) # lineEditSRC somente leitura

        # Garante que o diálogo seja destruído ao fechar (evita instâncias "fantasmas")
        self.setAttribute(Qt.WidgetAttribute.WA_DeleteOnClose, True)

        # Controle de conexões para evitar duplicação
        self._signals_connected = False
        self._project_signal_links = []  # lista de tuplas (signal, slot) para desconectar depois

        # Conecta os sinais aos slots
        self.connect_signals()

    def tr(self, message):
        return QCoreApplication.translate("GradeManager", message)

    def showEvent(self, event):
        """
        Manipula o evento de exibição do diálogo e reseta os valores dos spinBoxes para seus valores iniciais definidos no QtDesigner.

        Parâmetros:
        - event (QEvent): O evento de exibição que é acionado quando o diálogo é mostrado. É um parâmetro do tipo `QEvent`.

        Funcionalidades:
        - Chama a implementação original de `showEvent` da classe pai para garantir o comportamento padrão do evento.
        - Reseta os valores dos spinBoxes (`spinBox_espacamento`, `spinBox_percentual`, `spinBox_segundos`) para os valores iniciais 
          que foram definidos durante a inicialização da interface no QtDesigner.

        Retorno:
        - Nenhum. A função apenas redefine os valores dos spinBoxes quando o diálogo é exibido.
        """
        # Chama o método `showEvent` da classe pai para manter o comportamento padrão do evento
        super(GradeManager, self).showEvent(event)

        # Reseta os valores dos spinBoxes para os valores iniciais definidos no QtDesigner
        # Redefine `spinBox_espacamento` para seu valor inicial
        self.spinBox_espacamento.setValue(self.initial_spinBox_espacamento_value)

        # Redefine `spinBox_percentual` para seu valor inicial
        self.spinBox_percentual.setValue(self.initial_spinBox_percentual_value)

        # Redefine `spinBox_segundos` para seu valor inicial
        self.spinBox_segundos.setValue(self.initial_spinBox_segundos_value)
        
        # Atualiza imediatamente o estado do botão
        self.updatePushButtonDXFState()

        self.updatePushButtonsSRC() # chamada inicial

        self.atualizar_lineEditSRC()

        self.update_buttons_by_src()

    def connect_signals(self):
        # Evita reconectar se por algum motivo chamarem de novo na mesma instância
        if getattr(self, "_signals_connected", False):
            return
        self._signals_connected = True

        # Sinais da UI (só desta instância)
        self.pushButtonGradeGeo.clicked.connect(self.executar_criar_grade)
        self.pushButtonGradeUTM.clicked.connect(self.executar_criar_grade_utm)
        self.pushButtonFechar.clicked.connect(self.close)

        # Valores iniciais dos spinBoxes (Designer)
        self.initial_spinBox_espacamento_value = self.spinBox_espacamento.value()
        self.initial_spinBox_percentual_value = self.spinBox_percentual.value()
        self.initial_spinBox_segundos_value = self.spinBox_segundos.value()

        self.pushButtonGradeAj.clicked.connect(self.executar_criar_grade_utm_aj)
        self.pushButtonDXF.clicked.connect(self.exportar_para_dxf)
        self.pushButtonGradeGeoAj.clicked.connect(self.executar_criar_grade_geo_aj)

        self.pushButtonAtivarGEO.clicked.connect(self.ativar_src_geo)
        self.pushButtonAtivarUTM.clicked.connect(self.ativar_src_utm)

        # Sinais do Projeto updatePushButtonDXFState
        self._safe_connect(QgsProject.instance().layersAdded, self.updatePushButtonDXFState)
        self._safe_connect(QgsProject.instance().layersRemoved, self.updatePushButtonDXFState)

        # crsChanged existe no QGIS 3.x; mesmo assim, checamos por segurança
        if hasattr(QgsProject.instance(), "crsChanged"):
            self._safe_connect(QgsProject.instance().crsChanged, self.updatePushButtonDXFState)
            self._safe_connect(QgsProject.instance().crsChanged, self.atualizar_lineEditSRC)
            self._safe_connect(QgsProject.instance().crsChanged, self.updatePushButtonsSRC)
            self._safe_connect(QgsProject.instance().crsChanged, self.update_buttons_by_src)

    def _nome_grade_utm(self):
        return self.tr("Grade UTM")

    def _nome_coordenadas_utm(self):
        return self.tr("Coordenadas UTM")

    def _nome_grade_geo(self):
        return self.tr("Grade Geográfica")

    def _nome_coordenadas_geo(self):
        return self.tr("Coordenadas GEO")

    def _safe_connect(self, signal, slot):
        """
        Conecta signal->slot de forma segura e registra para desconexão no closeEvent.
        Usa UniqueConnection quando disponível.
        """
        # Tenta UniqueConnection em diferentes assinaturas (PyQt5 varia)
        try:
            signal.connect(slot, type=Qt.ConnectionType.UniqueConnection)
        except TypeError:
            try:
                signal.connect(slot, Qt.ConnectionType.UniqueConnection)
            except TypeError:
                # Fallback sem UniqueConnection (ainda assim, evitamos duplicar via self._signals_connected)
                signal.connect(slot)

        self._project_signal_links.append((signal, slot))

    def _disconnect_project_signals(self):
        """
        Desconecta todos os sinais registrados (evita disparos múltiplos entre instâncias).
        """
        for sig, slot in self._project_signal_links:
            try:
                sig.disconnect(slot)
            except Exception:
                pass  # nosec B110

        self._project_signal_links.clear()
        self._signals_connected = False

    def closeEvent(self, event):
        # Desconecta sinais globais do projeto para não acumular entre instâncias
        self._disconnect_project_signals()
        super().closeEvent(event)

    def executar_criar_grade(self):
        """
        Executa a criação da grade geográfica com base nos valores definidos no diálogo.
        """
        segundos = self.spinBox_segundos.value()
        percentual = self.spinBox_percentual.value()   # pegar o percentual

        # Chama o método ajustado
        self.criar_grade_e_pontos_geo(segundos, percentual)

        # Exibe os rótulos
        self.exibir_rotulos_na_camada_escolhida()

    def obter_camada_pelo_nome(self, nome):
        """
        Obtém uma camada do projeto QGIS com base no nome fornecido.

        Funcionalidades:
        - Percorre todas as camadas atualmente carregadas no projeto QGIS.
        - Verifica se o nome da camada coincide com o nome fornecido.
        - Retorna a camada correspondente se encontrada, ou `None` se nenhuma camada com o nome especificado for encontrada.

        Parâmetros:
        - nome (str): O nome da camada que se deseja buscar no projeto QGIS.

        Retorno:
        - QgsVectorLayer: A camada correspondente ao nome fornecido, se encontrada.
        - None: Se nenhuma camada com o nome especificado for encontrada.
        """
        # Percorre todas as camadas carregadas no projeto QGIS
        for layer in QgsProject.instance().mapLayers().values():
            # Verifica se o nome da camada corresponde ao nome fornecido
            if layer.name() == nome:
                return layer  # Retorna a camada encontrada

        # Retorna None se nenhuma camada correspondente for encontrada
        return None

    def executar_criar_grade_utm(self):
        """
        Executa a criação da grade UTM com base nos valores definidos no diálogo.

        Funcionalidades:
        - Obtém os valores atuais do spinBox de espaçamento e percentual.
        - Chama a função que cria a grade e os pontos UTM, utilizando os valores de espaçamento e percentual obtidos.
        - Exibe os rótulos na camada de pontos UTM criada.

        Parâmetros:
        - Nenhum.

        Retorno:
        - Nenhum. A função é responsável por acionar a criação da grade UTM e exibir os rótulos.
        """
        # Obtém o valor de espaçamento a partir do spinBox_espacamento
        intervalo = self.spinBox_espacamento.value()

        # Obtém o valor percentual a partir do spinBox_percentual
        percentual = self.spinBox_percentual.value()

        # Chama o método para criar a grade UTM e os pontos usando os valores de espaçamento e percentual
        self.criar_grade_e_pontos_utm(intervalo, percentual)

        # Exibe os rótulos nos pontos da camada UTM criada
        self.exibir_rotulos_na_camada_escolhida_utm()

    def remove_layers_if_exist(self, layer_names):
        """
        Remove camadas do projeto QGIS se elas existirem, baseado nos nomes fornecidos.

        Funcionalidades:
        - Verifica se camadas com os nomes fornecidos estão carregadas no projeto QGIS.
        - Remove as camadas encontradas que correspondem aos nomes fornecidos.

        Parâmetros:
        - layer_names (list): Lista de strings contendo os nomes das camadas a serem removidas.

        Retorno:
        - Nenhum. A função remove as camadas existentes que correspondem aos nomes fornecidos.
        """
        # Itera sobre a lista de nomes de camadas
        for layer_name in layer_names:
            # Obtém as camadas que possuem o nome correspondente
            existing_layers = QgsProject.instance().mapLayersByName(layer_name)

            # Itera sobre as camadas encontradas com o nome correspondente
            for layer in existing_layers:
                # Remove a camada do projeto QGIS com base em seu ID
                QgsProject.instance().removeMapLayer(layer.id())

    def esta_em_utm(self, src_projeto):
        """Verifica se o SRC informado é uma projeção UTM válida."""
        if not src_projeto or not src_projeto.isValid() or src_projeto.isGeographic():
            return False

        descricao = (src_projeto.description() or "").upper()
        proj = (src_projeto.toProj() or "").lower()
        return "UTM" in descricao or "+proj=utm" in proj

    def exibir_rotulos_na_camada_escolhida_geo(self):
        """Localiza a camada de coordenadas geográficas e aplica seus rótulos."""
        camada = self.obter_camada_pelo_nome(self._nome_coordenadas_geo())

        if camada:
            self.configurar_rotulos_na_camada(camada)

        # Nome da camada de pontos geográficos que será verificada
        nome_da_camada_pontos = "Coordenadas Limites"

        # Obtém a camada pelo nome, se ela estiver carregada no projeto
        camada_escolhida_pontos = self.obter_camada_pelo_nome(nome_da_camada_pontos)

        # Se a camada foi encontrada, configura os rótulos para essa camada
        if camada_escolhida_pontos:
            self.configurar_rotulos_na_camada(camada_escolhida_pontos)

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
        progressMessageBar = self.iface.messageBar().createMessage(self.tr("Criando Grade..."))
        progressBar = QProgressBar()  # Cria uma instância da QProgressBar
        ALIGN_LEFT = getattr(Qt, "AlignLeft", Qt.AlignmentFlag.AlignLeft)
        ALIGN_VCENTER = getattr(Qt, "AlignVCenter", Qt.AlignmentFlag.AlignVCenter)
        progressBar.setAlignment(ALIGN_LEFT | ALIGN_VCENTER)

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

    def criar_grade_e_pontos_utm(self, intervalo, percentual):
        """
        Esta função cria uma grade UTM e uma camada de pontos de interseção no QGIS.

        Função:
        - Remove as camadas existentes chamadas 'Grade UTM' e 'Coordenadas Limites'.
        - Verifica se o sistema de coordenadas do projeto está em UTM.
        - Define os limites da grade, ajusta os valores para serem múltiplos do intervalo fornecido.
        - Cria linhas horizontais e verticais para a grade, com base em um intervalo especificado.
        - Escala a janela central da grade com base em um percentual dado.
        - Gera e adiciona pontos de interseção nas extremidades e bordas da grade.
        - Exibe uma barra de progresso enquanto a grade e os pontos são criados.
        - Exibe uma mensagem de sucesso após a conclusão.

        Parâmetros:
        - intervalo (int): O espaçamento entre as linhas da grade (em metros).
        - percentual (float): Percentual para ajustar a escala da janela central (de 0% a 100%).

        Retorno:
        - Nenhum valor de retorno explícito. A função cria camadas de linhas e pontos diretamente no projeto QGIS.
        """
        if intervalo <= 0:
            self.mostrar_mensagem(self.tr("Intervalo inválido. Defina um valor maior que zero."), "Erro")
            return

        # Remove as camadas existentes 'Grade UTM' e 'Coordenadas Limites', se existirem
        self.remove_layers_if_exist([self._nome_grade_utm(), self._nome_coordenadas_utm(), "Coordenadas Limites"])

        # Obtém a extensão atual da tela do mapa e o SRC (Sistema de Referência de Coordenadas) do projeto
        canvas = self.iface.mapCanvas()
        extent = canvas.extent()
        src_projeto = QgsProject.instance().crs()

        # Check if the project CRS is UTM
        if not self.esta_em_utm(src_projeto):
            self.mostrar_mensagem(self.tr("O projeto não está configurado com um SRC UTM."), "Erro")
            return

        # Obtém os limites da extensão (xmin, ymin, xmax, ymax)
        xmin, ymin, xmax, ymax = extent.toRectF().getCoords()

        # Adjust grid limits to be multiples of the interval
        xmin = int(xmin) // intervalo * intervalo
        ymin = int(ymin) // intervalo * intervalo
        xmax = int(xmax) // intervalo * intervalo + intervalo
        ymax = int(ymax) // intervalo * intervalo + intervalo

        # Invert the scale of the central window based on the percentual
        escala_janela = (100 - percentual) / 100.0  # Invert scale to make 100% fill the entire area

        # Calcula as dimensões totais da grade (largura e altura)
        largura_total = xmax - xmin
        altura_total = ymax - ymin

         # Define as coordenadas da janela central com base na escala invertida
        largura_janela = largura_total * escala_janela
        altura_janela = altura_total * escala_janela
        xmin_janela = xmin + (largura_total - largura_janela) / 2
        xmax_janela = xmax - (largura_total - largura_janela) / 2
        ymin_janela = ymin + (altura_total - altura_janela) / 2
        ymax_janela = ymax - (altura_total - altura_janela) / 2

        # Total de etapas (EXATO)
        # Mesmas listas que os loops vão usar
        y_vals = list(range(int(ymin), int(ymax + intervalo), int(intervalo)))
        x_vals = list(range(int(xmin), int(xmax + intervalo), int(intervalo)))

        def _n_segs(val, vmin, vmax):
            # Dentro da janela central, cria 2 segmentos; fora, 1 linha
            return 2 if (vmin <= val <= vmax) else 1

        total_line_segs = (
            sum(_n_segs(y, ymin_janela, ymax_janela) for y in y_vals) +
            sum(_n_segs(x, xmin_janela, xmax_janela) for x in x_vals))

        # Pontos:
        # - para cada x: 2 pontos (ymin e ymax)
        # - para cada y interno: 2 pontos (xmin e xmax)
        total_points = (2 * len(x_vals)) + (2 * max(0, len(y_vals) - 2))

        total_steps = total_line_segs + total_points

        # Inicia a barra de progresso com o número total de etapas
        progressBar, progressMessageBar = self.iniciar_progress_bar(total_steps)
        current_step = 0

        # Cria a camada de linhas da grade
        grid_layer = QgsVectorLayer(f'LineString?crs={src_projeto.authid()}', self._nome_grade_utm(), 'memory')
        provider = grid_layer.dataProvider()
        provider.addAttributes([QgsField('ID', QMetaType.Type.Int)])  # Adiciona o campo 'ID'
        grid_layer.updateFields() # Atualiza os campos da camada

        # Inicia o ID das linhas em 1
        line_id = 1

        # Adiciona linhas horizontais à camada da grade
        for y in y_vals:
            if ymin_janela <= y <= ymax_janela:
                coords_inicio = [QgsPointXY(xmin, y), QgsPointXY(xmin_janela, y)]
                coords_fim = [QgsPointXY(xmax_janela, y), QgsPointXY(xmax, y)]
                for coords in [coords_inicio, coords_fim]:
                    line = QgsFeature()
                    line.setGeometry(QgsGeometry.fromPolylineXY(coords))
                    line.setAttributes([line_id]) # Atribui o ID à linha
                    provider.addFeature(line) # Adiciona a linha à camada
                    line_id += 1 # Incrementa o ID da linha

                    # Atualiza a barra de progresso
                    current_step += 1
                    progressBar.setValue(current_step)
            else:
                # Adiciona a linha completa fora da janela central
                line_coords = QgsGeometry.fromPolylineXY([QgsPointXY(xmin, y), QgsPointXY(xmax, y)])
                horizontal_line = QgsFeature()
                horizontal_line.setGeometry(line_coords)
                horizontal_line.setAttributes([line_id])
                provider.addFeature(horizontal_line)
                line_id += 1

                # Atualiza a barra de progresso
                current_step += 1
                progressBar.setValue(current_step)

        # Adiciona linhas verticais à camada da grade
        for x in x_vals:
            if xmin_janela <= x <= xmax_janela:
                coords_inicio = [QgsPointXY(x, ymin), QgsPointXY(x, ymin_janela)]
                coords_fim = [QgsPointXY(x, ymax_janela), QgsPointXY(x, ymax)]
                for coords in [coords_inicio, coords_fim]:
                    line = QgsFeature()
                    line.setGeometry(QgsGeometry.fromPolylineXY(coords)) # Define a geometria da linha
                    line.setAttributes([line_id]) # Atribui o ID à linha
                    provider.addFeature(line) # Adiciona a linha à camada
                    line_id += 1

                    # Atualiza a barra de progresso
                    current_step += 1
                    progressBar.setValue(current_step)
            else:
                # Adiciona a linha completa fora da janela central
                line_coords = QgsGeometry.fromPolylineXY([QgsPointXY(x, ymin), QgsPointXY(x, ymax)])
                vertical_line = QgsFeature()
                vertical_line.setGeometry(line_coords)
                vertical_line.setAttributes([line_id])
                provider.addFeature(vertical_line)
                line_id += 1

                # Update progress bar
                current_step += 1
                progressBar.setValue(current_step)

        # Adiciona a camada de linhas ao projeto
        QgsProject.instance().addMapLayer(grid_layer)

        # Cria a camada de pontos de interseção
        intersection_points_layer = QgsVectorLayer(f'Point?crs={src_projeto.authid()}', self._nome_coordenadas_utm(), 'memory')
        points_provider = intersection_points_layer.dataProvider()
        points_provider.addAttributes([
            QgsField('ID', QMetaType.Type.Int),
            QgsField('X', QMetaType.Type.Int),
            QgsField('Y', QMetaType.Type.Int)])
        intersection_points_layer.updateFields()

        # Add intersection points only on the boundary lines
        point_id = 1
        # Adiciona pontos de interseção nas bordas verticais (nos extremos superior e inferior)
        for x in x_vals:
            for y in [ymin, ymax]:
                intersection_point = QgsFeature()
                point_coords = QgsPointXY(x, y)
                intersection_point.setGeometry(QgsGeometry.fromPointXY(point_coords)) # Define a geometria do ponto
                intersection_point.setAttributes([point_id, x, y]) # Atribui o ID e coordenadas
                points_provider.addFeature(intersection_point) # Adiciona o ponto à camada
                point_id += 1

                # Atualiza a barra de progresso
                current_step += 1
                progressBar.setValue(current_step)

        # Adiciona pontos de interseção nas bordas horizontais
        for y in y_vals[1:-1]:
            for x in [xmin, xmax]:
                intersection_point = QgsFeature()
                point_coords = QgsPointXY(x, y)
                intersection_point.setGeometry(QgsGeometry.fromPointXY(point_coords)) # Define a geometria do ponto
                intersection_point.setAttributes([point_id, x, y]) # Atribui o ID e coordenadas
                points_provider.addFeature(intersection_point) # Adiciona o ponto à camada
                point_id += 1

                # Update progress bar
                current_step += 1
                progressBar.setValue(current_step)

        # Adiciona a camada de pontos de interseção ao projeto
        QgsProject.instance().addMapLayer(intersection_points_layer)

        # Limpa a barra de progresso após a conclusão
        self.iface.messageBar().clearWidgets()

        # Exibe uma mensagem de sucesso após a criação das camadas
        self.mostrar_mensagem(self.tr("As camadas '{grade}' e '{coordenadas}' foram criadas com sucesso.").format(grade=self._nome_grade_utm(), coordenadas=self._nome_coordenadas_utm()), "Sucesso")

    def exibir_rotulos_na_camada_escolhida_utm(self):
        """Localiza a camada de coordenadas UTM e aplica seus rótulos."""
        camada = self.obter_camada_pelo_nome(self._nome_coordenadas_utm())

        if camada:
            self.configurar_rotulos_na_camada_utm(camada)

        # Nome da camada de pontos que será configurada
        nome_da_camada_pontos = "Coordenadas Limites"

        # Obtém a camada pelo nome
        camada_escolhida_pontos = self.obter_camada_pelo_nome(nome_da_camada_pontos)

        # Verifica se a camada foi encontrada no projeto
        if camada_escolhida_pontos:
            # Se a camada foi encontrada, configura os rótulos na camada
            self.configurar_rotulos_na_camada_utm(camada_escolhida_pontos)

    def configurar_rotulos_na_camada_utm(self, camada_de_vetor):
        """
        Configura rótulos para uma camada de pontos UTM, exibindo:
        - Ambos X e Y nas quinas (min/max de X e Y)
        - X nas bordas superior/inferior (min/max de Y)
        - Y nas bordas esquerda/direita (min/max de X)
        """
        if not isinstance(camada_de_vetor, QgsVectorLayer):
            return

        # 1. Determina extremos
        xs, ys = [], []
        for f in camada_de_vetor.getFeatures():
            g = f.geometry()
            if g and not g.isEmpty():
                p = g.asPoint()
                xs.append(p.x())
                ys.append(p.y())
        if not xs or not ys:
            return

        min_x, max_x = min(xs), max(xs)
        min_y, max_y = min(ys), max(ys)
        tol = 1e-6  # Tolerância para comparação

        # 2. Expressão: ambos nas quinas, X no topo/baixo, Y na esquerda/direita
        expr = (
            f"CASE "
            f"WHEN (abs(\"X\" - {min_x}) < {tol} AND (abs(\"Y\" - {min_y}) < {tol} OR abs(\"Y\" - {max_y}) < {tol})) "
            f"  OR (abs(\"X\" - {max_x}) < {tol} AND (abs(\"Y\" - {min_y}) < {tol} OR abs(\"Y\" - {max_y}) < {tol})) "
            f"THEN concat(to_string(\"X\"), '\\n', to_string(\"Y\")) "
            f"WHEN abs(\"Y\" - {min_y}) < {tol} OR abs(\"Y\" - {max_y}) < {tol} "
            f"THEN to_string(\"X\") "
            f"WHEN abs(\"X\" - {min_x}) < {tol} OR abs(\"X\" - {max_x}) < {tol} "
            f"THEN to_string(\"Y\") "
            f"ELSE '' END")

        cfg = QgsPalLayerSettings()
        cfg.enabled = True
        cfg.isExpression = True
        cfg.displayAll = True
        cfg.priority = 0
        cfg.fieldName = expr

        camada_de_vetor.setLabeling(QgsVectorLayerSimpleLabeling(cfg))
        camada_de_vetor.setLabelsEnabled(True)
        camada_de_vetor.triggerRepaint()

    def dec_to_dms(self, valor):
        """
        Converte um valor decimal de coordenadas (graus decimais) em graus, minutos e segundos (DMS).

        A função é usada para converter valores de latitude e longitude no formato decimal para
        o formato de graus, minutos e segundos (DMS).

        Parâmetros:
        - valor (float): O valor de coordenada em graus decimais que será convertido para DMS.

        Retorno:
        - str: O valor convertido no formato DMS (graus, minutos, segundos), retornado como string.
        """
        # Define o sinal negativo se o valor for negativo, ou nenhum sinal se for positivo
        sinal = "-" if valor < 0 else ""

        # Converte o valor para positivo, se necessário, para calcular os graus, minutos e segundos
        valor = abs(valor)

        # Extrai a parte inteira do valor como graus
        graus = int(valor)

        # Calcula os minutos a partir da parte decimal dos graus
        minutos = int((valor - graus) * 60)

        # Calcula os segundos a partir da parte restante após a extração dos minutos
        segundos = (valor - graus - minutos / 60) * 3600

        # Retorna o valor formatado em graus, minutos e segundos com precisão de 2 casas decimais nos segundos
        return f"{sinal}{graus}° {minutos}' {segundos:.2f}\""

    def criar_grade_e_pontos_geo(self, segundos, percentual):
        """
        Cria grade geográfica e pontos de coordenadas nas bordas, com janela central (percentual).
        Barra de progresso com total_steps consistente (linhas + pontos únicos).
        """
        self.remove_layers_if_exist([self._nome_grade_geo(), self._nome_coordenadas_geo(), "Grade Geografica", "Coordenadas Limites"])

        canvas = self.iface.mapCanvas()
        extent = canvas.extent()
        src_projeto = QgsProject.instance().crs()

        if not src_projeto.isGeographic():
            self.mostrar_mensagem(self.tr("O sistema de coordenadas não está em coordenadas geográficas."), "Erro")
            return

        xmin, ymin, xmax, ymax = extent.toRectF().getCoords()

        if not (-180 <= xmin <= 180 and -180 <= xmax <= 180 and -90 <= ymin <= 90 and -90 <= ymax <= 90):
            self.mostrar_mensagem(self.tr("As coordenadas da grade estão fora dos limites válidos."), "Erro")
            return

        intervalo = segundos / 3600.0
        if intervalo <= 0:
            self.mostrar_mensagem(self.tr("Intervalo inválido. Defina segundos > 0."), "Erro")
            return

        xmin = math.floor(xmin / intervalo) * intervalo
        ymin = math.floor(ymin / intervalo) * intervalo
        xmax = math.ceil(xmax / intervalo) * intervalo
        ymax = math.ceil(ymax / intervalo) * intervalo

        tol = intervalo * 1e-6

        # Listas de linhas (valores)
        linhas_horizontais = []
        y = ymin
        while y <= ymax + tol:
            linhas_horizontais.append(round(y, 10))
            y += intervalo

        linhas_verticais = []
        x = xmin
        while x <= xmax + tol:
            linhas_verticais.append(round(x, 10))
            x += intervalo

        # Janela central
        escala_janela = (100 - percentual) / 100.0
        largura_total = xmax - xmin
        altura_total = ymax - ymin
        largura_janela = largura_total * escala_janela
        altura_janela = altura_total * escala_janela

        xmin_janela = xmin + (largura_total - largura_janela) / 2
        xmax_janela = xmax - (largura_total - largura_janela) / 2
        ymin_janela = ymin + (altura_total - altura_janela) / 2
        ymax_janela = ymax - (altura_total - altura_janela) / 2

        # Total de etapas (EXATO)
        def _n_segs(val, vmin, vmax):
            return 2 if (vmin <= val <= vmax) else 1

        total_line_segs = (
            sum(_n_segs(y, ymin_janela, ymax_janela) for y in linhas_horizontais) +
            sum(_n_segs(x, xmin_janela, xmax_janela) for x in linhas_verticais))

        def coordenada_ajustada(xv, yv, precisao=6):
            return (round(xv, precisao), round(yv, precisao))

        y_inner = linhas_horizontais[1:-1] if len(linhas_horizontais) > 2 else []

        pontos_previstos = set()

        # Bordas verticais (sem cantos)
        for xv in (xmin, xmax):
            for yv in y_inner:
                pontos_previstos.add(coordenada_ajustada(xv, yv))

        # Bordas horizontais (com cantos)
        for yv in (ymin, ymax):
            for xv in linhas_verticais:
                pontos_previstos.add(coordenada_ajustada(xv, yv))

        # Extremidades das linhas (garantia)
        for yv in linhas_horizontais:
            pontos_previstos.add(coordenada_ajustada(xmin, yv))
            pontos_previstos.add(coordenada_ajustada(xmax, yv))
        for xv in linhas_verticais:
            pontos_previstos.add(coordenada_ajustada(xv, ymin))
            pontos_previstos.add(coordenada_ajustada(xv, ymax))

        total_points = len(pontos_previstos)
        total_steps = total_line_segs + total_points

        # Barra de progresso
        progressBar, progressMessageBar = self.iniciar_progress_bar(total_steps)
        current_step = 0

        # 1) Camada de linhas
        grid_layer = QgsVectorLayer(f'LineString?crs={src_projeto.authid()}', self._nome_grade_geo(), 'memory')
        provider = grid_layer.dataProvider()
        provider.addAttributes([QgsField('ID', QMetaType.Type.Int)])
        grid_layer.updateFields()

        line_id = 1

        for yv in linhas_horizontais:
            if ymin_janela <= yv <= ymax_janela:
                # Segmentos esquerda/direita
                line_coords_esq = QgsGeometry.fromPolylineXY([QgsPointXY(xmin, yv), QgsPointXY(xmin_janela, yv)])
                line_coords_dir = QgsGeometry.fromPolylineXY([QgsPointXY(xmax_janela, yv), QgsPointXY(xmax, yv)])

                for lc in (line_coords_esq, line_coords_dir):
                    f = QgsFeature()
                    f.setGeometry(lc)
                    f.setAttributes([line_id])
                    provider.addFeature(f)
                    line_id += 1

                    current_step += 1
                    progressBar.setValue(current_step)
            else:
                # Linha completa
                lc = QgsGeometry.fromPolylineXY([QgsPointXY(xmin, yv), QgsPointXY(xmax, yv)])
                f = QgsFeature()
                f.setGeometry(lc)
                f.setAttributes([line_id])
                provider.addFeature(f)
                line_id += 1

                current_step += 1
                progressBar.setValue(current_step)

        for xv in linhas_verticais:
            if xmin_janela <= xv <= xmax_janela:
                # Segmentos baixo/cima
                line_coords_baixo = QgsGeometry.fromPolylineXY([QgsPointXY(xv, ymin), QgsPointXY(xv, ymin_janela)])
                line_coords_cima  = QgsGeometry.fromPolylineXY([QgsPointXY(xv, ymax_janela), QgsPointXY(xv, ymax)])

                for lc in (line_coords_baixo, line_coords_cima):
                    f = QgsFeature()
                    f.setGeometry(lc)
                    f.setAttributes([line_id])
                    provider.addFeature(f)
                    line_id += 1

                    current_step += 1
                    progressBar.setValue(current_step)
            else:
                lc = QgsGeometry.fromPolylineXY([QgsPointXY(xv, ymin), QgsPointXY(xv, ymax)])
                f = QgsFeature()
                f.setGeometry(lc)
                f.setAttributes([line_id])
                provider.addFeature(f)
                line_id += 1

                current_step += 1
                progressBar.setValue(current_step)

        QgsProject.instance().addMapLayer(grid_layer)

        # 2) Camada de pontos
        intersection_points_layer = QgsVectorLayer(f'Point?crs={src_projeto.authid()}', self._nome_coordenadas_geo(), 'memory')  ,
        points_provider = intersection_points_layer.dataProvider()
        points_provider.addAttributes([
            QgsField('ID', QMetaType.Type.Int),
            QgsField('X', QMetaType.Type.Double),
            QgsField('Y', QMetaType.Type.Double),
            QgsField('X_DMS', QMetaType.Type.QString, len=20),
            QgsField('Y_DMS', QMetaType.Type.QString, len=20)])
        intersection_points_layer.updateFields()

        point_id = 1
        pontos_criados = set()

        def add_ponto(xv, yv):
            nonlocal point_id, current_step
            key = coordenada_ajustada(xv, yv)
            if key in pontos_criados:
                return
            f = QgsFeature()
            f.setGeometry(QgsGeometry.fromPointXY(QgsPointXY(xv, yv)))
            f.setAttributes([point_id, xv, yv, self.dec_to_dms(xv), self.dec_to_dms(yv)])
            points_provider.addFeature(f)
            pontos_criados.add(key)
            point_id += 1

            current_step += 1
            progressBar.setValue(current_step)

        # Bordas verticais (sem cantos)
        for xv in (xmin, xmax):
            for yv in y_inner:
                add_ponto(xv, yv)

        # Bordas horizontais (com cantos)
        for yv in (ymin, ymax):
            for xv in linhas_verticais:
                add_ponto(xv, yv)

        # Extremidades (garantia)
        for yv in linhas_horizontais:
            add_ponto(xmin, yv)
            add_ponto(xmax, yv)
        for xv in linhas_verticais:
            add_ponto(xv, ymin)
            add_ponto(xv, ymax)

        QgsProject.instance().addMapLayer(intersection_points_layer)

        # Fecha a barra e mensagem final
        self.iface.messageBar().clearWidgets()
        self.mostrar_mensagem(self.tr("As camadas '{grade}' e '{coordenadas}' foram criadas com sucesso.").format(grade=self._nome_grade_geo(), coordenadas=self._nome_coordenadas_geo()), "Sucesso")

    def exibir_rotulos_na_camada_escolhida(self):
        """Localiza a camada de coordenadas geográficas e aplica seus rótulos."""
        camada = self.obter_camada_pelo_nome(self._nome_coordenadas_geo())

        if camada:
            self.configurar_rotulos_na_camada(camada)

        # Define o nome da camada de pontos onde os rótulos serão exibidos
        nome_da_camada_pontos = "Coordenadas Limites"

        # Busca a camada de pontos "Coordenadas Limites" no projeto atual
        camada_escolhida_pontos = self.obter_camada_pelo_nome(nome_da_camada_pontos)

        # Verifica se a camada foi encontrada
        if camada_escolhida_pontos:
            # Configura e exibe os rótulos sobre os pontos da camada
            self.configurar_rotulos_na_camada(camada_escolhida_pontos)

    def mostrar_mensagem(self, texto, tipo, duracao=3, caminho_pasta=None, caminho_arquivo=None):
        """
        Exibe uma mensagem na barra de mensagens do QGIS, proporcionando feedback ao usuário baseado nas ações realizadas.

        Parâmetros:
        - texto (str): O texto da mensagem que será exibido.
        - tipo (str): O tipo de mensagem ("Erro" ou "Sucesso") que determina o nível de prioridade da notificação.
        - duracao (int, opcional): O tempo em segundos que a mensagem permanecerá visível. O padrão é 3 segundos.
        - caminho_pasta (str, opcional): Caminho de uma pasta que pode ser aberto diretamente a partir da mensagem.
        - caminho_arquivo (str, opcional): Caminho de um arquivo que pode ser executado diretamente a partir da mensagem.

        Funcionalidades:
        - Exibe uma mensagem de erro ou sucesso com a duração especificada.
        - Se o tipo for "Erro", exibe uma mensagem com nível crítico.
        - Se o tipo for "Sucesso", exibe a mensagem com um botão opcional para abrir uma pasta ou executar um arquivo.
        """
        # Obtém a barra de mensagens da interface do QGIS
        bar = self.iface.messageBar()  # Acessa a barra de mensagens da interface do QGIS

        # Exibe a mensagem com o nível apropriado baseado no tipo
        if tipo == "Erro":
            # Mostra uma mensagem de erro na barra de mensagens com um ícone crítico e a duração especificada
            bar.pushMessage(self.tr("Erro"), texto, level=Qgis.MessageLevel.Critical, duration=duracao)
        elif tipo == "Sucesso":
            # Cria o item da mensagem
            msg = bar.createMessage(self.tr("Sucesso"), texto)
            
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

    def configurar_rotulos_na_camada(self, camada_de_vetor):
        """
        Configura os rótulos geográficos:
        - quinas: latitude e longitude;
        - topo e base: longitude;
        - esquerda e direita: latitude.
        """
        if not isinstance(camada_de_vetor, QgsVectorLayer):
            return

        xs, ys = [], []

        for feature in camada_de_vetor.getFeatures():
            geometria = feature.geometry()

            if geometria and not geometria.isEmpty():
                ponto = geometria.asPoint()
                xs.append(ponto.x())
                ys.append(ponto.y())

        if not xs or not ys:
            return

        min_x, max_x = min(xs), max(xs)
        min_y, max_y = min(ys), max(ys)
        tol = 1e-6

        expr = (
            f"CASE "
            f"WHEN (abs(\"X\" - {min_x}) < {tol} AND (abs(\"Y\" - {min_y}) < {tol} OR abs(\"Y\" - {max_y}) < {tol})) "
            f"OR (abs(\"X\" - {max_x}) < {tol} AND (abs(\"Y\" - {min_y}) < {tol} OR abs(\"Y\" - {max_y}) < {tol})) "
            f"THEN concat(to_string(\"Y_DMS\"), '\\n', to_string(\"X_DMS\")) "
            f"WHEN abs(\"Y\" - {min_y}) < {tol} OR abs(\"Y\" - {max_y}) < {tol} THEN to_string(\"X_DMS\") "
            f"WHEN abs(\"X\" - {min_x}) < {tol} OR abs(\"X\" - {max_x}) < {tol} THEN to_string(\"Y_DMS\") "
            f"ELSE '' END")

        cfg = QgsPalLayerSettings()
        cfg.enabled = True
        cfg.isExpression = True
        cfg.displayAll = True
        cfg.priority = 0
        cfg.fieldName = expr

        camada_de_vetor.setLabeling(QgsVectorLayerSimpleLabeling(cfg))
        camada_de_vetor.setLabelsEnabled(True)
        camada_de_vetor.triggerRepaint()

    def _camada_esta_visivel(self, layer):
        """Retorna True somente quando a camada está efetivamente visível na árvore do QGIS."""
        if not layer or not layer.isValid():
            return False

        node = QgsProject.instance().layerTreeRoot().findLayer(layer.id())

        if node is None:
            return False

        try:
            return bool(node.isVisible())
        except Exception:
            try:
                return bool(node.itemVisibilityChecked())
            except Exception:
                return False

    def _geometria_no_crs(self, geometria, crs_origem, crs_destino):
        """Copia e transforma uma geometria para o SRC de destino."""
        if geometria is None or geometria.isEmpty():
            return None

        geom = QgsGeometry(geometria)

        if not crs_destino or not crs_destino.isValid():
            return geom

        # Camadas temporárias podem não informar o SRC, embora suas
        # coordenadas já estejam no mesmo sistema do projeto.
        if not crs_origem or not crs_origem.isValid():
            crs_origem = crs_destino

        try:
            if crs_origem != crs_destino:
                geom.transform(QgsCoordinateTransform(crs_origem, crs_destino, QgsProject.instance()))
        except Exception:
            return None

        return geom if not geom.isEmpty() else None

    def _extensao_camada_no_crs(self, layer, crs_destino):
        """Transforma a extensão da camada para o SRC de destino."""
        if not layer or not layer.isValid() or layer.extent().isEmpty():
            return None

        try:
            extensao = layer.extent()
            crs_origem = layer.crs()

            # Caso o SRC da camada não esteja definido, considera que
            # a extensão já utiliza as coordenadas do projeto.
            if crs_origem and crs_origem.isValid() and crs_destino and crs_destino.isValid() and crs_origem != crs_destino:
                extensao = QgsCoordinateTransform(crs_origem, crs_destino, QgsProject.instance()).transformBoundingBox(extensao)

            return QgsGeometry.fromRect(extensao)
        except Exception:
            return None

    def executar_criar_grade_utm_aj(self):
        """
        Cria uma grade UTM que:
          - Ocupa totalmente a extensão do Map Canvas, arredondada a múltiplos do espaçamento
          - Linhas fechando as extremidades (fora das feições)
          - E também cria uma camada de pontos "Coordenadas Limites (Fora)" nas bordas,
            armazenando X e Y (apenas se estiverem fora das feições)
          - Para camadas lineares e pontuais, usa um buffer de 10% do valor do spinBox_espacamento
          - Se não houver feições (ou não estiver em UTM), exibe mensagem de erro.
          - Configura os rótulos nos pontos, exibindo X ou Y conforme a posição extrema.
        """
        # 1) Verificar se o projeto está em SRC UTM
        crs_projeto = QgsProject.instance().crs()
        if not self.esta_em_utm(crs_projeto):
            self.mostrar_mensagem(self.tr("O projeto não está em SRC UTM. Defina um SRC UTM antes de continuar."), "Erro")
            return

        # 2) Pegar espaçamento no spinBox
        intervalo = self.spinBox_espacamento.value()
        if intervalo <= 0:
            self.mostrar_mensagem(self.tr("Intervalo inválido. Defina um valor > 0."), "Erro")
            return

        # Buffer de 10% do espaçamento para linhas/pontos
        buffer_para_linhas_pontos = 0.1 * intervalo

        # 3) Remover camadas anteriores
        self.remove_layers_if_exist([self._nome_grade_utm(), self._nome_coordenadas_utm(), "Coordenadas Limites"])

        # 4) Constrói a união das geometrias no SRC atual do projeto.
        union_geom = None

        def unir_geometrias(base_geom, nova_geom):
            if nova_geom is None or nova_geom.isEmpty():
                return base_geom
            return nova_geom if base_geom is None else base_geom.combine(nova_geom)

        for layer in QgsProject.instance().mapLayers().values():
            if not layer.isValid() or not self._camada_esta_visivel(layer) or self._is_satellite_provider(layer):
                continue

            if layer.type() == QgsMapLayer.LayerType.VectorLayer:
                tipo_geometria = layer.geometryType()

                for feature in layer.getFeatures():
                    geom = self._geometria_no_crs(feature.geometry(), layer.crs(), crs_projeto)

                    if geom is None:
                        continue

                    if tipo_geometria in (QgsWkbTypes.GeometryType.LineGeometry, QgsWkbTypes.GeometryType.PointGeometry):
                        geom = geom.buffer(buffer_para_linhas_pontos, 5)

                    union_geom = unir_geometrias(union_geom, geom)

            elif layer.type() in (QgsMapLayer.LayerType.RasterLayer, QgsMapLayer.LayerType.MeshLayer):
                geom_extensao = self._extensao_camada_no_crs(layer, crs_projeto)
                union_geom = unir_geometrias(union_geom, geom_extensao)

        if union_geom is None or union_geom.isEmpty():
            self.mostrar_mensagem(self.tr("Não foram encontradas feições ou camadas visíveis para restringir a grade."), "Erro")
            return

        # 5) Extensão do Map Canvas, arredondada para múltiplos do espaçamento
        canvas = self.iface.mapCanvas()
        extent = canvas.extent()
        minx = extent.xMinimum()
        miny = extent.yMinimum()
        maxx = extent.xMaximum()
        maxy = extent.yMaximum()

        minx = math.floor(minx / intervalo) * intervalo
        miny = math.floor(miny / intervalo) * intervalo
        maxx = math.ceil(maxx / intervalo) * intervalo
        maxy = math.ceil(maxy / intervalo) * intervalo

        retangulo_geom = QgsGeometry.fromRect(QgsRectangle(minx, miny, maxx, maxy))

        # 6) Polígono externo = retângulo - union_geom
        poligono_externo = retangulo_geom.difference(union_geom)
        if poligono_externo.isEmpty():
            self.mostrar_mensagem(self.tr("As feições/camadas ocupam toda a área de trabalho. Nada sobra para a grade externa."), "Erro")
            return

        # 7) Criar camada de linhas: "Grade UTM Ajustada (Fora)"
        grade_layer = QgsVectorLayer(f'LineString?crs={crs_projeto.authid()}', self._nome_grade_utm(), 'memory')
        provider_lines = grade_layer.dataProvider()
        provider_lines.addAttributes([QgsField('ID', QMetaType.Type.Int)])
        grade_layer.updateFields()

        fid_lines = 1

        # 8) Calcular total para barra de progresso (linhas + pontos)
        qtd_horiz = int((maxy - miny) // intervalo) + 1
        qtd_vert = int((maxx - minx) // intervalo) + 1
        total_linhas = qtd_horiz + qtd_vert

        # Para pontos: cada x => 2 pontos (canto inferior e superior)
        # cada y => 2 pontos (canto esquerdo e direito)
        total_points = (qtd_vert * 2) + (max(0, qtd_horiz - 2) * 2)
        total_steps = total_linhas + total_points

        progressBar, progressMessageBar = self.iniciar_progress_bar(total_steps)
        steps_done = 0

        # 9) Criar linhas horizontais
        y_atual = miny
        while y_atual <= maxy:
            line_geom = QgsGeometry.fromPolylineXY([
                QgsPointXY(minx, y_atual),
                QgsPointXY(maxx, y_atual)])
            # Intersecta com poligono_externo => somente fora
            linha_fora = line_geom.intersection(poligono_externo)
            if not linha_fora.isEmpty():
                if linha_fora.isMultipart():
                    partes = linha_fora.asMultiPolyline()
                    for parte in partes:
                        feat_line = QgsFeature()
                        feat_line.setGeometry(QgsGeometry.fromPolylineXY(parte))
                        feat_line.setAttributes([fid_lines])
                        provider_lines.addFeature(feat_line)
                        fid_lines += 1
                else:
                    feat_line = QgsFeature()
                    feat_line.setGeometry(linha_fora)
                    feat_line.setAttributes([fid_lines])
                    provider_lines.addFeature(feat_line)
                    fid_lines += 1

            steps_done += 1
            progressBar.setValue(steps_done)
            y_atual += intervalo

        # 10) Criar linhas verticais
        x_atual = minx
        while x_atual <= maxx:
            line_geom = QgsGeometry.fromPolylineXY([
                QgsPointXY(x_atual, miny),
                QgsPointXY(x_atual, maxy)])
            linha_fora = line_geom.intersection(poligono_externo)
            if not linha_fora.isEmpty():
                if linha_fora.isMultipart():
                    partes = linha_fora.asMultiPolyline()
                    for parte in partes:
                        feat_line = QgsFeature()
                        feat_line.setGeometry(QgsGeometry.fromPolylineXY(parte))
                        feat_line.setAttributes([fid_lines])
                        provider_lines.addFeature(feat_line)
                        fid_lines += 1
                else:
                    feat_line = QgsFeature()
                    feat_line.setGeometry(linha_fora)
                    feat_line.setAttributes([fid_lines])
                    provider_lines.addFeature(feat_line)
                    fid_lines += 1

            steps_done += 1
            progressBar.setValue(steps_done)
            x_atual += intervalo

        # Adicionar a camada de linhas ao projeto
        QgsProject.instance().addMapLayer(grade_layer)

        # 11) Criar a camada de pontos: "Coordenadas Limites (Fora)"
        points_layer = QgsVectorLayer(f'Point?crs={crs_projeto.authid()}', self._nome_coordenadas_utm(), 'memory')
        provider_points = points_layer.dataProvider()
        provider_points.addAttributes([
            QgsField('ID', QMetaType.Type.Int),
            QgsField('X', QMetaType.Type.Double),
            QgsField('Y', QMetaType.Type.Double)])
        points_layer.updateFields()

        fid_points = 1

        # a) Pontos nas bordas verticais (x variando, y = miny ou maxy)
        x_val = minx
        while x_val <= maxx:
            for y_borda in [miny, maxy]:
                pt_geom = QgsGeometry.fromPointXY(QgsPointXY(x_val, y_borda))
                pt_fora = pt_geom.intersection(poligono_externo)
                if not pt_fora.isEmpty():
                    feat_pt = QgsFeature()
                    feat_pt.setGeometry(pt_geom)
                    feat_pt.setAttributes([fid_points, x_val, y_borda])
                    provider_points.addFeature(feat_pt)
                    fid_points += 1
            steps_done += 2
            progressBar.setValue(steps_done)
            x_val += intervalo

        # b) Pontos nas bordas horizontais (y variando, x = minx ou maxx)
        y_val = miny + intervalo
        while y_val < maxy:
            for x_borda in [minx, maxx]:
                pt_geom = QgsGeometry.fromPointXY(QgsPointXY(x_borda, y_val))
                pt_fora = pt_geom.intersection(poligono_externo)
                if not pt_fora.isEmpty():
                    feat_pt = QgsFeature()
                    feat_pt.setGeometry(pt_geom)
                    feat_pt.setAttributes([fid_points, x_borda, y_val])
                    provider_points.addFeature(feat_pt)
                    fid_points += 1
            steps_done += 2
            progressBar.setValue(steps_done)
            y_val += intervalo

        # Adicionar a camada de pontos ao projeto
        QgsProject.instance().addMapLayer(points_layer)

        # Configurar rótulos usando a função solicitada
        self.configurar_rotulos_na_camada_utm(points_layer)

        # 12) Limpar barra e exibir mensagem
        self.iface.messageBar().clearWidgets()
        self.mostrar_mensagem(self.tr("As camadas ajustadas '{grade}' e '{coordenadas}' foram criadas com sucesso.").format(grade=self._nome_grade_utm(), coordenadas=self._nome_coordenadas_utm()), "Sucesso")

    def escolher_local_para_salvar(self, nome_padrao, tipo_arquivo):
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
        fileName, _ = QFileDialog.getSaveFileName(self, self.tr("Salvar Camada"), nome_completo_proposto, tipo_arquivo, options=options)

        # Verifica se um nome de arquivo foi escolhido
        if fileName:
            # Atualiza o último diretório usado nas configurações do QGIS
            settings.setValue("lastDir", os.path.dirname(fileName))

            # Assegura que o arquivo tenha a extensão correta
            if not fileName.endswith(extensao):
                fileName += extensao

        return fileName  # Retorna o caminho completo do arquivo escolhido ou None se cancelado

    def exportar_para_dxf(self):
        """
        Exporta para DXF as camadas "Grade UTM" (linhas) e "Coordenadas Limites" (pontos com rótulos),
        utilizando ezdxf. Os rótulos são exportados como MText (quina: X e Y; topo/baixo: X; esquerda/direita: Y),
        e as linhas terão a cor cinza (color 8).
        """
        file_path = self.escolher_local_para_salvar("GradeUTM.dxf", self.tr("Arquivos DXF (*.dxf)"))
        if not file_path:
            return

        nome_grade = self._nome_grade_utm()
        nome_coordenadas = self._nome_coordenadas_utm()

        grade_layer = self.obter_camada_pelo_nome(nome_grade)
        pontos_layer = self.obter_camada_pelo_nome(nome_coordenadas)

        if not grade_layer or not pontos_layer:
            self.mostrar_mensagem(self.tr("Camadas '{grade}' e/ou '{coordenadas}' não encontradas.").format(grade=nome_grade, coordenadas=nome_coordenadas), "Erro")
            return

        doc = ezdxf.new(dxfversion='R2010')
        msp = doc.modelspace()
        if nome_grade not in doc.layers:
            doc.layers.new(name=nome_grade)

        if nome_coordenadas not in doc.layers:
            doc.layers.new(name=nome_coordenadas)

        # Exporta as linhas
        for feat in grade_layer.getFeatures():
            geom = feat.geometry()
            if geom is None:
                continue
            if geom.isMultipart():
                parts = geom.asMultiPolyline()
                for part in parts:
                    points = [(pt.x(), pt.y()) for pt in part]
                    msp.add_lwpolyline(points, dxfattribs={'layer': nome_grade, 'color': 8})
            else:
                part = geom.asPolyline()
                points = [(pt.x(), pt.y()) for pt in part]
                msp.add_lwpolyline(points, dxfattribs={'layer': nome_grade, 'color': 8})

        # Tamanho do texto
        scale_value = self.iface.mapCanvas().scale()
        char_height = 0.0025 * scale_value

        # Preparar extremos
        xs = []
        ys = []
        for feat in pontos_layer.getFeatures():
            pt = feat.geometry().asPoint()
            xs.append(pt.x())
            ys.append(pt.y())
        if not xs or not ys:
            self.mostrar_mensagem(self.tr("Nenhum ponto encontrado na camada '{coordenadas}'.").format(coordenadas=nome_coordenadas), "Erro")
            return

        min_x = min(xs)
        max_x = max(xs)
        min_y = min(ys)
        max_y = max(ys)
        tol = 1e-6

        # Exporta cada ponto como MText conforme regra das quinas
        for feat in pontos_layer.getFeatures():
            pt = feat.geometry().asPoint()
            x = pt.x()
            y = pt.y()
            # Detecta quina (ambos min/max)
            is_left = abs(x - min_x) < tol
            is_right = abs(x - max_x) < tol
            is_top = abs(y - max_y) < tol
            is_bottom = abs(y - min_y) < tol

            label = ""
            if (is_left or is_right) and (is_top or is_bottom):
                # Quina: mostra X e Y
                label = f"{x}\n{y}"
            elif is_top or is_bottom:
                label = str(x)
            elif is_left or is_right:
                label = str(y)
            # Senão, não mostra label (só para os limites)

            if label:
                mtext = msp.add_mtext(label, dxfattribs={'layer': nome_coordenadas, 'char_height': char_height})
                mtext.dxf.insert = (x, y)
                mtext.dxf.attachment_point = 5

        try:
            doc.saveas(file_path)
            self.mostrar_mensagem(self.tr("Exportação para DXF concluída: {file_path}").format(file_path=file_path), "Sucesso", duracao=3, caminho_pasta=os.path.dirname(file_path), caminho_arquivo=file_path)

        except Exception as e:
            self.mostrar_mensagem(self.tr("Erro ao salvar DXF: {error}").format(error=str(e)), "Erro")

    def updatePushButtonDXFState(self):
        """
        Atualiza o estado (habilitado ou não) do pushButtonDXF.
        O botão será habilitado somente se:
          - O projeto estiver em UTM (ou seja, CRS com 'UTM zone' na descrição);
          - As camadas "Grade UTM" e "Coordenadas Limites" existirem no projeto.
        """
        crs = QgsProject.instance().crs()
        # Se o projeto não estiver em UTM ou não houver CRS válido, desabilita o botão.
        if not crs or not self.esta_em_utm(crs):
            self.pushButtonDXF.setEnabled(False)
            return

        # Verifica se as camadas necessárias existem.
        grade_layer = self.obter_camada_pelo_nome(self._nome_grade_utm())
        coord_layer = self.obter_camada_pelo_nome(self._nome_coordenadas_utm())
        if grade_layer is None or coord_layer is None:
            self.pushButtonDXF.setEnabled(False)
        else:
            self.pushButtonDXF.setEnabled(True)

    def executar_criar_grade_geo_aj(self):
        """
        Cria uma grade geográfica (linhas horizontais/verticais e pontos de borda)
        respeitando uma folga exata de 0,5 segundos de arco das feições do projeto.
        """
        crs_proj = QgsProject.instance().crs()
        if not crs_proj.isGeographic():
            self.mostrar_mensagem(self.tr("O projeto não está em coordenadas geográficas."), "Erro")
            return

        segundos = self.spinBox_segundos.value()
        if segundos <= 0:
            self.mostrar_mensagem(self.tr("Espaçamento inválido. Defina um valor > 0."), "Erro")
            return
        intervalo = segundos / 3600.0      # graus

        # Folga de 0,5 segundos em graus
        RECUO_SEG = 0.5
        RECUO_DEG = RECUO_SEG / 3600.0

        self.remove_layers_if_exist([self._nome_grade_geo(), self._nome_coordenadas_geo(), "Grade Geografica", "Coordenadas Limites"])

        # Constrói diretamente a área de restrição com uma única folga.
        union_buffer = None

        def combinar_restricoes(base, nova):
            if nova is None or nova.isEmpty():
                return base
            return nova if base is None else base.combine(nova)

        for layer in QgsProject.instance().mapLayers().values():
            if not layer.isValid() or not self._camada_esta_visivel(layer) or self._is_satellite_provider(layer):
                continue

            if layer.type() == QgsMapLayer.LayerType.VectorLayer:
                for feature in layer.getFeatures():
                    geom = self._geometria_no_crs(feature.geometry(), layer.crs(), crs_proj)

                    if geom is None:
                        continue

                    restricao = geom.buffer(RECUO_DEG, 8)

                    if not restricao.isEmpty():
                        union_buffer = combinar_restricoes(union_buffer, restricao)

            elif layer.type() in (QgsMapLayer.LayerType.RasterLayer, QgsMapLayer.LayerType.MeshLayer):
                geom_extensao = self._extensao_camada_no_crs(layer, crs_proj)

                if geom_extensao is not None:
                    restricao = geom_extensao.buffer(RECUO_DEG, 8)
                    union_buffer = combinar_restricoes(union_buffer, restricao)

        if union_buffer is None or union_buffer.isEmpty():
            self.mostrar_mensagem(self.tr("Não foram encontradas feições ou camadas visíveis para restringir a grade."), "Erro")
            return

        # Limites alinhados ao grid
        ext = self.iface.mapCanvas().extent()
        minx = math.floor(ext.xMinimum() / intervalo) * intervalo
        miny = math.floor(ext.yMinimum() / intervalo) * intervalo
        maxx = math.ceil (ext.xMaximum() / intervalo) * intervalo
        maxy = math.ceil (ext.yMaximum() / intervalo) * intervalo

        # Criação das camadas
        linhas_lyr = QgsVectorLayer(f'LineString?crs={crs_proj.authid()}', self._nome_grade_geo(), 'memory')
        pl = linhas_lyr.dataProvider()
        pl.addAttributes([QgsField('ID', QMetaType.Type.Int)])
        linhas_lyr.updateFields()

        pts_lyr = QgsVectorLayer(f'Point?crs={crs_proj.authid()}', self._nome_coordenadas_geo(), 'memory')
        pp = pts_lyr.dataProvider()
        pp.addAttributes([
            QgsField('ID', QMetaType.Type.Int),
            QgsField('X',  QMetaType.Type.Double),
            QgsField('Y',  QMetaType.Type.Double),
            QgsField('X_DMS', QMetaType.Type.QString, len=20),
            QgsField('Y_DMS', QMetaType.Type.QString, len=20)])
        pts_lyr.updateFields()

        # Barra de progresso
        n_h = int((maxy - miny) // intervalo) + 1
        n_v = int((maxx - minx) // intervalo) + 1
        total = n_h + n_v + (n_h + n_v) * 2
        pbar, _ = self.iniciar_progress_bar(total)
        step = 0
        fid_l, fid_p = 1, 1
        pontos_criados = set()

        # Função para adicionar pontos só fora do buffer
        def add_ponto(x, y):
            nonlocal fid_p, step

            chave = (round(x, 10), round(y, 10))

            if chave not in pontos_criados:
                pontos_criados.add(chave)
                pt_geom = QgsGeometry.fromPointXY(QgsPointXY(x, y))

                if not pt_geom.intersects(union_buffer):
                    feature = QgsFeature()
                    feature.setGeometry(pt_geom)
                    feature.setAttributes([fid_p, x, y, self.dec_to_dms(x), self.dec_to_dms(y)])
                    pp.addFeature(feature)
                    fid_p += 1

            step += 1
            pbar.setValue(step)

        # Linhas horizontais (segmentos fora do buffer)
        y = miny
        while y <= maxy + 1e-12:
            linha = QgsGeometry.fromPolylineXY([QgsPointXY(minx, y), QgsPointXY(maxx, y)])
            fora = linha.difference(union_buffer)
            if not fora.isEmpty():
                parts = fora.asMultiPolyline() if fora.isMultipart() else [fora.asPolyline()]
                for seg in parts:
                    if seg:
                        f = QgsFeature()
                        f.setGeometry(QgsGeometry.fromPolylineXY(seg))
                        f.setAttributes([fid_l])
                        pl.addFeature(f)
                        fid_l += 1
            step += 1
            pbar.setValue(step)
            y += intervalo

        # Linhas verticais (segmentos fora do buffer)
        x = minx
        while x <= maxx + 1e-12:
            linha = QgsGeometry.fromPolylineXY([QgsPointXY(x, miny), QgsPointXY(x, maxy)])
            fora = linha.difference(union_buffer)
            if not fora.isEmpty():
                parts = fora.asMultiPolyline() if fora.isMultipart() else [fora.asPolyline()]
                for seg in parts:
                    if seg:
                        f = QgsFeature()
                        f.setGeometry(QgsGeometry.fromPolylineXY(seg))
                        f.setAttributes([fid_l])
                        pl.addFeature(f)
                        fid_l += 1
            step += 1
            pbar.setValue(step)
            x += intervalo

        QgsProject.instance().addMapLayer(linhas_lyr)

        # Pontos das bordas (apenas fora do buffer)
        for x in (minx, maxx):
            y = miny
            while y <= maxy + 1e-12:
                add_ponto(x, y)
                y += intervalo

        for y in (miny, maxy):
            x = minx
            while x <= maxx + 1e-12:
                add_ponto(x, y)
                x += intervalo

        QgsProject.instance().addMapLayer(pts_lyr)

        self.configurar_rotulos_na_camada(pts_lyr)
        self.iface.messageBar().clearWidgets()
        self.mostrar_mensagem(self.tr("As camadas ajustadas '{grade}' e '{coordenadas}' foram criadas com sucesso, com folga de 0,5 s.").format(grade=self._nome_grade_geo(), coordenadas=self._nome_coordenadas_geo()), "Sucesso")

    def atualizar_lineEditSRC(self):
        crs = QgsProject.instance().crs()
        if crs and crs.isValid():
            descricao = f"{crs.description()} (EPSG:{crs.postgisSrid()})"
        else:
            descricao = "SRC inválido"
        self.lineEditSRC.setText(descricao)
        self.lineEditSRC.setStyleSheet("color: blue;")
        self.lineEditSRC.setReadOnly(True)

    def ativar_src_geo(self):
        crs = QgsCoordinateReferenceSystem.fromEpsgId(4326)
        if crs.isValid():
            QgsProject.instance().setCrs(crs)
        else:
            self.mostrar_mensagem(self.tr("Não foi possível definir o SRC para WGS84."), "Erro")

    def updatePushButtonsSRC(self):
        """
        Habilita / desabilita pushButtonAtivarUTM e pushButtonAtivarGEO
        de acordo com o SRC atual do projeto.
        """
        crs = QgsProject.instance().crs()
        desc = crs.description().upper()

        em_geo = crs.isGeographic()
        em_utm = ("UTM" in desc) or ("+PROJ=UTM" in crs.toProj())

        self.pushButtonAtivarGEO.setEnabled(not em_geo)
        self.pushButtonAtivarUTM.setEnabled(not em_utm)

    def ativar_src_utm(self):
        """
        Define o SRC do projeto para SIRGAS 2000 / UTM de acordo
        com o fuso (zone) e o hemisfério do centro da tela.
        """
        # 1) Coordenadas do centro da tela em WGS-84
        canvas      = self.iface.mapCanvas()
        centro_map  = canvas.extent().center()
        crs_proj    = QgsProject.instance().crs()
        crs_wgs84   = QgsCoordinateReferenceSystem.fromEpsgId(4326)

        try:
            xform        = QgsCoordinateTransform(crs_proj, crs_wgs84, QgsProject.instance())
            centro_wgs84 = xform.transform(centro_map)
        except Exception as e:
            self.mostrar_mensagem(self.tr("Falha ao converter para WGS-84: {error}").format(error=str(e)), "Erro")
            return

        lon = centro_wgs84.x()
        lat = centro_wgs84.y()

        # 2) Cálculo do fuso UTM (1–60)
        zone = int((lon + 180) / 6) + 1
        zone = max(1, min(zone, 60))          # garante faixa válida

        # 3) Escolha do EPSG SIRGAS 2000
        if lat >= 0:                          # hemisfério Norte
            epsg = 31954 + zone               # 31970 → 16 N … 31976 → 22 N
        else:                                 # hemisfério Sul
            epsg = 31960 + zone               # 31977 → 17 S … 31983 → 23 S

        crs_utm = QgsCoordinateReferenceSystem.fromEpsgId(epsg)

        if not crs_utm.isValid():
            self.mostrar_mensagem(self.tr("EPSG {epsg} não é válido.").format(epsg=epsg), "Erro")
            return

        # 4) Aplica o SRC ao projeto
        QgsProject.instance().setCrs(crs_utm)
        self.mostrar_mensagem(self.tr("SRC alterado para {description} (EPSG:{epsg}).").format(description=crs_utm.description(), epsg=epsg), "Sucesso")

    def update_buttons_by_src(self):
        """
        Habilita ou desabilita botões de acordo com o SRC atual:
        - Se geográfico: desabilita botões e widgets de UTM.
        - Se UTM: desabilita botões e widgets de grade geográfica.
        """
        crs = QgsProject.instance().crs()
        is_geo = crs.isGeographic()
        is_utm = "UTM" in crs.description().upper() or "+proj=utm" in crs.toProj().lower()

        # Geográfica
        self.pushButtonGradeGeo.setEnabled(is_geo)
        self.pushButtonGradeGeoAj.setEnabled(is_geo)
        self.spinBox_segundos.setEnabled(is_geo)

        # UTM
        self.pushButtonGradeUTM.setEnabled(is_utm)
        self.pushButtonGradeAj.setEnabled(is_utm)
        self.spinBox_espacamento.setEnabled(is_utm)

    def _is_satellite_provider(self, layer: QgsMapLayer) -> bool:
        """
        Retorna True se a camada for imagem de satélite/tiles de provedor online
        (XYZ, WMTS, WMS-tile, ArcGIS, MapTiler, etc.).
        """
        if layer.type() != QgsMapLayer.LayerType.RasterLayer:
            return False

        # ProviderType costuma vir como 'wms', 'xyz', 'wmts', 'arcgismapserver', ...
        prov = (layer.providerType() or "").lower()
        if prov in {"xyz", "wmts", "wms", "arcgismapserver", "gdalwms"}:
            return True

        # Fallback: fonte contém URL http(s) e 'sat', 'worldimagery', 'google', 'bing'…
        src_lower = layer.source().lower()
        if src_lower.startswith("http") and any(k in src_lower for k in
            ("sat", "worldimagery", "google", "bing", "tileserver", "maptile")):
            return True

        return False