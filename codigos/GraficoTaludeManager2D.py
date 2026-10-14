from qgis.PyQt.QtWidgets import QDialog, QCheckBox, QComboBox, QPushButton, QGraphicsView, QGraphicsScene, QGraphicsPixmapItem, QTableWidget, QTableWidgetItem, QAbstractItemView, QFileDialog, QListWidgetItem, QProgressBar, QLabel, QGraphicsPathItem, QApplication
from qgis.core import QgsProject, QgsRasterLayer, QgsMapSettings, QgsMapRendererCustomPainterJob, Qgis, QgsVectorLayer, QgsField, QgsFeature, QgsPointXY, QgsLayerTreeLayer, QgsGeometry, QgsDistanceArea, edit, QgsVector, QgsCoordinateTransform, QgsPalLayerSettings, QgsProperty, QgsVectorLayerSimpleLabeling, QgsRenderContext, QgsRuleBasedRenderer, QgsMarkerSymbol, QgsMapLayer, QgsFeatureRequest, QgsVectorFileWriter, QgsProviderRegistry
from qgis.PyQt.QtGui import QImage, QPainter, QPixmap, QColor, QPainterPath, QFont, QDesktopServices
from qgis.PyQt.QtCore import Qt, QRectF, QPointF, QSize, QSettings, QTimer, QSignalBlocker, QMetaType, QUrl
from qgis.PyQt import QtWidgets, QtGui, QtCore, uic
from pyqtgraph import InfiniteLine, TextItem
from ezdxf import colors as ez_colors
from qgis.gui import QgsMapCanvas
from ezdxf.math import Matrix44
from qgis.utils import iface
import pyqtgraph as pg
pg.setConfigOptions(antialias=True)
import numpy as np
import ezdxf
import time
import math
import os
import re

def integrar_trapezio(y, x):
    """
    Integra pelo método dos trapézios sem depender de np.trapz/np.trapezoid.
    """
    y = np.asarray(y, dtype=float)
    x = np.asarray(x, dtype=float)

    validos = np.isfinite(y) & np.isfinite(x)
    if np.count_nonzero(validos) < 2:
        return 0.0

    y = y[validos]
    x = x[validos]

    return float(np.sum((y[1:] + y[:-1]) * (x[1:] - x[:-1]) / 2.0))

if not hasattr(np, "trapz"):
    np.trapz = integrar_trapezio

FORM_CLASS, _ = uic.loadUiType(os.path.join(
    os.path.dirname(__file__), 'GraficoPyQtGraphTalude.ui'))

class GraficoManager(QDialog, FORM_CLASS):
    def __init__(self, parent=None):
        """Constructor."""
        super(GraficoManager, self).__init__(parent)
        # Configura a interface do usuário a partir do Designer.
        self.setupUi(self)
        # Altera o título da janela
        self.setWindowTitle(self.tr("Gráfico com Talude 2D"))

        # Salva as referências para a interface do QGIS e o diálogo fornecidos
        self.iface = iface

        self._signals_connected = False
        self._layer_name_conn = {}  # {layer_id: callable}

        # Cria uma cena gráfica para o QGraphicsView
        self.scene = QGraphicsScene()
        self.graphicsViewRaster.setScene(self.scene)

        # Inicializa o ComboBox de Raster e Camadas
        self.init_combo_box_raster()
        self.init_combo_box_camadas()

        # Desativa o doubleSpinBoxDistancias inicialmente
        self.doubleSpinBoxDistancias.setEnabled(False)

        self._updating_table = False
        self._updating_graph = False
        self._excluindo_camadas = False
        self._suspender_render_raster = False

        # Controle da abertura do GeoPackage
        self._carregando_geopackage = False
        self._abertura_geopackage_em_andamento = False
        self._render_abertura_pendente = False
        self._progressBarAberturaGpkg = None
        self._progressMessageBarAberturaGpkg = None

        # Configura a janela para permitir minimizar, maximizar e fechar
        self.setWindowFlags(self.windowFlags() | Qt.WindowType.WindowMinimizeButtonHint | Qt.WindowType.WindowMaximizeButtonHint | Qt.WindowType.WindowCloseButtonHint)

        self.tableWidgetLista_layer_connected = None

        self._configurar_tablewidget_lista()

        self._init_h_spins_tab_jump()

        # Conecta os sinais aos slots
        self.connect_signals()

        # Configura a sincronização entre desníveis e cotas inicial/final
        self._configurar_sincronizacao_cotas()

        self._atualizar_estado_pushButtonSalvar()

    def connect_signals(self):
        """Conecta sinais do projeto e de camadas sem duplicar conexões."""
        if self._signals_connected:
            return

        self._signals_connected = True

        # camadas já existentes
        for lyr in QgsProject.instance().mapLayers().values():
            self._connect_layer_name_changed(lyr)

        # camadas novas / removidas
        # (varia por versão, mas essas duas são bem comuns no QGIS 3.x)
        try:
            QgsProject.instance().layerWasAdded.connect(self._on_project_layer_added)
        except Exception:
            pass  # nosec B110

        try:
            QgsProject.instance().layersWillBeRemoved.connect(self._on_project_layers_will_be_removed)
        except Exception:
            pass  # nosec B110

        # Conecta o sinal de adição de camada raster
        QgsProject.instance().layersAdded.connect(self.update_combo_box_raster)

        # Conecta os sinais aos slots
        self.comboBoxRaster.currentIndexChanged.connect(self.display_raster)

        # Conecta o sinal de remoção de camada
        QgsProject.instance().layersRemoved.connect(self.update_combo_box)

        # Desconectar todos os sinais para evitar múltiplas conexões
        try:
            QgsProject.instance().layersAdded.disconnect(self.handle_layers_added)
        except TypeError:
            pass  # nosec B110 | O sinal não estava conectado anteriormente

        # Conecta os RadioButtons para selecionar linhas ou pontos
        self.radioButtonLinhas.clicked.connect(self.update_combo_box_camadas)
        self.radioButtonPontos.clicked.connect(self.update_combo_box_camadas)

        # Conecta os RadioButtons ao método que seleciona a aba no tabWidget
        self.radioButtonLinhas.toggled.connect(self.selecionar_aba_tab_widget)
        self.radioButtonPontos.toggled.connect(self.selecionar_aba_tab_widget)

        # Conecta o sinal de alteração do comboBoxCamadas para carregar atributos
        self.comboBoxCamadas.currentIndexChanged.connect(self.load_layer_attributes)

        # Conecta o sinal de seleção no tableWidgetLista
        self.tableWidgetLista.itemSelectionChanged.connect(self.table_selection_changed)

        self.tableWidgetLista.setSelectionBehavior(QAbstractItemView.SelectionBehavior.SelectRows)
        self.tableWidgetLista.setSelectionMode(QAbstractItemView.SelectionMode.MultiSelection)

        # Conecta os RadioButtons para selecionar linhas ou pontos
        self.radioButtonLinhas.toggled.connect(self.update_doubleSpinBoxDistancias_state)
        
        # Conecta o sinal de alteração do comboBoxCamadas para carregar atributos
        self.comboBoxCamadas.currentIndexChanged.connect(self.update_doubleSpinBoxDistancias_state)

        # Conecta o botão pushButtonCalcular ao cálculo dos pontos
        self.pushButtonCalcular.clicked.connect(self.calcular_pontos)

        # Conecta o sinal de mudança de valor do doubleSpinBoxDistancias
        self.doubleSpinBoxDistancias.valueChanged.connect(self.verificar_condicoes_calcular)

        # Conecta o sinal de mudança de seleção no tableWidgetLista
        self.tableWidgetLista.itemSelectionChanged.connect(self.verificar_condicoes_calcular)

        # Conecta o botão pushButtonGerar ao método gerar_pontos_com_z
        self.pushButtonGerar.clicked.connect(self.gerar_pontos_com_z)
        
        # Atualiza o comboBoxGrupoZ quando uma nova camada é adicionada
        QgsProject.instance().layersAdded.connect(self.update_combo_box_grupo_z)
        
        # Atualiza o comboBoxGrupoZ quando uma camada é removida
        QgsProject.instance().layersRemoved.connect(self.update_combo_box_grupo_z)
        
        # Atualiza o comboBoxGrupoZ quando o nome de uma camada é alterado
        for layer in QgsProject.instance().mapLayers().values():
            layer.nameChanged.connect(self.update_combo_box_grupo_z)

        # Conecta o comboBoxGrupoZ à função que carrega atributos no tableWidgetLista2
        self.comboBoxGrupoZ.currentIndexChanged.connect(self.load_layer_attributes_grupo_z)

        # Conecta a seleção do tableWidgetLista2 ao método que sincroniza com a camada
        self.tableWidgetLista2.itemSelectionChanged.connect(self.table_selection_changed_grupo_z)

        # Update the comboBoxGrupoZ when a layer is about to be removed
        QgsProject.instance().layersWillBeRemoved.connect(self.limpar_tableWidgetLista2)

        # Conecta o sinal de adição de camada
        QgsProject.instance().layersAdded.connect(self.update_combo_box_camadas)

        # Conecta o sinal de alteração do nome da camada
        for layer in QgsProject.instance().mapLayers().values():
            layer.nameChanged.connect(self.update_combo_box_camadas)

        # Conecta as alterações dos doubleSpinBoxHinicial e doubleSpinBoxHFinal
        self.doubleSpinBoxHinicial.valueChanged.connect(self.on_spinbox_value_changed)
        self.doubleSpinBoxHFinal.valueChanged.connect(self.on_spinbox_value_changed)

        # Conecta o evento de alteração de seleção ao verificar as condições para o pushButtonGerar
        self.tableWidgetLista.itemSelectionChanged.connect(self.verificar_estado_pushButtonGerar)

        # #conectar este método ao sinal currentIndexChanged do comboBoxGrupoZ
        self.comboBoxGrupoZ.currentIndexChanged.connect(self.handle_support_points_layer)

        # Conecta as alterações do Corte/Aterro Inicial e Final
        self.tableWidgetLista2.cellChanged.connect(self.update_graph_from_table_widget)

        #Conecta a alteração da cor do fundo do Gráfico
        self.checkBoxFundo.stateChanged.connect(self.update_graph_background_color)

        #Conecta o pushButtonExportarDXF
        self.pushButtonExportarDXF.clicked.connect(self.exportar_dxf)

        # Conectar o botão pushButtonDel à função delete_selected_layer
        self.pushButtonDel.clicked.connect(self.delete_selected_layer)

        # Conecta o botão pushButtonFechar ao método de fechamento
        self.pushButtonFechar.clicked.connect(self.close_dialog)

        # Conecta o botão pushButtonDel
        self.comboBoxGrupoZ.currentIndexChanged.connect(self.atualizar_estado_pushButtonDel)

        # Acrescente estas conexões onde já faz os connects
        self.radioButtonPontos.toggled.connect(self.verificar_estado_pushButtonGerar)
        self.radioButtonLinhas.toggled.connect(self.verificar_estado_pushButtonGerar)

        QgsProject.instance().layersRemoved.connect(self._on_layers_removed_clear_graph)
        
        # Conecta as alterações do btoçao pushButtonGera as mudanças no comboBoxCamadas
        self.comboBoxCamadas.currentIndexChanged.connect(self.verificar_estado_pushButtonGerar)
        self.comboBoxCamadas.currentIndexChanged.connect(self.verificar_condicoes_calcular)
        self.radioButtonLinhas.toggled.connect(self.verificar_condicoes_calcular)
        self.radioButtonPontos.toggled.connect(self.verificar_condicoes_calcular)

        # Atualiza o gráfico quando a existência dos taludes for alterada
        self.checkBoxTaludeI.toggled.connect(self._on_estado_taludes_alterado)
        self.checkBoxTaludeF.toggled.connect(self._on_estado_taludes_alterado)

        # Atualiza o estado do botão quando camadas forem adicionadas ou removidas
        QgsProject.instance().layersAdded.connect(self._agendar_atualizacao_pushButtonSalvar)

        QgsProject.instance().layersRemoved.connect(self._agendar_atualizacao_pushButtonSalvar)

        self.pushButtonSalvar.clicked.connect(self.salvar_grupos_geopackage)

        self.pushButtonAbrir.clicked.connect(self.abrir_grupos_geopackage)

        self.pushButtonUsar.clicked.connect(self.abrir_ajuda_uso)

    def abrir_ajuda_uso(self):
        """Abre o guia de utilização do Gráfico com Talude 2D."""

        dialog_existente = getattr(
            self,
            "_dialogo_ajuda_uso",
            None)

        if dialog_existente is not None:
            try:
                dialog_existente.show()
                dialog_existente.raise_()
                dialog_existente.activateWindow()
                return

            except RuntimeError:
                self._dialogo_ajuda_uso = None

        dialog = QDialog(self)
        self._dialogo_ajuda_uso = dialog

        dialog.setWindowTitle(
            self.tr("Como usar - Gráfico com Talude 2D"))

        dialog.setWindowModality(
            Qt.WindowModality.NonModal)

        dialog.resize(780, 700)
        dialog.setMinimumSize(640, 520)

        layout = QtWidgets.QVBoxLayout(dialog)
        layout.setContentsMargins(10, 10, 10, 10)
        layout.setSpacing(8)

        texto = QtWidgets.QTextBrowser(dialog)

        partes = [
            f"<h2>{self.tr('Gráfico com Talude 2D')}</h2>",

            f"<p>{self.tr('Esta ferramenta permite criar e analisar um perfil de corte e aterro sobre o terreno natural. A partir de um MDT e de pontos ou linhas do projeto, o plugin obtém as cotas do terreno, calcula as cotas de projeto, gera o perfil longitudinal, representa os taludes e calcula as áreas de corte e aterro.')}</p>",

            f"<h3>{self.tr('Ideia geral de funcionamento')}</h3>",

            f"<p>{self.tr('O MDT representa o terreno natural. Os pontos utilizados no perfil recebem a cota Z do raster e uma cota de projeto NovoZ. A diferença entre NovoZ e Z determina se existe corte ou aterro. O gráfico compara a superfície projetada com o terreno, calcula as áreas entre os dois perfis e pode acrescentar taludes nas extremidades.')}</p>",

            f"<hr><h3>{self.tr('Fluxo recomendado')}</h3>",

            "<ol>",

            f"<li><b>{self.tr('Selecione o MDT')}</b><br>"
            f"{self.tr('Escolha no campo de raster o MDT que representa o terreno natural. As cotas Z e os pontos de apoio do perfil serão obtidos a partir desse raster.')}</li><br>",

            f"<li><b>{self.tr('Escolha como deseja iniciar o perfil')}</b><br>"
            f"{self.tr('A ferramenta pode trabalhar a partir de uma camada de linhas ou diretamente a partir de uma camada de pontos. Selecione a opção correspondente e escolha a camada que será utilizada.')}</li><br>",

            f"<li><b>{self.tr('Se estiver trabalhando com linhas, gere os pontos do perfil')}</b><br>"
            f"{self.tr('Selecione uma ou mais linhas na tabela, informe a equidistância desejada e clique em Calcular. O plugin distribui pontos ao longo de cada linha selecionada e cria as respectivas camadas no grupo Pontos de Linhas.')}</li><br>",

            f"<li><b>{self.tr('Selecione os pontos que formarão o perfil')}</b><br>"
            f"{self.tr('Ative a opção Pontos, escolha a camada desejada e selecione pelo menos dois pontos na tabela. A ordem do perfil é determinada pelo campo ID, por isso é importante que os IDs representem corretamente a sequência dos pontos.')}</li><br>",

            f"<li><b>{self.tr('Defina o desnível ou as cotas de projeto')}</b><br>"
            f"{self.tr('Informe os valores inicial e final do perfil. É possível trabalhar pelo desnível em relação ao terreno ou diretamente pelas cotas inicial e final. Esses controles são sincronizados automaticamente.')}</li><br>",

            f"<li><b>{self.tr('Gere os Pontos com Z')}</b><br>"
            f"{self.tr('Clique em Gerar. O plugin consulta o MDT para obter a cota Z de cada ponto e cria uma nova camada contendo ID, X, Y, Z, NovoZ, distância acumulada e desnível. Essa camada é adicionada ao grupo Pontos com Z.')}</li><br>",

            f"<li><b>{self.tr('Analise o perfil de corte e aterro')}</b><br>"
            f"{self.tr('Ao selecionar uma camada do grupo Pontos com Z, o plugin cria os pontos de apoio do terreno e monta o gráfico. A linha de projeto representa NovoZ e a linha do terreno representa as cotas obtidas do MDT.')}</li><br>",

            f"<li><b>{self.tr('Ajuste as cotas quando necessário')}</b><br>"
            f"{self.tr('As cotas inicial e final podem ser alteradas posteriormente. Ao modificar esses valores, o perfil é recalculado e o gráfico é atualizado. Os valores da tabela de Pontos com Z também podem ser editados para ajustes específicos.')}</li><br>",

            f"<li><b>{self.tr('Configure os taludes')}</b><br>"
            f"{self.tr('Use as opções de talude inicial e final para definir em quais extremidades o perfil deverá encontrar o terreno natural. Ao marcar ou desmarcar um talude, o gráfico, as hachuras e os cálculos de área são atualizados automaticamente.')}</li><br>",

            f"<li><b>{self.tr('Confira corte, aterro e inclinações')}</b><br>"
            f"{self.tr('O painel de informações apresenta a inclinação do perfil de corte ou aterro, a inclinação média do terreno e as áreas de corte e aterro da seção. No gráfico, o aterro é representado em azul e o corte em vermelho.')}</li><br>",

            f"<li><b>{self.tr('Exporte o resultado para DXF')}</b><br>"
            f"{self.tr('Depois que o gráfico estiver disponível, utilize Exportar DXF para gerar o desenho do perfil. A exportação inclui o terreno natural, o perfil de projeto, os taludes, as áreas de corte e aterro e as informações do gráfico. Quando a opção correspondente estiver habilitada, a camada de pontos também pode ser exportada nas coordenadas originais.')}</li><br>",

            f"<li><b>{self.tr('Salve o trabalho')}</b><br>"
            f"{self.tr('O botão Salvar grava em um único GeoPackage as camadas produzidas pelo módulo nos grupos Pontos com Z, Pontos Apoio e Pontos de Linhas. O botão Abrir restaura posteriormente essas camadas e reconstrói os grupos automaticamente.')}</li>",

            "</ol>",

            f"<hr><h3>{self.tr('Entendendo os principais valores')}</h3>",

            f"<p><b>Z:</b> {self.tr('cota do terreno natural obtida do MDT.')}</p>",

            f"<p><b>{self.tr('Novo Z')}:</b> {self.tr('cota de projeto utilizada para formar o perfil de corte e aterro.')}</p>",

            f"<p><b>{self.tr('Desnível')}:</b> {self.tr('diferença entre a cota de projeto NovoZ e a cota do terreno Z. Valor positivo representa aterro e valor negativo representa corte.')}</p>",

            f"<p><b>{self.tr('Distância acumulada')}:</b> {self.tr('distância percorrida ao longo da sequência de pontos utilizada no eixo horizontal do perfil.')}</p>",

            f"<hr><h3>{self.tr('Corte e Aterro')}</h3>",

            f"<p>{self.tr('Quando NovoZ está acima do terreno natural, existe aterro. Quando NovoZ está abaixo do terreno natural, existe corte. O plugin identifica as regiões de transição, calcula as áreas separadamente e atualiza o resultado conforme as cotas ou os taludes são modificados.')}</p>",

            f"<p>{self.tr('As áreas apresentadas são áreas da seção transversal do perfil, expressas em metros quadrados. Elas não representam diretamente volume de corte ou aterro.')}</p>",

            f"<hr><h3>{self.tr('Taludes')}</h3>",

            f"<p>{self.tr('Os taludes inicial e final são opcionais. Quando habilitados, prolongam o perfil de projeto até sua interseção com o terreno natural. Isso permite representar corretamente a transição entre a superfície projetada e o terreno existente.')}</p>",

            f"<hr><h3>{self.tr('Organização das camadas')}</h3>",

            "<ul>",

            f"<li><b>{self.tr('Pontos de Linhas')}:</b> "
            f"{self.tr('contém os pontos distribuídos ao longo das linhas de origem.')}</li>",

            f"<li><b>{self.tr('Pontos com Z')}:</b> "
            f"{self.tr('contém os pontos efetivamente utilizados no perfil, com terreno, projeto, distância acumulada e desnível.')}</li>",

            f"<li><b>{self.tr('Pontos Apoio')}:</b> "
            f"{self.tr('contém a amostragem mais detalhada do MDT utilizada para representar o terreno natural no gráfico.')}</li>",

            "</ul>",

            f"<hr><h3>{self.tr('Dicas importantes')}</h3>",

            "<ul>",

            f"<li>{self.tr('Confira a ordem dos IDs dos pontos antes de gerar o perfil, pois essa ordem define a sequência utilizada no cálculo.')}</li>",

            f"<li>{self.tr('Utilize um MDT compatível com a área e com o sistema de referência das camadas utilizadas.')}</li>",

            f"<li>{self.tr('Ao gerar pontos a partir de linhas, escolha uma equidistância adequada ao nível de detalhe desejado.')}</li>",

            f"<li>{self.tr('Use as cotas inicial e final para ajustes gerais do greide e a tabela para ajustes pontuais.')}</li>",

            f"<li>{self.tr('Confira se os taludes inicial e final realmente devem fazer parte da seção antes de utilizar as áreas calculadas.')}</li>",

            f"<li>{self.tr('Salve o GeoPackage depois de concluir alterações importantes para poder reconstruir o trabalho posteriormente.')}</li>",

            "</ul>",

            f"<hr><p><b>{self.tr('Resumo:')}</b> "
            f"{self.tr('MDT + Linhas/Pontos → Pontos do Perfil → Z/NovoZ → Pontos com Z → Terreno Natural → Taludes → Corte/Aterro → DXF → Salvar.')}</p>"]

        texto.setHtml("".join(partes))
        texto.setOpenExternalLinks(False)

        layout.addWidget(texto, 1)

        layout_botoes = QtWidgets.QHBoxLayout()
        layout_botoes.addStretch()

        botao_fechar = QPushButton(self.tr("Fechar"))

        botao_fechar.setMinimumWidth(100)
        botao_fechar.clicked.connect(dialog.close)

        layout_botoes.addWidget(botao_fechar)
        layout.addLayout(layout_botoes)

        dialog.show()
        dialog.raise_()
        dialog.activateWindow()

    def _atualizacoes_camadas_suspensas(self):
        """
        Indica se os sinais automáticos das camadas devem aguardar
        a operação atual.
        """
        return (getattr(self, "_excluindo_camadas", False)
            or getattr(self, "_carregando_geopackage", False))

    def _connect_layer_name_changed(self, layer):
        if not isinstance(layer, QgsMapLayer):
            return

        lid = layer.id()
        if lid in self._layer_name_conn:
            return  # ✅ já conectado, não duplica

        # Guardar o callable é essencial para conseguir dar disconnect depois
        def _cb(_lid=lid):
            lyr = QgsProject.instance().mapLayer(_lid)
            new_name = lyr.name() if lyr else ""
            self._on_any_layer_renamed(_lid, new_name)

        try:
            layer.nameChanged.connect(_cb)
            self._layer_name_conn[lid] = _cb
        except Exception:
            pass  # nosec B110

    def _disconnect_layer_name_changed(self, layer_id):
        cb = self._layer_name_conn.pop(layer_id, None)
        if cb is None:
            return

        lyr = QgsProject.instance().mapLayer(layer_id)
        if lyr is None:
            return

        try:
            lyr.nameChanged.disconnect(cb)
        except Exception:
            pass  # nosec B110

    def _on_project_layer_added(self, layer):
        self._connect_layer_name_changed(layer)

    def _on_project_layers_will_be_removed(self, layer_ids):
        # layer_ids normalmente é uma lista de IDs (QStringList)
        for lid in list(layer_ids):
            self._disconnect_layer_name_changed(lid)

    def _on_any_layer_renamed(self, layer_id, new_name):
        """Aqui você chama sua rotina que atualiza combos/listas."""
        # Exemplo:
        # self._rebuild_layer_comboboxes()
        # ou self._sync_combo_layers()
        self.atualizar_camadas_em_comboboxes()  # ajuste para o seu nome real

    def disconnect_signals(self):
        """Desconecta tudo para não deixar sinais fantasmas."""
        try:
            self._fechar_progresso_abertura_geopackage()

        except Exception:
            pass  # nosec B110

        if not self._signals_connected:
            return

        prj = QgsProject.instance()

        try:
            prj.layerWasAdded.disconnect(self._on_project_layer_added)
        except Exception:
            pass  # nosec B110

        try:
            prj.layersWillBeRemoved.disconnect(self._on_project_layers_will_be_removed)
        except Exception:
            pass  # nosec B110

        # Sinais globais do projeto conectados por esta janela. Sem esta limpeza,
        # reabrir o diálogo pode acumular callbacks e tornar as operações lentas.
        for signal, slot in (
            (prj.layersAdded, self.update_combo_box_raster),
            (prj.layersRemoved, self.update_combo_box),
            (prj.layersAdded, self.update_combo_box_grupo_z),
            (prj.layersRemoved, self.update_combo_box_grupo_z),
            (prj.layersWillBeRemoved, self.limpar_tableWidgetLista2),
            (prj.layersAdded, self.update_combo_box_camadas),
            (prj.layersRemoved, self._on_layers_removed_clear_graph),
            (prj.layersAdded, self._agendar_atualizacao_pushButtonSalvar),
            (prj.layersRemoved, self._agendar_atualizacao_pushButtonSalvar)):

            try:
                signal.disconnect(slot)

            except Exception:
                pass  # nosec B110

        # desconecta nameChanged de todas as camadas que registramos
        for lid in list(self._layer_name_conn.keys()):
            self._disconnect_layer_name_changed(lid)

        self._signals_connected = False

    def closeEvent(self, event):
        """
        Fecha com segurança:
        - desconecta sinais (evita duplicação/eco e objetos deletados)
        - tenta restaurar maptool anterior
        - limpa referências internas
        """
        # 1) Evita reentrância (às vezes closeEvent pode ser chamado mais de 1 vez)
        if getattr(self, "_is_closing", False):
            try:
                event.accept()
            except Exception:
                pass  # nosec B110
            return
        self._is_closing = True

        # 2) Desconectar sinais do plugin/projeto/camadas
        try:
            # Se você implementou o disconnect_signals que te passei antes:
            if hasattr(self, "disconnect_signals"):
                self.disconnect_signals()
        except Exception:
            pass  # nosec B110

        # 3) Restaurar map tool anterior (se você usa QgsMapTool)
        try:
            if hasattr(self, "iface") and self.iface and hasattr(self, "_prev_map_tool"):
                if self._prev_map_tool is not None:
                    self.iface.mapCanvas().setMapTool(self._prev_map_tool)
        except Exception:
            pass  # nosec B110

        # 4) Se você criou rubber bands / temporários, tente limpar
        try:
            if hasattr(self, "_rb") and self._rb is not None:
                try:
                    self._rb.reset(True)
                except Exception:
                    pass  # nosec B110
                self._rb = None
        except Exception:
            pass  # nosec B110

        # 5) Limpar refs internas comuns (ajuste para o seu plugin)
        for attr in (
            "_orig_geoms",
            "_layer_name_conn",
            "_inun_layer_id",
            "_recorte_layer_id",
            "_union_mascara",
            "_task",
            "_tasks"):
            if hasattr(self, attr):
                try:
                    setattr(self, attr, {} if attr in ("_orig_geoms", "_layer_name_conn", "_tasks") else None)
                except Exception:
                    pass  # nosec B110

        # 6) Aceitar e chamar o closeEvent da superclasse (importante)
        try:
            event.accept()
        except Exception:
            pass  # nosec B110

        try:
            super().closeEvent(event)
        except Exception:
            pass  # nosec B110

    def init_combo_box_camadas(self):
        """Inicializa o combo box de camadas (linhas e polígonos)"""
        self.comboBoxCamadas.clear()
        self.update_combo_box_camadas()

    def init_combo_box_raster(self):
        """
        Inicializa o comboBox para seleção de camadas raster disponíveis no projeto.
        """
        # Armazena o ID da camada raster atualmente selecionada
        current_raster_id = self.comboBoxRaster.currentData()
        
        # Obtém todas as camadas do projeto atual
        layers = QgsProject.instance().mapLayers().values()
        
        # Filtra apenas camadas raster
        raster_layers = [layer for layer in layers if isinstance(layer, QgsRasterLayer)]
        
        # Limpa o ComboBox antes de adicionar itens
        self.comboBoxRaster.clear()
        
        # Adiciona as camadas raster ao ComboBox
        for raster_layer in raster_layers:
            self.comboBoxRaster.addItem(raster_layer.name(), raster_layer.id())
        
        # Restaura a seleção anterior, se possível
        if current_raster_id:
            index = self.comboBoxRaster.findData(current_raster_id)
            if index != -1:
                self.comboBoxRaster.setCurrentIndex(index)
            else:
                # Seleciona a última camada raster, se existir
                if raster_layers:
                    self.comboBoxRaster.setCurrentIndex(self.comboBoxRaster.count() - 1)
        else:
            # Seleciona a última camada raster, se existir
            if raster_layers:
                self.comboBoxRaster.setCurrentIndex(self.comboBoxRaster.count() - 1)
        
        # Atualiza a exibição do raster
        self.display_raster()

    def update_combo_box_raster(self, layers):
        """Atualiza o comboBoxRaster quando novas camadas são adicionadas ao projeto."""
        if self._atualizacoes_camadas_suspensas():
            return

        # Verifica se há novas camadas raster entre as adicionadas
        raster_layers_added = [layer for layer in layers if isinstance(layer, QgsRasterLayer)]
        if raster_layers_added:
            # Atualiza o comboBoxRaster
            self.init_combo_box_raster()
            # Seleciona a última camada raster adicionada
            self.comboBoxRaster.setCurrentIndex(self.comboBoxRaster.count() - 1)
            # Atualiza a exibição do raster
            self.display_raster()

    def _traduzir_cabecalhos_grafico(self, fields):
        """Retorna nomes traduzíveis apenas para exibição no cabeçalho da tabela."""
        cabecalhos = {
            "ID": self.tr("ID"),
            "X": self.tr("X"),
            "Y": self.tr("Y"),
            "Z": self.tr("Z"),
            "NovoZ": self.tr("Novo Z"),
            "dist_acumulada": self.tr("Distância acumulada"),
            "Desnivel": self.tr("Desnível"),
            "Acumula_dist": self.tr("Distância acumulada"),
            "Znovo": self.tr("Novo Z")}

        return [cabecalhos.get(field.name(), field.name()) for field in fields]

    def load_layer_attributes_grupo_z(self):
        """Carrega os atributos da camada selecionada no comboBoxGrupoZ no tableWidgetLista2,
        guardando o FID no Qt.UserRole (coluna 0) e sincronizando seleção mapa <-> tabela.
        """
        # layer atual
        selected_layer_id = self.comboBoxGrupoZ.currentData()
        layer = QgsProject.instance().mapLayer(selected_layer_id)

        # se inválida, limpa tudo e desconecta anterior
        if not isinstance(layer, QgsVectorLayer):
            prev = getattr(self, "_sel_conn_layer_z", None)
            if isinstance(prev, QgsVectorLayer):
                try:
                    prev.selectionChanged.disconnect(self.layer_selection_changed_grupo_z)
                except (TypeError, RuntimeError):
                    pass  # nosec B110
            self._sel_conn_layer_z = None

            self.tableWidgetLista2.clear()
            self.tableWidgetLista2.setRowCount(0)
            self.tableWidgetLista2.setColumnCount(0)
            return

        # desconecta layer anterior
        prev = getattr(self, "_sel_conn_layer_z", None)
        if isinstance(prev, QgsVectorLayer):
            try:
                prev.selectionChanged.disconnect(self.layer_selection_changed_grupo_z)
            except (TypeError, RuntimeError):
                pass  # nosec B110

        # conecta layer atual
        self._sel_conn_layer_z = layer
        try:
            layer.selectionChanged.connect(self.layer_selection_changed_grupo_z)
        except (TypeError, RuntimeError):
            pass  # nosec B110

        # limpa tabela
        self.tableWidgetLista2.clearContents()
        self.tableWidgetLista2.setRowCount(0)

        fields = layer.fields()
        self.tableWidgetLista2.setColumnCount(len(fields))
        self.tableWidgetLista2.setHorizontalHeaderLabels(self._traduzir_cabecalhos_grafico(fields))

        # performance
        self.tableWidgetLista2.blockSignals(True)
        self.tableWidgetLista2.setSortingEnabled(False)
        self.tableWidgetLista2.setUpdatesEnabled(False)

        features = list(layer.getFeatures())
        self.tableWidgetLista2.setRowCount(len(features))

        # mapeamento row -> fid
        self.feature_ids_grupo_z = []

        for row_idx, feat in enumerate(features):
            fid = feat.id()
            self.feature_ids_grupo_z.append(fid)

            for col_idx, field in enumerate(fields):
                val = feat[field.name()]
                txt = "" if val is None else str(val)

                item = QTableWidgetItem(txt)
                item.setFlags(Qt.ItemFlag.ItemIsSelectable | Qt.ItemFlag.ItemIsEnabled)

                # Guarda o FID na coluna 0
                if col_idx == 0:
                    item.setData(Qt.ItemDataRole.UserRole, fid)

                self.tableWidgetLista2.setItem(row_idx, col_idx, item)

        # reabilita
        self.tableWidgetLista2.setUpdatesEnabled(True)
        self.tableWidgetLista2.setSortingEnabled(True)
        self.tableWidgetLista2.blockSignals(False)

        self.tableWidgetLista2.resizeRowsToContents()
        self.tableWidgetLista2.resizeColumnsToContents()

        # sincroniza seleção inicial (mapa -> tabela)
        self.layer_selection_changed_grupo_z(layer.selectedFeatureIds(), [], False)

        # atualiza spinboxes
        self.set_spinboxes_from_tablewidget()

    def layer_selection_changed_grupo_z(self, selected_feature_ids, deselected_feature_ids, clear_and_select):
        """Espelha a seleção do mapa para o tableWidgetLista2 (grupo Z)."""

        sender_layer = self.sender()
        if sender_layer is not None and isinstance(getattr(self, "_sel_conn_layer_z", None), QgsVectorLayer):
            try:
                if sender_layer.id() != self._sel_conn_layer_z.id():
                    return
            except Exception:
                return

        if not hasattr(self, "feature_ids_grupo_z"):
            return

        self.tableWidgetLista2.blockSignals(True)
        self.tableWidgetLista2.setUpdatesEnabled(False)
        self.tableWidgetLista2.clearSelection()

        for fid in selected_feature_ids:
            try:
                row = self.feature_ids_grupo_z.index(fid)
                self.tableWidgetLista2.selectRow(row)
            except ValueError:
                pass  # nosec B110

        self.tableWidgetLista2.setUpdatesEnabled(True)
        self.tableWidgetLista2.blockSignals(False)

    def table_selection_changed_grupo_z(self):
        """Sincroniza a seleção do tableWidgetLista2 com a camada selecionada no comboBoxGrupoZ."""

        layer_id = self.comboBoxGrupoZ.currentData()
        layer = QgsProject.instance().mapLayer(layer_id)
        if not isinstance(layer, QgsVectorLayer):
            return

        # evita loop: desconecta handler correto (assinatura compatível)
        try:
            layer.selectionChanged.disconnect(self.layer_selection_changed_grupo_z)
        except (TypeError, RuntimeError):
            pass  # nosec B110

        selected_rows = self.tableWidgetLista2.selectionModel().selectedRows()
        fids = []
        for index in selected_rows:
            item = self.tableWidgetLista2.item(index.row(), 0)
            if item:
                fid = item.data(Qt.ItemDataRole.UserRole)
                if fid is not None:
                    fids.append(int(fid))

        layer.selectByIds(fids)

        try:
            layer.selectionChanged.connect(self.layer_selection_changed_grupo_z)
        except (TypeError, RuntimeError):
            pass  # nosec B110

    def apply_table_widget_changes_to_layer(self, layer):
        """Aplica as alterações do tableWidgetLista2 na camada e grava imediatamente."""
        if not isinstance(layer, QgsVectorLayer):
            return

        with edit(layer):  # commit automático
            for row_idx in range(self.tableWidgetLista2.rowCount()):
                item_id = self.tableWidgetLista2.item(row_idx, 0)
                if not item_id:
                    continue

                fid = item_id.data(Qt.ItemDataRole.UserRole)
                if fid is None:
                    continue

                feat = layer.getFeature(int(fid))
                if not feat.isValid():
                    continue

                for col_idx in range(self.tableWidgetLista2.columnCount()):
                    cell = self.tableWidgetLista2.item(row_idx, col_idx)
                    if cell is None:
                        continue
                    field_name = layer.fields()[col_idx].name()
                    feat.setAttribute(field_name, cell.text())

                layer.updateFeature(feat)

    def display_raster(self):
        """
        Exibe a camada raster selecionada na interface do usuário.
        """
        # Limpa a cena antes de adicionar um novo item
        self.scene.clear()

        # Garantir que a cena do graphicsViewRaster seja independente
        self.scene = QGraphicsScene()  # Esta é a cena do raster
        self.graphicsViewRaster.setScene(self.scene)

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
        Sobrescreve o evento de exibição do diálogo para resetar os Widgets.
        """
        super(GraficoManager, self).showEvent(event)

        # Ajusta a visualização quando o diálogo é mostrado
        self.display_raster()

        # Reseta o gráfico no scrollAreaGrafico
        self.reset_scroll_area_grafico()

        # Reseta os controles e atualiza o comboBoxGrupoZ
        self.reset_controls()
        self.update_combo_box_grupo_z()

        # Chamar handle_support_points_layer() para carregar os dados
        self.handle_support_points_layer()

        # Resetar o listWidgetInfo ao reiniciar o diálogo
        self.listWidgetInfo.clear()

        # Verificar se o gráfico está presente e recarregar as informações, se necessário
        if hasattr(self, 'graphWidget') and self.graphWidget is not None:
            # Recarregar informações do gráfico no listWidgetInfo
            self.recarregar_informacoes_do_grafico()

        # RESET garantido dos radio buttons
        self._reset_radio_buttons_by_layers()

    def _reset_radio_buttons_by_layers(self):
        """
        Ativa/desativa radioButtonLinhas e radioButtonPontos de acordo com as camadas disponíveis.
        Se houver ambas, inicia com pontos selecionados.
        """
        # Desliga autoExclusive temporariamente
        self.radioButtonLinhas.setAutoExclusive(False)
        self.radioButtonPontos.setAutoExclusive(False)
        self.radioButtonLinhas.setChecked(False)
        self.radioButtonPontos.setChecked(False)
        self.radioButtonLinhas.setAutoExclusive(True)
        self.radioButtonPontos.setAutoExclusive(True)

        # Coleta as camadas existentes
        layers = QgsProject.instance().mapLayers().values()
        has_linha = any(isinstance(layer, QgsVectorLayer) and layer.geometryType() == Qgis.GeometryType.Line
            for layer in layers)
        has_ponto = any(isinstance(layer, QgsVectorLayer) and layer.geometryType() == Qgis.GeometryType.Point
            for layer in layers)

        # Lógica de seleção
        if has_linha and not has_ponto:
            self.radioButtonLinhas.setChecked(True)
        elif has_ponto:
            # Se tem ponto, ativa pontos (mesmo que tenha linha)
            self.radioButtonPontos.setChecked(True)
        # Se não tem nenhum, ambos ficam desmarcados

        # Atualiza o comboBoxCamadas de acordo com o radio selecionado
        self.update_combo_box_camadas()

    def reset_controls(self):
        """Função responsável por resetar os botões e widgets."""
        # Reseta os RadioButtons
        self.radioButtonLinhas.setChecked(False)
        self.radioButtonPontos.setChecked(False)

        # Reseta o doubleSpinBoxDistancias para o valor mínimo e desativa
        self.doubleSpinBoxDistancias.setValue(self.doubleSpinBoxDistancias.minimum())
        self.doubleSpinBoxDistancias.setEnabled(False)

        # Reseta o checkBoxFinal (desmarcado)
        self.checkBoxFinal.setChecked(False)

        # Define o fundo como branco por padrão
        self.checkBoxFundo.setChecked(True)

        # Define a exportação da Tabela para DXF por padrão
        self.checkBoxTabela.setChecked(True)

        # Desativa o botão pushButtonCalcular
        self.pushButtonCalcular.setEnabled(False)

        # Desativa o botão pushButtonGerar
        self.pushButtonGerar.setEnabled(False)

        # Desativa o botão pushButtonExportarDXF por padrão
        self.pushButtonExportarDXF.setEnabled(False)

        # Atualiza o comboBoxCamadas e o estado do doubleSpinBoxDistancias
        self.update_combo_box_camadas()
        self.update_doubleSpinBoxDistancias_state()

        # Define os spin boxes a partir do tableWidgetLista2
        self.set_spinboxes_from_tablewidget()

    def handle_layers_added(self, layers):
        """
        Trata a adição de novas camadas ao projeto.
        Atualiza elementos da interface, como combos e listas, conforme necessário.
        """
        # Chama a função de atualização quando novas camadas são adicionadas
        self.update_combo_box()
        
        # Atualiza o comboBox de camadas de acordo com a seleção do RadioButton
        self.update_combo_box_camadas()

    def update_combo_box(self):
        """Atualiza o comboBox de camadas quando uma camada é removida ou renomeada"""
        if self._atualizacoes_camadas_suspensas():
            return

        # Armazena o índice atual do comboBox para restaurar depois
        current_index = self.comboBoxCamadas.currentIndex()
        current_layer_id = self.comboBoxCamadas.itemData(current_index)

        # Atualiza o comboBox de camadas (Linhas ou Pontos)
        self.update_combo_box_camadas()

        # Tenta restaurar a seleção anterior
        if current_layer_id:
            index = self.comboBoxCamadas.findData(current_layer_id)
            if index != -1:
                self.comboBoxCamadas.setCurrentIndex(index)
            else:
                # Se a camada não existe mais, seleciona a primeira disponível
                if self.comboBoxCamadas.count() > 0:
                    self.comboBoxCamadas.setCurrentIndex(0)

    def _configurar_tablewidget_lista(self):
        """
        Define políticas de redimensionamento para que as linhas do tableWidgetLista
        permaneçam com altura fixa (não aumentam nem pelo conteúdo nem pelo usuário).
        """
        vh = self.tableWidgetLista.verticalHeader()

        # 1. Modo de redimensionamento fixo
        vh.setSectionResizeMode(QtWidgets.QHeaderView.ResizeMode.Fixed)

        # 2. Altura padrão das linhas (mesmo 20 que você usa manualmente)
        linha_altura = 20
        vh.setDefaultSectionSize(linha_altura)
        vh.setMinimumSectionSize(linha_altura)

        # 3. Desabilita word-wrap para o texto não “forçar” quebra e altura maior
        self.tableWidgetLista.setWordWrap(False)

    def load_layer_attributes(self):
        """
        Carrega atributos da camada selecionada no comboBoxCamadas para o tableWidgetLista.
        Ao alternar de camada, força a aba 'tab' do tabWidget.
        """
        # (A) pega camada selecionada
        selected_layer_id = self.comboBoxCamadas.currentData()
        selected_layer = QgsProject.instance().mapLayer(selected_layer_id)

        # (B) se inválida: desconecta e limpa
        if not isinstance(selected_layer, QgsVectorLayer):
            prev = getattr(self, "_sel_conn_layer", None)
            if isinstance(prev, QgsVectorLayer):
                try:
                    prev.selectionChanged.disconnect(self.layer_selection_changed)
                except (TypeError, RuntimeError):
                    pass  # nosec B110

            self._sel_conn_layer = None
            self.selected_layer = None
            self.selected_layer_id = None

            with QtCore.QSignalBlocker(self.tableWidgetLista):
                self.tableWidgetLista.setUpdatesEnabled(False)
                try:
                    self.tableWidgetLista.clear()
                    self.tableWidgetLista.setRowCount(0)
                    self.tableWidgetLista.setColumnCount(0)
                finally:
                    self.tableWidgetLista.setUpdatesEnabled(True)

            self.verificar_estado_pushButtonGerar()
            self.update_doubleSpinBoxDistancias_state()
            self.verificar_condicoes_calcular()
            return

        # (C) força abrir a aba "tab" do tabWidget ao alternar camada
        try:
            if hasattr(self, "tabWidget") and hasattr(self, "tab"):
                if self.tabWidget.currentWidget() is not self.tab:
                    self.tabWidget.setCurrentWidget(self.tab)
        except Exception:
            pass  # nosec B110

        # (D) desconecta selectionChanged da camada anterior
        prev = getattr(self, "_sel_conn_layer", None)
        if isinstance(prev, QgsVectorLayer):
            try:
                prev.selectionChanged.disconnect(self.layer_selection_changed)
            except (TypeError, RuntimeError):
                pass  # nosec B110

        # (E) salva refs e conecta selectionChanged da atual
        self.selected_layer = selected_layer
        self.selected_layer_id = selected_layer.id()
        self._sel_conn_layer = selected_layer

        try:
            selected_layer.selectionChanged.connect(self.layer_selection_changed)
        except (TypeError, RuntimeError):
            pass  # nosec B110

        # garante layer ativa
        try:
            if self.iface is not None:
                self.iface.setActiveLayer(self.selected_layer)
        except Exception:
            pass  # nosec B110

        # (F) conecta sinais de mudança da camada (sem duplicar)
        self.conectar_sinais_tableWidgetLista(selected_layer)

        # (G) preenche a tabela (performance)
        self._loading_tableWidgetLista = True
        try:
            fields = selected_layer.fields()
            n_fields = len(fields)

            # request mais leve: sem geometria
            req = QgsFeatureRequest()
            req.setFlags(Qgis.FeatureRequestFlag.NoGeometry)

            # se tiver sorting, desligue durante fill
            sorting_was_enabled = self.tableWidgetLista.isSortingEnabled()
            if sorting_was_enabled:
                self.tableWidgetLista.setSortingEnabled(False)

            with QtCore.QSignalBlocker(self.tableWidgetLista):
                self.tableWidgetLista.setUpdatesEnabled(False)
                try:
                    self.tableWidgetLista.clearContents()
                    self.tableWidgetLista.setRowCount(0)
                    self.tableWidgetLista.setColumnCount(n_fields)
                    self.tableWidgetLista.setHorizontalHeaderLabels([f.name() for f in fields])

                    # defaults bem mais baratos que loop em cada linha/coluna
                    try:
                        self.tableWidgetLista.verticalHeader().setDefaultSectionSize(18)
                        self.tableWidgetLista.horizontalHeader().setDefaultSectionSize(100)
                    except Exception:
                        pass  # nosec B110

                    self.feature_ids = []
                    self._fid_to_row = {}

                    row_idx = 0
                    for feat in selected_layer.getFeatures(req):
                        fid = int(feat.id())
                        self.feature_ids.append(fid)
                        self._fid_to_row[fid] = row_idx

                        self.tableWidgetLista.insertRow(row_idx)

                        attrs = feat.attributes()
                        for col_idx in range(n_fields):
                            v = attrs[col_idx]
                            txt = "" if v is None else str(v)

                            item = QtWidgets.QTableWidgetItem(txt)
                            item.setFlags(Qt.ItemFlag.ItemIsSelectable | Qt.ItemFlag.ItemIsEnabled)
                            if col_idx == 0:
                                item.setData(Qt.ItemDataRole.UserRole, fid)

                            self.tableWidgetLista.setItem(row_idx, col_idx, item)

                        row_idx += 1

                finally:
                    self.tableWidgetLista.setUpdatesEnabled(True)

            if sorting_was_enabled:
                self.tableWidgetLista.setSortingEnabled(True)

        finally:
            self._loading_tableWidgetLista = False

        # (H) sincroniza seleção inicial
        self.layer_selection_changed(self.selected_layer.selectedFeatureIds(), [], False)

        # (I) recalcula estados
        self.verificar_estado_pushButtonGerar()
        self.update_doubleSpinBoxDistancias_state()
        self.verificar_condicoes_calcular()

    def conectar_sinais_tableWidgetLista(self, layer: QgsVectorLayer):
        """Conecta sinais da camada ao refresh da tableWidgetLista, sem duplicar e com limpeza segura."""

        old = getattr(self, "tableWidgetLista_layer_connected", None)

        # Se já está conectado nesta mesma camada, não faça nada
        if old is layer and isinstance(layer, QgsVectorLayer) and layer.isValid():
            return

        # Desconecta sinais antigos
        if isinstance(old, QgsVectorLayer):
            for sig in (old.featureAdded, old.featureDeleted, old.attributeValueChanged, old.geometryChanged):
                try:
                    sig.disconnect(self._on_feature_changed_tableWidgetLista)
                except (TypeError, RuntimeError):
                    pass  # nosec B110
            try:
                old.destroyed.disconnect(self._on_tableWidgetLista_layer_destroyed)
            except (TypeError, RuntimeError):
                pass  # nosec B110

        self.tableWidgetLista_layer_connected = None

        # Conecta novos sinais
        if isinstance(layer, QgsVectorLayer) and layer.isValid():
            layer.featureAdded.connect(self._on_feature_changed_tableWidgetLista)
            layer.featureDeleted.connect(self._on_feature_changed_tableWidgetLista)
            layer.attributeValueChanged.connect(self._on_feature_changed_tableWidgetLista)
            layer.geometryChanged.connect(self._on_feature_changed_tableWidgetLista)

            # quando layer morrer, limpamos o ponteiro
            try:
                layer.destroyed.connect(self._on_tableWidgetLista_layer_destroyed)
            except Exception:
                pass  # nosec B110

            self.tableWidgetLista_layer_connected = layer

    def _on_tableWidgetLista_layer_destroyed(self, *args):
        self.tableWidgetLista_layer_connected = None

    def table_selection_changed(self):
        """
        Sincroniza a seleção de linhas no tableWidgetLista com a seleção de feições na camada correspondente.
        Garante que as seleções feitas na tabela sejam refletidas na camada do QGIS.
        Utiliza apenas o ID da camada para evitar erros caso a camada tenha sido removida do projeto.
        """
        # Use sempre o ID!
        if not hasattr(self, 'selected_layer_id') or not self.selected_layer_id:
            return

        # Recupera a camada pelo projeto (garante validade)
        layer = QgsProject.instance().mapLayer(self.selected_layer_id)
        if not isinstance(layer, QgsVectorLayer):
            self.selected_layer_id = None
            return

        # onde desconecta/reconecta o sinal:
        try:
            layer.selectionChanged.disconnect(self.layer_selection_changed)
        except (TypeError, RuntimeError):
            pass  # nosec B110

        # Obtém as linhas selecionadas na tabela
        selected_rows = self.tableWidgetLista.selectionModel().selectedRows()
        selected_feature_ids = []
        for index in selected_rows:
            row = index.row()
            item = self.tableWidgetLista.item(row, 0)
            if item:
                feature_id = item.data(Qt.ItemDataRole.UserRole)
                if feature_id is not None:
                    selected_feature_ids.append(feature_id)

        # Seleciona as feições na camada (se ainda existe)
        # camada_atual.selectByIds(selected_feature_ids)
        layer.selectByIds(selected_feature_ids)

        try:
            layer.selectionChanged.connect(self.layer_selection_changed)
        except (TypeError, RuntimeError):
            pass  # nosec B110

        # Reagir a seleção feita na tabela
        self.verificar_condicoes_calcular()

    def set_label_for_layer(self, layer, field_name):
        """
        Configura o rótulo para uma camada no QGIS, com base em um campo específico e formatações adicionais.
        """
        label_settings = QgsPalLayerSettings()
        label_settings.drawBackground = True  # Ativa o fundo do rótulo
        label_settings.fieldName = field_name  # Define o campo a ser rotulado

        # Configura a formatação do texto
        text_format = label_settings.format()
        font = text_format.font()
        font.setItalic(True)
        font.setBold(True)
        text_format.setFont(font)

        # Configura a cor do rótulo com base em uma expressão condicional
        color_expression = """CASE
                                WHEN "Desnivel" < 0 THEN '255,0,0'  -- Vermelho
                                WHEN "Desnivel" > 0 THEN '0,0,255'  -- Azul
                                ELSE '0,0,0'  -- Preto
                              END"""

        properties = label_settings.dataDefinedProperties()
        properties.setProperty(QgsPalLayerSettings.Property.Color, QgsProperty.fromExpression(color_expression))

        # Defina o tamanho da fonte usando propriedades definidas por dados
        properties.setProperty(QgsPalLayerSettings.Property.Size, QgsProperty.fromValue(9))
        label_settings.setDataDefinedProperties(properties)

        # Configura o fundo branco para os rótulos
        background_color = text_format.background()
        background_color.setEnabled(True)
        background_color.setFillColor(QColor(255, 255, 255))
        text_format.setBackground(background_color)

        label_settings.setFormat(text_format)

        # Ativa o rótulo para a camada
        layer.setLabelsEnabled(True)
        layer.setLabeling(QgsVectorLayerSimpleLabeling(label_settings))
        layer.triggerRepaint()

    def set_point_colors_by_desnivel(self, layer: QgsVectorLayer, eps: float = 0.05) -> bool:
        """
        Colore feições de PONTO conforme o campo Desnível:
          > +eps → azul, < -eps → vermelho, |.| ≤ eps → branco.
        Compatível com QGIS 3.36 (usa setters nas regras).
        """
        if not isinstance(layer, QgsVectorLayer):
            return False
        if layer.geometryType() != Qgis.GeometryType.Point:
            return False

        # Expressões: aceita 'Desnível' ou 'Desnivel'
        expr_pos = f'coalesce("Desnível","Desnivel") > {eps}'
        expr_neg = f'coalesce("Desnível","Desnivel") < {-eps}'
        expr_zer = f'abs(coalesce("Desnível","Desnivel")) <= {eps}'

        # Símbolo base (mantém forma/tamanho atuais, só troca cor)
        try:
            base_sym = layer.renderer().symbol().clone()
        except Exception:
            base_sym = QgsMarkerSymbol.createSimple({"name": "circle", "size": "2"})

        def _colored(sym: QgsMarkerSymbol, rgb):
            s = sym.clone()
            s.setColor(QColor(*rgb))
            for sl in s.symbolLayers():
                if hasattr(sl, "setOutlineColor"):
                    sl.setOutlineColor(QColor(0, 0, 0))  # contorno p/ branco não sumir
                if hasattr(sl, "setOutlineWidth"):
                    sl.setOutlineWidth(0.2)
            return s

        sym_pos = _colored(base_sym, (0, 0, 255))       # azul
        sym_neg = _colored(base_sym, (255, 0, 0))       # vermelho
        sym_zer = _colored(base_sym, (255, 255, 255))   # branco

        # Raiz do renderer por regras
        root = QgsRuleBasedRenderer.Rule(None)

        # Regras criadas com símbolo; filtros/labels por setters (compatível)
        rule_pos = QgsRuleBasedRenderer.Rule(sym_pos)
        rule_pos.setFilterExpression(expr_pos)
        rule_pos.setLabel(self.tr("Aterro (>0)"))
        root.appendChild(rule_pos)

        rule_neg = QgsRuleBasedRenderer.Rule(sym_neg)
        rule_neg.setFilterExpression(expr_neg)
        rule_neg.setLabel(self.tr("Corte (<0)"))
        root.appendChild(rule_neg)

        rule_zer = QgsRuleBasedRenderer.Rule(sym_zer)
        rule_zer.setFilterExpression(expr_zer)
        rule_zer.setLabel(self.tr("Zero (≈0)"))
        root.appendChild(rule_zer)

        renderer = QgsRuleBasedRenderer(root)
        layer.setRenderer(renderer)
        layer.triggerRepaint()

        # Refresh UI (se iface existir)
        try:
            self.iface.layerTreeView().refreshLayerSymbology(layer.id())
            self.iface.mapCanvas().refresh()
        except Exception:
            pass  # nosec B110

        return True

    def layer_selection_changed(self, selected_feature_ids, deselected_feature_ids, clear_and_select):
        """
        Trata mudanças na seleção de feições da camada.
        Atualiza a interface ou dados internos conforme seleção ou desseleção de feições.
        """
        # Ignora somente sinais emitidos por outra camada vetorial.
        # Quando a função é chamada durante a troca do comboBoxCamadas,
        # self.sender() pode ser o próprio comboBox.
        sender_layer = self.sender()

        if (isinstance(sender_layer, QgsVectorLayer)
            and getattr(self, "selected_layer_id", None)
            and sender_layer.id() != self.selected_layer_id):
            return

        # espelha a seleção do mapa na tabela
        self.tableWidgetLista.blockSignals(True)
        self.tableWidgetLista.setUpdatesEnabled(False)
        self.tableWidgetLista.clearSelection()

        # seleciona as linhas correspondentes aos FIDs
        if hasattr(self, "feature_ids"):
            for fid in selected_feature_ids:
                try:
                    row = self.feature_ids.index(fid)
                    self.tableWidgetLista.selectRow(row)
                except ValueError:
                    pass  # nosec B110

        self.tableWidgetLista.setUpdatesEnabled(True)
        self.tableWidgetLista.blockSignals(False)

        # reavalia os botões que dependem da seleção
        self.verificar_estado_pushButtonGerar()   # reage à seleção do mapa
        self.verificar_condicoes_calcular()       # se quiser que o Calcular reaja também

    def update_doubleSpinBoxDistancias_state(self):
        """
        Atualiza o estado (habilita ou desabilita) do doubleSpinBoxDistancias conforme as opções selecionadas na interface.
        """
        # Verifica se o radioButtonLinhas está selecionado
        if self.radioButtonLinhas.isChecked():
            # Verifica se há uma camada selecionada no comboBoxCamadas
            selected_layer_id = self.comboBoxCamadas.currentData()
            selected_layer = QgsProject.instance().mapLayer(selected_layer_id)

            if isinstance(selected_layer, QgsVectorLayer):
                # Verifica se a camada possui feições
                if selected_layer.featureCount() > 0:
                    # Ativa o doubleSpinBoxDistancias
                    self.doubleSpinBoxDistancias.setEnabled(True)
                    return  # Sai da função se todas as condições forem atendidas

        # Se qualquer condição não for atendida, desativa o doubleSpinBoxDistancias
        self.doubleSpinBoxDistancias.setEnabled(False)

    def calcular_pontos(self):
        """
        Calcula os pontos ao longo das feições de linha com base na distância e adiciona ao mapa,
        garantindo que tudo ocorra em um único clique, mesmo que precise commitar antes.
        """
        # Verifica se há uma camada selecionada e se é uma camada de linhas
        if not hasattr(self, 'selected_layer') or not isinstance(self.selected_layer, QgsVectorLayer):
            return

        # Antes do commit, armazene as geometrias das feições selecionadas (pode ser o WKT das linhas)
        selected_geoms = []
        selected_rows = self.tableWidgetLista.selectionModel().selectedRows()
        for idx in selected_rows:
            row = idx.row()
            item = self.tableWidgetLista.item(row, 0)
            if item:
                feature_id = item.data(Qt.ItemDataRole.UserRole)
                feat = self.selected_layer.getFeature(feature_id)
                if feat and feat.geometry():
                    selected_geoms.append(feat.geometry().asWkt())

        # Se não houver seleção, não faz nada
        if not selected_geoms:
            return

        # Commit se estiver em edição
        if self.selected_layer.isEditable():
            ok = self.selected_layer.commitChanges()
            if not ok:
                self.mostrar_mensagem(self.tr("Não foi possível salvar a camada antes de gerar os pontos."), "Erro")
                return

        # Recarrega a tabela (agora com os IDs definitivos)
        self.load_layer_attributes()

        # Agora, recupere as novas feições selecionadas usando as geometrias
        # Mapear o índice da linha no widget para a feição com geometria igual
        new_selected_rows = []
        for row in range(self.tableWidgetLista.rowCount()):
            item = self.tableWidgetLista.item(row, 0)
            if item:
                feature_id = item.data(Qt.ItemDataRole.UserRole)
                feat = self.selected_layer.getFeature(feature_id)
                if feat and feat.geometry().asWkt() in selected_geoms:
                    new_selected_rows.append(row)

        # Se não encontrar nada, não faz nada
        if not new_selected_rows:
            return

        # Selecionar as linhas correspondentes (restaura visualmente para o usuário)
        self.tableWidgetLista.clearSelection()
        for row in new_selected_rows:
            self.tableWidgetLista.selectRow(row)

        # Agora segue o fluxo normal: gerar pontos para os selecionados
        distancia = self.doubleSpinBoxDistancias.value()
        if distancia <= 0:
            return

        for row in new_selected_rows:
            item = self.tableWidgetLista.item(row, 0)
            if item:
                feature_id = item.data(Qt.ItemDataRole.UserRole)
                feature = self.selected_layer.getFeature(feature_id)
                geom = feature.geometry()
                if not geom or geom.isEmpty():
                    continue

                geometria_linha = None
                if geom.type() == Qgis.GeometryType.Line:
                    if geom.isMultipart():
                        parts = geom.asMultiPolyline()
                        if not parts or len(parts[0]) < 2:
                            continue
                        geometria_linha = parts[0]
                    else:
                        geometria_linha = geom.asPolyline()
                        if len(geometria_linha) < 2:
                            continue
                    # Desfaz fechamento se necessário
                    if geometria_linha[0] == geometria_linha[-1] and len(geometria_linha) > 2:
                        geometria_linha = geometria_linha[:-1]
                elif geom.type() == Qgis.GeometryType.Polygon:
                    poly = geom.asPolygon()
                    if poly and len(poly[0]) > 2:
                        geometria_linha = poly[0]
                        if geometria_linha[0] == geometria_linha[-1]:
                            geometria_linha = geometria_linha[:-1]
                    else:
                        continue
                else:
                    continue

                # Gerar o nome da camada de pontos baseado no ID da feição
                nome_cam_pontos_base = f"{self.selected_layer.name()}_ID{feature_id}"
                nome_cam_pontos = self._gerar_nome_cam_pontos_unico(nome_cam_pontos_base)

                # Criar uma nova camada de pontos para essa feição
                crs = self.selected_layer.crs()  # Utiliza o CRS da camada de linhas
                pontos_layer = QgsVectorLayer("Point?crs={}".format(crs.authid()), nome_cam_pontos, "memory")
                pontos_layer_provider = pontos_layer.dataProvider()

                # Definir os campos na camada de pontos: ID1 (id_linha), ID2 (id_ponto), X, Y
                pontos_layer_provider.addAttributes([
                    QgsField("ID_Linha", QMetaType.Type.Int),  # ID1 = ID da feição de linha
                    QgsField("ID", QMetaType.Type.Int),  # ID2 = ID do ponto gerado
                    QgsField("coord_x", QMetaType.Type.Double),
                    QgsField("coord_y", QMetaType.Type.Double)])
                pontos_layer.updateFields()

                comprimento_total = feature.geometry().length()
                pontos = []

                # Adiciona pontos ao longo da linha com base na distância
                distancia_acumulada = 0.0
                ponto_id = 1  # ID do ponto a ser incrementado
                while distancia_acumulada < comprimento_total:
                    ponto = feature.geometry().interpolate(distancia_acumulada)
                    pontos.append((ponto, distancia_acumulada))  # Armazena o ponto e a distância
                    distancia_acumulada += distancia

                # Se o checkboxFinal estiver marcado, adiciona um ponto no final da linha
                if self.checkBoxFinal.isChecked():
                    ponto_final = feature.geometry().interpolate(comprimento_total)
                    pontos.append((ponto_final, comprimento_total))

                # Adiciona os pontos à nova camada de pontos
                for ponto, dist in pontos:
                    if ponto.isNull():
                        continue  # Pula pontos inválidos

                    nova_feature = QgsFeature(pontos_layer.fields())
                    nova_feature.setGeometry(ponto)

                    # Extrai as coordenadas X e Y do ponto, arredondando para 3 casas decimais
                    coord_x = round(ponto.asPoint().x(), 3)
                    coord_y = round(ponto.asPoint().y(), 3)

                    # Define os atributos: ID1 (id_linha), ID2 (id_ponto), X, Y
                    nova_feature.setAttributes([feature.id(), ponto_id, coord_x, coord_y])
                    pontos_layer_provider.addFeature(nova_feature)

                    ponto_id += 1  # Incrementa o ID do ponto

                # Atualiza a camada de pontos
                pontos_layer.updateExtents()

                # Adiciona a camada criada ao grupo "Pontos de Linhas"
                self._add_layer_to_group(pontos_layer, self.tr("Pontos de Linhas"))

                self.mostrar_mensagem(self.tr("Camada de pontos '{nome_cam_pontos}' gerada e adicionada ao mapa.").format(nome_cam_pontos=nome_cam_pontos), "Sucesso")

        # Verifica novamente as condições após o cálculo
        self.verificar_condicoes_calcular()

    def _gerar_nome_cam_pontos_unico(self, nome_base):
        """Gera um nome único para a camada de pontos, adicionando um sufixo numérico se necessário."""
        nome_unico = nome_base
        contador = 1

        # Verifica se já existe uma camada com o nome fornecido
        while QgsProject.instance().mapLayersByName(nome_unico):
            nome_unico = f"{nome_base}_{contador}"
            contador += 1

        return nome_unico

    def mostrar_mensagem(self, texto, tipo, duracao=3, caminho_pasta=None, caminho_arquivo=None):
        """
        Exibe uma mensagem na barra de mensagens do QGIS
        """
        # Obtém a barra de mensagens da interface do QGIS
        bar = iface.messageBar()  # Acessa a barra de mensagens da interface do QGIS

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

    def verificar_condicoes_calcular(self):
        """Verifica se o botão Calcular deve ser ativado ou desativado."""
        
        # Verifica se há uma camada selecionada no comboBoxCamadas
        selected_layer_id = self.comboBoxCamadas.currentData()
        selected_layer = QgsProject.instance().mapLayer(selected_layer_id)

        # Verifica se a camada selecionada é uma camada de pontos e desativa o botão se for
        if isinstance(selected_layer, QgsVectorLayer) and selected_layer.geometryType() == Qgis.GeometryType.Point:
            self.pushButtonCalcular.setEnabled(False)
            return

        # Verifica se o valor do doubleSpinBoxDistancias é maior que 0
        distancia_valida = self.doubleSpinBoxDistancias.value() > 0
        
        # Verifica se há pelo menos uma linha selecionada no tableWidgetLista
        selected_rows = self.tableWidgetLista.selectionModel().selectedRows()
        linha_selecionada = len(selected_rows) > 0
        
        # Verifica se as feições selecionadas possuem ID válido
        for index in selected_rows:
            row = index.row()
            item = self.tableWidgetLista.item(row, 0)
            if item is None or item.data(Qt.ItemDataRole.UserRole) is None:
                # Exibe a mensagem de erro se a feição não contiver ID
                self.mostrar_mensagem("Feição selecionada não contém ID.", "Erro")
                self.pushButtonCalcular.setEnabled(False)  # Desativa o botão se o ID for inválido
                return
        
        # Se ambas as condições forem verdadeiras, ativa o botão Calcular
        if distancia_valida and linha_selecionada:
            self.pushButtonCalcular.setEnabled(True)
        else:
            self.pushButtonCalcular.setEnabled(False)

    def carregar_atributos_tableWidgetLista2(self, camada):
        """Carrega os atributos da camada no tableWidgetLista2."""
        # Limpa o tableWidgetLista2 antes de adicionar novos itens
        self.tableWidgetLista2.clearContents()
        self.tableWidgetLista2.setRowCount(0)

        if isinstance(camada, QgsVectorLayer):
            # Obtém os campos (atributos) da camada
            fields = camada.fields()

            # Define o número de colunas com base no número de campos
            self.tableWidgetLista2.setColumnCount(len(fields))

            # Configura o cabeçalho da tabela com os nomes dos campos
            self.tableWidgetLista2.setHorizontalHeaderLabels(self._traduzir_cabecalhos_grafico(fields))

            # Itera sobre as feições da camada e adiciona os atributos à tabela
            for row_idx, feature in enumerate(camada.getFeatures()):
                # Define o número de linhas dinamicamente
                self.tableWidgetLista2.insertRow(row_idx)

                # Itera sobre cada campo da feição e adiciona o valor correspondente à célula da tabela
                for col_idx, field in enumerate(fields):
                    field_value = str(feature[field.name()])
                    item = QTableWidgetItem(field_value)
                    item.setFlags(Qt.ItemFlag.ItemIsSelectable | Qt.ItemFlag.ItemIsEnabled)
                    self.tableWidgetLista2.setItem(row_idx, col_idx, item)

            # Ajusta automaticamente o tamanho das colunas e das linhas
            self.tableWidgetLista2.resizeRowsToContents()
            self.tableWidgetLista2.resizeColumnsToContents()

    def _add_layer_to_group(self, layer, group_name):
        """Adiciona a camada ao grupo especificado no projeto."""
        root = QgsProject.instance().layerTreeRoot()

        # Procura o grupo com o nome especificado
        group = root.findGroup(group_name)
        if not group:
            group = root.insertGroup(0, group_name)

        # Verifica se a camada já está no grupo para evitar duplicação
        if any(layer.name() == existing_layer.name() for existing_layer in group.findLayers()):
            return

        # Adiciona a camada ao grupo
        QgsProject.instance().addMapLayer(layer, False)
        group.insertLayer(0, layer)

    def update_combo_box_grupo_z(self):
        """Atualiza o comboBoxGrupoZ para exibir apenas as camadas do grupo 'Pontos com Z'."""
        if self._atualizacoes_camadas_suspensas():
            return

        self.comboBoxGrupoZ.blockSignals(True)  # Bloqueia sinais durante a atualização

        # Limpa o comboBox antes de adicionar novos itens para evitar duplicação
        self.comboBoxGrupoZ.clear()

        root = QgsProject.instance().layerTreeRoot()
        group = root.findGroup(self.tr("Pontos com Z"))

        if group:
            layers = [layer.layer() for layer in group.children() if isinstance(layer, QgsLayerTreeLayer)]
            for layer in layers:
                if self.comboBoxGrupoZ.findText(layer.name()) == -1:
                    self.comboBoxGrupoZ.addItem(layer.name(), layer.id())

        self.comboBoxGrupoZ.blockSignals(False)  # Desbloqueia sinais após a atualização

        # Chamar manualmente as funções necessárias para carregar os dados
        self.handle_support_points_layer()
        self.load_layer_attributes_grupo_z()  # Carrega os atributos no tableWidgetLista2

        # Se não houver camadas no comboBoxGrupoZ, limpa o tableWidgetLista2
        if self.comboBoxGrupoZ.count() == 0:
            self.tableWidgetLista2.clearContents()
            self.tableWidgetLista2.setRowCount(0)
            self.tableWidgetLista2.setColumnCount(0)

        self.atualizar_estado_pushButtonDel() # Atualiza o botão de deletar

        # Como os sinais do combo ficaram bloqueados durante seu preenchimento,
        # carrega manualmente as cotas da camada selecionada
        if hasattr(self, "doubleSpinBoxHinicial_Cota"):
            self._carregar_cotas_da_camada()

    def _get_z_value_from_raster(self, raster_layer, x, y, point_crs):
        """Obtém o valor Z do raster no ponto (x, y)."""
        raster_crs = raster_layer.crs()
        if raster_crs != point_crs:
            transform = QgsCoordinateTransform(point_crs, raster_crs, QgsProject.instance())
            point = transform.transform(QgsPointXY(x, y))
        else:
            point = QgsPointXY(x, y)

        # Obtém o valor do raster no ponto
        ident = raster_layer.dataProvider().identify(point, Qgis.RasterIdentifyFormat.Value)
        if ident.isValid():
            results = ident.results()
            if results:
                z_value = list(results.values())[0]
                return z_value
        return None

    def update_combo_box_camadas(self):
        """Atualiza o comboBoxCamadas quando há alterações no projeto."""
        if self._atualizacoes_camadas_suspensas():
            return

        # Armazena a seleção atual (índice e ID da camada)
        current_index = self.comboBoxCamadas.currentIndex()
        current_layer_id = self.comboBoxCamadas.itemData(current_index)

        # Limpa o combo box de camadas
        self.comboBoxCamadas.clear()

        # Obtém todas as camadas do projeto
        layers = QgsProject.instance().mapLayers().values()

        # Obter os IDs das camadas do grupo "Pontos com Z"
        root = QgsProject.instance().layerTreeRoot()
        grupo_z = root.findGroup(self.tr("Pontos com Z"))
        z_layers_ids = set()
        if grupo_z:
            z_layers_ids = {layer.layerId() for layer in grupo_z.findLayers()}

        # Obter os IDs das camadas do grupo "Pontos Apoio"
        grupo_apoio = root.findGroup(self.tr("Pontos Apoio"))
        apoio_layers_ids = set()
        if grupo_apoio:
            apoio_layers_ids = {layer.layerId() for layer in grupo_apoio.findLayers()}

        # Verifica qual RadioButton está selecionado (Linhas ou Pontos)
        if self.radioButtonLinhas.isChecked():
            # Filtra as camadas de linhas que não estão nos grupos "Pontos com Z" e "Pontos Apoio"
            line_layers = [
                layer for layer in layers
                if isinstance(layer, QgsVectorLayer)
                and layer.geometryType() == Qgis.GeometryType.Line
                and layer.id() not in z_layers_ids
                and layer.id() not in apoio_layers_ids]

            # Adiciona as camadas de linha ao comboBox
            for line_layer in line_layers:
                self.comboBoxCamadas.addItem(line_layer.name(), line_layer.id())

        elif self.radioButtonPontos.isChecked():
            # Filtra as camadas de pontos que não estão nos grupos "Pontos com Z" e "Pontos Apoio"
            point_layers = [
                layer for layer in layers
                if isinstance(layer, QgsVectorLayer)
                and layer.geometryType() == Qgis.GeometryType.Point
                and layer.id() not in z_layers_ids
                and layer.id() not in apoio_layers_ids]

            # Adiciona as camadas de pontos ao comboBox
            for point_layer in point_layers:
                self.comboBoxCamadas.addItem(point_layer.name(), point_layer.id())

        # Tenta restaurar a seleção que estava antes
        if current_layer_id is not None:
            index = self.comboBoxCamadas.findData(current_layer_id)
            if index != -1:
                # Se achou a camada anterior, restaura
                self.comboBoxCamadas.setCurrentIndex(index)
            else:
                # Se não achou a camada anterior (ela pode ter sido removida),
                # decide se seleciona nada ou a primeira camada disponível
                if self.comboBoxCamadas.count() > 0:
                    self.comboBoxCamadas.setCurrentIndex(0)
                else:
                    # Se não há camadas, desabilita o doubleSpinBoxDistancias
                    self.doubleSpinBoxDistancias.setEnabled(False)
        else:
            # Se não havia nada selecionado antes,
            # só seleciona a primeira se quiser manter o antigo comportamento
            if self.comboBoxCamadas.count() > 0:
                self.comboBoxCamadas.setCurrentIndex(0)
            else:
                self.doubleSpinBoxDistancias.setEnabled(False)

        # Após atualizar o comboBoxCamadas...
        if self.comboBoxCamadas.count() == 0:
            # Limpa o tableWidgetLista por completo, incluindo cabeçalhos
            self.tableWidgetLista.clear()
            self.tableWidgetLista.setRowCount(0)
            self.tableWidgetLista.setColumnCount(0)
        else:
            # Caso haja camada, pode carregar normalmente (ou deixar para o slot .currentIndexChanged)
            self.load_layer_attributes()

        # Atualiza o estado do doubleSpinBoxDistancias
        self.update_doubleSpinBoxDistancias_state()

    def recalculate_fields(self, layer):
        """
        Recalcula e atualiza campos de atributos da camada especificada conforme necessário.
        """
        h_inicial = self.doubleSpinBoxHinicial.value()
        h_final = self.doubleSpinBoxHFinal.value()

        # Obter os índices dos campos necessários
        idx_z = layer.fields().indexFromName('Z')
        idx_novoz = layer.fields().indexFromName('NovoZ')
        idx_desnivel = layer.fields().indexFromName('Desnivel')
        idx_dist_acumulada = layer.fields().indexFromName('dist_acumulada')

        if idx_z == -1 or idx_novoz == -1 or idx_desnivel == -1 or idx_dist_acumulada == -1:
            self.mostrar_mensagem(self.tr("Os campos necessários não estão presentes na camada."), "Erro")
            return

        # Coletar os valores de dist_acumulada
        dist_acumuladas = [feature['dist_acumulada'] for feature in layer.getFeatures()]
        total_length = max(dist_acumuladas)

        # Calcular Z inicial e Z final
        z_initial = None
        z_final = None
        for feature in layer.getFeatures():
            if feature['dist_acumulada'] == 0.0:
                z_initial = feature['Z'] + h_inicial
            if feature['dist_acumulada'] == total_length:
                z_final = feature['Z'] + h_final

        if z_initial is None or z_final is None:
            self.mostrar_mensagem(self.tr("Não foi possível determinar Z inicial ou Z final."), "Erro")
            return

        # Recalcular NovoZ e Desnivel
        # Como já estamos em modo de edição, podemos atualizar diretamente
        for feature in layer.getFeatures():
            dist_acumulada = feature['dist_acumulada']
            novo_z = z_initial + (dist_acumulada / total_length) * (z_final - z_initial)
            # desnivel = round(feature['Z'] - novo_z, 3)
            desnivel = round(novo_z - feature['Z'], 3)

            # Atualizar atributos
            feature['NovoZ'] = round(novo_z, 3)
            feature['Desnivel'] = desnivel

            # Atualiza a feição na camada
            layer.updateFeature(feature)

        # Atualizar o tableWidgetLista2
        self.update_tableWidgetLista2(layer)

    def on_spinbox_value_changed(self):
        """Acionada sempre que Hinicial ou Hfinal muda."""
        if self.tabWidget.currentWidget() != self.tab_2:
            return

        selected_layer_id = self.comboBoxGrupoZ.currentData()
        selected_layer = QgsProject.instance().mapLayer(selected_layer_id)
        if not isinstance(selected_layer, QgsVectorLayer):
            return

        # Grava imediatamente usando o contexto ‘edit’
        with edit(selected_layer):
            self.recalculate_fields(selected_layer)

        # Atualiza o gráfico já com os novos valores
        self.setup_graph_in_scroll_area()

    def gerar_pontos_com_z(self):
        """Gera uma nova camada de pontos com os valores Z e calcula NovoZ, dist_acumulada e Desnivel."""
        # Verifica se o radioButtonPontos está selecionado
        if not self.radioButtonPontos.isChecked():
            self.mostrar_mensagem(self.tr("Selecione 'Pontos' para gerar pontos com Z."), "Erro")
            return

        # Obtém o ID da camada de pontos selecionada no comboBoxCamadas
        selected_layer_id = self.comboBoxCamadas.currentData()
        point_layer = QgsProject.instance().mapLayer(selected_layer_id)

        if not isinstance(point_layer, QgsVectorLayer) or point_layer.geometryType() != Qgis.GeometryType.Point:
            self.mostrar_mensagem(self.tr("Camada de pontos inválida selecionada."), "Erro")
            return

        # Verifica se há feições selecionadas no tableWidgetLista
        selected_rows = self.tableWidgetLista.selectionModel().selectedRows()
        if not selected_rows:
            self.mostrar_mensagem(self.tr("Nenhuma feição de ponto foi selecionada."), "Erro")
            return

        # Obtém o raster selecionado no comboBoxRaster
        raster_layer_id = self.comboBoxRaster.currentData()
        raster_layer = QgsProject.instance().mapLayer(raster_layer_id)

        if not isinstance(raster_layer, QgsRasterLayer):
            self.mostrar_mensagem(self.tr("Camada raster inválida selecionada."), "Erro")
            return

        # Obtém os valores de Hinicial e Hfinal
        h_inicial = self.doubleSpinBoxHinicial.value()
        h_final = self.doubleSpinBoxHFinal.value()

        # Cria uma nova camada de pontos em memória
        crs = point_layer.crs()
        new_layer_name_base = f"{point_layer.name()}_Z"
        new_layer_name = self._gerar_nome_cam_pontos_unico(new_layer_name_base)
        new_layer = QgsVectorLayer(f"Point?crs={crs.authid()}", new_layer_name, "memory")
        provider = new_layer.dataProvider()

        # Adiciona campos ID, X, Y, Z, NovoZ, dist_acumulada, Desnivel
        provider.addAttributes([
            QgsField("ID", QMetaType.Type.QString),
            QgsField("X", QMetaType.Type.Double),
            QgsField("Y", QMetaType.Type.Double),
            QgsField("Z", QMetaType.Type.Double),
            QgsField("NovoZ", QMetaType.Type.Double),
            QgsField("dist_acumulada", QMetaType.Type.Double),
            QgsField("Desnivel", QMetaType.Type.Double)  # Campo adicional para desnível
        ])
        new_layer.updateFields()

        # Itera sobre as feições selecionadas e extrai o Z do raster
        points = []

        possui_campo_id = point_layer.fields().indexFromName("ID") != -1

        idx_novoz_origem = point_layer.fields().lookupField("NovoZ")
        possui_novoz = idx_novoz_origem != -1

        for index in selected_rows:
            row = index.row()
            item = self.tableWidgetLista.item(row, 0)

            if item is None:
                continue

            feature_id = item.data(Qt.ItemDataRole.UserRole)

            if feature_id is None:
                continue

            feature = point_layer.getFeature(int(feature_id))

            if not feature.isValid():
                continue

            geom = feature.geometry()

            if geom is None or geom.isEmpty():
                continue

            point = geom.asPoint()
            x = point.x()
            y = point.y()

            # ID lógico da camada. O FID interno só é usado para localizar a feição.
            if possui_campo_id:
                valor_id = feature["ID"]
                id_logico = str(valor_id).strip() if valor_id is not None else str(feature_id)
            else:
                id_logico = str(feature_id)

            # Obtém o valor Z do raster no ponto
            z_value = self._get_z_value_from_raster(raster_layer, x, y, crs)

            if z_value is None or z_value == raster_layer.dataProvider().sourceNoDataValue(1):
                self.mostrar_mensagem(
                    self.tr("Não foi possível obter Z para o ponto ID {feature_id}.").format(
                        feature_id=id_logico),
                    "Erro")
                continue

            novo_z_origem = None

            if possui_novoz:
                valor_novoz = feature[idx_novoz_origem]

                if valor_novoz is not None:
                    try:
                        novo_z_origem = float(valor_novoz)
                    except (TypeError, ValueError):
                        novo_z_origem = None

            points.append((id_logico, x, y, float(z_value), novo_z_origem))

        # A sequência do perfil é definida pelo campo ID.
        # A ordenação natural mantém, por exemplo:
        # TF-1, TF-2, TF-10, em vez de TF-1, TF-10, TF-2.
        def chave_id_natural(item):
            return [
                int(parte) if parte.isdigit() else parte.casefold()
                for parte in re.split(r"(\d+)", str(item[0]))]

        points.sort(key=chave_id_natural)

        if not points:
            self.mostrar_mensagem(self.tr("Nenhum ponto válido foi processado."), "Erro")
            return

        # Calcular total_length e distâncias entre pontos
        total_length = 0.0
        distances = []
        for i in range(1, len(points)):
            x1, y1 = points[i-1][1], points[i-1][2]
            x2, y2 = points[i][1], points[i][2]
            point1 = QgsPointXY(x1, y1)
            point2 = QgsPointXY(x2, y2)
            distance = QgsDistanceArea().measureLine(point1, point2)
            distances.append(distance)
            total_length += distance

        # Calcular Z inicial e Z final
        z_initial = points[0][3] + h_inicial
        z_final = points[-1][3] + h_final

        # Itera sobre os pontos para calcular dist_acumulada e NovoZ
        dist_acumulada = 0.0
        previous_point = None
        for i, (feature_id, x, y, z_value, novo_z_origem) in enumerate(points):
            current_point = QgsPointXY(x, y)
            if i == 0:
                dist_acumulada = 0.0
            else:
                dist_acumulada += distances[i - 1]

            if novo_z_origem is not None:
                novo_z = novo_z_origem
            else:
                novo_z = z_initial + (dist_acumulada / total_length) * (z_final - z_initial)

            if i == len(points) - 1:
                dist_acumulada = total_length

            # Calcula o desnível entre Z e NovoZ
            desnivel = round(novo_z - z_value, 3)

            # Cria uma nova feição com os campos ID, X, Y, Z, NovoZ, dist_acumulada, Desnivel
            new_feature = QgsFeature(new_layer.fields())
            new_feature.setGeometry(QgsGeometry.fromPointXY(current_point))

            # Define os atributos com 3 casas decimais para os campos numéricos
            new_feature.setAttributes([
                feature_id,
                round(x, 3),
                round(y, 3),
                round(z_value, 3),
                round(novo_z, 3),
                round(dist_acumulada, 3),
                desnivel])
            provider.addFeature(new_feature)

            previous_point = current_point

        new_layer.updateExtents()

        # Garante que as edições foram gravadas
        try:
            new_layer.commitChanges()
        except Exception:
            pass  # nosec B110

        # Aplicar os rótulos à nova camada
        self.set_label_for_layer(new_layer, "Desnivel")

        # Adiciona a nova camada ao projeto dentro do grupo "Pontos com Z"
        self._add_layer_to_group(new_layer, self.tr("Pontos com Z"))

        # Cores por Desnível para as feições de PONTO
        self.set_point_colors_by_desnivel(new_layer, eps=0.05)

        # atualiza a vista
        new_layer.triggerRepaint()
        if hasattr(self, "iface") and self.iface:
            self.iface.layerTreeView().refreshLayerSymbology(new_layer.id())
            self.iface.mapCanvas().refresh()

        # Atualiza o comboBoxGrupoZ para exibir as camadas no grupo "Pontos com Z"
        self.update_combo_box_grupo_z()

        self.mostrar_mensagem(self.tr("Camada '{layer_name}' adicionada ao grupo 'Pontos com Z'.").format(layer_name=new_layer.name()), "Sucesso")

    def selecionar_aba_tab_widget(self):
        """Seleciona a aba no tabWidget com base no RadioButton selecionado."""
        if self.radioButtonLinhas.isChecked():
            # Seleciona a aba de linhas chamada 'tab'
            self.tabWidget.setCurrentWidget(self.tab)
        elif self.radioButtonPontos.isChecked():
            # Seleciona a aba de pontos chamada 'tab'
            self.tabWidget.setCurrentWidget(self.tab)

    def _tab_index_by_objectname(self, obj_name: str) -> int:
        """Retorna o índice da aba cujo widget tem objectName == obj_name. -1 se não achar."""
        if not hasattr(self, "tabWidget") or self.tabWidget is None:
            return -1

        for i in range(self.tabWidget.count()):
            w = self.tabWidget.widget(i)
            if w is not None and w.objectName() == obj_name:
                return i
        return -1

    def _ensure_tab_open(self, obj_name: str = "tab"):
        """
        Garante que a aba (por objectName) esteja visível/habilitada e selecionada.
        Se não existir, tenta fallback para self.tab.
        """
        if not hasattr(self, "tabWidget") or self.tabWidget is None:
            return

        idx = self._tab_index_by_objectname(obj_name)

        # fallback: se você tem self.tab (Qt Designer costuma gerar)
        if idx == -1 and hasattr(self, "tab") and self.tab is not None:
            try:
                idx = self.tabWidget.indexOf(self.tab)
            except Exception:
                idx = -1

        if idx == -1:
            return  # não existe no tabWidget (nada a fazer)

        # Se sua versão do Qt/QGIS suportar setTabVisible, ajuda quando você “escondeu” aba
        try:
            if hasattr(self.tabWidget, "setTabVisible"):
                self.tabWidget.setTabVisible(idx, True)
        except Exception:
            pass  # nosec B110

        try:
            self.tabWidget.setTabEnabled(idx, True)
        except Exception:
            pass  # nosec B110

        if self.tabWidget.currentIndex() != idx:
            with QtCore.QSignalBlocker(self.tabWidget):
                self.tabWidget.setCurrentIndex(idx)

    def on_pushButtonGerar_clicked(self):
        """Função chamada ao clicar no botão pushButtonGerar"""
        # Muda para a aba tab_2
        self.tabWidget.setCurrentWidget(self.tab_2)

        # Verifica se há uma camada válida no comboBoxGrupoZ
        selected_layer_id = self.comboBoxGrupoZ.currentData()
        estacas_layer = QgsProject.instance().mapLayer(selected_layer_id)
        
        if not isinstance(estacas_layer, QgsVectorLayer):
            # self.mostrar_mensagem("Nenhuma camada válida de 'Pontos com Z' foi selecionada.", "Erro")
            return

        # Verifica se há um raster selecionado
        raster_layer_id = self.comboBoxRaster.currentData()
        raster_layer = QgsProject.instance().mapLayer(raster_layer_id)

        if not isinstance(raster_layer, QgsRasterLayer):
            self.mostrar_mensagem(self.tr("Nenhuma camada raster válida foi selecionada."), "Erro")
            return

        # Verifica se há pelo menos duas feições selecionadas no tableWidgetLista2
        selected_rows = self.tableWidgetLista2.selectionModel().selectedRows()
        if len(selected_rows) < 2:
            # self.mostrar_mensagem("Selecione pelo menos duas linhas no tableWidgetLista2.", "Erro")
            return

        # Gera a camada de suporte de pontos com base nas estacas e o raster selecionado
        try:
            support_layer = self.create_support_points_layer(estacas_layer, raster_layer)
        except Exception as e:
            self.mostrar_mensagem(self.tr("Erro ao gerar a camada de suporte: {error}").format(error=str(e)), "Erro")
            return

    def handle_support_points_layer(self):
        """
        Gerencia a camada de pontos de apoio:
        - Cria a camada de suporte baseada nos pontos e MDT selecionados
        - Adiciona ao grupo 'Pontos Apoio' no painel de camadas
        - Atualiza combos e UI conforme necessário
        - Remove camadas antigas de apoio se já existirem
        """
        start_time = time.time()
        self.comboBoxGrupoZ.blockSignals(True)

        try:
            selected_layer_id = self.comboBoxGrupoZ.currentData()
            pontos_z_layer = QgsProject.instance().mapLayer(selected_layer_id)
            
            if pontos_z_layer is None or not isinstance(pontos_z_layer, QgsVectorLayer):
                return

            support_layer_name = self.tr("{layer_name}_PontosApoio").format(layer_name=pontos_z_layer.name())

            # Verificar se a camada de apoio já existe
            existing_layer = QgsProject.instance().mapLayersByName(support_layer_name)
            if existing_layer:
                # A camada de apoio já existe, não é necessário recriá-la
                pass
            else:
                # Criar a camada de apoio somente se não existir
                group = QgsProject.instance().layerTreeRoot().findGroup(self.tr("Pontos Apoio"))
                if not group:
                    group = QgsProject.instance().layerTreeRoot().insertGroup(0, self.tr("Pontos Apoio"))

                raster_layer_id = self.comboBoxRaster.currentData()
                raster_layer = QgsProject.instance().mapLayer(raster_layer_id)
                
                if raster_layer is None or not isinstance(raster_layer, QgsRasterLayer):
                    return

                # Tente criar a camada de suporte
                support_layer = self.create_support_points_layer(pontos_z_layer, raster_layer)
                if support_layer is None:
                    raise ValueError(self.tr("Não foi possível criar a camada de apoio para '{layer_name}'.").format(layer_name=pontos_z_layer.name()))

                support_layer.setName(support_layer_name)

                QgsProject.instance().addMapLayer(support_layer, False)
                group_layer = group.insertLayer(0, support_layer)
                group_layer.setItemVisibilityChecked(False)

                self.update_combo_box_camadas()

            # Chamar setup_graph_in_scroll_area() para atualizar o gráfico
            self.setup_graph_in_scroll_area()

        except Exception as e:
            self.mostrar_mensagem(str(e), "Erro")

        finally:
            self.comboBoxGrupoZ.blockSignals(False)

    def sample_raster_value(self, point, raster_layer):
        """Amostra o valor Z do raster baseado nas coordenadas do ponto."""
        identify_result = raster_layer.dataProvider().identify(QgsPointXY(point.x(), point.y()), Qgis.RasterIdentifyFormat.Value)
        
        if identify_result.isValid():
            results = identify_result.results()
            if results:
                band_key = list(results.keys())[0]
                z_value = results.get(band_key)  # Use get para evitar KeyError
                if z_value is not None:  # Verifica se o valor é válido
                    return round(float(z_value), 3)
        return None  # Retorna None se não houver valor válido

    def _obter_camadas_dos_grupos_salvaveis(self):
        """
        Retorna as camadas dos grupos produzidos pelo módulo.
        O grupo Pontos de Linhas é opcional.
        """
        root = QgsProject.instance().layerTreeRoot()

        grupos = [
            self.tr("Pontos com Z"),
            self.tr("Pontos Apoio"),
            self.tr("Pontos de Linhas")]

        resultado = {}

        for nome_grupo in grupos:
            grupo = root.findGroup(nome_grupo)
            camadas = []

            if grupo is not None:
                for node in grupo.children():
                    if isinstance(node, QgsLayerTreeLayer):
                        camada = node.layer()

                        if (isinstance(camada, QgsVectorLayer)
                            and camada.isValid()):
                            camadas.append(camada)

            if camadas:
                resultado[nome_grupo] = camadas

        return resultado

    def _atualizar_estado_pushButtonSalvar(self):
        """Habilita o botão somente quando houver alguma camada para salvar."""
        grupos = self._obter_camadas_dos_grupos_salvaveis()
        possui_camadas = any(grupos.values())

        self.pushButtonSalvar.setEnabled(possui_camadas)

    def _agendar_atualizacao_pushButtonSalvar(self, *_):
        """
        Aguarda o QGIS concluir a inclusão ou remoção no painel
        antes de verificar os grupos.
        """
        if self._atualizacoes_camadas_suspensas():
            return

        QTimer.singleShot(0, self._atualizar_estado_pushButtonSalvar)

    def salvar_grupos_geopackage(self):
        """
        Salva em um único GeoPackage as camadas dos grupos:
        - Pontos com Z;
        - Pontos Apoio;
        - Pontos de Linhas, quando existir.

        O prefixo do nome interno permitirá reconstruir os grupos
        futuramente pelo botão Abrir.
        """
        grupos = self._obter_camadas_dos_grupos_salvaveis()

        if not grupos:
            self._atualizar_estado_pushButtonSalvar()
            return

        settings = QSettings()

        ultima_pasta = settings.value("GraficoTaludeManager2D/ultima_pasta_geopackage", "")

        arquivo_gpkg, _ = QFileDialog.getSaveFileName(self, self.tr("Salvar grupos em GeoPackage"), os.path.join(ultima_pasta, "Grafico_Talude_2D.gpkg"), self.tr("GeoPackage (*.gpkg)"))

        if not arquivo_gpkg:
            return

        if not arquivo_gpkg.lower().endswith(".gpkg"):
            arquivo_gpkg += ".gpkg"

        pasta_saida = os.path.dirname(arquivo_gpkg)

        settings.setValue("GraficoTaludeManager2D/ultima_pasta_geopackage", pasta_saida)

        prefixos = {
            self.tr("Pontos com Z"): "Pontos_com_Z",
            self.tr("Pontos Apoio"): "Pontos_Apoio",
            self.tr("Pontos de Linhas"): "Pontos_de_Linhas"}

        # Monta a relação completa das camadas que serão salvas
        camadas_para_salvar = []

        for nome_grupo, camadas in grupos.items():
            prefixo = prefixos.get(nome_grupo, nome_grupo.replace(" ", "_"))

            for camada in camadas:
                camadas_para_salvar.append((prefixo, camada))

        if not camadas_para_salvar:
            self._atualizar_estado_pushButtonSalvar()
            return

        # Cria a mensagem e a barra de progresso
        mensagem_progresso = self.iface.messageBar().createMessage(self.tr("Salvando camadas no GeoPackage..."))

        barra_progresso = QProgressBar()
        barra_progresso.setMinimum(0)
        barra_progresso.setMaximum(len(camadas_para_salvar))
        barra_progresso.setValue(0)
        barra_progresso.setAlignment(Qt.AlignmentFlag.AlignLeft | Qt.AlignmentFlag.AlignVCenter)

        barra_progresso.setFormat(self.tr("%p% - %v de %m camadas salvas"))

        barra_progresso.setMinimumWidth(320)

        mensagem_progresso.layout().addWidget(
            barra_progresso)

        self.iface.messageBar().pushWidget(
            mensagem_progresso,
            Qgis.MessageLevel.Info)

        primeira_camada = True
        nomes_utilizados = set()
        erros = []

        try:
            for indice, (prefixo, camada) in enumerate(camadas_para_salvar, start=1):
                nome_original = camada.name()

                nome_limpo = re.sub(r"[^A-Za-z0-9_]+", "_", nome_original).strip("_")

                if not nome_limpo:
                    nome_limpo = "Camada"

                nome_interno_base = (f"{prefixo}__{nome_limpo}")

                nome_interno = nome_interno_base
                contador = 1

                while nome_interno.casefold() in nomes_utilizados:
                    nome_interno = (f"{nome_interno_base}_{contador}")
                    contador += 1

                nomes_utilizados.add(
                    nome_interno.casefold())

                opcoes = QgsVectorFileWriter.SaveVectorOptions()
                opcoes.driverName = "GPKG"
                opcoes.fileEncoding = "UTF-8"
                opcoes.layerName = nome_interno

                if primeira_camada:
                    opcoes.actionOnExistingFile = (
                        QgsVectorFileWriter.ActionOnExistingFile.CreateOrOverwriteFile)
                else:
                    opcoes.actionOnExistingFile = (
                        QgsVectorFileWriter.ActionOnExistingFile.CreateOrOverwriteLayer)

                resultado = QgsVectorFileWriter.writeAsVectorFormatV3(camada, arquivo_gpkg, QgsProject.instance().transformContext(), opcoes)

                codigo_erro = resultado[0]
                mensagem_erro = resultado[1]

                if codigo_erro == QgsVectorFileWriter.WriterError.NoError:
                    primeira_camada = False
                else:
                    erros.append(f"{camada.name()}: {mensagem_erro}")

                barra_progresso.setValue(indice)
                QApplication.processEvents()

        except Exception as erro:
            erros.append(str(erro))

        finally:
            try:
                self.iface.messageBar().popWidget(
                    mensagem_progresso)
            except Exception:
                pass  # nosec B110

        if primeira_camada:
            self.mostrar_mensagem(self.tr("Nenhuma camada pôde ser salva no GeoPackage."), "Erro")
            return

        if erros:
            self.mostrar_mensagem(self.tr("O GeoPackage foi criado, mas algumas camadas não foram salvas: {errors}").format(errors="; ".join(erros)), "Erro")
            return

        self.mostrar_mensagem(self.tr("GeoPackage salvo com sucesso."), "Sucesso", caminho_pasta=pasta_saida)

    def _iniciar_progresso_abertura_geopackage(self):
        """Cria a barra usada em todas as etapas da abertura."""
        self._fechar_progresso_abertura_geopackage()

        mensagem = self.iface.messageBar().createMessage(self.tr("Abrindo GeoPackage do Gráfico com Talude 2D..."))

        barra = QProgressBar()
        barra.setRange(0, 100)
        barra.setValue(0)

        barra.setAlignment(Qt.AlignmentFlag.AlignLeft | Qt.AlignmentFlag.AlignVCenter)

        barra.setMinimumWidth(380)

        mensagem.layout().addWidget(barra)
        self.iface.messageBar().pushWidget(mensagem, Qgis.MessageLevel.Info)

        self._progressBarAberturaGpkg = barra
        self._progressMessageBarAberturaGpkg = mensagem
        self._abertura_geopackage_em_andamento = True
        self.pushButtonAbrir.setEnabled(False)

        self._atualizar_progresso_abertura_geopackage(2, self.tr("Preparando abertura"))

    def _atualizar_progresso_abertura_geopackage(self, valor, etapa):
        """Atualiza o percentual e informa a etapa executada."""
        barra = getattr(self,  "_progressBarAberturaGpkg", None)

        if barra is None:
            return

        try:
            barra.setFormat(self.tr("{stage} - %p%").format(stage=etapa))

            barra.setValue(max( 0, min(100, int(valor))))

            QApplication.processEvents()

        except RuntimeError:
            self._progressBarAberturaGpkg = None

    def _fechar_progresso_abertura_geopackage(self):
        """Remove a barra e desfaz a espera pelo canvas."""
        self._render_abertura_pendente = False

        try:
            self.iface.mapCanvas().renderComplete.disconnect(
                self._on_render_abertura_geopackage_concluido)

        except (TypeError, RuntimeError):
            pass  # nosec B110

        mensagem = getattr(self, "_progressMessageBarAberturaGpkg", None)
        if mensagem is not None:
            try:
                self.iface.messageBar().popWidget(mensagem)

            except (TypeError, RuntimeError):
                pass  # nosec B110

        self._progressBarAberturaGpkg = None
        self._progressMessageBarAberturaGpkg = None
        self._abertura_geopackage_em_andamento = False
        self._carregando_geopackage = False

        if hasattr(self, "pushButtonAbrir"):
            self.pushButtonAbrir.setEnabled(True)

    def _executar_etapa_final_abertura_geopackage(self, etapa):
        """
        Finaliza combos, tabela, gráfico e canvas em etapas.
        """
        if not getattr(self, "_abertura_geopackage_em_andamento", False):
            return

        if getattr(self, "_is_closing", False):
            self._fechar_progresso_abertura_geopackage()
            return

        try:
            # Etapa 1: lista de camadas
            if etapa == 0:
                self._atualizar_progresso_abertura_geopackage(72, self.tr("Atualizando lista de camadas"))

                self.update_combo_box_camadas()

                QTimer.singleShot(0, lambda: self._executar_etapa_final_abertura_geopackage(1))

                return

            # Etapa 2: tabela e gráfico
            if etapa == 1:
                self._atualizar_progresso_abertura_geopackage(82, self.tr("Carregando tabela e gráfico"))

                suspender_raster_anterior = (self._suspender_render_raster)

                self._suspender_render_raster = True

                try:
                    self.update_combo_box_grupo_z()

                finally:
                    self._suspender_render_raster = (suspender_raster_anterior)

                QTimer.singleShot(0, lambda: self._executar_etapa_final_abertura_geopackage(2))

                return

            # Etapa 3: renderização final
            self._atualizar_progresso_abertura_geopackage(
                95,
                self.tr("Atualizando mapa"))

            self._atualizar_estado_pushButtonSalvar()

            canvas = self.iface.mapCanvas()

            try:
                canvas.renderComplete.disconnect(
                    self._on_render_abertura_geopackage_concluido)

            except (TypeError, RuntimeError):
                pass  # nosec B110

            canvas.renderComplete.connect(
                self._on_render_abertura_geopackage_concluido)

            self._render_abertura_pendente = True

            canvas.refresh()

            # Impede que a barra fique presa caso o canvas
            # não emita renderComplete
            QTimer.singleShot(10000, self._verificar_timeout_render_abertura_geopackage)

        except Exception as erro:
            self._carregando_geopackage = False
            self._fechar_progresso_abertura_geopackage()

            self.mostrar_mensagem(self.tr("As camadas foram carregadas, mas ocorreu um erro ao finalizar a interface: {error}").format(error=str(erro)), "Erro")

    def _on_render_abertura_geopackage_concluido(self, *_):
        """
        Encerra a abertura depois da renderização final do mapa.
        """
        if not getattr(self, "_render_abertura_pendente", False):
            return

        self._render_abertura_pendente = False

        try:
            self.iface.mapCanvas().renderComplete.disconnect(self._on_render_abertura_geopackage_concluido)

        except (TypeError, RuntimeError):
            pass  # nosec B110

        self._atualizar_progresso_abertura_geopackage(100, self.tr("Carregamento concluído"))
        QTimer.singleShot(150, self._concluir_abertura_geopackage)

    def _verificar_timeout_render_abertura_geopackage(self):
        """
        Finaliza com segurança se renderComplete não for emitido.
        """
        if getattr(self, "_render_abertura_pendente", False):
            self._on_render_abertura_geopackage_concluido()

    def _concluir_abertura_geopackage(self):
        """Fecha a barra e apresenta a confirmação final."""
        if not getattr(self, "_abertura_geopackage_em_andamento", False):
            return

        self._carregando_geopackage = False

        self._fechar_progresso_abertura_geopackage()

        self.mostrar_mensagem(self.tr("GeoPackage carregado e grupos reconstruídos com sucesso."), "Sucesso")

    def abrir_grupos_geopackage(self):
        """
        Abre somente GeoPackages produzidos pelo módulo e reconstrói:
        - Pontos com Z;
        - Pontos Apoio;
        - Pontos de Linhas, quando existir.
        """
        if getattr(self, "_abertura_geopackage_em_andamento", False):
            self.mostrar_mensagem(self.tr("Aguarde a conclusão da abertura em andamento."), "Erro")

            return

        settings = QSettings()

        ultima_pasta = settings.value("GraficoTaludeManager2D/ultima_pasta_geopackage", "")

        arquivo_gpkg, _ = QFileDialog.getOpenFileName(self, self.tr("Abrir GeoPackage do Gráfico com Talude 2D"), ultima_pasta, self.tr("GeoPackage (*.gpkg)"))

        if not arquivo_gpkg:
            return

        if not arquivo_gpkg.lower().endswith(".gpkg"):
            self.mostrar_mensagem(self.tr("O arquivo selecionado não é um GeoPackage válido."), "Erro")
            return

        pasta_arquivo = os.path.dirname(arquivo_gpkg)

        settings.setValue("GraficoTaludeManager2D/ultima_pasta_geopackage", pasta_arquivo)

        metadata_ogr = QgsProviderRegistry.instance().providerMetadata("ogr")

        if metadata_ogr is None:
            self.mostrar_mensagem(self.tr("O provedor OGR não está disponível."), "Erro")
            return

        try:
            subcamadas = metadata_ogr.querySublayers(
                arquivo_gpkg)
        except Exception as erro:
            self.mostrar_mensagem(self.tr("Não foi possível inspecionar o GeoPackage: {error}").format(error=str(erro)), "Erro")
            return

        if not subcamadas:
            self.mostrar_mensagem(
                self.tr("O GeoPackage não possui camadas vetoriais válidas."), "Erro")
            return

        configuracoes = {
            "Pontos_com_Z__": {
                "grupo": self.tr("Pontos com Z"),
                "campos": {
                    "ID",
                    "X",
                    "Y",
                    "Z",
                    "NovoZ",
                    "dist_acumulada"}},
            "Pontos_Apoio__": {
                "grupo": self.tr("Pontos Apoio"),
                "campos": {
                    "ID",
                    "Original_ID",
                    "X",
                    "Y",
                    "Znovo",
                    "Acumula_dist"}},
            "Pontos_de_Linhas__": {
                "grupo": self.tr("Pontos de Linhas"),
                "campos": {
                    "ID_Linha",
                    "ID",
                    "coord_x",
                    "coord_y"}}}

        camadas_validadas = []
        grupos_encontrados = set()
        incompatibilidades = []

        for detalhes in subcamadas:
            nome_interno = detalhes.name()
            prefixo_encontrado = None
            configuracao = None

            for prefixo, dados in configuracoes.items():
                if nome_interno.startswith(prefixo):
                    prefixo_encontrado = prefixo
                    configuracao = dados
                    break

            if configuracao is None:
                incompatibilidades.append(self.tr("Camada não reconhecida: {layer_name}").format(layer_name=nome_interno))
                continue

            nome_exibicao = nome_interno[
                len(prefixo_encontrado):]

            if not nome_exibicao:
                incompatibilidades.append(self.tr("Camada com nome inválido: {layer_name}").format(layer_name=nome_interno))
                continue

            if QgsProject.instance().mapLayersByName(nome_exibicao):
                incompatibilidades.append(self.tr("A camada '{layer_name}' já está carregada no projeto.").format(layer_name=nome_exibicao))
                continue

            camada = QgsVectorLayer(detalhes.uri(), nome_exibicao, detalhes.providerKey())

            if not camada.isValid():
                incompatibilidades.append(self.tr("Camada inválida: {layer_name}").format(layer_name=nome_interno))
                continue

            if camada.geometryType() != Qgis.GeometryType.Point:
                incompatibilidades.append(self.tr("A camada '{layer_name}' não é uma camada de pontos.").format(layer_name=nome_exibicao))
                continue

            nomes_campos = {campo.name()
                for campo in camada.fields()}

            campos_ausentes = (configuracao["campos"] - nomes_campos)

            if campos_ausentes:
                incompatibilidades.append(self.tr("A camada '{layer_name}' não possui os campos: {fields}").format(layer_name=nome_exibicao, fields=", ".join(sorted(campos_ausentes))))
                continue

            # Pontos com Z deve possuir Desnivel ou Desnível
            if (prefixo_encontrado == "Pontos_com_Z__"
                and not {"Desnivel", "Desnível"}.intersection(nomes_campos)):
                incompatibilidades.append(self.tr("A camada '{layer_name}' não possui o campo 'Desnivel' ou 'Desnível'.").format(layer_name=nome_exibicao))
                continue

            grupos_encontrados.add(configuracao["grupo"])

            camadas_validadas.append((configuracao["grupo"], prefixo_encontrado, camada))

        # Recusa completamente o arquivo se houver qualquer camada incompatível
        if incompatibilidades:
            self.mostrar_mensagem(self.tr("O GeoPackage não corresponde às configurações do aplicativo: {errors}").format(errors="; ".join(incompatibilidades)), "Erro")
            return

        grupos_obrigatorios = {self.tr("Pontos com Z"), self.tr("Pontos Apoio")}

        grupos_ausentes = (grupos_obrigatorios - grupos_encontrados)

        if grupos_ausentes:
            self.mostrar_mensagem(self.tr("O GeoPackage não contém os grupos obrigatórios: {groups}").format(groups=", ".join(sorted(grupos_ausentes))), "Erro")
            return

        if not camadas_validadas:
            self.mostrar_mensagem(self.tr("Nenhuma camada compatível foi encontrada."), "Erro")
            return

        self._iniciar_progresso_abertura_geopackage()

        # Impede que layersAdded execute as atualizações automáticas
        # enquanto as camadas do arquivo ainda estão sendo adicionadas.
        self._carregando_geopackage = True

        root = QgsProject.instance().layerTreeRoot()

        camadas_adicionadas = []
        grupos_criados = []

        try:
            self._atualizar_progresso_abertura_geopackage(8, self.tr("Preparando grupos"))

            # Esta ordem mantém Pontos Apoio acima de Pontos com Z.
            ordem_grupos = [
                self.tr("Pontos de Linhas"),
                self.tr("Pontos com Z"),
                self.tr("Pontos Apoio")]

            grupos_qgis = {}

            for nome_grupo in ordem_grupos:
                if nome_grupo not in grupos_encontrados:
                    continue

                grupo = root.findGroup(nome_grupo)

                if grupo is None:
                    grupo = root.insertGroup(0, nome_grupo)
                    grupos_criados.append(grupo)
                grupos_qgis[nome_grupo] = grupo

            total_camadas = len(camadas_validadas)

            for indice, (nome_grupo, prefixo, camada
            ) in enumerate(camadas_validadas, start=1):
                progresso = (12 + int(53 * indice / total_camadas))

                self._atualizar_progresso_abertura_geopackage(progresso, self.tr("Adicionando camada {current} de {total}").format(current=indice, total=total_camadas))

                grupo = grupos_qgis[nome_grupo]

                QgsProject.instance().addMapLayer(camada, False)
                node_camada = grupo.addLayer(camada)

                camadas_adicionadas.append(camada.id())

                if prefixo == "Pontos_com_Z__":
                    nome_campo_desnivel = ("Desnivel"
                        if camada.fields().indexFromName( "Desnivel") != -1
                        else "Desnível")

                    self.set_label_for_layer(camada, nome_campo_desnivel)

                    self.set_point_colors_by_desnivel(camada, eps=0.05)

                    node_camada.setItemVisibilityChecked(True)

                elif prefixo == "Pontos_Apoio__":
                    # Pontos de apoio carregados sem seleção
                    camada.removeSelection()

                    # A camada fica desmarcada no painel
                    node_camada.setItemVisibilityChecked(
                        False)

                else:
                    node_camada.setItemVisibilityChecked(
                        True)

            # O grupo fica habilitado, mas suas camadas permanecem
            # individualmente desmarcadas.
            grupo_apoio = grupos_qgis.get(self.tr("Pontos Apoio"))

            if grupo_apoio is not None:
                grupo_apoio.setItemVisibilityChecked(True)

        except Exception as erro:
            # Mantém o bloqueio ativo durante a limpeza para não
            # executar uma atualização a cada camada removida.
            if camadas_adicionadas:
                QgsProject.instance().removeMapLayers(camadas_adicionadas)

            for grupo in grupos_criados:
                if not grupo.children():
                    root.removeChildNode(grupo)

            self._carregando_geopackage = False
            self._fechar_progresso_abertura_geopackage()

            self.mostrar_mensagem(self.tr("Erro ao carregar o GeoPackage: {error}").format(error=str(erro)), "Erro")

            return

        # Somente libera as atualizações depois que todas as camadas,
        # inclusive os pontos de apoio, estiverem no projeto.
        self._carregando_geopackage = False

        self._atualizar_progresso_abertura_geopackage(68, self.tr("Camadas adicionadas"))

        # Executa a atualização consolidada da interface.
        QTimer.singleShot(0, lambda: self._executar_etapa_final_abertura_geopackage(0))

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

    def verificar_estado_pushButtonGerar(self):
        """
        Ativa o pushButtonGerar somente se:
          • radioButtonPontos estiver selecionado;
          • existirem pelo menos duas linhas selecionadas na tableWidgetLista.
        Desativa em qualquer outro cenário.
        """
        # condição 1 – modo PONTOS
        if not self.radioButtonPontos.isChecked():
            self.pushButtonGerar.setEnabled(False)
            return

        # condição 2 – seleção mínima de linhas
        linhas_sel = self.tableWidgetLista.selectionModel().selectedRows()
        self.pushButtonGerar.setEnabled(len(linhas_sel) >= 2)

    def _on_layers_removed_clear_graph(self, removed_layer_ids):
        """
        Se a camada que alimenta o gráfico for removida no QGIS,
        limpa o scrollAreaGrafico e widgets associados.
        """
        if self._atualizacoes_camadas_suspensas():
            return

        if getattr(self, '_current_graph_layer_id', None) in removed_layer_ids:
            self.reset_scroll_area_grafico()

    def _safe_set_progress(self, value: int):
        """Atualiza a barra de progresso com segurança."""
        pb = getattr(self, '_progressBar', None)

        if pb is None:
            return

        try:
            pb.setValue(value)
        except RuntimeError:
            self._progressBar = None

    def _close_progress_bar(self):
        """Remove só a barra/mensagem que este método criou."""
        msg = getattr(self, '_progressMessageBar', None)
        if msg is not None:
            try:
                self.iface.messageBar().popWidget(msg)
            except Exception:
                pass  # nosec B110
        self._progressBar = None
        self._progressMessageBar = None

    def create_support_points_layer(self, estacas_layer, raster_layer):
        """
        Cria e retorna uma camada de pontos de apoio a partir das estacas e do raster, 
        interpolando valores Z e acumulando distâncias.
        """
        start_time = time.time()
        
        # Obter a resolução do pixel da camada raster
        raster_extent = raster_layer.extent()
        raster_width = raster_layer.width()
        raster_height = raster_layer.height()
        pixel_resolution_x = raster_extent.width() / raster_width
        pixel_resolution_y = raster_extent.height() / raster_height

        # Definir o espaçamento de suporte como a resolução do pixel
        support_spacing = min(pixel_resolution_x, pixel_resolution_y)

        # Obter o CRS da camada de estacas
        crs = estacas_layer.sourceCrs().authid()
        support_layer = QgsVectorLayer(f"Point?crs={crs}", "", "memory")  # Criar a camada sem nome

        prov = support_layer.dataProvider()

        # Adiciona os campos necessários, incluindo "Acumula_dist"
        fields = [
            QgsField("ID", QMetaType.Type.Int),              # Identificador do ponto de apoio
            QgsField("Original_ID", QMetaType.Type.QString),     # ID original do ponto de origem
            QgsField("X", QMetaType.Type.Double),            # Coordenada X
            QgsField("Y", QMetaType.Type.Double),            # Coordenada Y
            QgsField("Znovo", QMetaType.Type.Double),        # Altitude do MDT (Z interpolado)
            QgsField("Acumula_dist", QMetaType.Type.Double)]  # Distância acumulada ao longo da linha

        prov.addAttributes(fields)
        support_layer.updateFields()

        estacas_features = [feat for feat in estacas_layer.getFeatures()]
        estacas_points = [feat.geometry().asPoint() for feat in estacas_features]
        all_points = []
        support_point_id = 0
        last_coord = None
        acumula_dist = 0

        # Obter o índice do campo "Desnivel" (aceita também "Desnível")
        desnivel_index = estacas_layer.fields().indexFromName('Desnivel')
        if desnivel_index == -1:
            desnivel_index = estacas_layer.fields().indexFromName('Desnível')

        if desnivel_index == -1:
            raise ValueError(self.tr("A camada '{layer_name}' não possui o campo obrigatório 'Desnivel'/'Desnível'.").format(layer_name=estacas_layer.name()))

        # Acessar o valor do campo usando o índice
        first_desnivel = estacas_features[0][desnivel_index]
        last_desnivel = estacas_features[-1][desnivel_index]

        extend_by_start = min(abs(first_desnivel) + 10, 10)  # No máximo 10 metros
        extend_by_end = min(abs(last_desnivel) + 10, 10)  # No máximo 10 metros

        # Calcular o número total de pontos para a barra de progresso
        num_points_before_first_stake = int(extend_by_start // support_spacing)
        num_points_after_last_stake = int(extend_by_end // support_spacing) + 1
        num_points_along_segments = 0

        for i, start_point in enumerate(estacas_points[:-1]):
            end_point = estacas_points[i + 1]
            segment_length = start_point.distance(end_point)
            num_intermediate_points = int(segment_length / support_spacing)
            num_points_along_segments += num_intermediate_points + 1  # +1 para incluir o ponto final

        total_points = num_points_before_first_stake + num_points_along_segments + num_points_after_last_stake
        total_steps = total_points * 2  # Multiplica por 2 para incluir as etapas de atualização de Znovo

        # Iniciar a barra de progresso
        progressBar, progressMessageBar = self.iniciar_progress_bar(total_steps)
        # ‼️  guarde referências para checagens subsequentes
        self._progressBar        = progressBar
        self._progressMessageBar = progressMessageBar
        progressMessageBar.destroyed.connect(lambda *_: setattr(self, '_progressBar', None))
        current_step = 0

        # Adicionar pontos extras antes do primeiro ponto de estacas
        first_segment_dir = estacas_points[1] - estacas_points[0]
        for i in range(num_points_before_first_stake, 0, -1):
            extra_point = QgsPointXY(estacas_points[0].x() - first_segment_dir.x() * (i * support_spacing) / first_segment_dir.length(), estacas_points[0].y() - first_segment_dir.y() * (i * support_spacing) / first_segment_dir.length())
            
            z_value = self.sample_raster_value(extra_point, raster_layer)
            if z_value is None:
                # Interrompe a extensão se o valor de Z for None
                break
            
            support_point_id += 1
            all_points.append((extra_point, None, support_point_id))
            
            # Atualizar a barra de progresso
            current_step += 1
            self._safe_set_progress(current_step)
            self._ui_pump(step=current_step, every_steps=50)

        # Gerar os pontos de apoio ao longo dos segmentos
        for i, start_point in enumerate(estacas_points[:-1]):
            end_point = estacas_points[i + 1]
            segment_length = start_point.distance(end_point)
            num_intermediate_points = int(segment_length / support_spacing)

            for j in range(num_intermediate_points + 1):
                x = start_point.x() + (end_point.x() - start_point.x()) * (j * support_spacing) / segment_length
                y = start_point.y() + (end_point.y() - start_point.y()) * (j * support_spacing) / segment_length
                inter_point = QgsPointXY(x, y)
                support_point_id += 1
                all_points.append((inter_point, estacas_features[i]['ID'], support_point_id))
                
                # # Atualizar a barra de progresso
                current_step += 1
                self._safe_set_progress(current_step)
                self._ui_pump(step=current_step, every_steps=50)

        # Adicionar pontos extras após o último ponto de estacas
        last_segment_dir = estacas_points[-1] - estacas_points[-2]
        for i in range(0, num_points_after_last_stake):
            extra_point = QgsPointXY(estacas_points[-1].x() + last_segment_dir.x() * (i * support_spacing) / last_segment_dir.length(), estacas_points[-1].y() + last_segment_dir.y() * (i * support_spacing) / last_segment_dir.length())
            
            z_value = self.sample_raster_value(extra_point, raster_layer)
            if z_value is None:
                # Interrompe a extensão se o valor de Z for None
                break

            support_point_id += 1
            all_points.append((extra_point, estacas_features[-1]['ID'], support_point_id))
            
            # Atualizar a barra de progresso
            current_step += 1
            self._safe_set_progress(current_step)
            self._ui_pump(step=current_step, every_steps=50)

        # Criar os recursos e adicionar à camada com a distância acumulada
        first_positive_id_encountered = False
        for point, original_id, support_point_id in all_points:
            current_coord = (point.x(), point.y())
            if not first_positive_id_encountered:
                if original_id is not None:
                    acumula_dist = 0
                    first_positive_id_encountered = True
                else:
                    acumula_dist = -extend_by_start + (support_point_id - 1) * support_spacing
            else:
                if last_coord:
                    segment_distance = QgsPointXY(*last_coord).distance(QgsPointXY(*current_coord))
                    acumula_dist += segment_distance
            last_coord = current_coord

            # Atributos do recurso, incluindo acumulação de distância
            feat = QgsFeature()
            feat.setGeometry(QgsGeometry.fromPointXY(QgsPointXY(*current_coord)))
            feat.setAttributes([support_point_id, original_id, round(point.x(), 3), round(point.y(), 3), None, round(acumula_dist, 3)])
            prov.addFeature(feat)
            
            # Atualizar a barra de progresso
            current_step += 1
            self._safe_set_progress(current_step)
            self._ui_pump(step=current_step, every_steps=50)

        # Amostra os valores do MDT para os pontos de apoio e atualiza o campo "Znovo"
        support_layer.startEditing()
        z_value_previous = None

        for feature in support_layer.getFeatures():
            point = feature.geometry().asPoint()
            z_value = self.sample_raster_value(point, raster_layer)
            if z_value is None and z_value_previous is not None:
                z_value = z_value_previous
            if z_value is not None:
                z_value_previous = z_value
            feature['Znovo'] = round(z_value, 3) if z_value is not None else None
            support_layer.updateFeature(feature)
            
            # Atualizar a barra de progresso
            current_step += 1
            self._safe_set_progress(current_step)
            self._ui_pump(step=current_step, every_steps=50)

        support_layer.commitChanges()
        
        # Remover a barra de progresso
        self._close_progress_bar()

        end_time = time.time()
        elapsed_time = end_time - start_time

        self.mostrar_mensagem(self.tr("Camada de suporte criada com sucesso em {elapsed_time:.2f} segundos.").format(elapsed_time=elapsed_time), "Sucesso")

        # Retorna a camada sem adicionar ao projeto
        return support_layer

    def _calcular_area_trapezio(self, y_values, x_values):
        """
        Calcula área pelo método dos trapézios sem depender de np.trapz.

        Isso evita erro no QGIS 4 / Python 3.12 quando o NumPy instalado
        não possui mais o atributo trapz.
        """
        y_values = np.asarray(y_values, dtype=float)
        x_values = np.asarray(x_values, dtype=float)

        validos = np.isfinite(y_values) & np.isfinite(x_values)
        if np.count_nonzero(validos) < 2:
            return 0.0

        y_values = y_values[validos]
        x_values = x_values[validos]

        return float(np.sum((y_values[1:] + y_values[:-1]) * (x_values[1:] - x_values[:-1]) / 2.0))

    def _calcular_areas_com_taludes(self, estacas_distances, estacas_novoz, apoio_distances, apoio_elevations):
        """
        Calcula corte e aterro usando somente os taludes habilitados.
        Sem talude, o domínio termina exatamente na estaca correspondente.
        """
        x_end0, y_end0, x_end1, y_end1 = self._obter_limites_taludes(estacas_distances, estacas_novoz, apoio_distances, apoio_elevations)

        x_projeto = [
            float(x_end0),
            *map(float, estacas_distances),
            float(x_end1)]

        y_projeto = [
            float(y_end0),
            *map(float, estacas_novoz),
            float(y_end1)]

        # Ordena e elimina coordenadas X duplicadas
        pares_projeto = sorted(zip(x_projeto, y_projeto))
        x_projeto_unico = []
        y_projeto_unico = []

        for x, y in pares_projeto:
            if (x_projeto_unico
                and abs(x - x_projeto_unico[-1]) <= 1e-12):
                y_projeto_unico[-1] = y
            else:
                x_projeto_unico.append(x)
                y_projeto_unico.append(y)

        x_terreno = np.asarray(apoio_distances, dtype=float)
        y_terreno = np.asarray(apoio_elevations, dtype=float)

        ordem_terreno = np.argsort(x_terreno)
        x_terreno = x_terreno[ordem_terreno]
        y_terreno = y_terreno[ordem_terreno]

        xmin = max(x_projeto_unico[0], float(x_terreno[0]))
        xmax = min(x_projeto_unico[-1], float(x_terreno[-1]))

        if xmax <= xmin:
            return 0.0, 0.0

        x_values = sorted(set(
            [x for x in x_projeto_unico if xmin <= x <= xmax]
            + [float(x) for x in x_terreno if xmin <= x <= xmax]
            + [xmin, xmax]))

        y_projeto_interp = np.interp(x_values, x_projeto_unico, y_projeto_unico)
        y_terreno_interp = np.interp(x_values, x_terreno, y_terreno)

        diferencas = y_projeto_interp - y_terreno_interp

        # Insere os cruzamentos entre projeto e terreno
        intersecoes = []

        for indice in range(len(x_values) - 1):
            diferenca_0 = diferencas[indice]
            diferenca_1 = diferencas[indice + 1]

            if diferenca_0 * diferenca_1 < 0:
                x0 = x_values[indice]
                x1 = x_values[indice + 1]
                x_intersecao = (x0 + (x1 - x0) * diferenca_0 / (diferenca_0 - diferenca_1))

                intersecoes.append(float(x_intersecao))

        if intersecoes:
            x_values = sorted(set(x_values + intersecoes))

            y_projeto_interp = np.interp(x_values, x_projeto_unico, y_projeto_unico)
            y_terreno_interp = np.interp(x_values, x_terreno, y_terreno)

        x_values = np.asarray(x_values, dtype=float)
        diferencas = y_projeto_interp - y_terreno_interp

        area_aterro = self._calcular_area_trapezio(np.maximum(diferencas, 0), x_values)

        area_corte = self._calcular_area_trapezio(np.maximum(-diferencas, 0), x_values)

        return abs(area_aterro), abs(area_corte)

    def atualizar_listWidgetInfo_com_inclinacao_e_area(self, estacas_distances, estacas_novoz, apoio_distances, apoio_elevations):
        """
        Calcula a inclinação média das linhas 'Corte' e 'Terreno Natural' e a área das regiões hachuradas
        (azul para a área acima e vermelha para a área abaixo) e atualiza o listWidgetInfo.
        A inclinação e as áreas são exibidas no listWidgetInfo com cores e tamanho de fonte aprimorados.
        """
        distancia_total_corte = 0.0
        desnivel_total_corte = 0.0
        sinal_inclinacao = 0.0

        for i in range(1, len(estacas_distances)):
            dx = float(estacas_distances[i]) - float(estacas_distances[i - 1])
            dz = float(estacas_novoz[i]) - float(estacas_novoz[i - 1])

            if abs(dx) > 1e-12:
                distancia_total_corte += abs(dx)
                desnivel_total_corte += abs(dz)

                if sinal_inclinacao == 0.0 and abs(dz) > 1e-12:
                    sinal_inclinacao = -1.0 if dz > 0 else 1.0

        if distancia_total_corte > 0:
            inclinacao_corte = sinal_inclinacao * (desnivel_total_corte / distancia_total_corte) * 100.0
        else:
            inclinacao_corte = 0.0

        # Calcular inclinação da linha "Terreno Natural"
        delta_x_terreno = apoio_distances[-1] - apoio_distances[0]
        delta_y_terreno = apoio_elevations[-1] - apoio_elevations[0]
        if delta_x_terreno != 0:
            inclinacao_terreno = (delta_y_terreno / delta_x_terreno) * 100  # Convertido para porcentagem
        else:
            inclinacao_terreno = 0

        # Calcula as áreas considerando somente os taludes habilitados
        area_azul, area_vermelha = self._calcular_areas_com_taludes(estacas_distances, estacas_novoz, apoio_distances, apoio_elevations)

        # Atualizar listWidgetInfo
        self.listWidgetInfo.clear()  # Limpa o conteúdo anterior

        # Definir fonte e estilo para o texto
        font = QFont()
        font.setPointSize(9)  # Aumenta o tamanho da fonte

        # Função auxiliar para criar itens estilizados
        def criar_item(texto, cor):
            item = QListWidgetItem(texto)
            item.setFont(font)
            item.setForeground(QColor(cor))
            return item

        # Adicionar informações de inclinação ao listWidgetInfo
        self.listWidgetInfo.addItem(criar_item(self.tr("Incl. Corte/Aterro: {valor:.2f}%").format(valor=inclinacao_corte), "blue"))
        self.listWidgetInfo.addItem(criar_item(self.tr("Incl. Média Terreno: {valor:.2f}%").format(valor=inclinacao_terreno), "magenta"))

        # Adicionar informações de área ao listWidgetInfo
        self.listWidgetInfo.addItem(criar_item(self.tr("Área de Aterro: {valor:.2f} m²").format(valor=area_azul), "blue"))
        self.listWidgetInfo.addItem(criar_item(self.tr("Área de Corte: {valor:.2f} m²").format(valor=area_vermelha), "red"))

    def find_layer(self, layer_name, layer_type):
        """Função auxiliar para encontrar uma camada no projeto por nome."""
        for layer in QgsProject.instance().mapLayers().values():
            if layer.name() == layer_name and isinstance(layer, layer_type):
                return layer
        return None

    def setup_table_widget_signals(self):
        """Configura os sinais do tableWidgetLista2."""
        self.tableWidgetLista2.cellChanged.connect(self.update_graph_from_table_widget)

    def limpar_tableWidgetLista2(self, removed_layer_ids):
        """Limpa o tableWidgetLista2 se a camada selecionada no comboBoxGrupoZ for removida."""
        if self._atualizacoes_camadas_suspensas():
            return

        # Obtém o ID da camada atualmente selecionada no comboBoxGrupoZ
        selected_layer_id = self.comboBoxGrupoZ.currentData()

        # Verifica se a camada removida é a mesma que está selecionada no comboBoxGrupoZ
        if selected_layer_id in removed_layer_ids:
            # Limpa o tableWidgetLista2 se a camada foi removida
            self.tableWidgetLista2.clearContents()
            self.tableWidgetLista2.setRowCount(0)
            self.tableWidgetLista2.setColumnCount(0)

            # Limpa o gráfico no scrollAreaGrafico
            self.reset_scroll_area_grafico()

    def update_graph_from_table_widget(self, row, column):
        """Atualiza o gráfico dinamicamente quando valores no tableWidgetLista2 são alterados."""

        if getattr(self, "_updating_table", False) or getattr(self, "_updating_graph", False):
            return

        selected_layer_id = self.comboBoxGrupoZ.currentData()
        estacas_layer = QgsProject.instance().mapLayer(selected_layer_id)

        if not isinstance(estacas_layer, QgsVectorLayer):
            self.mostrar_mensagem(self.tr("Nenhuma camada válida de 'Pontos com Z' foi selecionada."), "Erro")
            return

        if self.tableWidgetLista2.rowCount() < 2:
            self.mostrar_mensagem(self.tr("É necessário pelo menos duas linhas no tableWidgetLista2."), "Erro")
            return

        # Aplica as mudanças do tableWidgetLista2 à camada
        self.apply_table_widget_changes_to_layer(estacas_layer)

        self._updating_graph = True
        try:
            self.setup_graph_in_scroll_area()
        finally:
            self._updating_graph = False

    def apply_single_cell_change_to_layer(self, layer, row, column):
        if not isinstance(layer, QgsVectorLayer):
            return

        item_id = self.tableWidgetLista2.item(row, 0)
        if not item_id:
            return
        fid = item_id.data(Qt.ItemDataRole.UserRole)
        if fid is None:
            return

        cell = self.tableWidgetLista2.item(row, column)
        if cell is None:
            return

        field = layer.fields()[column]
        field_name = field.name()

        feat = layer.getFeature(int(fid))
        if not feat.isValid():
            return

        new_val = cell.text()
        old_val = feat.attribute(field_name)

        # evita escrever se não mudou de verdade
        if str(old_val) == str(new_val):
            return

        with edit(layer):
            feat.setAttribute(field_name, new_val)
            layer.updateFeature(feat)

    def update_tableWidgetLista2(self, layer):
        """
        Atualiza o conteúdo do tableWidgetLista2 exibindo os dados da camada informada,
        sem disparar cellChanged/itemChanged (evita loop).
        """
        if not isinstance(layer, QgsVectorLayer) or not layer.isValid():
            return

        self._updating_table = True
        blocker = QtCore.QSignalBlocker(self.tableWidgetLista2)
        try:
            self.tableWidgetLista2.setUpdatesEnabled(False)

            # Limpa
            self.tableWidgetLista2.clearContents()
            self.tableWidgetLista2.setRowCount(0)

            fields = layer.fields()
            self.tableWidgetLista2.setColumnCount(len(fields))
            self.tableWidgetLista2.setHorizontalHeaderLabels(self._traduzir_cabecalhos_grafico(fields))

            # Popula
            for row_idx, feat in enumerate(layer.getFeatures()):
                self.tableWidgetLista2.insertRow(row_idx)

                for col_idx, field in enumerate(fields):
                    val = feat[field.name()]
                    txt = "" if val is None else str(val)

                    item = QTableWidgetItem(txt)

                    # IMPORTANTÍSSIMO: guardar o fid no UserRole da COLUNA 0,
                    if col_idx == 0:
                        item.setData(Qt.ItemDataRole.UserRole, int(feat.id()))
                        item.setFlags(Qt.ItemFlag.ItemIsSelectable | Qt.ItemFlag.ItemIsEnabled)  # não editável
                    else:
                        # Se você quer permitir edição, deixe editável:
                        item.setFlags(Qt.ItemFlag.ItemIsSelectable | Qt.ItemFlag.ItemIsEnabled| Qt.ItemFlag.ItemIsEditable)

                    self.tableWidgetLista2.setItem(row_idx, col_idx, item)

            self.tableWidgetLista2.resizeRowsToContents()
            self.tableWidgetLista2.resizeColumnsToContents()

        finally:
            self.tableWidgetLista2.setUpdatesEnabled(True)
            self._updating_table = False

    def set_spinboxes_from_tablewidget(self):
        """Define H inicial e H final usando os extremos reais de dist_acumulada da camada atual."""

        layer_id = self.comboBoxGrupoZ.currentData()
        layer = QgsProject.instance().mapLayer(layer_id)

        if not isinstance(layer, QgsVectorLayer):
            self._set_h_values_without_jumping_tab(0.0, 0.0)
            return

        idx_desnivel = layer.fields().indexFromName("Desnivel")
        idx_distancia = layer.fields().indexFromName("dist_acumulada")

        if idx_desnivel == -1 or idx_distancia == -1:
            self.mostrar_mensagem(self.tr("Os campos 'Desnivel' ou 'dist_acumulada' não foram encontrados na camada."), "Erro")
            return

        features = [
            feature for feature in layer.getFeatures()
            if feature["dist_acumulada"] is not None
            and feature["Desnivel"] is not None]

        if not features:
            self._set_h_values_without_jumping_tab(0.0, 0.0)
            return

        feature_inicial = min(features, key=lambda feature: float(feature["dist_acumulada"]))

        feature_final = max(features, key=lambda feature: float(feature["dist_acumulada"]))

        h_inicial = float(feature_inicial["Desnivel"])
        h_final = float(feature_final["Desnivel"])

        self._set_h_values_without_jumping_tab(h_inicial, h_final)

    def update_graph_background_color(self):
        """Atualiza a cor de fundo do gráfico dinamicamente ao alterar o checkBoxFundo."""
        # Verificar se o widget gráfico existe e não é None
        if hasattr(self, 'graphWidget') and self.graphWidget is not None:
            if self.checkBoxFundo.isChecked():
                self.graphWidget.setBackground('w')  # Fundo branco
            else:
                self.graphWidget.setBackground('k')  # Fundo preto
            
            # Atualizar as cores dos rótulos para se ajustarem à nova cor de fundo
            label_style = {'color': '#000', 'font-size': '9pt'} if self.checkBoxFundo.isChecked() else {'color': '#fff', 'font-size': '9pt'}
            self.graphWidget.setLabel('left', self.tr("Elevação (m)"), **label_style)
            self.graphWidget.setLabel('bottom', self.tr("Distância Acumulada (m)"), **label_style)

            # Atualizar o gráfico
            self.graphWidget.repaint()

    def recarregar_informacoes_do_grafico(self):
        """
        Recalcula e atualiza o listWidgetInfo com a inclinação média e área das regiões hachuradas,
        com base no gráfico atualmente exibido.
        """
        # Certifique-se de que há dados no gráfico para atualizar as informações
        if hasattr(self, 'estacas_distances') and hasattr(self, 'apoio_distances'):
            # Calcular e atualizar a inclinação e áreas no listWidgetInfo
            self.atualizar_listWidgetInfo_com_inclinacao_e_area(
                self.estacas_distances, self.estacas_novoz,
                self.apoio_distances, self.apoio_elevations)

    def setup_graph_in_scroll_area(self):
        """
        Configura e exibe o gráfico dentro da scrollAreaGrafico.
        Remove gráficos antigos e adiciona o novo widget gráfico na área de rolagem.
        """
        # Limpa o gráfico existente
        self.reset_scroll_area_grafico()

        # Obter o ID da camada selecionada no comboBoxGrupoZ
        selected_layer_id = self.comboBoxGrupoZ.currentData()
        estacas_layer = QgsProject.instance().mapLayer(selected_layer_id)

        if not isinstance(estacas_layer, QgsVectorLayer):
            # self.mostrar_mensagem("Nenhuma camada válida selecionada no comboBoxGrupoZ.", "Erro")
            return

        # Definir o nome da camada de pontos de apoio associada
        support_layer_name = self.tr("{layer_name}_PontosApoio").format(layer_name=estacas_layer.name())

        # Encontrar a camada de pontos de apoio
        pontos_apoio_layer = self.find_layer(support_layer_name, QgsVectorLayer)

        if not pontos_apoio_layer:
            # self.mostrar_mensagem(f"A camada de apoio '{support_layer_name}' não foi encontrada.", "Erro")
            return

        # Coletando dados das camadas para plotagem
        estacas_data = [
            (f['dist_acumulada'], f['NovoZ'], f['Z'], f['Desnivel'], f.geometry().asPoint().x(), f.geometry().asPoint().y())
            for f in estacas_layer.getFeatures()]

        pontos_apoio_data = [
            (f['Acumula_dist'], f['Znovo']) for f in pontos_apoio_layer.getFeatures()]

        # Verificar se há dados nas camadas
        if not estacas_data:
            self.mostrar_mensagem(self.tr("Nenhum dado encontrado na camada de estacas."), "Erro")
            return

        if not pontos_apoio_data:
            self.mostrar_mensagem(self.tr("Nenhum dado encontrado na camada de pontos de apoio."), "Erro")
            return

        # Ordenando dados baseados em 'dist_acumulada' e 'Acumula_dist'
        estacas_data.sort(key=lambda x: x[0])
        pontos_apoio_data.sort(key=lambda x: x[0])

        # Desempacotando os dados
        estacas_distances, estacas_novoz, estacas_z, estacas_desnivel, estacas_x, estacas_y = zip(*estacas_data)
        apoio_distances, apoio_elevations = zip(*pontos_apoio_data)

        # Criando o widget de gráfico PyQtGraph
        self.graphWidget = pg.PlotWidget()

        # Habilitar antialiasing para suavizar as linhas
        self.graphWidget.setAntialiasing(True)

        # Armazenar os dados para uso posterior
        self.estacas_distances = estacas_distances
        self.estacas_novoz = estacas_novoz
        self.apoio_distances = apoio_distances
        self.apoio_elevations = apoio_elevations

        # Criar linhas de referência para o cursor
        self.vLine = pg.InfiniteLine(angle=90, movable=False, pen=pg.mkPen('g', style=QtCore.Qt.PenStyle.DashLine))
        self.hLine = pg.InfiniteLine(angle=0, movable=False, pen=pg.mkPen('g', style=QtCore.Qt.PenStyle.DashLine))
        self.graphWidget.addItem(self.vLine, ignoreBounds=True)
        self.graphWidget.addItem(self.hLine, ignoreBounds=True)

        # Inicialmente, as linhas são invisíveis
        self.vLine.hide()
        self.hLine.hide()

        # Criar o TextItem para exibir as coordenadas
        self.coord_text = pg.TextItem(anchor=(0,1))
        self.graphWidget.addItem(self.coord_text)
        self.coord_text.hide()

        # Conectar o evento de movimento do mouse
        self.proxy = pg.SignalProxy(self.graphWidget.scene().sigMouseMoved, rateLimit=60, slot=self.mouse_moved)

        # Verificar o estado do checkBoxFundo para definir a cor de fundo
        if self.checkBoxFundo.isChecked():
            self.graphWidget.setBackground('w')  # Fundo branco
        else:
            self.graphWidget.setBackground('k')  # Fundo preto

        # Criação do layout para o gráfico dentro do scrollAreaGrafico
        layout = QtWidgets.QVBoxLayout()
        layout.addWidget(self.graphWidget)

        # Criando um widget container para o layout e o gráfico
        container_widget = QtWidgets.QWidget()
        container_widget.setLayout(layout)

        # Definindo as dimensões do container para caber no scrollAreaGrafico
        container_widget.setMinimumSize(623, 250)

        # Configurando o widget para o scrollAreaGrafico
        self.scrollAreaGrafico.setWidget(container_widget)

        # Renderizar o gráfico com alta qualidade
        self.graphWidget.setRenderHints(QtGui.QPainter.RenderHint.Antialiasing | QtGui.QPainter.RenderHint.SmoothPixmapTransform)

        # Plotar a linha "Corte" (dados de estacas)
        self.graphWidget.plot(estacas_distances, estacas_novoz, pen=pg.mkPen('b', width=2), name = self.tr("Corte"), antialias=True)

        # Plotar a linha "Terreno Natural" (dados de pontos de apoio)
        self.graphWidget.plot(apoio_distances, apoio_elevations, pen=pg.mkPen('m', width=2), name=self.tr("Terreno Natural"), antialias=True)

        # Adicionar grades ao gráfico para facilitar a visualização
        self.graphWidget.showGrid(x=True, y=True, alpha=0.3)

        # **Ajuste do zoom para incluir margens**
        x_min = min(estacas_distances) - (0.05 * (max(estacas_distances) - min(estacas_distances)))  # Margem de 5%
        x_max = max(estacas_distances) + (0.05 * (max(estacas_distances) - min(estacas_distances)))  # Margem de 5%
        y_min = min(min(estacas_novoz), min(apoio_elevations)) - 2  # Inclui uma margem extra no Y
        y_max = max(max(estacas_novoz), max(apoio_elevations)) + 2  # Inclui uma margem extra no Y

        self.graphWidget.setXRange(x_min, x_max)
        self.graphWidget.setYRange(y_min, y_max)

        # Adicionar rótulos e melhorar o tamanho das fontes
        label_style = {'color': '#000', 'font-size': '8pt'} if self.checkBoxFundo.isChecked() else {'color': '#fff', 'font-size': '8pt'}

        self.graphWidget.setLabel('left', self.tr("Elevação (m)"), **label_style)
        self.graphWidget.setLabel('bottom', self.tr("Distância Acumulada (m)"), **label_style)

        # Adicionar legenda
        self.graphWidget.addLegend()

        # Exibir a inclinação no gráfico
        self.exibir_inclinacao_no_grafico(estacas_distances, estacas_novoz)

        # Adicionar as linhas inclinadas e obter os pontos finais
        x_end0, y_end0, x_end1, y_end1 = self.adicionar_linhas_inclinadas(estacas_distances, estacas_novoz, apoio_distances, apoio_elevations)

        # Armazena os taludes para o cursor de coordenadas
        if self.checkBoxTaludeI.isChecked():
            self.talude_esquerdo = ((estacas_distances[0], estacas_novoz[0]), (x_end0, y_end0))
        else:
            self.talude_esquerdo = None

        if self.checkBoxTaludeF.isChecked():
            self.talude_direito = ((estacas_distances[-1], estacas_novoz[-1]), (x_end1, y_end1))
        else:
            self.talude_direito = None

        # Adicionar a hachura entre as linhas
        self.adicionar_hachura(estacas_distances, estacas_novoz, apoio_distances, apoio_elevations, x_end0, y_end0, x_end1, y_end1)

        # A prévia raster não muda durante a exclusão de camadas vetoriais.
        # Evita uma renderização síncrona desnecessária nesse caso.
        if not getattr(self, "_suspender_render_raster", False):
            self.display_raster()

        # Exibir a inclinação no gráfico
        self.exibir_inclinacao_no_grafico(estacas_distances, estacas_novoz)

        # Atualizar o listWidgetInfo com inclinação e áreas
        self.atualizar_listWidgetInfo_com_inclinacao_e_area(estacas_distances, estacas_novoz, apoio_distances, apoio_elevations)

        # Após configurar o gráfico com sucesso, habilita o pushButtonExportarDXF
        self.pushButtonExportarDXF.setEnabled(True)

        self._current_graph_layer_id = selected_layer_id  # ← novo

    def delete_selected_layer(self):
        """
        Deleta a camada selecionada no comboBoxGrupoZ e sua
        respectiva camada de pontos de apoio.

        A remoção é realizada em lote para evitar várias
        reconstruções da interface.
        """
        selected_layer_id = (self.comboBoxGrupoZ.currentData())

        if not selected_layer_id:
            self.mostrar_mensagem(self.tr("Nenhuma camada selecionada."), "Erro")

            return

        layer = QgsProject.instance().mapLayer(selected_layer_id)

        if not layer:
            self.mostrar_mensagem(self.tr("A camada selecionada não foi encontrada."), "Erro")

            return

        support_layer_name = self.tr("{layer_name}_PontosApoio").format(layer_name=layer.name())

        support_layer = self.find_layer(support_layer_name, QgsVectorLayer)

        project = QgsProject.instance()

        # Camadas removidas em uma única operação
        layers_to_remove = [layer.id()]

        if (support_layer
            and support_layer.id() not in layers_to_remove):
            layers_to_remove.append(support_layer.id())

        # Bloqueia as atualizações disparadas pelos sinais de remoção
        self._excluindo_camadas = True
        self._suspender_render_raster = True

        self.pushButtonDel.setEnabled(False)

        try:
            project.removeMapLayers(layers_to_remove)

            root = project.layerTreeRoot()

            # Remove os grupos somente quando ficarem vazios
            for group_name in (
                self.tr("Pontos com Z"),
                self.tr("Pontos Apoio")):
                group = root.findGroup(group_name)

                if (group
                    and not group.children()):

                    root.removeChildNode(group)

        except Exception as error:
            self.mostrar_mensagem(self.tr("Erro ao excluir a camada: {error}").format(error=str(error)), "Erro")

            return

        finally:
            self._excluindo_camadas = False

            try:
                # Atualiza somente o combo relacionado ao gráfico.
                # comboBoxCamadas não precisa ser reconstruído aqui.
                self.update_combo_box_grupo_z()

                self._atualizar_estado_pushButtonSalvar()

                # Se era a última camada, limpa e zera os controles
                if self.comboBoxGrupoZ.count() == 0:
                    self.tableWidgetLista2.clearContents()
                    self.tableWidgetLista2.setRowCount(0)
                    self.tableWidgetLista2.setColumnCount(0)

                    self.listWidgetInfo.clear()

                    self.reset_scroll_area_grafico()

                    with (QSignalBlocker(
                            self.doubleSpinBoxHinicial),
                        QSignalBlocker(
                            self.doubleSpinBoxHFinal),
                        QSignalBlocker(
                            self.doubleSpinBoxHinicial_Cota),
                        QSignalBlocker(
                            self.doubleSpinBoxHFinal_Cota)):
                        self.doubleSpinBoxHinicial.setValue(
                            0.0)

                        self.doubleSpinBoxHFinal.setValue(
                            0.0)

                        self.doubleSpinBoxHinicial_Cota.setValue(
                            0.0)

                        self.doubleSpinBoxHFinal_Cota.setValue(
                            0.0)

                # Atualiza o canvas somente depois que a função terminar
                QTimer.singleShot(0, self.iface.mapCanvas().refresh)

            finally:
                self._suspender_render_raster = False

        self.mostrar_mensagem(self.tr("Camada e pontos de apoio excluídos com sucesso."), "Sucesso")

    def mouse_moved(self, evt):
        """
        Atualiza o cursor de Elevação/Distância sobre:
        - Corte/Aterro;
        - Terreno Natural completo;
        - talude esquerdo;
        - talude direito.

        A tolerância é baseada em pixels, mantendo o comportamento
        consistente mesmo com alterações de zoom.
        """
        pos = evt[0]

        if not self.graphWidget.plotItem.sceneBoundingRect().contains(pos):
            self.vLine.hide()
            self.hLine.hide()
            self.coord_text.hide()
            return

        vb = self.graphWidget.plotItem.vb
        mouse_point = vb.mapSceneToView(pos)

        x_mouse = mouse_point.x()
        y_mouse = mouse_point.y()

        candidatos = []

        # Tolerância visual em pixels
        try:
            _, pixel_y = vb.viewPixelSize()
            tolerancia = abs(pixel_y) * 22
        except Exception:
            intervalo_y = max(self.apoio_elevations) - min(self.apoio_elevations)
            tolerancia = max(intervalo_y * 0.08, 0.20)

        # 1. TERRENO NATURAL COMPLETO
        x_terreno_min = min(self.apoio_distances)
        x_terreno_max = max(self.apoio_distances)

        if x_terreno_min <= x_mouse <= x_terreno_max:
            y_terreno = float(np.interp(x_mouse, self.apoio_distances, self.apoio_elevations))

            candidatos.append((abs(y_mouse - y_terreno), x_mouse, y_terreno))

        # 2. CORTE / ATERRO
        x_corte_min = min(self.estacas_distances)
        x_corte_max = max(self.estacas_distances)

        if x_corte_min <= x_mouse <= x_corte_max:
            y_corte = float(np.interp(x_mouse, self.estacas_distances, self.estacas_novoz))

            candidatos.append((abs(y_mouse - y_corte), x_mouse, y_corte))

        # Função auxiliar para os taludes
        def adicionar_candidato_segmento(segmento):
            if not segmento:
                return

            (x1, y1), (x2, y2) = segmento

            x_min = min(x1, x2)
            x_max = max(x1, x2)

            if not (x_min <= x_mouse <= x_max):
                return

            dx = x2 - x1

            if abs(dx) < 1e-12:
                return

            fator = (x_mouse - x1) / dx
            y_segmento = y1 + fator * (y2 - y1)

            candidatos.append((abs(y_mouse - y_segmento), x_mouse, y_segmento))

        # 3. TALUDE ESQUERDO
        adicionar_candidato_segmento(getattr(self, "talude_esquerdo", None))

        # 4. TALUDE DIREITO
        adicionar_candidato_segmento(getattr(self, "talude_direito", None))

        # Nenhuma linha disponível neste X
        if not candidatos:
            self.vLine.hide()
            self.hLine.hide()
            self.coord_text.hide()
            return

        # Escolhe a linha mais próxima do mouse
        distancia, x_snap, y_snap = min(candidatos, key=lambda item: item[0])

        # Fora da tolerância
        if distancia > tolerancia:
            self.vLine.hide()
            self.hLine.hide()
            self.coord_text.hide()
            return

        # Cor do texto conforme o fundo
        cor_texto = 'k' if self.checkBoxFundo.isChecked() else 'w'

        # Atualizar crosshair
        self.vLine.setPos(x_snap)
        self.hLine.setPos(y_snap)
        self.vLine.show()
        self.hLine.show()

        # Atualizar informações
        self.coord_text.setHtml(
            "{}<br>{}".format(
                self.tr("Elevação: {elevation:.2f} m").format(
                    elevation=y_snap),
                self.tr("Distância: {distance:.2f} m").format(
                    distance=x_snap)))

        self.coord_text.setFont(QtGui.QFont('Arial', 8, weight=QtGui.QFont.Weight.Bold))

        self.coord_text.setColor(cor_texto)
        self.coord_text.setPos(x_snap, y_snap)
        self.coord_text.show()

    def exibir_inclinacao_no_grafico(self, estacas_distances, estacas_novoz):
        """Exibe a inclinação entre o primeiro e o último ponto da linha 'Corte' no gráfico, centralizado e alinhado à linha."""
        # Calculando a diferença em distâncias e elevações
        distancia_total = 0.0
        desnivel_total = 0.0
        sinal_inclinacao = 0.0

        for i in range(1, len(estacas_distances)):
            delta_x_local = float(estacas_distances[i]) - float(estacas_distances[i - 1])
            delta_y_local = float(estacas_novoz[i]) - float(estacas_novoz[i - 1])

            if abs(delta_x_local) > 1e-12:
                distancia_total += abs(delta_x_local)
                desnivel_total += abs(delta_y_local)

                if sinal_inclinacao == 0.0 and abs(delta_y_local) > 1e-12:
                    sinal_inclinacao = -1.0 if delta_y_local > 0 else 1.0

        if distancia_total > 0:
            inclinacao_percent = sinal_inclinacao * (desnivel_total / distancia_total) * 100.0
        else:
            inclinacao_percent = 0.0

        delta_x = estacas_distances[-1] - estacas_distances[0]
        delta_y = estacas_novoz[-1] - estacas_novoz[0]

        # Calculando a posição média
        distancia_media = (estacas_distances[-1] + estacas_distances[0]) / 2
        z_medio = (estacas_novoz[-1] + estacas_novoz[0]) / 2

        # Determina se o perfil está predominantemente acima ou abaixo do terreno
        terreno_nas_estacas = np.interp(estacas_distances, self.apoio_distances, self.apoio_elevations)

        diferenca_media = float(np.mean(np.asarray(estacas_novoz, dtype=float) - terreno_nas_estacas))

        # Usa também o terreno para obter um afastamento visual perceptível
        valores_y = (list(map(float, estacas_novoz))
            + list(map(float, self.apoio_elevations)))

        amplitude_vertical = max(valores_y) - min(valores_y)
        deslocamento_texto = max(0.35, amplitude_vertical * 0.08)

        if diferenca_media >= 0:
            # Aterro: texto acima da linha do projeto
            z_texto = z_medio + deslocamento_texto
        else:
            # Corte: texto abaixo da linha do projeto
            z_texto = z_medio - deslocamento_texto

        # Calculando o ângulo em graus
        angle = math.degrees(math.atan2(delta_y, delta_x))

        # Ajustar o ângulo para manter o texto legível e alinhado corretamente
        if angle < -90 or angle > 90:
            angle = angle + 180 if angle < 0 else angle - 180
        else:
            angle = -angle  # Inverte o ângulo para alinhar corretamente com a linha

        # Criando o TextItem
        color = 'k' if self.checkBoxFundo.isChecked() else 'w'
        self.inclinacao_text_item = pg.TextItem(f"{inclinacao_percent:.2f}%", anchor=(0.5, 0.5), color='b', border=None, fill=None)
        
        # Definindo o tamanho da fonte como 8pt
        self.inclinacao_text_item.setFont(QtGui.QFont('Arial', 12))

        # Posiciona o texto acima da linha
        self.inclinacao_text_item.setPos(distancia_media, z_texto)

        # Rotacionando o texto para alinhar com a linha "Corte"
        self.inclinacao_text_item.setRotation(angle)

        # Adicionando o TextItem ao gráfico
        self.graphWidget.addItem(self.inclinacao_text_item)

    def _configurar_sincronizacao_cotas(self):
        """Configura os campos de cota inicial e final."""
        self._sincronizando_cotas = False

        for spinbox in (
            self.doubleSpinBoxHinicial_Cota,
            self.doubleSpinBoxHFinal_Cota):

            # As cotas são valores absolutos e podem ser maiores que 9,99
            spinbox.setRange(-999999999.0, 999999999.0)
            spinbox.setDecimals(3)
            spinbox.setSingleStep(0.1)

        self.doubleSpinBoxHinicial.valueChanged.connect(
            self._atualizar_cota_inicial)

        self.doubleSpinBoxHFinal.valueChanged.connect(
            self._atualizar_cota_final)

        self.doubleSpinBoxHinicial_Cota.valueChanged.connect(
            self._atualizar_desnivel_inicial)

        self.doubleSpinBoxHFinal_Cota.valueChanged.connect(
            self._atualizar_desnivel_final)

        self.comboBoxGrupoZ.currentIndexChanged.connect(
            self._carregar_cotas_da_camada)

        self._carregar_cotas_da_camada()

    def _obter_dados_cotas_extremas(self):
        """
        Obtém Z e NovoZ da primeira e da última feição, considerando
        a ordenação pelo campo dist_acumulada.
        """
        layer_id = self.comboBoxGrupoZ.currentData()
        layer = QgsProject.instance().mapLayer(layer_id)

        if not isinstance(layer, QgsVectorLayer):
            return None

        for campo in ("Z", "NovoZ", "dist_acumulada"):
            if layer.fields().indexFromName(campo) == -1:
                return None

        dados = []

        for feature in layer.getFeatures():
            try:
                distancia = float(feature["dist_acumulada"])
                z = float(feature["Z"])
                novo_z = float(feature["NovoZ"])
            except (TypeError, ValueError):
                continue

            if not all(np.isfinite(valor) for valor in (distancia, z, novo_z)):

                continue

            dados.append((distancia, z, novo_z))

        if not dados:
            return None

        dados.sort(key=lambda item: item[0])

        _, z_inicial, novo_z_inicial = dados[0]
        _, z_final, novo_z_final = dados[-1]

        return z_inicial, novo_z_inicial, z_final, novo_z_final

    def _carregar_cotas_da_camada(self, *_):
        """
        Obtém NovoZ da primeira e da última estaca e configura os limites
        das cotas conforme o intervalo permitido nos desníveis.
        """
        dados = self._obter_dados_cotas_extremas()

        if dados is None:
            return

        z_inicial, novo_z_inicial, z_final, novo_z_final = dados

        # Limites absolutos permitidos para as cotas
        cota_inicial_minima = (z_inicial + self.doubleSpinBoxHinicial.minimum())

        cota_inicial_maxima = (z_inicial + self.doubleSpinBoxHinicial.maximum())

        cota_final_minima = (z_final + self.doubleSpinBoxHFinal.minimum())

        cota_final_maxima = (z_final + self.doubleSpinBoxHFinal.maximum())

        self._sincronizando_cotas = True

        try:
            with (
                QSignalBlocker(self.doubleSpinBoxHinicial),
                QSignalBlocker(self.doubleSpinBoxHFinal),
                QSignalBlocker(self.doubleSpinBoxHinicial_Cota),
                QSignalBlocker(self.doubleSpinBoxHFinal_Cota)):

                # Primeiro configura os limites, depois define os valores
                self.doubleSpinBoxHinicial_Cota.setRange(cota_inicial_minima, cota_inicial_maxima)

                self.doubleSpinBoxHFinal_Cota.setRange(cota_final_minima, cota_final_maxima)

                # Cotas atualmente existentes na camada
                self.doubleSpinBoxHinicial_Cota.setValue(novo_z_inicial)

                self.doubleSpinBoxHFinal_Cota.setValue(novo_z_final)

                # Diferenças entre a cota projetada e a cota natural
                self.doubleSpinBoxHinicial.setValue(novo_z_inicial - z_inicial)

                self.doubleSpinBoxHFinal.setValue(novo_z_final - z_final)

        finally:
            self._sincronizando_cotas = False

    def _atualizar_cota_inicial(self, h_inicial):
        """Atualiza somente a cota inicial."""
        if self._sincronizando_cotas:
            return

        dados = self._obter_dados_cotas_extremas()

        if dados is None:
            return

        z_inicial = dados[0]
        cota_inicial = z_inicial + h_inicial

        with QSignalBlocker(self.doubleSpinBoxHinicial_Cota):
            self.doubleSpinBoxHinicial_Cota.setValue(cota_inicial)

    def _atualizar_cota_final(self, h_final):
        """Atualiza somente a cota final."""
        if self._sincronizando_cotas:
            return

        dados = self._obter_dados_cotas_extremas()

        if dados is None:
            return

        z_final = dados[2]
        cota_final = z_final + h_final

        with QSignalBlocker(self.doubleSpinBoxHFinal_Cota):
            self.doubleSpinBoxHFinal_Cota.setValue(cota_final)

    def _atualizar_desnivel_inicial(self, cota_inicial):
        """Atualiza o desnível inicial a partir da cota informada."""
        if self._sincronizando_cotas:
            return

        dados = self._obter_dados_cotas_extremas()

        if dados is None:
            return

        z_inicial = dados[0]
        h_inicial = cota_inicial - z_inicial

        # Segurança adicional para respeitar o intervalo permitido
        h_inicial = max(
            self.doubleSpinBoxHinicial.minimum(),
            min(self.doubleSpinBoxHinicial.maximum(), h_inicial))

        self.doubleSpinBoxHinicial.setValue(h_inicial)

    def _atualizar_desnivel_final(self, cota_final):
        """Atualiza o desnível final a partir da cota informada."""
        if self._sincronizando_cotas:
            return

        dados = self._obter_dados_cotas_extremas()

        if dados is None:
            return

        z_final = dados[2]
        h_final = cota_final - z_final

        # Segurança adicional para respeitar o intervalo permitido
        h_final = max(
            self.doubleSpinBoxHFinal.minimum(),
            min(self.doubleSpinBoxHFinal.maximum(), h_final))

        self.doubleSpinBoxHFinal.setValue(h_final)

    def reset_scroll_area_grafico(self):
        """Limpa o conteúdo da scrollAreaGrafico ao iniciar o diálogo."""
        # Verifica se o widget gráfico existe e se ele não foi deletado
        if hasattr(self, 'graphWidget') and self.graphWidget is not None:
            # Remove o widget gráfico do scrollAreaGrafico
            if self.scrollAreaGrafico.widget():
                self.scrollAreaGrafico.takeWidget()

            # Remove a referência do graphWidget para garantir que ele seja recriado corretamente
            self.graphWidget = None

            # Desabilita o pushButtonExportarDXF já que não há gráfico
            self.pushButtonExportarDXF.setEnabled(False)

            # Limpa o listWidgetInfo, já que o gráfico foi removido
            self.listWidgetInfo.clear()

        self._current_graph_layer_id = None               # adicione antes de sair

    def atualizar_estado_pushButtonDel(self):
        """Ativa ou desativa o pushButtonDel conforme há ou não camadas no comboBoxGrupoZ."""
        self.pushButtonDel.setEnabled(self.comboBoxGrupoZ.count() > 0)

    def adicionar_hachura(self, estacas_distances, estacas_novoz, apoio_distances, apoio_elevations, x_end0, y_end0, x_end1, y_end1):
        """
        Adiciona hachuras limitadas pelas linhas inclinadas, a linha 'Terreno Natural' e a linha 'Corte'.
        A hachura fica vermelha se a linha 'Corte' estiver abaixo da linha 'Terreno Natural',
        e azul se a linha 'Corte' estiver acima da linha 'Terreno Natural'.
        """
        # Combinar os dados em uma lista de pontos x únicos e ordenados
        x_values = sorted(set(list(estacas_distances) + list(apoio_distances) + [x_end0, x_end1]))
        x_values = [x for x in x_values if estacas_distances[0] <= x <= estacas_distances[-1]]

        # Interpolar os valores de y para cada x
        y_corte = [np.interp(x, estacas_distances, estacas_novoz) for x in x_values]
        y_terreno = [np.interp(x, apoio_distances, apoio_elevations) for x in x_values]

        # Adicionar os pontos finais das linhas inclinadas (Taludes)
        x_values = [x_end0] + x_values + [x_end1]
        y_corte = [y_end0] + y_corte + [y_end1]
        y_terreno = [np.interp(x_end0, apoio_distances, apoio_elevations)] + y_terreno + [np.interp(x_end1, apoio_distances, apoio_elevations)]

        # Encontrar os pontos de interseção
        intersecoes = []
        for i in range(len(x_values) - 1):
            x1, x2 = x_values[i], x_values[i+1]
            y1_corte, y2_corte = y_corte[i], y_corte[i+1]
            y1_terreno, y2_terreno = y_terreno[i], y_terreno[i+1]

            # Verificar se há cruzamento entre os segmentos
            s1 = y1_corte - y1_terreno
            s2 = y2_corte - y2_terreno
            if s1 * s2 < 0:
                # Há interseção
                p_intersec = self.calcular_intersecao(
                    (x1, y1_corte), (x2, y2_corte),
                    (x1, y1_terreno), (x2, y2_terreno))
                if p_intersec:
                    intersecoes.append((i, p_intersec))

        # Inserir os pontos de interseção nas listas
        for idx, (i, (x_int, y_int)) in enumerate(intersecoes):
            insert_pos = i + 1 + idx
            x_values.insert(insert_pos, x_int)
            y_corte.insert(insert_pos, y_int)
            y_terreno.insert(insert_pos, y_int)  # Ambos têm o mesmo y no ponto de interseção

        # Dividir os segmentos com base nos pontos de interseção
        segmentos = []
        start_idx = 0
        for idx in range(1, len(x_values)):
            x_seg = x_values[start_idx:idx+1]
            y_corte_seg = y_corte[start_idx:idx+1]
            y_terreno_seg = y_terreno[start_idx:idx+1]

            # Determinar se 'Corte' está acima ou abaixo neste segmento
            diff = np.array(y_corte_seg) - np.array(y_terreno_seg)
            media_diff = np.mean(diff)
            if media_diff >= 0:
                cor_hachura = (0, 0, 255, 100)  # Azul
            else:
                cor_hachura = (255, 0, 0, 100)  # Vermelho

            segmentos.append((x_seg, y_corte_seg, y_terreno_seg, cor_hachura))
            start_idx = idx

        # Desenhar hachuras para cada segmento
        for x_seg, y_corte_seg, y_terreno_seg, cor_hachura in segmentos:
            path = QPainterPath()
            # Começar no primeiro ponto do segmento na linha 'Corte'
            path.moveTo(x_seg[0], y_corte_seg[0])

            # Adicionar pontos da linha 'Corte'
            for x, y in zip(x_seg, y_corte_seg):
                path.lineTo(x, y)

            # Adicionar pontos da linha 'Terreno Natural' em ordem reversa
            for x, y in zip(reversed(x_seg), reversed(y_terreno_seg)):
                path.lineTo(x, y)

            # Fechar o caminho
            path.closeSubpath()

            # Criar o item gráfico para o preenchimento
            hachura_brush = pg.mkBrush(color=cor_hachura)
            hachura_item = QGraphicsPathItem(path)
            hachura_item.setBrush(hachura_brush)
            hachura_item.setPen(pg.mkPen(None))  # Sem bordas

            # Adicionar o item ao gráfico
            self.graphWidget.addItem(hachura_item)

    def _on_estado_taludes_alterado(self, *_):
        """Atualiza gráfico, hachura e áreas após marcar ou desmarcar um talude."""
        if getattr(self, "graphWidget", None) is not None:
            self.setup_graph_in_scroll_area()

    def _obter_limites_taludes(self, estacas_distances, estacas_novoz, apoio_distances, apoio_elevations):
        """
        Retorna os limites do perfil de projeto considerando a existência
        ou não dos taludes inicial e final.
        """
        x0 = float(estacas_distances[0])
        y0 = float(estacas_novoz[0])
        x1 = float(estacas_distances[-1])
        y1 = float(estacas_novoz[-1])

        usar_talude_inicial = self.checkBoxTaludeI.isChecked()
        usar_talude_final = self.checkBoxTaludeF.isChecked()

        if usar_talude_inicial:
            terreno_inicial = float(
                np.interp(x0, apoio_distances, apoio_elevations))

            if y0 >= terreno_inicial:
                angulo = math.radians(45)
            else:
                angulo = math.radians(135)

            m_talude = math.tan(angulo)

            x_end0, y_end0 = self.encontrar_intersecao(x0, y0, m_talude, apoio_distances, apoio_elevations, lado="esquerda")
        else:
            # Sem talude: o perfil começa exatamente na primeira estaca
            x_end0, y_end0 = x0, y0

        if usar_talude_final:
            terreno_final = float(
                np.interp(x1, apoio_distances, apoio_elevations))

            if y1 >= terreno_final:
                angulo = math.radians(135)
            else:
                angulo = math.radians(45)

            m_talude = math.tan(angulo)

            x_end1, y_end1 = self.encontrar_intersecao(x1, y1, m_talude, apoio_distances, apoio_elevations, lado="direita")
        else:
            # Sem talude: o perfil termina exatamente na última estaca
            x_end1, y_end1 = x1, y1

        return x_end0, y_end0, x_end1, y_end1

    def adicionar_linhas_inclinadas(self, estacas_distances, estacas_novoz, apoio_distances, apoio_elevations):
        """
        Desenha somente os taludes habilitados e retorna os limites
        usados pela hachura e pelo cálculo das áreas.
        """
        x_end0, y_end0, x_end1, y_end1 = self._obter_limites_taludes(estacas_distances, estacas_novoz, apoio_distances, apoio_elevations)

        if self.checkBoxTaludeI.isChecked():
            self.graphWidget.plot([estacas_distances[0], x_end0], [estacas_novoz[0], y_end0], pen=pg.mkPen("b", width=1.5, style=QtCore.Qt.PenStyle.DashLine), antialias=True)

        if self.checkBoxTaludeF.isChecked():
            self.graphWidget.plot([estacas_distances[-1], x_end1], [estacas_novoz[-1], y_end1], pen=pg.mkPen("b", width=1.5, style=QtCore.Qt.PenStyle.DashLine), antialias=True)

        return x_end0, y_end0, x_end1, y_end1

    def encontrar_intersecao(self, x0, y0, m_talude, apoio_distances, apoio_elevations, lado):
        """
        Encontra o ponto de interseção entre a linha inclinada (talude) e a linha do Terreno Natural.
        """
        # Criar a equação da linha inclinada: y = m_talude * (x - x0) + y0

        # Dependendo do lado, percorremos os segmentos do Terreno Natural em ordem adequada
        if lado == 'esquerda':
            indices = range(len(apoio_distances) - 1)
        else:
            indices = range(len(apoio_distances) - 1, 0, -1)

        for i in indices:
            if lado == 'esquerda':
                x_tn1, y_tn1 = apoio_distances[i], apoio_elevations[i]
                x_tn2, y_tn2 = apoio_distances[i + 1], apoio_elevations[i + 1]
            else:
                x_tn1, y_tn1 = apoio_distances[i], apoio_elevations[i]
                x_tn2, y_tn2 = apoio_distances[i - 1], apoio_elevations[i - 1]

            # Calcular o coeficiente angular da linha do Terreno Natural
            if x_tn2 - x_tn1 != 0:
                m_tn = (y_tn2 - y_tn1) / (x_tn2 - x_tn1)
            else:
                m_tn = float('inf')  # Linha vertical

            # Se as linhas não forem paralelas, calcular o ponto de interseção
            if m_tn != m_talude:
                if m_tn != float('inf'):
                    x_intersect = ( (m_tn * x_tn1 - y_tn1) - (m_talude * x0 - y0) ) / (m_tn - m_talude)
                    y_intersect = m_talude * (x_intersect - x0) + y0
                else:
                    x_intersect = x_tn1
                    y_intersect = m_talude * (x_intersect - x0) + y0

                # Verificar se o ponto de interseção está dentro do segmento do Terreno Natural
                if (min(x_tn1, x_tn2) <= x_intersect <= max(x_tn1, x_tn2)) and (min(y_tn1, y_tn2) <= y_intersect <= max(y_tn1, y_tn2)):
                    # Encontramos o ponto de interseção
                    return x_intersect, y_intersect

        # Se não encontrar interseção, retornar o ponto final da linha do Terreno Natural
        if lado == 'esquerda':
            return apoio_distances[0], apoio_elevations[0]
        else:
            return apoio_distances[-1], apoio_elevations[-1]

    def escolher_local_para_salvar(self, nome_padrao, tipo_arquivo):
        """
        Abre um diálogo para o usuário escolher o local e o nome do arquivo para salvar, 
        com um nome padrão e filtro de tipo de arquivo.
        """
        # Acessa as configurações do QGIS para recuperar o último diretório utilizado
        settings = QSettings()
        lastDir = settings.value("lastDir", "")  # Usa uma string vazia como padrão se não houver último diretório
        
        # Gera o nome e a extensão do arquivo
        base_nome_padrao, extensao = os.path.splitext(nome_padrao)
        if not extensao:  # Caso o nome não inclua uma extensão, extrair do tipo_arquivo
            extensao = tipo_arquivo.split("*.")[-1].replace(")", "")
        numero = 1
        nome_proposto = base_nome_padrao

        # Incrementa o número no nome até encontrar um nome que não exista
        while os.path.exists(os.path.join(lastDir, nome_proposto + "." + extensao)):
            nome_proposto = f"{base_nome_padrao}_{numero}"
            numero += 1

        # Propõe o nome completo no último diretório utilizado
        nome_completo_proposto = os.path.join(lastDir, nome_proposto + "." + extensao)

        # Exibe a caixa de diálogo para salvar arquivos com o nome proposto
        fileName, _ = QFileDialog.getSaveFileName(self, self.tr("Salvar Camada"), nome_completo_proposto, tipo_arquivo)

        # Verifica se um nome de arquivo foi escolhido
        if fileName:
            # Atualiza o último diretório usado nas configurações do QGIS
            settings.setValue("lastDir", os.path.dirname(fileName))

            # Assegura que o arquivo tenha a extensão correta
            if not fileName.endswith(f".{extensao}"):
                fileName += f".{extensao}"

        return fileName  # Retorna o caminho completo do arquivo escolhido ou None se cancelado

    def obter_dados_para_exportacao(self):
        """
        Coleta e retorna os dados necessários para exportação a partir dos elementos da interface e camadas.
        """
        # Obter o ID da camada selecionada no comboBoxGrupoZ
        selected_layer_id = self.comboBoxGrupoZ.currentData()
        estacas_layer = QgsProject.instance().mapLayer(selected_layer_id)

        if not isinstance(estacas_layer, QgsVectorLayer):
            self.mostrar_mensagem(self.tr("Nenhuma camada válida de 'Pontos com Z' foi selecionada."), "Erro")
            return None, None

        # Definir o nome da camada de pontos de apoio associada
        support_layer_name = self.tr("{layer_name}_PontosApoio").format(layer_name=estacas_layer.name())

        # Encontrar a camada de pontos de apoio
        pontos_apoio_layer = self.find_layer(support_layer_name, QgsVectorLayer)

        if not pontos_apoio_layer:
            self.mostrar_mensagem(self.tr("A camada de apoio '{support_layer_name}' não foi encontrada.").format(support_layer_name=support_layer_name), "Erro")
            return None, None

        # Coletando dados das camadas para exportação
        estacas_data = [
            (f.id(), f['dist_acumulada'], f['NovoZ'], f['Z'], f['Desnivel'], f.geometry().asPoint().x(), f.geometry().asPoint().y())
            for f in estacas_layer.getFeatures()]

        pontos_apoio_data = [
            (f['Acumula_dist'], f['Znovo']) for f in pontos_apoio_layer.getFeatures()]

        # Verificar se há dados nas camadas
        if not estacas_data:
            self.mostrar_mensagem(self.tr("Nenhum dado encontrado na camada de estacas."), "Erro")
            return None, None

        if not pontos_apoio_data:
            self.mostrar_mensagem(self.tr("Nenhum dado encontrado na camada de pontos de apoio."), "Erro")
            return None, None

        # Ordenando dados baseados em 'dist_acumulada' e 'Acumula_dist'
        estacas_data.sort(key=lambda x: x[1])
        pontos_apoio_data.sort(key=lambda x: x[0])

        return estacas_data, pontos_apoio_data

    def exportar_linhas_talude(self, msp, estacas_data, pontos_apoio_data):
        """
        Exporta as linhas do talude utilizando os dados das estacas e pontos de apoio para o modelo msp.
        """
        # Desempacotando os dados
        estacas_ids, estacas_distances, estacas_novoz, _, _, _, _ = zip(*estacas_data)
        apoio_distances, apoio_elevations = zip(*pontos_apoio_data)

        if self.checkBoxTaludeI.isChecked():
            # **Linha de talude inicial**
            x0 = estacas_distances[0]
            y0 = estacas_novoz[0]

            if y0 >= np.interp(x0, apoio_distances, apoio_elevations):
                angle = math.radians(45)
            else:
                angle = math.radians(135)

            m_talude = math.tan(angle)

            # Encontrar o ponto de interseção no início
            x_end0, y_end0 = self.encontrar_intersecao_dxf(x0, y0, m_talude, apoio_distances, apoio_elevations, lado='esquerda')

            # Adicionar a linha de talude inicial ao DXF
            msp.add_lwpolyline([(x0, y0), (x_end0, y_end0)], dxfattribs={'layer': 'Talude'})

        if self.checkBoxTaludeF.isChecked():
            # **Linha de talude final**
            x1 = estacas_distances[-1]
            y1 = estacas_novoz[-1]

            if y1 >= np.interp(x1, apoio_distances, apoio_elevations):
                angle = math.radians(135)
            else:
                angle = math.radians(45)

            m_talude = math.tan(angle)

            # Encontrar o ponto de interseção no final
            x_end1, y_end1 = self.encontrar_intersecao_dxf(x1, y1, m_talude, apoio_distances, apoio_elevations, lado='direita')

            # Adicionar a linha de talude final ao DXF
            msp.add_lwpolyline([(x1, y1), (x_end1, y_end1)], dxfattribs={'layer': 'Talude'})

    def encontrar_intersecao_dxf(self, x0, y0, m_talude, apoio_distances, apoio_elevations, lado):
        """
        Encontra o ponto de interseção entre a linha inclinada (talude) e a linha do Terreno Natural para o DXF.
        """
        # Mesma lógica da função anterior, adaptada se necessário para o contexto do DXF

        # Dependendo do lado, percorremos os segmentos do Terreno Natural em ordem adequada
        if lado == 'esquerda':
            indices = range(len(apoio_distances) - 1)
        else:
            indices = range(len(apoio_distances) - 1, 0, -1)

        for i in indices:
            if lado == 'esquerda':
                x_tn1, y_tn1 = apoio_distances[i], apoio_elevations[i]
                x_tn2, y_tn2 = apoio_distances[i + 1], apoio_elevations[i + 1]
            else:
                x_tn1, y_tn1 = apoio_distances[i], apoio_elevations[i]
                x_tn2, y_tn2 = apoio_distances[i - 1], apoio_elevations[i - 1]

            # Calcular o coeficiente angular da linha do Terreno Natural
            if x_tn2 - x_tn1 != 0:
                m_tn = (y_tn2 - y_tn1) / (x_tn2 - x_tn1)
            else:
                m_tn = float('inf')  # Linha vertical

            # Se as linhas não forem paralelas, calcular o ponto de interseção
            if m_tn != m_talude:
                if m_tn != float('inf'):
                    x_intersect = ( (m_tn * x_tn1 - y_tn1) - (m_talude * x0 - y0) ) / (m_tn - m_talude)
                    y_intersect = m_talude * (x_intersect - x0) + y0
                else:
                    x_intersect = x_tn1
                    y_intersect = m_talude * (x_intersect - x0) + y0

                # Verificar se o ponto de interseção está dentro do segmento do Terreno Natural
                if (min(x_tn1, x_tn2) <= x_intersect <= max(x_tn1, x_tn2)) and (min(y_tn1, y_tn2) <= y_intersect <= max(y_tn1, y_tn2)):
                    # Encontramos o ponto de interseção
                    return x_intersect, y_intersect

        # Se não encontrar interseção, retornar o ponto final da linha do Terreno Natural
        if lado == 'esquerda':
            return apoio_distances[0], apoio_elevations[0]
        else:
            return apoio_distances[-1], apoio_elevations[-1]

    def exportar_linhas_principais(self, msp, estacas_data, pontos_apoio_data):
        """
        Exporta as linhas principais do projeto utilizando os dados das estacas e pontos de apoio para o modelo msp.
        """
        # Desempacotando os dados
        estacas_ids, estacas_distances, estacas_novoz, estacas_z, estacas_desnivel, estacas_x, estacas_y = zip(*estacas_data)
        apoio_distances, apoio_elevations = zip(*pontos_apoio_data)

        # Adicionar a linha 'Corte' como uma polilinha no DXF
        corte_points = list(zip(estacas_distances, estacas_novoz))
        msp.add_lwpolyline(corte_points, dxfattribs={'layer': 'Corte'})

        # Adicionar a linha 'Terreno Natural' como uma polilinha no DXF
        terreno_points = list(zip(apoio_distances, apoio_elevations))
        msp.add_lwpolyline(terreno_points, dxfattribs={'layer': 'Terreno_Natural'})

    def adicionar_informacoes_adicionais(self, msp, ponto_superior_esquerdo, x_margin, y_margin, estacas_data, pontos_apoio_data):
        """
        Adiciona informações de inclinação da linha de Corte, inclinação média do Terreno Natural,
        e áreas das hachuras (corte e aterro) no canto superior esquerdo do retângulo principal, organizadas em linha e coloridas.
        """
        # Cálculo das inclinações e áreas
        estacas_distances, estacas_novoz = zip(*[(e[1], e[2]) for e in estacas_data])
        apoio_distances, apoio_elevations = zip(*pontos_apoio_data)

        # Inclinação da linha de Corte
        distancia_total_corte = 0.0
        desnivel_total_corte = 0.0
        sinal_inclinacao = 0.0

        for i in range(1, len(estacas_distances)):
            dx = float(estacas_distances[i]) - float(estacas_distances[i - 1])
            dz = float(estacas_novoz[i]) - float(estacas_novoz[i - 1])

            if abs(dx) > 1e-12:
                distancia_total_corte += abs(dx)
                desnivel_total_corte += abs(dz)

                if sinal_inclinacao == 0.0 and abs(dz) > 1e-12:
                    sinal_inclinacao = -1.0 if dz > 0 else 1.0

        if distancia_total_corte > 0:
            inclinacao_corte = sinal_inclinacao * (desnivel_total_corte / distancia_total_corte) * 100.0
        else:
            inclinacao_corte = 0.0

        # Inclinação média do Terreno Natural
        inclinacao_terreno = ((apoio_elevations[-1] - apoio_elevations[0]) /  (apoio_distances[-1] - apoio_distances[0])) * 100

        # Cálculo das áreas (hachuras) - área de corte e área de aterro
        area_aterro, area_corte = self._calcular_areas_com_taludes(estacas_distances, estacas_novoz, apoio_distances, apoio_elevations)

        # Posição inicial para o texto no canto superior esquerdo, dentro do retângulo
        pos_x = ponto_superior_esquerdo[0] + x_margin * 0.5 # Um pouco afastado da borda esquerda
        pos_y = ponto_superior_esquerdo[1] - y_margin * 1.2  # Um pouco afastado da borda superior

        # Espaçamento horizontal entre as informações em linha
        spacing = 15

        # Adicionar as informações em linha
        msp.add_text(self.tr("Inclinação Corte: {inclinacao_corte:.2f}%").format(inclinacao_corte=inclinacao_corte), dxfattribs={
            'height': 0.5,
            'layer': 'Moldura',
            'color': 5,  # Azul
            'insert': (pos_x, pos_y)})
        pos_x += spacing

        msp.add_text(self.tr("Inclinação Média Terreno: {inclinacao_terreno:.2f}%").format(inclinacao_terreno=inclinacao_terreno), dxfattribs={
            'height': 0.5,
            'layer': 'Moldura',
            'color': 6,  # Magenta
            'insert': (pos_x, pos_y)})
        pos_x += spacing

        msp.add_text(self.tr("Área Aterro: {area_aterro:.2f} m2").format(area_aterro=abs(area_aterro)), dxfattribs={
            'height': 0.5,
            'layer': 'Moldura',
            'color': 5,  # Azul
            'insert': (pos_x, pos_y)})
        pos_x += spacing

        msp.add_text(self.tr("Área Corte: {area_corte:.2f} m2").format(area_corte=abs(area_corte)), dxfattribs={
            'height': 0.5,
            'layer': 'Moldura',
            'color': 1,  # Vermelho
            'insert': (pos_x, pos_y)})

    def adicionar_retangulo_ao_redor(self, msp, estacas_data, pontos_apoio_data):
        """
        Adiciona um retângulo ao redor das estacas e pontos de apoio no modelo msp.
        """
        # Desempacotando os dados
        estacas_ids, estacas_distances, estacas_novoz, _, _, _, _ = zip(*estacas_data)
        apoio_distances, apoio_elevations = zip(*pontos_apoio_data)

        # Definir os limites dos eixos usando os valores de apoio
        x_min = min(apoio_distances)
        x_max = max(apoio_distances)
        y_min = min(min(estacas_novoz), min(apoio_elevations))
        y_max = max(max(estacas_novoz), max(apoio_elevations))

        # Definir um intervalo mínimo para o eixo Y
        intervalo_minimo_y = 10  # Valor mínimo para o intervalo vertical
        intervalo_y = y_max - y_min

        if intervalo_y < intervalo_minimo_y:
            centro_y = (y_max + y_min) / 2
            y_min = centro_y - intervalo_minimo_y / 2
            y_max = centro_y + intervalo_minimo_y / 2

        # Adicionar margens
        x_margin = (x_max - x_min) * 0.05  # 5% de margem
        y_margin = (y_max - y_min) * 0.05  # 5% de margem

        # Definir uma margem mínima para garantir que o retângulo cubra adequadamente os eixos
        margem_minima = 0.75  # Ajuste este valor conforme necessário
        x_margin = max(x_margin, margem_minima)
        y_margin = max(y_margin, margem_minima)

        # Ajustar y_min e y_max com as margens
        x_min -= x_margin
        x_max += x_margin
        y_min -= y_margin
        y_max += y_margin

        # Adicionar margem extra ao retângulo para garantir espaço para os labels
        extra_margin = y_margin * 5  # Ajuste conforme necessário

        # Mantém a mesma faixa lateral dos rótulos inferiores
        recuo_rotulos = 4.0

        # Definir os quatro cantos do retângulo (com a margem extra)
        ponto_inferior_esquerdo = (x_min - extra_margin - recuo_rotulos, y_min - extra_margin)
        ponto_inferior_direito = (x_max + extra_margin, y_min - extra_margin)
        ponto_superior_direito = (x_max + extra_margin, y_max + extra_margin)
        ponto_superior_esquerdo = (x_min - extra_margin - recuo_rotulos, y_max + extra_margin)

        # Desenhar o retângulo como uma linha única (polilinha)
        msp.add_lwpolyline([
            ponto_inferior_esquerdo,
            ponto_inferior_direito,
            ponto_superior_direito,
            ponto_superior_esquerdo,
            ponto_inferior_esquerdo  # Fechar o loop para garantir que o retângulo se feche
        ], dxfattribs={'layer': 'Moldura'}, close=True)

        # Adicionar o texto no canto superior esquerdo do retângulo
        texto = self.tr("Perfil de Corte/Aterro sobre o Terreno Natural")
        msp.add_text(texto, dxfattribs={
            'height': 0.5,  # Ajustar tamanho do texto conforme necessário
            'layer': 'Moldura',  # Colocar na mesma camada do retângulo
            'insert': (ponto_superior_esquerdo[0] + x_margin * 0.5, ponto_superior_esquerdo[1] + y_margin * 0.5)  # Ajustar posição
        })

        # Chamar a função auxiliar para adicionar informações adicionais
        self.adicionar_informacoes_adicionais(msp, ponto_superior_esquerdo, x_margin, y_margin, estacas_data, pontos_apoio_data)

        # Retornar as coordenadas dos vértices inferiores e a altura do retângulo principal
        altura_retangulo_principal = y_max - y_min
        return ponto_inferior_esquerdo, ponto_inferior_direito, altura_retangulo_principal

    def adicionar_linhas_verticais(self, msp, estacas_data, x_min, y_min):
        """
        Adiciona linhas verticais sólidas na cor azul entre o eixo X e a linha 'Corte' para cada ponto de estaca.
        """
        # Desempacotar os dados de estacas
        estacas_ids, estacas_distances, estacas_novoz, _, _, _, _ = zip(*estacas_data)

        # Definir a camada 'Linhas_Verticais' para as linhas verticais
        if 'Linhas_Verticais' not in msp.doc.layers:
            msp.doc.layers.new(name='Linhas_Verticais', dxfattribs={'color': 5})  # Azul

        # Dicionário para verificar se a linha já foi adicionada
        linhas_ja_adicionadas = set()

        # Adicionar linhas verticais sólidas usando polilinhas
        for x, y in zip(estacas_distances, estacas_novoz):
            # Verificar se já existe uma linha neste ponto x para evitar duplicação
            if (x, y_min, y) not in linhas_ja_adicionadas:
                # Adicionar polilinha vertical com dois pontos
                msp.add_lwpolyline(
                    [(x, y_min), (x, y)],
                    dxfattribs={
                        'layer': 'Linhas_Verticais',
                        'linetype': 'BYLAYER'})  # Usando o tipo de linha padrão sólido

                # Marcar como linha já adicionada
                linhas_ja_adicionadas.add((x, y_min, y))

    def adicionar_retangulo_inferior(self, msp, ponto_inferior_esquerdo, ponto_inferior_direito, altura_retangulo_principal, estacas_data, x_min, y_min):
        """
        Adiciona um retângulo abaixo e encostado ao retângulo principal,
        utilizando os vértices inferiores do retângulo principal.
        E adiciona os IDs das estacas alinhados com as linhas tracejadas no retângulo inferior.
        """
        # Definir a altura do retângulo inferior (ajuste conforme necessário)
        altura_retangulo_inferior = altura_retangulo_principal * 0.2  # Por exemplo, 20% da altura do retângulo principal

        # Largura da faixa dos títulos
        largura_coluna_rotulos = 8.0

        ponto_inferior_esquerdo_inferior = (ponto_inferior_esquerdo[0], ponto_inferior_esquerdo[1] - altura_retangulo_inferior)
        ponto_inferior_direito_inferior = (ponto_inferior_direito[0], ponto_inferior_direito[1] - altura_retangulo_inferior)
        ponto_superior_direito_inferior = (ponto_inferior_direito[0], ponto_inferior_direito[1])
        ponto_superior_esquerdo_inferior = (ponto_inferior_esquerdo[0], ponto_inferior_esquerdo[1])

        # Desenhar o retângulo inferior como uma polilinha fechada
        msp.add_lwpolyline([
            ponto_inferior_esquerdo_inferior,
            ponto_inferior_direito_inferior,
            ponto_superior_direito_inferior,
            ponto_superior_esquerdo_inferior,
            ponto_inferior_esquerdo_inferior  # Fechar o loop
        ], dxfattribs={'layer': 'Moldura'}, close=True)

        # Definir o estilo de texto Arial se ainda não existir
        if 'Arial' not in msp.doc.styles:
            msp.doc.styles.new('Arial', dxfattribs={'font': 'arial.ttf'})  # Define o estilo Arial usando a fonte arial.ttf

        # Adicionar o título "Estacas" alinhado com as IDs e na cor verde
        texto_estacas_x = ponto_inferior_esquerdo_inferior[0] + 0.1  # Definir a posição horizontal do texto "Estacas"
        msp.add_text(self.tr("Estacas"), dxfattribs={
            'height': 0.7,  # Ajuste o tamanho do texto conforme necessário
            'layer': 'Moldura',
            'color': 3,  # Cor verde
            'insert': (texto_estacas_x, ponto_inferior_esquerdo_inferior[1] + 1),  # Alinhamento com as IDs
            'style': 'Arial'})

        # Adicionar uma linha vertical de separação entre o texto "Estacas" e os IDs
        linha_vertical_x = texto_estacas_x + largura_coluna_rotulos  # Ajuste a posição horizontal da linha vertical
        msp.add_line(
            (linha_vertical_x, ponto_inferior_esquerdo_inferior[1]),  # Ponto inicial (embaixo)
            (linha_vertical_x, ponto_inferior_esquerdo_inferior[1] + altura_retangulo_inferior),  # Ponto final (em cima)
            dxfattribs={'layer': 'Moldura', 'color': 256})  # Cor BYLAYER
        

        # Adicionar os IDs das estacas alinhados com as linhas tracejadas no retângulo inferior
        for estaca in estacas_data:
            estaca_id = estaca[0]  # Pegar o ID da estaca
            estaca_distance = estaca[1]  # Pegar a distância acumulada

            # Inserir o texto do ID alinhado com a distância acumulada da estaca
            msp.add_text(f"{estaca_id}", dxfattribs={
                'height': 0.75,  # Ajuste o tamanho do texto conforme necessário
                'layer': 'Moldura',
                'color': 3,  # Cor verde
                'insert': (estaca_distance, ponto_inferior_esquerdo_inferior[1] + 1),  # Alinhamento horizontal com as estacas
                'rotation': 0,
                'style': 'Arial'})

        # Retornar as coordenadas dos vértices inferiores e a altura do retângulo inferior
        altura_retangulo_inferior = altura_retangulo_principal * 0.2  # Mesma altura definida anteriormente
        return ponto_inferior_esquerdo_inferior, ponto_inferior_direito_inferior, altura_retangulo_inferior

    def adicionar_terceiro_retangulo(self, msp, ponto_inferior_esquerdo_inferior, ponto_inferior_direito_inferior, altura_retangulo_inferior, estacas_data):
        """
        Adiciona um terceiro retângulo abaixo e encostado ao retângulo inferior,
        utilizando os vértices inferiores do retângulo inferior.
        Adiciona os textos "Cota" e "Terreno" e exibe apenas os valores de Z das estacas.
        """
        # Definir a altura do terceiro retângulo (mesma altura do retângulo inferior)
        altura_terceiro_retangulo = altura_retangulo_inferior  # Mesmo tamanho do retângulo inferior

        # Coordenadas do terceiro retângulo (em relação ao retângulo inferior)
        ponto_inferior_esquerdo_terceiro = (ponto_inferior_esquerdo_inferior[0], ponto_inferior_esquerdo_inferior[1] - altura_terceiro_retangulo)
        ponto_inferior_direito_terceiro = (ponto_inferior_direito_inferior[0], ponto_inferior_direito_inferior[1] - altura_terceiro_retangulo)
        ponto_superior_direito_terceiro = (ponto_inferior_direito_inferior[0], ponto_inferior_direito_inferior[1])
        ponto_superior_esquerdo_terceiro = (ponto_inferior_esquerdo_inferior[0], ponto_inferior_esquerdo_inferior[1])

        # Desenhar o terceiro retângulo como uma polilinha fechada
        msp.add_lwpolyline([
            ponto_inferior_esquerdo_terceiro,
            ponto_inferior_direito_terceiro,
            ponto_superior_direito_terceiro,
            ponto_superior_esquerdo_terceiro,
            ponto_inferior_esquerdo_terceiro  # Fechar o loop
        ], dxfattribs={'layer': 'Moldura'}, close=True)

        # Definir o estilo de texto Arial se ainda não existir
        if 'Arial' not in msp.doc.styles:
            msp.doc.styles.new('Arial', dxfattribs={'font': 'arial.ttf'})  # Define o estilo Arial usando a fonte arial.ttf

        # Adicionar o texto "Terreno" alinhado à esquerda
        texto_cota_x = ponto_inferior_esquerdo_terceiro[0] + 0.1
        texto_terreno_y = ponto_inferior_esquerdo_terceiro[1] + altura_terceiro_retangulo - 1.5

        msp.add_text(self.tr("Terreno"), dxfattribs={
            'height': 0.6,
            'layer': 'Moldura',
            'color': 6,  # Roxo/Magenta
            'insert': (texto_cota_x, texto_terreno_y),
            'style': 'Arial'})

        # Adicionar uma linha vertical de separação entre o texto e os valores
        linha_vertical_x = texto_cota_x + 8
        msp.add_line(
            (linha_vertical_x, ponto_inferior_esquerdo_terceiro[1]),
            (linha_vertical_x, ponto_inferior_esquerdo_terceiro[1] + altura_terceiro_retangulo),
            dxfattribs={'layer': 'Moldura'})

        # Adicionar os valores de Z (Terreno) das estacas
        for estaca in estacas_data:
            estaca_distance = estaca[1]
            z_terreno = estaca[3]

            msp.add_text(f"{z_terreno:.2f}", dxfattribs={
                'height': 0.55,
                'layer': 'Moldura',
                'insert': (estaca_distance, texto_terreno_y),
                'rotation': 0,
                'style': 'Arial',
                'color': 6})  # Roxo/Magenta

        # Retornar as coordenadas dos vértices inferiores e a altura do terceiro retângulo
        return ponto_inferior_esquerdo_terceiro, ponto_inferior_direito_terceiro, altura_terceiro_retangulo

    def adicionar_quarto_retangulo(self, msp, ponto_inferior_esquerdo_terceiro, ponto_inferior_direito_terceiro, altura_terceiro_retangulo, estacas_data):
        """
        Adiciona um quarto retângulo abaixo e encostado ao terceiro retângulo,
        utilizando os vértices inferiores do terceiro retângulo.
        Adiciona o texto "Corte" e exibe os valores de NovoZ das estacas.
        """
        # Definir a altura do quarto retângulo (mesma altura dos retângulos anteriores)
        altura_quarto_retangulo = altura_terceiro_retangulo  # Mesmo tamanho do retângulo anterior

        # Coordenadas do quarto retângulo (em relação ao terceiro retângulo)
        ponto_inferior_esquerdo_quarto = (ponto_inferior_esquerdo_terceiro[0], ponto_inferior_esquerdo_terceiro[1] - altura_quarto_retangulo)
        ponto_inferior_direito_quarto = (ponto_inferior_direito_terceiro[0], ponto_inferior_direito_terceiro[1] - altura_quarto_retangulo)
        ponto_superior_direito_quarto = (ponto_inferior_direito_terceiro[0], ponto_inferior_direito_terceiro[1])
        ponto_superior_esquerdo_quarto = (ponto_inferior_esquerdo_terceiro[0], ponto_inferior_esquerdo_terceiro[1])

        # Desenhar o quarto retângulo como uma polilinha fechada
        msp.add_lwpolyline([
            ponto_inferior_esquerdo_quarto,
            ponto_inferior_direito_quarto,
            ponto_superior_direito_quarto,
            ponto_superior_esquerdo_quarto,
            ponto_inferior_esquerdo_quarto  # Fechar o loop
        ], dxfattribs={'layer': 'Moldura'}, close=True)

        # Definir o estilo de texto Arial se ainda não existir
        if 'Arial' not in msp.doc.styles:
            msp.doc.styles.new('Arial', dxfattribs={'font': 'arial.ttf'})  # Define o estilo Arial usando a fonte arial.ttf

        # Adicionar o texto "Corte/Aterro" alinhado à esquerda
        texto_corte_x = ponto_inferior_esquerdo_quarto[0] + 0.1
        texto_corte_y = ponto_inferior_esquerdo_quarto[1] + altura_quarto_retangulo - 1.5

        msp.add_text(self.tr("Corte/Aterro"), dxfattribs={
            'height': 0.55,
            'color': 7,  # Branco
            'layer': 'Moldura',
            'insert': (texto_corte_x, texto_corte_y),
            'style': 'Arial'})

        # Adicionar uma linha vertical de separação entre o texto e os valores
        linha_vertical_x = texto_corte_x + 8
        msp.add_line(
            (linha_vertical_x, ponto_inferior_esquerdo_quarto[1]),
            (linha_vertical_x, ponto_inferior_esquerdo_quarto[1] + altura_quarto_retangulo),
            dxfattribs={'layer': 'Moldura'})

        # Adicionar os valores de Corte/Aterro das estacas
        for estaca in estacas_data:
            estaca_distance = estaca[1]
            novo_z = estaca[2]      # Corte/Aterro
            z_terreno = estaca[3]   # Terreno

            if novo_z > z_terreno:
                cor = 5  # Azul
            elif novo_z < z_terreno:
                cor = 1  # Vermelho
            else:
                cor = 7  # Branco

            msp.add_text(f"{novo_z:.2f}", dxfattribs={
                'height': 0.55,
                'layer': 'Moldura',
                'insert': (estaca_distance, texto_corte_y),
                'rotation': 0,
                'style': 'Arial',
                'color': cor})

        return ponto_inferior_esquerdo_quarto, ponto_inferior_direito_quarto, altura_quarto_retangulo

    def adicionar_quinto_retangulo(self, msp, ponto_inferior_esquerdo_quarto, ponto_inferior_direito_quarto, altura_quarto_retangulo, estacas_data):
        """
        Adiciona um quinto retângulo abaixo e encostado ao quarto retângulo,
        e escreve os valores de Desnível das estacas.
        estacas_data: (fid, dist_acumulada, NovoZ, Z, Desnivel, x, y)
        """
        altura_quinto_retangulo = altura_quarto_retangulo

        p_ie = (ponto_inferior_esquerdo_quarto[0], ponto_inferior_esquerdo_quarto[1] - altura_quinto_retangulo)
        p_id = (ponto_inferior_direito_quarto[0], ponto_inferior_direito_quarto[1] - altura_quinto_retangulo)
        p_sd = (ponto_inferior_direito_quarto[0], ponto_inferior_direito_quarto[1])
        p_se = (ponto_inferior_esquerdo_quarto[0], ponto_inferior_esquerdo_quarto[1])

        msp.add_lwpolyline([p_ie, p_id, p_sd, p_se, p_ie], dxfattribs={'layer': 'Moldura'}, close=True)

        if 'Arial' not in msp.doc.styles:
            msp.doc.styles.new('Arial', dxfattribs={'font': 'arial.ttf'})

        texto_x = p_ie[0] + 0.1
        texto_y = p_ie[1] + altura_quinto_retangulo - 1.5

        # Título
        msp.add_text(self.tr("Diferença de nível"), dxfattribs={
            'height': 0.55,
            'layer': 'Moldura',
            'insert': (texto_x, texto_y),
            'style': 'Arial',
            'color': 7})

        # Separador vertical
        linha_vertical_x = texto_x + 8
        msp.add_line(
            (linha_vertical_x, p_ie[1]),
            (linha_vertical_x, p_ie[1] + altura_quinto_retangulo),
            dxfattribs={'layer': 'Moldura'})

        # Valores
        for estaca in estacas_data:
            dist = estaca[1]
            desn = estaca[4]

            # cor por sinal (opcional)
            if desn is None:
                cor = 7
                txt = ""
            else:
                try:
                    desn_f = float(desn)
                    cor = 5 if desn_f > 0 else (1 if desn_f < 0 else 7)  # azul/verm/normal
                    txt = f"{desn_f:.2f}"
                except Exception:
                    cor = 7
                    txt = str(desn)

            msp.add_text(txt, dxfattribs={
                'height': 0.55,
                'layer': 'Moldura',
                'insert': (dist, texto_y),
                'rotation': 0,
                'style': 'Arial',
                'color': cor})

        return p_ie, p_id, altura_quinto_retangulo

    def adicionar_sexto_retangulo(self, msp, ponto_inferior_esquerdo_quinto, ponto_inferior_direito_quinto, altura_quinto_retangulo, estacas_data):
        """
        Adiciona um sexto retângulo abaixo e encostado ao quinto retângulo,
        utilizando os vértices inferiores do quinto retângulo.
        Adiciona o texto "Desnível (%)" e exibe os valores de desnível percentual das estacas com base no Terreno Natural.
        """
        # Definir a altura do sexto retângulo (mesma altura dos retângulos anteriores)
        altura_sexto_retangulo = altura_quinto_retangulo

        # Coordenadas do sexto retângulo (em relação ao quinto retângulo)
        ponto_inferior_esquerdo_sexto = (ponto_inferior_esquerdo_quinto[0], ponto_inferior_esquerdo_quinto[1] - altura_sexto_retangulo)
        ponto_inferior_direito_sexto = (ponto_inferior_direito_quinto[0], ponto_inferior_direito_quinto[1] - altura_sexto_retangulo)
        ponto_superior_direito_sexto = (ponto_inferior_direito_quinto[0], ponto_inferior_direito_quinto[1])
        ponto_superior_esquerdo_sexto = (ponto_inferior_esquerdo_quinto[0], ponto_inferior_esquerdo_quinto[1])

        # Desenhar o sexto retângulo como uma polilinha fechada
        msp.add_lwpolyline([
            ponto_inferior_esquerdo_sexto,
            ponto_inferior_direito_sexto,
            ponto_superior_direito_sexto,
            ponto_superior_esquerdo_sexto,
            ponto_inferior_esquerdo_sexto  # Fechar o loop
        ], dxfattribs={'layer': 'Moldura'}, close=True)

        # Adicionar o texto "Diferença de nível (%)" alinhado à esquerda
        texto_desnivel_perc_x = ponto_inferior_esquerdo_sexto[0] + 0.1
        texto_desnivel_perc_y = ponto_inferior_esquerdo_sexto[1] + altura_sexto_retangulo - 1.5

        if 'Arial' not in msp.doc.styles:
            msp.doc.styles.new('Arial', dxfattribs={'font': 'arial.ttf'})

        msp.add_text(self.tr("Diferença de nível (%)"), dxfattribs={
            'height': 0.5,
            'color': 7,  # Branco
            'layer': 'Moldura',
            'insert': (texto_desnivel_perc_x, texto_desnivel_perc_y),
            'style': 'Arial'})

        # Linha vertical de separação
        linha_vertical_x = texto_desnivel_perc_x + 8
        msp.add_line(
            (linha_vertical_x, ponto_inferior_esquerdo_sexto[1]),
            (linha_vertical_x, ponto_inferior_esquerdo_sexto[1] + altura_sexto_retangulo),
            dxfattribs={'layer': 'Moldura'})

        # Primeiro ponto = 0.00
        primeiro_ponto = estacas_data[0]
        msp.add_text("0.00", dxfattribs={
            'height': 0.5,
            'color': 7,  # Branco
            'layer': 'Moldura',
            'insert': (primeiro_ponto[1], texto_desnivel_perc_y),
            'rotation': 0,
            'style': 'Arial'})

        # Demais pontos
        for i in range(1, len(estacas_data)):
            estaca_atual = estacas_data[i]
            estaca_anterior = estacas_data[i - 1]

            distancia_entre_pontos = estaca_atual[1] - estaca_anterior[1]
            if distancia_entre_pontos != 0:
                desnivel_percentual = ((estaca_atual[3] - estaca_anterior[3]) / distancia_entre_pontos) * 100
            else:
                desnivel_percentual = 0.0

            if desnivel_percentual > 0:
                cor = 5  # Azul
            elif desnivel_percentual < 0:
                cor = 1  # Vermelho
            else:
                cor = 7  # Branco

            msp.add_text(f"{desnivel_percentual:.2f}", dxfattribs={
                'height': 0.5,
                'color': cor,
                'layer': 'Moldura',
                'insert': (estaca_atual[1], texto_desnivel_perc_y),
                'rotation': 0,
                'style': 'Arial'})

        # Retornar as coordenadas dos vértices inferiores e a altura do sexto retângulo
        return ponto_inferior_esquerdo_sexto, ponto_inferior_direito_sexto, altura_sexto_retangulo

    def calcular_intersecao(self, p1, p2, p3, p4):
        """
        Calcula o ponto de interseção entre duas linhas definidas por p1->p2 e p3->p4.
        Retorna o ponto de interseção como (x, y) ou None se não houver interseção.
        """
        x1, y1 = p1
        x2, y2 = p2
        x3, y3 = p3
        x4, y4 = p4

        denom = (y4 - y3) * (x2 - x1) - (x4 - x3) * (y2 - y1)
        if denom == 0:
            return None  # Linhas são paralelas

        ua = ((x4 - x3) * (y1 - y3) - (y4 - y3) * (x1 - x3)) / denom
        ub = ((x2 - x1) * (y1 - y3) - (y2 - y1) * (x1 - x3)) / denom
        if 0 <= ua <= 1 and 0 <= ub <= 1:
            # Calcula o ponto de interseção
            x = x1 + ua * (x2 - x1)
            y = y1 + ua * (y2 - y1)
            return (x, y)
        return None

    def preencher_com_hachura(self, msp, estacas_data, pontos_apoio_data):
        """
        Preenche a área delimitada pelas estacas (perfil de corte/aterro)
        e pontos de apoio (terreno natural) com hachura no modelo msp.

        Ajustes:
        - Transparência 30%
        - Taludes nas pontas fecham certinho (sem faltar/sobrar)
        - Evita "vazar" do TN (polígono é construído por interpolação no mesmo grid)
        - Hatch não some quando a diferença é muito pequena (epsilon anti-degeneração)
        """
        # helpers
        def _ensure_sorted_xy(xs, ys):
            xs = np.asarray(xs, dtype=float)
            ys = np.asarray(ys, dtype=float)
            if xs.size == 0:
                return xs, ys
            order = np.argsort(xs)
            xs = xs[order]
            ys = ys[order]

            # remove duplicatas de X (mantém o último)
            # (np.interp não gosta de x repetido)
            unique_x = []
            unique_y = []
            for x, y in zip(xs, ys):
                if not unique_x or abs(x - unique_x[-1]) > 1e-12:
                    unique_x.append(x)
                    unique_y.append(y)
                else:
                    unique_y[-1] = y
            return np.array(unique_x, float), np.array(unique_y, float)

        def _talude_intersection_with_tn(x0, y0, x_tn, y_tn, side: str):
            """
            Encontra a interseção entre a reta de talude 1:1 que sai do ponto (x0,y0)
            e a polilinha do TN (x_tn,y_tn).

            side:
              - "left": procura interseção para x <= x0 (talude para a esquerda)
              - "right": procura interseção para x >= x0 (talude para a direita)

            A inclinação m é escolhida (+1 ou -1) para subir/descer em direção ao TN.
            """
            # TN no mesmo x0 (se estiver dentro do domínio)
            if x0 <= x_tn[0]:
                y_tn0 = y_tn[0]
            elif x0 >= x_tn[-1]:
                y_tn0 = y_tn[-1]
            else:
                y_tn0 = float(np.interp(x0, x_tn, y_tn))

            # Escolha do slope para alcançar o TN na direção escolhida
            # left: x diminui
            #   m=+1 -> ao ir p/ esquerda, y diminui
            #   m=-1 -> ao ir p/ esquerda, y aumenta
            # right: x aumenta
            #   m=+1 -> ao ir p/ direita, y aumenta
            #   m=-1 -> ao ir p/ direita, y diminui
            if side == "left":
                m = -1.0 if (y_tn0 > y0) else 1.0
            else:
                m = 1.0 if (y_tn0 > y0) else -1.0

            best = None  # (x_int, y_int)
            if len(x_tn) < 2:
                return (x0, y_tn0)

            for xa, xb, ya, yb in zip(x_tn[:-1], x_tn[1:], y_tn[:-1], y_tn[1:]):
                dx = xb - xa
                dy = yb - ya
                denom = (dy - m * dx)

                # segmento paralelo ao talude
                if abs(denom) < 1e-15:
                    continue

                # resolve: ya + t*dy = y0 + m*( (xa + t*dx) - x0 )
                t = (y0 + m * (xa - x0) - ya) / denom
                if t < -1e-12 or t > 1 + 1e-12:
                    continue

                x_int = xa + t * dx
                y_int = ya + t * dy

                if side == "left" and x_int > x0 + 1e-9:
                    continue
                if side == "right" and x_int < x0 - 1e-9:
                    continue

                # pega a interseção "mais perto" do ponto de saída, na direção correta
                if best is None:
                    best = (x_int, y_int)
                else:
                    if side == "left":
                        # mais próximo, porém ainda <= x0 => maximiza x_int
                        if x_int > best[0]:
                            best = (x_int, y_int)
                    else:
                        # mais próximo, porém ainda >= x0 => minimiza x_int
                        if x_int < best[0]:
                            best = (x_int, y_int)

            return best if best is not None else (x0, y_tn0)

        def _build_x_grid(xmin, xmax, x_breaks, max_points=1200):
            """
            Densifica automaticamente para não ficar com cordas longas (que causam sobra/falta).
            Limita o total de pontos.
            """
            x_breaks = [x for x in x_breaks if xmin - 1e-9 <= x <= xmax + 1e-9]
            x_breaks = sorted(set(float(x) for x in x_breaks))
            if not x_breaks:
                return np.array([xmin, xmax], float)

            # garante extremidades
            if x_breaks[0] > xmin + 1e-12:
                x_breaks.insert(0, xmin)
            if x_breaks[-1] < xmax - 1e-12:
                x_breaks.append(xmax)

            span = max(1e-12, xmax - xmin)
            # alvo: ~400 amostras no máximo, sem ficar pesado
            max_step = max(0.25, span / 400.0)

            xs = [x_breaks[0]]
            for a, b in zip(x_breaks[:-1], x_breaks[1:]):
                d = b - a
                if d <= 1e-12:
                    continue
                n = int(math.ceil(d / max_step))
                # evita explodir
                n = max(1, min(n, 50))
                for i in range(1, n + 1):
                    xs.append(a + d * (i / n))

            xs = np.array(xs, float)

            # limita pontos (subamostra uniforme se necessário)
            if xs.size > max_points:
                idx = np.linspace(0, xs.size - 1, max_points).round().astype(int)
                xs = xs[idx]
            return xs

        def _unique_bounds(bounds, tol=1e-6):
            bounds = sorted(bounds)
            out = []
            for x in bounds:
                if not out or abs(x - out[-1]) > tol:
                    out.append(x)
            return out

        def _poly_area(poly):
            # shoelace
            if len(poly) < 3:
                return 0.0
            s = 0.0
            for (x0, y0), (x1, y1) in zip(poly, poly[1:] + poly[:1]):
                s += x0 * y1 - x1 * y0
            return 0.5 * s

        def _clean_poly(poly, tol=1e-9):
            if not poly:
                return poly
            out = [poly[0]]
            for p in poly[1:]:
                if abs(p[0] - out[-1][0]) > tol or abs(p[1] - out[-1][1]) > tol:
                    out.append(p)
            # remove fechamento repetido
            if len(out) > 2 and (abs(out[0][0] - out[-1][0]) < tol and abs(out[0][1] - out[-1][1]) < tol):
                out.pop()
            return out

        def _set_entity_transparency(ent, t_float):
            # t_float: 0.0 opaco, 1.0 invisível
            try:
                ent.transparency = float(t_float)
                return
            except Exception:
                pass  # nosec B110
            try:
                alpha = int(round(255 * (1.0 - float(t_float))))
                alpha = max(0, min(255, alpha))
                ent.dxf.transparency = int(0x02000000 | alpha)
            except Exception:
                pass  # nosec B110

        # dados
        _, estacas_distances, estacas_novoz, _, _, _, _ = zip(*estacas_data)
        apoio_distances, apoio_elevations = zip(*pontos_apoio_data)

        x_corte, y_corte = _ensure_sorted_xy(estacas_distances, estacas_novoz)
        x_tn, y_tn = _ensure_sorted_xy(apoio_distances, apoio_elevations)

        if x_corte.size < 2 or x_tn.size < 2:
            return

        # layer
        if 'Hachura' not in msp.doc.layers:
            msp.doc.layers.new(name='Hachura', dxfattribs={'color': 7})

        # monta linha PROJETO = talude + corte + talude
        x0, y0 = float(x_corte[0]), float(y_corte[0])
        xn, yn = float(x_corte[-1]), float(y_corte[-1])

        if self.checkBoxTaludeI.isChecked():
            xL, yL = _talude_intersection_with_tn(x0, y0, x_tn, y_tn, side="left")
        else:
            xL, yL = x0, y0

        if self.checkBoxTaludeF.isChecked():
            xR, yR = _talude_intersection_with_tn(xn, yn, x_tn, y_tn, side="right")
        else:
            xR, yR = xn, yn

        # garante ordem (evita talude “invertido”)
        if xL > x0:
            xL, yL = x0, float(np.interp(x0, x_tn, y_tn))
        if xR < xn:
            xR, yR = xn, float(np.interp(xn, x_tn, y_tn))

        x_proj = np.concatenate(([xL], x_corte, [xR]))
        y_proj = np.concatenate(([yL], y_corte, [yR]))
        x_proj, y_proj = _ensure_sorted_xy(x_proj, y_proj)

        # domínio comum
        xmin = max(float(x_proj[0]), float(x_tn[0]))
        xmax = min(float(x_proj[-1]), float(x_tn[-1]))
        if xmax <= xmin + 1e-12:
            return

        # grid de X (união de vértices + densificação)
        x_breaks = list(x_proj) + list(x_tn)
        x_grid = _build_x_grid(xmin, xmax, x_breaks, max_points=1400)

        y_proj_g = np.interp(x_grid, x_proj, y_proj)
        y_tn_g = np.interp(x_grid, x_tn, y_tn)
        diff = y_proj_g - y_tn_g

        # acha interseções (mudança de sinal)
        bounds = [xmin, xmax]
        for i in range(len(x_grid) - 1):
            d0 = diff[i]
            d1 = diff[i + 1]
            xA = x_grid[i]
            xB = x_grid[i + 1]

            # toca exatamente
            if abs(d0) < 1e-12:
                bounds.append(xA)

            # cruza
            if d0 * d1 < 0.0:
                # raiz linear
                xr = xA + (xB - xA) * (d0 / (d0 - d1))
                bounds.append(float(xr))

        bounds = _unique_bounds(bounds, tol=1e-5)

        # hachura por intervalo
        # epsilon anti-área-zero (mínimo possível)
        y_span = float(max(y_proj_g.max(), y_tn_g.max()) - min(y_proj_g.min(), y_tn_g.min()))
        eps_y = max(1e-7, y_span * 1e-7)

        for a, b in zip(bounds[:-1], bounds[1:]):
            if b <= a + 1e-10:
                continue

            x_mid = 0.5 * (a + b)
            y_proj_mid = float(np.interp(x_mid, x_proj, y_proj))
            y_tn_mid = float(np.interp(x_mid, x_tn, y_tn))
            dmid = y_proj_mid - y_tn_mid

            # se praticamente igual, não tem o que preencher (mas ainda tentamos se houver área)
            # define cor
            hatch_color = 5 if dmid > 0 else 1  # azul / vermelho

            # pontos do intervalo no grid (inclui a e b)
            mask = (x_grid >= a - 1e-9) & (x_grid <= b + 1e-9)
            xs = x_grid[mask]
            if xs.size == 0 or xs[0] > a + 1e-9:
                xs = np.insert(xs, 0, a)
            if xs[-1] < b - 1e-9:
                xs = np.append(xs, b)

            # garante ordenado e sem duplicatas
            xs = np.unique(np.round(xs, 9))

            yP = np.interp(xs, x_proj, y_proj)
            yT = np.interp(xs, x_tn, y_tn)

            poly = list(zip(xs, yP)) + list(zip(xs[::-1], yT[::-1]))
            poly = _clean_poly(poly, tol=1e-10)

            # área para hatch não falhar
            area = _poly_area(poly)
            if abs(area) < (eps_y * (b - a) * 0.5):
                # “infla” só o suficiente para o DXF aceitar (imperceptível)
                sign = 1.0 if dmid >= 0 else -1.0
                yP2 = yP + sign * eps_y
                poly = list(zip(xs, yP2)) + list(zip(xs[::-1], yT[::-1]))
                poly = _clean_poly(poly, tol=1e-10)
                area = _poly_area(poly)
                if abs(area) < 1e-18:
                    continue

            # cria hatch SOLID para não “sumir” em faixas finas
            hatch = msp.add_hatch(dxfattribs={'layer': 'Hachura'})
            try:
                hatch.set_solid_fill(color=hatch_color)
            except Exception:
                # fallback antigo: cor no add_hatch
                hatch.dxf.color = hatch_color

            hatch.paths.add_polyline_path(poly, is_closed=True)

            # 30% transparente
            _set_entity_transparency(hatch, 0.30)

    def adicionar_legendas_dxf(self, msp, x_min, x_max, y_max, escala, y_margin):
        """
        Adiciona legendas ao DXF, incluindo linhas e textos para "Perfil de Corte/Aterro," "Terreno,"
        "Talude," e retângulos para as áreas de "Corte" e "Aterro."
        """
        # Definir a altura inicial das legendas, acima do gráfico
        y_text_line = y_max + y_margin * 0.5

        # Posição horizontal inicial para a primeira legenda
        x_start_text = x_min + y_margin * 0.5

        # **Perfil de Corte/Aterro**
        msp.add_line((x_start_text, y_text_line), (x_start_text + 3 * escala, y_text_line), dxfattribs={'layer': 'Corte', 'color': 5})
        msp.add_text(self.tr("Perfil de Corte/Aterro"), dxfattribs={
            'height': 0.35 * escala,
            'layer': 'Corte',
            'insert': (x_start_text + 3.5 * escala, y_text_line),
            'style': 'Arial'})

        # **Terreno**
        x_start_text += 10 * escala
        msp.add_line((x_start_text, y_text_line), (x_start_text + 3 * escala, y_text_line), dxfattribs={'layer': 'Terreno_Natural', 'color': 6})
        msp.add_text(self.tr("Terreno"), dxfattribs={
            'height': 0.35 * escala,
            'layer': 'Terreno_Natural',
            'insert': (x_start_text + 3.5 * escala, y_text_line),
            'style': 'Arial'})

        # **Talude**
        x_start_text += 7 * escala
        msp.add_line((x_start_text, y_text_line), (x_start_text + 3 * escala, y_text_line), dxfattribs={'layer': 'Talude', 'color': 3})
        msp.add_text(self.tr("Talude"), dxfattribs={
            'height': 0.35 * escala,
            'layer': 'Talude',
            'insert': (x_start_text + 3.5 * escala, y_text_line),
            'style': 'Arial'})

        # **Área de Corte (vermelho preenchido)**
        x_start_text += 7 * escala
        corte_rect_x = x_start_text
        corte_rect_y = y_text_line - 0.1 * escala

        corte_pts = [
            (corte_rect_x, corte_rect_y),
            (corte_rect_x + 1 * escala, corte_rect_y),
            (corte_rect_x + 1 * escala, corte_rect_y + 0.5 * escala),
            (corte_rect_x, corte_rect_y + 0.5 * escala)]

        hatch_corte = msp.add_hatch(color=1, dxfattribs={'layer': 'Hachura'})
        hatch_corte.set_solid_fill(color=1)
        hatch_corte.paths.add_polyline_path(corte_pts, is_closed=True)

        msp.add_text(self.tr("Área de Corte"), dxfattribs={
            'height': 0.35 * escala,
            'layer': 'Hachura',
            'insert': (corte_rect_x + 2.0 * escala, corte_rect_y),
            'style': 'Arial'})

        # **Área de Aterro (azul preenchido)**
        x_start_text += 7 * escala
        aterro_rect_x = x_start_text
        aterro_rect_y = y_text_line - 0.1 * escala

        aterro_pts = [
            (aterro_rect_x, aterro_rect_y),
            (aterro_rect_x + 1 * escala, aterro_rect_y),
            (aterro_rect_x + 1 * escala, aterro_rect_y + 0.5 * escala),
            (aterro_rect_x, aterro_rect_y + 0.5 * escala)]

        hatch_aterro = msp.add_hatch(color=5, dxfattribs={'layer': 'Hachura'})
        hatch_aterro.set_solid_fill(color=5)
        hatch_aterro.paths.add_polyline_path(aterro_pts, is_closed=True)

        msp.add_text(self.tr("Área de Aterro"), dxfattribs={
            'height': 0.35 * escala,
            'layer': 'Hachura',
            'insert': (aterro_rect_x + 2.0 * escala, aterro_rect_y),
            'style': 'Arial'})

    def exportar_eixos(self, msp, estacas_data, pontos_apoio_data):
        """
        Exporta os eixos principais utilizando os dados de estacas e pontos de apoio para o modelo msp.
        """
        # Desempacotando os dados
        estacas_ids, estacas_distances, estacas_novoz, _, _, _, _ = zip(*estacas_data)
        apoio_distances, apoio_elevations = zip(*pontos_apoio_data)

        # Manter os limites originais do eixo X com base em apoio_distances
        x_min = min(apoio_distances)
        x_max = max(apoio_distances)
        y_min = min(min(estacas_novoz), min(apoio_elevations))
        y_max = max(max(estacas_novoz), max(apoio_elevations))

        # Definir um intervalo mínimo para o eixo Y
        intervalo_minimo_y = 10  # Valor mínimo para o intervalo vertical
        intervalo_y = y_max - y_min

        if intervalo_y < intervalo_minimo_y:
            centro_y = (y_max + y_min) / 2
            y_min = centro_y - intervalo_minimo_y / 2
            y_max = centro_y + intervalo_minimo_y / 2

        # Adicionar margens
        x_margin = (x_max - x_min) * 0.05  # 5% de margem
        y_margin = (y_max - y_min) * 0.05  # 5% de margem

        # Definir uma margem mínima para garantir que labels e ticks caibam dentro do retângulo
        margem_minima = 1  # Ajuste este valor conforme necessário
        x_margin = max(x_margin, margem_minima)
        y_margin = max(y_margin, margem_minima)

        # Ajustar x_min, x_max, y_min e y_max com as margens
        x_min -= x_margin
        x_max += x_margin
        y_min -= y_margin
        y_max += y_margin

        # Usar apenas os valores de dist_acumulada das estacas (estacas_distances) para os ticks no eixo X
        all_ticks = np.unique(estacas_distances)

        # Filtrar ticks que estão dentro dos limites x_min e x_max
        all_ticks = all_ticks[(all_ticks >= x_min) & (all_ticks <= x_max)]

        # Definir o estilo de texto Arial se ainda não existir
        if 'Arial' not in msp.doc.styles:
            msp.doc.styles.new('Arial', dxfattribs={'font': 'arial.ttf'})  # Define o estilo Arial usando a fonte arial.ttf

        # Desenhar os ticks e labels no eixo X
        for x in all_ticks:
            # Linha vertical pequena para o tick
            msp.add_line((x, y_min - y_margin * 0.3), (x, y_min + y_margin * 0.3), dxfattribs={'layer': 'Eixos'})
            # Label do tick
            msp.add_text(f"{x:.2f} m", dxfattribs={
                'height': 0.5,
                'layer': 'Eixos',
                'insert': (x, y_min - y_margin * 1.5),
                'rotation': 0,
                'style': 'Arial'})

        # Adicionar ticks no eixo Y com valores próximos à linha horizontal do tick
        num_ticks_y = 9  # Agora serão 9 ticks no total
        y_ticks = np.linspace(y_min + y_margin, y_max - y_margin, num_ticks_y)

        # Margem fixa para posicionar os rótulos ao lado da linha horizontal
        margem_fixa_x = x_min - 2.5  # Valor fixo ao lado do eixo Y

        for y in y_ticks:
            # Linha horizontal pequena para o tick, agora na cor vermelha (color=1)
            msp.add_line(
                (x_min - x_margin * 0.1, y),
                (x_min + x_margin * 0.1, y),
                dxfattribs={'layer': 'Eixos', 'color': 1})

            # Label do tick fixado na mesma posição horizontal ao lado da linha do tick
            msp.add_text(f"{y:.2f}", dxfattribs={
                'height': 0.45,
                'layer': 'Eixos',
                'insert': (margem_fixa_x, y),  # Posição fixa ao lado dos ticks
                'rotation': 0,
                'style': 'Arial'})

            # Linha horizontal paralela completa, cor cinza (50% transparente)
            linha_grid = msp.add_line(
                (x_min, y),  # início no eixo Y
                (x_max, y),  # fim no lado oposto do retângulo
                dxfattribs={'layer': 'Eixos', 'color': 254})  # cinza

            # Transparência no ezdxf: 0.0 = opaco, 1.0 = totalmente transparente
            try:
                linha_grid.transparency = 0.5
            except Exception:
                # Fallback (valor bruto DXF R2004+): 0x02 + alpha (0..255), onde 255 = opaco
                linha_grid.dxf.transparency = int(0x02000000 | 128)

        # Adicionar o contorno do retângulo ao redor dos eixos X e Y
        msp.add_lwpolyline([
            (x_min, y_min),  # Inferior esquerdo
            (x_max, y_min),  # Inferior direito
            (x_max, y_max),  # Superior direito
            (x_min, y_max),  # Superior esquerdo
            (x_min, y_min)   # Fechar o loop
        ], dxfattribs={'layer': 'Eixos'}, close=True)

        # Calcular a escala para as legendas
        escala = (x_max - x_min) / 100

        # Adicionar legendas usando a função auxiliar
        self.adicionar_legendas_dxf(msp, x_min, x_max, y_max, escala, y_margin)

        # No final da função, retornar x_min e y_min
        return x_min, y_min

    def exportar_tabela_dxf(self, msp, ponto_inferior_esquerdo_sexto, ponto_inferior_direito_sexto, altura_sexto_retangulo):
        """
        Exporta a tabela de atributos da camada selecionada no comboBoxGrupoZ para o DXF,
        posicionando-a logo abaixo do sexto retângulo.

        Ajuste solicitado:
        - Trocar cabeçalho "ID" por "Estacas"
        - Trocar cabeçalho "NovoZ" por "Corte"
        """
        nome_camada = self.comboBoxGrupoZ.currentText()
        camada = QgsProject.instance().mapLayersByName(nome_camada)

        if camada:
            camada = camada[0]

            # Criar camada DXF da tabela (evita erro se já existir)
            if 'Tabela_Atributos' not in msp.doc.layers:
                msp.doc.layers.new(name='Tabela_Atributos', dxfattribs={'color': 7})  # Amarelo

            pos_x = ponto_inferior_esquerdo_sexto[0] + 0.1
            pos_y = ponto_inferior_esquerdo_sexto[1] - altura_sexto_retangulo - 1

            cell_height = 1

            # Nomes reais dos campos
            field_names = [field.name() for field in camada.fields()]

            # Larguras individuais das colunas
            column_widths = []
            for field_name in field_names:
                if field_name == "NovoZ":
                    column_widths.append(9.0)
                elif field_name == "dist_acumulada":
                    column_widths.append(12.0)
                elif field_name == "Desnivel":
                    column_widths.append(12.0)
                else:
                    column_widths.append(7.0)

            def coluna_x(col_index):
                return pos_x + sum(column_widths[:col_index])

            # Nomes exibidos no cabeçalho DXF, mantendo os campos reais intactos
            def _header_display_name(name: str) -> str:
                cabecalhos = {
                    "ID": self.tr("Estacas"),
                    "X": self.tr("X"),
                    "Y": self.tr("Y"),
                    "Z": self.tr("Z"),
                    "NovoZ": self.tr("Corte"),
                    "dist_acumulada": self.tr("Distância acumulada"),
                    "Desnivel": self.tr("Desnível"),
                    "Acumula_dist": self.tr("Distância acumulada"),
                    "Znovo": self.tr("Corte")}

                return cabecalhos.get(name, name)

            headers = [_header_display_name(n) for n in field_names]

            # Cabeçalhos
            for col_index, header in enumerate(headers):
                col_x = coluna_x(col_index)
                col_width = column_widths[col_index]

                header_x = col_x + 0.3
                header_y = pos_y - cell_height / 2 - 0.3

                msp.add_text(header, dxfattribs={
                    'layer': 'Tabela_Atributos',
                    'height': 0.5,
                    'insert': (header_x, header_y)})

                msp.add_lwpolyline([
                    (col_x, pos_y),
                    (col_x + col_width, pos_y),
                    (col_x + col_width, pos_y - cell_height),
                    (col_x, pos_y - cell_height),
                    (col_x, pos_y)
                ], dxfattribs={'layer': 'Tabela_Atributos', 'color': 7})

            pos_y -= cell_height

            # Valores
            for feature in camada.getFeatures():
                for col_index, field_name in enumerate(field_names):
                    valor = str(feature[field_name])

                    col_x = coluna_x(col_index)
                    col_width = column_widths[col_index]

                    valor_x = col_x + 0.3
                    valor_y = pos_y - cell_height / 2 - 0.3

                    msp.add_text(valor, dxfattribs={
                        'layer': 'Tabela_Atributos',
                        'height': 0.5,
                        'insert': (valor_x, valor_y)})

                    msp.add_lwpolyline([
                        (col_x, pos_y),
                        (col_x + col_width, pos_y),
                        (col_x + col_width, pos_y - cell_height),
                        (col_x, pos_y - cell_height),
                        (col_x, pos_y)
                    ], dxfattribs={'layer': 'Tabela_Atributos', 'color': 7})

                pos_y -= cell_height

            # Remover a linha extra na parte inferior da tabela
            pos_y += cell_height

    def _exportar_layer_comboz_para_dxf(self, doc, msp):
        """
        Exporta a camada selecionada no comboBoxGrupoZ (pontos) usando:
          - BLOCK 'CirculoX_*' (tamanho 1) com cor por regra do Desnível
          - MTEXT (altura 1) com o próprio valor do Desnível como rótulo, na mesma cor
        Entidades ficam nas coordenadas originais (sem translação).
        """
        layer_id = self.comboBoxGrupoZ.currentData()
        layer = QgsProject.instance().mapLayer(layer_id)
        if not isinstance(layer, QgsVectorLayer):
            self.mostrar_mensagem(self.tr("Camada do comboBoxGrupoZ inválida para exportação."), "Erro")
            return

        # Garante uma camada DXF com o mesmo nome (opcional)
        dxf_layer_name = layer.name() or self.tr("GrupoZ")
        try:
            if dxf_layer_name not in doc.layers:
                doc.layers.new(name=dxf_layer_name)
        except Exception:
            dxf_layer_name = self.tr("GrupoZ")

        for f in layer.getFeatures():
            g = f.geometry()
            if not g or g.isEmpty():
                continue
            if g.type() != Qgis.GeometryType.Point:
                # Se sua camada puder ter linhas/polígonos, adaptar aqui (vértices/centróide).
                continue

            pt = g.asPoint()

            # Valor do Desnível e cor correspondente
            desn = self._get_attr_float_desnivel(f, layer)
            rgb = self._color_from_desnivel(desn)
            block_name = self._ensure_block_circulox_rgb(doc, rgb)

            # INSERT do bloco (tamanho 1) na cor do bloco (true_color nas subentidades)
            ins = msp.add_blockref(block_name, (pt.x(), pt.y()), dxfattribs={'layer': dxf_layer_name})
            ins.dxf.xscale = 1.0
            ins.dxf.yscale = 1.0
            ins.dxf.rotation = 0.0

            # MTEXT com o rótulo = valor do Desnível (duas casas), mesma cor, altura 1
            label = f"{desn:.2f}"
            mtx = msp.add_mtext(label, dxfattribs={
                'insert': (pt.x() + 1.2, pt.y()),  # deslocado à direita para não colidir
                'char_height': 1.0,
                'layer': dxf_layer_name})
            mtx.dxf.true_color = ez_colors.rgb2int(rgb)

    def _get_attr_float_desnivel(self, feat, layer):
        """
        Lê 'Desnivel' (sem acento) ou 'Desnível' (com acento), case-insensitive.
        Retorna float; se não existir ou não for numérico, retorna 0.0.
        """
        candidates = ['Desnivel', 'Desnível', 'desnivel', 'desnível']
        for name in candidates:
            idx = layer.fields().indexFromName(name)
            if idx != -1:
                val = feat.attribute(name)
                try:
                    return float(val)
                except Exception:
                    break
        return 0.0

    def _color_from_desnivel(self, desnivel_val, eps=0.05):
        """
        Mapeia cor por regra:
          >0 → azul (0,0,255)
          <0 → vermelho (255,0,0)
          =0 → branco (255,255,255)
        """
        if abs(desnivel_val) < eps:
            return (255, 255, 255)  # branco
        return (0, 0, 255) if desnivel_val > 0 else (255, 0, 0)

    def _ensure_block_circulox_rgb(self, doc, rgb_tuple):
        """
        Cria (se necessário) um BLOCK 'CirculoX_R_G_B' com círculo raio 0.5 e um 'X'.
        Subentidades com true_color (cor exata).
        """
        r, g, b = rgb_tuple
        bname = f"CirculoX_{r}_{g}_{b}"
        if bname in doc.blocks:
            return bname

        blk = doc.blocks.new(name=bname, base_point=(0.0, 0.0))
        # círculo raio 0.5
        c = blk.add_circle(center=(0.0, 0.0), radius=0.5)
        c.dxf.true_color = ez_colors.rgb2int(rgb_tuple)
        # linhas do X (±0.35)
        l1 = blk.add_line((-0.35, -0.35), (0.35, 0.35))
        l1.dxf.true_color = ez_colors.rgb2int(rgb_tuple)
        l2 = blk.add_line((-0.35, 0.35), (0.35, -0.35))
        l2.dxf.true_color = ez_colors.rgb2int(rgb_tuple)
        return bname

    def exportar_dxf(self):
        """
        Exporta o gráfico (e tabela) para DXF.
        Se checkBoxCorteAterro estiver marcado, exporta também a camada do comboBoxGrupoZ
        (pontos com bloco 'CirculoX_*' e rótulos em MTEXT, tamanho 1 e cor = QGIS).
        O gráfico é ancorado a 20 m à direita do ponto mais à direita da camada do comboBoxGrupoZ,
        mantendo o Y igual ao desse ponto. Os pontos ficam nas coordenadas originais (sem translação).
        """
        nome_camada = self.comboBoxGrupoZ.currentText()
        filename = self.escolher_local_para_salvar(nome_camada, self.tr("DXF Files (*.dxf)"))
        if not filename:
            return

        try:
            # 1) Dados de exportação do gráfico
            estacas_data, pontos_apoio_data = self.obter_dados_para_exportacao()
            if estacas_data is None or pontos_apoio_data is None:
                return

            tempo_inicio = time.time()

            # 2) Documento DXF e modelspace
            doc = ezdxf.new(dxfversion='R2013')
            msp = doc.modelspace()

            # 3) Descobrir o ponto mais à direita da camada do comboBoxGrupoZ (geometrias reais)
            layer_id = self.comboBoxGrupoZ.currentData()
            layer_z = QgsProject.instance().mapLayer(layer_id)
            if not isinstance(layer_z, QgsVectorLayer):
                self.mostrar_mensagem(self.tr("Camada do comboBoxGrupoZ inválida para ancoragem."), "Erro")
                return

            max_x = float("-inf")
            right_pt = None
            for f in layer_z.getFeatures():
                g = f.geometry()
                if g and not g.isEmpty():
                    if g.type() == Qgis.GeometryType.Point:
                        p = g.asPoint()
                        if p.x() > max_x:
                            max_x = p.x()
                            right_pt = p
                    elif g.type() == Qgis.GeometryType.Line:
                        seq = g.asPolyline() if not g.isMultipart() else sum(g.asMultiPolyline(), [])
                        for v in seq:
                            if v.x() > max_x:
                                max_x = v.x(); right_pt = v
                    elif g.type() == Qgis.GeometryType.Polygon:
                        ring = None
                        if g.isMultipart():
                            mpoly = g.asMultiPolygon()
                            if mpoly and mpoly[0] and mpoly[0][0]:
                                ring = mpoly[0][0]
                        else:
                            poly = g.asPolygon()
                            if poly and poly[0]:
                                ring = poly[0]
                        if ring:
                            for v in ring:
                                if v.x() > max_x:
                                    max_x = v.x(); right_pt = v

            if right_pt is None:
                self.mostrar_mensagem(self.tr("Não foi possível determinar o ponto mais à direita."), "Erro")
                return

            target_x = right_pt.x() + 20.0   # 20 m à direita
            target_y = right_pt.y()          # mesmo Y do ponto mais à direita

            # 4) Criar camadas DXF do gráfico
            doc.layers.new(name='Corte', dxfattribs={'color': 5})
            doc.layers.new(name='Terreno_Natural', dxfattribs={'color': 6})
            doc.layers.new(name='Talude', dxfattribs={'color': 3})
            doc.layers.new(name='Eixos', dxfattribs={'color': 7})
            doc.layers.new(name='Moldura', dxfattribs={'color': 256})

            # Snapshot antes de desenhar o GRÁFICO
            handles_before_graph = {e.dxf.handle for e in msp}

            # 5) Desenhar o gráfico
            x_min, y_min = self.exportar_eixos(msp, estacas_data, pontos_apoio_data)
            self.preencher_com_hachura(msp, estacas_data, pontos_apoio_data)
            self.exportar_linhas_principais(msp, estacas_data, pontos_apoio_data)
            self.exportar_linhas_talude(msp, estacas_data, pontos_apoio_data)
            self.adicionar_linhas_verticais(msp, estacas_data, x_min, y_min)

            # Moldura principal → âncora atual (canto inferior esquerdo)
            ponto_inferior_esquerdo, ponto_inferior_direito, altura_retangulo_principal = \
                self.adicionar_retangulo_ao_redor(msp, estacas_data, pontos_apoio_data)

            # Retângulos subsequentes (empilhados abaixo)
            p_ie_inf, p_id_inf, h_inf = self.adicionar_retangulo_inferior(
                msp, ponto_inferior_esquerdo, ponto_inferior_direito, altura_retangulo_principal,
                estacas_data, x_min, y_min)

            p_ie_3, p_id_3, h_3 = self.adicionar_terceiro_retangulo(msp, p_ie_inf, p_id_inf, h_inf, estacas_data)
            p_ie_4, p_id_4, h_4 = self.adicionar_quarto_retangulo(msp, p_ie_3, p_id_3, h_3, estacas_data)
            p_ie_5, p_id_5, h_5 = self.adicionar_quinto_retangulo(msp, p_ie_4, p_id_4, h_4, estacas_data)
            p_ie_6, p_id_6, h_6 = self.adicionar_sexto_retangulo(msp, p_ie_5, p_id_5, h_5, estacas_data)

            # Tabela (opcional)
            if self.checkBoxTabela.isChecked():
                self.exportar_tabela_dxf(msp, p_ie_6, p_id_6, h_6)

            # 6) Transladar SÓ o GRÁFICO (e tabela), ancorando no target
            current_anchor = ponto_inferior_esquerdo
            dx = target_x - current_anchor[0]
            dy = target_y - current_anchor[1]

            created_graph = [e for e in msp if getattr(e.dxf, "handle", None) not in handles_before_graph]
            transformacao = Matrix44.translate(dx, dy, 0.0)
            for entity in created_graph:
                try:
                    entity.transform(transformacao)
                except Exception:
                    insert_point = getattr(entity.dxf, "insert", None)
                    if insert_point is not None:
                        entity.dxf.insert = (insert_point[0] + dx, insert_point[1] + dy)

            # 7) Exportar a camada do comboBoxGrupoZ (pontos + MTEXT) nas coordenadas ORIGINAIS
            if self.checkBoxCorteAterro.isChecked():
                self._exportar_layer_comboz_para_dxf(doc, msp)

            # 8) Salvar e reportar
            doc.saveas(filename)
            tempo_execucao = time.time() - tempo_inicio
            caminho_pasta = os.path.dirname(filename)
            self.mostrar_mensagem(self.tr("Arquivo DXF salvo com sucesso em: {tempo_execucao:.2f} segundos").format(tempo_execucao=tempo_execucao), "Sucesso", caminho_pasta=caminho_pasta, caminho_arquivo=filename)

        except Exception as e:
            self.mostrar_mensagem(self.tr("Erro ao exportar DXF: {error}").format(error=str(e)), "Erro")
#====================================================

#====================================================
    def close_dialog(self):
        """Fecha o diálogo quando o botão Fechar é clicado."""
        self.close()

    def _ensure_tbl_reload_timer(self):
        if not hasattr(self, "_tbl_reload_timer"):
            self._tbl_reload_timer = QtCore.QTimer(self)
            self._tbl_reload_timer.setSingleShot(True)
            self._tbl_reload_timer.timeout.connect(self.load_layer_attributes)

    def _schedule_table_reload(self, ms=200):
        self._ensure_tbl_reload_timer()
        self._tbl_reload_timer.start(ms)

    def _update_table_cell_by_fid(self, fid: int, field_idx: int, value):
        row = getattr(self, "_fid_to_row", {}).get(int(fid))
        if row is None:
            return
        if field_idx < 0 or field_idx >= self.tableWidgetLista.columnCount():
            return

        txt = "" if value is None else str(value)

        with QtCore.QSignalBlocker(self.tableWidgetLista):
            item = self.tableWidgetLista.item(row, field_idx)
            if item is None:
                item = QtWidgets.QTableWidgetItem(txt)
                item.setFlags(Qt.ItemFlag.ItemIsSelectable | Qt.ItemFlag.ItemIsEnabled)
                if field_idx == 0:
                    item.setData(Qt.ItemDataRole.UserRole, int(fid))
                self.tableWidgetLista.setItem(row, field_idx, item)
            else:
                if item.text() != txt:
                    item.setText(txt)

    def _on_feature_changed_tableWidgetLista(self, *args, **kwargs):
        # Evita cascata quando a tabela está sendo montada
        if getattr(self, "_loading_tableWidgetLista", False):
            return

        # QGIS: attributeValueChanged(fid, idx, value)
        if len(args) >= 3 and isinstance(args[0], (int,)) and isinstance(args[1], (int,)):
            fid, idx, value = int(args[0]), int(args[1]), args[2]
            self._update_table_cell_by_fid(fid, idx, value)
            return

        # QGIS: geometryChanged(fid, geom) -> ignore (se tabela não depende de geometria)
        if len(args) == 2 and isinstance(args[0], (int,)):
            return

        # featureAdded(fid) / featureDeleted(fid) / outros -> debounce reload
        self._schedule_table_reload(200)

    def _ui_pump(self, *, every_steps=50, step=0):
        if step % every_steps == 0:
            QtWidgets.QApplication.processEvents()

    def _init_h_spins_tab_jump(self):
        """Chame isso no seu __init__ depois do setupUi(self)."""
        self._block_tab_jump = False

        if hasattr(self, "doubleSpinBoxHinicial"):
            self.doubleSpinBoxHinicial.valueChanged.connect(self._on_h_range_changed_open_tab2)

        if hasattr(self, "doubleSpinBoxHFinal"):
            self.doubleSpinBoxHFinal.valueChanged.connect(self._on_h_range_changed_open_tab2)

    def _on_h_range_changed_open_tab2(self, *_):
        """Ao alterar H inicial/final, abre a tab_2."""
        if getattr(self, "_block_tab_jump", False):
            return
        self._open_tab_2()

    def _open_tab_2(self):
        """Abre a aba cujo widget tem objectName == 'tab_2'."""
        tab2 = getattr(self, "tab_2", None)
        if tab2 is None:
            tab2 = self.findChild(type(self.centralWidget()) if hasattr(self, "centralWidget") else object, "tab_2")
            # fallback simples (se findChild acima não ajudar):
            tab2 = self.findChild(object, "tab_2")

        if tab2 is None:
            return  # não achou a aba

        # Caso você tenha um tabWidget conhecido:
        if hasattr(self, "tabWidget"):
            idx = self.tabWidget.indexOf(tab2)
            if idx >= 0:
                self.tabWidget.setCurrentIndex(idx)
                return

        # Caso existam múltiplos QTabWidget, acha o que contém a tab_2
        for tw in self.findChildren(type(getattr(self, "tabWidget", None))):
            idx = tw.indexOf(tab2)
            if idx >= 0:
                tw.setCurrentIndex(idx)
                return

    def _set_h_values_without_jumping_tab(self, h_ini: float, h_fim: float):
        """Use isso quando seu próprio código precisar setar os valores sem abrir a tab_2."""
        self._block_tab_jump = True
        try:
            with QSignalBlocker(self.doubleSpinBoxHinicial), QSignalBlocker(self.doubleSpinBoxHFinal):
                self.doubleSpinBoxHinicial.setValue(h_ini)
                self.doubleSpinBoxHFinal.setValue(h_fim)
        finally:
            self._block_tab_jump = False