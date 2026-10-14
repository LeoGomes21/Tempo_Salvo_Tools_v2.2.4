from qgis.PyQt.QtWidgets import QTreeWidget, QInputDialog, QTreeView, QFileDialog, QColorDialog, QMessageBox, QMenu, QStyledItemDelegate, QDialog, QVBoxLayout, QListWidget, QPushButton, QHBoxLayout, QLabel, QCheckBox, QLineEdit, QRadioButton, QSpinBox, QDialogButtonBox, QGridLayout,QComboBox, QDoubleSpinBox, QButtonGroup, QFrame, QGraphicsView, QGraphicsScene, QAction, QProgressBar, QGraphicsRectItem, QToolTip, QAbstractItemView
from qgis.core import QgsMapLayer, QgsField, QgsProject, QgsWkbTypes, QgsVectorFileWriter, QgsVectorLayer,  QgsSingleSymbolRenderer, QgsCategorizedSymbolRenderer, Qgis, QgsVectorLayerSimpleLabeling, QgsEditorWidgetSetup, QgsPalLayerSettings, QgsLayerTreeLayer, QgsProperty, QgsFeature, QgsExpression, QgsExpressionContext, QgsExpressionContextUtils, QgsPointXY, QgsCoordinateTransform, QgsCoordinateReferenceSystem, QgsDefaultValue, QgsFields, QgsRuleBasedRenderer, QgsLineSymbol, QgsGeometry, QgsMarkerSymbol, QgsRenderContext, QgsSymbolLayer, QgsLayerTreeGroup, QgsEditFormConfig, QgsDistanceArea, QgsProviderRegistry, QgsUnitTypes
from qgis.PyQt.QtGui import QStandardItemModel, QStandardItem, QIcon, QPixmap, QColor, QPen, QFont, QGuiApplication, QPalette, QCursor, QFontMetrics, QDesktopServices, QPainter
from qgis.PyQt.QtCore import Qt, QSettings, QRectF, QObject, QEvent, QCoreApplication, QTimer, QMetaType, QUrl
from qgis.gui import QgsProjectionSelectionDialog
from PIL import Image, UnidentifiedImageError
from ezdxf.lldxf.const import DXFValueError
from lxml import etree as XmlET
try:
    from defusedxml import ElementTree as DefusedET
    from defusedxml.common import DefusedXmlException
    DEFUSEDXML_OK = True
except ImportError:
    DefusedET = None
    DefusedXmlException = Exception
    DEFUSEDXML_OK = False
from itertools import zip_longest
from ezdxf.colors import aci2rgb
from collections import Counter
from qgis.PyQt import sip
from io import BytesIO
import processing
import requests
import zipfile
import random
import ezdxf
import math
import time
import csv
import os
import re
import gc

# Importe as Classes Externas
from .gerenciar_etiquetas_dialog import GerenciarEtiquetasDialog
from .salvar_multiplos import DialogoSalvarFormatos
from .criar_linhas import CamadaLinhasManager

class UiManager:
    """
    Gerencia a interface do usuário, interagindo com um QTreeView para listar e gerenciar camadas de linhas no QGIS.
    """
    def __init__(self, iface, dialog, plugin):
        """
        Construtor da classe.

        :param iface: Interface do QGIS, usada para interagir com o ambiente do QGIS.
        :param dialog: Diálogo ou janela que esta classe controlará.
        """
        self._layer_signals_connected: set[str] = set()
        self.iface = iface # Atribui a interface do QGIS à variável de instância
        self.dlg = dialog  # Referência ao diálogo principal
        
        self.plugin = plugin

        # Conectar o sinal selectionChanged após o modelo estar configurado
        self.dlg.treeViewListaLinha.clicked.connect(self.on_treeViewItem_clicked)

        # Conectar o sinal do tooltip
        self.dlg.treeViewListaLinha.setMouseTracking(True)

        self.dlg.pushButtonReprojetarLinha.clicked.connect(self.abrir_dialogo_crs)

        # Configura o treeView para aceitar um menu de contexto personalizado
        self.dlg.treeViewListaLinha.setContextMenuPolicy(Qt.ContextMenuPolicy.CustomContextMenu)

        # Conecta o evento de solicitação de menu de contexto ao método open_context_menu
        self.dlg.treeViewListaLinha.customContextMenuRequested.connect(self.open_context_menu)

        # Chamar a função para atualizar a lista inicialmente
        self.atualizar_treeView_lista_linha() 

        # Configura o delegado personalizado
        custom_delegate = CustomDelegate(self.dlg.treeViewListaLinha)
        self.dlg.treeViewListaLinha.setItemDelegate(custom_delegate)
        self.dlg.treeViewListaLinha.update()  # Força a atualização do QTreeView

        # TreeView: tooltip + drag&drop (UMA ÚNICA instalação do filtro)
        tv = self.dlg.treeViewListaLinha

        # Mouse move no viewport (tooltip/hovers)
        tv.setMouseTracking(True)
        tv.viewport().setMouseTracking(True)

        # Drag & Drop de arquivos/pastas
        tv.setAcceptDrops(True)
        tv.viewport().setAcceptDrops(True)
        tv.setDragDropMode(QAbstractItemView.DragDropMode.DropOnly)
        tv.setDefaultDropAction(Qt.DropAction.CopyAction)

        # Instala apenas UM filtro (tooltip + drop)
        self._tree_filter = TreeViewEventFilter(self)
        tv.viewport().installEventFilter(self._tree_filter)

        self._tree_sync_depth = 0

        # Atualiza o QTreeView com as camadas de linha
        self.atualizar_treeView_lista_linha()

        # Conectar sinal de visibilidade de TODOS os grupos
        root = QgsProject.instance().layerTreeRoot()
        self._connect_group_visibility_signals(root)

        # Escuta novos nós (grupos) criados depois que o diálogo já está aberto
        try:
            root.addedChildren.connect(self._on_layer_tree_children_added, type=Qt.ConnectionType.UniqueConnection)
        except TypeError:
            # Se já estiver conectado, ignora
            pass  # nosec B110

        try:
            root.visibilityChanged.connect(
                self._on_any_layer_tree_visibility_changed,
                type=Qt.ConnectionType.UniqueConnection)
        except TypeError:
            try:
                root.visibilityChanged.connect(self._on_any_layer_tree_visibility_changed)
            except Exception:
                pass  # nosec B110

        # Estado persistente (não reinicializar em reconexões)
        if not hasattr(self, "fieldColors"):
            self.fieldColors = {}       # {layer_id: {field_name: QColor/str/...}}
        if not hasattr(self, "fieldVisibility"):
            self.fieldVisibility = {}   # {layer_id: {field_name: bool}}

        # Chama a função para atualizar o estado dos botões
        self.atualizar_estado_botoes()

        # Cria uma seleção sobre a Camada no treeView
        self.dlg.treeViewListaLinha.setStyleSheet("""
            QTreeView::item:hover:!selected {
                background-color: #def2fc; /* Cor de fundo ao passar o mouse sobre itens não selecionados */}
            QTreeView::item:selected {/* Estilo para itens selecionados, se necessário */}""")

        # Mantém na memória a última posição  
        self.ultimo_caminho_salvo = ""  # Inicializa a variável para armazenar o último caminho

       # Conectamos as mudanças de camadas no QGIS para SINCRONIZAR com TreeView
        self.iface.mapCanvas().layersChanged.connect(self.sync_from_qgis_to_treeview)

        # instancia uma vez só o manager
        self.linhas_manager = CamadaLinhasManager(self.iface)

        QgsProject.instance().layerWasAdded.connect(self._on_layer_added)

        # Conecta os sinais aos slots
        self.connect_signals()

    def tr(self, message):
        """
        Traduz textos deste diálogo.
        O contexto precisa ser estável para o Qt Linguist encontrar as traduções.
        """
        return QCoreApplication.translate("UiManager", message)

    def _aplicar_alias_comprimento(self, layer):
        """Mantém o campo interno estável e traduz somente o nome exibido."""
        if not isinstance(layer, QgsVectorLayer) or not layer.isValid():
            return

        # Campo normal e versão truncada de Shapefile.
        for nome_campo in ("Comprimento", "Compriment"):
            idx = layer.fields().indexOf(nome_campo)

            if idx >= 0:
                layer.setFieldAlias(idx,
                    QCoreApplication.translate("UiManager", "Comprimento"))

    def connect_signals(self):

        # Conectar ao sinal de remoção de camadas
        QgsProject.instance().layersRemoved.connect(self.atualizar_treeView_lista_linha)      

        # Conecta o botão para criar uma camada de linhas ao método que adiciona a camada e atualiza o treeView
        self.dlg.ButtonCriarLinha.clicked.connect(self.adicionar_camada_e_atualizar)
        self.dlg.ButtonCriarLinhaNome.clicked.connect(self.abrir_caixa_nome_camada)

        # Conectar o botão de deletar à função de remover a camada
        self.dlg.pushButtonDel.clicked.connect(self.remover_camada_selecionada)

        # Conectar o botão de renomear à função de renomear a camada
        self.dlg.pushButtonRenome.clicked.connect(self.renomear_camada_selecionada)

        # Conectar o botão de salvar permanente à função de salvar a camada
        self.dlg.pushButton_Permanente.clicked.connect(self.salvar_camada_permanente)

        # Conectar o botão 'salvar como' à função 'salvar_camada_multiplo' para salvar em múltiplos formatos
        self.dlg.pushButtonSalvaMultiplos.clicked.connect(self.salvar_camada_multiplo)

        # Sincroniza o seleção da lista de camadas do QGis
        self.iface.currentLayerChanged.connect(self.sincronizar_selecao_com_qgis)

        # Conecta o botão pushButtonFechar ao método fechar_dialogo
        self.dlg.pushButtonFechar.clicked.connect(self.fechar_dialogo)

       # Conecta a alteração da cor da linha do treeView
        self.dlg.treeViewListaLinha.doubleClicked.connect(self.on_treeViewItem_doubleClicked)

        # Conectando o botão à função pushButtonAbrir
        self.dlg.pushButtonAbrir.clicked.connect(self.abrir_adicionar_arquivo)

        #Diálogo que permite ao usuário selecionar campos da camada atual que serão
        self.dlg.pushButtonCampo.clicked.connect(self.abrir_dialogo_selecao_campos)

        # Limpa caches antes de o QGIS destruir os objetos (melhor momento)
        try:
            QgsProject.instance().layersWillBeRemoved.connect(self._on_layers_will_be_removed, Qt.ConnectionType.UniqueConnection)
        except TypeError:
            # alguns wrappers não aceitam Qt.UniqueConnection
            try:
                QgsProject.instance().layersWillBeRemoved.connect(self._on_layers_will_be_removed)
            except Exception:
                pass  # nosec B110

        #Conecta o botão para exportar a camada para DXF
        self.dlg.pushButtonExporta.clicked.connect(self.exportar_para_dxf)

        # Conecta o botão para exportar a camada para KML
        self.dlg.pushButtonExportaKml.clicked.connect(self.exportar_para_kml)

        # Conecta o botão para Zoom
        self.dlg.pushButtonVisualizarLinha.clicked.connect(self.visualizar_linha_selecionada)

        # Conecta o botão para Clocar a Camada de Linha
        self.dlg.pushButtonClonarLinha.clicked.connect(self.clone_layer)

        # Conectar o botão 'pushButtonTabela' à função de abrir a tabela de atributos
        self.dlg.pushButtonTabela.clicked.connect(self.abrir_tabela_atributos)

    def atualizar_estado_botoes(self):
        """
        Atualiza o estado de habilitação dos botões na interface com base na presença ou ausência de camadas no modelo do treeView.

        Funcionalidades:
        - Verifica se o modelo do treeView está vazio, ou seja, se não contém nenhuma camada.
        - Habilita ou desabilita todos os botões relevantes com base na presença de camadas. Se não houver camadas, todos os botões são desabilitados para evitar operações que requerem uma camada selecionada.
        - Os botões afetados incluem: deletar camada, renomear camada, salvar permanentemente, salvar múltiplos formatos, abrir tabela de atributos, escolher campos para operações, exportar para DXF, exportar para KML, visualizar linha e clonar linha.
        """
        # Verifica se o modelo do treeView está vazio
        modelo_vazio = self.dlg.treeViewListaLinha.model().rowCount() == 0

        # Atualiza o estado dos botões baseado na presença ou ausência de itens no modelo
        self.dlg.pushButtonDel.setEnabled(not modelo_vazio)
        self.dlg.pushButtonRenome.setEnabled(not modelo_vazio)
        self.dlg.pushButton_Permanente.setEnabled(not modelo_vazio)
        self.dlg.pushButtonSalvaMultiplos.setEnabled(not modelo_vazio)
        self.dlg.pushButtonTabela.setEnabled(not modelo_vazio)
        self.dlg.pushButtonCampo.setEnabled(not modelo_vazio)
        self.dlg.pushButtonExporta.setEnabled(not modelo_vazio)
        self.dlg.pushButtonExportaKml.setEnabled(not modelo_vazio)
        self.dlg.pushButtonVisualizarLinha.setEnabled(not modelo_vazio)
        self.dlg.pushButtonClonarLinha.setEnabled(not modelo_vazio)
        self.dlg.pushButtonReprojetarLinha.setEnabled(not modelo_vazio)

    def _connect_group_visibility_signals(self, group_node):
        """
        Conecta recursivamente 'visibilityChanged' de todos os grupos, sem duplicar conexões.
        Passa o próprio group_node ao slot e registra o estado inicial do checkbox do grupo.
        """
        # GARANTIA: só grupos
        if not isinstance(group_node, QgsLayerTreeGroup):
            return

        # cache de último estado do checkbox do grupo
        if not hasattr(self, "_grp_last_checked"):
            self._grp_last_checked = {}

        # estado inicial do checkbox do grupo
        try:
            curr_checked = group_node.itemVisibilityChecked()
        except Exception:
            curr_checked = group_node.isVisible()
        self._grp_last_checked[id(group_node)] = bool(curr_checked)

        # conecta sem duplicar
        try:
            group_node.visibilityChanged.connect(
                lambda *a, g=group_node: self._on_group_visibility_changed(g, *a),
                type=Qt.ConnectionType.UniqueConnection)

        except TypeError:
            pass  # nosec B110

        # desce nos subgrupos
        for child in group_node.children():
            if isinstance(child, QgsLayerTreeGroup):
                self._connect_group_visibility_signals(child)

    def _on_group_visibility_changed(self, group_node, *args):
        """
        Propaga visibilidade APENAS quando o checkbox do PRÓPRIO grupo foi alternado.
        Se a mudança veio de uma camada (grupo fica 'parcial'), não propaga.
        """
        if not isinstance(group_node, QgsLayerTreeGroup):
            return
        if getattr(self, "_vis_propagating", False):
            return
        if not hasattr(self, "_grp_last_checked"):
            self._grp_last_checked = {}

        # estado atual do checkbox do grupo
        try:
            checked_self = group_node.itemVisibilityChecked()
        except Exception:
            checked_self = group_node.isVisible()
        checked_self = bool(checked_self)

        prev_checked = self._grp_last_checked.get(id(group_node), checked_self)
        toggled_by_group = (checked_self != prev_checked)

        # Atualiza cache já aqui
        self._grp_last_checked[id(group_node)] = checked_self

        # Se NÃO foi clique no grupo (foi numa camada → estado parcial), não propaga
        if not toggled_by_group:
            # ainda assim, mantém seu treeView sincronizado
            self.sync_from_qgis_to_treeview()
            return

        # Clique FOI no grupo → propaga coerentemente para os descendentes
        # Coleta todas as camadas descendentes
        layers = []
        stack = [group_node]
        while stack:
            g = stack.pop()
            for ch in g.children():
                if isinstance(ch, QgsLayerTreeLayer):
                    layers.append(ch)
                elif isinstance(ch, QgsLayerTreeGroup):
                    stack.append(ch)

        if not layers:
            self.sync_from_qgis_to_treeview()
            return

        # usa o estado do checkbox da camada, não a visibilidade efetiva
        any_checked = any(bool(ln.itemVisibilityChecked()) for ln in layers)

        # Caso 1: grupo marcado e já havia alguma camada marcada → não mexe nelas
        if checked_self and any_checked:
            self.sync_from_qgis_to_treeview()
            return

        # Caso 2: grupo desmarcado e nenhuma camada estava marcada → nada a fazer
        if (not checked_self) and (not any_checked):
            self.sync_from_qgis_to_treeview()
            return

        # Caso 3: precisamos PROPGAR o estado do grupo para todas as camadas
        try:
            self._vis_propagating = True
            for ln in layers:
                ln.setItemVisibilityChecked(checked_self)
        finally:
            self._vis_propagating = False

        # Mantém o treeView sincronizado com o QGIS
        self.sync_from_qgis_to_treeview()

    def _on_layer_tree_children_added(self, node, indexFrom, indexTo):
        """
        Slot chamado quando novos nós são adicionados à árvore de camadas.

        Garante que grupos criados *depois* da abertura do diálogo também tenham
        o sinal visibilityChanged conectado em _on_group_visibility_changed.

        Parâmetros:
        - node: QgsLayerTreeNode pai que recebeu novos filhos.
        - indexFrom, indexTo: intervalo de índices dos filhos recém-adicionados.
        """
        # Nem todo node terá children() (por segurança)
        try:
            children = node.children()
        except AttributeError:
            return

        # Percorre apenas os filhos que acabaram de ser inseridos
        for i in range(indexFrom, indexTo + 1):
            if i < 0 or i >= len(children):
                continue

            child = children[i]

            # Se for um grupo, conecta os sinais de visibilidade nele
            if isinstance(child, QgsLayerTreeGroup):
                # Esse método já é recursivo e conecta subgrupos também
                self._connect_group_visibility_signals(child)

    def configurar_tooltip(self, index):
        """
        Configura um tooltip para exibir informações sobre a camada de linha selecionada no treeView.

        A função extrai informações sobre a camada de linha, como o tipo de linha (ex: LineString) e o sistema
        de referência de coordenadas (SRC) atual da camada. Essas informações são exibidas em um tooltip
        que aparece quando o usuário passa o mouse sobre o item correspondente no treeView.

        Parâmetros:
        - self: Referência à instância atual do objeto. (UiManager)
        - index: QModelIndex do item atualmente sob o cursor no treeView.

        A função não retorna valores.
        """
        item = index.model().itemFromIndex(index)  # Obtém o item do modelo de dados com base no índice fornecido
        layer_id = item.data()  # Obtém o ID da camada associada ao item
        layer = QgsProject.instance().mapLayer(layer_id)  # Recupera a camada correspondente ao ID no projeto QGIS
        if layer:  # Verifica se a camada existe
            tipo_linha = self.obter_tipo_de_linha(layer)  # Obtém o tipo de linha (ex: LineString) da camada
            crs = layer.crs().description() if layer.crs().isValid() else self.tr("Sem Georreferências")  # Obtém a descrição do SRC da camada ou "Sem Georreferências" se inválido
            tooltip_text = self.tr("Tipo: {tipo_linha}\nSRC: {crs}").format(tipo_linha=tipo_linha, crs=crs)  # Formata o texto do tooltip com as informações da camada
            QToolTip.showText(QCursor.pos(), tooltip_text)  # Exibe o tooltip na posição atual do cursor

    def obter_tipo_de_linha(self, layer):
        """
        Retorna uma string que descreve o tipo de geometria da camada fornecida.

        A função obtém o tipo de geometria WKB (Well-Known Binary) da camada e converte esse tipo
        em uma string legível, como 'LineString', 'MultiLineStringZM', etc.

        Parâmetros:
        - self: Referência à instância atual do objeto. (UiManager)
        - layer: Objeto QgsVectorLayer representando a camada de onde o tipo de linha será extraído.

        Retorno:
        - tipo_linha (str): Uma string que descreve o tipo de geometria da camada.
        """
        geometry_type = layer.wkbType()  # Obtém o tipo de geometria WKB (Well-Known Binary) da camada
        tipo_linha = QgsWkbTypes.displayString(geometry_type)  # Converte o tipo de geometria em uma string legível
        return tipo_linha  # Retorna a string que descreve o tipo de geometria

    def visualizar_linha_selecionada(self):
        """
        Aproxima a visualização do mapa para a camada de linha selecionada no treeView.

        Observação: ao criar/adicionar feições recentemente, a extensão (extent) pode ainda
        não estar atualizada. Por isso, forçamos updateExtents() e, se necessário, tentamos
        novamente no próximo ciclo da UI.
        """
        index = self.dlg.treeViewListaLinha.currentIndex()
        if not index.isValid():
            return

        item = index.model().itemFromIndex(index)
        if item is None:
            return

        layer_id = item.data()
        layer = QgsProject.instance().mapLayer(layer_id)
        if not layer or not hasattr(layer, "extent"):
            return

        def _do_zoom():
            # Força atualização da extensão (camadas recém-criadas podem vir com extent vazio)
            try:
                layer.updateExtents()
            except Exception:
                pass  # nosec B110

            rect = layer.extent()
            if not rect or rect.isEmpty():
                return

            # Opção 1: garante que a camada selecionada é a ativa antes de aplicar o zoom do QGIS
            self.iface.setActiveLayer(layer)
            self.iface.zoomToActiveLayer()

        # Tentativa imediata
        _do_zoom()

        # Se ainda estiver sem extent, tenta mais uma vez no próximo "tick" da UI
        try:
            layer.updateExtents()
        except Exception:
            pass  # nosec B110

        if layer.extent().isEmpty():
            QTimer.singleShot(0, _do_zoom)

    def abrir_dialogo_crs(self):
        """
        Abre um diálogo de seleção de CRS e reprojeta a camada selecionada no treeView.

        A função permite ao usuário escolher um novo sistema de referência de coordenadas (SRC) para a camada 
        selecionada no treeView. Após a seleção, a camada é reprojetada usando o novo SRC, e a nova camada é 
        adicionada ao projeto QGIS com a mesma cor e estilo de rótulo da camada original.

        Parâmetros:
        - self: Referência à instância atual do objeto. (UiManager)

        A função não retorna valores, mas adiciona uma nova camada reprojetada ao projeto QGIS.
        """
        index = self.dlg.treeViewListaLinha.currentIndex()  # Obtém o índice atualmente selecionado no treeView
        if not index.isValid():  # Verifica se o índice é válido (se há uma seleção)
            return  # Sai da função se o índice não for válido
        
        layer_id = index.model().itemFromIndex(index).data()  # Obtém o ID da camada associada ao item selecionado
        layer = QgsProject.instance().mapLayer(layer_id)  # Recupera a camada correspondente ao ID no projeto QGIS
        if not layer:  # Verifica se a camada existe
            return  # Sai da função se a camada não existir
        
        # Abre o diálogo de seleção de CRS para que o usuário possa escolher um novo SRC
        dialog = QgsProjectionSelectionDialog(self.dlg)  # Cria uma instância do diálogo de seleção de CRS
        dialog.setCrs(layer.crs())  # Configura o CRS atual da camada como o CRS padrão no diálogo
        if dialog.exec():  # Exibe o diálogo e verifica se o usuário confirmou a seleção
            novo_crs = dialog.crs()  # Obtém o novo CRS selecionado pelo usuário

            # Usa o processamento do QGIS para reprojetar a camada
            params = {
                'INPUT': layer,  # Define a camada original como entrada
                'TARGET_CRS': novo_crs,  # Define o novo CRS como o CRS alvo
                'OUTPUT': 'memory:'  # Salva o resultado na memória
            }
            resultado = processing.run('qgis:reprojectlayer', params)  # Executa o processo de reprojeção
            nova_camada = resultado['OUTPUT']  # Obtém a nova camada reprojetada a partir dos resultados

            # Verifique se a nova camada tem feições válidas
            if nova_camada and nova_camada.isValid():  # Verifica se a nova camada foi criada corretamente
                # Gerar nome único para a nova camada reprojetada
                novo_nome = self.gerar_nome_unico_rep(layer.name())  # Gera um nome único para evitar duplicidades
                nova_camada.setName(novo_nome)  # Define o nome da nova camada

                # Aplicar a cor da camada original
                self.aplicar_cor_linha(nova_camada, self.obter_cor_linha(layer))  # Copia a cor da camada original

                # Aplicar o estilo de rótulo da camada original
                self.aplicar_estilo_rotulo(nova_camada, layer)  # Copia o estilo de rótulo da camada original

                QgsProject.instance().addMapLayer(nova_camada)  # Adiciona a nova camada reprojetada ao projeto

                # Atualiza a camada na tela
                layer.triggerRepaint()  # Recarrega a camada original (caso necessário)
                self.iface.mapCanvas().refresh()  # Atualiza a tela do mapa para refletir a nova camada

                # Exibe uma mensagem informando que a camada foi reprojetada
                texto_mensagem = self.tr("A camada '{layer_name}' foi reprojetada para {crs_authid} ({crs_description}) com o nome '{novo_nome}'.").format(layer_name=layer.name(), crs_authid=novo_crs.authid(), crs_description=novo_crs.description(), novo_nome=novo_nome)
                self.mostrar_mensagem(texto_mensagem, "Sucesso")  # Exibe a mensagem na barra de mensagens do QGIS
            else:
                self.mostrar_mensagem(self.tr("Erro na reprojeção da camada '{layer_name}'.").format(layer_name=layer.name()), "Erro")  # Exibe uma mensagem de erro se a reprojeção falhar

    def gerar_nome_unico_rep(self, base_nome):
        """
        Gera um nome único para uma nova camada baseada no nome da camada original.

        A função cria um novo nome para a camada reprojetada, adicionando um sufixo incremental 
        (_rep1, _rep2, etc.) ao nome base, garantindo que o novo nome seja único dentro do projeto QGIS.

        Parâmetros:
        - self: Referência à instância atual do objeto. (UiManager)
        - base_nome (str): O nome original da camada, usado como base para gerar o novo nome.

        Retorno:
        - novo_nome (str): Um nome único gerado para a nova camada reprojetada.
        """
        # Cria um conjunto contendo todos os nomes de camadas existentes no projeto QGIS
        existing_names = {layer.name() for layer in QgsProject.instance().mapLayers().values()}
        
        # Se o nome base ainda não existir no projeto, retorna com o sufixo _rep1
        if base_nome not in existing_names:
            return f"{base_nome}_rep1"
        
        # Inicia o contador de sufixos em 1
        i = 1
        # Gera o primeiro nome com o sufixo _rep1
        novo_nome = f"{base_nome}_rep{i}"
        
        # Incrementa o sufixo até encontrar um nome que não exista no projeto
        while novo_nome in existing_names:
            i += 1
            novo_nome = f"{base_nome}_rep{i}"
        
        # Retorna o nome único gerado
        return novo_nome

    def obter_estilo_rotulo(self, layer):
        """
        Obtém as configurações de rótulo da camada fornecida.

        A função recupera as configurações de rotulagem da camada especificada. Se a camada tiver 
        um estilo de rotulagem definido, a função retorna uma cópia (clone) dessas configurações 
        para que possam ser aplicadas a outra camada. Se a camada não tiver rotulagem definida, 
        a função retorna None.

        Parâmetros:
        - self: Referência à instância atual do objeto. (UiManager)
        - layer: Objeto QgsVectorLayer representando a camada da qual as configurações de rótulo 
          serão extraídas.

        Retorno:
        - labeling (QgsAbstractVectorLayerLabeling ou None): Retorna uma cópia das configurações 
          de rotulagem se existirem, caso contrário, retorna None.
        """
        labeling = layer.labeling()  # Obtém as configurações de rotulagem da camada
        if labeling:  # Verifica se a camada possui rotulagem definida
            return labeling.clone()  # Retorna uma cópia das configurações de rotulagem
        return None  # Retorna None se não houver rotulagem definida

    def aplicar_estilo_rotulo(self, nova_camada, camada_original):
        """
        Aplica o estilo de rótulo da camada original à nova camada reprojetada.

        A função tenta copiar as configurações de rótulo da camada original para a nova camada 
        reprojetada. Se a cópia direta do estilo de rótulo não for bem-sucedida, a função tenta 
        configurar manualmente o estilo de rótulo baseado no campo de rótulo da camada original.

        Se os rótulos não estiverem ativados na camada original, não serão aplicados à nova camada.

        Parâmetros:
        - self: Referência à instância atual do objeto. (UiManager)
        - nova_camada: Objeto QgsVectorLayer representando a nova camada para a qual o estilo de rótulo será aplicado.
        - camada_original: Objeto QgsVectorLayer representando a camada original da qual o estilo de rótulo será copiado.

        A função não retorna valores, mas aplica o estilo de rótulo à nova camada.
        """
        # Verifica se a camada original tem rotulagem ativa
        if camada_original.labelsEnabled():
            # Obtém as configurações de rótulo da camada original
            label_settings = self.obter_estilo_rotulo(camada_original)
            if label_settings:  # Verifica se as configurações de rótulo foram obtidas
                nova_camada.setLabeling(label_settings)  # Aplica as configurações de rótulo à nova camada
                nova_camada.setLabelsEnabled(True)  # Certifica-se de que os rótulos estão ativados na nova camada
                nova_camada.triggerRepaint()  # Recarrega a camada para aplicar as mudanças visuais

            # Se ainda não funcionar, tenta configurar manualmente o estilo dos rótulos
            else:
                provider = camada_original.dataProvider()  # Obtém o provedor de dados da camada original
                if provider:  # Verifica se o provedor de dados foi obtido
                    # Tenta acessar as configurações de rótulo manualmente, se disponível
                    expression = camada_original.labeling().settings().fieldName
                    if expression:  # Verifica se o campo de rótulo foi obtido
                        nova_camada.setLabelsEnabled(True)  # Ativa os rótulos na nova camada
                        label_settings = QgsPalLayerSettings()  # Cria uma nova instância de configurações de rótulo
                        label_settings.fieldName = expression  # Define o campo de rótulo
                        label_settings.isExpression = True  # Define que o rótulo é baseado em uma expressão
                        label_settings.placement = QgsPalLayerSettings.Placement.Line  # Define o posicionamento dos rótulos
                        labeling = QgsVectorLayerSimpleLabeling(label_settings)  # Cria o sistema de rotulagem simples
                        nova_camada.setLabeling(labeling)  # Aplica o sistema de rotulagem à nova camada
                        nova_camada.triggerRepaint()  # Recarrega a camada para aplicar as mudanças visuais

    def abrir_caixa_nome_camada(self):
        """
        Abre o diálogo para configurar a nova camada de linhas:

        - nome da camada;
        - cor opcional;
        - SRC opcional;
        - exibição ou supressão do formulário de atributos.
        """
        dialog = QDialog(self.dlg)
        dialog.setWindowTitle(self.tr("Nome da Camada"))

        layout = QVBoxLayout(dialog)

        # Frame principal
        frame = QFrame()
        frame.setFrameStyle(
            QFrame.Shape.Box |
            QFrame.Shadow.Raised)

        frame_layout = QVBoxLayout(frame)
        frame_layout.setContentsMargins(8, 8, 8, 8)
        frame_layout.setSpacing(6)

        # Nome da camada
        frame_layout.addWidget( QLabel(self.tr("Digite o nome da camada:")))

        lineEdit = QLineEdit()

        # Texto real e editável, não placeholder
        lineEdit.setText(self.tr("Linhas Temporárias"))

        frame_layout.addWidget(lineEdit)

        # Botões de cor e SRC
        hLayoutBotoesCorReproj = QHBoxLayout()
        hLayoutBotoesCorReproj.setSpacing(6)

        pushButtonCor = QPushButton(self.tr("Escolher Cor"))

        pushButtonReproj = QPushButton(self.tr("Projetar SRC"))

        hLayoutBotoesCorReproj.addWidget(pushButtonCor)

        hLayoutBotoesCorReproj.addWidget(pushButtonReproj)

        frame_layout.addLayout( hLayoutBotoesCorReproj)

        # Checkbox do formulário de atributos
        checkBoxNaoExibirDialogo = QCheckBox(self.tr("Não exibir diálogo de atributos"))

        checkBoxNaoExibirDialogo.setChecked(False)

        checkBoxNaoExibirDialogo.setToolTip(
            self.tr("Quando marcado, as linhas serão adicionadas "
                "sem abrir o formulário de atributos."))

        frame_layout.addWidget(checkBoxNaoExibirDialogo)

        layout.addWidget(frame)

        # Valores opcionais
        selectedColor = None
        selectedCrs = None

        # Escolher cor
        def escolher_cor():
            nonlocal selectedColor

            cor_inicial = (QColor(0, 0, 0)
                if selectedColor is None
                else selectedColor)

            cor = QColorDialog.getColor(cor_inicial, dialog, self.tr("Escolher Cor da Linha"))

            if not cor.isValid():
                return

            selectedColor = QColor(cor)

            cor_texto = ("#000000"
                if cor.lightness() > 150
                else "#ffffff" )

            pushButtonCor.setStyleSheet("QPushButton {"
                f"background-color: {cor.name()};"
                f"color: {cor_texto};"
                "}")

        pushButtonCor.clicked.connect(escolher_cor)

        # Escolher SRC
        def escolher_crs():
            nonlocal selectedCrs

            dialog_crs = QgsProjectionSelectionDialog(dialog)

            crs_inicial = (selectedCrs
                if (isinstance( selectedCrs, QgsCoordinateReferenceSystem)
                    and selectedCrs.isValid())
                else QgsProject.instance().crs())

            dialog_crs.setCrs(crs_inicial)

            if (dialog_crs.exec()
                != QDialog.DialogCode.Accepted):
                return

            novo_crs = dialog_crs.crs()

            if not novo_crs.isValid():
                return

            selectedCrs = QgsCoordinateReferenceSystem(novo_crs)

            pushButtonReproj.setText(novo_crs.authid()
                or self.tr("SRC selecionado"))

            pushButtonReproj.setToolTip(self.tr("{authid} - {description}").format(authid=novo_crs.authid(), description=novo_crs.description()))

        pushButtonReproj.clicked.connect(escolher_crs)

        # Botões Adicionar e Cancelar
        okButton = QPushButton(self.tr("Adicionar"))

        cancelButton = QPushButton(self.tr("Cancelar"))

        # O campo já inicia preenchido
        okButton.setEnabled(bool(lineEdit.text().strip()))

        lineEdit.textChanged.connect(lambda texto:
            okButton.setEnabled(bool(texto.strip())))

        buttonLayout = QHBoxLayout()
        buttonLayout.addWidget(okButton)
        buttonLayout.addWidget(cancelButton)

        layout.addLayout(buttonLayout)

        okButton.clicked.connect(dialog.accept)

        cancelButton.clicked.connect(dialog.reject)

        # Seleciona "Linhas Temporárias" quando o diálogo abrir
        QTimer.singleShot(0, lambda: (lineEdit.setFocus(), lineEdit.selectAll()))

        # Executa o diálogo
        if (dialog.exec()
            != QDialog.DialogCode.Accepted):
            return

        nome_camada = lineEdit.text().strip()

        if not nome_camada:
            return

        if selectedCrs is None:
            selectedCrs = QgsProject.instance().crs()

        # Cria a camada
        nova_camada = (self.linhas_manager.criar_camada_linhas( nome_camada=nome_camada, cor=selectedColor, crs=selectedCrs.authid()))

        if (not isinstance(nova_camada, QgsVectorLayer)
            or not nova_camada.isValid()):
            self.mostrar_mensagem(self.tr("Não foi possível criar a camada de linhas."), "Erro")
            return

        # Configura o formulário somente para esta camada
        try:
            config_formulario = (nova_camada.editFormConfig())

            if checkBoxNaoExibirDialogo.isChecked():
                try:
                    config_formulario.setSuppress(Qgis.AttributeFormSuppression.On)
                except Exception:
                    config_formulario.setSuppress(QgsEditFormConfig.FeatureFormSuppress.SuppressOn)
            else:
                try:
                    config_formulario.setSuppress(Qgis.AttributeFormSuppression.Off)
                except Exception:
                    config_formulario.setSuppress(QgsEditFormConfig.FeatureFormSuppress.SuppressOff)

            nova_camada.setEditFormConfig(config_formulario)

        except Exception:
            pass  # nosec B110

        # Atualiza primeiro o TreeView
        self.atualizar_treeView_lista_linha()

        def selecionar_e_ativar_nova_camada():
            try:
                # Garante que a camada recém-criada seja a camada ativa
                self.iface.setActiveLayer(nova_camada)

                self.iface.layerTreeView().setCurrentLayer(nova_camada)

                # Seleciona explicitamente a nova camada
                # no TreeView do plugin
                model = self.dlg.treeViewListaLinha.model()

                if model is not None:
                    for row in range(model.rowCount()):
                        item = model.item(row)

                        if (item
                            and item.data() == nova_camada.id()):
                            index = model.indexFromItem(item)

                            self.dlg.treeViewListaLinha.setCurrentIndex(index)

                            self.dlg.treeViewListaLinha.scrollTo(index)

                            break

                # Ativa a ferramenta "Adicionar Linha"
                action = self.iface.actionAddFeature()

                if (action is not None
                    and action.isEnabled()
                    and not action.isChecked()):
                    action.trigger()

            except Exception:
                pass  # nosec B110

        # Executa depois que QGIS/TreeView concluírem
        # a atualização da nova camada
        QTimer.singleShot(0, selecionar_e_ativar_nova_camada)

    def conectar_sinal_de_visibilidade(self, layer: QgsVectorLayer):
        """
        Conecta sinais relevantes do QGIS à camada fornecida, garantindo que eventos de visibilidade,
        mudança de nome e alteração de simbologia sejam refletidos automaticamente no treeView da interface.

        Funcionalidades detalhadas:
        1. Verifica se os sinais da camada já foram conectados para evitar duplicidade de conexão.
        2. Localiza o objeto QgsLayerTreeLayer correspondente à camada no projeto QGIS.
        3. Se encontrado, conecta os seguintes sinais:
           - visibilityChanged: dispara quando a visibilidade da camada muda.
           - nameChanged: dispara quando o nome da camada é alterado.
           - rendererChanged: dispara quando o estilo de simbologia da camada é modificado.
        4. Utiliza Qt.UniqueConnection para evitar múltiplas conexões do mesmo sinal ao mesmo slot.
        5. Marca a camada como conectada, registrando seu ID em um conjunto interno.
        """
        if layer.id() in self._layer_signals_connected:
            return  # Já conectado anteriormente, evita conexão duplicada

        layer_tree_layer = (QgsProject.instance().layerTreeRoot().findLayer(layer.id()))
        if not layer_tree_layer:
            return  # Não encontrou o layer na árvore, nada a conectar

        # Conecta o sinal de visibilidade (checkbox)
        layer_tree_layer.visibilityChanged.connect(self.atualizar_item_visibilidade, Qt.ConnectionType.UniqueConnection)
        # Conecta o sinal de mudança de nome
        layer_tree_layer.nameChanged.connect(self.atualizar_nome_camada, Qt.ConnectionType.UniqueConnection)
        # Conecta o sinal de alteração de simbologia
        layer.rendererChanged.connect(lambda: self.atualizar_cor_simbologia(layer), Qt.ConnectionType.UniqueConnection)

        # Marca a camada como já conectada para não duplicar conexões
        self._layer_signals_connected.add(layer.id())

    def _on_layer_added(self, layer: QgsMapLayer):
        """
        Slot chamado automaticamente sempre que uma nova camada é adicionada ao projeto QGIS.

        Para camadas de linha, garante que o nó da árvore nasça marcado/visível
        e só depois reconstrói o treeView, no próximo ciclo da UI.
        """
        if not self.eh_camada_de_linha(layer):
            return

        def _finish_add():
            try:
                root = QgsProject.instance().layerTreeRoot()
                node = root.findLayer(layer.id())
                if node is not None:
                    node.setItemVisibilityChecked(True)
            except Exception:
                pass  # nosec B110

            try:
                self.conectar_sinal_de_visibilidade(layer)
            except Exception:
                pass  # nosec B110

            self.atualizar_treeView_lista_linha()
            self.sync_from_qgis_to_treeview()

        QTimer.singleShot(0, _finish_add)

    def _on_layers_will_be_removed(self, layer_ids):
        """
        Limpa caches internos quando camadas forem removidas do projeto,
        evitando crescimento indefinido em sessões longas.
        """
        if not layer_ids:
            return

        # layer_ids pode vir como QStringList; garantimos lista python
        try:
            ids = list(layer_ids)
        except Exception:
            ids = [layer_ids]

        for lid in ids:
            lid = str(lid)
            # cache que impede reconectar sinais
            if hasattr(self, "_layer_signals_connected"):
                self._layer_signals_connected.discard(lid)

            # (opcional, mas recomendado) limpa caches por layer, se existirem
            if hasattr(self, "fieldColors"):
                self.fieldColors.pop(lid, None)
            if hasattr(self, "fieldVisibility"):
                self.fieldVisibility.pop(lid, None)

    def atualizar_cor_simbologia(self, layer):
        """
        Atualiza no treeView a cor correspondente à simbologia atual da camada.
        Compatível com símbolo único e simbologia categorizada.
        """
        if (layer is None
            or not isinstance(layer, QgsVectorLayer)
            or sip.isdeleted(layer)):
            return

        model = self.dlg.treeViewListaLinha.model()

        if model is None:
            return

        cor_linha = None

        # Primeiro tenta a lógica já existente
        try:
            cor_obtida = self.obter_cor_linha(layer)

            if isinstance(cor_obtida, QColor):
                if cor_obtida.isValid():
                    cor_linha = QColor(cor_obtida)

            elif cor_obtida is not None:
                cor_teste = QColor(cor_obtida)

                if cor_teste.isValid():
                    cor_linha = cor_teste

        except (TypeError, RuntimeError):
            cor_linha = None

        # Fallback para simbologia categorizada/graduada/etc.
        if cor_linha is None:
            try:
                renderer = layer.renderer()

                if renderer is not None:
                    symbols = renderer.symbols(QgsRenderContext())

                    if symbols:
                        cor_linha = QColor(symbols[0].color())

            except (TypeError, RuntimeError, AttributeError):
                cor_linha = None

        # Último fallback para nunca passar None ao QColor
        if cor_linha is None or not cor_linha.isValid():
            cor_linha = QColor(Qt.GlobalColor.black)

        for row in range(model.rowCount()):
            item = model.item(row)

            if not item:
                continue

            if item.data() != layer.id():
                continue

            item.setData(cor_linha.name(QColor.NameFormat.HexArgb), Qt.ItemDataRole.UserRole)

            break

        self.dlg.treeViewListaLinha.viewport().update()

    def atualizar_nome_camada(self, layer_tree_layer):
        """
        Atualiza o nome de uma camada na visualização treeView quando o nome da camada é alterado no projeto.

        Parâmetros:
        - layer_tree_layer (QgsLayerTreeLayer): A camada do projeto cujo nome foi alterado.

        Funcionalidades:
        - Acessa o modelo de dados associado ao treeView.
        - Percorre todas as linhas do modelo para encontrar a camada correspondente pelo ID.
        - Quando a camada é encontrada, atualiza o texto do item no treeView com o novo nome da camada.
        - Interrompe a busca assim que a camada correta é atualizada, para eficiência.
        """
        model = self.dlg.treeViewListaLinha.model()
        for row in range(model.rowCount()):
            item = model.item(row)
            if item and item.data() == layer_tree_layer.layerId():
                novo_nome = layer_tree_layer.name()
                item.setText(novo_nome)
                break

    def atualizar_treeView_lista_linha(self):
        """
        Atualiza o treeView com as camadas de linhas disponíveis no projeto QGIS.

        Funcionalidades:
        - Salva o ID da camada atualmente selecionada no treeView.
        - Atualiza o modelo do treeView com as camadas de linhas existentes.
        - Restaura a seleção anterior no treeView, se possível.
        - Se nenhuma seleção anterior existir, seleciona o primeiro item no treeView.
        - Atualiza o estado dos botões da interface com base no conteúdo do treeView.

        Atribuições:
        - current_layer_id: Armazena o ID da camada atualmente selecionada (se houver).
        - current_index: Obtém o índice atualmente selecionado no treeView.
        - model: Modelo associado ao treeView, usado para manipular os itens.
        """
        # Salva o ID da camada atualmente selecionada, se houver uma seleção válida
        current_layer_id = None  # Inicializa a variável para armazenar o ID da camada selecionada
        current_index = self.dlg.treeViewListaLinha.currentIndex()  # Obtém o índice atualmente selecionado no treeView
        if current_index.isValid():  # Verifica se o índice atual é válido
            current_layer_id = current_index.model().itemFromIndex(current_index).data()  # Obtém o ID da camada associada ao índice

        # Atualiza o modelo do treeView com as camadas de linhas disponíveis
        self.criar_modelo_para_treeview()  # Cria um novo modelo para o treeView
        self.adicionar_camadas_ao_modelo()  # Adiciona as camadas de linhas ao modelo

        # Restaura a seleção anterior no treeView, se possível
        model = self.dlg.treeViewListaLinha.model()  # Obtém o modelo atual do treeView
        if current_layer_id:  # Verifica se havia uma camada selecionada anteriormente
            for row in range(model.rowCount()):  # Itera sobre todas as linhas do modelo
                item = model.item(row)  # Obtém o item na linha atual
                if item and item.data() == current_layer_id:  # Verifica se o item corresponde à camada anteriormente selecionada
                    index = model.indexFromItem(item)  # Obtém o índice do item correspondente
                    self.dlg.treeViewListaLinha.setCurrentIndex(index)  # Define o índice como o item selecionado no treeView
                    break  # Sai do loop após encontrar e restaurar a seleção
        elif model.rowCount() > 0:  # Se não houver seleção anterior, mas houver itens no modelo
            first_index = model.index(0, 0)  # Obtém o índice do primeiro item no modelo
            self.dlg.treeViewListaLinha.setCurrentIndex(first_index)  # Define o primeiro item como selecionado

        # Atualiza o estado dos botões da interface com base no conteúdo do treeView
        self.atualizar_estado_botoes()  # Habilita ou desabilita botões conforme necessário

    def adicionar_camada_e_atualizar(self):
        """
        Cria uma nova camada de linhas e atualiza a visualização no treeView para incluir essa nova camada.

        Funcionalidades:
        - Chama a função criar_camada_linhas, que é responsável por criar e configurar uma nova camada de linhas no projeto.
        - Atualiza a árvore de visualização de camadas (treeView) chamando o método atualizar_treeView_lista_linha. Isso garante que a nova camada seja imediatamente visível na lista de camadas na interface do usuário.

        Atribuição no código:
        Essencial para a funcionalidade de adição de novas camadas no projeto. Permite ao usuário criar rapidamente uma nova camada de linhas e ver essa adição refletida na interface do usuário sem ações adicionais, melhorando a fluidez e a interação no uso do aplicativo.
        """
        # Chamada para a função que cria uma nova camada de linhas
        self.linhas_manager.criar_camada_linhas()

        # Após adicionar a camada, atualize o treeView
        self.atualizar_treeView_lista_linha()

    def on_item_changed(self, item):
        """
        É acionada sempre que um item do modelo (QStandardItem) tem seu estado de
        checkbox alterado (marcado ou desmarcado), atualizando a visibilidade da
        camada no QGIS de maneira equivalente ao UiManagerP.

        Funções e Ações Desenvolvidas:
        - Obtém o ID da camada (layer_id) armazenado no item (item.data()).
        - Localiza a camada no projeto QGIS usando mapLayer(layer_id).
        - Encontra o nó correspondente na árvore de camadas (layerTreeRoot().findLayer(layer_id)).
        - Ajusta a visibilidade da camada chamando node.setItemVisibilityChecked(...)
          com base no estado do checkbox (item.checkState()).
        
        Observações Importantes:
        - Substitui a lógica anterior baseada em dataChanged e signals individuais 
          (visibilityChanged) para cada camada, simplificando a sincronização via 
          checagem e layersChanged.
        """
        # Evita loop/reentrada: quando o modelo é atualizado programaticamente (sync), ignoramos o itemChanged
        if getattr(self, "_tree_sync_depth", 0) > 0:
            return

        # Obtém o ID da camada do próprio item
        layer_id = item.data()
        layer = QgsProject.instance().mapLayer(layer_id)
        if not layer:
            return

        # Acha o nó da camada na árvore do QGIS
        root = QgsProject.instance().layerTreeRoot()
        node = root.findLayer(layer_id)

        if node:
            # Ajusta a visibilidade com base no estado do checkbox
            node.setItemVisibilityChecked(item.checkState() == Qt.CheckState.Checked)

    def adicionar_camadas_ao_modelo(self):
        """
        Adiciona as camadas de linha do projeto QGIS ao modelo do QTreeView.
    
        IMPORTANTE:
        - Não bloqueia sinais do modelo (para manter o view responsivo).
        - Usa guard (_tree_sync_depth) durante a montagem para evitar que qualquer
          itemChanged eventual dispare lógica de visibilidade.
        """
        model = getattr(self, "model", None)
        if model is None:
            return
    
        self._tree_sync_depth = getattr(self, "_tree_sync_depth", 0) + 1
        try:
            for layer in self.obter_camadas_de_linha():
                item = self.criar_item_para_camada(layer)
                model.appendRow(item)
                self.conectar_sinal_de_visibilidade(layer)
        finally:
            self._tree_sync_depth = max(0, getattr(self, "_tree_sync_depth", 1) - 1)

    def configurar_treeview_header(self):
        """
        Configura o cabeçalho do treeView, definindo o alinhamento padrão do texto do cabeçalho.

        Funcionalidades:
        - Acessa o cabeçalho do treeView, que é a parte superior da visualização onde os títulos das colunas são exibidos.
        - Define o alinhamento padrão do texto do cabeçalho para centralizado (Qt.AlignCenter), garantindo que os títulos das colunas sejam apresentados de forma clara e esteticamente agradável.

        Atribuição no código:
        Melhora a legibilidade e a aparência da interface do usuário, contribuindo para uma experiência visual mais organizada e profissional. Essa configuração é fundamental para manter um padrão visual consistente em toda a aplicação.
        """
        # Acessa o cabeçalho da TreeView
        header = self.dlg.treeViewListaLinha.header()
        # Define o alinhamento padrão para o texto do cabeçalho
        header.setDefaultAlignment(Qt.AlignmentFlag.AlignCenter)

    def obter_camadas_de_linha(self):
        """
        Itera sobre todas as camadas no projeto QGIS e retorna aquelas que são camadas de linha.

        Funcionalidades:
        - Acessa todas as camadas atualmente carregadas no projeto QGIS através do método mapLayers() do QgsProject.
        - Verifica cada camada para determinar se ela é uma camada de linha utilizando o método eh_camada_de_linha, que compara o tipo da geometria da camada com o tipo de geometria de linha.
        - Se a camada for identificada como uma camada de linha, ela é retornada para o chamador através do uso de 'yield', permitindo que a função seja usada em um loop para processar apenas camadas de linha.

        Atribuição no código:
        Essencial para filtrar e trabalhar especificamente com camadas de linha dentro de uma variedade de camadas em um projeto QGIS. Facilita a implementação de funcionalidades que dependem exclusivamente de manipulação ou visualização de camadas de linha, como análises topológicas ou estilização baseada em atributos específicos de linha.
        """
        # Itera sobre todas as camadas no projeto QGIS
        for layer in QgsProject.instance().mapLayers().values():
            # Verifica se a camada é uma camada de linha
            if self.eh_camada_de_linha(layer):
                yield layer # Retorna a camada se ela for uma camada de linha

    def eh_camada_de_linha(self, layer):
        """
        Determina se uma camada especificada é uma camada de linha dentro do projeto QGIS.

        Parâmetros:
        - layer (QgsMapLayer): A camada que está sendo verificada.

        Funcionalidades:
        - Verifica se o tipo da camada é VectorLayer, indicando que a camada é uma camada vetorial.
        - Adicionalmente, verifica se o tipo de geometria da camada é LineGeometry, confirmando que a camada consiste em geometrias de linha.
        - Retorna True se ambas as condições forem atendidas, indicando que a camada é uma camada de linha, ou False caso contrário.

        Atribuição no código:
        Fundamental para filtrar e manipular apenas as camadas de linha dentro de várias funcionalidades do sistema, como análises específicas para linhas, operações de visualização ou processamento de dados de linha. Permite que a aplicação trate de forma eficiente e específica as camadas baseadas em sua tipologia geométrica, otimizando o desempenho e a precisão das operações realizadas.
        """
        # Verifica se o tipo da camada é VectorLayer e o tipo de geometria é LineGeometry
        return layer.type() == QgsMapLayer.LayerType.VectorLayer and layer.geometryType() == QgsWkbTypes.GeometryType.LineGeometry

    def criar_item_para_camada(self, layer):
        """
        Cria um item de visualização para uma camada específica para ser usado no modelo do treeView.
        """
        if (layer is None
            or not isinstance(layer, QgsVectorLayer)
            or sip.isdeleted(layer)):
            return None

        item = QStandardItem(layer.name())

        self.configurar_item(item, layer)

        cor_linha = None

        try:
            cor_obtida = self.obter_cor_linha(layer)

            if isinstance(cor_obtida, QColor):
                if cor_obtida.isValid():
                    cor_linha = QColor(cor_obtida)

            elif cor_obtida is not None:
                cor_teste = QColor(cor_obtida)

                if cor_teste.isValid():
                    cor_linha = cor_teste

        except (TypeError, RuntimeError):
            cor_linha = None

        # Fallback para simbologia categorizada, graduada etc.
        if cor_linha is None:
            try:
                renderer = layer.renderer()

                if renderer is not None:
                    symbols = renderer.symbols(QgsRenderContext())

                    if symbols:
                        cor_linha = QColor(symbols[0].color())

            except (TypeError, RuntimeError, AttributeError):
                cor_linha = None

        # Segurança final
        if cor_linha is None or not cor_linha.isValid():
            cor_linha = QColor(Qt.GlobalColor.black)

        item.setData(cor_linha.name(QColor.NameFormat.HexArgb), Qt.ItemDataRole.UserRole)

        return item

    def configurar_item(self, item, layer):
        """
        Configura as propriedades de um item QStandardItem para refletir as características e o estado de uma camada específica no treeView.

        Parâmetros:
        - item (QStandardItem): O item a ser configurado no modelo do treeView.
        - layer (QgsMapLayer): A camada associada ao item, cujas propriedades influenciarão a configuração do item.

        Funcionalidades:
        - Torna o item selecionável com um checkbox, permitindo que o usuário altere a visibilidade da camada diretamente através do treeView.
        - Armazena o ID da camada como um dado do item para facilitar a identificação e manipulação posterior da camada através do item.
        - Desabilita a capacidade de arrastar o item para evitar reordenamento ou movimentação inapropriada do item no treeView.
        - Define o estado inicial do checkbox do item com base na visibilidade atual da camada, garantindo que o estado do checkbox reflita corretamente o estado de visibilidade da camada.
        - Remove a capacidade de editar o texto do item para manter a integridade do nome da camada como fornecido pelo sistema ou pelo usuário.
        - Configura a fonte do item com base em propriedades específicas da camada, como itálico para camadas temporárias e negrito para outras, ajudando na distinção visual das camadas no treeView.

        Atribuição no código:
        Essencial para a representação adequada das camadas dentro do treeView, garantindo que os itens reflitam de forma precisa e útil as propriedades e o estado das camadas associadas. Facilita a interação do usuário com as camadas, oferecendo controles visuais intuitivos para visibilidade e organização.
        """
        # Torna o item selecionável (checkable)
        item.setCheckable(True)
        # Armazena o ID da camada como um dado do item
        item.setData(layer.id())
        # Desabilita a capacidade de arrastar o item (drag)
        item.setDragEnabled(False)
        # Define o estado do checkbox do item com base na visibilidade da camada
        item.setCheckState(Qt.CheckState.Checked if self.camada_esta_visivel(layer) else Qt.CheckState.Unchecked)
        # Remove a possibilidade de editar o texto do item
        item.setEditable(False)
        # Define a fonte do item com base em propriedades específicas da camada
        item.setFont(self.obter_fonte_para_camada(layer))

    def _node_checkbox_checked(self, node):
        """
        Retorna o estado do checkbox do nó na árvore de camadas,
        independentemente da visibilidade herdada dos grupos.
        Compatível com QGIS 3.x e 4.x.
        """
        if node is None:
            return False

        try:
            return bool(node.itemVisibilityChecked())
        except Exception:
            try:
                return bool(node.isVisible())
            except Exception:
                return False

    def _on_any_layer_tree_visibility_changed(self, node):
        """
        Mantém o treeView sincronizado com qualquer alteração de checkbox
        na árvore de camadas nativa do QGIS.
        """
        if isinstance(node, QgsLayerTreeLayer):
            self.atualizar_item_visibilidade(node)
        else:
            self.sync_from_qgis_to_treeview()

    def camada_esta_visivel(self, layer):
        """
        Retorna o estado do checkbox da camada na árvore do QGIS.
        Não usa visibilidade efetiva herdada de grupos.
        """
        layer_tree_layer = QgsProject.instance().layerTreeRoot().findLayer(layer.id())
        return self._node_checkbox_checked(layer_tree_layer)

    def sync_from_qgis_to_treeview(self):
        """
        Sincroniza o estado do checkbox no QTreeView com o estado do checkbox
        da árvore de camadas do QGIS.
        """
        model = getattr(self, "model", None)
        if model is None:
            return

        root = QgsProject.instance().layerTreeRoot()

        self._tree_sync_depth = getattr(self, "_tree_sync_depth", 0) + 1
        try:
            for i in range(model.rowCount()):
                item = model.item(i)
                if not item:
                    continue

                layer_id = item.data()
                node = root.findLayer(layer_id)
                if not node:
                    continue

                desired = (
                    Qt.CheckState.Checked
                    if self._node_checkbox_checked(node)
                    else Qt.CheckState.Unchecked)

                if item.checkState() != desired:
                    item.setCheckState(desired)
        finally:
            self._tree_sync_depth = max(0, getattr(self, "_tree_sync_depth", 1) - 1)

    def atualizar_item_visibilidade(self, layer_tree_layer):
        """
        Atualiza o checkbox da camada no treeView quando o checkbox do nó
        correspondente muda no QGIS.
        """
        if not isinstance(layer_tree_layer, QgsLayerTreeLayer):
            self.sync_from_qgis_to_treeview()
            return

        model = self.dlg.treeViewListaLinha.model()
        if model is None:
            return

        target_id = layer_tree_layer.layerId()
        desired = (
            Qt.CheckState.Checked
            if self._node_checkbox_checked(layer_tree_layer)
            else Qt.CheckState.Unchecked)

        for row in range(model.rowCount()):
            item = model.item(row)
            if not item:
                continue
            if item.data() != target_id:
                continue

            if item.checkState() != desired:
                self._tree_sync_depth = getattr(self, "_tree_sync_depth", 0) + 1
                try:
                    item.setCheckState(desired)
                finally:
                    self._tree_sync_depth = max(0, getattr(self, "_tree_sync_depth", 1) - 1)
            break
        self.sync_from_qgis_to_treeview()

    def criar_modelo_para_treeview(self):
        """
        Cria e configura o modelo (QStandardItemModel) a ser usado pelo QTreeView.
        """
        self.model = QStandardItemModel()
        self.model.setHorizontalHeaderLabels([self.tr("Lista de Camadas de Linhas")])

        # Captura tanto alterações diretas do item quanto alterações vindas do delegate/view
        self.model.itemChanged.connect(self.on_item_changed)
        self.model.dataChanged.connect(self.on_data_changed)

        self.dlg.treeViewListaLinha.setModel(self.model)
        self.configurar_treeview_header()

    def _aplicar_visibilidade_item_no_qgis(self, item):
        """
        Aplica ao QGIS o estado do checkbox do item do treeView.
        """
        if getattr(self, "_tree_sync_depth", 0) > 0:
            return

        if not item:
            return

        layer_id = item.data()
        if not layer_id:
            return

        root = QgsProject.instance().layerTreeRoot()
        node = root.findLayer(layer_id)
        if not node:
            return

        desired = (item.checkState() == Qt.CheckState.Checked)

        try:
            current = bool(node.itemVisibilityChecked())
        except Exception:
            current = bool(node.isVisible())

        if current == desired:
            return

        node.setItemVisibilityChecked(desired)

        # reforço visual e de sincronização no próximo ciclo da UI
        QTimer.singleShot(0, self.sync_from_qgis_to_treeview)
        try:
            QTimer.singleShot(0, self.iface.mapCanvas().refresh)
        except Exception:
            pass  # nosec B110

    def _aplicar_check_item_no_qgis(self, item):
        """
        Empurra explicitamente o estado atual do checkbox do item do treeView
        para o nó correspondente na árvore de camadas do QGIS.
        """
        if item is None:
            return

        layer_id = item.data()
        if not layer_id:
            return

        root = QgsProject.instance().layerTreeRoot()
        node = root.findLayer(layer_id)
        if node is None:
            return

        desired = (item.checkState() == Qt.CheckState.Checked)

        try:
            current = bool(node.itemVisibilityChecked())
        except Exception:
            try:
                current = bool(node.isVisible())
            except Exception:
                current = None

        if current != desired:
            node.setItemVisibilityChecked(desired)

    def on_treeViewItem_clicked(self, index):
        """
        Ativa a camada correspondente no QGIS e, como fallback,
        sincroniza o estado atual do checkbox do item para a árvore do QGIS.
        """
        if not index.isValid():
            return

        item = index.model().itemFromIndex(index)
        if item is None:
            return

        layer_id = item.data()
        layer = QgsProject.instance().mapLayer(layer_id)

        if layer:
            self.iface.setActiveLayer(layer)

        # Fallback importante para QGIS 4:
        # garante que o estado do checkbox seja aplicado mesmo se itemChanged
        # não disparar de forma consistente neste clique.
        QTimer.singleShot(0, lambda i=item: self._aplicar_check_item_no_qgis(i))

    def on_data_changed(self, topLeft, bottomRight, roles=None):
        """
        (LEGADO) Slot para QStandardItemModel.dataChanged.

        Hoje o UiManager usa model.itemChanged -> on_item_changed, mas este método
        fica aqui para compatibilidade caso algum trecho antigo ainda conecte dataChanged.
        """
        # Evita loop/reentrada: se a mudança veio de sync programático, não propaga de volta ao QGIS
        if getattr(self, "_tree_sync_depth", 0) > 0:
            return

        # Qt6/PyQt6: CheckStateRole fica em Qt.ItemDataRole
        if roles:
            check_role = int(Qt.ItemDataRole.CheckStateRole)
            normalized_roles = {int(r) for r in roles}
            if check_role not in normalized_roles:
                return

        try:
            item = topLeft.model().itemFromIndex(topLeft)
        except Exception:
            return

        if not item:
            return

        layer_id = item.data()
        if not layer_id:
            return

        root = QgsProject.instance().layerTreeRoot()
        node = root.findLayer(layer_id)
        if not node:
            return

        desired = (item.checkState() == Qt.CheckState.Checked)

        try:
            current = bool(node.itemVisibilityChecked())
        except Exception:
            current = bool(node.isVisible())

        if current != desired:
            node.setItemVisibilityChecked(desired)

    def obter_fonte_para_camada(self, layer):
        """
        Determina a fonte apropriada para um item no treeView com base no tipo de provedor de dados da camada associada.

        Parâmetros:
        - layer (QgsMapLayer): A camada cujas propriedades do provedor de dados influenciam a estilização da fonte do item no treeView.

        Funcionalidades:
        - Cria um objeto QFont para definir as propriedades da fonte.
        - Configura a fonte para ser itálica se o provedor de dados da camada for 'memory', indicativo de que a camada é temporária e armazenada apenas na memória.
        - Configura a fonte para ser negrito se o provedor de dados da camada não for 'memory', destacando camadas que são persistentes e possivelmente armazenadas em fontes de dados externas ou permanentes.
        - Retorna o objeto QFont configurado, pronto para ser aplicado ao item representativo da camada no treeView.

        Atribuição no código:
        Essencial para fornecer um feedback visual imediato sobre o tipo de armazenamento das camadas no treeView, facilitando a distinção entre camadas temporárias e permanentes. Esta diferenciação ajuda os usuários a entenderem rapidamente a natureza da camada sem a necessidade de inspeção adicional, melhorando a usabilidade e a eficiência da interface do usuário.
        """
        fonte_item = QFont()
        # Define o estilo da fonte com base no tipo de camada (memória ou não)
        fonte_item.setItalic(layer.dataProvider().name() == 'memory')
        fonte_item.setBold(layer.dataProvider().name() != 'memory')
        return fonte_item

    def on_treeViewItem_doubleClicked(self, index):
        """
        Responde a eventos de duplo clique em um item no treeView, permitindo ao usuário alterar a cor da linha da camada correspondente.

        Parâmetros:
        - index (QModelIndex): O índice do item no modelo do treeView que foi duplamente clicado.

        Funcionalidades:
        - Obtém o ID da camada associada ao item clicado no treeView, permitindo a recuperação da camada correspondente no projeto QGIS.
        - Verifica se a camada existe e, em caso afirmativo, recupera a cor atual da linha da camada usando o método obter_cor_linha.
        - Abre um diálogo de seleção de cor pré-configurado com a cor atual da linha, permitindo ao usuário escolher uma nova cor para a linha da camada.
        - Se o usuário selecionar uma cor válida (isto é, não cancelar o diálogo), aplica a nova cor à linha da camada usando o método aplicar_cor_linha.

        Atribuição no código:
        Proporciona uma interação direta e intuitiva para personalizar a aparência das camadas de linha no projeto QGIS diretamente através da interface do usuário. Este método melhora significativamente a experiência do usuário ao permitir ajustes visuais rápidos e eficientes, facilitando a personalização da representação das camadas no mapa.
        """
        # Obtém o ID da camada a partir do índice
        layer_id = index.model().itemFromIndex(index).data()
        layer = QgsProject.instance().mapLayer(layer_id)
        if layer:
            # Obtém a cor atual da linha da camada
            cor_atual = self.obter_cor_linha(layer)
            # Abre um diálogo de seleção de cor e permite que o usuário escolha uma nova cor
            cor_selecionada = QColorDialog.getColor(cor_atual, self.dlg, self.tr("Escolher Cor da Linha"))
            
            if cor_selecionada.isValid():
                # Aplica a nova cor à linha da camada
                self.aplicar_cor_linha(layer, cor_selecionada)

    def _obter_cor_atributos_linha(self, layer):
        """
        Obtém uma cor representativa a partir dos atributos da camada.

        Camadas DXF importadas pelo plugin utilizam os campos r, g e b
        para definir a cor por feição através de data-defined properties.
        """
        if not isinstance(layer, QgsVectorLayer):
            return QColor()

        campos = {campo.name()
            for campo in layer.fields()}

        # Camadas DXF criadas pelo plugin
        if {"r", "g", "b"}.issubset(campos):
            contagem_cores = Counter()

            for indice, feature in enumerate(layer.getFeatures()):
                try:
                    r = int(round(float(feature["r"])))
                    g = int(round(float(feature["g"])))
                    b = int(round(float(feature["b"])))

                    if (0 <= r <= 255
                        and 0 <= g <= 255
                        and 0 <= b <= 255):
                        contagem_cores[(r, g, b)] += 1

                except (TypeError, ValueError, KeyError):
                    continue

                # Evita percorrer camadas enormes somente para montar o ícone
                if indice >= 499:
                    break

            if contagem_cores:
                rgb, _quantidade = contagem_cores.most_common(1)[0]

                return QColor(
                    rgb[0],
                    rgb[1],
                    rgb[2])

        # Camadas KML/KMZ com cor armazenada em campo
        if "__kml_color" in campos:
            contagem_cores = Counter()

            for indice, feature in enumerate(layer.getFeatures()):
                try:
                    texto_cor = str(feature["__kml_color"]
                        or "").strip()

                    cor = QColor(texto_cor)

                    if cor.isValid():
                        contagem_cores[cor.name(QColor.NameFormat.HexArgb)] += 1

                except (TypeError, ValueError, KeyError):
                    continue

                if indice >= 499:
                    break

            if contagem_cores:
                cor_hex, _quantidade = contagem_cores.most_common(1)[0]
                return QColor(cor_hex)

        return QColor()

    def obter_cor_linha(self, layer):
        """
        Obtém uma cor representativa da camada de linhas.

        Prioridade:
        1. cor definida por atributos r/g/b ou __kml_color;
        2. cor das camadas internas do símbolo;
        3. cor geral do símbolo;
        4. preto como fallback.
        """
        cor_default = QColor(
            Qt.GlobalColor.black)

        if not isinstance(layer, QgsVectorLayer):
            return cor_default

        # DXF e KML podem usar cor dinâmica por feição.
        cor_atributos = self._obter_cor_atributos_linha(
            layer)

        if cor_atributos.isValid():
            return cor_atributos

        renderer = layer.renderer()

        if renderer is None:
            return cor_default

        simbolos = []

        try:
            simbolo = renderer.symbol()

            if simbolo is not None:
                simbolos.append(simbolo)

        except Exception:
            pass  # nosec B110

        if not simbolos:
            try:
                simbolos = [simbolo
                    for simbolo in renderer.symbols(QgsRenderContext())
                    if simbolo is not None]

            except Exception:
                simbolos = []

        if (not simbolos
            and isinstance(renderer, QgsRuleBasedRenderer)):
            def localizar_simbolos(regra):
                encontrados = []

                if regra is None:
                    return encontrados

                try:
                    simbolo_regra = regra.symbol()

                    if simbolo_regra is not None:
                        encontrados.append(simbolo_regra)

                except Exception:
                    pass  # nosec B110

                try:
                    for regra_filha in regra.children():
                        encontrados.extend(localizar_simbolos(regra_filha))

                except Exception:
                    pass  # nosec B110

                return encontrados

            simbolos = localizar_simbolos(
                renderer.rootRule())

        for simbolo in simbolos:
            try:
                for indice in range(simbolo.symbolLayerCount()):
                    symbol_layer = simbolo.symbolLayer(indice)

                    if symbol_layer is None:
                        continue

                    try:
                        stroke_color = getattr( symbol_layer, "strokeColor", None)

                        if callable(stroke_color):
                            cor = QColor(stroke_color())

                            if cor.isValid():
                                return cor

                    except Exception:
                        pass  # nosec B110

                    try:
                        cor = QColor(symbol_layer.color())

                        if cor.isValid():
                            return cor

                    except Exception:
                        pass  # nosec B110

            except Exception:
                pass  # nosec B110

            try:
                cor = QColor(simbolo.color())

                if cor.isValid():
                    return cor

            except Exception:
                pass  # nosec B110

    def aplicar_cor_linha(self, layer, nova_cor):
        """
        Aplica a nova cor à camada, ao mapa, à legenda nativa do QGIS
        e ao indicador do treeView.

        Para camadas DXF com campos r, g e b, atualiza também os
        atributos responsáveis pela cor definida por expressão.
        """
        if (layer is None
            or not isinstance(layer, QgsVectorLayer)
            or not nova_cor.isValid()):
            return

        nova_cor = QColor(nova_cor)

        renderer = layer.renderer()

        if renderer is None:
            return

        nomes_campos = {campo.name()
            for campo in layer.fields()}

        possui_rgb = {"r", "g", "b"}.issubset(nomes_campos)

        # Camadas DXF importadas usam os campos r/g/b para controlar
        # efetivamente a cor desenhada no mapa.
        if possui_rgb:
            idx_r = layer.fields().indexFromName("r")
            idx_g = layer.fields().indexFromName("g")
            idx_b = layer.fields().indexFromName("b")

            alteracoes = {feature.id(): {
                    idx_r: nova_cor.red(),
                    idx_g: nova_cor.green(),
                    idx_b: nova_cor.blue()}
                for feature in layer.getFeatures()}

            if alteracoes:
                provider = layer.dataProvider()

                alterado = False

                try:
                    alterado = provider.changeAttributeValues(alteracoes)
                except Exception:
                    alterado = False

                # Fallback usando o buffer de edição da camada.
                if not alterado:
                    ja_estava_editando = layer.isEditable()
                    iniciou_edicao = False

                    if not ja_estava_editando:
                        iniciou_edicao = layer.startEditing()

                        if not iniciou_edicao:
                            self.mostrar_mensagem(self.tr("Não foi possível iniciar a edição da camada para alterar sua cor."), "Erro")
                            return

                    sucesso_edicao = True

                    for feature_id, valores in alteracoes.items():
                        for indice_campo, valor in valores.items():
                            if not layer.changeAttributeValue(
                                feature_id,
                                indice_campo,
                                valor):
                                sucesso_edicao = False

                    if iniciou_edicao:
                        if sucesso_edicao:
                            sucesso_edicao = layer.commitChanges()
                        else:
                            layer.rollBack()

                    if not sucesso_edicao:
                        self.mostrar_mensagem(self.tr("Não foi possível atualizar os campos de cor da camada."), "Erro")
                        return

        # Atualiza também a cor-base do renderer.
        # Essa é a cor usada na legenda nativa do QGIS.
        if isinstance(renderer, QgsSingleSymbolRenderer):
            simbolo = renderer.symbol()

            if simbolo is not None:
                simbolo.setColor(nova_cor)

                for indice in range(simbolo.symbolLayerCount()):
                    symbol_layer = simbolo.symbolLayer(
                        indice)

                    if symbol_layer is None:
                        continue

                    try:
                        symbol_layer.setColor(nova_cor)
                    except Exception:
                        pass  # nosec B110

            layer.setRenderer(renderer)

        elif isinstance(renderer, QgsCategorizedSymbolRenderer):
            for categoria in renderer.categories():
                simbolo = categoria.symbol()

                if simbolo is not None:
                    simbolo.setColor(nova_cor)

            layer.setRenderer(renderer)

        elif isinstance(renderer, QgsRuleBasedRenderer):
            def alterar_cor_regra(regra):
                if regra is None:
                    return

                simbolo = regra.symbol()

                if simbolo is not None:
                    simbolo.setColor(nova_cor)

                for regra_filha in regra.children():
                    alterar_cor_regra(regra_filha)

            alterar_cor_regra(renderer.rootRule())

            layer.setRenderer(renderer)

        else:
            simbolo = QgsLineSymbol.createSimple({"color": nova_cor.name()})

            layer.setRenderer(QgsSingleSymbolRenderer(simbolo))

        # Atualiza o indicador do treeView personalizado.
        model = self.dlg.treeViewListaLinha.model()

        if model is not None:
            for row in range(model.rowCount()):
                item = model.item(row)

                if not item:
                    continue

                if item.data() != layer.id():
                    continue

                item.setData(nova_cor.name(QColor.NameFormat.HexArgb), Qt.ItemDataRole.UserRole)

                break

        # Atualiza o mapa e a legenda nativa do QGIS.
        layer.triggerRepaint()

        self.iface.layerTreeView().refreshLayerSymbology(
            layer.id())

        self.dlg.treeViewListaLinha.viewport().update()
        self.iface.mapCanvas().refresh()

    def sincronizar_selecao_com_qgis(self, layer):
        """
        Sincroniza a seleção atual no treeView da interface do usuário com a camada ativa no projeto QGIS.

        Parâmetros:
        - layer (QgsMapLayer): A camada que se tornou ativa no QGIS e que deve ser refletida como selecionada no treeView.

        Funcionalidades:
        - Verifica se a camada fornecida é nula, interrompendo a função se for o caso, para evitar erros.
        - Obtém o modelo de dados associado ao treeView, que lista as camadas.
        - Itera sobre todas as linhas (itens) do modelo para encontrar o item correspondente à camada ativa.
        - Verifica se o item existe no modelo e se o ID da camada associada ao item corresponde ao ID da camada ativa.
        - Se um item correspondente for encontrado, obtém o índice desse item no modelo.
        - Define o índice atual no treeView para o índice do item encontrado, efetivamente selecionando o item na interface do usuário.

        Atribuição no código:
        Essencial para manter a consistência entre a camada selecionada na interface do usuário e a camada ativa no projeto QGIS. Facilita a usabilidade e melhora a interação do usuário, garantindo que as mudanças de contexto no QGIS sejam imediatamente refletidas na interface, ajudando o usuário a identificar qual camada está atualmente ativa e sendo manipulada.
        """
        # Verifica se a camada é nula
        if layer is None:
            return
        # Obtém o modelo da árvore de camadas
        model = self.dlg.treeViewListaLinha.model()
        # Itera sobre as linhas do modelo
        for row in range(model.rowCount()):
            item = model.item(row)
            # Verifica se o item existe e se corresponde à camada atual
            if item and item.data() == layer.id():
                index = model.indexFromItem(item)  # Obtém o índice do item
                # Define o índice atual na árvore de camadas como o índice do item
                self.dlg.treeViewListaLinha.setCurrentIndex(index)
                break

    def renomear_camada_selecionada(self):
        """
        Permite ao usuário renomear uma camada selecionada no treeView através de uma caixa de diálogo, garantindo que o nome seja único dentro do projeto.

        Funcionalidades:
        - Obtém os índices selecionados no treeView. Se um índice estiver selecionado, identifica a camada associada ao item selecionado.
        - Se uma camada estiver associada ao item selecionado, exibe uma caixa de diálogo que solicita ao usuário um novo nome para a camada, pré-preenchendo o campo de entrada com o nome atual da camada.
        - Verifica se o usuário confirmou a ação e forneceu um novo nome. Se sim, chama a função `gerar_nome_unico` para ajustar o nome para um formato único dentro do projeto.
        - Define o novo nome para a camada no projeto QGIS e atualiza o texto do item correspondente no treeView para refletir o novo nome.

        Atribuição no código:
        Essencial para a administração eficaz das camadas, permitindo ao usuário personalizar os nomes das camadas de acordo com suas necessidades e garantindo que não haja conflitos de nomeação dentro do projeto. Facilita a organização e a identificação das camadas, melhorando a gestão de dados e a experiência do usuário ao trabalhar com múltiplas camadas.
        """
        selected_indexes = self.dlg.treeViewListaLinha.selectedIndexes()
        if selected_indexes:
            selected_index = selected_indexes[0]
            layer_id = selected_index.model().itemFromIndex(selected_index).data()
            selected_layer = QgsProject.instance().mapLayer(layer_id)
            if selected_layer:
                novo_nome, ok = QInputDialog.getText(
                    self.dlg,
                    self.tr("Renomear Camada"),
                    self.tr("Digite o novo nome da camada:"),
                    text=selected_layer.name())
                if ok and novo_nome:
                    novo_nome = self.gerar_nome_unico(novo_nome, selected_layer.id())
                    selected_layer.setName(novo_nome)
                    selected_index.model().itemFromIndex(selected_index).setText(novo_nome)

    def gerar_nome_unico(self, base_nome, current_layer_id):
        """
        Gera um nome único para uma camada dentro do projeto QGIS, assegurando que não haja conflitos de nomeação com outras camadas existentes.

        Parâmetros:
        - base_nome (str): O nome base proposto para a camada.
        - current_layer_id (str): O ID da camada que está sendo renomeada, usado para excluir seu nome atual da verificação de duplicidade.

        Funcionalidades:
        - Cria um dicionário dos nomes de todas as camadas existentes no projeto QGIS, excluindo a camada que está sendo renomeada, para evitar considerar seu próprio nome como duplicado.
        - Verifica se o nome base já existe entre as camadas. Se não existir, retorna o nome base como um nome válido.
        - Se o nome base já existir, gera variações do nome acrescentando um sufixo numérico (por exemplo, "Nome_1", "Nome_2") até encontrar um nome não utilizado.
        - Retorna o novo nome único gerado.
        """
        existing_names = {layer.name(): layer.id() for layer in QgsProject.instance().mapLayers().values() if layer.id() != current_layer_id}
        if base_nome not in existing_names:
            return base_nome
        else:
            i = 1
            novo_nome = f"{base_nome}_{i}"
            while novo_nome in existing_names:
                i += 1
                novo_nome = f"{base_nome}_{i}"
            return novo_nome

    def mostrar_mensagem(self, texto, tipo, duracao=3, caminho_pasta=None, caminho_arquivos=None):
        """
        Exibe uma mensagem na barra de mensagens do QGIS.

        Para mensagens de sucesso, pode apresentar:
        - botão para abrir a pasta;
        - botão para executar o arquivo;
        - botão para abrir o Google Earth Web quando o arquivo for KML/KMZ.
        """
        bar = self.iface.messageBar()

        if tipo == "Erro":
            bar.pushMessage(self.tr("Erro"), texto, level=Qgis.MessageLevel.Critical, duration=duracao)
            return

        if tipo == "Aviso":
            bar.pushMessage(self.tr("Aviso"), texto, level=Qgis.MessageLevel.Warning, duration=duracao)
            return

        if tipo != "Sucesso":
            bar.pushMessage(self.tr("Info"), texto, level=Qgis.MessageLevel.Info, duration=duracao)
            return

        # Mensagem personalizada de sucesso
        msg = bar.createMessage(self.tr("Sucesso"), texto)

        posicao_botao = 1

        # Botão Abrir Pasta
        if caminho_pasta:
            botao_abrir_pasta = QPushButton(self.tr("Abrir Pasta"))
            botao_abrir_pasta.clicked.connect(
                lambda _checked=False, caminho=caminho_pasta:
                    QDesktopServices.openUrl(
                        QUrl.fromLocalFile(
                            os.path.abspath(os.fspath(caminho)))))

            msg.layout().insertWidget(posicao_botao, botao_abrir_pasta)

            posicao_botao += 1

        # Botão Executar
        if caminho_arquivos:
            botao_executar = QPushButton(self.tr("Executar"))

            botao_executar.clicked.connect(
                lambda _checked=False, caminho=caminho_arquivos:
                    QDesktopServices.openUrl(
                        QUrl.fromLocalFile(
                            os.path.abspath(os.fspath(caminho)))))

            msg.layout().insertWidget(posicao_botao, botao_executar)

            posicao_botao += 1

        # Botão Google Earth Web somente para KML/KMZ
        caminho_earth = None

        if isinstance(caminho_arquivos, str):
            extensao = os.path.splitext(caminho_arquivos)[1].lower()

            if extensao in (".kml", ".kmz"):
                caminho_earth = caminho_arquivos

        if caminho_earth:
            botao_google_earth = QPushButton(self.tr("Abrir Google Earth Web"))

            botao_google_earth.setToolTip(self.tr("Abre o Google Earth Web e copia o caminho do arquivo para a área de transferência."))

            botao_google_earth.clicked.connect(lambda _checked=False, caminho=caminho_earth:
                self.abrir_google_earth_web(caminho))

            msg.layout().insertWidget(posicao_botao, botao_google_earth)

        bar.pushWidget(msg, level=Qgis.MessageLevel.Info, duration=duracao)

    def abrir_google_earth_web(self, caminho_arquivo=None):
        """
        Abre o Google Earth Web e copia o caminho do KML/KMZ
        para a área de transferência.
        """
        if caminho_arquivo:
            try:
                caminho_normalizado = os.path.normpath(caminho_arquivo)

                QGuiApplication.clipboard().setText(caminho_normalizado)

            except Exception:
                pass  # nosec B110

        QDesktopServices.openUrl(QUrl("https://earth.google.com/web/"))

        # Mostra a orientação sem bloquear
        QTimer.singleShot(250,
            lambda: self.iface.messageBar().pushMessage(
                self.tr("Google Earth Web"),
                self.tr("Clique em Novo > Importar arquivo > "
                    "Dispositivo local. O caminho do KML foi copiado."), level=Qgis.MessageLevel.Info, duration=5))


    def salvar_camada_multiplo(self):
        """
        Salva a camada selecionada em múltiplos formatos e exibe UMA mensagem final
        com apenas o botão 'Abrir pasta'.
        """
        # 1) Resolve a camada selecionada pelo ID salvo no Qt.UserRole
        selected_indexes = self.dlg.treeViewListaLinha.selectedIndexes()
        if not selected_indexes:
            self.mostrar_mensagem(self.tr("Selecione uma camada para exportar."), "Erro")
            return
        selected_index = selected_indexes[0]
        item = selected_index.model().itemFromIndex(selected_index)
        layer_id = item.data(Qt.ItemDataRole.UserRole + 1)  # ID da camada
        if not isinstance(layer_id, str):
            self.mostrar_mensagem(self.tr("Falha ao obter ID da camada."), "Erro")
            return

        layer_to_save = QgsProject.instance().mapLayer(layer_id)
        if not layer_to_save or layer_to_save.type() != QgsMapLayer.LayerType.VectorLayer or not layer_to_save.isValid():
            self.mostrar_mensagem(self.tr("Nenhuma camada vetorial válida selecionada."), "Erro")
            return
        if layer_to_save.featureCount() == 0:
            self.mostrar_mensagem(self.tr("Nenhuma feição para exportar."), "Erro")
            return

        # 2) Diálogo de formatos (seu diálogo atual)
        formatos = {
            "DXF": ".dxf",
            "KML": ".kml",
            "GeoJSON": ".geojson",
            "CSV": ".csv",
            "Shapefile": ".shp",
            "TXT": ".txt",
            "Excel": ".xlsx",
            "Geopackage": ".gpkg"}
        dialogo = DialogoSalvarFormatos(formatos, self.dlg)
        if not dialogo.exec():
            return  # cancelado

        if not dialogo.formatos_selecionados:
            self.mostrar_mensagem(self.tr("Nenhum formato selecionado."), "Info")
            return

        # 3) Escolher 1 diretório (usar o padrão nativo aqui é ok; se preferir, faça um seletor não-nativo)
        diretorio = QFileDialog.getExistingDirectory(self.dlg, self.tr("Escolha um diretório para salvar os arquivos"))
        if not diretorio:
            return  # cancelado

        # 4) Exporta todos em silêncio e acumula resultados
        resultados = []  # (ext, caminho_final_ou_None, ok)
        for extensao in dialogo.formatos_selecionados:
            nome_arquivo = os.path.join(diretorio, f"{layer_to_save.name()}{extensao}")
            self.salvar_no_formato_especifico(layer_to_save, extensao, nome_arquivo, silencioso=True, coletor=resultados)

        # 5) Mensagem única com APENAS o botão "Abrir pasta"
        total = len(resultados)
        ok_list   = [r for r in resultados if r[2]]
        fail_list = [r for r in resultados if not r[2]]

        fmt_ok   = ", ".join(sorted({ext.lstrip(".").upper() for ext, _, ok in resultados if ok}))
        fmt_fail = ", ".join(sorted({ext.lstrip(".").upper() for ext, _, ok in resultados if not ok}))

        if not fail_list:
            msg = self.tr("Arquivos salvos com sucesso ({ok}/{total}): {fmt_ok}.").format(ok=len(ok_list), total=total, fmt_ok=fmt_ok)
            self.mostrar_mensagem(msg, "Sucesso", caminho_pasta=diretorio)
        else:
            msg = self.tr("Arquivos salvos ({ok}/{total}).").format(ok=len(ok_list), total=total)
            if fmt_ok:
                msg += " " + self.tr("OK: {fmt_ok}.").format(fmt_ok=fmt_ok)
            if fmt_fail:
                msg += " " + self.tr("Falharam: {fmt_fail}.").format(fmt_fail=fmt_fail)
            self.mostrar_mensagem(msg, "Info", caminho_pasta=diretorio)

    def salvar_no_formato_especifico(self, layer, extensao, nome_arquivo=None, *, silencioso=False, coletor=None):
        """
        Exporta uma camada QGIS para um formato específico (ex.: SHP, KML, DXF, TXT, XLSX).

        - Garante extensão correta no nome do arquivo;
        - Evita sobrescrita gerando nomes incrementais (_1, _2...);
        - Usa diálogos de "Salvar como" quando não há caminho informado;
        - Atualiza o último diretório salvo (`self.ultimo_caminho_salvo`);
        - Permite execução silenciosa (sem mensagens de sucesso/erro);
        - Opcionalmente registra resultados em `coletor` [(extensão, caminho, ok), ...].

        Retorna:
            bool: True se a camada foi salva com sucesso, False caso contrário.
        """
        # Validação básica
        if layer is None or not getattr(layer, "isValid", lambda: False)():
            if coletor is not None:
                coletor.append((extensao, None, False))
            if not silencioso:
                self.mostrar_mensagem(self.tr("Camada inválida para salvar."), "Erro")
            return False

        # Normaliza extensão
        ext = (extensao or "").strip().lower()
        if not ext:
            if coletor is not None:
                coletor.append((extensao, None, False))
            if not silencioso:
                self.mostrar_mensagem(self.tr("Extensão não informada."), "Erro")
            return False
        if not ext.startswith("."):
            ext = f".{ext}"

        # Filtro/driver
        tipos_de_arquivo = {
            ".dxf": ("DXF Files (*.dxf)", "DXF"),
            ".kml": ("KML Files (*.kml)", "KML"),
            ".shp": ("Shapefile Files (*.shp)", "ESRI Shapefile"),
            ".txt": ("Text Files (*.txt)", "TXT"),
            ".csv": ("CSV Files (*.csv)", "CSV"),
            ".geojson": ("GeoJSON Files (*.geojson)", "GeoJSON"),
            ".gpkg": ("Geopackage Files (*.gpkg)", "GPKG"),
            ".xlsx": ("Excel Files (*.xlsx)", "XLSX")}
        filtro, driver_name = tipos_de_arquivo.get(ext, (None, None))
        if not filtro:
            if coletor is not None:
                coletor.append((ext, None, False))
            if not silencioso:
                self.mostrar_mensagem(self.tr("Extensão não suportada: {ext}").format(ext=ext), "Erro")
            return False

        # Se veio diretório, vira arquivo dentro dele
        if nome_arquivo and os.path.isdir(nome_arquivo):
            nome_arquivo = os.path.join(nome_arquivo, f"{layer.name()}{ext}")

        # Se não veio arquivo, pergunta por um
        if not nome_arquivo:
            base_dir = getattr(self, "ultimo_caminho_salvo", "") or os.path.expanduser("~")
            sugestao = os.path.join(base_dir, f"{layer.name()}{ext}")
            nome_arquivo = self.escolher_local_para_salvar(sugestao, filtro)
            if not nome_arquivo:
                if coletor is not None:
                    coletor.append((ext, None, False))
                return False

        # Garante extensão
        if not nome_arquivo.lower().endswith(ext):
            nome_arquivo = f"{nome_arquivo}{ext}"

        # Evita overwrite
        base_sem_ext, _ = os.path.splitext(nome_arquivo)
        final_path = nome_arquivo
        c = 1
        while os.path.exists(final_path):
            final_path = f"{base_sem_ext}_{c}{ext}"
            c += 1

        # Atualiza último diretório
        try:
            ultimo_dir = os.path.dirname(final_path)
            if ultimo_dir:
                self.ultimo_caminho_salvo = ultimo_dir
        except Exception:
            pass  # nosec B110

        # Salvar (silencioso)
        ok = False
        try:
            if ext == ".txt":
                ok = self.salvar_como_txt(layer, final_path, silencioso=True)
            elif ext == ".xlsx":
                ok = self.salvar_como_xlsx(layer, final_path, silencioso=True)
            else:
                ok = self.salvar_camada(layer, final_path, driverName=driver_name, silencioso=True)
        except Exception as e:
            ok = False

        # Reporta no coletor
        if coletor is not None:
            coletor.append((ext, final_path if ok else None, ok))

        # Se não for silencioso, mostra a mensagem individual
        if not silencioso:
            if ok:
                self.mostrar_mensagem(self.tr("Arquivo salvo com sucesso ({ext}).").format(ext=ext.lstrip('.').upper()), "Sucesso", caminho_pasta=os.path.dirname(final_path), caminho_arquivos=final_path)
            else:
                self.mostrar_mensagem(self.tr("Não foi possível salvar ({ext}).").format(ext=ext.lstrip('.').upper()), "Erro")

        return ok

    def salvar_como_txt(self, layer, fileName, silencioso=True):
        """
        Exporta os atributos de uma camada vetorial para um arquivo TXT (tabulado).

        Funcionalidades:
        - Exporta apenas os campos da tabela de atributos (sem X/Y calculados).
        - Escreve a primeira linha como cabeçalho.
        - Salva cada feição como uma linha de valores separados por tabulação.
        - Retorna True em caso de sucesso, False em caso de falha.
        """
        try:
            # Obtém nomes dos campos da tabela de atributos
            fields = [f.name() for f in layer.fields()]

            # Abre arquivo TXT para escrita com delimitador de tabulação
            with open(fileName, "w", encoding="utf-8", newline="") as f:
                writer = csv.writer(f, delimiter="\t")

                # Escreve cabeçalho (nomes dos campos)
                writer.writerow(fields)

                # Escreve cada feição (apenas atributos)
                for feat in layer.getFeatures():
                    writer.writerow(feat.attributes())

            return True
        except Exception:
            return False

    def salvar_como_xlsx(self, layer, file_path, silencioso=True):
        """
        Exporta apenas a TABELA DE ATRIBUTOS de uma camada para XLSX,
        usando exclusivamente o xlsxwriter.
        """
        if layer is None or layer.type() != QgsMapLayer.LayerType.VectorLayer or not layer.isValid():
            return False

        fields = [f.name() for f in layer.fields()]  # cabeçalho = nomes dos atributos

        try:
            import xlsxwriter
            wb = xlsxwriter.Workbook(file_path)
            ws = wb.add_worksheet("dados")

            # Cabeçalho
            for c, h in enumerate(fields):
                ws.write(0, c, h)

            # Dados
            r = 1
            for feat in layer.getFeatures():
                for c, v in enumerate(feat.attributes()):
                    ws.write(r, c, v)
                r += 1

            wb.close()
            return True
        except Exception:
            return False

    def salvar_camada(self, layer, fileName, driverName, silencioso=True):
        """
        Salva uma camada vetorial, preservando UTF-8 e a precisão
        dos campos numéricos no Shapefile.
        """
        driver = (driverName or "").upper()

        options = QgsVectorFileWriter.SaveVectorOptions()
        options.driverName = driver
        options.fileEncoding = "UTF-8"
        options.onlySelectedFeatures = False

        lyr_to_write = layer

        # Mantém o conversor vivo até o término da exportação.
        conversor_precisao = None

        if driver == "KML":
            try:
                target = QgsCoordinateReferenceSystem("EPSG:4326")

                if layer.crs().authid() != target.authid():
                    resultado = processing.run(
                        "native:reprojectlayer",
                        {"INPUT": layer,
                            "TARGET_CRS": target,
                            "OUTPUT": "memory:"})
                    lyr_to_write = resultado["OUTPUT"]

            except Exception:
                return False

            options.symbologyExport = (
                QgsVectorFileWriter.SymbologyExport.FeatureSymbology)

        elif driver == "CSV":
            if (lyr_to_write.geometryType()
                == QgsWkbTypes.GeometryType.PointGeometry):
                options.layerOptions = [
                    "GEOMETRY=AS_XY",
                    "CREATE_CSVT=YES"]
            else:
                # Linhas e polígonos são exportados como WKT.
                options.layerOptions = [
                    "GEOMETRY=AS_WKT",
                    "CREATE_CSVT=YES"]

        elif driver == "ESRI SHAPEFILE":
            options.fileEncoding = "UTF-8"
            options.layerOptions = ["ENCODING=UTF-8"]

            conversor_precisao = (
                self._configurar_precisao_shapefile(
                    lyr_to_write,
                    options))

        elif driver == "DXF":
            options.skipAttributeCreation = True

        elif driver == "GEOJSON":
            options.layerOptions = [
                "COORDINATE_PRECISION=8"]

        elif driver == "GPKG":
            options.layerOptions = [
                "SPATIAL_INDEX=YES"]

        try:
            error, _ = QgsVectorFileWriter.writeAsVectorFormat(
                lyr_to_write,
                fileName,
                options)

            if error != QgsVectorFileWriter.WriterError.NoError:
                return False

            if driver == "ESRI SHAPEFILE":
                caminho_cpg = (
                    os.path.splitext(fileName)[0] + ".cpg")

                try:
                    with open(
                        caminho_cpg,
                        "w",
                        encoding="ascii"
                    ) as arquivo_cpg:
                        arquivo_cpg.write("UTF-8")
                except OSError:
                    pass  # nosec B110

            if (driver == "KML"
                and hasattr(
                    self,
                    "modificar_kml_para_tessellation")):
                try:
                    self.modificar_kml_para_tessellation(fileName)
                except Exception:
                    pass  # nosec B110

            return True

        except Exception:
            return False

    def salvar_camada_permanente(self):
        """
        Salva a camada de linhas selecionada como Shapefile,
        preservando estilo, etiquetas, UTF-8 e precisão numérica.
        """
        selected_indexes = (self.dlg.treeViewListaLinha.selectedIndexes())

        if not selected_indexes:
            self.mostrar_mensagem(self.tr("Selecione uma camada."), "Aviso")
            return

        idx = next(
            (i for i in selected_indexes
                if i.column() == 0),
            selected_indexes[0])

        item = idx.model().itemFromIndex(idx)

        layer_id = item.data(
            Qt.ItemDataRole.UserRole + 1)

        if not isinstance(layer_id, str):
            layer_id = item.data()

        if not isinstance(layer_id, str):
            self.mostrar_mensagem(self.tr("Camada selecionada inválida."), "Erro")
            return

        layer_to_save = QgsProject.instance().mapLayer(layer_id)

        if (not layer_to_save
            or not layer_to_save.isValid()):
            self.mostrar_mensagem(self.tr("Camada não encontrada ou inválida."), "Erro")
            return

        if (layer_to_save.geometryType()
            != QgsWkbTypes.GeometryType.LineGeometry):
            self.mostrar_mensagem(self.tr("A camada selecionada não é uma camada de linhas."), "Aviso")
            return

        # Guarda os dados antes da exportação. O objeto original
        # pode ser removido ou substituído durante o processo.
        nome_camada_original = layer_to_save.name()

        is_temporary = (
            layer_to_save.dataProvider().name()
            == "memory")

        labels_enabled = layer_to_save.labelsEnabled()
        cor_atual = self.obter_cor_linha(layer_to_save)

        renderer = (
            layer_to_save.renderer().clone()
            if layer_to_save.renderer()
            else None)

        etiquetas = (
            layer_to_save.labeling().clone()
            if layer_to_save.labeling()
            else None)

        if layer_to_save.isEditable():
            try:
                layer_to_save.commitChanges()
            except Exception:
                pass  # nosec B110

        base_dir = (
            getattr(self, "ultimo_caminho_salvo", "")
            or os.path.expanduser("~"))

        sugestao = os.path.join(
            base_dir,
            f"{nome_camada_original}.shp")

        nome_arquivo = self.escolher_local_para_salvar(
            sugestao,
            "ESRI Shapefile Files (*.shp)")

        if not nome_arquivo:
            return

        if not nome_arquivo.lower().endswith(".shp"):
            nome_arquivo += ".shp"

        # O nome exibido no grupo será igual ao arquivo salvo.
        nome_camada_salva = os.path.splitext(
            os.path.basename(nome_arquivo)
        )[0]

        pasta = os.path.dirname(nome_arquivo)

        if pasta:
            self.ultimo_caminho_salvo = pasta

        start = time.time()

        if not self.salvar_camada(
            layer_to_save,
            nome_arquivo,
            "ESRI Shapefile"):
            self.mostrar_mensagem(self.tr("Falha ao salvar a camada no formato Shapefile."), "Erro")
            return

        # Não acessar layer_to_save abaixo deste ponto.
        new_layer = QgsVectorLayer(
            nome_arquivo,
            nome_camada_salva,
            "ogr")

        if not new_layer.isValid():
            self.mostrar_mensagem(self.tr("Falha ao carregar a nova camada."), "Erro")
            return

        try:
            new_layer.setProviderEncoding("UTF-8")
        except (AttributeError, TypeError):
            pass  # nosec B110

        if renderer:
            new_layer.setRenderer(renderer)

        if etiquetas:
            new_layer.setLabeling(etiquetas)
            new_layer.setLabelsEnabled(labels_enabled)

        self.tratar_linhas(new_layer)

        QgsProject.instance().addMapLayer(new_layer, False)

        root = QgsProject.instance().layerTreeRoot()

        grupo = (root.findGroup(self.tr("Camadas Salvas"))
            or root.addGroup(self.tr("Camadas Salvas")))

        grupo.addLayer(new_layer)

        if (is_temporary
            and QgsProject.instance().mapLayer(layer_id)):
            QgsProject.instance().removeMapLayer(layer_id)

        if cor_atual is not None:
            self.aplicar_cor_linha(new_layer, cor_atual)

        try:
            new_layer.startEditing()
        except Exception:
            pass  # nosec B110

        elapsed = time.time() - start

        self.mostrar_mensagem(self.tr("Camada salva em {elapsed:.2f} s.").format(elapsed=elapsed), "Sucesso", caminho_pasta=pasta)

    def _configurar_precisao_shapefile(self, layer, options):
        """
        Detecta a maior quantidade de casas decimais significativa
        de cada campo e aplica essa precisão ao Shapefile.
        """
        precisoes = {}
        tipos_decimais = {QMetaType.Type.Double, QMetaType.Type.Float}

        for indice, campo in enumerate(layer.fields()):
            if campo.type() not in tipos_decimais:
                continue

            maior_precisao = 0

            for feature in layer.getFeatures():
                valor = feature.attribute(indice)

                if valor is None:
                    continue

                try:
                    numero = float(valor)

                    if not math.isfinite(numero):
                        continue
                except (TypeError, ValueError):
                    continue

                # Tolera pequenos resíduos internos de números Double.
                tolerancia = max(1e-9, math.ulp(numero) * 16)

                casas_valor = 10

                for casas in range(11):
                    if abs(numero - round(numero, casas)) <= tolerancia:
                        casas_valor = casas
                        break

                maior_precisao = max(maior_precisao, casas_valor)

            precisoes[indice] = maior_precisao

        class ConversorPrecisao(QgsVectorFileWriter.FieldValueConverter):
            def __init__(self, campos, precisoes_campos):
                super().__init__()
                self.campos = QgsFields(campos)
                self.precisoes = dict(precisoes_campos)

            def fieldDefinition(self, campo):
                novo_campo = QgsField(campo)
                indice = self.campos.indexOf(campo.name())

                if indice in self.precisoes:
                    precisao = self.precisoes[indice]
                    novo_campo.setPrecision(precisao)

                    # Garante largura suficiente no DBF.
                    largura = novo_campo.length()

                    if largura <= 0:
                        largura = 20

                    novo_campo.setLength(max(largura, precisao + 12))

                return novo_campo

            def convert(self, indice, valor):
                if indice not in self.precisoes:
                    return valor

                if valor is None:
                    return valor

                try:
                    return round(
                        float(valor), self.precisoes[indice])
                except (TypeError, ValueError):
                    return valor

            def clone(self):
                return ConversorPrecisao(self.campos, self.precisoes)

        conversor = ConversorPrecisao(layer.fields(), precisoes)

        options.fieldValueConverter = conversor

        # Retorna para manter o objeto vivo durante a exportação.
        return conversor

    def _selecionar_formato_salvamento(self, parent=None):
        """
        Mostra um combo simples para o usuário escolher o FORMATO de saída.
        Retorna a extensão escolhida (ex.: ".gpkg") ou None se cancelar.
        """
        parent = parent or getattr(self, "dlg", None) or self.iface.mainWindow()

        opcoes = [
            ("GeoPackage (.gpkg)", ".gpkg"),
            ("Shapefile (.shp)", ".shp"),
            ("GeoJSON (.geojson)", ".geojson"),
            ("KML (.kml)", ".kml"),
            ("DXF (.dxf)", ".dxf"),
            ("CSV (.csv)", ".csv"),
            ("TXT (.txt)", ".txt"),
            ("Excel (.xlsx)", ".xlsx")]
        labels = [lbl for (lbl, _) in opcoes]
        mapa = {lbl: ext for (lbl, ext) in opcoes}

        label, ok = QInputDialog.getItem(parent, self.tr("Salvar antes de remover"), self.tr("Formato de arquivo:"), labels, 0, False)
        if not ok or not label:
            return None
        return mapa.get(label)

    def remover_camada_selecionada(self):
        """
        Remove a camada selecionada no treeView após verificar o estado de edição e as mudanças pendentes.
        Se houver alterações não salvas, pergunta e permite escolher o FORMATO para salvar
        usando salvar_no_formato_especifico(...).
        """
        # Índices selecionados (use a 1ª coluna se possível)
        selected_indexes = self.dlg.treeViewListaLinha.selectedIndexes()
        if not selected_indexes:
            self.mostrar_mensagem(self.tr("Selecione uma camada."), "Aviso")
            return
        idx = next((i for i in selected_indexes if i.column() == 0), selected_indexes[0])

        # Resolve a camada
        item = idx.model().itemFromIndex(idx)
        layer_id = item.data(Qt.ItemDataRole.UserRole + 1)
        if not isinstance(layer_id, str):
            self.mostrar_mensagem(self.tr("Camada não encontrada (ID inválido)."), "Erro")
            return

        layer_to_remove = QgsProject.instance().mapLayer(layer_id)
        if not layer_to_remove:
            self.mostrar_mensagem(self.tr("Camada não encontrada."), "Erro")
            return

        # Se tem edição pendente, pergunta
        if layer_to_remove.isEditable() and layer_to_remove.isModified():
            resposta = QMessageBox.question(self.dlg, self.tr("Confirmar Remoção"), self.tr("Existem alterações não salvas. Deseja salvar antes de remover?"), QMessageBox.StandardButton.Yes | QMessageBox.StandardButton.No | QMessageBox.StandardButton.Cancel, QMessageBox.StandardButton.Yes)

            if resposta == QMessageBox.StandardButton.Yes:
                # Escolhe o FORMATO
                ext = self._selecionar_formato_salvamento(parent=self.dlg)
                if not ext:
                    return  # usuário cancelou a escolha do formato

                # Usa diretamente a sua função pronta (abre o 'Salvar como...' e mostra mensagem)
                ok = self.salvar_no_formato_especifico(layer_to_remove, ext, nome_arquivo=None, silencioso=False)
                if not ok:
                    return  # cancelado ou falhou ao salvar

                # Fecha a edição e confirma alterações
                try:
                    if layer_to_remove.isEditable():
                        layer_to_remove.commitChanges()
                except Exception:
                    pass  # nosec B110

            elif resposta == QMessageBox.StandardButton.No:
                # Descarta alterações
                try:
                    layer_to_remove.rollBack()
                except Exception:
                    pass  # nosec B110
            else:
                return  # Cancel

        # Remove a camada do projeto
        QgsProject.instance().removeMapLayer(layer_id)

        # Limpeza e UI
        try:
            del layer_to_remove
            gc.collect()
        except Exception:
            pass  # nosec B110

        self.atualizar_treeView_lista_linha()
        self.iface.mapCanvas().refresh()

    def _calc_next_id(self, layer, *, exclude_fid=None) -> int:
        """
        Calcula o próximo ID disponível (max(ID)+1) varrendo as feições da camada.
        exclude_fid: ignora uma feição específica (útil para não considerar a recém-criada).
        """
        idx_id = layer.fields().indexOf("ID")
        if idx_id == -1:
            return 1

        max_id = 0
        for f in layer.getFeatures():
            if exclude_fid is not None and f.id() == exclude_fid:
                continue
            try:
                v = f["ID"]
                if v is None or str(v).strip() == "":
                    continue
                iv = int(float(v))  # aceita 2.0, 3.00 etc.
                if iv > max_id:
                    max_id = iv
            except Exception:  # nosec B112
                continue

        return max_id + 1

    def _on_ponto_feature_added(self, layer, fid):
        """
        Slot para quando uma feição é adicionada na camada de pontos.

        - Garante que o campo ID não fique duplicado (caso de Copiar/Mover feições).
        - Se ID vier vazio ou repetido, sobrescreve com max(ID)+1.
        - Atualiza X/Y/DMS da feição recém-criada.
        """
        try:
            idx_id = layer.fields().indexOf("ID")
            if idx_id != -1:
                feat = layer.getFeature(fid)
                if feat and feat.isValid():
                    # valor atual do ID (pode vir copiado)
                    cur = feat["ID"]

                    # tenta converter para inteiro
                    cur_int = None
                    try:
                        if cur is not None and str(cur).strip() != "":
                            cur_int = int(float(cur))
                    except Exception:
                        cur_int = None

                    # detecta duplicidade (existe outra feição com mesmo ID?)
                    duplicado = False
                    if cur_int is not None:
                        for f in layer.getFeatures():
                            if f.id() == fid:
                                continue
                            try:
                                v = f["ID"]
                                if v is None or str(v).strip() == "":
                                    continue
                                if int(float(v)) == cur_int:
                                    duplicado = True
                                    break
                            except Exception:  # nosec B112
                                continue

                    # se vier vazio ou duplicado, força novo ID
                    if cur_int is None or duplicado:
                        novo_id = self._calc_next_id(layer, exclude_fid=fid)

                        # garante edição ativa (normalmente já está, mas por segurança)
                        if not layer.isEditable():
                            layer.startEditing()

                        layer.changeAttributeValue(fid, idx_id, int(novo_id))
        except Exception:
            pass  # nosec B110

        # Mantém o comportamento atual: atualizar X/Y/DMS ao adicionar
        try:
            self.atualizar_comprimento_linha(layer, fid)
        except Exception:
            pass  # nosec B110

    def tratar_linhas(self, new_layer):
        """
        Configura sinais e comportamentos personalizados para uma nova camada de linhas.

        Funcionalidades:
        - Conecta sinais para atualizar automaticamente o comprimento das linhas.
        - Configura o campo 'ID' para ser atribuído automaticamente via expressão.
        - Oculta todos os campos exceto o campo 'ID' na interface da camada.
        - Remove o formulário de atributos ao adicionar feições.
        - Atualiza o campo 'Comprimento' para todas as feições existentes.
        """
        # Alias traduzido, mantendo "Comprimento" como nome interno.
        self._aplicar_alias_comprimento(new_layer)

        # Feature adicionada: corrige ID (se duplicado) e atualiza X/Y/DMS
        new_layer.featureAdded.connect(lambda fid, lyr=new_layer: self._on_ponto_feature_added(lyr, fid))

        # Geometria mudou: só atualiza X/Y/DMS
        new_layer.geometryChanged.connect(lambda fid, _g, lyr=new_layer: self.atualizar_comprimento_linha(lyr, fid))

        # ID automático
        idx_id = new_layer.fields().indexOf("ID")
        if idx_id != -1:
            new_layer.setDefaultValueDefinition(
                idx_id, QgsDefaultValue('coalesce(maximum("ID"),0)+1'))
            new_layer.setEditorWidgetSetup(idx_id, QgsEditorWidgetSetup("Hidden", {}))

        # Oculta demais campos
        for i in range(new_layer.fields().count()):
            if i != idx_id:
                new_layer.setEditorWidgetSetup(i, QgsEditorWidgetSetup("Hidden", {}))

        # Suprime pop-up do formulário
        cfg = new_layer.editFormConfig()               # obtém configuração atual
        cfg.setSuppress(QgsEditFormConfig.FeatureFormSuppress.SuppressOn)  # liga supressão
        new_layer.setEditFormConfig(cfg)               # grava de volta na camada

        # Atualiza 'Comprimento' existentes (inclui SHP = "Compriment")
        idx_comp = new_layer.fields().indexOf("Comprimento")
        if idx_comp == -1:
            idx_comp = new_layer.fields().indexOf("Compriment")  # shapefile (10 chars)

        if idx_comp != -1:
            new_layer.startEditing()
            for f in new_layer.getFeatures():
                self.atualizar_comprimento_linha(new_layer, f.id())
            new_layer.commitChanges()

    def atualizar_comprimento_linha(self, camada: QgsVectorLayer, fid: int):
        """
        Atualiza o valor do campo 'Comprimento' (ou 'Compriment' para shapefile) com o comprimento da geometria
        de uma feição específica, sempre que essa feição é adicionada ou modificada na camada.
        """
        # Tenta encontrar o índice do campo 'Comprimento' (nome completo)
        idx = camada.fields().indexOf("Comprimento")
        # Se não existir, tenta o nome truncado 'Compriment'
        if idx == -1:
            idx = camada.fields().indexOf("Compriment")
        # Se ainda não existir, não faz nada
        if idx == -1:
            return

        # Obtém a feição pelo seu ID
        feature = camada.getFeature(fid)

        # Se a feição tem geometria válida, calcula o comprimento
        if feature.geometry():
            # Usa medição geográfica se necessário
            medida = QgsDistanceArea()
            if camada.crs().isGeographic():
                medida.setSourceCrs(camada.crs(), QgsProject.instance().transformContext())
                medida.setEllipsoid(QgsProject.instance().crs().ellipsoidAcronym())
                comp = round(medida.measureLength(feature.geometry()), 3)
            else:
                comp = round(feature.geometry().length(), 3)
            # Atualiza o valor do campo com o comprimento calculado
            camada.changeAttributeValue(fid, idx, comp)

    def escolher_local_para_salvar(self, nome_padrao, tipo_arquivo):
        """
        Salva uma camada especificada para um arquivo externo usando o formato especificado pelo driverName.

        Parâmetros:
        - layer (QgsVectorLayer): A camada do QGIS que será salva.
        - fileName (str): O caminho completo do arquivo onde a camada será salva.
        - driverName (str): O nome do driver que define o formato de arquivo (por exemplo, "DXF", "KML").

        Funcionalidades:
        - Configura as opções de salvamento adequadas para o formato especificado, como codificação de arquivo e tratamento de simbologia.
        - Aplica configurações específicas para formatos como KML e DXF, adaptando o processo de salvamento às particularidades desses formatos.
        - Executa a operação de salvamento e verifica o resultado. Se bem-sucedido, exibe uma mensagem de sucesso. Caso contrário, exibe uma mensagem de erro detalhando o problema.
        - Para KML, realiza modificações adicionais no arquivo salvo para garantir a adequação às necessidades específicas (como tessellation).

        Atribuição no código:
        Facilita a exportação de camadas para diversos formatos, permitindo a utilização dos dados em outros softwares ou para fins de arquivamento e compartilhamento. A função é crucial para a interoperabilidade e gerenciamento eficaz dos dados geoespaciais, adaptando a camada às especificações requeridas pelos diferentes formatos de arquivo e garantindo que os dados sejam exportados corretamente.
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
            self.dlg,
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

    def _adicionar_arquivo_por_caminho(self, file_path: str) -> bool:
        """Adiciona um arquivo ao projeto usando o mesmo fluxo do botão, sem abrir QFileDialog."""
        if not file_path:
            return False

        layer_name = os.path.splitext(os.path.basename(file_path))[0]
        ext = os.path.splitext(file_path)[1].lower()

        start_time = time.time()

        layers_to_add = []
        text_layer = None  # DXF (opcional)

        if ext == ".dxf":
            line_layer, text_layer = self._processar_dxf(file_path, layer_name)
            if line_layer:
                layers_to_add.append(line_layer)
            if text_layer:
                layers_to_add.append(text_layer)

        elif ext in (".kml", ".kmz"):
            layers_to_add = self._processar_kml_kmz(file_path, layer_name) or []
            if not layers_to_add:
                return False

        else:
            origem = QgsVectorLayer(file_path, layer_name, "ogr")
            if not origem.isValid():
                self.mostrar_mensagem(self.tr("Falha ao carregar o arquivo vetorial."), "Erro")
                return False

            mem = self._copiar_para_memoria(origem, layer_name)
            del origem

            if mem and mem.isValid():
                layers_to_add = [mem]
            else:
                return False

        # adiciona ao projeto (KML/KMZ com várias camadas vai em grupo)
        root = QgsProject.instance().layerTreeRoot()
        group = None
        if ext in (".kml", ".kmz") and len(layers_to_add) > 1:
            group = root.addGroup(layer_name)

        for lyr in layers_to_add:
            if not lyr or not lyr.isValid():
                continue

            if group:
                QgsProject.instance().addMapLayer(lyr, False)
                group.addLayer(lyr)
                node = root.findLayer(lyr.id())
            else:
                QgsProject.instance().addMapLayer(lyr)
                node = root.findLayer(lyr.id())

            if node:
                node.setItemVisibilityChecked(True)

        elapsed = time.time() - start_time
        tempo_formatado = "{:.1f}s".format(elapsed) if elapsed < 60 else "{:.0f}min {:.1f}s".format(elapsed // 60, elapsed % 60)

        self.mostrar_mensagem(self.tr("Camadas de '{layer_name}' adicionadas com sucesso em {tempo_formatado}.").format(layer_name=layer_name, tempo_formatado=tempo_formatado), "Sucesso")
        self.atualizar_treeView_lista_linha()
        return True

    def abrir_adicionar_arquivo(self):
        """
        Abre o diálogo para selecionar e adicionar um arquivo de linhas.

        Os nomes dos formatos são traduzidos, mas os padrões das extensões
        permanecem fixos para evitar alterações indevidas no Qt Linguist.
        """
        file_filter = ";;".join([
            f"{self.tr('Todos os formatos suportados')} "
            "(*.dxf *.DXF *.kml *.KML *.kmz *.KMZ "
            "*.shp *.SHP *.geojson *.GEOJSON *.gpkg *.GPKG)",

            f"{self.tr('Arquivos DXF')} (*.dxf *.DXF)",
            f"{self.tr('Arquivos KML')} (*.kml *.KML)",
            f"{self.tr('Arquivos KMZ')} (*.kmz *.KMZ)",
            f"{self.tr('Arquivos Shapefile')} (*.shp *.SHP)",
            f"{self.tr('Arquivos GeoJSON')} (*.geojson *.GEOJSON)",
            f"{self.tr('Arquivos GeoPackage')} (*.gpkg *.GPKG)",
            f"{self.tr('Todos os arquivos')} (*.*)"])

        file_path, _ = QFileDialog.getOpenFileName(self.dlg, self.tr("Abrir Arquivo de Linhas"), "", file_filter)

        if not file_path:
            return

        try:
            ok = self._adicionar_arquivo_por_caminho(file_path)

            if not ok:
                self.mostrar_mensagem(self.tr(
                        "Nenhuma feição de linha encontrada "
                        "ou o arquivo não pôde ser carregado."), "Aviso")

        except Exception as e:
            self.mostrar_mensagem(self.tr("Erro ao adicionar arquivo: {error}").format(error=str(e)), "Erro")

    def abrir_tabela_atributos(self):
        """
        Abre o diálogo Gerenciador de Tabelas para a camada selecionada no treeView.
        """
        selected_indexes = self.dlg.treeViewListaLinha.selectedIndexes()
        if not selected_indexes:
            return

        selected_index = selected_indexes[0]
        layer_id = selected_index.model().itemFromIndex(selected_index).data()
        layer = QgsProject.instance().mapLayer(layer_id)
        if not layer:
            return

        # Define a camada ativa no QGIS
        try:
            self.iface.setActiveLayer(layer)
        except Exception:
            pass  # nosec B110

        # Abre/reaproveita o diálogo já controlado pelo plugin principal
        self.plugin.run_tabelas()

        dlg_tabelas = getattr(self.plugin, "tabelas_dlg", None)
        if dlg_tabelas is None:
            return

        # Tenta sincronizar o tipo geométrico e a camada selecionada no combo
        try:
            geom_type = layer.geometryType()

            if geom_type == QgsWkbTypes.GeometryType.LineGeometry:
                dlg_tabelas.radioButtonLinha.setChecked(True)
            elif geom_type == QgsWkbTypes.GeometryType.PolygonGeometry:
                dlg_tabelas.radioButtonPoligono.setChecked(True)
            elif geom_type == QgsWkbTypes.GeometryType.PointGeometry:
                dlg_tabelas.radioButtonPonto.setChecked(True)

            dlg_tabelas.update_combo_box_item()

            for i in range(dlg_tabelas.comboBoxCamada.count()):
                if dlg_tabelas.comboBoxCamada.itemData(i) == layer.id():
                    dlg_tabelas.comboBoxCamada.setCurrentIndex(i)
                    break

            dlg_tabelas.raise_()
            dlg_tabelas.activateWindow()

        except Exception:
            pass  # nosec B110

    def obter_cor_rotulo_kml(self, layer):
        """
        Obtém a cor dos rótulos de uma camada em formato adequado para uso em arquivos KML, considerando a configuração de visibilidade e estilização dos rótulos.

        Parâmetros:
        - layer (QgsVectorLayer): A camada do QGIS de onde as configurações de cor do rótulo serão extraídas.

        Funcionalidades:
        - Verifica se os rótulos estão habilitados para a camada. Se não estiverem, retorna uma cor padrão (branco).
        - Obtém as configurações de formatação do rótulo, que incluem detalhes sobre a cor do texto.
        - Extrai a cor do texto dessas configurações e a converte para o formato de cor KML (AABBGGRR), que organiza os canais de cor de forma diferente do padrão RGB usado em muitas outras aplicações.
        - Formata a cor convertida em um valor hexadecimal de 8 dígitos, adequado para uso direto em arquivos KML.

        Atribuição no código:
        Essencial para garantir que a visualização de rótulos em KML reflita as configurações definidas no QGIS, proporcionando consistência visual quando os dados são exportados para visualizações em plataformas que suportam KML, como o Google Earth. Facilita a personalização e o detalhamento na representação de rótulos, melhorando a acessibilidade e a compreensão das informações geográficas.
        """
        if layer.labelsEnabled(): # Verifica se os rótulos estão habilitados para a camada
            text_format = layer.labeling().settings().format() # Obtém as configurações de formatação do rótulo
            cor_texto = text_format.color() # Extrai a cor do texto das configurações de formatação
            # Converte a cor do Qt para o formato de cor KML (AABBGGRR)
            cor_kml = cor_texto.alpha() << 24 | cor_texto.blue() << 16 | cor_texto.green() << 8 | cor_texto.red()
            cor_kml_hex = format(cor_kml, '08x')  # Formata o valor da cor para hexadecimal
            return cor_kml_hex # Retorna a cor formatada
        return 'ffffffff'  # Branco como cor padrão se não houver configuração de rótulo

    def cor_rgb_para_kml(self, cor_rgb):
        """
        Converte uma cor no formato RGB (usado comumente em interfaces gráficas) para o formato ABGR hexadecimal usado em arquivos KML.

        Parâmetros:
        - cor_rgb (QColor): O objeto QColor que representa a cor no formato RGB.

        Funcionalidades:
        - Extrai os componentes vermelho, verde, azul e alfa (transparência) da cor fornecida.
        - Converte esses valores para uma string hexadecimal.
        - Reorganiza a string para se adequar ao formato ABGR, que é o requerido pelo KML para especificar cores. No KML, a ordem dos componentes é alfa (transparência), azul, verde e vermelho, o que difere do padrão RGB mais comum.

        Atribuição no código:
        Facilita a integração e a exportação de dados visuais do QGIS para formatos que utilizam o padrão KML, como o Google Earth. A função assegura que a representação de cores seja mantida corretamente ao transferir informações de cor entre diferentes sistemas e formatos de arquivo, mantendo a fidelidade visual e a clareza das representações geográficas.
        """
        r = cor_rgb.red()
        g = cor_rgb.green()
        b = cor_rgb.blue()
        a = cor_rgb.alpha()

        # Converte os valores RGB para um formato hexadecimal e inverte a ordem para ABGR
        return f'{a:02x}{b:02x}{g:02x}{r:02x}'

    def gerar_cor_suave(self):
        """
        Gera uma cor aleatória com tonalidades suaves, geralmente inclinadas para cores claras, utilizando valores altos no espectro RGB.

        Funcionalidades:
        - Gera valores aleatórios para cada um dos componentes vermelho, verde e azul (RGB), garantindo que os valores estejam no intervalo de 180 a 255. Isso assegura que as cores geradas sejam suaves e claras, ideais para fundos ou para áreas onde cores menos saturadas são desejáveis.
        - Formata os valores RGB gerados em uma string hexadecimal que pode ser usada diretamente em estilos de interfaces gráficas ou em páginas web.

        Atribuição no código:
        Útil para a criação de interfaces de usuário atraentes e agradáveis visualmente, onde cores suaves e menos invasivas são necessárias. Também pode ser utilizada em gráficos, mapas e qualquer aplicativo que beneficie de uma paleta de cores mais suave e menos saturada.
        """
        # Gera uma cor clara somente para apresentação visual.
        r = random.randint(180, 255)  # nosec B311
        g = random.randint(180, 255)  # nosec B311
        b = random.randint(180, 255)  # nosec B311

        return f"#{r:02x}{g:02x}{b:02x}" # Retorna a cor formatada como uma string hexadecimal

    def exportar_para_kml(self):
        """
        Exporta uma camada selecionada do QGIS para o formato KML, permitindo configurações detalhadas através de um diálogo interativo.

        Funcionalidades:
        - Verifica se uma camada está selecionada para exportação. Exibe uma mensagem de erro e encerra se nenhuma camada estiver selecionada.
        - Recupera a camada selecionada e verifica sua existência no projeto QGIS.
        - Inicializa um diálogo com opções detalhadas de exportação para KML, incluindo seleção de campos, configurações de visualização 3D, e outros.
        - Se o diálogo for aceito pelo usuário, inicia o processo de exportação, incluindo a escolha do local para salvar o arquivo.
        - Cria um documento KML em memória com as configurações definidas, escreve no local especificado e aplica modificações adicionais se necessário.
        - Calcula e exibe o tempo decorrido para a operação de exportação, informando o usuário sobre a conclusão bem-sucedida.

        Atribuição no código:
        Essencial para a interoperabilidade com outras plataformas que suportam KML, como Google Earth. Esta funcionalidade facilita a visualização e compartilhamento de dados geográficos, permitindo que informações detalhadas das camadas do QGIS sejam apresentadas eficazmente em um formato amplamente utilizado. O diálogo interativo garante que os usuários possam personalizar a exportação para atender suas necessidades específicas.
        """
        # Seleciona a camada antes de escolher o local de salvamento
        indexes = self.dlg.treeViewListaLinha.selectedIndexes()  # Obtém a camada do projeto QGIS usando o ID
        if not indexes:
            self.mostrar_mensagem(self.tr("Nenhuma camada selecionada."), "Erro") # Exibe mensagem de erro se nenhuma camada estiver selecionada
            return

        # Obtém o ID da camada selecionada
        layer_id = indexes[0].model().itemFromIndex(indexes[0]).data()
        layer = QgsProject.instance().mapLayer(layer_id)

        if not layer:
            self.mostrar_mensagem(self.tr("Camada não encontrada."), "Erro")
            return

        campos = [field.name() for field in layer.fields()] # Lista os nomes dos campos da camada
        dialog = ExportarKMLDialog(campos) # Inicializa o diálogo de exportação com os campos da camada

        if dialog.exec() == QDialog.DialogCode.Accepted: # Verifica se o usuário aceitou o diálogo de exportação
            start_time = time.time()  # Inicia o temporizador

            # Obtém os valores definidos no diálogo de exportação
            campo_rotulo, espessura_linha, altitude, url_imagem, url_imagem_2, incluir_tabela, use_3d, num_repeticoes = dialog.getValues()

            # Define o nome padrão do arquivo e o local de salvamento
            nome_padrao = f"{layer.name()}.kml"
            tipo_arquivo = "KML Files (*.kml)"
            caminho_arquivos = self.escolher_local_para_salvar(nome_padrao, tipo_arquivo)

            if not caminho_arquivos:
                self.mostrar_mensagem(self.tr("Exportação cancelada."), "Info") # Cancela a exportação se o usuário não escolher um local para salvar
                return

            # Cria o KML em memória com as opções definidas
            kml_element = self.criar_kml_em_memoria(layer, campo_rotulo, espessura_linha, altitude, url_imagem, url_imagem_2, incluir_tabela, use_3d, num_repeticoes)

            # Escreve o KML no arquivo
            tree = XmlET.ElementTree(kml_element)
            tree.write(caminho_arquivos, xml_declaration=True, encoding='utf-8', method="xml")

            # Modificar KML para tessellation (se necessário)
            self.modificar_kml_para_tessellation(caminho_arquivos)

            elapsed_time = time.time() - start_time  # Calcula o tempo decorrido

            # Exibir mensagem de sucesso com o tempo de execução e caminhos dos arquivos
            self.mostrar_mensagem(self.tr("Camada exportada para KMZ em {elapsed_time:.2f} segundos").format(elapsed_time=elapsed_time), "Sucesso", caminho_pasta=os.path.dirname(caminho_arquivos), caminho_arquivos=caminho_arquivos)
        else:
            self.mostrar_mensagem(self.tr("Exportação cancelada."), "Aviso")

    def _fromstring_xml_seguro(self, xml_bytes):
        """
        Faz parse seguro de XML em memória usando defusedxml.
        Se a biblioteca não estiver instalada, mostra mensagem amigável.
        """
        if not DEFUSEDXML_OK:
            if not hasattr(self, "_avisou_defusedxml"):
                self._avisou_defusedxml = False

            if not self._avisou_defusedxml:
                self._avisou_defusedxml = True
                self.mostrar_mensagem(self.tr("A biblioteca 'defusedxml' não está instalada no Python do QGIS. Instale com: python -m pip install defusedxml"), "Erro", duracao=3)
            return None

        try:
            return DefusedET.fromstring(xml_bytes)
        except (DefusedET.ParseError, DefusedXmlException) as e:
            self.mostrar_mensagem(self.tr("XML/KML inválido ou inseguro: {error}").format(error=str(e)), "Erro", duracao=3)
            return None
        except Exception:
            return None

    def formatar_valor_kml(self, valor):
        """
        Formata valores de atributos para exportação KML.

        Corrige QDate, QTime e QDateTime do PyQt/QGIS,
        evitando saída do tipo:
        PyQt6.QtCore.QDateTime(...)
        """
        if valor is None:
            return ""

        try:
            if hasattr(valor, "isNull") and valor.isNull():
                return ""
        except Exception:
            pass  # nosec B110

        try:
            if hasattr(valor, "isValid") and not valor.isValid():
                return ""
        except Exception:
            pass  # nosec B110

        # QDateTime
        try:
            if hasattr(valor, "date") and hasattr(valor, "time") and hasattr(valor, "toString"):
                return valor.toString("dd/MM/yyyy HH:mm:ss")
        except Exception:
            pass  # nosec B110

        # QDate
        try:
            if (
                hasattr(valor, "year")
                and hasattr(valor, "month")
                and hasattr(valor, "day")
                and hasattr(valor, "toString")):
                return valor.toString("dd/MM/yyyy")
        except Exception:
            pass  # nosec B110

        # QTime
        try:
            if (
                hasattr(valor, "hour")
                and hasattr(valor, "minute")
                and hasattr(valor, "second")
                and hasattr(valor, "toString")):
                return valor.toString("HH:mm:ss")
        except Exception:
            pass  # nosec B110

        # datetime/date/time nativos do Python
        try:
            if hasattr(valor, "strftime"):
                if hasattr(valor, "year") and hasattr(valor, "hour"):
                    return valor.strftime("%d/%m/%Y %H:%M:%S")
                if hasattr(valor, "year"):
                    return valor.strftime("%d/%m/%Y")
                if hasattr(valor, "hour"):
                    return valor.strftime("%H:%M:%S")
        except Exception:
            pass  # nosec B110

        return str(valor)

    def criar_placemark_kml(self, document, feature, campo_rotulo, cor_linha_kml, espessura_linha, altitude_base, transformar, transform, url_imagem, url_imagem_2, incluir_tabela, use_3d, num_repeticoes):
        """
        Cria múltiplos Placemarks no documento KML para uma camada selecionada, permitindo configurações detalhadas de visualização e inclusão de dados em 3D.

        Parâmetros:
        - document (XmlET.Element): O elemento XML do documento KML onde os Placemarks serão adicionados.
        - feature (QgsFeature): A feição geográfica da qual o Placemark será criado.
        - campo_rotulo, cor_linha_kml, espessura_linha, altitude_base, transformar, transform, url_imagem, url_imagem_2, incluir_tabela, use_3d, num_repeticoes: Diversos parâmetros que definem as propriedades visuais e funcionais do Placemark, como cor, espessura, altitude, transformação geométrica, e opções de repetição para representações múltiplas.

        Funcionalidades:
        - Itera sobre o número de repetições especificadas para criar várias instâncias do Placemark, cada uma em uma altitude incremental.
        - Configura cada Placemark com linhas que podem ser simples ou multipartes, adaptando-se à geometria da feição.
        - Define estilos visuais detalhados, incluindo cor e espessura das linhas.
        - Se solicitado, adiciona uma tabela de atributos ao Placemark usando um BalloonStyle, enriquecendo a representação com informações detalhadas.
        - Permite a inclusão de imagens e estilos visuais personalizados para melhorar a apresentação dos dados.

        Atribuição no código:
        A função é crucial para exportações detalhadas para KML, proporcionando uma representação rica e interativa das camadas do QGIS em plataformas como o Google Earth. Permite a visualização eficaz de informações complexas e é essencial em contextos onde a clareza e a profundidade da apresentação de dados geográficos são necessárias.
        """
        for i in range(num_repeticoes):
            altitude = altitude_base + i * altitude_base
            placemark = XmlET.SubElement(document, 'Placemark')

            if feature.geometry().isMultipart():
                lines = feature.geometry().asMultiPolyline()
                multi_geometry = XmlET.SubElement(placemark, 'MultiGeometry')
                for part in lines:
                    self.add_line_string_kml(multi_geometry, part, altitude, transformar, transform, cor_linha_kml, espessura_linha, use_3d)
            else:
                lines = feature.geometry().asPolyline()
                self.add_line_string_kml(placemark, lines, altitude, transformar, transform, cor_linha_kml, espessura_linha, use_3d)

            # Configura o estilo do Placemark para cada repetição
            style = XmlET.SubElement(placemark, 'Style')
            line_style = XmlET.SubElement(style, 'LineStyle')
            color = XmlET.SubElement(line_style, 'color')
            color.text = cor_linha_kml
            width = XmlET.SubElement(line_style, 'width')
            width.text = f'{espessura_linha:.1f}'
       
        # Se incluir_tabela for True, adiciona os atributos da feature e configura o BalloonStyle
        if incluir_tabela:
            valor_campo_rotulo = self.formatar_valor_kml(feature[campo_rotulo])

            name = XmlET.SubElement(placemark, 'name')
            name.text = valor_campo_rotulo

            extended_data = XmlET.SubElement(placemark, 'ExtendedData')

            for field in feature.fields():
                valor_formatado = self.formatar_valor_kml(feature[field.name()])

                data = XmlET.SubElement(extended_data, 'Data', name=field.name())
                value = XmlET.SubElement(data, 'value')
                value.text = valor_formatado

            # Inserindo visibilidade do rótulo
            label_visibility = XmlET.SubElement(line_style, '{http://www.google.com/kml/ext/2.2}labelVisibility')
            label_visibility.text = '1'

            # Início da construção da tabela de atributos
            tabela_geral_html = '<table border="1" style="border-collapse: collapse; border: 2px solid black; width: 100%;">'

            for field in feature.fields():
                valor_formatado = self.formatar_valor_kml(feature[field.name()])
                cor_fundo = self.gerar_cor_suave()

                tabela_geral_html += '<tr><td>'

                tabela_campo_html = f'<table border="0" style="background-color: {cor_fundo}; width: 100%;">'
                tabela_campo_html += f'<tr><td style="text-align: left;"><b>{field.name()}</b></td><td style="text-align: right;">{valor_formatado}</td></tr>'
                tabela_campo_html += '</table>'

                tabela_geral_html += tabela_campo_html
                tabela_geral_html += '</td></tr>'

            tabela_geral_html += '</table>'

            # Checagem se a URL da imagem foi fornecida
            imagem_html = ""

            texto_alt_icone = self.tr("Ícone")
            titulo_tabela = self.tr("Tabela de Informações:")

            if url_imagem:
                imagem_redimensionada, nova_largura, nova_altura = self.redimensionar_imagem_proporcional_url(url_imagem, 150, 75)

                if imagem_redimensionada is not None:
                    imagem_html = f'<div style="text-align: center;"><img src="{url_imagem}" alt="{texto_alt_icone}" width="{nova_largura}" height="{nova_altura}" style="margin-top: 1px; margin-bottom: -15px; margin-left: 0px; margin-right: 0px;"></div>'

            # BalloonStyle com a imagem condicional e tabela de atributos
            balloon_style = XmlET.SubElement(style, 'BalloonStyle')
            text = XmlET.SubElement(balloon_style, 'text')
            balloon_html = f"""
            {imagem_html}
            <h3 style="margin-bottom:1px;">{campo_rotulo}: {valor_campo_rotulo}</h3>
            <p>{titulo_tabela}</p>
            {tabela_geral_html}
            $[description]
            """
            text.text = balloon_html

    def add_line_string_kml(self, parent, line_points, altitude, transformar, transform, cor_linha_kml, espessura_linha, use_3d):
        """
        Adiciona uma representação KML de uma linha (LineString) ao elemento KML pai fornecido, configurando opções como altitude, tesselação e transformação de coordenadas conforme necessário.

        Parâmetros:
        - parent (ElementTree Element): O elemento pai KML ao qual a LineString será adicionada.
        - line_points (list of QgsPointXY): Lista dos pontos que compõem a linha.
        - altitude (float): A altitude que cada ponto da linha deve ter.
        - transformar (bool): Se verdadeiro, aplica uma transformação geográfica aos pontos da linha.
        - transform (QgsCoordinateTransform): A transformação a ser aplicada, se transformar for verdadeiro.
        - cor_linha_kml (str): Cor da linha no formato KML.
        - espessura_linha (float): A espessura da linha para a visualização.
        - use_3d (bool): Se verdadeiro, habilita a extrusão para efeito tridimensional.

        Funcionalidades:
        - Cria um subelemento LineString dentro do elemento parente especificado.
        - Configura o modo de altitude para a LineString baseado no valor de altitude fornecido.
        - Habilita a tesselação se a altitude for zero para garantir uma renderização correta no Google Earth.
        - Habilita a extrusão se `use_3d` estiver ativo e a altitude for diferente de zero, criando um efeito tridimensional.
        - Transforma os pontos da linha se necessário e os formata em uma string de coordenadas que inclui a altitude.
        - Adiciona as coordenadas transformadas e formatadas ao elemento LineString.

        Atribuição no código:
        Essencial para criar visualizações detalhadas e precisas de linhas em arquivos KML, permitindo a representação adequada de características geográficas em plataformas que suportam KML, como o Google Earth. A funcionalidade de transformação e a inclusão de altitude são cruciais para garantir que as linhas sejam visualizadas corretamente em relação ao terreno e em diferentes contextos geográficos.
        """
        # Cria um subelemento LineString dentro do elemento parente
        line_string = XmlET.SubElement(parent, 'LineString')

        # Configura o modo de altitude para a LineString
        altitude_mode = XmlET.SubElement(line_string, 'altitudeMode')
        # Define o texto do modo de altitude com base no valor da altitude
        altitude_mode.text = 'relativeToGround' if altitude != 0 else 'clampToGround'
        
        # Se a altitude é 0, habilita a tesselação para melhorar a renderização no Google Earth
        if altitude != 0 and use_3d:
            extrude = XmlET.SubElement(line_string, 'extrude')
            extrude.text = '1'
        tessellate = XmlET.SubElement(line_string, 'tessellate')
        tessellate.text = '1'
        
        # Cria um subelemento para as coordenadas
        coordinates = XmlET.SubElement(line_string, 'coordinates')
        coords = [] # Inicializa uma lista para armazenar as coordenadas formatadas

        for point in line_points: # Itera sobre cada ponto na linha fornecida
            if transformar:  # Se a transformação estiver habilitada, transforma o ponto
                point = transform.transform(point)  # Transforma o ponto se necessário
            # Adiciona o ponto transformado (ou não) à lista de coordenadas, incluindo a altitude
            coords.append(f"{point.x()},{point.y()},{altitude}")
        # Junta todas as coordenadas em uma string e a define como texto do elemento de coordenadas
        coordinates.text = ' '.join(coords) 

    def criar_kml_em_memoria(self, layer, campo_rotulo, espessura_linha, altitude, url_imagem, url_imagem_2, incluir_tabela, use_3d, num_repeticoes):
        """
        # Cria uma representação KML em memória de uma camada do QGIS, incluindo opções para visualização 3D, repetição de elementos, tabelas de atributos e a possibilidade de adicionar uma imagem como ScreenOverlay.

        # Parâmetros:
        # - layer (QgsVectorLayer): A camada de onde os dados serão extraídos.
        # - campo_rotulo (str): O campo utilizado para o rótulo dos placemarks.
        # - espessura_linha (float): A espessura das linhas no KML.
        # - altitude (int): A altitude base para os placemarks.
        # - url_imagem (str): URL para uma imagem usada como ícone nos placemarks.
        # - url_imagem_2 (str): URL para uma imagem usada como ScreenOverlay no KML.
        # - incluir_tabela (bool): Se verdadeiro, inclui uma tabela de atributos em cada placemark.
        # - use_3d (bool): Se verdadeiro, aplica extrusão para efeito tridimensional.
        # - num_repeticoes (int): Número de vezes que cada placemark será repetido com incremento de altitude.

        # Funcionalidades:
        # - Cria o elemento KML e um subelemento Documento.
        # - Utiliza um índice espacial para otimizar a criação de placemarks.
        # - Para cada feição na camada, um placemark é criado com opções de visualização configuráveis.
        # - Utiliza uma barra de progresso para indicar o progresso da criação do KML.
        # - Adiciona um ScreenOverlay ao KML se uma segunda URL de imagem for fornecida e a imagem for processada corretamente.
        # - Caso a imagem do ScreenOverlay não possa ser processada, o KML é gerado normalmente sem o ScreenOverlay.
        # - Retorna o elemento KML criado para uso posterior, como salvar em um arquivo ou enviar por rede.
        """
        # Barra de progresso (mensagem opcional)
        progressBar, messageBarWidget = self.iniciar_progress_bar(layer, message=f"Exportando para KML: {layer.name()}")

        # Estrutura base
        kml = XmlET.Element('kml', xmlns="http://www.opengis.net/kml/2.2")
        document = XmlET.SubElement(kml, 'Document')

        # Pré-cálculos (não faça isso dentro do loop!)
        cor_linha = self.obter_cor_linha(layer)
        cor_linha_kml = self.cor_rgb_para_kml(cor_linha)

        src_crs = layer.crs()
        transformar = (src_crs.isValid() and src_crs.authid() != "EPSG:4326")

        transform = None
        if transformar:
            crsDestino = QgsCoordinateReferenceSystem("EPSG:4326")
            if crsDestino.isValid():
                transform = QgsCoordinateTransform(src_crs, crsDestino, QgsProject.instance().transformContext())
            else:
                transformar = False

        # Total e “peso” do update da UI
        total_features = 0
        try:
            total_features = int(layer.featureCount())
        except Exception:
            total_features = 0

        if total_features > 0:
            progressBar.setMaximum(total_features)
        else:
            progressBar.setMaximum(0)

        # Loop ÚNICO: gera 1 vez cada feição
        step_ui = 50  # ajuste fino: 25/50/100 dependendo do tamanho
        for i, feature in enumerate(layer.getFeatures()):
            self.criar_placemark_kml(
                document, feature, campo_rotulo,
                cor_linha_kml, espessura_linha, altitude,
                transformar, transform,
                url_imagem, url_imagem_2,
                incluir_tabela, use_3d, num_repeticoes)

            # Atualiza UI em blocos (muito mais rápido)
            if (i + 1) % step_ui == 0:
                try:
                    progressBar.setValue(i + 1)
                except RuntimeError:
                    # Barra removida pelo usuário
                    return kml
                QCoreApplication.processEvents()

        # Fecha barra (100%)
        try:
            if total_features > 0:
                progressBar.setValue(total_features)
        except Exception:
            pass  # nosec B110

        # ScreenOverlay só 1 vez (fora do loop)
        if url_imagem_2:
            imagem_redimensionada, nova_largura, nova_altura = self.redimensionar_imagem_proporcional_url(
                url_imagem_2, 300, 150)
            if imagem_redimensionada is not None:
                screen_overlay = XmlET.SubElement(document, 'ScreenOverlay')
                name = XmlET.SubElement(screen_overlay, 'name')
                name.text = 'logo'

                icon = XmlET.SubElement(screen_overlay, 'Icon')
                href = XmlET.SubElement(icon, 'href')
                href.text = url_imagem_2

                XmlET.SubElement(screen_overlay, 'overlayXY', x="0", y="0", xunits="fraction", yunits="fraction")
                XmlET.SubElement(screen_overlay, 'screenXY', x="0", y="0", xunits="fraction", yunits="fraction")
                XmlET.SubElement(screen_overlay, 'rotationXY', x="0", y="0", xunits="fraction", yunits="fraction")
                XmlET.SubElement(
                    screen_overlay, 'size',
                    x=f"{nova_largura}", y=f"{nova_altura}",
                    xunits="pixels", yunits="pixels")

        # Remove só o widget que você criou (não limpa a messageBar inteira)
        try:
            self.iface.messageBar().popWidget(messageBarWidget)
        except Exception:
            pass  # nosec B110

        return kml

    def redimensionar_imagem_proporcional_url(self, url_imagem, largura_max, altura_max):
        """
        Baixa imagem de um URL e redimensiona proporcionalmente.

        Otimização:
        - Cache por (url, largura_max, altura_max) para não baixar/redimensionar repetidas vezes.
        - Timeout no requests.get para evitar travas em URL lenta.
        """
        if not url_imagem:
            return None, None, None

        # Cache na instância
        if not hasattr(self, "_img_resize_cache"):
            self._img_resize_cache = {}

        key = (str(url_imagem), int(largura_max), int(altura_max))
        if key in self._img_resize_cache:
            return self._img_resize_cache[key]

        headers = {'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120 Safari/537.36'}

        try:
            response = requests.get(url_imagem, headers=headers, timeout=10)
            response.raise_for_status()

            imagem = Image.open(BytesIO(response.content))
            largura_original, altura_original = imagem.size

            proporcao_largura = largura_max / largura_original
            proporcao_altura = altura_max / altura_original
            proporcao_final = min(proporcao_largura, proporcao_altura)

            nova_largura = max(1, int(largura_original * proporcao_final))
            nova_altura = max(1, int(altura_original * proporcao_final))

            imagem_redimensionada = imagem.resize((nova_largura, nova_altura), Image.LANCZOS)

            out = (imagem_redimensionada, nova_largura, nova_altura)
            self._img_resize_cache[key] = out
            return out

        except UnidentifiedImageError:
            self._img_resize_cache[key] = (None, None, None)
            self.mostrar_mensagem(self.tr("Erro ao abrir a imagem. O arquivo não é uma imagem válida ou está corrompido."), "Erro")
            return None, None, None

        except Exception as e:
            self._img_resize_cache[key] = (None, None, None)
            self.mostrar_mensagem(self.tr("Erro ao processar a imagem: {error}").format(error=e), "Erro")
            return None, None, None

    def modificar_kml_para_tessellation(self, caminho_kml):
        """
        Evita reescrever o KML se ele já possuir tessellate.
        Caso contrário, adiciona tessellate aos LineString.
        """
        try:
            with open(
                caminho_kml,
                "r",
                encoding="utf-8",
                errors="ignore") as arquivo:
                head = arquivo.read(200000)

            if "<tessellate>" in head:
                return

        except Exception:
            pass  # nosec B110

        try:
            parser = XmlET.XMLParser(
                resolve_entities=False,
                no_network=True,
                recover=False)

            tree = XmlET.parse(caminho_kml, parser)

            root = tree.getroot()

            ns = "http://www.opengis.net/kml/2.2"
            nsmap = {"kml": ns}

            line_strings = root.findall(".//kml:LineString", nsmap)

            for line_string in line_strings:
                if line_string.find("kml:tessellate", nsmap
                ) is None:
                    tess = XmlET.SubElement(
                        line_string,
                        f"{{{ns}}}tessellate")
                    tess.text = "1"

            tree.write(
                caminho_kml,
                xml_declaration=True,
                encoding="utf-8",
                method="xml")

        except Exception as e:
            self.mostrar_mensagem(self.tr("Erro ao modificar o arquivo KML: {error}").format(error=e), "Erro")

    def _processar_kml_kmz(self, file_path: str, layer_name: str):
        """
        Abre KML/KMZ e adiciona APENAS camadas de LINHAS.
        Também limpa o nome final da camada:
        - remove o prefixo do arquivo/grupo (ex.: "Teste - ")
        - remove extensão .kml/.kmz do nome (ex.: "APP.kml" -> "APP")
        Retorna: list[QgsVectorLayer] (memory) ou [].
        """
        out_layers = []
        seen = set()
        used_names = set()

        def _limpar_nome(nome: str) -> str:
            if not nome:
                return layer_name

            nome = str(nome).strip()

            # remove extensão se vier no nome (APP.kml / APP.kmz)
            low = nome.lower()
            if low.endswith(".kml") or low.endswith(".kmz"):
                nome = os.path.splitext(nome)[0].strip()

            # remove prefixo do arquivo/grupo se estiver embutido no sublayer
            # ex.: "Teste - APP" / "Teste_APP" / "Teste-APP"
            low_nome = nome.lower()
            low_prefix = layer_name.lower()
            if low_nome.startswith(low_prefix):
                resto = nome[len(layer_name):].lstrip(" _-–—").strip()
                if resto:
                    nome = resto

            return nome or layer_name

        def _nome_unico(base: str) -> str:
            n = base
            i = 2
            while n in used_names:
                n = f"{base} ({i})"
                i += 1
            used_names.add(n)
            return n

        def _infer_geom_type(layer: QgsVectorLayer):
            """Inferência robusta (igual ideia da _copiar_para_memoria), mas só pra decidir se é LINHA."""
            geom_type = QgsWkbTypes.geometryType(layer.wkbType())
            if geom_type in (QgsWkbTypes.GeometryType.UnknownGeometry, QgsWkbTypes.GeometryType.NullGeometry):
                for f in layer.getFeatures():
                    g = f.geometry()
                    if g and not g.isEmpty():
                        geom_type = QgsWkbTypes.geometryType(g.wkbType())
                        break
            return geom_type

        def _yield_sublayers():
            # 1) provider metadata (quando disponível)
            try:
                md = QgsProviderRegistry.instance().providerMetadata("ogr")
                details = md.querySublayers(file_path)
                for d in details or []:
                    uri = d.uri() if hasattr(d, "uri") else None
                    name = d.name() if hasattr(d, "name") else None
                    if uri and name:
                        key = (uri, name)
                        if key in seen:
                            continue
                        seen.add(key)
                        yield uri, name
                if details:
                    return
            except Exception:
                pass  # nosec B110

            # 2) fallback: subLayers() do provider
            dummy = QgsVectorLayer(file_path, layer_name, "ogr")
            if not dummy.isValid():
                return

            try:
                subs = dummy.dataProvider().subLayers() or []
            except Exception:
                subs = []

            if subs:
                for s in subs:
                    parts = s.split(":")
                    if len(parts) >= 2:
                        name = parts[1]
                        uri = f"{file_path}|layername={name}"
                        key = (uri, name)
                        if key in seen:
                            continue
                        seen.add(key)
                        yield uri, name
            else:
                yield file_path, layer_name

        any_valid = False

        for uri, subname in _yield_sublayers():
            src = QgsVectorLayer(uri, subname, "ogr")
            if not src.isValid():
                continue

            any_valid = True

            # Só LINHAS
            if _infer_geom_type(src) != QgsWkbTypes.GeometryType.LineGeometry:
                del src
                continue

            # Nome limpo (sem "Teste - " e sem ".kml")
            clean = _limpar_nome(subname)
            clean = _nome_unico(clean)

            mem = self._copiar_para_memoria(src, clean)
            if mem and mem.isValid():
                # aplica o estilo NORMAL do KML por pasta (REDE/APP/etc)
                # use subname (antes de limpar) porque costuma bater com o <name> do Folder no KML/GE
                self._aplicar_estilo_kml_normal_na_memoria(file_path, subname, mem)
                out_layers.append(mem)
            del src

        if not any_valid:
            self.mostrar_mensagem(self.tr("Falha ao carregar KML/KMZ."), "Erro")
            return []

        if not out_layers:
            self.mostrar_mensagem(self.tr("Nenhuma camada de LINHAS encontrada no KML/KMZ."), "Aviso")
            return []

        return out_layers

    def _kml_read_xml(self, file_path: str) -> bytes | None:
        """Lê XML do KML (arquivo .kml) ou do doc.kml dentro do KMZ."""
        ext = os.path.splitext(file_path)[1].lower()

        if ext == ".kml":
            try:
                with open(file_path, "rb") as f:
                    return f.read()
            except Exception:
                return None

        if ext == ".kmz":
            try:
                with zipfile.ZipFile(file_path, "r") as z:
                    kml_files = [n for n in z.namelist() if n.lower().endswith(".kml")]

                    # doc.kml é o padrão mais comum
                    for n in kml_files:
                        if os.path.basename(n).lower() == "doc.kml":
                            return z.read(n)

                    # fallback: primeiro kml encontrado
                    if kml_files:
                        return z.read(kml_files[0])
            except Exception:
                return None

        return None

    def _kml_parse_style_index(self, root):
        """Indexa Style e StyleMap (normal) do KML."""
        ns = {"k": "http://www.opengis.net/kml/2.2"}

        # Style id -> (QColor, width_px)
        styles = {}
        for st in root.findall(".//k:Style", ns):
            sid = st.get("id")
            if not sid:
                continue
            ls = st.find("k:LineStyle", ns)
            if ls is None:
                continue

            col_hex = (ls.findtext("k:color", default="", namespaces=ns) or "").strip()
            wid_txt = (ls.findtext("k:width", default="", namespaces=ns) or "").strip()

            qcol = None
            if col_hex and len(col_hex) == 8:
                # KML: AABBGGRR
                try:
                    a = int(col_hex[0:2], 16)
                    b = int(col_hex[2:4], 16)
                    g = int(col_hex[4:6], 16)
                    r = int(col_hex[6:8], 16)
                    qcol = QColor(r, g, b, a)
                except Exception:
                    qcol = None

            wpx = None
            if wid_txt:
                try:
                    wpx = float(wid_txt)
                except Exception:
                    wpx = None

            if qcol:
                styles[sid] = (qcol, wpx)

        # StyleMap id -> normal style id
        stylemaps = {}
        for sm in root.findall(".//k:StyleMap", ns):
            mid = sm.get("id")
            if not mid:
                continue
            normal_url = None
            for pair in sm.findall("k:Pair", ns):
                key = (pair.findtext("k:key", default="", namespaces=ns) or "").strip().lower()
                if key == "normal":
                    normal_url = (pair.findtext("k:styleUrl", default="", namespaces=ns) or "").strip()
                    break
            if normal_url:
                stylemaps[mid] = normal_url.lstrip("#")

        return styles, stylemaps

    def _kml_find_folder(self, root, folder_name: str):
        """Acha Folder/Document com <name> igual ao nome da subcamada."""
        ns = {"k": "http://www.opengis.net/kml/2.2"}

        wanted = set()
        raw = (folder_name or "").strip()
        if raw:
            wanted.add(raw)
            wanted.add(os.path.splitext(raw)[0])

        # procura em Document e Folder
        for tag in ("Document", "Folder"):
            for el in root.findall(f".//k:{tag}", ns):
                nm = (el.findtext("k:name", default="", namespaces=ns) or "").strip()
                if nm in wanted or os.path.splitext(nm)[0] in wanted:
                    return el

        return None

    def _kml_normal_linestyle_for_folder(self, kml_xml: bytes, folder_name: str):
        """Retorna (QColor, width_px) do estilo NORMAL predominante dentro da pasta."""
        if not kml_xml:
            return None, None

        ns = {"k": "http://www.opengis.net/kml/2.2"}

        root = self._fromstring_xml_seguro(kml_xml)
        if root is None:
            return None, None

        styles, stylemaps = self._kml_parse_style_index(root)
        container = self._kml_find_folder(root, folder_name)

        # se não achar pasta, cai pro documento todo
        if container is None:
            container = root

        style_ids = []
        for pm in container.findall(".//k:Placemark", ns):
            style_url = (pm.findtext("k:styleUrl", default="", namespaces=ns) or "").strip()
            sid = style_url.lstrip("#") if style_url else ""

            if sid in stylemaps:
                sid = stylemaps[sid]

            if sid in styles:
                style_ids.append(sid)

            # (opcional) inline Style dentro do Placemark
            if not sid:
                st = pm.find("k:Style", ns)
                if st is not None:
                    ls = st.find("k:LineStyle", ns)
                    if ls is not None:
                        col_hex = (ls.findtext("k:color", default="", namespaces=ns) or "").strip()
                        wid_txt = (ls.findtext("k:width", default="", namespaces=ns) or "").strip()
                        if col_hex and len(col_hex) == 8:
                            try:
                                a = int(col_hex[0:2], 16)
                                b = int(col_hex[2:4], 16)
                                g = int(col_hex[4:6], 16)
                                r = int(col_hex[6:8], 16)
                                qcol = QColor(r, g, b, a)
                                wpx = float(wid_txt) if wid_txt else None
                                return qcol, wpx
                            except Exception:
                                pass  # nosec B110

        if not style_ids:
            return None, None

        sid = Counter(style_ids).most_common(1)[0][0]
        return styles.get(sid, (None, None))

    def _aplicar_estilo_kml_normal_na_memoria(self, file_path: str, folder_name: str, mem_layer):
        """Aplica na camada memória o estilo NORMAL do KML (cor + width em pixels)."""
        if not mem_layer or not mem_layer.isValid():
            return

        xml = self._kml_read_xml(file_path)
        col, wpx = self._kml_normal_linestyle_for_folder(xml, folder_name)

        if not col:
            return

        symbol = QgsLineSymbol()
        sl = symbol.symbolLayer(0)

        # Cor (com alpha)
        try:
            sl.setColor(col)
        except Exception:
            pass  # nosec B110

        # Largura em pixels (mais fiel ao Google Earth/KML)
        if wpx is not None:
            try:
                sl.setWidth(float(wpx))
                # QGIS 3.x
                if hasattr(sl, "setWidthUnit"):
                    sl.setWidthUnit(QgsUnitTypes.RenderUnit.RenderPixels)
                elif hasattr(sl, "setOutputUnit"):
                    sl.setOutputUnit(QgsUnitTypes.RenderUnit.RenderPixels)
            except Exception:
                pass  # nosec B110

        mem_layer.setRenderer(QgsSingleSymbolRenderer(symbol))
        mem_layer.triggerRepaint()

    def _copiar_para_memoria(self, src: QgsVectorLayer, new_name: str) -> QgsVectorLayer:
        """
        Copia a camada `src` para memória, mantendo atributos e garantindo que TODAS as feições entrem.

        Extra (KML/KMZ):
        - Se o renderer for QgsEmbeddedSymbolRenderer, extrai cor/espessura POR FEIÇÃO
          e aplica na camada em memória via data-defined (campos __kml_color / __kml_width_mm).
        """
        if not isinstance(src, QgsVectorLayer) or not src.isValid():
            raise ValueError(self.tr("Camada de origem inválida em _copiar_para_memoria()."))

        crs_authid = src.crs().authid() if src.crs() and src.crs().isValid() else "EPSG:4326"

        # Detecta tipo geom (Point/Line/Polygon/Unknown/Null)
        geom_type = QgsWkbTypes.geometryType(src.wkbType())
        if geom_type in (QgsWkbTypes.GeometryType.UnknownGeometry, QgsWkbTypes.GeometryType.NullGeometry):
            for f in src.getFeatures():
                g = f.geometry()
                if g and not g.isEmpty():
                    geom_type = QgsWkbTypes.geometryType(g.wkbType())
                    break

        # Sem geometria → copia tabela
        if geom_type in (QgsWkbTypes.GeometryType.UnknownGeometry, QgsWkbTypes.GeometryType.NullGeometry):
            mem = QgsVectorLayer(f"None?crs={crs_authid}", new_name, "memory")
            if not mem.isValid():
                raise RuntimeError(self.tr("Falha ao criar camada em memória (None)."))

            dp = mem.dataProvider()
            dp.addAttributes(src.fields())
            mem.updateFields()

            feats_out = []
            for f in src.getFeatures():
                nf = QgsFeature(mem.fields())
                nf.setAttributes(f.attributes())
                feats_out.append(nf)

            if feats_out:
                dp.addFeatures(feats_out)

            # tenta clonar renderer (tanto faz aqui)
            try:
                if src.renderer():
                    mem.setRenderer(src.renderer().clone())
            except Exception:
                pass  # nosec B110

            return mem

        # Mem sempre MULTI (robusto)
        if geom_type == QgsWkbTypes.GeometryType.PointGeometry:
            mem_geom = "MultiPoint"
        elif geom_type == QgsWkbTypes.GeometryType.LineGeometry:
            mem_geom = "MultiLineString"
        else:
            mem_geom = "MultiPolygon"

        mem = QgsVectorLayer(f"{mem_geom}?crs={crs_authid}", new_name, "memory")
        if not mem.isValid():
            raise RuntimeError(self.tr("Falha ao criar camada em memória ({mem_geom}).").format(mem_geom=mem_geom))

        dp = mem.dataProvider()

        # Detecta renderer embedded (KML)
        renderer = src.renderer()
        is_embedded = bool(renderer and hasattr(renderer, "type") and renderer.type() == "embeddedSymbol")

        # Campos base
        dp.addAttributes(src.fields())

        # Campos extras para estilo por feição (somente se for embedded)
        if is_embedded and geom_type == QgsWkbTypes.GeometryType.LineGeometry:
            dp.addAttributes([
                QgsField("__kml_color", QMetaType.Type.QString),
                QgsField("__kml_width_mm", QMetaType.Type.Double)])

        mem.updateFields()

        # Contexto básico de render (pra symbolForFeature)
        ctx = QgsRenderContext()
        ctx.setScaleFactor(1.0)

        def _extract_line_style(feat: QgsFeature) -> tuple[str | None, float | None]:
            """Extrai cor (HexArgb) e width(mm) do renderer embedded para uma feição."""
            if not renderer:
                return None, None
            try:
                sym = renderer.symbolForFeature(feat, ctx)
                if sym is None:
                    return None, None
                # cor: para linha, sym.color() costuma representar o stroke
                col = sym.color()
                color_hex = col.name(QColor.NameFormat.HexArgb) if col else None

                # width: tenta no symbol layer 0
                w = None
                sl = sym.symbolLayer(0) if sym.symbolLayerCount() > 0 else None
                if sl and hasattr(sl, "width"):
                    w = float(sl.width())
                return color_hex, w
            except Exception:
                return None, None

        def _to_multi_geom(g: QgsGeometry) -> QgsGeometry | None:
            """
            Converte QUALQUER coisa linha/ponto/polígono (single ou multi, com/sem Z)
            para um Multi 2D compatível com a layer memory.
            """
            if g is None or g.isEmpty():
                return None

            try:
                if geom_type == QgsWkbTypes.GeometryType.PointGeometry:
                    if QgsWkbTypes.isMultiType(g.wkbType()):
                        pts = g.asMultiPoint()
                        if pts:
                            return QgsGeometry.fromMultiPointXY(pts)
                    pt = g.asPoint()
                    if not pt:
                        return None
                    return QgsGeometry.fromMultiPointXY([pt])

                if geom_type == QgsWkbTypes.GeometryType.LineGeometry:
                    # multi também vira MultiPolylineXY (2D), não volta "cru" com Z
                    if QgsWkbTypes.isMultiType(g.wkbType()):
                        mls = g.asMultiPolyline()
                        if mls:
                            return QgsGeometry.fromMultiPolylineXY(mls)

                    ls = g.asPolyline()
                    if ls:
                        return QgsGeometry.fromMultiPolylineXY([ls])

                    # fallback extra (curvas / casos estranhos)
                    gg = QgsGeometry(g)
                    try:
                        gg.convertToType(QgsWkbTypes.GeometryType.LineGeometry, True)
                        mls2 = gg.asMultiPolyline()
                        if mls2:
                            return QgsGeometry.fromMultiPolylineXY(mls2)
                    except Exception:
                        pass  # nosec B110
                    return None

                # PolygonGeometry
                if QgsWkbTypes.isMultiType(g.wkbType()):
                    mp = g.asMultiPolygon()
                    if mp:
                        return QgsGeometry.fromMultiPolygonXY(mp)

                p = g.asPolygon()
                if not p:
                    return None
                return QgsGeometry.fromMultiPolygonXY([p])

            except Exception:
                return None

        feats_out = []
        for f in src.getFeatures():
            g = f.geometry()
            if g is None or g.isEmpty():
                continue

            if QgsWkbTypes.geometryType(g.wkbType()) != geom_type:
                continue

            mg = _to_multi_geom(g)
            if mg is None or mg.isEmpty():
                continue

            nf = QgsFeature(mem.fields())

            attrs = list(f.attributes())

            # adiciona attrs extras se embedded (linha)
            if is_embedded and geom_type == QgsWkbTypes.GeometryType.LineGeometry:
                color_hex, width_mm = _extract_line_style(f)
                attrs.append(color_hex or "#ff000000")
                attrs.append(float(width_mm) if width_mm is not None else 0.26)

            nf.setAttributes(attrs)
            nf.setGeometry(mg)
            feats_out.append(nf)

        if feats_out:
            dp.addFeatures(feats_out)

        mem.updateExtents()

        # SÍMBOLOS
        if is_embedded and geom_type == QgsWkbTypes.GeometryType.LineGeometry:
            # aplica estilo por feição via data-defined (campos)
            base = QgsLineSymbol.createSimple({})
            sl = base.symbolLayer(0)

            sl.setDataDefinedProperty(QgsSymbolLayer.Property.PropertyStrokeColor, QgsProperty.fromField("__kml_color"))
            sl.setDataDefinedProperty(QgsSymbolLayer.Property.PropertyStrokeWidth, QgsProperty.fromField("__kml_width_mm"))
            sl.setWidthUnit(QgsUnitTypes.RenderUnit.RenderMillimeters)

            mem.setRenderer(QgsSingleSymbolRenderer(base))
        else:
            # padrão: tenta clonar renderer
            try:
                if src.renderer():
                    mem.setRenderer(src.renderer().clone())
            except Exception:
                pass  # nosec B110

        return mem

    def carregar_texto_dxf(self, path_dxf: str, nome_layer: str, crs_authid: str = "EPSG:4326") -> QgsVectorLayer | None:
        """
        Lê um arquivo DXF e, se houver entidades de texto, cria uma camada de pontos em memória
        rotulada com o conteúdo e a formatação original, com suporte à cor ByLayer.

        Funcionalidades principais:
        1. Valida o caminho do arquivo DXF.
        2. Lê todas as entidades do tipo TEXT e MTEXT do modelspace do DXF usando ezdxf.
        3. Cria uma camada de pontos em memória (QGIS) com os campos:
            - text: conteúdo do texto.
            - height: altura do texto (quando disponível).
            - rotation: rotação (em graus, ajustada para sentido do QGIS).
            - x, y: coordenadas de inserção.
            - r, g, b: cor do texto (detecta true-color, ByLayer ou ACI, com fallback para preto em ByBlock).
        4. Monta um dicionário de cores das layers do DXF, para suportar textos com cor ByLayer.
        5. Para cada entidade, extrai atributos, converte e ajusta rotação, determina cor conforme prioridade:
            a. True-color direto (rgb);
            b. ByLayer (herda cor da layer do DXF);
            c. ByBlock ou sem cor definida: preto;
            d. Cor direta (ACI - AutoCAD Color Index).
        6. Adiciona todos os textos como feições à camada de pontos.
        7. Configura a camada para exibir rótulos (labels) com rotação e cor dinâmicas por campo.
        8. Torna o símbolo de ponto invisível para que apenas o texto apareça no mapa.

        Parâmetros:
            path_dxf   : str
                Caminho completo do arquivo DXF a ser lido.
            nome_layer : str
                Nome desejado para a camada criada.
            crs_authid : str (opcional)
                Código de referência espacial (ex: "EPSG:4326") para o sistema de coordenadas.

        Retorno:
            QgsVectorLayer | None
                Camada de pontos QGIS com textos e propriedades originais, ou None se não houver textos.
        """
        # Verifica existência do arquivo DXF
        if not path_dxf or not os.path.isfile(path_dxf):
            raise FileNotFoundError(self.tr("Caminho DXF inválido: {path_dxf}").format(path_dxf=repr(path_dxf)))

        doc = ezdxf.readfile(path_dxf)
        msp = doc.modelspace()
        entities = list(msp.query("TEXT MTEXT"))
        if not entities:
            return None  # Sem entidades de texto, retorna None

        # Cria camada de pontos em memória
        vl = QgsVectorLayer(f"Point?crs={crs_authid}", nome_layer, "memory")
        pr = vl.dataProvider()

        # Define os campos que serão utilizados na camada
        pr.addAttributes([
            QgsField("text",     QMetaType.Type.QString),
            QgsField("height",   QMetaType.Type.Double),
            QgsField("rotation", QMetaType.Type.Double),
            QgsField("x",        QMetaType.Type.Double),
            QgsField("y",        QMetaType.Type.Double),
            QgsField("r",        QMetaType.Type.Int),
            QgsField("g",        QMetaType.Type.Int),
            QgsField("b",        QMetaType.Type.Int)])
        vl.updateFields()

        # Monta dicionário de cores das layers (para suporte ao ByLayer)
        dxf_layers = {}
        for lay in doc.layers:
            aci = lay.color
            if hasattr(lay, 'rgb') and lay.rgb is not None:
                rgb = lay.rgb
            else:
                rgb = aci2rgb(aci)
            dxf_layers[lay.dxf.name] = rgb

        feats = []
        for ent in entities:
            # Obtém o texto (TEXT ou MTEXT)
            txt = ent.plain_text() if ent.dxftype() == "MTEXT" else ent.dxf.text
            ins = ent.dxf.insert  # Ponto de inserção
            rot = getattr(ent.dxf, "rotation", 0.0)  # Rotação bruta

            if rot is None:
                rot = 0.0
            # Converte rotação para graus, se necessário
            if rot > 2 * math.pi:
                rot = rot
            else:
                rot = math.degrees(rot)
            rot = -rot  # Ajusta sinal para QGIS

            ht = getattr(ent.dxf, "height", None)  # Altura do texto

            # === Determina a cor ===
            if hasattr(ent, 'rgb') and ent.rgb is not None:
                r, g, b = ent.rgb  # True-color
            else:
                aci = ent.dxf.color
                if aci == 256:  # ByLayer: pega cor do layer do DXF
                    layer_name = ent.dxf.layer
                    r, g, b = dxf_layers.get(layer_name, (0, 0, 0))
                elif aci == 0:  # ByBlock (ou indefinido): preto
                    r, g, b = (0, 0, 0)
                else:
                    r, g, b = aci2rgb(aci)  # ACI normal

            # Cria feature com atributos
            f = QgsFeature(vl.fields())
            f.setAttributes([txt, ht, rot, ins.x, ins.y, r, g, b])
            f.setGeometry(QgsGeometry.fromPointXY(QgsPointXY(ins.x, ins.y)))
            feats.append(f)

        # Adiciona feições à camada
        if feats:
            pr.addFeatures(feats)
            vl.updateExtents()
            vl.triggerRepaint()

        # Configura os rótulos da camada
        pal = QgsPalLayerSettings()  # Cria configurações de rótulos
        pal.fieldName = "text"  # Define o campo usado para os rótulos (conteúdo do texto)
        pal.placement = Qgis.LabelPlacement.OverPoint  # Define o posicionamento dos rótulos sobre os pontos

        # Configura a rotação dos rótulos com base no campo "rotation"
        pal.dataDefinedProperties().setProperty(
            QgsPalLayerSettings.Property.Rotation,
            QgsProperty.fromField("rotation"))  # Vincula o campo "rotation" à propriedade de rotação

        # Configura o posicionamento dos rótulos com base no campo "rotation"
        expression_rotation = f'"rotation"'  # Usa o campo "rotation" diretamente como expressão
        pal.dataDefinedProperties().setProperty(
            QgsPalLayerSettings.Property.LabelRotation,
            QgsProperty.fromExpression(expression_rotation))  # Aplica a rotação à posição dos rótulos

        # Configura a cor dos rótulos com base nos campos r, g, b
        pal.dataDefinedProperties().setProperty(
            QgsPalLayerSettings.Property.Color,
            QgsProperty.fromExpression('color_rgba("r","g","b",255)'))  # Define a cor usando RGBA

        # Aplica as configurações de rótulos à camada
        vl.setLabeling(QgsVectorLayerSimpleLabeling(pal))
        vl.setLabelsEnabled(True)  # Habilita os rótulos

        # Define um símbolo de ponto "invisível" para evitar sobreposição visual
        symbol = QgsMarkerSymbol.createSimple({"name": "circle", "size": "0"})  # Cria símbolo circular com tamanho 0
        vl.renderer().setSymbol(symbol)  # Define o símbolo para o renderizador da camada

        return vl  # Retorna a camada vetorial criada

    def _carregar_dxf_via_ogr(self, file_path: str, layer_name: str ) -> tuple[QgsVectorLayer, ezdxf.layouts.Modelspace]:
        """
        Abre um DXF como camada de linhas no QGIS (tentando 3D e depois 2D) e também abre o mesmo
        arquivo via ezdxf para acessar o Modelspace. Se o DXF não tiver CRS, pede ao usuário.
        Retorna (QgsVectorLayer, modelspace).
        """
        def _tenta(gt: str) -> QgsVectorLayer:
            """Tenta abrir o DXF com o geometrytype informado."""
            uri = f"{file_path}|layername=entities|geometrytype={gt}"
            return QgsVectorLayer(uri, f"{layer_name}_lin", "ogr")

        # Tenta 3 D primeiro (LineString25D ≅ LineStringZ em QGIS)
        ogr_layer = _tenta("LineString25D")

        # Se não for válido, volta para 2 D
        if not ogr_layer.isValid():
            ogr_layer = _tenta("LineString")

        if not ogr_layer.isValid():
            raise RuntimeError(self.tr("Não foi possível abrir o DXF como LineString ou LineStringZ."))

        # Valida CRS, idêntico ao que você já tinha
        if not ogr_layer.crs().isValid():
            dlg = QgsProjectionSelectionDialog()
            if not dlg.exec():
                raise RuntimeError(self.tr("Operação cancelada pelo usuário."))
            chosen = dlg.crs()
            if not chosen.isValid():
                raise RuntimeError(self.tr("Nenhum SRC selecionado – operação cancelada."))
            ogr_layer.setCrs(chosen)

        # abre o DXF com ezdxf
        try:
            dxf_doc = ezdxf.readfile(file_path)
        except DXFValueError as e:
            raise ValueError(self.tr("Erro ao abrir o DXF (camada com nome inválido): {error}").format(error=e))

        return ogr_layer, dxf_doc.modelspace()

    def _extrair_cores_dxf(self, msp) -> list[tuple[int, int, int]]:
        """Extrai cores RGB das entidades DXF."""
        cores_dxf = []
        for ent in msp.query("LINE LWPOLYLINE POLYLINE"):
            if ent.rgb:
                cores_dxf.append(ent.rgb)
            else:
                try:
                    cores_dxf.append(aci2rgb(ent.dxf.color))
                except IndexError:
                    cores_dxf.append((0, 0, 0))
        return cores_dxf

    def _criar_camada_linhas(self, ogr_layer, layer_name, cores_dxf) -> QgsVectorLayer:
        """
        Cria camada temporária editável contendo:
          • Todos os campos relevantes herdados do DXF
          • Z   → elevação (float)
          • r,g,b → cor original
        """
        skip_fields = {"PaperSpace", "SubClasses", "Linetype", "EntityHandle", "Text"}
        keep_fields = [f for f in ogr_layer.fields() if f.name() not in skip_fields]

        tmp_layer = QgsVectorLayer(
            f"{QgsWkbTypes.displayString(ogr_layer.wkbType())}?crs={ogr_layer.crs().authid()}",
            f"{layer_name}_lin", "memory")
        tmp_dp = tmp_layer.dataProvider()

        # Novos campos
        fld_z = QgsField("Z",  QMetaType.Type.Double)
        fld_r = QgsField("r",  QMetaType.Type.Int)
        fld_g = QgsField("g",  QMetaType.Type.Int)
        fld_b = QgsField("b",  QMetaType.Type.Int)

        tmp_dp.addAttributes(keep_fields + [fld_z, fld_r, fld_g, fld_b])
        tmp_layer.updateFields()

        # índices úteis
        idx_z = tmp_layer.fields().indexFromName("Z")
        idx_r = tmp_layer.fields().indexFromName("r")
        idx_g = tmp_layer.fields().indexFromName("g")
        idx_b = tmp_layer.fields().indexFromName("b")

        # Cria feições
        feats_out = []
        for feat, cor in zip_longest(ogr_layer.getFeatures(), cores_dxf, fillvalue=(0, 0, 0)):
            if feat is None:
                break

            geom = feat.geometry()

            # Z
            if QgsWkbTypes.hasZ(geom.wkbType()):
                try:
                    z_val = next(geom.vertices()).z() # 1º vértice
                except StopIteration:
                    z_val = 0.0 # geometria vazia
            else:
                z_val = 0.0

            # Cores
            r, g, b = cor

            new_feat = QgsFeature(tmp_layer.fields())
            new_feat.setGeometry(geom)
            attrs = [feat[field.name()] for field in keep_fields] + [z_val, r, g, b]
            new_feat.setAttributes(attrs)
            feats_out.append(new_feat)

        tmp_dp.addFeatures(feats_out)
        tmp_layer.updateExtents()

        # Renderer por cor
        sym = QgsLineSymbol.createSimple({})
        sym.symbolLayer(0).dataDefinedProperties().setProperty(
            QgsSymbolLayer.Property.PropertyStrokeColor,
            QgsProperty.fromExpression('color_rgb("r","g","b")'))
        tmp_layer.setRenderer(QgsSingleSymbolRenderer(sym))

        # Oculta somente r/g/b
        for idx in (idx_r, idx_g, idx_b):
            tmp_layer.setEditorWidgetSetup(idx, QgsEditorWidgetSetup("Hidden", {}))
            cfg = tmp_layer.attributeTableConfig()
            cfg.setColumnHidden(idx, True)
            tmp_layer.setAttributeTableConfig(cfg)

        # (campo “Z” permanece visível para o usuário)
        return tmp_layer

    def _configurar_renderizacao_e_campos(self, tmp_layer: QgsVectorLayer):
        """Configura renderização com cores e oculta campos RGB."""
        sym = QgsLineSymbol.createSimple({})
        sym.symbolLayer(0).dataDefinedProperties().setProperty(
            QgsSymbolLayer.Property.PropertyStrokeColor,
            QgsProperty.fromExpression('color_rgb("r","g","b")'))
        tmp_layer.setRenderer(QgsSingleSymbolRenderer(sym))

        for color in ("r", "g", "b"):
            idx = tmp_layer.fields().indexFromName(color)
            tmp_layer.setEditorWidgetSetup(idx, QgsEditorWidgetSetup("Hidden", {}))
            cfg = tmp_layer.attributeTableConfig()
            cfg.setColumnHidden(idx, True)
            tmp_layer.setAttributeTableConfig(cfg)

    def _processar_dxf(self, file_path: str, layer_name: str, manter_original: bool = False) -> tuple[QgsVectorLayer | None, QgsVectorLayer | None]:
        """
        Processa arquivo DXF criando camadas editáveis (linhas e textos) para uso no QGIS.
        """
        # Exibe barra inicial indeterminada
        prep_msg = self.iface.messageBar().createMessage(self.tr("Preparando processamento do DXF, aguarde…"))
        prep_bar = QProgressBar()
        prep_bar.setMinimum(0)
        prep_bar.setMaximum(0)
        prep_bar.setMinimumWidth(300)
        prep_msg.layout().addWidget(prep_bar)
        widget_preparacao = self.iface.messageBar().pushWidget(prep_msg, Qgis.MessageLevel.Info)
        QCoreApplication.processEvents()

        try:
            ogr_layer, msp = self._carregar_dxf_via_ogr(file_path, layer_name)
        except (RuntimeError, ValueError) as e:
            self.iface.messageBar().popWidget(widget_preparacao)
            self.mostrar_mensagem(str(e), "Erro")
            return None, None

        self.iface.messageBar().popWidget(widget_preparacao)

        cores_dxf = self._extrair_cores_dxf(msp)

        progressBar, progressMsgBar = self.iniciar_progress_bar(
            ogr_layer, message=self.tr('Carregando entidades do DXF "{layer_name}", aguarde...').format(layer_name=layer_name))
        progressBar.setValue(0)

        tmp_layer = self._criar_camada_linhas(ogr_layer, layer_name, cores_dxf)

        # Atualiza progresso
        progressBar.setValue(ogr_layer.featureCount())
        QCoreApplication.processEvents()

        self._configurar_renderizacao_e_campos(tmp_layer)

        # Carrega textos DXF
        text_layer = None
        try:
            text_layer = self.carregar_texto_dxf(
                file_path, f"{layer_name}_txt", ogr_layer.crs().authid())
        except Exception as exc:
            self.mostrar_mensagem(self.tr("Erro ao ler TEXTOS do DXF: {error}").format(error=exc), "Erro")

        try:
            self.iface.messageBar().popWidget(progressMsgBar)
        except RuntimeError:
            pass  # nosec B110

        del ogr_layer

        return tmp_layer, text_layer

    def open_context_menu(self, position):
        """
        Abre um menu de contexto para a camada selecionada na árvore de visualização de camadas, fornecendo opções rápidas como mudar a espessura da linha e abrir propriedades da camada.

        Parâmetros:
        - position (QPoint): A posição do cursor do mouse no momento do clique direito, usada para posicionar o menu de contexto.

        Funcionalidades:
        - Verifica se existe algum item selecionado na árvore de camadas.
        - Cria um menu de contexto com opções específicas relacionadas à camada selecionada, como alterar a espessura da linha ou abrir as propriedades da camada.
        - Exibe o menu de contexto na posição do cursor e aguarda o usuário escolher uma ação.
        - Responde à seleção do usuário, chamando a função apropriada com base na ação escolhida.

        Atribuição no código:
        Facilita o acesso rápido às funções de modificação e visualização de propriedades das camadas diretamente da árvore de visualização, melhorando a eficiência do fluxo de trabalho e permitindo ajustes rápidos sem necessidade de navegar por menus adicionais. Essencial para a usabilidade e acessibilidade em interfaces ricas em funcionalidades.
        """
        # Obtém os índices dos itens selecionados na lista de camadas
        indexes = self.dlg.treeViewListaLinha.selectedIndexes() # Acessa os índices selecionados no treeView
        if indexes:
            menu = QMenu() # Cria um objeto QMenu para o menu de contexto
            change_thickness_action = menu.addAction(self.tr("Espessura da Linha")) # Adiciona uma ação para mudar a espessura da linha
            layer_properties_action = menu.addAction(self.tr("Abrir Propriedades da Camada")) # Adiciona uma ação para abrir propriedades da camada
            action = menu.exec(self.dlg.treeViewListaLinha.viewport().mapToGlobal(position)) # Exibe o menu e aguarda uma ação ser selecionada
            if action == layer_properties_action: # Verifica se a ação selecionada é abrir propriedades da camada
                self.abrir_layer_properties(indexes[0]) # Chama função para abrir propriedades da camada selecionada
            elif action == change_thickness_action:  # Verifica se a ação selecionada é alterar a espessura da linha
                self.prompt_for_new_line_thickness(indexes[0]) # Chama função para ajustar a espessura da linha

    def prompt_for_new_line_thickness(self, index):
        """
        Abre um diálogo para que o usuário possa ajustar a espessura da linha de uma camada selecionada no QGIS.

        Parâmetros:
        - index (QModelIndex): O índice da camada selecionada no QTreeView.

        Funcionalidades:
        - Recupera o ID da camada a partir do item selecionado no QTreeView usando o UserRole + 1.
        - Busca a camada correspondente no projeto QGIS usando o ID recuperado.
        - Verifica se a camada foi encontrada e prossegue se for positivo.
        - Obtém a espessura atual da linha da camada para uso como valor inicial no diálogo.
        - Cria um diálogo personalizado com um QDoubleSpinBox para permitir ao usuário definir uma nova espessura da linha.
        - O diálogo permite definir a espessura da linha de 0 a 10 com passos de 0.1 e duas casas decimais.
        - Exibe o diálogo e aplica a nova espessura à camada se o usuário confirmar a mudança.

        Atribuição no código:
        Facilita a personalização visual das camadas no projeto QGIS, permitindo ajustes finos na apresentação das linhas, o que é crucial para a clareza visual e a precisão em representações cartográficas. A função melhora a interatividade do usuário com o QGIS, oferecendo controle direto sobre as propriedades estilísticas das camadas.
        """
        # Recupera o ID da camada do item selecionado no QTreeView usando o UserRole + 1
        layer_id = index.model().itemFromIndex(index).data(Qt.ItemDataRole.UserRole + 1)
        # Busca a camada correspondente no projeto QGIS usando o ID
        layer = QgsProject.instance().mapLayer(layer_id)
        if layer:  # Verifica se a camada foi encontrada
            # Obtém a espessura atual da linha da camada
            current_thickness = self.get_current_line_thickness(layer)
            # Cria um diálogo personalizado para ajuste de espessura
            dlg = QDialog(self.dlg)
            dlg.setWindowTitle(self.tr("Alterar Espessura da Linha"))  # Define o título do diálogo
            layout = QVBoxLayout(dlg)  # Cria um layout vertical para o diálogo
            # Configura um QDoubleSpinBox para escolha da nova espessura
            spinBox = QDoubleSpinBox(dlg)
            spinBox.setRange(0, 10)  # Define o intervalo de valores
            spinBox.setSingleStep(0.1)  # Define o incremento de ajuste
            spinBox.setValue(current_thickness)  # Define o valor inicial com a espessura atual
            spinBox.setDecimals(2)  # Define a precisão decimal
            layout.addWidget(spinBox)  # Adiciona o QDoubleSpinBox ao layout
            # Cria um layout horizontal para os botões
            buttonLayout = QHBoxLayout()
            okButton = QPushButton(self.tr("OK"), dlg)  # Cria um botão de OK
            okButton.clicked.connect(dlg.accept)  # Conecta o botão OK à ação de aceitar o diálogo
            buttonLayout.addWidget(okButton)  # Adiciona o botão OK ao layout de botões
            layout.addLayout(buttonLayout)  # Adiciona o layout de botões ao layout principal
            # Exibe o diálogo e espera pela ação do usuário
            if dlg.exec():  # Se o usuário clicar em OK
                new_thickness = spinBox.value()  # Obtém o novo valor da espessura
                # Aplica a nova espessura à camada se o usuário confirmar
                self.apply_new_line_thickness(layer, new_thickness)

    def _collect_symbols(self, layer):
        """
        Retorna uma lista de símbolos associados à camada, independentemente do tipo de renderizador.

        Essa função identifica o tipo de renderizador utilizado pela camada e extrai corretamente os
        símbolos associados, tratando os seguintes casos:

        1. Renderizadores com o método `.symbols(QgsRenderContext)` (ex: Categorized, Graduated).
        2. Renderizadores do tipo `QgsSingleSymbolRenderer`, que possuem `.symbol()`.
        3. Renderizadores embutidos (`QgsEmbeddedSymbolRenderer`), que usam `.embeddedSymbol()`.

        Retorna
        list[QgsSymbol]
            Lista de símbolos associados ao renderizador da camada. Pode estar vazia.
        """
        renderer = layer.renderer()             # Obtém o renderizador da camada
        symbols = []                            # Inicializa a lista de símbolos

        # Renderizadores que implementam .symbols(context)
        if hasattr(renderer, "symbols"):
            symbols = renderer.symbols(QgsRenderContext())  # Usa symbols() com contexto de renderização

        # Renderizador de símbolo único (SingleSymbolRenderer)
        elif hasattr(renderer, "symbol"):
            symbols = [renderer.symbol()]       # Acessa o símbolo diretamente

        # Renderizador embutido (EmbeddedSymbolRenderer)
        elif hasattr(renderer, "embeddedSymbol"):
            sym = renderer.embeddedSymbol()     # Obtém o símbolo embutido
            if sym:
                symbols = [sym]                 # Adiciona à lista se não for None

        return symbols                          # Retorna a lista final de símbolos (pode estar vazia)

    def get_current_line_thickness(self, layer):
        """
        Retorna a espessura (largura da linha) do primeiro símbolo associado à camada.

        A função tenta obter os símbolos aplicados à camada usando `_collect_symbols()`.
        Caso exista pelo menos um símbolo com suporte a largura (`setWidth`), retorna seu valor.
        Se não houver símbolos aplicáveis ou a camada não tiver simbologia de linha, retorna 0.0.

        Parâmetros
        layer : QgsVectorLayer
            Camada vetorial cujo estilo será consultado.

        Retorno
        float
            Valor da espessura do símbolo de linha, ou 0.0 se não aplicável.
        """
        syms = self._collect_symbols(layer)     # Obtém todos os símbolos da camada
        return syms[0].width() if syms else 0.0 # Retorna a espessura do primeiro símbolo, ou 0.0 se não houver

    def apply_new_line_thickness(self, layer, new_thickness):
        """
        Aplica uma nova espessura de linha a todos os símbolos da camada fornecida.

        A função varre todos os símbolos associados ao renderizador da camada usando `_collect_symbols()`
        e aplica o novo valor de espessura (largura de linha) onde for possível. Em seguida, força
        a atualização visual da camada para refletir as alterações.

        Parâmetros
        layer : QgsVectorLayer
            Camada vetorial que terá seus símbolos ajustados.

        new_thickness : float
            Novo valor de espessura (largura da linha) a ser aplicado.
        """
        for sym in self._collect_symbols(layer):       # Itera sobre todos os símbolos da camada
            if hasattr(sym, "setWidth"):               # Garante que o símbolo suporta ajuste de largura
                sym.setWidth(new_thickness)            # Define a nova espessura no símbolo

        layer.triggerRepaint()                         # Força a camada a repintar-se visualmente no mapa

    def abrir_layer_properties(self, index):
        """
        Abre a janela de propriedades para uma camada específica selecionada no QGIS, permitindo que os usuários ajustem configurações detalhadas da camada.

        Parâmetros:
        - index (QModelIndex): O índice no treeView que representa a camada selecionada.

        Funcionalidades:
        - Recupera o ID da camada a partir do índice fornecido.
        - Busca a camada correspondente no projeto QGIS usando o ID.
        - Se a camada for encontrada, abre a janela de propriedades da camada na interface do QGIS, permitindo ao usuário acessar e modificar uma ampla variedade de configurações da camada.

        Atribuição no código:
        Essencial para oferecer acesso direto às configurações avançadas de camadas, como simbologia, rótulos, e configurações de renderização. Facilita a gestão detalhada das camadas, melhorando a eficiência e a precisão na personalização das propriedades das camadas. A função é particularmente útil em fluxos de trabalho de gestão de dados geográficos, onde ajustes frequentes nas configurações das camadas são comuns.
        """
        # Obtém o ID da camada do item selecionado no treeView
        layer_id = index.model().itemFromIndex(index).data()
        layer = QgsProject.instance().mapLayer(layer_id)
        if layer:
            self.iface.showLayerProperties(layer)

    def abrir_dialogo_selecao_campos(self):
        """
        Abre o diálogo para gerenciar etiquetas (campos, cores, visibilidade) da camada selecionada.
        Corrigido:
          - Usa currentIndex/coluna 0
          - fieldColors/fieldVisibility agora são por layer_id
          - Não vaza alterações no Cancelar (commita só se Accepted)
        """
        # Pega o índice atual (mais confiável que selectedIndexes)
        index = self.dlg.treeViewListaLinha.currentIndex()
        if not index.isValid():
            # fallback: tenta selectedIndexes (coluna 0)
            selected = [ix for ix in self.dlg.treeViewListaLinha.selectedIndexes() if ix.column() == 0]
            if not selected:
                return
            index = selected[0]

        item = index.model().itemFromIndex(index)
        if item is None:
            return

        layer_id = item.data()
        layer = QgsProject.instance().mapLayer(layer_id)
        if not layer:
            return

        # MIGRAÇÃO suave (se ainda estiver no formato antigo "flat")
        # Formato novo: self.fieldColors[layer_id] -> dict{field: cor}
        if not isinstance(getattr(self, "fieldColors", None), dict):
            self.fieldColors = {}
        if not isinstance(getattr(self, "fieldVisibility", None), dict):
            self.fieldVisibility = {}

        if layer_id not in self.fieldColors or not isinstance(self.fieldColors.get(layer_id), dict):
            # se estava no formato antigo (field->cor), migra só para esta layer
            if self.fieldColors and all(isinstance(v, (str, QColor)) for v in self.fieldColors.values()):
                self.fieldColors = {layer_id: dict(self.fieldColors)}
            else:
                self.fieldColors[layer_id] = {}

        if layer_id not in self.fieldVisibility or not isinstance(self.fieldVisibility.get(layer_id), dict):
            # se estava no formato antigo (field->bool), migra só para esta layer
            if self.fieldVisibility and all(isinstance(v, bool) for v in self.fieldVisibility.values()):
                self.fieldVisibility = {layer_id: dict(self.fieldVisibility)}
            else:
                self.fieldVisibility[layer_id] = {}

        layer_colors = self.fieldColors.get(layer_id, {})
        layer_vis = self.fieldVisibility.get(layer_id, {})

        # IMPORTANTÍSSIMO: passa CÓPIAS para o diálogo (Cancelar não vaza mudanças)
        dialog = GerenciarEtiquetasDialog(layer, dict(layer_colors), dict(layer_vis), self.iface, parent=self.dlg)

        if dialog.exec() == QDialog.DialogCode.Accepted:
            # Commita somente se o usuário aplicou
            self.fieldColors[layer_id] = dict(dialog.fieldColors)
            self.fieldVisibility[layer_id] = dict(dialog.fieldVisibility)

    def clone_layer(self):
        """
        Clona uma camada selecionada na interface do usuário do QGIS, permitindo ao usuário criar uma cópia exata de uma camada existente dentro do projeto.

        Funcionalidades:
        - Verifica se uma camada está selecionada na árvore de visualização de camadas.
        - Recupera o identificador (ID) da camada selecionada para localizar a camada no projeto QGIS.
        - Verifica se a camada selecionada é válida. Se não for, exibe uma mensagem de erro e encerra a função.
        - Utiliza um gerenciador de clonagem para clonar a camada, oferecendo ao usuário a opção de configurar parâmetros específicos para a clonagem, como cópia de atributos e configurações de estilo.
        - Atualiza a visualização da lista de camadas na interface após a clonagem para refletir a nova camada adicionada.

        Atribuição no código:
        Essencial para operações que requerem duplicação de camadas, permitindo aos usuários multiplicar camadas eficientemente sem recriar manualmente as configurações. Facilita a gestão de versões e experimentações com diferentes configurações de uma mesma camada, melhorando a eficácia do trabalho em projetos complexos de mapeamento e análise geoespacial.
        """
        # Obtém os índices das camadas selecionadas na interface do usuário
        selected_indexes = self.dlg.treeViewListaLinha.selectedIndexes()

        # Verifica se alguma camada foi realmente selecionada
        if not selected_indexes:
            # Exibe uma mensagem de erro se nenhuma camada estiver selecionada
            self.mostrar_mensagem(self.tr("Nenhuma camada selecionada."), "Erro")
            return # Encerra a execução da função

        # Obtém o primeiro índice selecionado, assumindo uma única seleção
        selected_index = selected_indexes[0]
        # Recupera o ID da camada a partir do índice selecionado
        layer_id = selected_index.model().itemFromIndex(selected_index).data()
        # Busca a camada no projeto QGIS usando o ID recuperado
        layer_to_clone = QgsProject.instance().mapLayer(layer_id)

        if not layer_to_clone: # Verifica se a camada recuperada é válida
            self.mostrar_mensagem(self.tr("A camada selecionada não é válida."), "Erro")
            return # Encerra a execução da função

        # Cria uma instância do CloneManager para gerenciar o processo de clonagem
        clone_manager = CloneManager(self, layer_to_clone)
        clone_manager.show_clone_options() # Exibe as opções de clonagem ao usuário

        # Atualiza a lista de camadas no treeView
        self.atualizar_treeView_lista_linha()

    def iniciar_progress_bar(self, layer: QgsVectorLayer = None, message: str = None):
        """
        Inicia e exibe uma barra de progresso na Message Bar do QGIS.

        - Estilo mantido como na sua função “original” (fundo #cddbde, chunk azul, etc.)
        - Mensagem padrão genérica (não fixa em DXF)
        - Define máximo pelo featureCount quando disponível
        - Retorna (QProgressBar, progressMessageBar) para atualização externa
        """
        if message is None:
            if layer is not None:
                message = self.tr("Processando: {layer_name}").format(layer_name=layer.name())
            else:
                message = self.tr("Processando, aguarde...")

        progressMessageBar = self.iface.messageBar().createMessage(message)

        progressBar = QProgressBar()
        progressBar.setAlignment(Qt.AlignmentFlag.AlignLeft | Qt.AlignmentFlag.AlignVCenter)
        progressBar.setTextVisible(True)
        progressBar.setFormat(self.tr("%p% - %v de %m Feições processadas"))
        progressBar.setMinimum(0)
        progressBar.setValue(0)
        progressBar.setMinimumWidth(300)

        if layer is not None:
            try:
                progressBar.setMaximum(max(0, int(layer.featureCount())))
            except Exception:
                progressBar.setMaximum(0)
        else:
            progressBar.setMaximum(0)

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
                min-height: 5px;
            }
        """)

        progressMessageBar.layout().addWidget(progressBar)
        self.iface.messageBar().pushWidget(progressMessageBar, Qgis.MessageLevel.Info, duration=0)

        return progressBar, progressMessageBar

    def calcular_angulo_entre_pontos(self, ponto_inicial, ponto_final):
        """
        Calcula o ângulo entre dois pontos em graus, considerando o ponto inicial como referência.
        O resultado é ajustado para ficar no intervalo de 0 a 360 graus.

        Parâmetros:
        ponto_inicial (QgsPointXY): O ponto de partida para o cálculo do ângulo.
        ponto_final (QgsPointXY): O ponto de chegada para o cálculo do ângulo.

        Retorna:
        float: O ângulo entre os dois pontos em graus, ajustado para estar no intervalo de 0 a 360 graus.
        """
        # Calcula o ângulo em radianos e converte para graus
        angle = math.degrees(math.atan2(ponto_final.y() - ponto_inicial.y(), ponto_final.x() - ponto_inicial.x()))
        angle = (angle + 180) % 360 # Ajusta o ângulo para garantir que seja positivo
        if 90 < angle < 180: # Se o ângulo estiver no segundo quadrante, ajusta para o terceiro quadrante
            angle += 180
        elif 180 <= angle < 270: # Se o ângulo estiver no terceiro quadrante, ajusta para o quarto quadrante
            angle -= 180
        return angle % 360 # Retorna o ângulo ajustado para estar dentro do intervalo de 0 a 360 graus

    def calcular_rotulo_centralizado(self, geometry):
        """
        Identifica o segmento mais longo de uma geometria e calcula tanto seu ponto médio quanto o ângulo.

        Parâmetros:
        - geometry (QgsGeometry): A geometria sobre a qual os cálculos serão realizados.

        Retorna:
        - tuple: Retorna uma tupla contendo o ângulo e o ponto central (QgsPointXY) do segmento mais longo.

        Detalhes:
        - A função verifica primeiro se a geometria é multipartida (composta por várias linhas) ou uma única linha.
        - Para cada linha da geometria, a função itera sobre os segmentos formados por pontos consecutivos.
        - Para cada segmento, a função calcula o comprimento e, se este for o maior até então encontrado, atualiza as informações de comprimento máximo,
          além de calcular e armazenar o ponto médio e o ângulo desse segmento.
        - O ângulo é calculado a partir da função `calcular_angulo_entre_pontos`, que presume existir em algum local do mesmo objeto ou módulo.

        Exemplo de utilização:
        - A função pode ser utilizada para otimizar a posição de rótulos em mapas ou outras representações gráficas,
          colocando o rótulo no ponto médio do maior segmento de uma estrada, curso de rio, ou outra entidade linear.
        """
        max_length = -1  # Inicializa a variável para armazenar o comprimento máximo encontrado
        longest_segment_center = None  # Inicializa a variável para armazenar o centro do segmento mais longo
        angle = 0  # Inicializa o ângulo do segmento mais longo

        # Verifica se a geometria é multipartida
        if geometry.isMultipart():
            lines = geometry.asMultiPolyline() # Obtém as linhas da geometria multipartida
        else:
            lines = [geometry.asPolyline()] # Trata a geometria simples como uma lista de uma linha

        # Itera sobre cada linha na geometria
        for line in lines:
            # Itera sobre cada segmento na linha (ponto inicial até o penúltimo ponto)
            for i in range(len(line) - 1):
                segment_start = QgsPointXY(line[i]) # Ponto inicial do segmento
                segment_end = QgsPointXY(line[i + 1]) # Ponto final do segmento
                segment_length = segment_start.distance(segment_end) # Calcula o comprimento do segmento

                # Verifica se o comprimento atual é o maior encontrado até agora
                if segment_length > max_length:
                    max_length = segment_length # Atualiza o comprimento máximo
                    # Calcula o ponto médio do segmento
                    mid_x = (segment_start.x() + segment_end.x()) / 2
                    mid_y = (segment_start.y() + segment_end.y()) / 2
                    longest_segment_center = QgsPointXY(mid_x, mid_y)
                    # Calcula o ângulo do segmento usando a função definida anteriormente
                    angle = self.calcular_angulo_entre_pontos(segment_start, segment_end)

        # Retorna o ângulo e o centro do segmento mais longo
        return angle, longest_segment_center

    def calcular_rotulo_equidistante(self, geometry, distancia_intervalo):
        """
        Identifica o segmento mais longo de uma geometria e calcula tanto seu ponto médio quanto o ângulo.

        Parâmetros:
        - geometry (QgsGeometry): A geometria sobre a qual os cálculos serão realizados.

        Retorna:
        - tuple: Retorna uma tupla contendo o ângulo e o ponto central (QgsPointXY) do segmento mais longo.

        Detalhes:
        - A função verifica primeiro se a geometria é multipartida (composta por várias linhas) ou uma única linha.
        - Para cada linha da geometria, a função itera sobre os segmentos formados por pontos consecutivos.
        - Para cada segmento, a função calcula o comprimento e, se este for o maior até então encontrado, atualiza as informações de comprimento máximo,
          além de calcular e armazenar o ponto médio e o ângulo desse segmento.
        - O ângulo é calculado a partir da função `calcular_angulo_entre_pontos`, que presume existir em algum local do mesmo objeto ou módulo.

        Exemplo de utilização:
        - A função pode ser utilizada para otimizar a posição de rótulos em mapas ou outras representações gráficas,
          colocando o rótulo no ponto médio do maior segmento de uma estrada, curso de rio, ou outra entidade linear.
        """
        posicoes_rotulos = [] # Inicializa a lista que armazenará as posições dos rótulos
        
        # Verifica se a geometria é multipartida
        if geometry.isMultipart():
            lines = geometry.asMultiPolyline() # Obtém as linhas da geometria multipartida
        else:
            lines = [geometry.asPolyline()] # Trata a geometria simples como uma lista de uma linha

        for line in lines: # Itera sobre cada linha na geometria
            distancia_acumulada_desde_ultimo_rotulo = 0 # Inicia a distância acumulada desde o último rótulo

            # Itera sobre cada segmento na linha
            for i in range(len(line) - 1):
                segment_start = QgsPointXY(line[i]) # Ponto inicial do segmento
                segment_end = QgsPointXY(line[i + 1])  # Ponto final do segmento
                segment_length = segment_start.distance(segment_end) # Calcula o comprimento do segmento

                # Se for o primeiro segmento ou após adicionar um rótulo
                if i == 0 or distancia_acumulada_desde_ultimo_rotulo == 0:
                    angle = self.calcular_angulo_entre_pontos(segment_start, segment_end)
                    posicoes_rotulos.append((segment_start, angle))

                # Enquanto a distância acumulada e o comprimento do segmento forem suficientes para adicionar outro rótulo
                while distancia_acumulada_desde_ultimo_rotulo + segment_length >= distancia_intervalo:
                    # Calcula o excesso além do último rótulo
                    excesso = distancia_intervalo - distancia_acumulada_desde_ultimo_rotulo
                    ratio = excesso / segment_length  # Calcula a proporção do segmento que corresponde ao excesso
                    x = segment_start.x() + ratio * (segment_end.x() - segment_start.x()) # Calcula a posição x equidistante
                    y = segment_start.y() + ratio * (segment_end.y() - segment_start.y()) # Calcula a posição Y equidistante
                    angle = self.calcular_angulo_entre_pontos(segment_start, QgsPointXY(x, y)) # Calcula o ângulo no novo ponto
                    posicoes_rotulos.append((QgsPointXY(x, y), angle)) # Adiciona a nova posição e o ângulo
                    segment_start = QgsPointXY(x, y)  # Atualiza o ponto inicial do segmento para continuar a partir do novo ponto
                    segment_length -= excesso # Reduz o comprimento restante do segmento
                    distancia_acumulada_desde_ultimo_rotulo = 0 # Reseta a distância acumulada

                # Atualiza a distância acumulada com o comprimento restante do segmento
                distancia_acumulada_desde_ultimo_rotulo += segment_length

        # Se sobrou uma distância acumulada no final da linha, adiciona o último ponto
            if distancia_acumulada_desde_ultimo_rotulo > 0 and distancia_acumulada_desde_ultimo_rotulo < distancia_intervalo:
                final_point = QgsPointXY(line[-1]) # Último ponto da linha
                penultimate_point = QgsPointXY(line[-2]) # Penúltimo ponto da linha
                final_angle = self.calcular_angulo_entre_pontos(penultimate_point, final_point) # Calcula o ângulo no último segmento
                posicoes_rotulos.append((final_point, final_angle)) # Adiciona o último ponto e o ângulo
        
        return posicoes_rotulos # Retorna a lista de posições dos rótulos

    def calcular_rotulo_segmentado(self, geometry):
        """
        Calcula o ponto médio e o ângulo de cada segmento de uma geometria, normalmente utilizada para posicionar rótulos.

        Parâmetros:
        - geometry (QgsGeometry): A geometria sobre a qual os cálculos serão realizados.

        Retorna:
        - list: Uma lista de tuplas, cada uma contendo um objeto QgsPointXY (ponto médio do segmento) e um ângulo (orientação do segmento).

        Funcionalidades:
        - Verifica se a geometria é composta por múltiplas partes (multipartida) ou uma única linha.
        - Itera sobre cada linha da geometria.
        - Para cada linha, itera sobre cada segmento, calculando o ponto médio e o ângulo de inclinação.
        - Armazena cada ponto médio e ângulo em uma lista para uso posterior, como na colocação de rótulos.

        Utilização:
        - Esta função é especialmente útil em aplicações GIS onde rótulos precisam ser alinhados de maneira precisa com segmentos de linha.
          Pode ser usada para rotular estradas, rios, ou outras entidades lineares em mapas, garantindo que os rótulos sejam facilmente legíveis
          e esteticamente posicionados.
        """
        posicoes_rotulos = []  # Inicializa a lista que armazenará as posições dos rótulos

        # Verifica se a geometria é multipartida
        posicoes_rotulos = []
        if geometry.isMultipart():
            lines = geometry.asMultiPolyline() # Obtém as linhas da geometria multipartida
        else:
            lines = [geometry.asPolyline()] # Trata a geometria simples como uma lista de uma linha

        # Itera sobre cada linha na geometria
        for line in lines:
            # Itera sobre cada segmento na linha (ponto inicial até o penúltimo ponto)
            for i in range(len(line) - 1):
                segment_start = QgsPointXY(line[i]) # Ponto inicial do segmento
                segment_end = QgsPointXY(line[i + 1]) # Ponto final do segmento
                mid_x = (segment_start.x() + segment_end.x()) / 2
                mid_y = (segment_start.y() + segment_end.y()) / 2
                mid_point = QgsPointXY(mid_x, mid_y) # Cria o objeto QgsPointXY para o ponto médio

                # Calcula o ângulo do segmento usando a função definida anteriormente
                angle = self.calcular_angulo_entre_pontos(segment_start, segment_end)
                # Adiciona o ponto médio e o ângulo à lista de posições de rótulos
                posicoes_rotulos.append((mid_point, angle))

        return posicoes_rotulos # Retorna a lista de posições dos rótulos

    def exportar_rotulos_para_dxf(self, layer, msp, selected_attribute, rotulo_modo, distancia_intervalo, text_style=None):
        """
        Exporta rótulos para um arquivo DXF com base no modo de rotulagem especificado,
        utilizando as propriedades de texto fornecidas e os atributos selecionados de cada feição da camada.

        Parâmetros:
        - layer (QgsVectorLayer): Camada de onde os atributos e geometrias serão extraídos.
        - msp (Modelspace): Espaço de modelo do arquivo DXF onde os textos serão inseridos.
        - selected_attribute (str): Nome do atributo que será usado como texto do rótulo.
        - rotulo_modo (str): Modo de rotulagem ('Centralizado', 'Segmentado', 'Equidistante').
        - distancia_intervalo (float): Distância entre rótulos no modo 'Equidistante'.
        - text_style (dict, optional): Dicionário contendo estilo de texto como fonte e tamanho.

        Funcionalidades:
        - Verifica se o modo de rotulagem foi definido.
        - Itera sobre cada feição na camada para extrair a geometria e o valor do atributo selecionado.
        - Determina o modo de rotulagem e calcula as posições e ângulos correspondentes para os rótulos.
        - Adiciona cada rótulo ao espaço de modelo do arquivo DXF com os atributos de texto configurados.
        """
        # Verifica se o modo de rotulagem foi definido
        if not rotulo_modo:
            return  # Encerra a função se nenhum modo de rotulagem foi especificado

        # Itera sobre cada feição na camada
        for feat in layer.getFeatures():
            geom = feat.geometry() # Extrai a geometria da feição
            attribute_value = feat.attribute(selected_attribute) # Extrai o valor do atributo selecionado
            posicoes_rotulos = []  # Inicializa a lista que armazenará as posições e ângulos dos rótulos

            # Determina o modo de rotulagem e calcula as posições e ângulos correspondentes
            if rotulo_modo == "Centralizado":
                angle, position = self.calcular_rotulo_centralizado(geom)  # Calcula posição centralizada e ângulo
                posicoes_rotulos.append((position, angle)) # Adiciona a posição e ângulo à lista
            elif rotulo_modo == "Segmentado":
                posicoes_rotulos = self.calcular_rotulo_segmentado(geom)  # Calcula posições e ângulos para cada segmento
            elif rotulo_modo == "Equidistante" and distancia_intervalo:
                posicoes_rotulos = self.calcular_rotulo_equidistante(geom, distancia_intervalo) # Calcula posições equidistantes

            # Adiciona cada rótulo ao espaço de modelo do arquivo DXF
            for position, angle in posicoes_rotulos:
                msp.add_text(
                    str(attribute_value), # Converte o valor do atributo para string
                    dxfattribs={
                        'insert': (position.x(), position.y()), # Define a posição de inserção do texto
                        'height': text_style['size'], # Define a altura do texto baseada no estilo
                        'rotation': angle, # Define a rotação do texto baseada no ângulo calculado
                        'style': text_style['font'], # Define o estilo da fonte baseado no estilo
                        'layer': selected_attribute, # Define a camada do DXF baseada no atributo selecionado
                        'color': text_style.get('aci_color', 7)  # Usa o índice ACI ou padrão se não definido
                    })

    def definir_estilos_de_texto(self, doc, text_style):
        """
        Define os estilos de texto para um documento DXF, criando novos estilos conforme necessário.

        Parâmetros:
        - doc (ezdxf.document.Drawing): O documento DXF onde o estilo de texto será definido.
        - text_style (dict): Dicionário contendo as propriedades de estilo do texto, como a fonte.

        Funcionalidades:
        - Verifica se o estilo de texto especificado já existe no documento.
        - Se não existir, cria um novo estilo com os atributos fornecidos.
        """
        # Verifica se o estilo de texto já existe no documento
        if text_style['font'] not in doc.styles:
            # Cria um novo estilo no documento DXF com o nome e os atributos de fonte especificados
            doc.styles.new(name=text_style['font'], dxfattribs={'font': text_style['font']})

    def exportar_para_dxf(self):
        """
        Exporta uma camada selecionada para um arquivo DXF, utilizando diálogo de exportação para configurar detalhes.

        Funcionalidades:
        - Verifica se uma camada foi selecionada.
        - Valida se a camada selecionada é adequada para exportação (deve ser espacial e de geometria de linhas).
        - Abre um diálogo para o usuário configurar opções de exportação, como campo selecionado, atributos, estilo de texto, etc.
        - Executa a exportação para DXF se as configurações forem aceitas no diálogo.
        - Exibe mensagens de erro ou sucesso conforme o resultado da operação.
        """
        # Obtém o índice do item atualmente selecionado na árvore de camadas
        index = self.dlg.treeViewListaLinha.currentIndex()
        # Verifica se o índice é válido (ou seja, se há uma camada selecionada)
        if not index.isValid():
            self.mostrar_mensagem(self.tr("Nenhuma camada selecionada."), "Erro")
            return

        # Obtém o ID da camada a partir do índice selecionado
        layer_id = index.model().itemFromIndex(index).data()
        # Busca a camada no projeto QGIS pelo ID
        layer = QgsProject.instance().mapLayer(layer_id)
        # Verifica se a camada é válida, espacial e do tipo de geometria de linhas
        if not layer or not layer.isSpatial() or layer.geometryType() != QgsWkbTypes.GeometryType.LineGeometry:
            self.mostrar_mensagem(self.tr("A camada selecionada não é válida ou não é uma camada de linhas."), "Erro")
            return

        # Cria e exibe o diálogo de exportação
        dialog = ExportDialogDXF(layer, self.iface.mainWindow(), self.obter_cor_linha(layer))
        if dialog.exec() == QDialog.DialogCode.Accepted:
            # Obtém as configurações do diálogo
            selected_field, selected_attribute, scale_factor = dialog.get_Values()
            rotulo_modo, distancia_intervalo = dialog.get_labeling_options()
            text_style = dialog.get_text_style()  # Acessa o estilo de texto configurado
            linetype_selected = dialog.get_selected_linetype()  # Obtém o linetype selecionado
            # Solicita ao usuário escolher o local para salvar o arquivo DXF
            filePath = self.escolher_local_para_salvar(layer.name() + ".dxf", "DXF Files (*.dxf)")
            if filePath:
                start_time = time.time()  # Inicia o cronômetro para medir a duração da exportação
                # Realiza a exportação com as configurações obtidas
                self.realizar_exportacao_para_dxf(layer, filePath, selected_field, selected_attribute, rotulo_modo, distancia_intervalo, text_style, dialog, linetype_selected, scale_factor)
                duration = time.time() - start_time  # Calcula a duração da operação

                # Exibir mensagem de sucesso com o tempo de execução e caminhos dos arquivos
                self.mostrar_mensagem(self.tr("Camada exportada para DXF em {duration:.2f} segundos").format(duration=duration), "Sucesso", caminho_pasta=os.path.dirname(filePath), caminho_arquivos=filePath)
        else:
            # Exibe mensagem de cancelamento se o diálogo de exportação não for aceito
            self.mostrar_mensagem(self.tr("Exportação cancelada."), "Info")

    def obter_dxf_atributos_cor(self, feat, layer, linetype_selected, selected_field):
        """
        Obtém os atributos DXF relacionados à cor com base na simbologia da camada.

        Parâmetros:
        - feat (QgsFeature): A feição atual a ser processada.
        - layer (QgsVectorLayer): A camada de onde a feição foi extraída.
        - linetype_selected (str): O tipo de linha selecionado para exportação (ex.: CONTINUOUS, PERSONALIZAR).
        - selected_field (str): O campo selecionado para a camada DXF.

        Funcionalidades:
        - Verifica se o renderizador da camada é categorizado ou de símbolo único.
        - Avalia expressões para renderizadores categorizados para determinar o valor da categoria.
        - Converte a cor do símbolo associado à feição para o formato DXF (RGB).
        - Retorna um dicionário contendo a cor em formato DXF, o tipo de linha e o nome da camada.
        """
        symbol = None
        dxf_color = ezdxf.colors.rgb2int((255, 255, 255))  # Cor padrão (branco)

        # Verifica se o renderizador da camada é categorizado
        if isinstance(layer.renderer(), QgsCategorizedSymbolRenderer):
            renderer = layer.renderer()
            class_attribute = renderer.classAttribute()

            # Avalia a expressão para obter o valor da categoria
            expression = QgsExpression(class_attribute)
            context = QgsExpressionContext()
            context.appendScopes(QgsExpressionContextUtils.globalProjectLayerScopes(layer))
            context.setFeature(feat)
            
            class_value = expression.evaluate(context)
            
            # Encontra a categoria correspondente ao valor da feição
            for category in renderer.categories():
                if category.value() == class_value:
                    symbol = category.symbol()
                    break

        elif isinstance(layer.renderer(), QgsSingleSymbolRenderer):
            # Para renderização de símbolo único, obtém a cor do símbolo
            symbol = layer.renderer().symbol()

        # Se encontrou um símbolo, converte a cor RGB para o formato DXF
        if symbol is not None:
            line_color = symbol.color()
            dxf_color = ezdxf.colors.rgb2int((line_color.red(), line_color.green(), line_color.blue()))

        # Retorna os atributos DXF com a cor e o tipo de linha
        return {'true_color': dxf_color, 'linetype': linetype_selected, 'layer': selected_field}

    def realizar_exportacao_para_dxf(self, layer, filePath, selected_field, selected_attribute, rotulo_modo, distancia_intervalo, text_style, dialog, linetype_selected, scale_factor):
        """
        Exporta uma camada para o formato DXF, incluindo geometrias, atributos e rótulos.

        Parâmetros:
        - layer (QgsVectorLayer): A camada que será exportada.
        - filePath (str): O caminho do arquivo DXF onde a camada será salva.
        - selected_field (str): O campo selecionado para nomear a camada DXF.
        - selected_attribute (str): O atributo da feição que será utilizado para rotulagem.
        - rotulo_modo (str): O modo de rotulagem (Centralizado, Segmentado, Equidistante).
        - distancia_intervalo (float): A distância para a rotulagem equidistante (se aplicável).
        - text_style (dict): Dicionário contendo estilo de texto (fonte, tamanho, cor).
        - dialog (QDialog): A instância do diálogo que contém opções e configurações de exportação.
        - linetype_selected (str): O tipo de linha selecionado para exportação (ex.: CONTINUOUS, PERSONALIZAR).
        - scale_factor (float): O fator de escala a ser aplicado às linhas.

        Funcionalidades:
        - Inicia uma barra de progresso para acompanhar o processo de exportação.
        - Cria um novo documento DXF e define o modelspace.
        - Insere geometrias no DXF de acordo com o tipo de renderizador da camada.
        - Suporta a exportação de rótulos com diferentes modos de posicionamento.
        - Aplica padrões personalizados ou complexos às linhas dependendo das opções selecionadas.
        - Salva o arquivo DXF no caminho especificado.
        """
        # Inicia uma barra de progresso para o processo de exportação
        progressBar, progressMessageBar = self.iniciar_progress_bar(layer)

        # Cria um novo documento DXF e define o modelspace
        doc = ezdxf.new('R2013')
        msp = doc.modelspace()

        # Define o estilo de linha no documento DXF
        dialog.definir_estilo_linha(doc, linetype_selected, scale_factor)

        # Define os estilos de texto no documento DXF
        self.definir_estilos_de_texto(doc, text_style)

        # Verifica se o campo selecionado existe na camada DXF, caso contrário, cria um novo
        if selected_field not in doc.layers:
            doc.layers.new(name=selected_field, dxfattribs={'color': 7})

        processed_features = 0
        for feat in layer.getFeatures():
            geom = feat.geometry()

            if geom is None or geom.isEmpty():
                processed_features += 1
                progressBar.setValue(processed_features)
                continue

            feature_length = geom.length()

            # Obtém os atributos DXF relacionados à cor usando a função atualizada
            dxfattribs = self.obter_dxf_atributos_cor(feat, layer, linetype_selected, selected_field)

            # Define o padrão personalizado ou complexo dependendo da seleção
            if linetype_selected == 'PERSONALIZAR':
                # Obtém o texto personalizado do usuário
                custom_text = dialog.linetypeInput.text()
                linetype_name = 'PERSONALIZAR'
                dialog.adicionar_padrao_personalizado(doc, linetype_name, scale_factor, feature_length, custom_text)
                dxfattribs['linetype'] = linetype_name
            elif linetype_selected == 'CERCA':
                linetype_name = 'CERCA'
                dialog.adicionar_padrao_complexo1(doc, linetype_name, scale_factor, feature_length)
                dxfattribs['linetype'] = linetype_name
            elif linetype_selected == 'CERCA 2':
                linetype_name = 'CERCA 2'
                dialog.adicionar_padrao_complexo2(doc, linetype_name, scale_factor, feature_length)
                dxfattribs['linetype'] = linetype_name
            elif linetype_selected == 'SETAS':
                linetype_name = 'SETAS'
                dialog.adicionar_padrao_setas(doc, linetype_name, scale_factor, feature_length)
                dxfattribs['linetype'] = linetype_name
            else:
                dxfattribs['linetype'] = linetype_selected

            # Adiciona as geometrias ao modelspace com os atributos definidos
            self.adicionar_geometrias_ao_modelspace(msp, geom, dxfattribs)

            processed_features += 1
            progressBar.setValue(processed_features)

        # Exporta os rótulos para o DXF
        self.exportar_rotulos_para_dxf(layer, msp, selected_attribute, rotulo_modo, distancia_intervalo, text_style)

        # Salva o documento DXF no caminho especificado
        doc.saveas(filePath)

        # Limpa a barra de mensagens após a exportação
        self.iface.messageBar().clearWidgets()

    def adicionar_geometrias_ao_modelspace(self, msp, geom, dxfattribs):
        """
        Adiciona geometrias de linha ao modelspace DXF de forma robusta.

        Corrige o erro:
        TypeError: 'NoneType' object is not iterable

        Causas tratadas:
        - geometria vazia;
        - geometria inválida;
        - geom.constGet() retornando None;
        - LineString simples;
        - MultiLineString;
        - geometrias com Z;
        - geometrias cujo iterador interno do QGIS muda entre versões.
        """
        if geom is None:
            return False

        try:
            if geom.isEmpty():
                return False
        except Exception:
            return False

        try:
            is3D = QgsWkbTypes.hasZ(geom.wkbType())
        except Exception:
            is3D = False

        def _point_to_tuple(point):
            """Converte QgsPoint/QgsPointXY para tupla DXF."""
            if point is None:
                return None

            try:
                x = float(point.x())
                y = float(point.y())
            except Exception:
                return None

            if is3D:
                try:
                    z = float(point.z())
                except Exception:
                    z = 0.0
                return (x, y, z)

            return (x, y)

        def _points_from_sequence(seq):
            """Converte uma sequência de pontos QGIS em lista de tuplas DXF."""
            if seq is None:
                return []

            pts = []
            try:
                for p in seq:
                    tp = _point_to_tuple(p)
                    if tp is not None:
                        pts.append(tp)
            except Exception:
                return []

            return pts

        def _points_from_part(part):
            """
            Extrai vértices de uma parte da geometria.

            Tenta primeiro part.vertices(), depois tenta iterar diretamente.
            """
            if part is None:
                return []

            try:
                return _points_from_sequence(part.vertices())
            except Exception:
                pass  # nosec B110

            return _points_from_sequence(part)

        polylines = []

        # 1) Caminho preferencial: constParts(), mais seguro para multipart e QGIS 4
        try:
            for part in geom.constParts():
                pts = _points_from_part(part)
                if len(pts) >= 2:
                    polylines.append(pts)
        except Exception:
            pass  # nosec B110

        # 2) Fallback para multipart tradicional
        if not polylines:
            try:
                if geom.isMultipart():
                    for pl in geom.asMultiPolyline():
                        pts = _points_from_sequence(pl)
                        if len(pts) >= 2:
                            polylines.append(pts)
                else:
                    pl = geom.asPolyline()
                    pts = _points_from_sequence(pl)
                    if len(pts) >= 2:
                        polylines.append(pts)
            except Exception:
                pass  # nosec B110

        # 3) Último fallback: vertices() direto da geometria
        if not polylines:
            try:
                pts = _points_from_sequence(geom.vertices())
                if len(pts) >= 2:
                    polylines.append(pts)
            except Exception:
                pass  # nosec B110

        if not polylines:
            return False

        for pts in polylines:
            try:
                if is3D:
                    msp.add_polyline3d(points=pts, dxfattribs=dxfattribs)
                else:
                    msp.add_lwpolyline(pts, dxfattribs=dxfattribs)
            except Exception:
                # Fallback para DXF 2D antigo, caso LWPolyline falhe
                try:
                    pts_2d = [(p[0], p[1]) for p in pts]
                    poly = msp.add_polyline2d(pts_2d, dxfattribs=dxfattribs)
                    poly.close(False)
                except Exception:
                    pass  # nosec B110

        return True

    def fechar_dialogo(self):
        """
        - Fecha o diálogo.
        """
        # Fecha o diálogo principal
        self.dlg.close()

class TreeViewEventFilter(QObject):
    """
    Filtro de eventos do `treeViewListaLinha` para melhorar a interação do usuário.

    Responsabilidades:
    - Exibir tooltip ao mover o mouse sobre itens do treeView (reaproveita `UiManager.configurar_tooltip`).
    - Permitir adicionar arquivos por arrastar e soltar (drag & drop) sobre o treeView,
      chamando o fluxo de importação do UiManager (ex.: `_adicionar_arquivo_por_caminho`).

    Observação:
    - Este filtro é instalado no `viewport()` do QTreeView, pois é onde os eventos de mouse e drop
      realmente ocorrem para os itens exibidos.

    Parâmetros:
    - ui_manager: Referência à instância do `UiManager` que contém o diálogo (`dlg`) e as rotinas
      de importação/feedback (mostrar mensagens, adicionar camadas etc.).
    """
    def __init__(self, ui_manager):
        """
        Inicializa o filtro de eventos com uma referência ao UiManager.

        Parâmetros:
        - self: Referência à instância atual do objeto (TreeViewEventFilter).
        - ui_manager: Instância do UiManager que será usada para acessar e manipular a interface do usuário.
        """
        super().__init__()  # Inicializa a classe base QObject
        self.ui_manager = ui_manager  # Armazena a referência ao UiManager para uso posterior

    def tr(self, message):
        return QCoreApplication.translate("TreeViewEventFilter", message)

    def _is_ext_suportada(self, path: str) -> bool:
        """Retorna True se a extensão do arquivo é suportada pelo fluxo de adicionar."""
        ext = os.path.splitext(path)[1].lower()
        return ext in (".dxf", ".kml", ".kmz", ".shp", ".geojson", ".gpkg")

    def _coletar_paths_drop(self, paths: list[str]) -> list[str]:
        """
        Recebe uma lista de caminhos (arquivos e/ou pastas) e devolve uma lista
        de arquivos suportados.

        - Se for pasta, varre recursivo.
        - Remove duplicados.
        """
        out = []
        seen = set()

        for p in paths:
            if not p:
                continue

            if os.path.isdir(p):
                for root, _, files in os.walk(p):
                    for fn in files:
                        fp = os.path.join(root, fn)
                        if self._is_ext_suportada(fp) and fp not in seen:
                            seen.add(fp)
                            out.append(fp)
            else:
                if self._is_ext_suportada(p) and p not in seen:
                    seen.add(p)
                    out.append(p)

        return out

    def eventFilter(self, obj, event):
        """
        Intercepta eventos do `viewport()` do treeView para:
        - aceitar drag & drop de arquivos/pastas (adicionando camadas ao QGIS),
        - atualizar tooltip quando o mouse passa sobre um item,
        mantendo o comportamento padrão do QTreeView quando não for um evento tratado.
        """
        tv = self.ui_manager.dlg.treeViewListaLinha  # ? aqui é o ponto do erro

        # Só intercepta eventos do viewport do treeView
        if obj != tv.viewport():
            return super().eventFilter(obj, event)

        event_type = event.type()

        # Drag & Drop (Adicionar)
        if event_type in (QEvent.Type.DragEnter, QEvent.Type.DragMove):
            md = event.mimeData()
            if md and md.hasUrls():
                paths = [u.toLocalFile() for u in md.urls() if u.isLocalFile()]
                if self._coletar_paths_drop(paths):
                    event.setDropAction(Qt.DropAction.CopyAction)
                    event.accept()
                    return True
            event.ignore()
            return True

        if event_type == QEvent.Type.Drop:
            md = event.mimeData()
            if md and md.hasUrls():
                raw_paths = [u.toLocalFile() for u in md.urls() if u.isLocalFile()]
                files = self._coletar_paths_drop(raw_paths)

                ok = 0
                for fp in files:
                    try:
                        if self.ui_manager._adicionar_arquivo_por_caminho(fp):
                            ok += 1
                    except Exception as e:
                        self.ui_manager.mostrar_mensagem(self.tr("Falha ao adicionar '{file_name}': {error}").format(file_name=os.path.basename(fp), error=e), "Erro")

                if ok == 0 and files:
                    self.ui_manager.mostrar_mensagem(self.tr("Nenhum arquivo foi adicionado (todos falharam)."), "Aviso")

                elif ok > 0 and len(files) > 1:
                    self.ui_manager.mostrar_mensagem(self.tr("{ok}/{total} arquivos adicionados via arrastar e soltar.").format(ok=ok, total=len(files)), "Sucesso")

                event.setDropAction(Qt.DropAction.CopyAction)
                event.accept()
                return True

            event.ignore()
            return True

        # Tooltip / Hover
        if event_type == QEvent.Type.MouseMove:
            index = tv.indexAt(event.pos())
            if index.isValid():
                self.ui_manager.configurar_tooltip(index)
            # não “consome” o mouse move, deixa o treeView continuar normal
            return False

        return super().eventFilter(obj, event)

class ExportDialogDXF(QDialog):
    def __init__(self, layer, parent=None, line_color=None):
        """
        Inicializa o diálogo de exportação DXF com opções configuráveis para rotulagem, estilo de linha e outros atributos.

        Parâmetros:
        - layer (QgsVectorLayer): Camada de origem para a exportação.
        - parent (QWidget): Widget pai do diálogo.
        - line_color (QColor): Cor padrão das linhas, preto se não especificado.

        Funcionalidades:
        - Configura opções interativas para seleção de atributos e estilos.
        - Permite ajustar a escala e o estilo das linhas diretamente no diálogo.
        - Integra com métodos para aplicar estilos personalizados e pré-configurados.
        """
        super(ExportDialogDXF, self).__init__(parent)
        self.layer = layer
        self.line_color = line_color if line_color else QColor(0, 0, 0)  # Usa a cor passada ou preto como padrão
        self.setWindowTitle(self.tr("Exportar para DXF"))

        # Inicializa as opções de rotulagem
        self.rotulo_modo = None
        self.distancia_intervalo = None
        self.text_style = {'font': 'Arial', 'size': 1, 'color': QColor(0, 0, 0)}
        self.is_linetypeInput_connected = False

        # Configuração do layout principal do diálogo
        layout = QVBoxLayout(self)
        frame = QFrame(self)
        frame.setFrameShape(QFrame.Shape.StyledPanel)
        frame.setFrameShadow(QFrame.Shadow.Raised)
        layout.addWidget(frame)
        frame_layout = QVBoxLayout(frame)

        # Layout para seleção do campo da camada
        field_layout = QHBoxLayout()
        label = QLabel(self.tr("Selecione o Campo da Camada:"), frame)
        field_layout.addWidget(label)
        self.comboBox = QComboBox(frame)
        self.comboBox.addItems([field.name() for field in layer.fields()])
        field_layout.addWidget(self.comboBox)
        frame_layout.addLayout(field_layout)

        # Layout para seleção de atributos e botões de configuração de rotulagem e estilo
        attribute_layout = QHBoxLayout()
        attribute_label = QLabel(self.tr("Selecione o Rótulo:"), frame)
        attribute_layout.addWidget(attribute_label)
        self.attributeComboBox = QComboBox(frame)
        self.attributeComboBox.setFixedWidth(75)
        self.attributeComboBox.addItems([field.name() for field in layer.fields()])
        attribute_layout.addWidget(self.attributeComboBox)

        # Botões para configuração de rotulagem e estilo.
        self.labelingButton = QPushButton(self.tr("Rotulagem"), frame)
        self.labelingButton.clicked.connect(self.show_labeling_options)
        self.labelingButton.setFixedWidth(75)
        attribute_layout.addWidget(self.labelingButton)

        self.estiloButton = QPushButton(self.tr("Estilo"), frame)
        self.estiloButton.clicked.connect(self.choose_estilo)
        self.estiloButton.setFixedWidth(50)
        attribute_layout.addWidget(self.estiloButton)
        frame_layout.addLayout(attribute_layout)

        # ListWidget, DoubleSpinBox e GraphicsView
        list_layout = QVBoxLayout()
        
        self.linetypeList = QListWidget(frame)
        self.linetypeList.setMaximumSize(120, 101)
        list_layout.addWidget(self.linetypeList)

        # Em algum lugar após adicionar itens ao QListWidget, como no construtor do ExportDialogDXF:
        if self.linetypeList.count() > 0:
            self.linetypeList.setCurrentRow(0)  # Define o primeiro item como selecionado

        self.init_linetype_list()  # Método para preencher a lista de tipos de linha

        # Layout para os elementos à direita (DoubleSpinBox e GraphicsView)
        right_layout = QVBoxLayout()
        
        # Layout horizontal para o rótulo "Escala" e o QDoubleSpinBox
        scale_layout = QHBoxLayout()
        linetypeSizeLabel = QLabel(self.tr("Escala: (Linear)"), frame)
        scale_layout.addWidget(linetypeSizeLabel)
        
        self.linetypeSize = QDoubleSpinBox(frame)
        self.linetypeSize.setRange(0.5, 10.0)
        self.linetypeSize.setSingleStep(0.5)
        self.linetypeSize.setValue(1.0)
        scale_layout.addWidget(self.linetypeSize)

        self.linetypeSize.valueChanged.connect(self.update_linetype_preview)

        # Adiciona o layout da escala ao layout à direita
        right_layout.addLayout(scale_layout)

        # Layout horizontal para o linetypeInput e o botão Aplicar
        linetypeInputLayout = QHBoxLayout()
        self.linetypeInput = QLineEdit(frame)
        self.linetypeInput.setPlaceholderText(self.tr("Digite o padrão personalizado..."))
        self.linetypeInput.setMaxLength(12) # Limita o número de caracteres a 12
        linetypeInputLayout.addWidget(self.linetypeInput)

        right_layout.addLayout(linetypeInputLayout)

        self.linetypeInput.setEnabled(False)
        # self.applyButton.setEnabled(False)

        self.linetypePreview = QGraphicsView(frame)
        self.scene = QGraphicsScene()  # Cria uma cena para o QGraphicsView
        self.linetypePreview.setScene(self.scene)
        self.linetypePreview.setMaximumSize(190, 45)
        right_layout.addWidget(self.linetypePreview)

        # Conecta a seleção do QListWidget ao método de atualização do preview
        self.linetypeList.currentTextChanged.connect(self.update_linetype_preview)

        # Cria um layout horizontal e adiciona o layout da lista e o layout à direita
        horizontal_layout = QHBoxLayout()
        horizontal_layout.addLayout(list_layout)
        horizontal_layout.addLayout(right_layout)

        # Adiciona o layout horizontal ao layout principal do frame
        frame_layout.addLayout(horizontal_layout)

        # Botões de controle do diálogo.
        button_layout = QHBoxLayout()
        self.ok_button = QPushButton(self.tr("Exportar"), frame)
        self.ok_button.clicked.connect(self.accept)
        button_layout.addWidget(self.ok_button)
        self.cancel_button = QPushButton(self.tr("Cancelar"), frame)
        self.cancel_button.clicked.connect(self.reject)
        button_layout.addWidget(self.cancel_button)
        frame_layout.addLayout(button_layout)

        self.linetypeInput.textChanged.connect(self._on_linetypeInput_textChanged)

    def _on_linetypeInput_textChanged(self):
        # Só atualiza preview se "PERSONALIZAR" está selecionado
        if self.linetypeList.currentItem() and self.linetypeList.currentItem().text() == self.tr("PERSONALIZAR"):
            self.update_linetype_preview()

    def update_linetype_input_status(self):
        """
        Atualiza o estado do campo de entrada e do botão de aplicação com base no tipo de linha selecionado pelo usuário.
        Habilita a entrada para padrões de linha personalizados e gerencia a conexão do evento de mudança de texto.

        Funcionalidades:
        - Verifica se um item está selecionado na lista de tipos de linha.
        - Conecta ou desconecta o evento de mudança de texto para ativar o botão de aplicar somente quando há texto válido.
        """
        # Verifica se algum item está selecionado na lista de tipos de linha
        current_item = self.linetypeList.currentItem()
        if current_item is not None:
            # Verifica se o tipo de linha selecionado é "PERSONALIZAR"
            is_custom = current_item.text() == self.tr("PERSONALIZAR")
            self.linetypeInput.setEnabled(is_custom)

             # Gerencia a conexão do evento textChanged para atualizar o status do botão de aplicar
            if is_custom and not self.is_linetypeInput_connected:
                # Conecta o evento se ainda não estiver conectado
                self.is_linetypeInput_connected = True
            elif not is_custom and self.is_linetypeInput_connected:
                # Desconecta o evento se o tipo de linha não é personalizado e estava conectado
                self.is_linetypeInput_connected = False
        else:
            # Desativa o campo de entrada e o botão de aplicar se nenhum item está selecionado
            self.linetypeInput.setEnabled(False)

    def init_linetype_list(self):
        """
        Inicializa a lista de tipos de linha no diálogo de exportação, oferecendo opções pré-definidas e uma opção para personalizar.

        Funcionalidades:
        - Limpa a lista atual de tipos de linha para garantir que não haja duplicatas ou entradas antigas.
        - Adiciona um conjunto padrão de tipos de linha, incluindo opções comuns e uma opção para personalização.
        - Conecta o evento de mudança de seleção na lista para atualizar o status do campo de entrada e do botão de aplicar conforme necessário.
        """
        # Limpa a lista existente para remover qualquer item anteriormente adicionado
        self.linetypeList.clear()

        # Adiciona itens à lista de tipos de linha
        # "PERSONALIZAR" permite ao usuário inserir um padrão de linha customizado
        self.linetypeList.addItems([self.tr("PERSONALIZAR"), "CONTINUOUS", "DOTTED", "DASHED", "CENTER", self.tr("CERCA"), self.tr("CERCA 2"), self.tr("SETAS")])

        # Conecta a mudança de texto na lista de tipos de linha
        self.linetypeList.currentTextChanged.connect(self.update_linetype_input_status)

    def adicionar_padrao_personalizado(self, doc, linetype_name, scale_factor, feature_length, text):
        """
        Adiciona um tipo de linha personalizado ao documento DXF que inclui texto especificado pelo usuário.

        Parâmetros:
        - doc (ezdxf.document.Drawing): O documento DXF ao qual o novo tipo de linha será adicionado.
        - linetype_name (str): Nome do novo tipo de linha.
        - scale_factor (float): Fator de escala usado para ajustar a escala do texto e do padrão.
        - feature_length (float): Comprimentorimento da feição a ser usado para calcular o número de repetições do padrão.
        - text (str): Texto a ser incorporado no padrão de linha.

        Funcionalidades:
        - Calcula a escala e o posicionamento do texto dentro do padrão.
        - Estima a largura do texto para centrar visualmente dentro do padrão.
        - Constrói o padrão de linha DXF que incorpora o texto.
        - Adiciona o novo tipo de linha ao documento DXF, se ainda não existir.
        """
        # Configurações iniciais de escalas e espaçamentos com base no fator de escala
        text_scale = 0.5 * scale_factor  # Escala do texto
        long_dash = 0.5 * scale_factor
        short_space = 2 * scale_factor
        text_gap = 0.25 * scale_factor  # Espaço após o texto

        # Estima a largura do texto (ajustando aqui para tentar centralizar melhor visualmente)
        estimated_text_width = len(text) * 1 * text_scale

        # Ajustes de posicionamento para o texto dentro do padrão de linha
        text_x_offset = -estimated_text_width / 2  # Ajuste baseado na largura estimada
        text_y_offset = -text_scale / 2  # Ajuste vertical para centralizar

        # Define o código para incorporar texto ao padrão com ajustes de posicionamento
        text_code = f'["{text}",STANDARD,S={text_scale},X={text_x_offset},Y={text_y_offset}]'

        # Calcula o comprimento total de uma repetição do padrão de linha
        single_pattern_length = 2 * (long_dash + text_gap + abs(short_space))

        # Determina o número de repetições necessárias para cobrir a feição
        num_repeats = max(1, int(feature_length / single_pattern_length))

        # Monta a string do padrão de linha incorporando o texto
        pattern_str = ("A," + ",".join([str(long_dash), str(-short_space), text_code, str(-short_space), "1"]) * num_repeats).rstrip(',')

        # Adiciona o novo tipo de linha ao documento DXF, caso ainda não exista
        if linetype_name not in doc.linetypes:
            doc.linetypes.add(
                name=linetype_name,
                pattern=pattern_str,
                description=f"Custom line with text '{text}' repeated",
                length=single_pattern_length)

    def adicionar_padrao_setas(self, doc, linetype_name, scale_factor, feature_length):
        """
        Adiciona um padrão de linha complexo com setas ">>" intercaladas ao documento DXF.

        Parâmetros:
        - doc: Documento DXF onde o padrão será adicionado.
        - linetype_name: Nome do tipo de linha a ser adicionado.
        - scale_factor: Fator de escala para ajustar o tamanho dos componentes do padrão.
        - feature_length: Comprimentorimento da feição para calcular o número de repetições do padrão.

        Descrição:
        A função define um padrão de linha complexo com setas ">>" intercaladas e adiciona esse padrão ao documento DXF.
        O tamanho e a posição dos componentes são ajustados de acordo com o fator de escala fornecido.
        """

        # Ajuste da escala dos componentes do padrão com base no fator de escala
        scale_symbol = 0.5 * scale_factor  # Mantém o tamanho das setas ">>"
        long_dash = 0.3 * scale_factor  # Comprimentorimento do traço ajustado
        short_dash = 0.5 * scale_factor  # Comprimentorimento do traço curto
        space_between_dashes = 0.1 * scale_factor  # Espaço entre traços

        # Código para as setas ">>", ajustando a posição vertical para centralizar na linha
        shape_code = f"[\">>\",STANDARD,S={scale_symbol},R=0.0,X=-0.25,Y=-0.25]"

        # Define o comprimento total de uma repetição do padrão
        single_pattern_length = long_dash + short_dash + space_between_dashes + scale_symbol

        # Calcula o número de repetições do padrão com base no comprimento da feição
        num_repeats = max(1, int(feature_length / single_pattern_length))

        # Monta a string do padrão de linha incorporando as setas ">>"
        pattern_str = f"A,{long_dash},{-space_between_dashes},{short_dash},{-space_between_dashes},{shape_code},{-space_between_dashes},{short_dash},{-space_between_dashes},{long_dash}"

        # Adiciona o novo tipo de linha ao documento DXF, se ainda não estiver presente
        if linetype_name not in doc.linetypes:
            doc.linetypes.add(
                name=linetype_name,
                pattern=pattern_str,
                description=self.tr("Linha com setas ---->>---->>---->>"),
                length=single_pattern_length)

    def draw_custom_setas_pattern(self, scene, x_start, y_start, x_end, y_end, scale_factor):
        """
        Desenha um padrão de linha com setas ">>" intercaladas no QGraphicsScene.

        Parâmetros:
        - scene: QGraphicsScene onde o padrão será desenhado.
        - x_start: Coordenada X inicial da linha.
        - y_start: Coordenada Y inicial da linha.
        - x_end: Coordenada X final da linha.
        - y_end: Coordenada Y final da linha.
        - scale_factor: Fator de escala para ajustar o tamanho dos componentes do padrão.

        Descrição:
        A função desenha uma linha horizontal no QGraphicsScene com setas ">>" intercaladas e traços contínuos entre elas.
        O tamanho e a posição dos componentes são ajustados de acordo com o fator de escala fornecido.
        """

        # Define a espessura da linha, garantindo uma espessura mínima de 1
        line_thickness = max(1, 1)
        pen = QPen(self.line_color, line_thickness)  # Configura a caneta para desenhar a linha com a cor especificada

        # Calcula a largura e altura do símbolo ">>" com base no fator de escala
        symbol_width = max(8, 20 * scale_factor)
        symbol_height = max(8, 20 * scale_factor)

        # Define o comprimento dos traços entre os símbolos ">>" e nos extremos da linha
        inter_symbol_dash_length = max(15, 15 * scale_factor)
        start_end_dash_length = max(15, 15 * scale_factor)

        # Calcula o comprimento total disponível para desenhar a linha
        total_length = x_end - x_start - 2 * start_end_dash_length

        # Calcula o número de símbolos ">>" que podem ser desenhados ao longo da linha
        num_symbols = max(3, int((total_length + inter_symbol_dash_length) / (symbol_width + inter_symbol_dash_length)))

        # Calcula o espaçamento entre os símbolos, garantindo que haja espaço suficiente
        symbol_spacing = (total_length - num_symbols * symbol_width - (num_symbols - 1) * inter_symbol_dash_length) / (num_symbols - 1) if num_symbols > 1 else 0

        # Desenha o primeiro traço da linha
        scene.addLine(x_start, y_start, x_start + start_end_dash_length, y_start, pen)
        current_pos = x_start + start_end_dash_length  # Atualiza a posição atual ao longo da linha

        # Itera sobre o número de símbolos ">>" para desenhá-los ao longo da linha
        for i in range(num_symbols):
            pos_x = current_pos  # Posição X atual para o símbolo ">>"
            text_item = scene.addText(">>")  # Adiciona o texto ">>" na cena
            font = text_item.font()
            font.setPointSizeF(10 * scale_factor)  # Ajusta o tamanho da fonte com base no fator de escala
            text_item.setFont(font)
            text_item.setPos(pos_x, y_start - (text_item.boundingRect().height() / 2))  # Centraliza o ">>" verticalmente na linha
            text_item.setDefaultTextColor(self.line_color)  # Define a cor do ">>"
            current_pos += symbol_width  # Atualiza a posição atual ao longo da linha após desenhar o ">>"

            # Desenha o traço entre os símbolos ">>" se não for o último símbolo
            if i < num_symbols - 1:
                scene.addLine(current_pos, y_start, current_pos + inter_symbol_dash_length, y_start, pen)
                current_pos += inter_symbol_dash_length  # Atualiza a posição atual ao longo da linha após desenhar o traço

        # Desenha o último traço da linha até o ponto final
        scene.addLine(current_pos, y_start, x_end, y_start, pen)

        # Ajusta os limites da cena para incluir todos os elementos desenhados
        scene.setSceneRect(scene.itemsBoundingRect())

        # Ajusta a visualização da linha para garantir que ela se encaixe corretamente na área visível
        self.linetypePreview.fitInView(scene.itemsBoundingRect(), Qt.AspectRatioMode.KeepAspectRatio)

    def adicionar_padrao_complexo1(self, doc, linetype_name, scale_factor, feature_length):
        """
        Adiciona um tipo de linha complexo ao documento DXF que inclui símbolos definidos pelo usuário.

        Parâmetros:
        - doc (ezdxf.document.Drawing): O documento DXF ao qual o novo tipo de linha será adicionado.
        - linetype_name (str): Nome do novo tipo de linha.
        - scale_factor (float): Fator de escala usado para ajustar a escala dos componentes do padrão.
        - feature_length (float): Comprimentorimento da feição para calcular o número de repetições do padrão.

        Funcionalidades:
        - Ajusta a escala dos componentes do padrão, incluindo traços e espaços.
        - Define um código de símbolo personalizado que é incorporado ao padrão de linha.
        - Calcula o número necessário de repetições para cobrir a feição de forma eficaz.
        - Cria e adiciona o novo tipo de linha ao documento DXF, caso ainda não exista.
        """
        # Ajuste da escala dos componentes do padrão com base no fator de escala
        scale_symbol = 0.5 * scale_factor  # Mantém o tamanho dos símbolos "[]"
        long_dash = 0.5 * scale_factor # Comprimentorimento do traço ajustado para coincidir com o símbolo
        short_space = 0.5 * scale_factor  # Define o espaço entre os componentes do padrão

        # Código para o símbolo customizado
        shape_code = f"[132,ltypeshp.shx,x={-scale_symbol},s={scale_symbol}]"

        # Define o comprimento total de uma repetição do padrão
        single_pattern_length = 2  # Aumentar para melhorar a visualização

        # Calcula o número de repetições do padrão com base no comprimento da feição
        num_repeats = max(1, int(feature_length / single_pattern_length))

        # Criando o padrão como uma string
        pattern_str = ("A," + ",".join([str(long_dash), str(-short_space), shape_code, str(-short_space), "1"]) * num_repeats).rstrip(',')

        # Adiciona o novo tipo de linha ao documento DXF, se ainda não estiver presente
        if linetype_name not in doc.linetypes:
            doc.linetypes.add(linetype_name,
                pattern=pattern_str,
                description="Grenze eckig ----[]-----[]----[]-----[]----[]--",
                length=single_pattern_length)  # Ajuste do comprimento para flexibilidade

    def adicionar_padrao_complexo2(self, doc, linetype_name, scale_factor, feature_length):
        """
        Adiciona um padrão de linha complexo com símbolos "X" intercalados ao documento DXF.

        Parâmetros:
        - doc: Documento DXF onde o padrão será adicionado.
        - linetype_name: Nome do tipo de linha a ser adicionado.
        - scale_factor: Fator de escala para ajustar o tamanho dos componentes do padrão.
        - feature_length: Comprimentorimento da feição para calcular o número de repetições do padrão.

        Descrição:
        A função define um padrão de linha complexo com símbolos "X" intercalados e adiciona esse padrão ao documento DXF.
        O tamanho e a posição dos componentes são ajustados de acordo com o fator de escala fornecido.
        """

        # Ajuste da escala dos componentes do padrão com base no fator de escala
        scale_symbol = 0.5 * scale_factor  # Mantém o tamanho dos símbolos "X"
        long_dash = 0.5 * scale_factor  # Comprimentorimento do traço ajustado
        short_space = 0.1 * scale_factor  # Define o espaço entre os componentes do padrão

        # Ajuste dinâmico das posições horizontal e vertical do símbolo "X"
        x_offset = -0.17 * scale_factor  # Ajusta a posição horizontal de acordo com o fator de escala
        y_offset = -0.25 * scale_factor  # Ajusta a posição vertical de acordo com o fator de escala

        # Código para o símbolo "X", ajustando as posições horizontal e vertical para centralizar na linha
        shape_code = f"[\"X\",STANDARD,S={scale_symbol},R=0.0,X={x_offset},Y={y_offset}]"

        # Define o comprimento total de uma repetição do padrão
        single_pattern_length = long_dash + short_space + scale_symbol

        # Calcula o número de repetições do padrão com base no comprimento da feição
        num_repeats = max(1, int(feature_length / single_pattern_length))

        # Monta a string do padrão de linha incorporando o símbolo "X"
        pattern_str = f"A,{long_dash},{-short_space},{shape_code},{-short_space},1"

        # Adiciona o novo tipo de linha ao documento DXF, se ainda não estiver presente
        if linetype_name not in doc.linetypes:
            doc.linetypes.add(
                name=linetype_name,
                pattern=pattern_str,
                description=self.tr("Linha com X ----X-----X----X-----X----X--"),
                length=single_pattern_length)

    def draw_custom_complex_pattern2(self, scene, x_start, y_start, x_end, y_end, scale_factor):
        """
        Desenha um padrão complexo personalizado no QGraphicsScene, representando uma linha com o símbolo "X" intercalado.
        
        Parâmetros:
        - scene: QGraphicsScene onde o padrão será desenhado.
        - x_start: Coordenada X inicial da linha.
        - y_start: Coordenada Y inicial da linha.
        - x_end: Coordenada X final da linha.
        - y_end: Coordenada Y final da linha.
        - scale_factor: Fator de escala para ajustar o tamanho dos componentes do padrão.
        
        Descrição:
        A função desenha uma linha horizontal no QGraphicsScene com o símbolo "X" intercalado. O padrão é ajustado
        de acordo com o fator de escala fornecido. A linha entre os símbolos "X" é contínua e próxima ao símbolo.
        """
        # Define a espessura da linha, garantindo uma espessura mínima de 1
        line_thickness = max(1, 1)
        pen = QPen(self.line_color, line_thickness)  # Configura a caneta para desenhar a linha com a cor especificada

        # Calcula a largura e altura do símbolo "X" com base no fator de escala
        symbol_width = max(8, 20 * scale_factor)
        symbol_height = max(8, 20 * scale_factor)

        # Define o comprimento dos traços entre os símbolos "X" e nos extremos da linha
        inter_symbol_dash_length = max(15, 15 * scale_factor)
        start_end_dash_length = max(15, 15 * scale_factor)

        # Calcula o comprimento total disponível para desenhar a linha
        total_length = x_end - x_start - 2 * start_end_dash_length

        # Calcula o número de símbolos "X" que podem ser desenhados ao longo da linha
        num_symbols = max(3, int((total_length + inter_symbol_dash_length) / (symbol_width + inter_symbol_dash_length)))

        # Calcula o espaçamento entre os símbolos, garantindo que haja espaço suficiente
        symbol_spacing = (total_length - num_symbols * symbol_width - (num_symbols - 1) * inter_symbol_dash_length) / (num_symbols - 1) if num_symbols > 1 else 0

        # Desenha o primeiro traço da linha
        scene.addLine(x_start, y_start, x_start + start_end_dash_length, y_start, pen)
        current_pos = x_start + start_end_dash_length  # Atualiza a posição atual ao longo da linha

        # Itera sobre o número de símbolos "X" para desenhá-los ao longo da linha
        for i in range(num_symbols):
            pos_x = current_pos  # Posição X atual para o símbolo "X"
            text_item = scene.addText("X")  # Adiciona o texto "X" na cena
            font = text_item.font()
            font.setPointSizeF(10 * scale_factor)  # Ajusta o tamanho da fonte com base no fator de escala
            text_item.setFont(font)
            text_item.setPos(pos_x, y_start - (text_item.boundingRect().height() / 2))  # Centraliza o "X" verticalmente na linha
            text_item.setDefaultTextColor(self.line_color)  # Define a cor do "X"
            current_pos += symbol_width  # Atualiza a posição atual ao longo da linha após desenhar o "X"

            # Desenha o traço entre os símbolos "X" se não for o último símbolo
            if i < num_symbols - 1:
                scene.addLine(current_pos, y_start, current_pos + inter_symbol_dash_length, y_start, pen)
                current_pos += inter_symbol_dash_length  # Atualiza a posição atual ao longo da linha após desenhar o traço

        # Desenha o último traço da linha até o ponto final
        scene.addLine(current_pos, y_start, x_end, y_start, pen)

        # Ajusta os limites da cena para incluir todos os elementos desenhados
        scene.setSceneRect(scene.itemsBoundingRect())

        # Ajusta a visualização da linha para garantir que ela se encaixe corretamente na área visível
        self.linetypePreview.fitInView(scene.itemsBoundingRect(), Qt.AspectRatioMode.KeepAspectRatio)

    def definir_estilo_linha(self, doc, linetype_selected, scale_factor):
        """
        Define ou atualiza um estilo de linha no documento DXF com base no tipo de linha selecionado e no fator de escala aplicado.

        Parâmetros:
        - doc (ezdxf.document.Drawing): O documento DXF onde o estilo de linha será definido.
        - linetype_selected (str): O tipo de linha selecionado pelo usuário.
        - scale_factor (float): Fator de escala que ajusta o tamanho e o espaçamento dos elementos do padrão de linha.

        Funcionalidades:
        - Verifica se o tipo de linha já existe no documento.
        - Se não existir, cria um novo estilo de linha baseado no tipo selecionado e ajusta de acordo com o scale_factor.
        - Adiciona padrões de linha como CONTINUOUS, DOTTED, DASHED e CENTER com especificações detalhadas.
        - Atualiza a lista de tipos de linha na interface do usuário, se necessário.
        """
        # Verifica se o tipo de linha já está definido no documento DXF
        if linetype_selected not in doc.linetypes:
            # Adiciona o tipo de linha CONTINUOUS sem padrão específico
            if linetype_selected == 'CONTINUOUS':
                doc.linetypes.new(linetype_selected, dxfattribs={'pattern': []})

            # Define o padrão para linhas pontilhadas ajustando com o scale_factor
            elif linetype_selected == 'DOTTED':
                # Aplica o scale_factor ao padrão para estilo DOTTED
                dotted_pattern = [0.0, 1.0 * scale_factor, 0.0, -1.0 * scale_factor]
                doc.linetypes.new(linetype_selected, dxfattribs={'pattern': dotted_pattern})

            # Define o padrão para linhas tracejadas ajustando com o scale_factor
            elif linetype_selected == 'DASHED':
                # Aplica o scale_factor ao padrão para estilo DASHED
                dashed_pattern = [1.0 * scale_factor, -1.0 * scale_factor]
                doc.linetypes.new(linetype_selected, dxfattribs={'pattern': dashed_pattern})

            # Adiciona um estilo de linha CENTER com segmentos e espaços definidos pelo scale_factor
            elif linetype_selected == 'CENTER':
                # Adiciona o novo estilo de linha CENTER
                center_pattern = [4.0 * scale_factor, -1.0 * scale_factor, 2.0 * scale_factor, -1.0 * scale_factor, 4.0 * scale_factor]
                doc.linetypes.new(linetype_selected, dxfattribs={'pattern': center_pattern})

            # Após adicionar o novo estilo de linha, atualiza a lista de tipos de linha na interface do usuário para refletir as mudanças
            self.init_linetype_list()

    def update_linetype_preview(self):
        """
        Atualiza a pré-visualização do tipo de linha selecionado no diálogo de exportação, 
        ajustando a visualização conforme o estilo e o fator de escala definidos.

        Funcionalidades:
        - Verifica se um item está selecionado na lista de tipos de linha.
        - Limpa a cena gráfica anterior para garantir que a nova visualização seja limpa.
        - Aplica as configurações de estilo de linha baseadas na seleção do usuário.
        - Ajusta a pré-visualização de acordo com o tipo de linha, aplicando escala e estilo correspondentes.
        - Desenha a linha na cena gráfica para visualização.
        """
        # Verifica se há um item selecionado na lista de tipos de linha no QListWidget
        current_item = self.linetypeList.currentItem()
        if not current_item:
            return  # Retorna imediatamente se não houver item selecionado

        # Obtém o tipo de linha e o fator de escala da interface
        linetype = current_item.text()
        scale_factor = self.linetypeSize.value()  # Obtém o valor atual do QDoubleSpinBox
        self.scene.clear()  # Limpa a cena para desenhar o novo estilo de linha

        # Configura o objeto QPen com a cor da linha selecionada e a espessura básica
        pen = QPen(self.line_color, 1)

        # Aplica estilos diferentes dependendo do tipo de linha selecionado
        if linetype == "DOTTED":
            pen.setStyle(Qt.PenStyle.CustomDashLine)
            pen.setDashPattern([4 * scale_factor, 5 * scale_factor])  # Aplica a escala ao padrão de traço

        elif linetype == "DASHED":
            pen.setStyle(Qt.PenStyle.DotLine)
            pen.setDashPattern([0.5 * scale_factor, 5 * scale_factor])  # Aplica a escala ao padrão de traço

        elif linetype == "CENTER":
            pen.setStyle(Qt.PenStyle.CustomDashLine)
            # Aqui, ajustamos o padrão de acordo com a descrição anterior
            pen.setDashPattern([10.0 * scale_factor, 4.0 * scale_factor, 6.0 * scale_factor, 4.0 * scale_factor, 10.0 * scale_factor])

        elif linetype == "CONTINUOUS":
            pen.setStyle(Qt.PenStyle.SolidLine)  # Linha contínua

        elif linetype == self.tr("CERCA"):
            # Chama uma função auxiliar para desenhar um padrão complexo específico
            self.draw_custom_complex_pattern(self.scene, 10, 20, 180, 20, scale_factor)

        elif linetype == self.tr("CERCA 2"):
            self.draw_custom_complex_pattern2(self.scene, 10, 20, 180, 20, scale_factor)

        elif linetype == self.tr("SETAS"):
            self.draw_custom_setas_pattern(self.scene, 10, 20, 180, 20, scale_factor)

        elif linetype == self.tr("PERSONALIZAR"):
            # Obtém texto personalizado e chama função para desenhar padrão de texto
            custom_text = self.linetypeInput.text()  # Supõe que há um QLineEdit chamado linetypeInput para entrada de texto
            if custom_text:
                self.draw_custom_text_pattern(self.scene, 10, 20, 180, 20, scale_factor, custom_text)

        # Desenha a linha na cena, exceto para os tipos especiais que já adicionam suas próprias linhas
        if linetype != self.tr("CERCA") and linetype != self.tr("CERCA 2") and linetype != self.tr("SETAS") and linetype != self.tr("PERSONALIZAR"):
            self.scene.addLine(10, 20, 180, 20, pen)

        # Ajusta a visualização para enquadrar corretamente a linha dentro da área visível
        self.linetypePreview.fitInView(self.scene.itemsBoundingRect(), Qt.AspectRatioMode.KeepAspectRatio)

    def draw_custom_text_pattern(self, scene, x_start, y_start, x_end, y_end, scale_factor, text):
        """
        Desenha um padrão personalizado de texto na cena gráfica.

        Parâmetros:
        - scene (QGraphicsScene): A cena onde o padrão será desenhado.
        - x_start, y_start (float): Posição inicial da linha no eixo x e y.
        - x_end, y_end (float): Posição final da linha no eixo x e y.
        - scale_factor (float): Fator de escala usado para ajustar o tamanho dos elementos gráficos.
        - text (str): Texto a ser incluído no padrão.

        Funcionalidades:
        - Configura a caneta para desenho com espessura e cor adequadas.
        - Define a fonte e tamanho do texto com base no fator de escala.
        - Calcula a largura do texto e ajusta o padrão de traços para combinar visualmente com o texto.
        - Desenha repetidamente o texto e traços ao longo da linha, garantindo que o padrão preencha o comprimento definido.
        """
        # Configurações de espessura da linha e da fonte
        line_thickness = max(1, 0.5 * scale_factor)  # Garante uma espessura mínima para a linha
        pen = QPen(self.line_color, line_thickness)
        
        # Definindo a fonte para o texto
        font_size = max(5, 5 * scale_factor)  # Garante um tamanho mínimo para a fonte
        font = QFont("Arial", int(font_size))

        # Comprimentorimento estimado do texto
        text_width = QFontMetrics(font).boundingRect(text).width()

        # Comprimentorimento dos traços
        dash_length = max(5, 5 * scale_factor)  # Garante um comprimento mínimo para os traços

        # Espaço adicional entre traços e texto
        additional_space = max(2, 5 * scale_factor)  # Garante um espaço mínimo

        # Comprimentorimento total de uma repetição do padrão
        pattern_length = dash_length + text_width + dash_length + 2 * additional_space

        # Calculando o número de repetições do texto baseado no comprimento da linha
        total_length = x_end - x_start
        num_repeats = max(1, int(total_length / pattern_length))  # Garante pelo menos uma repetição

        # Posição inicial
        current_pos = x_start

        # Adiciona o texto e os traços repetidamente ao longo da linha
        for i in range(num_repeats):
            # Desenha o traço inicial
            scene.addLine(current_pos, y_start, current_pos + dash_length, y_start, pen)
            current_pos += dash_length + additional_space

            # Adiciona o texto
            text_item = scene.addText(text, font)
            # Ajusta a posição y para centralizar verticalmente com a linha
            text_y_position = y_start/2 - QFontMetrics(font).height() / 2 + QFontMetrics(font).ascent() / 2
            text_item.setPos(current_pos, text_y_position)
            text_item.setDefaultTextColor(self.line_color)
            current_pos += text_width + additional_space

            # Desenha o traço final
            scene.addLine(current_pos, y_start, current_pos + dash_length, y_start, pen)
            current_pos += dash_length

        # Assegura que tudo seja visível dentro dos limites da visualização
        scene.setSceneRect(scene.itemsBoundingRect())  # Ajusta a área da cena para incluir todos os itens
        self.linetypePreview.fitInView(scene.itemsBoundingRect(), Qt.AspectRatioMode.KeepAspectRatio)

    def draw_custom_complex_pattern(self, scene, x_start, y_start, x_end, y_end, scale_factor):
        """
        Desenha um padrão complexo com símbolos e traços numa cena gráfica.

        Parâmetros:
        - scene (QGraphicsScene): Cena onde o padrão será desenhado.
        - x_start, y_start (int): Coordenadas iniciais da linha no eixo X e Y.
        - x_end, y_end (int): Coordenadas finais da linha no eixo X e Y.
        - scale_factor (float): Fator de escala para ajustar o tamanho dos símbolos e traços.

        Funcionalidades:
        - Configura a caneta para desenhar com espessura adequada.
        - Calcula o tamanho e a disposição dos símbolos e traços com base no comprimento total disponível.
        - Desenha um padrão repetitivo de símbolos e traços ajustados para visualização clara.
        """
        # Define a espessura da linha baseada no scale_factor
        line_thickness = max(1, 1)  # Ajuste para evitar excesso

        # Configura a caneta para desenhar a linha e os símbolos
        pen = QPen(self.line_color, line_thickness)

        # Configurações para o símbolo "[]"
        symbol_width = max(8, 12 * scale_factor)  # Garante tamanho adequado
        symbol_height = max(8, 12 * scale_factor)  # Mantém proporção

        # Comprimentorimento dos traços entre os símbolos e nos extremos
        inter_symbol_dash_length = max(5, 8 * scale_factor)
        start_end_dash_length = max(5, 8 * scale_factor)

        # Comprimentorimento disponível para símbolos e traços
        total_length = x_end - x_start - 2 * start_end_dash_length
        num_symbols = max(3, int((total_length + inter_symbol_dash_length) / (symbol_width + inter_symbol_dash_length)))
        symbol_spacing = (total_length - num_symbols * symbol_width - (num_symbols - 1) * inter_symbol_dash_length) / (num_symbols - 1) if num_symbols > 1 else 0

        # Desenha o primeiro traço
        scene.addLine(x_start, y_start, x_start + start_end_dash_length, y_start, pen)
        current_pos = x_start + start_end_dash_length

        # Adiciona os retângulos como símbolos "[]"
        for i in range(num_symbols):
            pos_x = current_pos
            rect_item = QGraphicsRectItem(QRectF(pos_x, y_start - (symbol_height / 2), symbol_width, symbol_height))
            rect_item.setPen(pen)
            rect_item.setBrush(QColor(255, 255, 255))
            scene.addItem(rect_item)
            current_pos += symbol_width

            if i < num_symbols - 1:
                scene.addLine(current_pos, y_start, current_pos + inter_symbol_dash_length, y_start, pen)
                current_pos += inter_symbol_dash_length

        # Desenha o último traço
        scene.addLine(current_pos, y_start, x_end, y_start, pen)

        # Ajusta os limites da cena para incluir todos os elementos
        scene.setSceneRect(scene.itemsBoundingRect())
        self.linetypePreview.fitInView(scene.itemsBoundingRect(), Qt.AspectRatioMode.KeepAspectRatio)

    def show_labeling_options(self):
        """
        Exibe um diálogo de opções de rotulagem, permitindo ao usuário escolher entre modos de rotulagem diferentes
        e definir parâmetros específicos para cada modo.
        """
        # Cria um novo diálogo de opções de rotulagem
        dialog = QDialog(self)
        dialog.setWindowTitle(self.tr("Opções de Rotulagem"))
        layout = QVBoxLayout(dialog)

        # Cria um quadro para conter os widgets de opção
        frame = QFrame(dialog)
        frame.setFrameShape(QFrame.Shape.StyledPanel)  # Estilo do painel
        frame.setFrameShadow(QFrame.Shadow.Raised)  # Sombra elevada
        layout.addWidget(frame)  # Adiciona o frame ao layout

        # Layout vertical para os widgets dentro do frame       
        frame_layout = QVBoxLayout(frame)

        # Cria botões de opção para diferentes modos de rotulagem
        radioButtonCentralizado = QRadioButton(self.tr("Centralizado"))
        radioButtonSegmentado = QRadioButton(self.tr("Segmentado"))
        radioButtonEquidistante = QRadioButton(self.tr("Equidistante"))

        # Cria e configura uma SpinBox para definir a distância no modo Equidistante
        spinBoxDistancia = QSpinBox()
        spinBoxDistancia.setMinimum(1)
        spinBoxDistancia.setMaximum(1000)
        spinBoxDistancia.setSingleStep(1)
        spinBoxDistancia.setValue(10)
        spinBoxDistancia.setSuffix(" m")
        spinBoxDistancia.setEnabled(False) # Desabilitada inicialmente

        # Adiciona os botões de rádio ao layout
        frame_layout.addWidget(radioButtonCentralizado)
        frame_layout.addWidget(radioButtonSegmentado)

        # Adiciona os botões de rádio ao layout
        equidistante_layout = QHBoxLayout()
        equidistante_layout.addWidget(radioButtonEquidistante)
        equidistante_layout.addWidget(spinBoxDistancia)
        frame_layout.addLayout(equidistante_layout)

        # Conecta o sinal de alteração do botão Equidistante para habilitar/desabilitar a SpinBox
        radioButtonEquidistante.toggled.connect(lambda checked: spinBoxDistancia.setEnabled(checked))

        # Cria e configura o botão OK
        ok_button = QPushButton(self.tr("OK"), dialog)
        ok_button.setEnabled(False)  # Inicia com o botão OK desativado
        # Ativar o botão OK quando qualquer radioButton for selecionado
        radioButtonCentralizado.toggled.connect(lambda checked: ok_button.setEnabled(True))
        radioButtonSegmentado.toggled.connect(lambda checked: ok_button.setEnabled(True))
        radioButtonEquidistante.toggled.connect(lambda checked: ok_button.setEnabled(checked))

        # Cria e configura o botão Cancelar
        cancel_button = QPushButton(self.tr("Cancelar"), dialog)
        cancel_button.clicked.connect(dialog.reject)

        # Atualiza o estado do botão OK com base na seleção dos radio buttons
        def update_ok_button_status():
            """
            Atualiza o estado do botão OK baseado na seleção dos botões de rádio.
            Habilita o botão OK se algum dos modos de rotulagem estiver selecionado.
            """
            # Verifica se algum dos botões de rádio está selecionado para habilitar o botão OK
            if radioButtonCentralizado.isChecked() or radioButtonSegmentado.isChecked() or radioButtonEquidistante.isChecked():
                ok_button.setEnabled(True)
            else:
                ok_button.setEnabled(False)

        # Conecta os sinais dos botões de rádio ao método que atualiza o estado do botão OK
        radioButtonCentralizado.toggled.connect(update_ok_button_status)
        radioButtonSegmentado.toggled.connect(update_ok_button_status)
        radioButtonEquidistante.toggled.connect(update_ok_button_status)

        # Layout para os botões OK e Cancelar
        button_layout = QHBoxLayout()
        button_layout.addWidget(ok_button)
        button_layout.addWidget(cancel_button)
        frame_layout.addLayout(button_layout)

        # Quando OK for clicado, salve as opções e atualize o texto do botão
        ok_button.clicked.connect(lambda: self.update_labeling_options(radioButtonCentralizado, radioButtonSegmentado, radioButtonEquidistante, spinBoxDistancia, dialog))

        # Quando clicar em Cancelar, redefina o texto do botão para remover a marca de seleção
        cancel_button.clicked.connect(lambda: self.reset_labeling_button(dialog))

        dialog.exec()

    def reset_labeling_button(self, dialog):
        """
        Redefine o estado do botão de rotulagem para remover a marca de seleção e fecha o diálogo.
        """
        self.labelingButton.setText(self.tr("Rotulagem"))  # Reset the text to remove the check mark
        self.labelingButton.setStyleSheet("")  # Clear any custom styles to restore default appearance
        dialog.reject()

    def update_labeling_options(self, rb1, rb2, rb3, spinBox, dialog):
        """
        Atualiza as opções de rotulagem com base na seleção do usuário e fecha o diálogo.

        Parâmetros:
        - rb1 (QRadioButton): Botão para selecionar o modo de rotulagem 'Centralizado'.
        - rb2 (QRadioButton): Botão para selecionar o modo de rotulagem 'Segmentado'.
        - rb3 (QRadioButton): Botão para selecionar o modo de rotulagem 'Equidistante'.
        - spinBox (QSpinBox): Caixa de entrada para definir a distância no modo 'Equidistante'.
        - dialog (QDialog): Diálogo que contém as opções de rotulagem.

        Funcionalidades:
        - Verifica qual botão de rádio está marcado e define o modo de rotulagem apropriado.
        - No caso do modo 'Equidistante', também captura o valor da distância definido pelo usuário.
        - Fecha o diálogo e atualiza o texto e o estilo do botão de rotulagem para refletir a seleção.
        """
        # Verifica qual modo de rotulagem foi selecionado e atualiza a propriedade rotulo_modo
        if rb1.isChecked():
            self.rotulo_modo = "Centralizado"
        elif rb2.isChecked():
            self.rotulo_modo = "Segmentado"
        elif rb3.isChecked():
            self.rotulo_modo = "Equidistante"
            self.distancia_intervalo = spinBox.value()
        dialog.accept()
        # Atualiza o texto do botão de rotulagem na interface principal para indicar que uma configuração foi selecionada
        self.labelingButton.setText(self.tr("Rotulagem ✓"))  # Atualiza o texto do botão para incluir um "✓"
        # Altera a cor do texto do botão para verde, fornecendo um feedback visual de que a configuração foi aplicada
        self.labelingButton.setStyleSheet("QPushButton { color: green; }")

    def choose_estilo(self):
        """
        Abre uma caixa de diálogo para que o usuário escolha o estilo de texto, incluindo fonte, tamanho e cor.

        Funcionalidades:
        - Inicia uma caixa de diálogo com o título "Estilo do Texto".
        - Utiliza um QVBoxLayout para organizar os elementos verticalmente dentro do diálogo.
        - Adiciona um QFrame ao diálogo para delimitar visualmente a área de interação do usuário.
        - Utiliza um QVBoxLayout dentro do QFrame para organizar os controles de seleção de estilo.
        - Configura uma QHBoxLayout para a seleção da família de fontes:
            - Adiciona um QLabel para rotular a seleção de fonte.
            - Cria um QComboBox para listar as fontes suportadas.
            - Limita a visualização para 5 itens no QComboBox para evitar sobrecarga visual.
            - Seleciona a fonte atualmente configurada no QComboBox com base nas preferências salvas.
        - Configura uma QHBoxLayout para a seleção do tamanho da fonte:
            - Adiciona um QLabel para rotular o controle de tamanho.
            - Cria um QDoubleSpinBox para ajustar o tamanho da fonte, com limites e incrementos definidos.
            - Define o valor atual do tamanho da fonte no QDoubleSpinBox.
        - Configura uma QHBoxLayout para a seleção da cor da fonte:
            - Adiciona um QLabel para rotular a seleção de cor.
            - Cria um QPushButton que, quando clicado, abre um seletor de cores.
        - Adiciona um QDialogButtonBox para gerenciar as ações de OK e Cancelar:
            - Configura ações para salvar as alterações ou cancelar e fechar o diálogo.
        - Organiza os botões centralmente utilizando QHBoxLayout com espaçadores à esquerda e à direita.
        - Executa o diálogo para permitir que o usuário interaja com as opções de estilo de texto.
        """
        dialog = QDialog(self)
        dialog.setWindowTitle(self.tr("Estilo do Texto"))
        layout = QVBoxLayout(dialog)

        # Configura um quadro para conter os elementos da interface
        frame = QFrame(dialog)
        frame.setFrameShape(QFrame.Shape.StyledPanel)
        frame.setFrameShadow(QFrame.Shadow.Raised)
        layout.addWidget(frame)

        frame_layout = QVBoxLayout(frame) # Layout vertical para os controles dentro do frame

        # Font family selection
        fontLayout = QHBoxLayout()
        fontLabel = QLabel(self.tr("Fonte:"))
        fontComboBox = QComboBox()  # Usando QComboBox para controlar as entradas
        supported_fonts = ["Arial", "Arial Narrow", "Courier New", "Times New Roman", "Verdana", "Tahoma",
                           "Helvetica", "Calibri", "Garamond", "Lucida Console", "Consolas", "Georgia",
                           "Lucida Sans Unicode", "Palatino Linotype", "Comic Sans MS", "Trebuchet MS", 
                           "Impact", "Century Gothic", "Berlin Sans FB", "Franklin Gothic Medium"]
        fontComboBox.addItems(supported_fonts)
        fontComboBox.setMaxVisibleItems(5)  # Limita a quantidade de itens visíveis na lista dropdown
        fontComboBox.setStyleSheet("""
        QComboBox { combobox-popup: 0; }
        QComboBox QAbstractItemView {
            min-height: 80px; /* Ajuste conforme necessário para mostrar apenas 5 itens */
            max-height: 80px; /* Ajuste conforme necessário para mostrar apenas 5 itens */
        }
        """)
        fontComboBox.setCurrentIndex(supported_fonts.index(self.text_style['font']))  # Define a fonte atual baseada no estilo salvo
        fontLayout.addWidget(fontLabel)
        fontLayout.addWidget(fontComboBox)
        frame_layout.addLayout(fontLayout)
        dialog.fontComboBox = fontComboBox  # Store the fontComboBox in the dialog

        # Configuração da seleção do tamanho da fonte
        sizeLayout = QHBoxLayout()
        sizeLabel = QLabel(self.tr("Tamanho:"))
        sizeSpinBox = QDoubleSpinBox()
        sizeSpinBox.setRange(0.2, 100)
        sizeSpinBox.setSingleStep(0.2)
        sizeSpinBox.setValue(1.0)
        sizeSpinBox.setValue(self.text_style['size'])
        sizeLayout.addWidget(sizeLabel)
        sizeLayout.addWidget(sizeSpinBox)
        frame_layout.addLayout(sizeLayout)
        dialog.sizeSpinBox = sizeSpinBox  # Store the sizeSpinBox in the dialog

        # Configuração da seleção de cor
        colorLayout = QHBoxLayout()
        colorLabel = QLabel(self.tr("Cor:"))
        colorButton = QPushButton(self.tr("Escolher Cor"))
        colorButton.clicked.connect(lambda: self.choose_color(colorButton))
        colorLayout.addWidget(colorLabel)
        colorLayout.addWidget(colorButton)
        frame_layout.addLayout(colorLayout)
        dialog.colorButton = colorButton  # Store the colorButton in the dialog

        # Configuração dos botões de ação
        buttonBox = QDialogButtonBox(QDialogButtonBox.StandardButton.Ok | QDialogButtonBox.StandardButton.Cancel)
        buttonBox.accepted.connect(lambda: self.update_text_style_and_close(dialog, True))
        buttonBox.rejected.connect(lambda: self.update_text_style_and_close(dialog, False))
        buttonBox.rejected.connect(dialog.reject)
        frame_layout.addWidget(buttonBox)

        # Adiciona espaçadores para centralizar os botões
        buttonLayout = QHBoxLayout()
        buttonLayout.addStretch()  # Espaçador à esquerda
        buttonLayout.addWidget(buttonBox)
        buttonLayout.addStretch()  # Espaçador à direita

        frame_layout.addLayout(buttonLayout)

        dialog.exec()

    def update_text_style_and_close(self, dialog, accepted):
        """
        Finaliza a configuração do estilo de texto, atualizando ou rejeitando as mudanças com base na ação do usuário.

        Parâmetros:
        - dialog (QDialog): A caixa de diálogo de onde as configurações são obtidas.
        - accepted (bool): Indica se as alterações foram aceitas ou não.

        Funcionalidades:
        - Verifica se as alterações foram aceitas.
        - Se aceitas, atualiza o dicionário de estilo de texto com os valores selecionados para fonte, tamanho e cor.
        - Atualiza o texto e o estilo do botão de estilo na interface principal para refletir a aceitação das mudanças.
        - Fecha a caixa de diálogo com 'accept', indicando que as mudanças foram confirmadas.
        - Se não aceitas, redefine o texto e estilo do botão de estilo para o estado original.
        - Fecha a caixa de diálogo com 'reject', indicando que as mudanças foram descartadas.
        """
        if accepted:
            # Atualiza o dicionário de estilo de texto com as novas configurações obtidas da caixa de diálogo
            self.text_style['font'] = dialog.fontComboBox.currentText()
            self.text_style['size'] = dialog.sizeSpinBox.value()
            # Atualiza a cor usando a cor atual do botão na paleta de cores
            self.text_style['color'] = dialog.colorButton.palette().color(QPalette.ColorRole.Button)
            # Atualiza o texto do botão de estilo para mostrar que as configurações foram aplicadas
            self.estiloButton.setText(self.tr("Estilo ✓"))
            self.estiloButton.setStyleSheet("QPushButton { color: blue; }")
            dialog.accept()
        else:
            # Redefine o texto do botão de estilo para o estado original
            self.estiloButton.setText(self.tr("Estilo"))
            # Remove qualquer estilo personalizado aplicado anteriormente ao botão
            self.estiloButton.setStyleSheet("")
            dialog.reject()

    def choose_color(self, button):
        """
        Exibe um menu de seleção de cores, permitindo ao usuário escolher uma cor que é aplicada a um botão e armazenada para uso posterior.

        Parâmetros:
        - button (QPushButton): O botão ao qual a cor selecionada será aplicada.

        Funcionalidades:
        - Cria um menu contextual com opções de cores nomeadas.
        - Associa cada opção de cor a um índice ACI específico.
        - Usa ícones coloridos para representar visualmente as cores no menu.
        - Aplica a cor selecionada ao estilo do botão e armazena o índice ACI correspondente.
        """
        # Cria um objeto QMenu para o menu de seleção de cores
        menu = QMenu()
        # Define um dicionário de cores com seus respectivos valores RGB e índice ACI
        colors = {
            'Red': (255, 0, 0, 1),
            'Yellow': (255, 255, 0, 2),
            'Green': (0, 255, 0, 3),
            'Cyan': (0, 255, 255, 4),
            'Blue': (0, 0, 255, 5),
            'Magenta': (255, 0, 255, 6),
            'White': (255, 255, 255, 7)}

        # Itera sobre o dicionário de cores para adicionar cada cor ao menu
        for name, (r, g, b, aci) in colors.items():
            color_action = QAction(name, self) # Cria uma ação com o nome da cor
            color_action.setData(aci) # Armazena o índice ACI como dado associado à ação
            color_action.setIcon(self.create_color_icon(r, g, b)) # Define um ícone colorido para a ação
            menu.addAction(color_action)

        # Exibe o menu na posição atual do cursor e aguarda uma seleção
        action = menu.exec(QCursor.pos())

        if action: # Verifica se uma ação foi selecionada
            aci_index = action.data() # Obtém o índice ACI da ação selecionada
            color = QColor(*colors[action.text()][:3])
            button.setStyleSheet(f"background-color: {color.name()};")
            # Armazena a cor selecionada no botão para uso futuro
            button.palette().setColor(QPalette.ColorRole.Button, color)
            # Armazena o índice ACI no estilo de texto
            self.text_style['aci_color'] = aci_index

    def create_color_icon(self, r, g, b):
        """
        Cria um ícone colorido que representa uma cor específica usando valores RGB.

        Parâmetros:
        - r (int): Valor do componente vermelho da cor, de 0 a 255.
        - g (int): Valor do componente verde da cor, de 0 a 255.
        - b (int): Valor do componente azul da cor, de 0 a 255.

        Retorna:
        - QIcon: O objeto QIcon criado com a cor especificada.

        Funcionalidades:
        - Cria um QPixmap de tamanho 16x16 pixels.
        - Preenche o QPixmap com a cor especificada pelos valores RGB.
        - Converte o QPixmap em um QIcon para uso em elementos da interface do usuário.
        """
        # Cria um QPixmap de 16x16 pixels para o ícone
        pixmap = QPixmap(16, 16)
        # Preenche o pixmap com a cor especificada
        pixmap.fill(QColor(r, g, b))
        # Cria um QIcon a partir do pixmap
        return QIcon(pixmap)

    def get_Values(self):
        """
        Retorna os valores atuais selecionados em comboboxes e um spinbox da interface gráfica do usuário.

        Retorna:
        - tuple: Uma tupla contendo o texto selecionado no comboBox de campos, no attributeComboBox de atributos,
                 e o valor numérico do linetypeSize (tamanho ou escala de linha).

        Detalhes:
        - self.comboBox.currentText(): Recupera e retorna o texto atualmente selecionado no comboBox.
          Este comboBox pode estar listando opções como nomes de campos, camadas, ou outros parâmetros configuráveis.
        
        - self.attributeComboBox.currentText(): Recupera e retorna o texto atualmente selecionado no attributeComboBox.
          Este comboBox é geralmente usado para selecionar atributos específicos de um objeto ou entidade,
          como características de dados geográficos ou propriedades de elementos em um projeto.

        - self.linetypeSize.value(): Recupera e retorna o valor atual do linetypeSize, que é um QDoubleSpinBox.
          Este controlador ajusta o tamanho ou a escala das linhas, podendo influenciar a visualização ou a impressão
          de desenhos técnicos ou diagramas.

        Utilização:
        Esta função é útil para coletar configurações essenciais de usuário que impactam operações subsequentes,
        como ajustes em visualizações gráficas, configurações de exportação para formatos como DXF, ou ajustes
        de renderização em aplicações de CAD.
        """
        return (
        self.comboBox.currentText(), 
        self.attributeComboBox.currentText(),
        self.linetypeSize.value())

    def get_labeling_options(self):
        """
        Recupera as opções de rotulagem atualmente configuradas no sistema.

        Retorna:
        - tuple: Uma tupla contendo duas entradas:
            1. self.rotulo_modo (str): O modo de rotulagem selecionado, como 'Centralizado', 'Segmentado', ou 'Equidistante'.
            2. self.distancia_intervalo (int): A distância entre rótulos, aplicável no modo 'Equidistante'.

        Funcionalidades:
        - Recupera e retorna as configurações de rotulagem que influenciam como os rótulos são aplicados a entidades ou dados
          em uma visualização ou exportação. Essas configurações podem afetar diretamente a legibilidade e a utilidade
          da informação apresentada, sendo críticas em aplicações de mapeamento, CAD, ou visualização de dados.

        Utilização:
        - Esta função é utilizada para acessar as configurações de rotulagem correntes para serem aplicadas ou ajustadas
          em operações de renderização ou quando se prepara a exportação de dados para formatos que suportam rotulagem,
          como DXF ou outros formatos de arquivo específicos de indústria.
        """
        return self.rotulo_modo, self.distancia_intervalo

    def get_text_style(self):
        """
        Retorna o estilo de texto atual como um dicionário.
        """
        return self.text_style

    def get_selected_linetype(self):
        """
        Obtém o tipo de linha selecionado no QListWidget responsável por listar os tipos de linha disponíveis.

        Retorna:
        - str: O nome do tipo de linha selecionado, ou 'CONTINUOUS' como valor padrão se nenhuma linha estiver selecionada.

        Funcionalidades:
        - Acessa o item atualmente selecionado na lista de tipos de linha.
        - Retorna o texto associado a esse item, que descreve o tipo de linha.
        - Se nenhum item estiver selecionado, retorna 'CONTINUOUS' como um padrão seguro, assumindo que o tipo de linha contínua é o padrão desejado.

        Utilização:
        - Esta função é útil para aplicações que necessitam configurar propriedades gráficas ou de exportação baseadas no tipo de linha selecionado,
          como em sistemas de desenho assistido por computador (CAD) ou outras ferramentas gráficas que lidam com representações visuais detalhadas.
        """
        # Tenta obter o item atualmente selecionado no QListWidget
        current_item = self.linetypeList.currentItem()
        if current_item:
            return current_item.text()
        return 'CONTINUOUS'  # Se nenhum item estiver selecionado, retorna 'CONTINUOUS' como padrão

class CustomDelegate(QStyledItemDelegate):
    """
    CustomDelegate é uma subclasse de QStyledItemDelegate usada para personalizar
    a forma como os itens são desenhados em um QTreeView.

    Esta classe é responsável por desenhar um traço representativo da linha
    para cada camada no QTreeView. A cor e a posição do traço são baseadas nos
    dados do item do modelo.
    """
    def paint(self, painter, option, index):
        """
        Desenha o item padrão e o indicador usando a cor real da camada.
        """
        super().paint(painter, option, index)

        valor_cor = index.data(Qt.ItemDataRole.UserRole)

        cor_linha = (QColor(valor_cor)
            if valor_cor
            else QColor())

        if not cor_linha.isValid():
            cor_linha = QColor(Qt.GlobalColor.black)

        espessura_linha = 7
        comprimento_linha = 10
        espaco_linha = -13

        linha_x = (option.rect.x() + espaco_linha)

        linha_y = (option.rect.y() + (option.rect.height() - espessura_linha) // 2 + 4)

        painter.save()

        painter.setRenderHint(QPainter.RenderHint.Antialiasing)

        painter.setPen(QPen(cor_linha, espessura_linha))

        painter.drawLine(linha_x, linha_y, linha_x + comprimento_linha, linha_y)

        painter.restore()

class ExportarKMLDialog(QDialog):
    """
    Diálogo personalizado para configurar a exportação de camadas do QGIS para o formato KML, com opções avançadas incluindo atributos de linha, URLs de imagem, e configurações 3D.

    Atributos de classe:
    - ultimoTextoUrl (str): Armazena o último URL de imagem válido usado para a tabela.
    - ultimoTextoUrl2 (str): Armazena o último URL de imagem válido usado para o ScreenOverlay.

    Métodos:
    - __init__(self, campos): Construtor que inicializa o diálogo com opções configuráveis baseadas nos campos da camada.
    - checkAltitudeValue(self): Verifica o valor da altitude para ativar ou desativar opções dependentes de altura.
    - toggleWidgets(self): Ativa ou desativa widgets com base no estado de uma CheckBox.
    - verificarValidadeURL(self, url): Valida URLs usando uma expressão regular.
    - colarTexto(self): Cola texto do clipboard para o campo URL da imagem da tabela.
    - colarTexto2(self): Cola texto do clipboard para o campo URL do ScreenOverlay.
    - verificarValidadeURLImagem(self, url): Checa se a URL termina com uma extensão de arquivo de imagem válida.
    - verificarTexto(self): Verifica e atualiza o estilo do campo URL da imagem da tabela com base na sua validade.
    - verificarTexto2(self): Verifica e atualiza o estilo do campo URL do ScreenOverlay com base na sua validade.
    - getValues(self): Retorna os valores configurados no diálogo.

    Utilização:
    - Usuários podem abrir este diálogo para configurar detalhadamente como uma camada será exportada para KML, incluindo opções visuais e de dados, facilitando a integração com plataformas como Google Earth.
    """
    # Atributos de classe para armazenar os URLs
    ultimoTextoUrl = ""
    ultimoTextoUrl2 = ""

    def __init__(self, campos):
        super().__init__()

        self.setWindowTitle(self.tr("Exportar para KML"))

        # Criação do layout principal
        mainLayout = QVBoxLayout(self) # Define o título da janela

        # Adiciona um QFrame com estilo Raised ao layout principal
        frame = QFrame() # Cria um frame para conter os widgets
        frame.setFrameShape(QFrame.Shape.StyledPanel) # Define o estilo do frame para StyledPanel
        frame.setFrameShadow(QFrame.Shadow.Raised) # Sombra do frame definida como elevada
        layout = QVBoxLayout(frame)  # Layout para conter todos os outros widgets dentro do frame

        # Adiciona o frame ao layout principal
        mainLayout.addWidget(frame)

        # Layout horizontal para o rótulo, ComboBox, e CheckBox
        rotuloCampoLayout = QHBoxLayout()

        # Label para escolher o campo para o rótulo
        self.labelCampo = QLabel(self.tr("Campo de Identificação:"))
        rotuloCampoLayout.addWidget(self.labelCampo)

        # ComboBox para escolher o campo para o rótulo
        self.comboBoxCampo = QComboBox()
        self.comboBoxCampo.addItems(campos)
        rotuloCampoLayout.addWidget(self.comboBoxCampo)

        rotuloCampoLayout.addSpacing(12)  # Adiciona um pequeno espaço entre os widgets

        # CheckBox para escolher se inclui a tabela de atributos
        self.checkBoxTabela = QCheckBox(self.tr("Tabela")) # Cria CheckBox
        self.checkBoxTabela.setChecked(True) # CheckBox marcada por padrão
        rotuloCampoLayout.addWidget(self.checkBoxTabela)

        # Conecta o sinal stateChanged do checkBox a um método que controla o estado do comboBox, lineEdit, e botão
        self.checkBoxTabela.stateChanged.connect(self.toggleWidgets)

        # Adiciona o layout horizontal do rótulo, ComboBox, e CheckBox ao layout principal
        layout.addLayout(rotuloCampoLayout)

        # Layout horizontal para Espessura da Linha e Altitude
        linhaAltitudeLayout = QHBoxLayout()

        # Espessura
        espessuraLayout = QHBoxLayout()
        self.labelEspessura = QLabel(self.tr("Espessura:"))
        self.doubleSpinBoxEspessura = QDoubleSpinBox()
        self.doubleSpinBoxEspessura.setSingleStep(0.1)
        self.doubleSpinBoxEspessura.setDecimals(1)
        self.doubleSpinBoxEspessura.setValue(1.0)
        espessuraLayout.addWidget(self.labelEspessura)
        espessuraLayout.addWidget(self.doubleSpinBoxEspessura)

        # Altura
        alturaLayout = QHBoxLayout()
        self.labelAltitude = QLabel(self.tr("Altura:"))
        self.doubleSpinBoxAltitude = QDoubleSpinBox()
        self.doubleSpinBoxAltitude.setSingleStep(0.5)
        self.doubleSpinBoxAltitude.setDecimals(1)
        self.doubleSpinBoxAltitude.setValue(0.0)
        alturaLayout.addWidget(self.labelAltitude)
        alturaLayout.addWidget(self.doubleSpinBoxAltitude)
        # Espaço entre Altitude e 3D (por exemplo, 10px)
        alturaLayout.addSpacing(12)

        # Layout separado para "3D" e checkBox3D
        self.checkBox3D = QCheckBox(self.tr("3D"))
        alturaLayout.addWidget(self.checkBox3D)

        # Adiciona sub-layouts com espaçamento entre eles
        linhaAltitudeLayout.addLayout(espessuraLayout)
        linhaAltitudeLayout.addSpacing(8)
        linhaAltitudeLayout.addLayout(alturaLayout)

        layout.addLayout(linhaAltitudeLayout)

        # Layout para "Repetições" alinhado à esquerda em grid
        linhaRepeteLayout = QGridLayout()

        self.labelRepete = QLabel(self.tr("Quantidade de Repetições Verticais das Feições:   "))
        self.labelRepete.setStyleSheet("color: blue;")  # cor azul conforme ajuste anterior
        self.spinBoxRepete = QSpinBox()
        self.spinBoxRepete.setMinimum(1)
        self.spinBoxRepete.setMaximum(100)

        linhaRepeteLayout.addWidget(self.labelRepete, 0, 0)
        linhaRepeteLayout.addWidget(self.spinBoxRepete, 0, 1)
        linhaRepeteLayout.setColumnStretch(2, 1)  # garante que fique à esquerda

        layout.addLayout(linhaRepeteLayout)  # Adiciona ao layout principal

        self.checkAltitudeValue()  # Verifica inicialmente o valor para configurar a atividade do spinBoxRepete
        # Conecta mudança de valor para verificação
        self.doubleSpinBoxAltitude.valueChanged.connect(self.checkAltitudeValue)

        # Primeiro QLineEdit e QPushButton para o URL da imagem
        self.labelImageUrl = QLabel(self.tr("URL da Imagem para a Tabela:"))
        layout.addWidget(self.labelImageUrl)

        urlLayout1 = QHBoxLayout()
        self.lineEditImageUrl = QLineEdit()
        self.lineEditImageUrl.setPlaceholderText(self.tr("Colar o URL da IMG para a Tabela: Opcional"))
        self.lineEditImageUrl.setClearButtonEnabled(True)  # Habilita o botão de limpeza
        self.btnAbrirImagem = QPushButton(self.tr("Colar"))
        self.btnAbrirImagem.setMaximumWidth(40)
        urlLayout1.addWidget(self.lineEditImageUrl)
        urlLayout1.addWidget(self.btnAbrirImagem)

        layout.addLayout(urlLayout1)   # Adiciona layout de URL da imagem ao layout principal

        self.btnAbrirImagem.clicked.connect(self.colarTexto) # Conecta botão para colar texto

        # Segundo QLineEdit e QPushButton para o URL da imagem
        self.labelImageUrl2 = QLabel(self.tr("URL para ScreenOverlay:"))
        layout.addWidget(self.labelImageUrl2)

        urlLayout2 = QHBoxLayout()
        self.lineEditImageUrl2 = QLineEdit()
        self.lineEditImageUrl2.setPlaceholderText(self.tr("Colar o URL para o ScreenOverlay: Opcional"))
        self.lineEditImageUrl2.setClearButtonEnabled(True)  # Habilita o botão de limpeza
        self.btnAbrirImagem2 = QPushButton(self.tr("Colar"))
        self.btnAbrirImagem2.setMaximumWidth(40)
        urlLayout2.addWidget(self.lineEditImageUrl2)
        urlLayout2.addWidget(self.btnAbrirImagem2)
        layout.addLayout(urlLayout2)

        self.btnAbrirImagem2.clicked.connect(self.colarTexto2)

        # Setar o texto dos QLineEdit com os últimos valores usados
        self.lineEditImageUrl.setText(self.ultimoTextoUrl)
        self.lineEditImageUrl2.setText(self.ultimoTextoUrl2)

        # Conecta o sinal textChanged a um novo método para lidar com a atualização do texto
        self.lineEditImageUrl.textChanged.connect(self.verificarTexto)
        self.lineEditImageUrl2.textChanged.connect(self.verificarTexto2)

        # Layout para os botões
        buttonLayout = QHBoxLayout()
        self.btnConfirmar = QPushButton(self.tr("Confirmar"))
        self.btnConfirmar.clicked.connect(self.accept)
        buttonLayout.addWidget(self.btnConfirmar)

        self.btnCancelar = QPushButton(self.tr("Cancelar"))
        self.btnCancelar.clicked.connect(self.reject)
        buttonLayout.addWidget(self.btnCancelar)

        layout.addLayout(buttonLayout)  # Adiciona o layout dos botões ao layout principal do frame

        if not campos:
            self.doubleSpinBoxEspessura.setEnabled(True)  # Habilita SpinBox de espessura se não há campos
            self.doubleSpinBoxAltitude.setEnabled(True)  # Habilita SpinBox de altitude se não há campos
            self.btnConfirmar.setEnabled(False)  # Desabilita botão de confirmar se não há campos

    def checkAltitudeValue(self):
        """
        Verifica o valor atual da altitude para determinar se determinados widgets devem ser habilitados ou desabilitados. 
        Se a altitude for zero, desabilita as opções de repetição e a funcionalidade 3D, que dependem de uma altitude não nula para serem aplicáveis.

        Funcionalidades:
        - Verifica o valor da altitude a partir do widget DoubleSpinBox.
        - Habilita ou desabilita os widgets de número de repetições e a caixa de seleção 3D com base no valor da altitude.
        
        Utilização:
        - Essencial para garantir que as configurações de visualização 3D e repetições sejam aplicáveis apenas quando há uma altitude definida, evitando configurações não suportadas ou sem sentido em altitudes zero.
        """
        # Verifica se o valor da altitude é diferente de zero
        enable = self.doubleSpinBoxAltitude.value() != 0

        # Habilita ou desabilita o spinBox de repetições com base no valor da altitude
        self.spinBoxRepete.setEnabled(enable)

        # Habilita ou desabilita a caixa de seleção 3D com base no valor da altitude
        self.checkBox3D.setEnabled(enable)

        if not enable:
            self.checkBox3D.setChecked(False)  # Desmarca ao inativar

    def toggleWidgets(self):
        """
        Alterna a ativação de diversos widgets com base no estado do checkBox para inclusão de tabela de atributos. 
        Quando ativado, permite a seleção do campo de rótulo e o uso de URLs de imagem.

        Funcionalidades:
        - Obtém o estado atual do checkBoxTabela.
        - Habilita ou desabilita o comboBox para escolha do campo de rótulo, o campo de entrada de URL da imagem, e o botão associado à entrada de URL, com base no estado do checkBox.

        Utilização:
        - Essencial para garantir que o usuário só possa selecionar ou inserir informações relevantes para a inclusão da tabela de atributos no KML, mantendo a interface limpa e prevenindo entradas desnecessárias quando a tabela não é desejada.
        """
        # O estado do checkBoxTabela determina a ativação dos outros widgets
        is_checked = self.checkBoxTabela.isChecked()
        
        # Ativar ou desativar widgets com base no estado do checkBox
        self.comboBoxCampo.setEnabled(is_checked)
        self.lineEditImageUrl.setEnabled(is_checked)
        self.btnAbrirImagem.setEnabled(is_checked)

    def verificarValidadeURL(self, url):
        """
        Verifica se a string fornecida é uma URL válida usando uma expressão regular.

        Parâmetros:
        - url (str): A URL a ser validada.

        Funcionalidades:
        - Comprimentoila uma expressão regular que valida URLs de forma abrangente, cobrindo protocolos, domínios, IPs, portas, caminhos, query strings e fragmentos.
        - Verifica se a URL fornecida corresponde à expressão regular.

        Retorno:
        - Retorna True se a URL for válida, False caso contrário.

        Utilização:
        - Utilizada para garantir que as URLs inseridas para imagens ou links em campos de URL sejam válidas antes de serem utilizadas para evitar erros na aplicação ou na visualização do KML.
        """
        # Expressão regular atualizada para validar URLs de forma mais abrangente.
        padrao_url = re.compile(
            r'^(https?:\/\/)?'  # http:// ou https://
            r'((([a-z\d]([a-z\d-]*[a-z\d])*)\.)+[a-z]{2,}|'  # domínio
            r'((\d{1,3}\.){3}\d{1,3}))'  # ou ip
            r'(\:\d+)?(\/[-a-z\d%_.~+]*)*'  # porta e caminho
            r'(\?[;&a-z\d%_.~+=-]*)?'  # query string
            r'(\#[-a-z\d_]*)?$', re.IGNORECASE)  # fragmento
        return re.match(padrao_url, url) is not None

    def colarTexto(self):
        """
        Obtém o texto do clipboard e insere no campo QLineEdit destinado ao URL da imagem, 
        se o texto for uma URL válida.

        Funcionalidades:
        - Acessa o conteúdo do clipboard do sistema.
        - Verifica se o texto é uma URL válida.
        - Insere a URL válida no campo de texto se for válida.

        Utilização:
        - Usado para facilitar a inserção de URLs por meio do uso de clipboard, evitando a necessidade de digitação manual, 
          aumentando a eficiência do usuário e reduzindo a chance de erro de entrada.
        """
        # Acessa o clipboard do sistema
        clipboard = QGuiApplication.clipboard() # Obtém o objeto clipboard do sistema
        texto = clipboard.text() # Lê o texto atualmente armazenado no clipboard
        
        # Verifica se o texto copiado é uma URL válida
        if self.verificarValidadeURL(texto): # Chama o método para verificar a validade da URL
            self.lineEditImageUrl.setText(texto) # Insere o texto no QLineEdit se for uma URL válida

    def colarTexto2(self):
        """
        Obtém o texto do clipboard e insere no campo QLineEdit destinado ao URL para ScreenOverlay,
        se o texto for uma URL válida.

        Funcionalidades:
        - Acessa o conteúdo do clipboard do sistema.
        - Verifica se o texto é uma URL válida.
        - Insere a URL válida no campo de texto destinado ao ScreenOverlay se for válida.

        Utilização:
        - Usado para facilitar a inserção de URLs de ScreenOverlay por meio do uso de clipboard, 
          evitando a necessidade de digitação manual e melhorando a eficiência do usuário.
        """
        # Acessa o clipboard do sistema
        clipboard = QGuiApplication.clipboard() # Obtém o objeto clipboard do sistema
        texto = clipboard.text() # Lê o texto atualmente armazenado no clipboard

        # Verifica se o texto copiado é uma URL válida
        if self.verificarValidadeURL(texto): # Chama o método para verificar a validade da URL
            self.lineEditImageUrl2.setText(texto) # Insere o texto no QLineEdit destinado ao ScreenOverlay se for uma URL válida

    def verificarValidadeURLImagem(self, url):
        """
        Verifica se a URL fornecida termina com uma extensão de arquivo de imagem aceitável. 
        Este método é usado para garantir que URLs inseridas para imagens sejam de formatos compatíveis para visualização.

        Parâmetros:
        - url (str): A URL da imagem a ser validada.

        Funcionalidades:
        - Define uma lista de extensões de arquivo de imagem que são aceitáveis.
        - Verifica se a URL fornecida termina com uma dessas extensões.

        Retorno:
        - Retorna True se a URL terminar com uma extensão de arquivo de imagem válida, False caso contrário.

        Utilização:
        - Utilizada para validar URLs de imagens, assegurando que os links fornecidos apontem para arquivos de imagem reais que podem ser carregados e exibidos corretamente no KML.
        """
        # Define as extensões de arquivo de imagem que são aceitáveis
        extensoes_validas = ['.jpg', '.jpeg', '.png', '.gif', '.bmp', '.tif', '.tiff', '.webp']
        # Verifica se a URL termina com alguma das extensões válidas
        return any(url.lower().endswith(ext) for ext in extensoes_validas) # Verifica se a URL corresponde a uma extensão válida

    def verificarTexto(self):
        """
        Verifica o conteúdo do campo de entrada para URL da imagem, ajusta a cor do texto baseada na validade da URL
        e atualiza o último texto de URL válido armazenado. Este método é usado para fornecer feedback visual imediato 
        sobre a validade da URL inserida.

        Funcionalidades:
        - Obtém o texto atual do campo QLineEdit destinado à URL da imagem.
        - Verifica se o texto é uma URL válida e se corresponde a uma extensão de arquivo de imagem aceitável.
        - Atualiza o armazenamento do último texto válido ou o limpa se o texto atual não for válido.
        - Altera a cor do texto do QLineEdit para azul se a URL for válida, para vermelho se for inválida, e retorna para a cor padrão se o campo estiver vazio.

        Utilização:
        - Essencial para fornecer uma resposta visual instantânea ao usuário sobre a validade da URL inserida, 
          facilitando a correção de erros e garantindo que apenas URLs válidas sejam utilizadas.
        """
        # Obtém o texto atual do QLineEdit
        texto = self.lineEditImageUrl.text() # Lê o texto da caixa de entrada de URL da imagem
        
        # Verifica a validade da URL e se a URL é uma imagem
        if self.verificarValidadeURL(texto) and self.verificarValidadeURLImagem(texto):
            ExportarKMLDialog.ultimoTextoUrl = texto # Atualiza o último texto válido se a URL for válida
            self.lineEditImageUrl.setStyleSheet("QLineEdit { color: blue; }") # Muda a cor do texto para azul
        else:
            ExportarKMLDialog.ultimoTextoUrl = "" # Limpa o último texto válido se a URL for inválida
            if texto.strip() != "": # Verifica se o campo não está vazio
                self.lineEditImageUrl.setStyleSheet("QLineEdit { color: red; }") # Muda a cor do texto para vermelho se houver texto inválido
            else:
                self.lineEditImageUrl.setStyleSheet("") # Retorna a cor do texto para o padrão se o campo estiver vazio

    def verificarTexto2(self):
        """
        Verifica o conteúdo do campo de entrada para o URL do ScreenOverlay, ajusta a cor do texto baseada na validade da URL,
        e atualiza o último texto de URL válido armazenado. Este método é usado para fornecer feedback visual imediato 
        sobre a validade da URL inserida.

        Funcionalidades:
        - Obtém o texto atual do campo QLineEdit destinado ao URL do ScreenOverlay.
        - Verifica se o texto é uma URL válida e se corresponde a uma extensão de arquivo de imagem aceitável.
        - Atualiza o armazenamento do último texto válido ou o limpa se o texto atual não for válido.
        - Altera a cor do texto do QLineEdit para azul se a URL for válida, para vermelho se for inválida, e retorna para a cor padrão se o campo estiver vazio.

        Utilização:
        - Essencial para fornecer uma resposta visual instantânea ao usuário sobre a validade da URL inserida para o ScreenOverlay,
          facilitando a correção de erros e garantindo que apenas URLs válidas sejam utilizadas para o ScreenOverlay.
        """
        # Obtém o texto atual do QLineEdit destinado ao URL do ScreenOverlay
        texto = self.lineEditImageUrl2.text()  # Lê o texto da caixa de entrada de URL para o ScreenOverlay

        # Verifica a validade da URL e se a URL é uma imagem
        if self.verificarValidadeURL(texto) and self.verificarValidadeURLImagem(texto):
            ExportarKMLDialog.ultimoTextoUrl2 = texto # Atualiza o último texto válido se a URL for válida
            self.lineEditImageUrl2.setStyleSheet("QLineEdit { color: blue; }") # Muda a cor do texto para azul
        else:
            ExportarKMLDialog.ultimoTextoUrl2 = "" # Limpa o último texto válido se a URL for inválida
            if texto.strip() != "": # Verifica se o campo não está vazio
                self.lineEditImageUrl2.setStyleSheet("QLineEdit { color: red; }") # Muda a cor do texto para vermelho se houver texto inválido
            else:
                self.lineEditImageUrl2.setStyleSheet("") # Retorna a cor do texto para o padrão se o campo estiver vazio

    def getValues(self):
        """
        Coleta e retorna todos os valores dos controles de entrada definidos no diálogo. 
        Isso inclui informações sobre o campo de rótulo, espessura da linha, altitude, URLs de imagem,
        e opções como tabela de atributos, visualização em 3D e número de repetições.

        Retorno:
        - Retorna uma tupla contendo:
          - O texto atual do comboBox para seleção do campo de rótulo.
          - O valor atual da espessura da linha.
          - O valor atual da altitude.
          - O texto do campo de entrada para a URL da imagem da tabela.
          - O texto do campo de entrada para a URL do ScreenOverlay.
          - O estado atual da caixa de seleção para incluir tabela de atributos.
          - O estado atual da caixa de seleção para visualização em 3D.
          - O valor atual do número de repetições.

        Utilização:
        - Usado para capturar todas as configurações do usuário em um único ponto, facilitando a passagem dessas informações 
          para outras partes do sistema que processam a exportação para KML.
        """
        # Retorna todos os valores relevantes como uma tupla
        return (
            self.comboBoxCampo.currentText(),  # Texto atual do comboBox para o campo de rótulo
            self.doubleSpinBoxEspessura.value(),  # Valor atual da espessura da linha
            self.doubleSpinBoxAltitude.value(),  # Valor atual da altitude
            self.lineEditImageUrl.text(),  # Texto atual do campo de entrada para a URL da imagem
            self.lineEditImageUrl2.text(),  # Texto atual do campo de entrada para a URL do ScreenOverlay
            self.checkBoxTabela.isChecked(),  # Estado atual da caixa de seleção para incluir tabela de atributos
            self.checkBox3D.isChecked(),  # Estado atual da caixa de seleção para visualização em 3D
            self.spinBoxRepete.value())  # Número de repetições definido pelo usuário

class CloneManager:
    def __init__(self, ui_manager, layer_to_clone):
        """
        Inicializa a classe CloneManager, que gerencia as operações de clonagem de camadas dentro de um aplicativo GIS.
        
        :param ui_manager: Uma referência ao gerenciador de interface do usuário, responsável por interações e atualizações da UI.
        :param layer_to_clone: A camada que será clonada. Esta camada pode ser qualquer tipo de camada suportada pelo GIS, como camadas vetoriais.
        """
        self.ui_manager = ui_manager  # Armazena a referência ao gerenciador de interface do usuário para operações relacionadas à UI.
        self.layer_to_clone = layer_to_clone  # Armazena a camada que será clonada, usada nas diversas operações de clonagem.

    def tr(self, message):
        return QCoreApplication.translate("CloneManager", message)

    def show_clone_options(self):
        """
        Exibe uma janela de diálogo com opções para o usuário selecionar o tipo de clonagem desejado.
        
        A função cria um diálogo modal que permite ao usuário escolher entre diferentes tipos de clonagem:
        1. Clonar apenas a geometria das feições, sem copiar a tabela de atributos.
        2. Copiar apenas a tabela de atributos, sem as feições.
        3. Combinar ambos, copiando as feições e a tabela de atributos, e tratar linhas específicas.
        4. Excluir a tabela de atributos da clonagem, mantendo apenas as feições e tratando linhas específicas.
        
        A escolha é feita por meio de botões de rádio, e a opção selecionada é passada para a função de clonagem correspondente.
        """
        # Criação de um diálogo como um subdiálogo do diálogo principal
        dialog = QDialog(self.ui_manager.dlg)  # Acesso ao dlg através de ui_manager
        dialog.setWindowTitle(self.tr("Escolher Tipo de Clonagem")) # Define o título do diálogo
        layout = QVBoxLayout(dialog) # Layout vertical para organizar os elementos internos

        # Criação de um grupo de botões para gerenciar as opções de clonagem
        button_group = QButtonGroup(dialog)  # Deve ser criado antes de ser usado

        # Definição dos botões de rádio para cada opção de clonagem
        self.radio_buttons = {
            1: QRadioButton(self.tr("Clonar Feição, sem a Tabela")),
            2: QRadioButton(self.tr("Copiar Tabela de Atributos")),
            3: QRadioButton(self.tr("Combinar Tabela e Tratar Linhas")),
            4: QRadioButton(self.tr("Excluir Tabela e Tratar Linhas"))}

        for id, radio in self.radio_buttons.items():
            # Cria um QFrame como contêiner para cada QRadioButton
            frame = QFrame(dialog)
            frame_layout = QVBoxLayout(frame)
            frame.setFrameShape(QFrame.Shape.StyledPanel) # Estilo do contêiner
            frame.setFrameShadow(QFrame.Shadow.Raised)
            frame.setFixedSize(200, 30)  # Define a largura e altura do QFrame

            # Adição do botão de rádio ao layout do contêiner
            frame_layout.addWidget(radio)
            layout.addWidget(frame)
            
            # Adiciona o QRadioButton ao QButtonGroup para garantir a seleção exclusiva
            button_group.addButton(radio, id)

            # Seleciona por padrão a primeira opção de clonagem
            if id == 1:
                radio.setChecked(True)

        # Criação e configuração de botões de ação para confirmar ou cancelar
        buttonBox = QDialogButtonBox(QDialogButtonBox.StandardButton.Ok | QDialogButtonBox.StandardButton.Cancel)
        buttonBox.accepted.connect(dialog.accept) # Conecta o botão OK à aceitação do diálogo
        buttonBox.rejected.connect(dialog.reject)   # Conecta o botão Cancelar à rejeição do diálogo
        layout.addWidget(buttonBox)

        # Criação de um layout horizontal para centralizar os botões
        hLayout = QHBoxLayout()
        hLayout.addStretch()  # Adiciona um espaço flexível antes dos botões
        hLayout.addWidget(buttonBox)  # Adiciona o QDialogButtonBox ao layout horizontal
        hLayout.addStretch()  # Adiciona um espaço flexível após os botões

        # Adiciona o layout horizontal ao layout principal do diálogo
        layout.addLayout(hLayout)

        result = dialog.exec() # Executa o diálogo e verifica o resultado após o fechamento
        if result == QDialog.DialogCode.Accepted:
            # Identifica o botão de rádio selecionado e realiza a clonagem correspondente
            for id, radio in self.radio_buttons.items():
                if radio.isChecked():
                    self.realizar_clonagem(id) # Chama a função de clonagem com o tipo selecionado
                    break

    def realizar_clonagem(self, tipo_clonagem):
        """
        Determina o tipo de clonagem a ser realizado na camada e chama a função correspondente.
        
        Esta função serve como um controlador que, com base no tipo de clonagem fornecido como argumento,
        direciona para a função específica de clonagem. As opções de clonagem incluem:
        1. Clonar apenas as feições sem os atributos.
        2. Clonar apenas os atributos sem as feições.
        3. Combinar os atributos e feições em uma clonagem completa.
        4. Clonar a camada excluindo certos atributos.
        
        Parâmetros:
        - tipo_clonagem: Inteiro que indica o tipo de clonagem desejada.
        """
        # Verificação do tipo de clonagem e chamada da função correspondente
        if tipo_clonagem == 1:
            self.clone_feicao()  # Chama a função para clonar apenas as feições
        elif tipo_clonagem == 2:
            self.clone_atributos()  # Chama a função para clonar apenas os atributos
        elif tipo_clonagem == 3:
            self.clone_combinar()  # Chama a função para combinar clonagem de atributos e feições
        elif tipo_clonagem == 4:
            self.clone_excluir()  # Chama a função para clonar a camada excluindo certos atributos

    def criar_camada_clonada(self, name_suffix, fields=None, features_to_add=None, set_renderer=True, only_id_comp=False):
        """
        Cria uma camada clonada baseada na camada original, com opções para customizar os campos,
        as feições a serem adicionadas, e se o renderizador da camada original deve ser copiado.
        A camada clonada é adicionada a um grupo específico no projeto chamado "Camadas Clonadas".

        Processo:
        1. Prepara o nome e verifica se a camada original é temporária.
        2. Define o tipo de geometria e o sistema de referência de coordenadas (CRS) baseando-se na camada original.
        3. Cria a camada clonada como uma camada de memória.
        4. Verifica se a camada clonada foi criada corretamente.
        5. Adiciona os campos especificados à camada clonada.
        6. Adiciona as feições especificadas à camada clonada.
        7. Copia o renderizador da camada original, se solicitado.
        8. Adiciona a camada clonada ao grupo "Camadas Clonadas" no projeto.

        Parâmetros:
        - name_suffix: Sufixo para o nome da camada clonada.
        - fields: Campos a serem adicionados à camada clonada. Se None, copia todos os campos da original.
        - features_to_add: Feições a serem adicionadas à camada clonada. Se None, copia todas as feições da original.
        - set_renderer: Booleano para decidir se o renderizador da camada original será copiado.
        - only_id_comp: Não utilizado diretamente nesta função, pode ser parte de uma implementação futura ou customização.
        """
        # Preparação do nome da camada clonada e verificação se a camada original é temporária
        clone_name = f"{name_suffix}_{self.layer_to_clone.name()}"
        is_temporary = "memory:" in self.layer_to_clone.source()

        # Define o tipo de geometria e o CRS baseados na camada original, para todas as novas camadas
        geom_type = self.layer_to_clone.geometryType()
        geom_type_str = ["Point", "LineString", "Polygon"][geom_type]  # Ajuste conforme necessário
        crs = self.layer_to_clone.crs().authid()
        clone = QgsVectorLayer(f"{geom_type_str}?crs={crs}", clone_name, "memory")

        # Verificação da validade da camada clonada
        if not clone.isValid():
            QMessageBox.critical(None, self.tr("Erro"), self.tr("Não foi possível criar a camada clonada."))
            return None

        # Adiciona campos à camada clonada
        clone_provider = clone.dataProvider()

        # Adiciona apenas os campos especificados, se fornecidos
        if fields is not None:
            clone_provider.addAttributes(fields.toList())
        else:
             # Se não forem especificados campos, copia todos os campos da camada original
            clone_provider.addAttributes(self.layer_to_clone.fields().toList())
        clone.updateFields() # Atualiza os campos na camada clonada

        # Aplica aliases traduzidos aos campos conhecidos.
        self.ui_manager._aplicar_alias_comprimento(clone)

        # Adiciona feições à camada clonada
        if features_to_add is not None:
            clone_provider.addFeatures(features_to_add)
        else:
            # Se não especificado, copia todas as feições da camada original
            all_features = [feat for feat in self.layer_to_clone.getFeatures()]
            clone_provider.addFeatures(all_features)

        # Copia o renderizador da camada original se solicitado
        if set_renderer:
            clone.setRenderer(self.layer_to_clone.renderer().clone())

        # Adiciona a camada clonada ao projeto e ao grupo "Camadas Clonadas"
        QgsProject.instance().addMapLayer(clone, False) # Adiciona a camada ao projeto sem mostrá-la imediatamente
        root = QgsProject.instance().layerTreeRoot()
        my_group = root.findGroup(self.tr("Camadas Clonadas")) # Procura o grupo de camadas clonadas
        if not my_group:
            my_group = root.addGroup(self.tr("Camadas Clonadas")) # Cria o grupo se não existir
        my_group.addLayer(clone) # Adiciona a camada ao grupo

        return clone # Retorna a camada clonada

    def clone_feicao(self):
        """
        Clona as feições de uma camada selecionada, excluindo seus atributos, resultando em uma nova camada apenas com geometrias.

        Processo:
        1. Itera por cada feição na camada original, copiando apenas a geometria para uma nova feição sem atributos.
        2. Cria uma nova camada "clone" que contém apenas as geometrias das feições, sem os campos de atributos.
        3. Armazena a camada clonada para uso posterior.
        4. Exibe uma mensagem de sucesso ao concluir a clonagem.
        """

        # Cria uma lista para armazenar as novas feições sem atributos
        features_to_add = []
        for feat in self.layer_to_clone.getFeatures():
            new_feat = QgsFeature() # Cria uma nova feição sem atributos, copiando apenas a geometria
            new_feat.setGeometry(feat.geometry())
            features_to_add.append(new_feat) # Adiciona a nova feição à lista

        # Cria a camada clonada sem passar os campos (ou seja, sem tabela de atributos)
        clone = self.criar_camada_clonada(self.tr("Clone_SemTabela"), features_to_add=features_to_add, fields=QgsFields())

        if clone is not None: # Verifica se a clonagem foi bem-sucedida e armazena a camada clonada
            self.cloned_layer = clone  # Armazenar a camada clonada para uso posterior

        # Exibe uma mensagem de sucesso na interface do usuário
        self.ui_manager.mostrar_mensagem(self.tr("Clonagem de feição realizada com sucesso."), "Sucesso")

    def clone_atributos(self):
        """
        Clona uma camada selecionada, incluindo tanto as geometrias quanto os atributos das feições, 
        resultando em uma nova camada idêntica à original.

        Processo:
        1. Copia todos os campos (atributos) da camada original.
        2. Itera por cada feição na camada original, copiando tanto a geometria quanto os atributos para novas feições.
        3. Cria uma nova camada clonada que contém as novas feições com geometrias e atributos.
        4. Define o renderizador da camada clonada para ser o mesmo da camada original.
        5. Armazena a camada clonada para uso posterior.
        6. Exibe uma mensagem de sucesso ao concluir a clonagem dos atributos.
        """

        # Recupera os campos e as feições da camada original
        fields = self.layer_to_clone.fields() # Campos (atributos) da camada original
        features = [feat for feat in self.layer_to_clone.getFeatures()] # Lista de feições da camada original

        # Prepara uma nova lista para armazenar as feições clonadas com atributos
        new_features = []
        for feature in features:
            new_feature = QgsFeature(fields) # Cria uma nova feição com os mesmos campos da camada original
            new_feature.setGeometry(feature.geometry())  # Copia a geometria da feição original
            for field in fields.names():
                new_feature.setAttribute(field, feature[field])  # Copia cada atributo da feição original
            new_features.append(new_feature)  # Adiciona a nova feição à lista

        # Utiliza a função criar_camada_clonada para criar e adicionar a camada clonada ao projeto
        clone = self.criar_camada_clonada(self.tr("Clone_Tabela"), fields, new_features)

        # Verifica se a clonagem foi bem-sucedida
        if not clone:
            return  # Falha ao criar a camada clonada, a mensagem de erro já foi exibida

        # Configura o renderizador da camada clonada para ser igual ao da camada original
        clone.setRenderer(self.layer_to_clone.renderer().clone())

        # Armazena a referência à camada clonada para uso posterior
        self.cloned_layer = clone

        # Exibe uma mensagem de sucesso na interface do usuário
        self.ui_manager.mostrar_mensagem(self.tr("Clonagem de atributos realizada com sucesso."), "Sucesso")

    def clone_combinar(self):
        """
        Combina a clonagem de feições com a adição e ajuste de campos específicos ("ID" e "Comprimento"), 
        resultando em uma camada clonada que inclui campos originais, excluindo possíveis duplicatas 
        de "ID" e "Comprimento", e adiciona estes dois campos com valores atualizados.

        Processo:
        1. Prepara uma nova estrutura de campos, adicionando campos "ID" e "Comprimento" antes dos campos originais.
        2. Exclui os campos "ID" e "Comprimento" da camada original se já existirem, para evitar duplicatas.
        3. Itera por cada feição na camada original, criando novas feições com geometrias idênticas.
        4. Ajusta os valores de "ID" (incremental) e "Comprimento" (comprimento da geometria) para cada nova feição.
        5. Copia os atributos restantes da feição original para a nova feição, ajustando os índices conforme necessário.
        6. Cria uma nova camada clonada com a estrutura de campos ajustada e as novas feições.
        7. Aplica um tratamento adicional para os campos "ID" e "Comprimento" na camada clonada, se necessário.
        8. Exibe uma mensagem de sucesso ao concluir a operação.
        """

        # Inicializa a estrutura de campos para a nova camada, incluindo "ID" e "Comprimento"
        fields_to_add = QgsFields()

        # Adiciona primeiramente os campos "ID" e "Comprimento"
        fields_to_add.append(QgsField("ID", QMetaType.Type.Int))
        fields_to_add.append(QgsField("Comprimento", QMetaType.Type.Double))

        # Recupera os campos da camada original
        original_fields = self.layer_to_clone.fields()

        # Adiciona os campos da camada original, excluindo "ID" e "Comprimento" se já existirem
        for field in original_fields:
            if field.name() not in ["ID", "Comprimento"]:
                fields_to_add.append(field)

        # Lista para armazenar as novas feições com campos ajustados
        new_features = []
        for index, feature in enumerate(self.layer_to_clone.getFeatures(), start=1):
            new_feature = QgsFeature(fields_to_add)  # Cria uma nova feição com a estrutura de campos atualizada
            new_feature.setGeometry(feature.geometry()) # Copia a geometria

            # Prepara uma lista de atributos com espaços reservados para todos os campos
            new_attributes = [None] * len(fields_to_add)

            # Ajusta os valores de "ID" e "Comprimento" diretamente
            new_attributes[0] = index  # ID baseado no índice da iteração
            new_attributes[1] = round(feature.geometry().length(), 3) # Comprimento calculado a partir da geometria

            # Copia os atributos da feição original, ajustando para a nova estrutura de campos
            original_attributes = feature.attributes()
            for i, field in enumerate(original_fields):
                if field.name() not in ["ID", "Comprimento"]:
                    # Encontra o índice correto para o atributo na nova lista de campos
                    new_index = fields_to_add.indexOf(field.name()) # Encontra o novo índice do campo
                    new_attributes[new_index] = original_attributes[i] # Atribui o valor correspondente

            new_feature.setAttributes(new_attributes) # Atualiza os atributos da nova feição
            new_features.append(new_feature) # Adiciona a feição à lista

        # Cria a camada clonada com os campos e feições preparados
        clone = self.criar_camada_clonada("Clone_Combinado", fields=fields_to_add, features_to_add=new_features)

        # Chama a função tratar_linhas para tratar os campos "ID" e "Comprimento" na camada clonada
        self.ui_manager.tratar_linhas(clone)

        if clone: # Aplica tratamento adicional se necessário
            # Chama a função para tratar "ID" e "Comprimento" se necessário
            self.ui_manager.mostrar_mensagem(self.tr("Combinação de tabela e tratamento de linhas realizados com sucesso."), "Sucesso")

        return clone # Retorna a camada clonada

    def clone_excluir(self):
        """
        Cria uma camada clonada que exclui todos os campos originais exceto a geometria,
        adicionando apenas dois novos campos: "ID" e "Comprimento". "ID" é um identificador sequencial
        e "Comprimento" representa o comprimento da geometria da feição. Esta função é útil para simplificar
        a camada, mantendo apenas informações essenciais e a geometria.

        Processo:
        1. Prepara uma nova estrutura de campos contendo apenas "ID" e "Comprimento".
        2. Itera pelas feições da camada original, copiando suas geometrias.
        3. Para cada nova feição, calcula e atribui um ID sequencial e o comprimento da geometria.
        4. Cria uma camada clonada com a nova estrutura de campos e as novas feições.
        5. Aplica um tratamento adicional para os campos "ID" e "Comprimento", se necessário.
        6. Exibe uma mensagem de sucesso ao concluir a operação.
        """

        # Inicializa os campos para a nova camada com "ID" e "Comprimento"
        new_fields = QgsFields()
        new_fields.append(QgsField("ID", QMetaType.Type.Int))
        new_fields.append(QgsField("Comprimento", QMetaType.Type.Double))

        # Lista para armazenar as novas feições com os valores de "ID" e "Comprimento" definidos
        new_features = []
        for index, feature in enumerate(self.layer_to_clone.getFeatures(), start=1):
            new_feature = QgsFeature(new_fields) # Cria uma nova feição com a estrutura de campos atualizada
            new_feature.setGeometry(feature.geometry()) # Copia a geometria da feição original
            new_feature.setAttribute("ID", index)   # Atribui um ID sequencial
            new_feature.setAttribute("Comprimento", round(feature.geometry().length(), 3))  # Calcula e atribui o comprimentodecimais
            new_features.append(new_feature) # Adiciona a nova feição à lista

        # Utiliza a função de utilidade para criar a camada clonada com os novos campos e feições
        clone = self.criar_camada_clonada(self.tr("Clone_Excluir"), new_fields, new_features)

        if clone is None:
            QMessageBox.critical(None, self.tr("Erro"), self.tr("Falha ao criar a camada clonada.")) # Exibe uma mensagem de erro se a clonagem falhar
            return

        # Chamada para tratar os campos "ID" e "Comprimento" após a clonagem
        self.ui_manager.tratar_linhas(clone)

        # Armazena a referência à camada clonada para uso posterior
        self.cloned_layer = clone

        # Mensagem de sucesso ao finalizar o processo
        self.ui_manager.mostrar_mensagem(self.tr("Exclusão de tabela e tratamento de linhas realizados com sucesso."), "Sucesso")