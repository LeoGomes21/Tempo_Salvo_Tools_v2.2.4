from qgis.PyQt.QtWidgets import QDialog, QCheckBox, QPushButton, QTableView, QAbstractItemView, QProgressBar, QLineEdit, QStyledItemDelegate, QHeaderView, QMessageBox, QGraphicsScene, QFileDialog, QGraphicsPixmapItem, QGraphicsItem, QDialogButtonBox, QComboBox, QWidget, QVBoxLayout, QFormLayout, QFrame
from qgis.core import Qgis, QgsMessageLog, QgsProject, QgsVectorLayer, QgsWkbTypes, QgsGeometry, QgsPointXY, QgsFeature, QgsVectorDataProvider, QgsCoordinateTransform, QgsCoordinateReferenceSystem, QgsFields, QgsNetworkAccessManager
from qgis.PyQt.QtGui import QStandardItemModel, QStandardItem, QPixmap, QIcon, QPainter, QColor, QBrush, QPen, QImage, QDoubleValidator, QDesktopServices
from qgis.PyQt.QtCore import QDir, Qt, QSize, QEvent, QRect, QPoint, QItemSelectionModel, QSettings, QRectF, QFileInfo, QVariant, QUrl, QCoreApplication, QMetaType
from qgis.PyQt.QtNetwork import QNetworkRequest, QNetworkReply
from qgis.PyQt import uic, QtCore, QtWidgets, QtGui
from qgis.utils import iface
from pathlib import Path
import pandas as pd
import simplekml
import datetime
import zipfile
import random
import time
import math
import os
import re

FORM_CLASS, _ = uic.loadUiType(os.path.join(
    os.path.dirname(__file__), 'imagens_kmz.ui'))

class ImagensManager(QDialog, FORM_CLASS):

    autor_texto = ""  # Variável de classe para armazenar o texto do autor
    exibir_texto = "1400"  # Variável de classe para armazenar o texto de exibição padrão
    icones_imagens = {}  # Dicionário de classe para armazenar os ícones selecionados
    info_imagens = {}  # Dicionário de classe para armazenar todas as informações das imagens
    ultima_pasta = QDir.homePath()  # Variável de classe para armazenar o caminho da última pasta usada

    def __init__(self, parent=None):
        """Constructor."""
        super(ImagensManager, self).__init__(parent)
        # Configura a interface do usuário a partir do Designer.
        self.setupUi(self)
        # Altera o título da janela
        self.setWindowTitle(self.tr("Exporta Imagens para KMZ"))

        self.icon_scene = QGraphicsScene(self)  # Inicializa a cena para o graphicsViewIcones
        self.graphicsViewIcones.setScene(self.icon_scene)  # Define a cena no QGraphicsView

        self._icon_cache = {}
        self._icon_req_serial = 0
        self._icon_pending_serial = 0
        self._icon_pending_url = None
        self._icon_reply = None
        self._nam = QgsNetworkAccessManager.instance()

        # Inicialmente desativa os itens que dependem de imagens carregadas
        self.comboBoxLinks.setEnabled(False)  # Desativa comboBoxLinks
        self.graphicsViewIcones.setEnabled(False)  # Desativa graphicsViewIcones
        self.pushButtonKMZ.setEnabled(False)  # Desativa pushButtonKMZ

        # Restaura os textos dos line edits
        self.lineEdit_Autor.setText(ImagensManager.autor_texto)  # Restaura o texto do autor
        self.lineEditExibir.setText(ImagensManager.exibir_texto if ImagensManager.exibir_texto != "1400" else "")  # Restaura o texto do tempo de exibição
        self.lineEditExibir.setPlaceholderText("1400")  # Define o texto placeholder para lineEditExibir
        self.lineEditExibir2.setPlaceholderText(self.tr("Automático"))  # Define o texto placeholder para lineEditExibir2
        self.lineEditExibir2.setEnabled(False)  # Desativa lineEditExibir2

        # Armazena os estados iniciais dos componentes que precisam ser resetados
        self.lineEdit_Autor_texto_inicial = ImagensManager.autor_texto
        self.lineEditExibir_texto_inicial = self.lineEditExibir.text()

        # Armazena o estilo padrão do botão de cor
        self.pushButton_Screen_default_style = self.pushButton_Screen.styleSheet()

        # Centralizar o texto em lineEditExibir e lineEditExibir2
        self.lineEditExibir.setAlignment(Qt.AlignmentFlag.AlignCenter)  # Centraliza o texto em lineEditExibir
        self.lineEditExibir2.setAlignment(Qt.AlignmentFlag.AlignCenter)  # Centraliza o texto em lineEditExibir2

        # Limitar o número de caracteres e filtrar caracteres inválidos
        self.lineEdit_Autor.setMaxLength(32)  # Limita o número de caracteres no lineEdit_Autor

        # Configurar QLineEdit para serem apenas leitura e permitir seleção e cópia
        line_edits = [
            self.lineEditLatitude, self.lineEditLongitude, self.lineEditResolucao, self.lineEditData, self.lineEditHorario]
        for line_edit in line_edits:
            line_edit.setReadOnly(True)  # Define os QLineEdits como apenas leitura

        # Carregar os links no comboBoxLinks
        self.carregar_links_comboBox()

        # Chamar exibir_icone uma vez para carregar o ícone inicial
        self.exibir_icone()

        # Configurar estilo do comboBoxLinks
        self.comboBoxLinks.setStyleSheet("""
            QComboBox {combobox-popup: 0;}
            QComboBox QAbstractItemView {
                min-height: 140px; /* 10 itens */
                max-height: 140px; /* 10 itens */
                min-width: 90px; /* ajuste conforme necessário */
                max-width: 90px; /* ajuste conforme necessário */}
            """)  # Define o estilo do comboBox

        # Conecta os sinais aos slots
        self.connect_signals()

    def tr(self, message):
        """
        Traduz textos deste diálogo.
        O contexto precisa ser estável para o Qt Linguist encontrar as traduções.
        """
        return QCoreApplication.translate("ImagensManager", message)

    def connect_signals(self):
        self.pushButtonAbrir.clicked.connect(self.abrir_pasta) # Conecta o botão Abrir à função abrir_pasta

        self.pushButtonFecha.clicked.connect(self.close_dialog)  # Conecta o botão para fechar o diálogo

        # self.pushButtonKMZ.clicked.connect(self.exportar_para_kmz)  # Conecta o botão para exportar KMZ

        # Conecta sinais do projeto para atualizar comboBox quando camadas forem adicionadas, removidas ou renomeadas
        QgsProject.instance().layersAdded.connect(self.populate_combo_box)
        QgsProject.instance().layersRemoved.connect(self.populate_combo_box)

        # Conecta a mudança de seleção no comboBoxCamada para atualizar o checkBoxSeleciona
        self.comboBoxCamada.currentIndexChanged.connect(self.update_checkBoxSeleciona)
        
        # Conecta o sinal currentIndexChanged do comboBoxCamada à função update_combo_box_campos
        self.comboBoxCamada.currentIndexChanged.connect(self.update_combo_box_campos)

        self.comboBoxCampos.currentIndexChanged.connect(self._atualizar_selecao_comboCampo)
        
        self.comboBoxCampos.currentIndexChanged.connect(self._sincronizar_comboAtributo)

        self.comboBoxLinks.currentIndexChanged.connect(self.exibir_icone)  # Conecta a mudança de índice do comboBoxLinks à função exibir_icone
        self.comboBoxLinks.currentIndexChanged.connect(self.atualizar_icones)  # Conecta a mudança de índice do comboBoxLinks à função atualizar_icones

        self.comboBoxLinks.currentIndexChanged.connect(self.atualizar_icone_selecionado)

        self.pushButtonAddCoordenadas.clicked.connect(self._adicionar_coordenadas)

        # Conectar sinais de alteração de texto dos line edits para armazenar os valores
        self.lineEdit_Autor.textChanged.connect(lambda texto: self.atualizar_texto('autor_texto', texto))  # Conecta a mudança de texto do autor
        self.lineEditExibir.textChanged.connect(lambda texto: self.validar_formatar_exibir('exibir_texto', texto, self.lineEditExibir))  # Conecta a mudança de texto do exibir

        # aplica só à(s) linha(s) selecionada(s) e mostra o ícone certo
        self.comboBoxLinks.currentIndexChanged.connect(self.atualizar_icone_imagem_selecionada)

        self.pushButton_Screen.clicked.connect(self.abrir_screen_overlay)  # Conecta o botão Screen à função abrir_screen_overlay

        self.pushButtonKMZ.clicked.connect(self.exportar_para_kmz)  # Conecta o botão para exportar KMZ

    def showEvent(self, event):
        """
        Evento disparado ao mostrar o diálogo.

        Este método garante que, ao ser exibido, o diálogo seja resetado para seu estado inicial,
        restaurando todos os componentes a partir do método `resetar_componentes`.
        """
        super(ImagensManager, self).showEvent(event)

        # 1) limpa os dicionários
        ImagensManager.icones_imagens.clear()
        ImagensManager.info_imagens.clear()

        # RESETA A TABELA DE IMAGENS
        empty_model = QStandardItemModel()
        empty_model.setHorizontalHeaderLabels([self.tr("Miniaturas"), self.tr("Ações")])
        self.tableViewImagens.setModel(empty_model)

        # faz com que as colunas fiquem ajustadas
        header = self.tableViewImagens.horizontalHeader()
        header.setSectionResizeMode(QHeaderView.ResizeMode.Stretch)

        self.atualizar_estado_itens()  # Atualiza o estado dos itens baseando-se nas condições atuais

        # Garante que combo e view fiquem desativados
        self.comboBoxLinks.setEnabled(False)

        self.update_checkBoxSeleciona()  # Atualiza o estado do checkBoxSeleciona com base nas feições selecionadas

        self.update_layer_connections()  # Conecta os sinais da camada atual

        self.populate_combo_box()  # Atualiza o comboBoxCamada com as camadas disponíveis
        
        self.update_combo_box_campos() # Atualiza o comboBoxCampos com os campos disponíveis

        # Exibe o primeiro ícone da lista no graphicsViewIcones
        if self.comboBoxLinks.count() > 0:
            self.comboBoxLinks.setCurrentIndex(0)  # Seleciona o primeiro item do comboBox
            self.exibir_icone()  # Exibe o ícone selecionado

        self.comboBoxLinks.setEnabled(False)        # desabilitado até carregar novas imagens

        # Limpar todos os lineEdits de detalhes
        for le in (self.lineEditLatitude,
                   self.lineEditLongitude,
                   self.lineEditResolucao,
                   self.lineEditData,
                   self.lineEditHorario):
            le.clear()

        # Reseta o texto do lineEdit_Autor para o valor salvo inicialmente
        self.lineEdit_Autor.setText(ImagensManager.autor_texto)
        
        # Reseta o texto do lineEditExibir para o valor inicial
        self.lineEditExibir.setText(self.lineEditExibir_texto_inicial)

        # Reseta o estado do pushButton_Screen
        self.pushButton_Screen.setText(self.tr("ScreenOverlay"))  # Reseta o texto para o valor inicial
        self.pushButton_Screen.setStyleSheet(self.pushButton_Screen_default_style)  # Reseta o estilo para o padrão
        self.screen_overlay_data = {}  # Limpa qualquer dado associado ao ScreenOverlay

        self.pushButtonAddCoordenadas.setEnabled(False)

    def atualizar_texto(self, line_edit_name, texto):
        """
        Atualiza o texto armazenado de um QLineEdit específico.

        Parâmetros:
        line_edit_name: str - O nome do atributo de classe que armazena o texto do QLineEdit.
        texto: str - O novo texto a ser armazenado.

        Funções:
        - Usa setattr para atualizar o valor do atributo de classe correspondente ao nome do QLineEdit.
        """
        setattr(ImagensManager, line_edit_name, texto)  # Atualiza o valor do atributo de classe correspondente ao nome do QLineEdit

    def validar_formatar_exibir(self, attr_name, texto, line_edit):
        """
        Valida e formata o texto inserido no QLineEdit, garantindo que seja numérico e dentro de um limite específico.

        Parâmetros:
        attr_name: str - O nome do atributo de classe que armazena o texto validado.
        texto: str - O texto inserido no QLineEdit.
        line_edit: QLineEdit - O QLineEdit a ser atualizado.

        Funções:
        - Remove todos os caracteres não numéricos do texto.
        - Limita o texto a 4 dígitos.
        - Converte o texto para inteiro e verifica se está dentro do valor máximo permitido (4000).
        - Atualiza o QLineEdit com o texto validado e formatado.
        - Armazena o texto validado no atributo de classe correspondente.
        """
        # Remove todos os caracteres não numéricos
        texto = ''.join(filter(str.isdigit, texto))  # Filtra caracteres não numéricos

        # Limita a 4 dígitos
        if len(texto) > 4:
            texto = texto[:4]  # Limita o texto a 4 dígitos

        # Converte para inteiro e verifica o valor máximo
        if texto:
            valor = int(texto)  # Converte o texto para inteiro
            if valor > 4000:
                valor = 4000  # Limita o valor máximo a 4000
            texto = str(valor)  # Converte o valor de volta para string

        # Atualiza o line edit com o texto validado e formatado
        line_edit.setText(texto)  # Atualiza o QLineEdit com o texto validado
        setattr(ImagensManager, attr_name, texto)  # Armazena o texto validado no atributo de classe correspondente

    def atualizar_estado_itens(self):
        """
        Atualiza o estado dos widgets dependendo da presença de imagens no tableViewImagens.
        
        Funções:
        - Verifica se há imagens no modelo do tableViewImagens.
        - Habilita ou desabilita os widgets lineEdit_Nome, comboBoxLinks, graphicsViewIcones e pushButtonKMZ com base na presença de imagens.
        """
        tem_imagens = self.tableViewImagens.model() is not None and self.tableViewImagens.model().rowCount() > 0  # Verifica se há imagens no modelo do tableViewImagens
        # self.lineEdit_Nome.setEnabled(tem_imagens)  # Habilita/desabilita lineEdit_Nome
        self.comboBoxLinks.setEnabled(tem_imagens)  # Habilita/desabilita comboBoxLinks
        self.graphicsViewIcones.setEnabled(tem_imagens)  # Habilita/desabilita graphicsViewIcones
        self.pushButtonKMZ.setEnabled(tem_imagens)  # Habilita/desabilita pushButtonKMZ

    def abrir_pasta(self):
        # Abre um diálogo para selecionar a pasta
        pasta = QFileDialog.getExistingDirectory(self, self.tr("Selecione a pasta com as imagens"), ImagensManager.ultima_pasta)
        
        if pasta:
            # Atualiza a última pasta usada
            ImagensManager.ultima_pasta = pasta

            # Registra o tempo de início
            tempo_inicio = time.time()

            # Lista de extensões de imagem suportadas
            extensoes = ['.png', '.jpg', '.jpeg', '.bmp']
            # Lista de caminhos completos das imagens
            caminhos_imagens = [os.path.join(pasta, arquivo) for arquivo in os.listdir(pasta)
                                if any(arquivo.lower().endswith(ext) for ext in extensoes)]

            if not caminhos_imagens:
                self.mostrar_mensagem(self.tr(
                        "Nenhuma imagem compatível foi encontrada "
                        "na pasta selecionada."), "Aviso", duracao=3)
                return

            # Inicializa a barra de progresso
            progressBar, progressMessageBar = self.iniciar_progress_bar(len(caminhos_imagens))
            
            # Carrega as imagens no TableView com barra de progresso
            self.carregar_imagens_no_tableview(caminhos_imagens, progressBar)

            # Remove a barra de progresso ao finalizar
            iface.messageBar().popWidget(progressMessageBar)

            # HABILITA widgets agora que há imagens
            self.atualizar_estado_itens()    

            # Calcula o tempo de execução
            tempo_execucao = time.time() - tempo_inicio

            # Mostra uma mensagem de sucesso
            self.mostrar_mensagem(self.tr("Imagens carregadas em {tempo_execucao:.2f} segundos.").format(tempo_execucao=tempo_execucao), "Sucesso")
        else:
            # Mostra uma mensagem de erro se nenhuma pasta foi selecionada
            self.mostrar_mensagem(self.tr("Nenhuma pasta foi selecionada."), "Erro")

    def iniciar_progress_bar(self, total_steps):
        progressMessageBar = iface.messageBar().createMessage(self.tr("Carregando imagens"))
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
        iface.messageBar().pushWidget(progressMessageBar, Qgis.MessageLevel.Info)

        # Define o valor máximo da barra de progresso com base no número total de etapas
        progressBar.setMaximum(total_steps)

        return progressBar, progressMessageBar

    def mostrar_mensagem(self, texto, tipo, duracao=3):
        # Obtém a barra de mensagens da interface do QGIS
        bar = iface.messageBar()  # Acessa a barra de mensagens da interface do QGIS

        # Exibe a mensagem com o nível apropriado baseado no tipo
        if tipo == "Erro":
            # Mostra uma mensagem de erro na barra de mensagens com um ícone crítico e a duração especificada
            bar.pushMessage(self.tr("Erro"), texto, level=Qgis.MessageLevel.Critical, duration=duracao)
        elif tipo == "Sucesso":
            # Cria o item da mensagem
            msg = bar.createMessage(self.tr("Sucesso"), texto)
            
            # Adiciona a mensagem à barra com o nível informativo e a duração especificada
            bar.pushWidget(msg, level=Qgis.MessageLevel.Info, duration=duracao)

        elif tipo == "Aviso":
            bar.pushMessage(self.tr("Aviso"), texto, level=Qgis.MessageLevel.Warning, duration=duracao)

        else:
            bar.pushMessage(self.tr("Info"), texto, level=Qgis.MessageLevel.Info, duration=duracao)

    def carregar_links_comboBox(self):
        """
        Carrega uma lista de URLs de ícones no comboBoxLinks, associando cada URL com um nome.

        Funções:
        - Define uma lista de URLs de ícones.
        - Para cada URL na lista, extrai o nome do arquivo sem extensão.
        - Adiciona o nome e a URL ao comboBoxLinks.
        """
        
        icon_urls = [  # Define uma lista de URLs de ícones
            "http://maps.google.com/mapfiles/kml/paddle/go.png",
            "http://maps.google.com/mapfiles/kml/shapes/parks.png",
            "http://maps.google.com/mapfiles/kml/shapes/water.png",
            "http://maps.google.com/mapfiles/kml/shapes/campground.png",
            "http://maps.google.com/mapfiles/kml/shapes/man.png",
            "http://maps.google.com/mapfiles/kml/shapes/woman.png",
            "http://maps.google.com/mapfiles/kml/shapes/flag.png",
            "http://maps.google.com/mapfiles/kml/shapes/info.png",
            "http://maps.google.com/mapfiles/kml/shapes/airports.png",
            "http://maps.google.com/mapfiles/kml/shapes/poi.png",
            "http://maps.google.com/mapfiles/kml/paddle/blu-circle.png",
            "http://maps.google.com/mapfiles/kml/paddle/ylw-diamond.png",
            "http://maps.google.com/mapfiles/kml/paddle/red-stars.png",
            "http://maps.google.com/mapfiles/kml/paddle/ltblu-square.png",
            "http://maps.google.com/mapfiles/kml/paddle/orange-circle.png",
            "http://maps.google.com/mapfiles/kml/shapes/ranger_station.png",
            "http://earth.google.com/images/kml-icons/track-directional/track-8.png",
            "http://maps.google.com/mapfiles/kml/shapes/gas_stations.png",
        ]
        for url in icon_urls:  # Para cada URL na lista
            name = os.path.splitext(os.path.basename(url))[0]  # Extrai o nome do arquivo sem extensão
            self.comboBoxLinks.addItem(name, url)  # Adiciona o nome e a URL ao comboBoxLinks

    def _linhas_selecionadas(self) -> set[int]:
        sel_model = self.tableViewImagens.selectionModel()
        if not sel_model:
            return set()

        # Preferencial: seleção por linha (estável)
        rows = {idx.row() for idx in sel_model.selectedRows(0)}
        if rows:
            return rows

        # Fallback: caso algum estilo/seleção estranha marque só células
        return {idx.row() for idx in sel_model.selectedIndexes()}

    def atualizar_icone_imagem_selecionada(self):
        # 1) Seleção (sempre por linha)
        sel = self.tableViewImagens.selectionModel()
        if not sel:
            return
        rows = sel.selectedRows(0)
        if not rows:
            return

        row = rows[0].row()

        # 2) Path & URL (o path fica na coluna 0, UserRole)
        modelo = self.tableViewImagens.model()
        if not modelo:
            return

        caminho = modelo.index(row, 0).data(Qt.ItemDataRole.UserRole)
        url = self.comboBoxLinks.currentData()
        if not caminho or not url:
            return

        # 3) Atualiza dicts
        ImagensManager.icones_imagens[caminho] = url
        if caminho in ImagensManager.info_imagens:
            ImagensManager.info_imagens[caminho]["icon_url"] = url

        # 4) Redesenha
        self.exibir_icone()

    def atualizar_icone_selecionado(self):
        sel = self.tableViewImagens.selectionModel()
        if not sel:
            return
        rows = sel.selectedRows(0)
        if not rows:
            return

        row = rows[0].row()
        modelo = self.tableViewImagens.model()
        if not modelo:
            return

        caminho_imagem = modelo.index(row, 0).data(Qt.ItemDataRole.UserRole)
        if not caminho_imagem:
            return

        icon_url = ImagensManager.icones_imagens.get(caminho_imagem)
        if not icon_url:
            return

        self.comboBoxLinks.blockSignals(True)
        self.comboBoxLinks.setCurrentIndex(self.comboBoxLinks.findData(icon_url))
        self.comboBoxLinks.blockSignals(False)
        self.exibir_icone()

    def atualizar_icones(self):
        """
        • Se houver ≥1 linha selecionada → muda o ícone só dessas linhas  
        • Se não houver seleção → muda o ícone de TODAS as linhas
        """
        url = self.comboBoxLinks.currentData()
        if not url:
            return

        modelo = self.tableViewImagens.model()
        if not modelo:
            return

        linhas = self._linhas_selecionadas()
        if not linhas:                       # nenhuma seleção → todas
            linhas = range(modelo.rowCount())

        for row in linhas:
            path = modelo.index(row, 0).data(Qt.ItemDataRole.UserRole)
            if path:
                ImagensManager.icones_imagens[path] = url

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
        current_layer_id = self.comboBoxCamada.currentData()  # Salva a camada atualmente selecionada
        self.comboBoxCamada.blockSignals(True)  # Bloqueia os sinais para evitar chamadas desnecessárias a update_poligono_edit_nome
        self.comboBoxCamada.clear()  # Limpa o comboBox antes de preencher

        layer_list = QgsProject.instance().mapLayers().values()
        for layer in layer_list:
            if isinstance(layer, QgsVectorLayer) and QgsWkbTypes.geometryType(layer.wkbType()) == QgsWkbTypes.GeometryType.PointGeometry:
                self.comboBoxCamada.addItem(layer.name(), layer.id())
                # evita conexões duplicadas ao repopular o combo
                try:
                    layer.nameChanged.disconnect(self.update_combo_box_item)
                except (TypeError, RuntimeError):
                    pass  # nosec B110
                layer.nameChanged.connect(self.update_combo_box_item)

        # Restaura a seleção anterior, se possível
        if current_layer_id:
            index = self.comboBoxCamada.findData(current_layer_id) # Tenta encontrar a camada selecionada anteriormente
            if index != -1:
                self.comboBoxCamada.setCurrentIndex(index) # Restaura a seleção anterior

        self.comboBoxCamada.blockSignals(False)  # Desbloqueia os sinais

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

    def carregar_imagens_no_tableview(self, caminhos_imagens, progressBar):
        # Modelo para o TableView com miniaturas e widgets de combo
        modelo = QStandardItemModel()
        modelo.setHorizontalHeaderLabels([self.tr("Miniaturas"), self.tr("Ações")])

        for i, caminho in enumerate(caminhos_imagens):
            # coluna 0: miniatura
            pixmap = QPixmap(caminho)
            if pixmap.width() > 120 or pixmap.height() > 120:
                pixmap = pixmap.scaled(120, 120, Qt.AspectRatioMode.KeepAspectRatio, Qt.TransformationMode.SmoothTransformation)
            thumb_item = QStandardItem()
            thumb_item.setIcon(QIcon(pixmap))
            thumb_item.setData(caminho, Qt.ItemDataRole.UserRole)

            # coluna 1: placeholder
            placeholder = QStandardItem()
            modelo.appendRow([thumb_item, placeholder])
            progressBar.setValue(i + 1)

        self.tableViewImagens.setModel(modelo)


        # Ícone padrão = o primeiro item do combo
        icone_padrao = self.comboBoxLinks.itemData(0)
        for caminho in caminhos_imagens:
            ImagensManager.icones_imagens.setdefault(caminho, icone_padrao)

        # PREENCHE DICIONÁRIO DE INFO COM META-DADOS DA IMAGEM
        for caminho in caminhos_imagens:
            # resolução (se não conseguir ler, deixa "")
            img = QImage(caminho)

            resol = (""
                if img.isNull()
                else f"{img.width()}×{img.height()}")

            # data e hora (modificação do arquivo)
            try:
                ts   = os.path.getmtime(caminho)
                dt = datetime.datetime.fromtimestamp(ts)

                data = dt.strftime("%d/%m/%Y")
                hora = dt.strftime("%H:%M:%S")
            except Exception:
                data = hora = ""

            ImagensManager.info_imagens[caminho] = {
                'icon_url'  : icone_padrao,
                'feature_id': None,      # ainda não tem feição
                'latitude'  : None,
                'longitude' : None,
                'resolution': resol,
                'date'      : data,
                'time'      : hora}

        # instala o botão-“x” sobre a coluna das miniaturas
        self._del_delegate = DeleteButtonDelegate(self)      # passa self p/ chamar remover_imagem
        self.tableViewImagens.setItemDelegateForColumn(0, self._del_delegate)

        self.tableViewImagens.setSelectionBehavior(QAbstractItemView.SelectionBehavior.SelectRows)
        self.tableViewImagens.setEditTriggers(QAbstractItemView.EditTrigger.NoEditTriggers)
        self.tableViewImagens.setIconSize(QSize(120, 120))

        # ajusta altura das linhas
        for row in range(modelo.rowCount()):
            # altura = modelo.item(row, 
            icon = modelo.item(row, 0).icon()
            sizes = icon.availableSizes()
            altura = sizes[0].height() if sizes else self.tableViewImagens.iconSize().height()
            self.tableViewImagens.setRowHeight(row, altura)

        # redimensiona colunas
        header = self.tableViewImagens.horizontalHeader()
        header.setSectionResizeMode(0, QHeaderView.ResizeMode.ResizeToContents)
        header.setSectionResizeMode(1, QHeaderView.ResizeMode.Stretch)

        # insere widgets de combo na coluna 1
        for row in range(modelo.rowCount()):
            idx = modelo.index(row, 1)
            combo_widget = self.create_combo_widget()
            self.tableViewImagens.setIndexWidget(idx, combo_widget)

        self._sincronizar_itens_comboCampo()
        
        self._sincronizar_comboAtributo()  # NOVO

        # depois de self.tableViewImagens.setModel(modelo) e _sincronizar…
        sel_model = self.tableViewImagens.selectionModel()
        sel_model.selectionChanged.connect(self._on_imagem_selection_changed)

        # depois de sel_model.selectionChanged.connect(self._on_imagem_selection_changed)
        sel_model.selectionChanged.connect(self._update_add_button_state)

        # faça uma chamada inicial pra refletir o estado sem seleção:
        self._update_add_button_state()

    def _mostrar_pixmap_icone(self, pixmap: QPixmap):
        """
        Renderiza o pixmap do ícone no graphicsViewIcones.
        """
        self.graphicsViewIcones.setRenderHints(
            QPainter.RenderHint.Antialiasing | QPainter.RenderHint.SmoothPixmapTransform)

        self.icon_scene.clear()
        self.icon_scene.addPixmap(pixmap)

        rect = QRectF(pixmap.rect())
        self.graphicsViewIcones.setSceneRect(rect)
        self.graphicsViewIcones.fitInView(rect, Qt.AspectRatioMode.KeepAspectRatio)

    def _on_icon_reply_finished(self, serial: int, url: str, reply):
        """
        Callback de download do ícone. Falhas de preview ficam no log, sem erro visual.
        """
        try:
            if serial != self._icon_pending_serial:
                return

            if bool(reply.property("ignore_icon_error")):
                return

            network_error_enum = getattr(QNetworkReply, "NetworkError", QNetworkReply)

            no_error = getattr(network_error_enum, "NoError")

            if reply.error() != no_error:
                url_key = str(reply.property("icon_url_original") or url or reply.url().toString())
                QgsMessageLog.logMessage(
                    self.tr("Falha ao carregar pré-visualização do ícone: {url} | erro: {error}").format(
                        url=url_key, error=reply.errorString()),
                    "TempoSalvoTools",
                    Qgis.MessageLevel.Warning)
                return

            data_bytes = bytes(reply.readAll())
            if not data_bytes:
                url_key = str(reply.property("icon_url_original") or url)
                QgsMessageLog.logMessage(
                    self.tr("Resposta vazia ao baixar ícone: {url}").format(url=url_key),
                    "TempoSalvoTools",
                    Qgis.MessageLevel.Warning)
                return

            pixmap = QPixmap()
            if not pixmap.loadFromData(data_bytes) or pixmap.isNull():
                url_key = str(reply.property("icon_url_original") or url)
                QgsMessageLog.logMessage(
                    self.tr("Não foi possível decodificar o ícone: {url}").format(url=url_key),
                    "TempoSalvoTools",
                    Qgis.MessageLevel.Warning)
                return

            url_key = str(reply.property("icon_url_original") or url)
            self._icon_cache[url_key] = pixmap
            self._mostrar_pixmap_icone(pixmap)

        finally:
            try:
                reply.deleteLater()
            except Exception:
                pass  # nosec B110

            if self._icon_reply is reply:
                self._icon_reply = None

    def exibir_icone(self):
        """
        Exibe o ícone selecionado no comboBoxLinks usando download assíncrono.
        """
        current_url = self.comboBoxLinks.currentData()
        if not current_url:
            return

        if current_url in self._icon_cache:
            self._mostrar_pixmap_icone(self._icon_cache[current_url])
            return

        if self._icon_reply is not None and current_url == self._icon_pending_url:
            return

        if self._icon_reply is not None:
            old_reply = self._icon_reply
            try:
                self._icon_pending_serial = -1
                old_reply.setProperty("ignore_icon_error", True)
                old_reply.abort()
            except Exception:
                pass  # nosec B110
            self._icon_reply = None

        self._icon_req_serial += 1
        serial = self._icon_req_serial
        self._icon_pending_serial = serial
        self._icon_pending_url = current_url

        request_url = current_url
        if request_url.startswith("http://"):
            request_url = "https://" + request_url[len("http://"):]

        req = QNetworkRequest(QUrl(request_url))
        reply = self._nam.get(req)
        reply.setProperty("icon_url_original", current_url)
        reply.setProperty("ignore_icon_error", False)

        self._icon_reply = reply
        reply.finished.connect(lambda s=serial, u=current_url, r=reply: self._on_icon_reply_finished(s, u, r))

    def _parse_coord_float(self, txt: str) -> float:
        s = (txt or "").strip().replace(" ", "")
        if not s:
            raise ValueError("vazio")

        sign = ""
        if s[0] in "+-":
            sign, s = s[0], s[1:]

        s = re.sub(r"[^0-9,\.]", "", s)

        if "." in s and "," in s:
            if s.rfind(",") > s.rfind("."):
                s = s.replace(".", "").replace(",", ".")
            else:
                s = s.replace(",", "")
        elif "," in s:
            s = s.replace(",", ".")
        else:
            if s.count(".") > 1:
                parts = s.split(".")
                s = "".join(parts[:-1]) + "." + parts[-1]

        return float(sign + s)

    def update_combo_box_campos(self):
        """
        Atualiza o comboBoxCampos com os campos da camada selecionada no comboBoxCamada.
        Esta função é chamada sempre que uma nova camada é selecionada no comboBoxCamada.
        Ela garante que o comboBoxCampos exiba apenas os campos da camada atualmente selecionada.
        """
        # Limpa o conteúdo atual do comboBoxCampos para evitar duplicatas ou campos de camadas anteriores
        self.comboBoxCampos.clear()

        # Obtém o ID da camada selecionada no comboBoxCamada
        layer_id = self.comboBoxCamada.currentData()

        # Se nenhum ID de camada for encontrado, significa que não há camada selecionada
        if not layer_id:
            return

        # Obtém a instância da camada usando o ID
        layer = QgsProject.instance().mapLayer(layer_id)

        # Se a camada não for encontrada (pode ocorrer se a camada foi removida do projeto), a função é encerrada
        if not layer:
            return

        # Verifica se a camada é um vetor (QgsVectorLayer)
        if not isinstance(layer, QgsVectorLayer):
            return

        # Obtém os campos da camada usando o método fields()
        fields = layer.fields()

        # Verifica se a camada possui campos
        if fields.isEmpty():
            return

        # Itera sobre os campos da camada e adiciona seus nomes ao comboBoxCampos
        for field in fields:
            self.comboBoxCampos.addItem(field.name())

        self._sincronizar_itens_comboCampo()

        self._sincronizar_comboAtributo()

    def closeEvent(self, event):
        """
        Cancela o download assíncrono do preview do ícone ao fechar o diálogo.
        """
        if getattr(self, "_icon_reply", None) is not None:
            try:
                self._icon_pending_serial = -1
                self._icon_reply.setProperty("ignore_icon_error", True)
                self._icon_reply.abort()
                self._icon_reply.deleteLater()
            except Exception:
                pass  # nosec B110
            self._icon_reply = None

        super(ImagensManager, self).closeEvent(event)

    def close_dialog(self):
        """
        Fecha a janela de diálogo.
        """
        self.close()

    def _copiar_itens_combo(self, origem: QComboBox, destino: QComboBox):
        """Replica textos e `userData` de `origem` em `destino`."""
        destino.blockSignals(True)
        destino.clear()
        for i in range(origem.count()):
            destino.addItem(origem.itemText(i), origem.itemData(i))
        destino.blockSignals(False)

    def create_combo_widget(self):
        widget = QWidget()
        layout = QVBoxLayout(widget)
        layout.setContentsMargins(2, 2, 2, 2)

        comboCampo = QComboBox(widget)
        comboCampo.setObjectName("comboBoxCampo")

        comboAtributo = QComboBox(widget)
        comboAtributo.setObjectName("comboBoxAtributo")

        layout.addWidget(comboCampo)
        layout.addWidget(comboAtributo)

        # Já copia os itens do combo “mestre” na criação
        self._copiar_itens_combo(self.comboBoxCampos, comboCampo)
        comboCampo.setCurrentIndex(self.comboBoxCampos.currentIndex())

        # NOVO: quando o campo mudar, atualiza os atributos dessa linha
        comboCampo.currentIndexChanged.connect(self._on_comboCampo_changed)

        comboAtributo.currentIndexChanged.connect(lambda *_: self._marcar_duplicados_comboAtributo())

        comboAtributo.currentIndexChanged.connect(lambda *_: self._update_add_button_state())

        return widget

    def _atualizar_selecao_comboCampo(self, idx_master: int):
        modelo = self.tableViewImagens.model()
        if not modelo:
            return
        for row in range(modelo.rowCount()):
            idx = modelo.index(row, 1)
            widget = self.tableViewImagens.indexWidget(idx)
            if not widget:
                continue
            comboCampo = widget.findChild(QComboBox, "comboBoxCampo")
            if comboCampo and idx_master < comboCampo.count():
                comboCampo.setCurrentIndex(idx_master)

    def update_layer_connections(self):
        """
        (re)conecta sinais da camada atualmente selecionada
        e força atualização imediata de checkbox / atributos.
        """

        # 1) tenta desconectar o layer anterior, se ainda existir
        old = getattr(self, "_connected_layer", None)
        if old:
            try:
                old_id = old.id()
                if QgsProject.instance().mapLayer(old_id):
                    try:
                        old.selectionChanged.disconnect(self.update_checkBoxSeleciona)
                    except (TypeError, RuntimeError):
                        pass  # nosec B110
                    try:
                        old.selectionChanged.disconnect(self._on_layer_selection_changed)
                    except (TypeError, RuntimeError):
                        pass  # nosec B110
            except RuntimeError:
                pass  # nosec B110

        # 2) pega o novo layer (pode vir como None)
        layer_id = self.comboBoxCamada.currentData()
        layer = QgsProject.instance().mapLayer(layer_id) if layer_id else None
        self._connected_layer = layer  # guarda a referência só se for válida

        # 3) conecta o novo layer
        if layer:
            layer.selectionChanged.connect(self.update_checkBoxSeleciona)
            layer.selectionChanged.connect(self._on_layer_selection_changed)

            # atualiza estados imediatamente
            self.update_checkBoxSeleciona()
            self._sincronizar_comboAtributo()
        else:
            # sem layer → só garante que o checkbox seja recalculado
            self.update_checkBoxSeleciona()

    def _row_from_index_widget(self, widget: QWidget) -> int:
        model = self.tableViewImagens.model()
        if not model or not widget:
            return -1
        for r in range(model.rowCount()):
            w = self.tableViewImagens.indexWidget(model.index(r, 1))
            if w is widget:
                return r
        return -1

    def _on_layer_selection_changed(self, *_):
        # handler dedicado em vez de lambda — mais fácil de (des)conectar
        self._sincronizar_comboAtributo()

    def _sincronizar_itens_comboCampo(self):
        modelo = self.tableViewImagens.model()
        if not modelo:
            return

        # quantidade de feições
        campo_atual = self.comboBoxCampos.currentText()
        total_vals = len(self._valores_campo(campo_atual))

        for row in range(modelo.rowCount()):
            idx = modelo.index(row, 1)
            widget = self.tableViewImagens.indexWidget(idx)
            if not widget:
                continue
            comboCampo = widget.findChild(QComboBox, "comboBoxCampo")
            if comboCampo is None:
                continue

            comboCampo.blockSignals(True)
            comboCampo.clear()
            if row < total_vals:
                # só replica os campos-mestre para linhas que têm feição
                self._copiar_itens_combo(self.comboBoxCampos, comboCampo)
                comboCampo.setCurrentIndex(self.comboBoxCampos.currentIndex())
            # else: comboCampo fica vazio
            comboCampo.blockSignals(False)

    def _marcar_duplicados_comboAtributo(self):
        modelo = self.tableViewImagens.model()
        if not modelo:
            return

        # conta quantas vezes cada feature ID aparece
        counts = {}
        combos = []
        for row in range(modelo.rowCount()):
            widget = self.tableViewImagens.indexWidget(modelo.index(row,1))
            if not widget:
                continue
            combo = widget.findChild(QComboBox, "comboBoxAtributo")
            if not combo:
                continue
            fid = combo.currentData()
            combos.append((combo, fid))
            if fid is not None:
                counts[fid] = counts.get(fid, 0) + 1

        # aplica estilo
        for combo, fid in combos:
            if fid is not None and counts.get(fid,0) > 1:
                combo.setStyleSheet("background-color: #ffcccc;")
            else:
                combo.setStyleSheet("")

    def _sincronizar_comboAtributo(self):
        campo_atual = self.comboBoxCampos.currentText()
        pairs = self._valores_campo_com_ids(campo_atual)
        total = len(pairs)

        modelo = self.tableViewImagens.model()
        if not modelo:
            return

        for row in range(modelo.rowCount()):
            widget = self.tableViewImagens.indexWidget(modelo.index(row, 1))
            if not widget:
                continue
            comboAttr = widget.findChild(QComboBox, "comboBoxAtributo")
            if comboAttr is None:
                continue

            comboAttr.blockSignals(True)
            comboAttr.clear()
            # adiciona cada (texto, userData=ID)
            for fid, txt in pairs:
                comboAttr.addItem(txt, fid)
            # seleciona só se existir feição correspondente
            comboAttr.setCurrentIndex(row if row < total else -1)
            comboAttr.blockSignals(False)

        self._marcar_duplicados_comboAtributo()

    def _on_comboCampo_changed(self):
        """
        Quando o usuário muda o campo em um comboCampo,
        atualiza o comboAtributo da *mesma* linha.
        """
        comboCampo = self.sender()
        if not comboCampo:
            return

        widget = comboCampo.parent()
        if not widget:
            return

        comboAttr = widget.findChild(QComboBox, "comboBoxAtributo")
        if not comboAttr:
            return

        row = self._row_from_index_widget(widget)
        if row < 0:
            return

        campo = comboCampo.currentText()
        pairs = self._valores_campo_com_ids(campo)
        total = len(pairs)

        comboAttr.blockSignals(True)
        comboAttr.clear()
        for fid, txt in pairs:
            comboAttr.addItem(txt, fid)
        comboAttr.setCurrentIndex(row if row < total else -1)
        comboAttr.blockSignals(False)

        self._marcar_duplicados_comboAtributo()
        self._update_add_button_state()

    def remover_imagem(self, caminho_imagem: str):
        """Remove a linha cujo UserRole da coluna-0 corresponde a caminho_imagem."""
        modelo = self.tableViewImagens.model()
        if not modelo:
            return

        for row in range(modelo.rowCount()):
            if modelo.index(row, 0).data(Qt.ItemDataRole.UserRole) == caminho_imagem:
                modelo.removeRow(row)
                break

        # limpa dicionários auxiliares
        self.icones_imagens.pop(caminho_imagem, None)
        self.info_imagens.pop(caminho_imagem, None)

        if modelo.rowCount() == 0:
            # 1. desativa apenas o combo (impede troca de ícone)
            self.comboBoxLinks.setEnabled(False)

            # 2. mantém o graphicsView ativo, mas tira interatividade
            self.graphicsViewIcones.setInteractive(False)
            # (não faça setEnabled(False) aqui!)

            # 3. força o índice 0 do combo e redesenha o ícone padrão
            self.comboBoxLinks.blockSignals(True)
            self.comboBoxLinks.setCurrentIndex(0)
            self.comboBoxLinks.blockSignals(False)
            self.exibir_icone()

            # 4. limpa campos de detalhes
            for le in (self.lineEditLatitude, self.lineEditLongitude,
                       self.lineEditResolucao, self.lineEditData, self.lineEditHorario):
                le.clear()

        # atualiza estados visuais
        self.atualizar_estado_itens()
        self._marcar_duplicados_comboAtributo()

    def _on_imagem_selection_changed(self, selected, deselected):
        """
        Ao selecionar uma linha:
          - lê o fid do comboAtributo
          - mostra coords nos lineEdits com casas decimais condicionais
          - extrai resolução (pixels) da imagem e mostra em lineEditResolucao
          - extrai data e hora de modificação do arquivo e mostra em lineEditData e lineEditHorario
        """
        # 1) Sem seleção → limpa tudo
        if not selected.indexes():
            for edit in (self.lineEditLatitude,
                         self.lineEditLongitude,
                         self.lineEditResolucao,
                         self.lineEditData,
                         self.lineEditHorario):
                edit.clear()
            return

        row = selected.indexes()[0].row()

        # 2) Identifica o path da imagem (coluna 0, UserRole)
        idx0 = self.tableViewImagens.model().index(row, 0)
        path = idx0.data(Qt.ItemDataRole.UserRole)
        if not path or not os.path.isfile(path):
            self.mostrar_mensagem(self.tr("Arquivo de imagem inválido"), "Erro")
            return

        # 3) Coordenas da feição (conforme antes)...
        idx1 = self.tableViewImagens.model().index(row, 1)
        widget = self.tableViewImagens.indexWidget(idx1)
        comboAttr = widget.findChild(QComboBox, "comboBoxAtributo")
        fid = comboAttr.currentData() if comboAttr else None

        # limpa coords se não há fid
        if fid is None:
            self.lineEditLatitude.clear()
            self.lineEditLongitude.clear()
        else:
            layer_id = self.comboBoxCamada.currentData()
            layer = QgsProject.instance().mapLayer(layer_id)
            crs = layer.crs() if layer else None

            feat = layer.getFeature(fid) if layer else None
            if feat:
                geom = feat.geometry()
                pt = (geom.asPoint() if QgsWkbTypes.geometryType(    layer.wkbType()) == Qgis.GeometryType.Point
                      else geom.centroid().asPoint())
                # formatação por CRS
                fmt = "{:.6f}" if crs and crs.isGeographic() else "{:.3f}"
                self.lineEditLatitude.setText(fmt.format(pt.y()))
                self.lineEditLongitude.setText(fmt.format(pt.x()))
            else:
                self.lineEditLatitude.clear()
                self.lineEditLongitude.clear()

        # 4) Resolução da imagem
        try:
            img = QImage(path)
            if img.isNull():
                raise ValueError(self.tr("Não pôde ler imagem"))
            res = f"{img.width()}×{img.height()}"
            self.lineEditResolucao.setText(res)
        except Exception:
            self.lineEditResolucao.clear()
            self.mostrar_mensagem(self.tr("Erro ao ler resolução da imagem"), "Erro", duracao=2)

        # 5) Data e hora do arquivo (modificação)
        try:
            ts = os.path.getmtime(path)
            dt = datetime.datetime.fromtimestamp(ts)
            self.lineEditData.setText(dt.strftime("%d/%m/%Y"))
            self.lineEditHorario.setText(dt.strftime("%H:%M:%S"))
        except Exception:
            self.lineEditData.clear()
            self.lineEditHorario.clear()
            self.mostrar_mensagem(self.tr("Erro ao ler data/hora do arquivo"), "Erro", duracao=2)

        url_salvo = ImagensManager.icones_imagens.get(path)
        self.comboBoxLinks.blockSignals(True)
        if url_salvo:
            self.comboBoxLinks.setCurrentIndex(
                self.comboBoxLinks.findData(url_salvo))
        else:
            # cai no ícone padrão
            self.comboBoxLinks.setCurrentIndex(0)
        self.comboBoxLinks.blockSignals(False)

        self.exibir_icone()        # força a atualização do graphicsView

        # — grava tudo em info_imagens[path] —
        record = ImagensManager.info_imagens.get(path, {})
        record.update({
            'feature_id': fid,
            'latitude'  : self.lineEditLatitude.text() or None,
            'longitude' : self.lineEditLongitude.text() or None,
            'resolution': self.lineEditResolucao.text() or None,
            'date'      : self.lineEditData.text() or None,
            'time'      : self.lineEditHorario.text() or None})
        ImagensManager.info_imagens[path] = record

    def _fmt_val(self, v) -> str:
        """Formata valor para exibição (remove .0 quando for float inteiro)."""
        if v is None:
            return ""

        # float "inteiro" (2.0, 3.0...) -> "2", "3"
        if isinstance(v, float):
            if v.is_integer():
                return str(int(v))
            # opcional: remove zeros finais tipo 2.5000 -> 2.5
            s = f"{v}".rstrip("0").rstrip(".")
            return s

        # int normal
        if isinstance(v, int):
            return str(v)

        return str(v)

    def exportar_para_kmz(self):
        """Gera o KMZ usando os dados já armazenados em info_imagens."""
        layer_id = self.comboBoxCamada.currentData()
        layer = QgsProject.instance().mapLayer(layer_id) if layer_id else None

        default_name = f"{layer.name()}.kmz" if layer else self.tr("IMAGENS.kmz")
        fileName = self.escolher_local_para_salvar(default_name, self.tr("KMZ files (*.kmz)"))
        if not fileName:
            return

        kml_content, imagens_para_incluir = self.gerar_conteudo_kml()
        if not kml_content:
            self.mostrar_mensagem(self.tr("Não há conteúdo KML para exportar."), "Erro")
            return

        # ScreenOverlay no KML (se existir)
        if getattr(self, "screen_overlay_data", None):
            kml_content = kml_content.replace(
                "</Document>",
                self.gerar_conteudo_screenoverlay(self.screen_overlay_data) + "</Document>")

        tempo_ini = time.time()

        # progresso: 1 passo pro KML + N imagens + (overlay imagem, se existir)
        steps_tot = 1 + len(imagens_para_incluir) + (1 if getattr(self, "screen_overlay_data", None) else 0)
        pbar, pw = self.iniciar_progress_bar(steps_tot)

        try:
            # Nome do KML dentro do KMZ
            kml_inside = os.path.splitext(os.path.basename(fileName))[0] + ".kml"

            # compresslevel=1 é mais rápido; imagens vão como STORED (sem compressão)
            with zipfile.ZipFile(
                fileName, "w",
                compression=zipfile.ZIP_DEFLATED,
                compresslevel=1) as kmz:

                # 1) grava o KML direto no zip (sem arquivo temporário)
                kmz.writestr(kml_inside, kml_content)
                pbar.setValue(1)
                QCoreApplication.processEvents()

                # 2) imagens: sem compressão (muito mais rápido)
                step = 1
                for img_path in imagens_para_incluir:
                    step += 1
                    kmz.write(
                        img_path,
                        "files/" + os.path.basename(img_path),
                        compress_type=zipfile.ZIP_STORED)
                    pbar.setValue(step)
                    QCoreApplication.processEvents()

                # 3) overlay (arquivo da imagem)
                if getattr(self, "screen_overlay_data", None):
                    step += 1
                    ov_path = self.screen_overlay_data["image_path"]
                    kmz.write(
                        ov_path,
                        "files/" + os.path.basename(ov_path),
                        compress_type=zipfile.ZIP_STORED)
                    pbar.setValue(step)
                    QCoreApplication.processEvents()

            self.mostrar_mensagem(self.tr("KMZ exportado para {fileName} em {elapsed:.2f}s.").format(fileName=fileName, elapsed=time.time() - tempo_ini), "Sucesso")

            QDesktopServices.openUrl(QUrl.fromLocalFile(fileName))

        except Exception as e:
            self.mostrar_mensagem(self.tr("Falha ao criar KMZ: {error}").format(error=str(e)), "Erro")

        finally:
            iface.messageBar().popWidget(pw)

    def _valores_campo(self, campo: str) -> list[str]:
        """
        Retorna os valores (em ordem) do `campo` na camada escolhida,
        filtrando pelas feições selecionadas se checkBoxSeleciona estiver ativo.
        """
        layer_id = self.comboBoxCamada.currentData()
        layer = QgsProject.instance().mapLayer(layer_id) if layer_id else None
        if not (layer and isinstance(layer, QgsVectorLayer)):
            return []

        usar_selecao = self.findChild(QCheckBox, "checkBoxSeleciona").isChecked()
        feats = layer.selectedFeatures() if usar_selecao else layer.getFeatures()

        # Verifica se o campo existe na camada antes de acessá-lo
        if campo not in [field.name() for field in layer.fields()]:
            return []

        # Mantemos a ordem dos registros; transformamos None em string vazia
        return [self._fmt_val(f[campo]) for f in feats]

    def _valores_campo_com_ids(self, campo: str) -> list[tuple[int, str]]:
        """
        Retorna lista de (feature.id(), valor_str) em ordem,
        respeitando seleção se checkBoxSeleciona estiver marcado.
        """
        layer_id = self.comboBoxCamada.currentData()
        layer = QgsProject.instance().mapLayer(layer_id) if layer_id else None
        if not (layer and isinstance(layer, QgsVectorLayer)):
            return []

        usar_selecao = self.findChild(QCheckBox, "checkBoxSeleciona").isChecked()
        feats = layer.selectedFeatures() if usar_selecao else layer.getFeatures()

        # Verifica se o campo existe na camada antes de acessá-lo
        if campo not in [field.name() for field in layer.fields()]:
            return []

        return [(f.id(), self._fmt_val(f[campo])) for f in feats]

    def _adicionar_coordenadas(self):
        # 0) linha da imagem – como já estava …
        idxs = self.tableViewImagens.selectionModel().selectedRows(0)
        if not idxs:
            self.mostrar_mensagem(self.tr("Selecione uma imagem primeiro"), "Erro")
            return
        row = idxs[0].row()
        widget = self.tableViewImagens.indexWidget(
            self.tableViewImagens.model().index(row, 1))
        comboAttr = widget.findChild(QComboBox, "comboBoxAtributo")
        if comboAttr.currentData() is not None:
            self.mostrar_mensagem(self.tr("Esta imagem já tem feição"), "Erro")
            return

        # 1) obtém a camada atual
        layer_id = self.comboBoxCamada.currentData()
        layer = QgsProject.instance().mapLayer(layer_id)
        if not layer:
            self.mostrar_mensagem(self.tr("Camada não encontrada"), "Erro")
            return

        # extrai a URI para detectar extensões
        uri = layer.dataProvider().dataSourceUri().lower()

        # 2) se a camada NÃO for editável, e for KML/KMZ ou DXF, pede confirmação
        if not self.is_layer_editable(layer):
            if any(ext in uri for ext in ('.kml', '.kmz', '.dxf')):
                reply = QMessageBox.question(self,
                    self.tr("Camada não editável"),
                    self.tr("A camada atual é KML/KMZ ou DXF e não permite edição direta.\nDeseja criar uma nova camada idêntica e editável?"),
                    QMessageBox.StandardButton.Yes | QMessageBox.StandardButton.No)

                if reply != QMessageBox.StandardButton.Yes:
                    return
            # para outros formatos não editáveis, vai direto criar
            new_layer = self.create_editable_layer(layer)
            if not new_layer:
                self.mostrar_mensagem(self.tr("Falha ao criar camada editável"), "Erro")
                return

            # seleciona a nova camada
            self.comboBoxCamada.setCurrentIndex(
                self.comboBoxCamada.findData(new_layer.id()))
            self.mostrar_mensagem(self.tr("Nova camada editável criada automaticamente."), "Sucesso", duracao=3)

            # atualiza conexões e passa a usar a nova camada
            self.update_layer_connections()
            layer = new_layer

        # 3) abre o diálogo de coordenadas
        dlg = AddFeatureDialog(layer, parent=self)
        res = dlg.exec()
        if res != QDialog.DialogCode.Accepted:
            return

        # 4) monta e adiciona a feição
        feat = QgsFeature(layer.fields())
        feat.setGeometry(dlg.geometry())
        for fld_name, value in dlg.attributes().items():
            feat[fld_name] = value

        added_ok = False
        started_here = False

        if not layer.isEditable():
            if not layer.startEditing():
                self.mostrar_mensagem(self.tr("Não foi possível iniciar a edição da camada."), "Erro")
                return
            started_here = True

        added_ok = layer.addFeature(feat)

        if not added_ok:
            if started_here:
                layer.rollBack()
            self.mostrar_mensagem(self.tr("Não foi possível adicionar a feição na camada."), "Erro")
            return

        if started_here:
            if not layer.commitChanges():
                layer.rollBack()
                self.mostrar_mensagem(self.tr("A feição foi criada, mas não foi possível salvar a edição."), "Erro")
                return

        # Grava info_imagens
        geom = feat.geometry()
        pt = (geom.asPoint()
            if QgsWkbTypes.geometryType(geom.wkbType()) == Qgis.GeometryType.Point
            else geom.centroid().asPoint())

        path = self.tableViewImagens.model().index(row, 0).data(Qt.ItemDataRole.UserRole)
        rec  = ImagensManager.info_imagens.get(path, {})
        rec.update({
            'feature_id': feat.id(),
            'latitude'  : pt.y(),
            'longitude' : pt.x()})
        ImagensManager.info_imagens[path] = rec

        # 5) atualiza interface
        self._sincronizar_comboAtributo()
        self._sincronizar_itens_comboCampo()
        comboAttr.setCurrentIndex(comboAttr.findData(feat.id()))
        self.mostrar_mensagem(self.tr("Feição criada"), "Sucesso", duracao=2)

    def is_layer_editable(self, layer) -> bool:
        """
        Retorna True se a camada suporta receber novas feições (AddFeatures).
        Isso é diferente de layer.isEditable() (que só diz se está em modo edição agora).
        """
        if not layer or not isinstance(layer, QgsVectorLayer) or not layer.isValid():
            return False

        # Se o QGIS marcar a layer como somente leitura (quando disponível)
        try:
            if hasattr(layer, "isReadOnly") and layer.isReadOnly():
                return False
        except Exception:
            pass  # nosec B110

        # Se existir supportsEditing(), é um bom sinalizador (nem sempre suficiente, mas ajuda)
        try:
            if hasattr(layer, "supportsEditing") and not layer.supportsEditing():
                return False
        except Exception:
            pass  # nosec B110

        dp = layer.dataProvider()
        if not dp:
            return False

        # Capabilities do provider (fonte mais confiável)
        try:
            caps = dp.capabilities()
        except Exception:
            return False

        # Para seu caso (criar ponto), o essencial é permitir adicionar feições
        if not (caps & QgsVectorDataProvider.Capability.AddFeatures):
            return False

        # Salvaguarda: KML/KMZ/DXF geralmente são read-only via OGR,
        # e às vezes o provider pode "enganar" nas capabilities.
        try:
            uri = (dp.dataSourceUri() or "").lower()
            if any(ext in uri for ext in (".kml", ".kmz", ".dxf")):
                return False
        except Exception:
            pass  # nosec B110

        return True

    def create_editable_layer(self, original_layer):
        """Cria nova camada editável com mesma estrutura e dados, removendo campos específicos."""
        crs = original_layer.crs()
        wkb_type = original_layer.wkbType()
        geom_type = QgsWkbTypes.displayString(wkb_type)

        # Cria nova camada em memória
        uri = f"{geom_type}?crs={crs.authid()}"
        new_layer = QgsVectorLayer(uri, f"{original_layer.name()}_editável", "memory")
        
        if not new_layer.isValid():
            self.mostrar_mensagem(self.tr("Falha ao criar nova camada"), "Erro")
            return None

        # Lista de campos a serem removidos
        campos_para_remover = {
            "Name", "description", "timestamp", "begin", "end",
            "altitudeMode", "tessellate", "extrude", "drawOrder", "visibility", "icon"}

        # Filtra os campos que não estão na lista de remoção
        campos_filtrados = [
            field for field in original_layer.fields()
            if field.name() not in campos_para_remover]

        # Adiciona os campos filtrados à nova camada
        provider = new_layer.dataProvider()
        provider.addAttributes(campos_filtrados)
        new_layer.updateFields()

        # Copia as feições, mantendo apenas os atributos dos campos filtrados
        features = []
        for feat in original_layer.getFeatures():
            new_feat = QgsFeature(new_layer.fields())
            new_feat.setGeometry(feat.geometry())
            
            # Filtra os atributos para incluir apenas os campos que permanecem
            atributos_filtrados = {
                field.name(): feat[field.name()]
                for field in campos_filtrados
                if field.name() in feat.fields().names()}

            new_feat.setAttributes([atributos_filtrados.get(field.name(), None) for field in new_layer.fields()])
            features.append(new_feat)

        provider.addFeatures(features)

        # Adiciona a nova camada ao projeto
        QgsProject.instance().addMapLayer(new_layer)
        return new_layer

    def _update_add_button_state(self, selected=None, deselected=None):
        """
        Habilita pushButtonAddCoordenadas só se houver exatamente
        UMA linha selecionada cujo comboAtributo.currentData() seja None.
        """
        sel = self.tableViewImagens.selectionModel().selectedRows(0)
        if len(sel) != 1:
            self.pushButtonAddCoordenadas.setEnabled(False)
            return

        row = sel[0].row()
        idx_attr = self.tableViewImagens.model().index(row, 1)
        widget = self.tableViewImagens.indexWidget(idx_attr)
        comboAttr = widget.findChild(QComboBox, "comboBoxAtributo") if widget else None

        # só habilita se aquele combo não tiver data (ou seja, "sem feição")
        ok = comboAttr is not None and comboAttr.currentData() is None
        self.pushButtonAddCoordenadas.setEnabled(ok)

    def abrir_screen_overlay(self):
        """
        Abre um diálogo para adicionar ou editar um ScreenOverlay.
        
        Funções:
        - Cria uma instância do diálogo ScreenOverlay com a janela atual como pai.
        - Executa o diálogo de maneira modal.
        """
        
        dialog = ScreenOverlay(self)  # Cria uma instância do diálogo ScreenOverlay
        dialog.exec()  # Executa o diálogo de maneira modal

    def escolher_local_para_salvar(self, nome_padrao, tipo_arquivo):
        """
        Exibe uma caixa de diálogo para salvar arquivos, sugerindo um nome e local com base no último diretório utilizado.

        Parâmetros:
        nome_padrao: str - O nome padrão sugerido para o arquivo a ser salvo.
        tipo_arquivo: str - O tipo de arquivo (extensão) a ser salvo, ex: "KMZ files (*.kmz)".

        Retorna:
        str - O caminho completo do arquivo escolhido ou None se cancelado.

        Funções:
        - Acessa as configurações do QGIS para recuperar o último diretório utilizado.
        - Configura as opções da caixa de diálogo para salvar arquivos.
        - Gera um nome de arquivo único com um sufixo numérico se o arquivo já existir.
        - Exibe a caixa de diálogo para salvar arquivos com o nome proposto.
        - Atualiza o último diretório usado nas configurações do QGIS se um nome de arquivo foi escolhido.
        - Assegura que o arquivo tenha a extensão correta.
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
            self,
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

    def gerar_conteudo_screenoverlay(self, screen_overlay_data):
        """
        Gera o conteúdo KML para o ScreenOverlay.

        Parâmetros:
        screen_overlay_data: dict - O dicionário contendo os dados do ScreenOverlay.

        Retorna:
        str - O conteúdo KML gerado para o ScreenOverlay.

        Funções:
        - Gera o conteúdo KML para o ScreenOverlay com base nos dados fornecidos.
        - Adiciona o elemento ScreenOverlay com suas propriedades ao KML.
        - Retorna o conteúdo KML como uma string.
        """

        # Cria a lista de strings que compõem o conteúdo do ScreenOverlay em KML
        screen_overlay_content = [
            '<ScreenOverlay>',  # Abre o elemento ScreenOverlay
            '<name>logo</name>',  # Define o nome do ScreenOverlay
            '<Icon>',  # Abre o elemento Icon
            f'<href>files/{os.path.basename(screen_overlay_data["image_path"])}</href>',  # Define o caminho do ícone
            '</Icon>',  # Fecha o elemento Icon
            f'<overlayXY x="{screen_overlay_data["overlayXY"][0]}" y="{screen_overlay_data["overlayXY"][1]}" xunits="fraction" yunits="fraction"/>',  # Define as coordenadas overlayXY
            f'<screenXY x="{screen_overlay_data["screenXY"][0]}" y="{screen_overlay_data["screenXY"][1]}" xunits="pixels" yunits="pixels"/>',  # Define as coordenadas screenXY
            f'<rotationXY x="{screen_overlay_data["rotationXY"][0]}" y="{screen_overlay_data["rotationXY"][1]}" xunits="fraction" yunits="fraction"/>',  # Define as coordenadas rotationXY
            f'<size x="{screen_overlay_data["sizeXY"][0]}" y="{screen_overlay_data["sizeXY"][1]}" xunits="pixels" yunits="pixels"/>',  # Define o tamanho do ScreenOverlay
            '</ScreenOverlay>']  # Fecha o elemento ScreenOverlay
        
        return '\n'.join(screen_overlay_content)  # Junta todas as partes do conteúdo e retorna como uma única string

    def decimal_to_dms(self, decimal, coord_type):
        """
        Converte coordenadas decimais para DMS (Graus, Minutos, Segundos).

        Parâmetros:
        decimal: float - O valor da coordenada em formato decimal.
        coord_type: str - O tipo de coordenada ('lat' para latitude ou 'lon' para longitude).

        Retorna:
        str - A coordenada formatada em DMS com a direção apropriada.

        Funções:
        - Converte o valor decimal da coordenada em graus, minutos e segundos.
        - Determina a direção da coordenada com base no tipo e no sinal do valor decimal.
        - Retorna a coordenada formatada em DMS com a direção.
        """
        is_positive = decimal >= 0  # Verifica se o valor decimal é positivo
        decimal = abs(decimal)  # Obtém o valor absoluto da coordenada
        degrees = int(decimal)  # Obtém a parte inteira dos graus
        minutes = int((decimal - degrees) * 60)  # Calcula os minutos a partir da parte decimal dos graus
        seconds = (decimal - degrees - minutes / 60) * 3600  # Calcula os segundos a partir da parte decimal dos minutos
        direction = ''  # Inicializa a direção como uma string vazia

        if coord_type == 'lat':  # Define a direção para latitude
            direction = 'N' if is_positive else 'S'
        elif coord_type == 'lon':  # Define a direção para longitude
            direction = 'E' if is_positive else 'W'
        
        return f"{degrees}°{minutes}'{seconds:.2f}\"{direction}"  # Retorna a coordenada formatada em DMS com a direção

    def _get_current_crs(self):
        """Retorna o CRS da camada selecionada no comboBoxCamada."""
        layer_id = self.comboBoxCamada.currentData()
        layer = QgsProject.instance().mapLayer(layer_id) if layer_id else None
        return layer.crs() if layer else None

    def _to_geographic(self, lon: float, lat: float) -> tuple[float, float]:
        """
        Se o CRS atual não for geográfico, reprojeta (lon,lat) para EPSG:4326.
        Caso contrário, retorna os valores como estão.
        """
        src_crs = self._get_current_crs()
        if src_crs and not src_crs.isGeographic():
            tr = QgsCoordinateTransform(
                src_crs,
                QgsCoordinateReferenceSystem("EPSG:4326"),
                QgsProject.instance())

            pt = tr.transform(QgsPointXY(lon, lat))
            return pt.x(), pt.y()
        return lon, lat

    def gerar_conteudo_kml(self):
        modelo = self.tableViewImagens.model()
        if not modelo or modelo.rowCount() == 0:
            self.mostrar_mensagem(self.tr("Nenhuma imagem carregada."), "Aviso")
            return None, []

        pasta_nome  = os.path.basename(ImagensManager.ultima_pasta or "")
        largura_img = ImagensManager.exibir_texto or "1400"
        kml = [
            '<?xml version="1.0" encoding="UTF-8"?>',
            '<kml xmlns="http://www.opengis.net/kml/2.2">',
            f'<Document><name>{pasta_nome}.kmz</name><open>1</open>']
        imgs_kmz = []

        layer = QgsProject.instance().mapLayer(self.comboBoxCamada.currentData())
        if not layer:
            self.mostrar_mensagem(self.tr("Camada não encontrada."), "Erro")
            return None, []
        crs_cam = layer.crs()
        if crs_cam.isGeographic():
            transformer = None
        else:
            dest_crs = QgsCoordinateReferenceSystem("EPSG:4326")
            transformer = QgsCoordinateTransform(crs_cam, dest_crs, QgsProject.instance())

        for row in range(modelo.rowCount()):
            idx0   = modelo.index(row, 0)
            caminho = idx0.data(Qt.ItemDataRole.UserRole)
            idx1    = modelo.index(row, 1)
            widget  = self.tableViewImagens.indexWidget(idx1)
            combo_attr = widget.findChild(QComboBox, "comboBoxAtributo") if widget else None
            fid     = combo_attr.currentData() if combo_attr else None
            if fid is None:
                continue

            feat = layer.getFeature(fid)
            geom = feat.geometry()
            pt   = (geom.asPoint() if QgsWkbTypes.geometryType(    layer.wkbType()) == Qgis.GeometryType.Point
                    else geom.centroid().asPoint())
            x, y = pt.x(), pt.y()
            if transformer:
                pt_geo = transformer.transform(x, y)
                lon, lat = pt_geo.x(), pt_geo.y()
            else:
                lon, lat = x, y

            lat_dms = self.decimal_to_dms(lat, "lat")
            lon_dms = self.decimal_to_dms(lon, "lon")
            nome_pm  = combo_attr.currentText() or os.path.splitext(os.path.basename(caminho))[0]
            icon_url = ImagensManager.icones_imagens.get(caminho, self.comboBoxLinks.itemData(0))
            autor    = ImagensManager.autor_texto or ""

            imagem_label = self.tr("IMAGEM")
            coordenadas_label = self.tr("Coordenadas da Imagem")
            lat_label = self.tr("Lat")
            lon_label = self.tr("Lon")

            autor_html = (
                f'<div style="text-align:right; font-size:12px; color:blue;">'
                f'<b>{imagem_label}: {autor} </b></div>'
                if autor else "")

            # cabeçalhos e valores com cor pastel aleatória por coluna
            header_cells, value_cells = [], []
            for field in layer.fields():

                # Gera uma cor pastel apenas para apresentação visual.
                # Não é usada para segurança, senha, token ou criptografia.
                r = random.randint(200, 255)  # nosec B311
                g = random.randint(200, 255)  # nosec B311
                b = random.randint(200, 255)  # nosec B311
                cor = f"#{r:02x}{g:02x}{b:02x}"

                header_cells.append(
                    f'<th style="background:{cor}; padding:3px; '
                    f'border:1px solid #d0d0d0;">{field.name()}</th>')
                val = feat[field.name()]
                value_cells.append(
                    f'<td style="background:{cor}; padding:3px; '
                    f'border:1px solid #d0d0d0;">{val if val is not None else ""}</td>')

            header_html = "".join(header_cells)
            value_html  = "".join(value_cells)

            tabela_html = (
                '<table style="border-collapse:collapse; font-size:90%; '
                'border:2px solid #c0c0c0;" cellpadding="0" cellspacing="0">'
                f'<tr>{header_html}</tr>'
                f'<tr>{value_html}</tr>'
                '</table>')

            style_id = f"st_{row}"
            kml.append(
                f'<Style id="{style_id}">'
                f'  <BalloonStyle><text><![CDATA['
                f'{autor_html}'
                f'<b>{coordenadas_label}: </b> <b>{lat_label}:</b> {lat_dms} <b>{lon_label}:</b> {lon_dms}<br>'
                f'{tabela_html}<br>'
                f'<img width="{largura_img}" src="files/{os.path.basename(caminho)}"/>'
                f']]></text></BalloonStyle>'
                f'  <IconStyle><Icon><href>{icon_url}</href></Icon></IconStyle>'
                f'</Style>')

            kml.append(
                f'<Placemark>'
                f'  <name>{nome_pm}</name>'
                f'  <styleUrl>#{style_id}</styleUrl>'
                f'  <Point><coordinates>{lon},{lat}</coordinates></Point>'
                f'</Placemark>')

            imgs_kmz.append(caminho)

        kml.append('</Document></kml>')
        return "\n".join(kml), imgs_kmz

class AddFeatureDialog(QDialog):
    def __init__(self, layer: QgsVectorLayer, parent=None):
        super().__init__(parent)
        self.setWindowTitle(self.tr("Nova feição"))
        self._layer = layer
        self._inputs = {}

        # Layout principal
        main_layout = QVBoxLayout(self)

        # QFrame Box/Raised
        frame = QFrame(self)
        frame.setFrameShape(QFrame.Shape.Box)
        frame.setFrameShadow(QFrame.Shadow.Raised)
        main_layout.addWidget(frame)

        form = QFormLayout(frame)

        # Decide rótulos e intervalos pelo CRS
        crs = layer.crs()
        is_geo = crs.isGeographic()
        lblY, lblX = ("Lat (°)", "Lon (°)") if is_geo else ("Y", "X")

        # Criar QLineEdits
        self._inpX = QLineEdit();  self._inpY = QLineEdit()
        form.addRow(lblY, self._inpY)
        form.addRow(lblX, self._inpX)

        # Demais atributos, pulando possíveis campos Y/X
        skip = {lblX, lblY}
        skip_lower = {s.lower().split()[0] for s in skip}
        fields = layer.fields()
        for i, fld in enumerate(fields):
            name = fld.name()
            if name in skip or name.lower() in skip_lower:
                continue

            origin = fields.fieldOrigin(i)
            if origin in (QgsFields.FieldOrigin.OriginJoin, QgsFields.FieldOrigin.OriginExpression):
                continue

            if hasattr(fld, "isReadOnly") and fld.isReadOnly():
                continue

            le = QLineEdit()
            if fld.type() in (QMetaType.Type.Double, QMetaType.Type.Int):
                le.setValidator(QDoubleValidator())
            form.addRow(name, le)
            self._inputs[name] = le

        # Botões
        self._btns = QDialogButtonBox(QDialogButtonBox.StandardButton.Ok | QDialogButtonBox.StandardButton.Cancel, parent=self)
        self._btns.accepted.connect(self._accept)
        self._btns.rejected.connect(self.reject)
        main_layout.addWidget(self._btns)

        # OK inicialmente desabilitado
        self._ok_btn = self._btns.button(QDialogButtonBox.StandardButton.Ok)
        self._ok_btn.setEnabled(False)

        # Conecta validação em tempo real
        self._inpY.textChanged.connect(self._on_coord_changed)
        self._inpX.textChanged.connect(self._on_coord_changed)

    def validate(self, line_edit: QLineEdit, low=None, high=None) -> bool:
        texto = line_edit.text().strip()

        if not texto:
            line_edit.setStyleSheet("border: 1px solid red;")
            return False

        try:
            manager = self.parent()

            valor = manager._parse_coord_float(texto)

        except (TypeError, ValueError, AttributeError):
            line_edit.setStyleSheet("border: 1px solid red;")
            return False

        if not math.isfinite(valor):
            line_edit.setStyleSheet("border: 1px solid red;")
            return False

        if low is not None and valor < low:
            line_edit.setStyleSheet("border: 1px solid red;")
            return False

        if high is not None and valor > high:
            line_edit.setStyleSheet("border: 1px solid red;")
            return False

        line_edit.setStyleSheet("")
        return True

    def geometry(self):
        x = ImagensManager._parse_coord_float(self.parent(), self._inpX.text())
        y = ImagensManager._parse_coord_float(self.parent(), self._inpY.text())

        return QgsGeometry.fromPointXY(QgsPointXY(x, y))

    def _on_coord_changed(self, _text):
        """
        Valida as coordenadas digitadas e habilita o botão OK
        somente quando X e Y estiverem dentro dos limites permitidos.
        """
        def validar_coordenada(line_edit: QLineEdit, limite_minimo: float, limite_maximo: float) -> bool:
            try:
                valor = ImagensManager._parse_coord_float(
                    self.parent(),
                    line_edit.text())

            except (TypeError, ValueError, AttributeError):
                line_edit.setStyleSheet(
                    "border: 1px solid red;")
                return False

            if not limite_minimo <= valor <= limite_maximo:
                line_edit.setStyleSheet(
                    "border: 1px solid red;")
                return False

            line_edit.setStyleSheet("")
            return True

        crs = self._layer.crs()

        if crs.isGeographic():
            x_valido = validar_coordenada(self._inpX, -180.0, 180.0)

            y_valido = validar_coordenada(self._inpY, -90.0, 90.0)

        else:
            x_valido = validar_coordenada(self._inpX, 100_000.0, 900_000.0)

            y_valido = validar_coordenada(self._inpY, 0.0,10_000_000.0)

        self._ok_btn.setEnabled(x_valido and y_valido)

    def attributes(self):
        return {fld: inp.text() for fld, inp in self._inputs.items()}

    def _accept(self):
        # reforça validação final
        if not self._ok_btn.isEnabled():
            QMessageBox.warning(self, self.tr("Erro"), self.tr("Coordenadas inválidas"))
            return
        self.accept()

class DeleteButtonDelegate(QStyledItemDelegate):
    """
    Delegate para adicionar um botão de deletar estilizado em cada item de uma view.
    
    Funções:
    - Inicializa o delegate com um parent opcional.
    - Renderiza um ícone de deletar no canto superior direito do item.
    - Lida com eventos de clique no ícone de deletar para remover a imagem correspondente.
    """
    
    def __init__(self, parent=None):
        """
        Inicializa o DeleteButtonDelegate.
        
        Parâmetros:
        parent: QWidget (opcional) - O widget pai, se houver.
        """
        super(DeleteButtonDelegate, self).__init__(parent)  # Chama o construtor da classe base QStyledItemDelegate
        self.parent = parent  # Armazena o widget pai

    def paint(self, painter, option, index):
        """
        Renderiza o ícone de deletar no canto superior direito do item.
        
        Parâmetros:
        painter: QPainter - O objeto QPainter usado para desenhar o item.
        option: QStyleOptionViewItem - As opções de estilo para o item.
        index: QModelIndex - O índice do item a ser desenhado.
        """
        super(DeleteButtonDelegate, self).paint(painter, option, index)  # Chama o método paint da classe base

        # Renderizar o ícone de deletar no canto superior direito
        if index.isValid():  # Verifica se o índice é válido
            rect = option.rect  # Obtém o retângulo do item
            icon_rect = QRect(rect.right() - 15, rect.top() + 2, 12, 12)  # Ajusta o tamanho e posição do ícone

            # Desenhar ícone estilizado com quadrado de bordas arredondadas
            painter.save()  # Salva o estado atual do painter
            painter.setRenderHint(QPainter.RenderHint.Antialiasing)  # Habilita antialiasing
            painter.setPen(QPen(QColor(0, 0, 255), 2))  # Cor da borda do quadrado
            painter.setBrush(QBrush(QColor(255, 0, 0, 200)))  # Fundo vermelho claro
            radius = 2  # Raio das bordas arredondadas
            painter.drawRoundedRect(icon_rect, radius, radius)  # Desenha o quadrado com bordas arredondadas

            # Desenha o "x" dentro do quadrado
            painter.setPen(QPen(QColor(255, 255, 255), 2))  # Cor e espessura do "x"
            # Desenha o "x" simétrico dentro do quadrado
            painter.drawLine(icon_rect.topLeft() + QPoint(2, 2), icon_rect.bottomRight() - QPoint(2, 2))
            painter.drawLine(icon_rect.topRight() + QPoint(-2, 2), icon_rect.bottomLeft() + QPoint(2, -2))
            painter.restore()  # Restaura o estado do painter

    def editorEvent(self, event, model, option, index):
        """
        Lida com eventos de clique no ícone de deletar para remover a imagem correspondente.
        
        Parâmetros:
        event: QEvent - O evento de entrada.
        model: QAbstractItemModel - O modelo de dados.
        option: QStyleOptionViewItem - As opções de estilo para o item.
        index: QModelIndex - O índice do item a ser manipulado.
        
        Retorna:
        bool - True se o evento foi tratado, caso contrário chama o método da classe base.
        """
        if event.type() == QEvent.Type.MouseButtonRelease:  # Verifica se o evento é de clique do mouse
            rect = option.rect  # Obtém o retângulo do item
            icon_rect = QRect(rect.right() - 15, rect.top() + 2, 12, 12)  # Ajusta o tamanho e posição do ícone
            if icon_rect.contains(event.pos()):  # Verifica se o clique ocorreu dentro do ícone
                # Aciona a remoção da imagem
                caminho_imagem = index.data(Qt.ItemDataRole.UserRole)  # Obtém o caminho da imagem do índice
                self.parent.remover_imagem(caminho_imagem)  # Chama a função de remover imagem no widget pai
                return True  # Indica que o evento foi tratado
        return super(DeleteButtonDelegate, self).editorEvent(event, model, option, index)  # Chama o método da classe base para outros eventos

class ScreenOverlay(QDialog):
    def __init__(self, parent=None):
        """
         Inicializa a classe ScreenOverlay, configurando a interface do usuário e conectando os sinais e slots.

        Parâmetros:
        - parent: O widget pai opcional para este diálogo.
        
        Funções realizadas:
        - Inicializa o diálogo com a interface do usuário.
        - Define o título da janela.
        - Conecta os sinais dos widgets aos métodos correspondentes.
        - Desativa os controles inicialmente.
        - Define variáveis de instância para armazenamento de estado e configurações.
        - Carrega dados de ScreenOverlay se estiverem disponíveis no widget pai.
        - Ativa ou desativa os controles com base na presença dos dados de ScreenOverlay no widget pai.
        """
        super(ScreenOverlay, self).__init__(parent)  # Chama o construtor da classe base QDialog
        self.setupUi(self)  # Configura a interface do usuário

        self.setWindowTitle(self.tr("Adicionar ScreenOverlay ao KMZ"))  # Define o título da janela

        self.buttonBox.button(QDialogButtonBox.StandardButton.Ok).setEnabled(False) # Inicia inativo e ativa ao detectar imagem no gráfico

        #Captura a configuração definida no QT Designer, para o caso de redifinição posterior
        self.parent().pushButton_Screen.setStyleSheet(self.parent().pushButton_Screen_default_style)

        # Conecta os sinais dos widgets aos métodos correspondentes
        self.pushButtonAdd.clicked.connect(self.adicionar_imagem)  # Conecta o clique do botão ao método adicionar_imagem
        self.lineEditPX.textChanged.connect(self.redimensionar_imagem)  # Conecta a mudança de texto ao método redimensionar_imagem
        self.lineEditPY.textChanged.connect(self.redimensionar_imagem)  # Conecta a mudança de texto ao método redimensionar_imagem
        self.lineEditX.textChanged.connect(self.atualizar_posicao_imagem)  # Conecta a mudança de texto ao método atualizar_posicao_imagem
        self.lineEditY.textChanged.connect(self.atualizar_posicao_imagem)  # Conecta a mudança de texto ao método atualizar_posicao_imagem
        self.pushButtonReseta.clicked.connect(self.resetar_valores)  # Conecta o botão ao método de reset

        self.desativar_controles()  # Desativar controles inicialmente
        self.last_opened_folder = QDir.homePath()  # Define last_opened_folder na instância
        self.original_pixmap = None  # Para armazenar a imagem original
        self.pixmap_item = None  # Para armazenar o item pixmap na cena gráfica
        self.linha_horizontal = None  # Armazenar a linha horizontal
        self.linha_vertical = None  # Armazenar a linha vertical
        self.original_pos = (0, 0)  # Inicializar original_pos para evitar erro de atributo
        self.image_path = None  # Atributo de instância para armazenar o caminho da imagem
        self.transform_state = None  # Atributo para armazenar o estado da transformação

        # Verifica se o widget pai tem dados de screen_overlay e carrega-os se existirem
        if hasattr(self.parent(), 'screen_overlay_data') and self.parent().screen_overlay_data:
            self.carregar_dados_screen_overlay()  # Carrega os dados de screen_overlay
            self.ativar_controles()  # Ativa os controles se os dados existirem
        else:
            self.desativar_controles()  # Desativa os controles se os dados não existirem

        # OverlayXY começa sempre em 0x0
        self.lineEditX.setText("0")
        self.lineEditY.setText("0")

        # Flag: só sincroniza quando a alteração vier do usuário
        self._pixels_edited_by_user = False

        # Marca que o usuário mexeu em Pixels
        self.lineEditPX.textEdited.connect(self._mark_pixels_user_edit)
        self.lineEditPY.textEdited.connect(self._mark_pixels_user_edit)

    def showEvent(self, event):
        """
        Método showEvent que é chamado automaticamente sempre que o diálogo é exibido.

        O objetivo deste método é restaurar o estado visual do gráfico (imagem e transformações aplicadas)
        para o último estado modificado antes do diálogo ser fechado ou oculto. Ele garante que,
        ao reabrir o diálogo, a imagem seja exibida exatamente como estava na última vez que foi visualizada.

        A função realiza as seguintes operações:
        1. Chama o método showEvent da classe base para garantir que qualquer comportamento padrão do QDialog seja executado.
        2. Verifica se há uma imagem (pixmap_item) no gráfico.
        3. Se uma transformação anterior foi aplicada (transform_state), a função restaura essa transformação ao gráfico.
        4. Ajusta a visualização do gráfico dentro do QGraphicsView para garantir que a imagem caiba perfeitamente na área disponível.
        """
        super(ScreenOverlay, self).showEvent(event)  # Chama o método showEvent da classe base QDialog para manter o comportamento padrão

        if self.pixmap_item:  # Verifica se há uma imagem no gráfico
            if self.transform_state:  # Verifica se há uma transformação salva para o gráfico
                self.graphicsView.setTransform(self.transform_state)  # Aplica a transformação salva ao gráfico

            # Ajusta a visualização do gráfico para caber na área do QGraphicsView mantendo a proporção
            self.graphicsView.fitInView(self.graphicsView.scene().itemsBoundingRect(), Qt.AspectRatioMode.KeepAspectRatio)

    def setupUi(self, Dialog):
        """
        Configura a interface do usuário do diálogo, incluindo layouts, widgets e conexões de sinais.
        
        Parâmetros:
        Dialog: QDialog - O diálogo que está sendo configurado.
        
        Funções:
        - Define o nome do objeto do diálogo.
        - Redimensiona o diálogo e define o tamanho máximo.
        - Configura layouts e widgets, incluindo QGraphicsView, QLineEdits, QLabel, QCheckBox, QPushButton e QDialogButtonBox.
        - Conecta os sinais dos botões a funções específicas.
        - Inverte o eixo Y do QGraphicsView.
        """
        Dialog.setObjectName("Dialog")  # Define o nome do objeto do diálogo como "Dialog"
        Dialog.resize(270, 360)  # Redimensiona o diálogo para 270x360 pixels
        Dialog.setMaximumSize(QtCore.QSize(270, 360))  # Define o tamanho máximo do diálogo para 270x360 pixels
        self.gridLayout_6 = QtWidgets.QGridLayout(Dialog)  # Cria um layout de grade para o diálogo
        self.gridLayout_6.setObjectName("gridLayout_6")  # Define o nome do objeto do layout de grade
        self.frame = QtWidgets.QFrame(Dialog)  # Cria um frame dentro do diálogo
        self.frame.setFrameShape(QtWidgets.QFrame.Shape.Box)  # Define a forma do frame como uma caixa
        self.frame.setFrameShadow(QtWidgets.QFrame.Shadow.Raised)  # Define a sombra do frame como elevada
        self.frame.setObjectName("frame")  # Define o nome do objeto do frame
        self.gridLayout_5 = QtWidgets.QGridLayout(self.frame)  # Cria um layout de grade para o frame
        self.gridLayout_5.setObjectName("gridLayout_5")  # Define o nome do objeto do layout de grade
        self.graphicsView = QtWidgets.QGraphicsView(self.frame)  # Cria um QGraphicsView dentro do frame
        self.graphicsView.setObjectName("graphicsView")  # Define o nome do objeto do QGraphicsView
        self.gridLayout_5.addWidget(self.graphicsView, 0, 0, 1, 1)  # Adiciona o QGraphicsView ao layout de grade na posição (0, 0)

        self.frame_2 = QtWidgets.QFrame(self.frame)  # Inicializa frame_2 dentro do frame principal
        self.frame_2.setFrameShape(QtWidgets.QFrame.Shape.Box)  # Define a forma do frame como uma caixa
        self.frame_2.setFrameShadow(QtWidgets.QFrame.Shadow.Raised)  # Define a sombra do frame como elevada
        self.frame_2.setObjectName("frame_2")  # Define o nome do objeto do frame
        self.gridLayout_4 = QtWidgets.QGridLayout(self.frame_2)  # Cria um layout de grade para frame_2
        self.gridLayout_4.setObjectName("gridLayout_4")  # Define o nome do objeto do layout de grade
        self.gridLayout = QtWidgets.QGridLayout()  # Cria um layout de grade
        self.gridLayout.setObjectName("gridLayout")  # Define o nome do objeto do layout de grade

        self.label = QtWidgets.QLabel(self.frame_2)  # Cria um QLabel dentro de frame_2
        self.label.setObjectName("label")  # Define o nome do objeto do QLabel
        self.gridLayout.addWidget(self.label, 0, 0, 1, 1)  # Adiciona o QLabel ao layout de grade na posição (0, 0)

        self.lineEditX = QtWidgets.QLineEdit(self.frame_2)  # Cria um QLineEdit dentro de frame_2
        self.lineEditX.setObjectName("lineEditX")  # Define o nome do objeto do QLineEdit
        self.lineEditX.setText("0")  # Define o valor inicial como "0"
        self.lineEditX.setPlaceholderText("0")  # Define o texto do placeholder como "0"
        self.lineEditX.setAlignment(Qt.AlignmentFlag.AlignCenter)  # Centraliza o texto em lineEditX
        self.gridLayout.addWidget(self.lineEditX, 0, 1, 1, 1)  # Adiciona o QLineEdit ao layout de grade na posição (0, 1)

        self.label_5 = QtWidgets.QLabel(self.frame_2)  # Cria um QLabel dentro de frame_2
        self.label_5.setObjectName("label_5")  # Define o nome do objeto do QLabel
        self.gridLayout.addWidget(self.label_5, 0, 2, 1, 1)  # Adiciona o QLabel ao layout de grade na posição (0, 2)

        self.lineEditY = QtWidgets.QLineEdit(self.frame_2)  # Cria um QLineEdit dentro de frame_2
        self.lineEditY.setObjectName("lineEditY")  # Define o nome do objeto do QLineEdit
        self.lineEditY.setText("0")  # Define o valor inicial como "0"
        self.lineEditY.setPlaceholderText("0")  # Define o texto do placeholder como "0"
        self.lineEditY.setAlignment(Qt.AlignmentFlag.AlignCenter)  # Centraliza o texto em lineEditY
        self.gridLayout.addWidget(self.lineEditY, 0, 3, 1, 1)  # Adiciona o QLineEdit ao layout de grade na posição (0, 3)

        self.label_3 = QtWidgets.QLabel(self.frame_2)  # Cria um QLabel dentro de frame_2
        self.label_3.setObjectName("label_3")  # Define o nome do objeto do QLabel
        self.gridLayout.addWidget(self.label_3, 1, 0, 1, 1)  # Adiciona o QLabel ao layout de grade na posição (1, 0)

        self.lineEditPX = QtWidgets.QLineEdit(self.frame_2)  # Cria um QLineEdit dentro de frame_2
        self.lineEditPX.setObjectName("lineEditPX")  # Define o nome do objeto do QLineEdit
        self.lineEditPX.setAlignment(Qt.AlignmentFlag.AlignCenter)  # Centraliza o texto em lineEditPX
        self.gridLayout.addWidget(self.lineEditPX, 1, 1, 1, 1)  # Adiciona o QLineEdit ao layout de grade na posição (1, 1)

        self.label_4 = QtWidgets.QLabel(self.frame_2)  # Cria um QLabel dentro de frame_2
        self.label_4.setObjectName("label_4")  # Define o nome do objeto do QLabel
        self.gridLayout.addWidget(self.label_4, 1, 2, 1, 1)  # Adiciona o QLabel ao layout de grade na posição (1, 2)

        self.lineEditPY = QtWidgets.QLineEdit(self.frame_2)  # Cria um QLineEdit dentro de frame_2
        self.lineEditPY.setObjectName("lineEditPY")  # Define o nome do objeto do QLineEdit
        self.lineEditPY.setAlignment(Qt.AlignmentFlag.AlignCenter)  # Centraliza o texto em lineEditPY
        self.gridLayout.addWidget(self.lineEditPY, 1, 3, 1, 1)  # Adiciona o QLineEdit ao layout de grade na posição (1, 3)

        self.gridLayout_4.addLayout(self.gridLayout, 0, 0, 1, 2)  # Adiciona o layout de grade gridLayout ao layout de grade gridLayout_4 na posição (0, 0) ocupando 1 linha e 2 colunas

        self.checkBoxPropocao = QtWidgets.QCheckBox(self.frame_2)  # Cria um QCheckBox dentro de frame_2
        self.checkBoxPropocao.setObjectName("checkBoxPropocao")  # Define o nome do objeto do QCheckBox
        self.gridLayout_4.addWidget(self.checkBoxPropocao, 1, 0, 1, 1)  # Adiciona o QCheckBox ao layout de grade na posição (1, 0)

        self.pushButtonReseta = QtWidgets.QPushButton(self.frame_2)  # Cria um QPushButton dentro de frame_2
        self.pushButtonReseta.setObjectName("pushButtonReseta")  # Define o nome do objeto do QPushButton
        self.gridLayout_4.addWidget(self.pushButtonReseta, 1, 1, 1, 1)  # Adiciona o QPushButton ao layout de grade na posição (1, 1)

        self.gridLayout_5.addWidget(self.frame_2, 1, 0, 1, 1)  # Adiciona frame_2 ao layout de grade gridLayout_5 na posição (1, 0) ocupando 1 linha e 1 coluna

        self.pushButtonAdd = QtWidgets.QPushButton(self.frame)  # Cria um QPushButton dentro do frame principal
        self.pushButtonAdd.setObjectName("pushButtonAdd")  # Define o nome do objeto do QPushButton
        self.gridLayout_5.addWidget(self.pushButtonAdd, 2, 0, 1, 1)  # Adiciona o QPushButton ao layout de grade na posição (2, 0)

        self.gridLayout_6.addWidget(self.frame, 0, 0, 1, 1)  # Adiciona o frame principal ao layout de grade gridLayout_6 na posição (0, 0) ocupando 1 linha e 1 coluna

        self.buttonBox = QtWidgets.QDialogButtonBox(Dialog)  # Cria um QDialogButtonBox dentro do diálogo
        self.buttonBox.setStandardButtons(QtWidgets.QDialogButtonBox.StandardButton.Cancel | QtWidgets.QDialogButtonBox.StandardButton.Ok)  # Define os botões padrão como Cancelar e Ok
        self.buttonBox.setCenterButtons(True)  # Centraliza os botões
        self.buttonBox.setObjectName("buttonBox")  # Define o nome do objeto do QDialogButtonBox
        self.gridLayout_6.addWidget(self.buttonBox, 1, 0, 1, 1)  # Adiciona o QDialogButtonBox ao layout de grade na posição (1, 0)

        self.retranslateUi(Dialog)  # Chama a função retranslateUi para definir os textos dos widgets
        QtCore.QMetaObject.connectSlotsByName(Dialog)  # Conecta os slots por nome

        self.graphicsView.setTransform(QtGui.QTransform().scale(1, -1))  # Inverte o eixo Y do QGraphicsView

        self.buttonBox.accepted.connect(self.aceitar)  # Conecta o botão OK do buttonBox à função aceitar
        self.buttonBox.rejected.connect(self.remover_imagem)  # Conecta o botão Cancelar ao método de remoção

    def remover_imagem(self):
        """
        Remove a imagem do QGraphicsView e reseta os dados de screen_overlay.
        
        Funções:
        - Verifica se o item do pixmap existe e o remove da cena do QGraphicsView.
        - Reseta o caminho da imagem e os dados de screen_overlay do pai.
        - Atualiza o texto e o estilo do botão pushButton_Screen do pai.
        - Desativa os controles.
        - Rejeita (fecha) o diálogo.
        """
        # Verifica se o item do pixmap existe e o remove da cena do QGraphicsView
        if hasattr(self, 'pixmap_item') and self.pixmap_item:
            scene = self.graphicsView.scene()  # Obtém a cena do QGraphicsView
            if scene:
                scene.removeItem(self.pixmap_item)  # Remove o item do pixmap da cena
                self.pixmap_item = None  # Reseta o item do pixmap

        self.image_path = None  # Reseta o caminho da imagem

        # Verifica se o pai tem dados de screen_overlay e os reseta
        if hasattr(self.parent(), 'screen_overlay_data'):
            self.parent().screen_overlay_data = {}

        # Atualiza o texto e o estilo do botão pushButton_Screen do pai
        self.parent().pushButton_Screen.setText(self.tr("ScreenOverlay"))
        self.parent().pushButton_Screen.setStyleSheet(self.parent().pushButton_Screen_default_style)

        self.desativar_controles()  # Desativa os controles

        self.reject()  # Rejeita (fecha) o diálogo

        # Desativa o botão OK porque a imagem foi removida
        self.buttonBox.button(QDialogButtonBox.StandardButton.Ok).setEnabled(False)

    def retranslateUi(self, Dialog):
        """
        Define os textos dos widgets do diálogo, traduzindo-os conforme necessário.
        
        Parâmetros:
        Dialog: QDialog - O diálogo que está sendo configurado.
        
        Funções:
        - Define o título da janela do diálogo.
        - Define os textos dos labels, checkboxes e botões.
        """
        
        _translate = QtCore.QCoreApplication.translate  # Atalho para a função de tradução do Qt

        Dialog.setWindowTitle(_translate("Dialog", "Dialog"))  # Define o título da janela do diálogo como "Dialog"

        self.label.setText(_translate("Dialog", self.tr("OverlayXY:"))) # Define o texto do QLabel self.label como "OverlayXY:"
        self.label_5.setText(_translate("Dialog", "x")) # Define o texto do QLabel self.label_5 como "x"
        self.label_3.setText(_translate("Dialog", "Pixels:"))  # Define o texto do QLabel self.label_3 como "Pixels:"
        self.label_4.setText(_translate("Dialog", "x")) # Define o texto do QLabel self.label_4 como "x"
        self.checkBoxPropocao.setText(_translate("Dialog", self.tr("Manter Proporção"))) # Define o texto do QCheckBox self.checkBoxPropocao como "Manter Proporção"
        self.pushButtonReseta.setText(_translate("Dialog", self.tr("Resetar")))  # Define o texto do QPushButton self.pushButtonReseta como "Reseta"
        self.pushButtonAdd.setText(_translate("Dialog", self.tr("Adicionar"))) # Define o texto do QPushButton self.pushButtonAdd como "Adicionar"

    def ativar_controles(self):
        """
        Ativa os controles do diálogo, permitindo que o usuário interaja com eles.
        
        Funções:
        - Ativa o botão de resetar.
        - Ativa os campos de texto de posição e tamanho da imagem.
        - Ativa a caixa de seleção para manter proporção.
        """
        self.pushButtonReseta.setEnabled(True)  # Ativa o botão de resetar
        self.lineEditPX.setEnabled(True)  # Ativa o campo de texto de largura da imagem
        self.lineEditPY.setEnabled(True)  # Ativa o campo de texto de altura da imagem
        self.lineEditX.setEnabled(True)  # Ativa o campo de texto de posição X da imagem
        self.lineEditY.setEnabled(True)  # Ativa o campo de texto de posição Y da imagem
        self.checkBoxPropocao.setEnabled(True)  # Ativa a caixa de seleção para manter proporção

    def desativar_controles(self):
        """
        Desativa os controles do diálogo, impedindo que o usuário interaja com eles.
        
        Funções:
        - Desativa o botão de resetar.
        - Desativa os campos de texto de posição e tamanho da imagem.
        - Desativa a caixa de seleção para manter proporção.
        """
        self.pushButtonReseta.setEnabled(False)  # Desativa o botão de resetar
        self.lineEditPX.setEnabled(False)  # Desativa o campo de texto de largura da imagem
        self.lineEditPY.setEnabled(False)  # Desativa o campo de texto de altura da imagem
        self.lineEditX.setEnabled(False)  # Desativa o campo de texto de posição X da imagem
        self.lineEditY.setEnabled(False)  # Desativa o campo de texto de posição Y da imagem
        self.checkBoxPropocao.setEnabled(False)  # Desativa a caixa de seleção para manter proporção

    def redimensionar_imagem(self):
        """
        Redimensiona a imagem no QGraphicsView com base nos valores de largura e altura fornecidos pelo usuário.
        
        Funções:
        - Verifica se a imagem original existe.
        - Obtém os valores de largura e altura dos campos de texto.
        - Ajusta os valores de largura e altura para não excederem os tamanhos originais da imagem.
        - Mantém a proporção da imagem se a opção estiver marcada.
        - Aplica a transformação de escala à imagem.
        """
        if not self.original_pixmap:  # Verifica se a imagem original existe
            return

        try:
            largura = int(self.lineEditPX.text())  # Obtém o valor de largura do campo de texto
            altura = int(self.lineEditPY.text())  # Obtém o valor de altura do campo de texto
        except ValueError:  # Lida com valores inválidos
            return

        original_width = self.original_pixmap.width()  # Obtém a largura original da imagem
        original_height = self.original_pixmap.height()  # Obtém a altura original da imagem

        if largura > original_width:  # Ajusta a largura para não exceder a largura original
            largura = original_width
            self.lineEditPX.setText(str(largura))

        if altura > original_height:  # Ajusta a altura para não exceder a altura original
            altura = original_height
            self.lineEditPY.setText(str(altura))

        if self.checkBoxPropocao.isChecked():  # Mantém a proporção da imagem se a opção estiver marcada
            aspect_ratio = original_width / original_height  # Calcula a proporção da imagem
            if self.sender() == self.lineEditPX:  # Ajusta a altura com base na largura
                altura = int(largura / aspect_ratio)
                self.lineEditPY.blockSignals(True)  # Bloqueia sinais temporariamente
                self.lineEditPY.setText(str(altura))
                self.lineEditPY.blockSignals(False)  # Desbloqueia sinais
            elif self.sender() == self.lineEditPY:  # Ajusta a largura com base na altura
                largura = int(altura * aspect_ratio)
                self.lineEditPX.blockSignals(True)  # Bloqueia sinais temporariamente
                self.lineEditPX.setText(str(largura))
                self.lineEditPX.blockSignals(False)  # Desbloqueia sinais

        # Aplicar a transformação de escala
        scale_x = largura / original_width  # Calcula a escala em X
        scale_y = altura / original_height  # Calcula a escala em Y

        transform = QtGui.QTransform()  # Cria uma transformação
        transform.scale(scale_x, scale_y)  # Aplica a escala à transformação
        self.pixmap_item.setTransform(transform)  # Aplica a transformação ao item do pixmap
        
        self.transform_state = self.graphicsView.transform()  # Salvar o estado da transformação após adicionar a imagem

        # Aplica flip + escala no item sem destruir a orientação
        self._apply_pixmap_transform(largura, altura)

        # Depois que o tamanho final ficou “definido”, sincroniza OverlayXY
        if getattr(self, "_pixels_edited_by_user", False):
            self._sync_overlayxy_from_pixels()
            self._pixels_edited_by_user = False

    def _mark_pixels_user_edit(self, *_):
        # Só marca (não sincroniza aqui) pra pegar o valor final após redimensionar/ajuste de proporção
        self._pixels_edited_by_user = True

    def _sync_overlayxy_from_pixels(self):
        """
        Copia Pixels (PX/PY) -> OverlayXY (X/Y).
        Começa em 0x0 e só atualiza quando o usuário editar Pixels.
        """
        px = self._safe_int(self.lineEditPX.text(), default=0, min_val=0)
        py = self._safe_int(self.lineEditPY.text(), default=0, min_val=0)

        # evita disparar atualizar_posicao_imagem / loops
        self.lineEditX.blockSignals(True)
        self.lineEditY.blockSignals(True)
        self.lineEditX.setText(str(px))
        self.lineEditY.setText(str(py))
        self.lineEditX.blockSignals(False)
        self.lineEditY.blockSignals(False)

    def _safe_int(self, txt: str, default: int = 0, min_val: int | None = 0, max_val: int | None = None) -> int:
        try:
            v = int(str(txt).strip())
        except Exception:
            v = default
        if min_val is not None:
            v = max(min_val, v)
        if max_val is not None:
            v = min(max_val, v)
        return v

    def _apply_pixmap_transform(self, largura_px: int | None = None, altura_px: int | None = None):
        """
        Mantém o sistema Y+ para cima (por causa do transform do View) e deixa a imagem "em pé".
        - View: scale(1, -1)  -> y visual cresce pra cima
        - Item: aplica flip vertical + translate + escala -> imagem aparece correta e tamanho acompanha lineEdits
        """
        if not self.pixmap_item or not self.original_pixmap:
            return

        ow = self.original_pixmap.width()
        oh = self.original_pixmap.height()
        if ow <= 0 or oh <= 0:
            return

        if largura_px is None:
            largura_px = ow
        if altura_px is None:
            altura_px = oh

        # limita e evita zero
        largura_px = self._safe_int(largura_px, default=ow, min_val=1, max_val=ow)
        altura_px  = self._safe_int(altura_px,  default=oh, min_val=1, max_val=oh)

        sx = largura_px / ow
        sy = altura_px / oh

        t = QtGui.QTransform(sx, 0, 0, -sy, 0, sy * oh)
        self.pixmap_item.setTransform(t)

        # mantém eixos coerentes com tamanho atual
        self.adicionar_linhas_eixos()

    def adicionar_linhas_eixos(self):
        """
        Adiciona linhas horizontais e verticais no QGraphicsView para indicar os eixos da imagem.
        
        Funções:
        - Verifica se o item do pixmap existe.
        - Obtém as coordenadas da origem da imagem.
        - Cria e adiciona uma linha horizontal se não existir, ou atualiza a posição da linha existente.
        - Cria e adiciona uma linha vertical se não existir, ou atualiza a posição da linha existente.
        """
        if not self.pixmap_item:
            return

        scene = self.graphicsView.scene()
        if not scene:
            return

        # Se as linhas existirem mas pertencerem a outra scene (ou foram deletadas), descarta
        for attr in ("linha_horizontal", "linha_vertical"):
            item = getattr(self, attr, None)
            if item:
                try:
                    if item.scene() is not scene:
                        setattr(self, attr, None)
                except RuntimeError:
                    setattr(self, attr, None)

        x_origem = self.pixmap_item.pos().x()
        y_origem = self.pixmap_item.pos().y()

        # Use o boundingRect já transformado, senão a linha fica errada quando você escala
        br = self.pixmap_item.mapToScene(self.pixmap_item.boundingRect()).boundingRect()
        largura = br.width()
        altura  = br.height()

        # Horizontal
        if not self.linha_horizontal:
            self.linha_horizontal = scene.addLine(
                x_origem, y_origem, x_origem + largura, y_origem,
                QtGui.QPen(QColor(255, 0, 0), 3))
        else:
            try:
                self.linha_horizontal.setLine(x_origem, y_origem, x_origem + largura, y_origem)
            except RuntimeError:
                self.linha_horizontal = scene.addLine(
                    x_origem, y_origem, x_origem + largura, y_origem,
                    QtGui.QPen(QColor(255, 0, 0), 3))

        # Vertical
        if not self.linha_vertical:
            self.linha_vertical = scene.addLine(
                x_origem, y_origem, x_origem, y_origem + altura,
                QtGui.QPen(QColor(0, 0, 255), 3))
        else:
            try:
                self.linha_vertical.setLine(x_origem, y_origem, x_origem, y_origem + altura)
            except RuntimeError:
                self.linha_vertical = scene.addLine(
                    x_origem, y_origem, x_origem, y_origem + altura,
                    QtGui.QPen(QColor(0, 0, 255), 3))

    def atualizar_posicao_imagem(self):
        """
        Atualiza a posição da imagem no QGraphicsView com base nos valores fornecidos pelo usuário.
        
        Funções:
        - Verifica se o item do pixmap existe.
        - Obtém os valores de posição X e Y dos campos de texto.
        - Ajusta os valores para não serem negativos.
        - Define a nova posição da imagem.
        - Reseta os valores se ambos forem zero.
        - Atualiza o botão pushButton_Screen se a imagem foi removida.
        """
        if not self.pixmap_item:  # Verifica se o item do pixmap existe
            return

        try:
            x = int(self.lineEditX.text())  # Obtém o valor de posição X do campo de texto
            y = int(self.lineEditY.text())  # Obtém o valor de posição Y do campo de texto
        except ValueError:  # Lida com valores inválidos
            x = 0  # Define X como 0
            y = 0  # Define Y como 0
            self.lineEditX.setText(str(x))  # Define o valor de X no campo de texto
            self.lineEditY.setText(str(y))  # Define o valor de Y no campo de texto

        if x < 0:  # Ajusta X para não ser negativo
            x = 0
            self.lineEditX.setText(str(x))

        if y < 0:  # Ajusta Y para não ser negativo
            y = 0
            self.lineEditY.setText(str(y))

        # Ajustar a posição da imagem para o canto inferior esquerdo
        self.pixmap_item.setPos(x, y)  # Define a nova posição da imagem

        # Verificar se ambos os valores são 0 e resetar valores se necessário
        if x == 0 and y == 0:
            self.resetar_valores()  # Reseta os valores

        # Verificar se a imagem foi removida e atualizar o botão
        if x == 0 and y == 0 and self.pixmap_item is None:
            self.parent().pushButton_Screen.setText(self.tr("ScreenOverlay"))  # Atualiza o texto do botão
            self.parent().pushButton_Screen.setStyleSheet("color: black;")  # Define a cor do texto do botão como preto

    def aceitar(self):
        """
        Aceita e salva os dados do screen overlay, fechando o diálogo.
        
        Funções:
        - Verifica se o item do pixmap e o caminho da imagem existem.
        - Cria um dicionário com os dados do screen overlay.
        - Salva os dados no objeto pai.
        - Fecha o diálogo com aceitação.
        """
        if not self.pixmap_item:  # Verifica se o item do pixmap existe
            return

        if not self.image_path:  # Verifica se o caminho da imagem existe
            return

        self.screen_overlay_data = {  # Cria um dicionário com os dados do screen overlay
            "screenXY": (self.lineEditX.text(), self.lineEditY.text()),  # Posição da imagem
            "overlayXY": (1, 1), # Posição do overlay (fixo como 1, 1)
            "sizeXY": (self.lineEditPX.text(), self.lineEditPY.text()), # Tamanho da imagem
            "rotationXY": (0, 0),  # Rotação do overlay (fixo como 0, 0)
            "image_path": self.image_path} # Caminho da imagem

        self.parent().screen_overlay_data = self.screen_overlay_data  # Salva os dados no objeto pai
        self.accept()  # Fecha o diálogo com aceitação

    def carregar_dados_screen_overlay(self):
        """
        Carrega os dados do screen overlay a partir do objeto pai e atualiza a interface do usuário.
        
        Funções:
        - Obtém os dados do screen overlay do objeto pai.
        - Verifica se há dados de screen overlay disponíveis.
        - Carrega a imagem se o caminho existir e for válido.
        - Atualiza os campos de texto com os valores de posição e tamanho.
        - Atualiza a posição e o tamanho da imagem.
        """
        screen_overlay_data = self.parent().screen_overlay_data  # Obtém os dados do screen overlay do objeto pai
        if screen_overlay_data:  # Verifica se há dados de screen overlay disponíveis
            self.image_path = screen_overlay_data.get("image_path")  # Obtém o caminho da imagem
            if self.image_path and os.path.exists(self.image_path):  # Verifica se o caminho da imagem existe e é válido
                self.adicionar_imagem(self.image_path)  # Carrega a imagem

            self.lineEditX.setText(screen_overlay_data["screenXY"][0])  # Atualiza o campo de texto de posição X
            self.lineEditY.setText(screen_overlay_data["screenXY"][1])  # Atualiza o campo de texto de posição Y
            self.lineEditPX.setText(screen_overlay_data["sizeXY"][0])  # Atualiza o campo de texto de largura
            self.lineEditPY.setText(screen_overlay_data["sizeXY"][1])  # Atualiza o campo de texto de altura

            self.atualizar_posicao_imagem()  # Atualiza a posição da imagem
            self.redimensionar_imagem()  # Redimensiona a imagem

    def resetar_valores(self):
        """
        Restaura os valores originais da imagem e dos controles do diálogo.
        - X/Y (OverlayXY) volta para 0x0
        - Pixels volta para o tamanho original
        """
        if not self.original_pixmap:
            return

        # Reset do gatilho (não sincroniza overlay a partir de pixels aqui)
        self._pixels_edited_by_user = False

        # Restaurar os valores originais nos lineEdits (sem disparar sinais)
        largura = self.original_pixmap.width()
        altura = self.original_pixmap.height()

        self.lineEditPX.blockSignals(True)
        self.lineEditPY.blockSignals(True)
        self.lineEditPX.setText(str(largura))
        self.lineEditPY.setText(str(altura))
        self.lineEditPX.blockSignals(False)
        self.lineEditPY.blockSignals(False)

        # OverlayXY deve ficar 0x0 sempre no reset
        self.lineEditX.blockSignals(True)
        self.lineEditY.blockSignals(True)
        self.lineEditX.setText("0")
        self.lineEditY.setText("0")
        self.lineEditX.blockSignals(False)
        self.lineEditY.blockSignals(False)

        # Redefinir a cena do graphicsView
        scene = QtWidgets.QGraphicsScene()
        self.graphicsView.setScene(scene)

        # Ao trocar a scene, as linhas antigas ficam inválidas
        self.linha_horizontal = None
        self.linha_vertical = None

        self.pixmap_item = scene.addPixmap(self.original_pixmap)
        self.original_pos = (0, 0)
        self.pixmap_item.setPos(0, 0)

        # aplica tamanho original
        self._apply_pixmap_transform(largura, altura)
        self.adicionar_linhas_eixos()
        self.graphicsView.fitInView(scene.itemsBoundingRect(), Qt.AspectRatioMode.KeepAspectRatio)

        # Adiciona o "✓" azul ao pushButton_Screen
        self.parent().pushButton_Screen.setText(self.tr("ScreenOverlay ✓"))
        self.parent().pushButton_Screen.setStyleSheet("color: blue;")

    def adicionar_imagem(self, caminho_imagem=None):
        """
        Adiciona uma imagem ao QGraphicsView.
        - X/Y (OverlayXY) inicia 0x0
        - Pixels inicia com o tamanho da imagem
        """
        if not caminho_imagem:
            formatos = self.tr("Imagens (*.png *.jpg *.jpeg *.bmp)")
            caminho_imagem, _ = QFileDialog.getOpenFileName(
                self, self.tr("Selecione uma imagem"), self.last_opened_folder, formatos)

        if not caminho_imagem:
            return

        self.last_opened_folder = os.path.dirname(caminho_imagem)
        self.image_path = caminho_imagem

        pixmap = QPixmap(caminho_imagem)
        self.original_pixmap = pixmap

        scene = QtWidgets.QGraphicsScene()
        self.graphicsView.setScene(scene)

        self.linha_horizontal = None
        self.linha_vertical = None

        self.pixmap_item = scene.addPixmap(pixmap)
        self.original_pos = (0, 0)
        self.pixmap_item.setPos(0, 0)

        largura = pixmap.width()
        altura = pixmap.height()

        # Reset do gatilho (não sincroniza overlay a partir de pixels aqui)
        self._pixels_edited_by_user = False

        # Pixels: set por código (sem sinais)
        self.lineEditPX.blockSignals(True)
        self.lineEditPY.blockSignals(True)
        self.lineEditPX.setText(str(largura))
        self.lineEditPY.setText(str(altura))
        self.lineEditPX.blockSignals(False)
        self.lineEditPY.blockSignals(False)

        # OverlayXY deve iniciar 0x0
        self.lineEditX.blockSignals(True)
        self.lineEditY.blockSignals(True)
        self.lineEditX.setText("0")
        self.lineEditY.setText("0")
        self.lineEditX.blockSignals(False)
        self.lineEditY.blockSignals(False)

        # aplica orientação/tamanho no view invertido
        self._apply_pixmap_transform(largura, altura)

        self.adicionar_linhas_eixos()
        self.ativar_controles()

        self.parent().pushButton_Screen.setText(self.tr("ScreenOverlay ✓"))
        self.parent().pushButton_Screen.setStyleSheet("color: blue;")

        if self.pixmap_item:
            self.buttonBox.button(QDialogButtonBox.StandardButton.Ok).setEnabled(True)
