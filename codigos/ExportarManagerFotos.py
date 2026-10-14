from qgis.PyQt.QtWidgets import QDialog, QCheckBox, QPushButton, QTableView, QAbstractItemView, QProgressBar, QLineEdit, QStyledItemDelegate, QHeaderView, QMessageBox, QGraphicsScene, QFileDialog, QGraphicsPixmapItem, QGraphicsItem, QDialogButtonBox
from qgis.PyQt.QtGui import QStandardItemModel, QStandardItem, QPixmap, QIcon, QPainter, QColor, QBrush, QPen, QDesktopServices
from qgis.PyQt.QtCore import QDir, Qt, QSize, QEvent, QRect, QPoint, QItemSelectionModel, QSettings, QRectF, QUrl, QCoreApplication
from qgis.PyQt import QtCore, QtWidgets, uic, QtGui
from qgis.core import Qgis, QgsNetworkAccessManager, QgsMessageLog
from qgis.PyQt.QtNetwork import QNetworkRequest, QNetworkReply
from PIL.ExifTags import TAGS
from qgis.utils import iface
import pandas as pd
import PIL.ExifTags
import PIL.Image
import simplekml
import zipfile
import time
import os
import re

FORM_CLASS, _ = uic.loadUiType(os.path.join(
    os.path.dirname(__file__), 'fotos_kmz.ui'))

class FotosManager(QDialog, FORM_CLASS):
    """
    Classe que gerencia a interface de exportação de fotos para KMZ.

    Atributos de classe:
    - autor_texto: str - Texto do autor para exibição.
    - exibir_texto: str - Texto padrão para exibição, usado para definir a largura das imagens.
    - nomes_imagens: dict - Dicionário para armazenar os nomes das imagens carregadas.
    - icones_imagens: dict - Dicionário para armazenar os ícones selecionados para cada imagem.
    - info_imagens: dict - Dicionário para armazenar todas as informações EXIF das imagens carregadas.
    - ultima_pasta: str - Caminho da última pasta usada para selecionar imagens.

    Atributos de instância e métodos são definidos no restante da classe.
    """
    autor_texto = ""  # Variável de classe para armazenar o texto do autor
    exibir_texto = "1400"  # Variável de classe para armazenar o texto de exibição padrão
    ultima_pasta = QDir.homePath()  # Variável de classe para armazenar o caminho da última pasta usada

    def __init__(self, parent=None):
        """
        Construtor da classe FotosManager. Inicializa a interface do usuário e configura os elementos gráficos e as conexões de sinal.
        
        Parâmetros:
        parent: QWidget (opcional) - O widget pai, se houver.
        
        Funções:
        - Inicializa a interface do usuário a partir do Designer.
        - Define o título da janela.
        - Inicializa a cena para o QGraphicsView onde os ícones serão exibidos.
        - Conecta os sinais dos widgets aos slots correspondentes.
        - Restaura os textos dos QLineEdits para os valores armazenados.
        - Configura os placeholders dos QLineEdits.
        - Inicialmente desativa certos widgets que dependem da presença de imagens carregadas.
        """
        super(FotosManager, self).__init__(parent)  # Chama o construtor da classe base QDialog
        self.setupUi(self)  # Configura a interface do usuário a partir do Designer

        self.setWindowTitle(self.tr("Exporta Fotos para KMZ"))  # Define o título da janela

        self.icon_scene = QGraphicsScene(self)  # Inicializa a cena para o graphicsViewIcones
        self.graphicsViewIcones.setScene(self.icon_scene)  # Define a cena no QGraphicsView

        # Cache e controle de downloads (precisa existir ANTES de exibir_icone)
        self._nam = QgsNetworkAccessManager.instance()
        self._icon_cache = {}  # {url: QPixmap}
        self._icon_reply = None
        self._icon_req_serial = 0
        self._icon_pending_serial = 0
        self._icon_pending_url = None

        # Estado da sessão (não vaza entre aberturas)
        self.nomes_imagens = {}
        self.icones_imagens = {}
        self.info_imagens = {}

        self.connect_signals()  # Conecta os sinais aos slots

        # Restaura os textos dos line edits
        self.lineEdit_Autor.setText(FotosManager.autor_texto)  # Restaura o texto do autor
        self.lineEditExibir.setText(FotosManager.exibir_texto if FotosManager.exibir_texto != "1400" else "")  # Restaura o texto do tempo de exibição
        self.lineEditExibir.setPlaceholderText("1400")  # Define o texto placeholder para lineEditExibir
        self.lineEditExibir2.setPlaceholderText(self.tr("Automático"))  # Define o texto placeholder para lineEditExibir2
        self.lineEditExibir2.setEnabled(False)  # Desativa lineEditExibir2

        # Inicialmente desativa os itens que dependem de imagens carregadas
        self.lineEdit_Nome.setEnabled(False)  # Desativa lineEdit_Nome
        self.comboBoxLinks.setEnabled(False)  # Desativa comboBoxLinks
        self.graphicsViewIcones.setEnabled(False)  # Desativa graphicsViewIcones
        self.pushButtonKMZ.setEnabled(False)  # Desativa pushButtonKMZ

        # Armazena os estados iniciais dos componentes que precisam ser resetados
        self.lineEdit_Nome_texto_inicial = self.lineEdit_Nome.text()
        self.lineEdit_Autor_texto_inicial = FotosManager.autor_texto
        self.lineEditExibir_texto_inicial = self.lineEditExibir.text()
        # Armazena o estilo padrão do botão de cor
        self.pushButton_Screen_default_style = self.pushButton_Screen.styleSheet()
        # Armazena um modelo vazio para resetar a tableViewFotos
        self.tableViewFotos_modelo_inicial = QStandardItemModel()

    def tr(self, message):
        """
        Traduz textos deste diálogo.
        O contexto precisa ser estável para o Qt Linguist encontrar as traduções.
        """
        return QCoreApplication.translate("FotosManager", message)

    def closeEvent(self, event):
        parent = self.parent()
        if parent:
            parent.fotos_kmz_dlg = None

        if getattr(self, "_icon_reply", None) is not None:
            try:
                self._icon_pending_serial = -1
                self._icon_reply.setProperty("ignore_icon_error", True)
                self._icon_reply.abort()
                self._icon_reply.deleteLater()
            except Exception:
                pass  # nosec B110
            self._icon_reply = None

        super(FotosManager, self).closeEvent(event)

    def abrir_arquivo_no_sistema(self, file_path: str):
        """Abre um arquivo com o aplicativo padrão do sistema (Windows/Linux/macOS)."""
        try:
            ok = QDesktopServices.openUrl(QUrl.fromLocalFile(file_path))
            if not ok:
                self.mostrar_mensagem(self.tr("Não foi possível abrir o arquivo automaticamente: {file_path}").format(file_path=file_path), "Erro")
        except Exception as e:
            self.mostrar_mensagem(self.tr("Erro ao abrir arquivo: {error}").format(error=str(e)), "Erro")

    def _mostrar_pixmap_icone(self, pixmap: QPixmap):
        """
        Renderiza o pixmap do ícone no graphicsViewIcones.
        Compatível com QGIS 4 / Qt6.
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
        Callback de download do ícone.
        Falhas de preview não devem aparecer como erro crítico para o usuário.
        """
        try:
            if serial != self._icon_pending_serial:
                return

            if bool(reply.property("ignore_icon_error")):
                return

            network_error_enum = getattr(QNetworkReply, "NetworkError", QNetworkReply)

            no_error = getattr(network_error_enum, "NoError")

            err = reply.error()

            if err != no_error:
                try:
                    url_key = str(reply.property("icon_url_original") or url or reply.url().toString())
                    QgsMessageLog.logMessage(self.tr("Falha ao carregar pré-visualização do ícone: {url} | erro: {error}").format(url=url_key, error=reply.errorString()), "TempoSalvoTools", Qgis.MessageLevel.Warning)
                except Exception:
                    pass  # nosec B110
                return

            data_bytes = bytes(reply.readAll())
            if not data_bytes:
                try:
                    url_key = str(reply.property("icon_url_original") or url)
                    QgsMessageLog.logMessage(self.tr("Resposta vazia ao baixar ícone: {url}").format(url=url_key), "TempoSalvoTools", Qgis.MessageLevel.Warning)
                except Exception:
                    pass  # nosec B110
                return

            pixmap = QPixmap()
            if not pixmap.loadFromData(data_bytes) or pixmap.isNull():
                try:
                    url_key = str(reply.property("icon_url_original") or url)
                    QgsMessageLog.logMessage(self.tr("Não foi possível decodificar o ícone: {url}").format(url=url_key), "TempoSalvoTools", Qgis.MessageLevel.Warning)
                except Exception:
                    pass  # nosec B110
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
        Exibe o ícone selecionado no comboBoxLinks no graphicsViewIcones
        usando download assíncrono, sem gerar erro visual se o preview falhar.
        """
        current_url = self.comboBoxLinks.currentData()
        if not current_url:
            return

        if not hasattr(self, "_icon_cache"):
            self._icon_cache = {}
        if not hasattr(self, "_nam"):
            self._nam = QgsNetworkAccessManager.instance()
        if not hasattr(self, "_icon_req_serial"):
            self._icon_req_serial = 0
            self._icon_pending_serial = 0
            self._icon_pending_url = None
            self._icon_reply = None

        if current_url in self._icon_cache:
            self._mostrar_pixmap_icone(self._icon_cache[current_url])
            return

        if self._icon_reply is not None and current_url == getattr(self, "_icon_pending_url", None):
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
        #
        try:
            attribute_enum = getattr(QNetworkRequest, "Attribute", QNetworkRequest)

            redirect_policy_enum = getattr(QNetworkRequest, "RedirectPolicy", QNetworkRequest)

            redirect_attribute = getattr(attribute_enum, "RedirectPolicyAttribute")

            redirect_policy = getattr(redirect_policy_enum, "NoLessSafeRedirectPolicy")

            req.setAttribute(redirect_attribute, redirect_policy)

        except (AttributeError, TypeError):
            pass  # nosec B110

        try:
            req.setRawHeader(b"User-Agent", b"Mozilla/5.0")
            req.setRawHeader(b"Accept", b"image/png,image/*;q=0.8,*/*;q=0.5")
        except Exception:
            pass  # nosec B110

        reply = self._nam.get(req)
        reply.setProperty("icon_url_original", current_url)
        reply.setProperty("ignore_icon_error", False)

        self._icon_reply = reply
        reply.finished.connect(lambda s=serial, u=current_url, r=reply: self._on_icon_reply_finished(s, u, r))

    def resetar_componentes(self):
        """
        Reseta os componentes do diálogo para o estado inicial.

        Este método realiza as seguintes ações:
        1. Restaura o texto dos campos de entrada (lineEdits) para os valores iniciais ou salvos.
        2. Reseta o modelo de dados da tabela de fotos para o modelo inicial.
        3. Limpa e reseta a cena gráfica que exibe os ícones.
        4. Exibe o primeiro ícone disponível na lista de ícones.
        5. Restaura o botão de overlay (ScreenOverlay) para o estado padrão.
        6. Desativa os componentes que devem ser inativos até que novas ações sejam realizadas.
        7. Atualiza o estado dos itens baseando-se nas condições atuais.

        Funções principais:
        - `self.lineEdit_Nome.setText(self.lineEdit_Nome_texto_inicial)`: Restaura o texto do campo Nome.
        - `self.lineEdit_Autor.setText(FotosManager.autor_texto)`: Restaura o texto do campo Autor.
        - `self.lineEditExibir.setText(self.lineEditExibir_texto_inicial)`: Restaura o texto do campo Exibir.
        - `self.tableViewFotos.setModel(self.tableViewFotos_modelo_inicial)`: Reseta o modelo da tabela de fotos.
        - `self.icon_scene.clear()`: Limpa a cena gráfica que exibe os ícones.
        - `self.pushButton_Screen.setText("ScreenOverlay")`: Reseta o texto do botão de overlay para o valor inicial.
        - `self.pushButton_Screen.setStyleSheet(self.pushButton_Screen_default_style)`: Reseta o estilo do botão de overlay.
        - `self.lineEdit_Nome.setEnabled(False)`: Desativa o campo Nome até que uma nova pasta seja carregada.
        - `self.atualizar_estado_itens()`: Atualiza o estado de todos os itens.

        """
        # Limpa dados da sessão anterior
        self.nomes_imagens.clear()
        self.icones_imagens.clear()
        self.info_imagens.clear()

        # Reseta o texto do lineEdit_Nome para o valor inicial
        self.lineEdit_Nome.setText(self.lineEdit_Nome_texto_inicial)
        
        # Reseta o texto do lineEdit_Autor para o valor salvo inicialmente
        self.lineEdit_Autor.setText(FotosManager.autor_texto)
        
        # Reseta o texto do lineEditExibir para o valor inicial
        self.lineEditExibir.setText(self.lineEditExibir_texto_inicial)
        
        # Reseta o modelo da tableViewFotos para um modelo vazio
        self.tableViewFotos.setModel(self.tableViewFotos_modelo_inicial)
        
        # Limpa a cena do graphicsViewIcones
        self.icon_scene.clear()
        
        # Exibe o primeiro ícone da lista no graphicsViewIcones
        if self.comboBoxLinks.count() > 0:
            self.comboBoxLinks.setCurrentIndex(0)  # Seleciona o primeiro item do comboBox
            self.exibir_icone()  # Exibe o ícone selecionado

        # Reseta o estado do pushButton_Screen
        self.pushButton_Screen.setText(self.tr("ScreenOverlay"))  # Reseta o texto para o valor inicial
        self.pushButton_Screen.setStyleSheet(self.pushButton_Screen_default_style)  # Reseta o estilo para o padrão
        self.screen_overlay_data = {}  # Limpa qualquer dado associado ao ScreenOverlay

        # Desativa novamente os itens até que uma nova pasta seja carregada
        self.lineEdit_Nome.setEnabled(False)  # Desativa o campo Nome
        self.comboBoxLinks.setEnabled(False)  # Desativa o comboBox de Links
        self.graphicsViewIcones.setEnabled(False)  # Desativa o gráfico de ícones
        self.pushButtonKMZ.setEnabled(False)  # Desativa o botão de exportação para KMZ

        self.clear_line_edits() # Resetar os campos de informações

        # Reseta qualquer outra configuração adicional necessária
        self.atualizar_estado_itens()  # Atualiza o estado dos itens baseando-se nas condições atuais

    def showEvent(self, event):
        """
        Evento disparado ao mostrar o diálogo.

        Este método garante que, ao ser exibido, o diálogo seja resetado para seu estado inicial,
        restaurando todos os componentes a partir do método `resetar_componentes`.
        """
        super(FotosManager, self).showEvent(event)
        self.resetar_componentes()  # Chama o método para resetar os componentes

    def connect_signals(self):
        """
        Conecta os sinais dos widgets aos slots correspondentes e configura as propriedades dos QLineEdits e QComboBox.
        
        Funções:
        - Conecta os botões a funções específicas.
        - Configura os QLineEdits para serem apenas leitura, permitindo seleção e cópia.
        - Conecta os sinais de alteração de texto dos QLineEdits para armazenar e validar os valores.
        - Centraliza o texto nos QLineEdits.
        - Limita o número de caracteres nos QLineEdits e filtra caracteres inválidos.
        - Carrega os links no comboBoxLinks.
        - Conecta a mudança de índice do comboBoxLinks a funções específicas.
        - Configura o estilo do comboBoxLinks.
        """
        self.pushButtonAbrir.clicked.connect(self.abrir_pasta)  # Conecta o botão Abrir à função abrir_pasta
        self.pushButton_Screen.clicked.connect(self.abrir_screen_overlay)  # Conecta o botão Screen à função abrir_screen_overlay
        self.pushButtonFecha.clicked.connect(self.close_dialog)  # Conecta o botão para fechar o diálogo
        self.pushButtonKMZ.clicked.connect(self.exportar_para_kmz)  # Conecta o botão para exportar KMZ

        # Configurar QLineEdit para serem apenas leitura e permitir seleção e cópia
        line_edits = [
            self.lineEditLatitude, self.lineEditLongitude, self.lineEditAltitude,
            self.lineEditResolucao, self.lineEditData, self.lineEditHorario]
        for line_edit in line_edits:
            line_edit.setReadOnly(True)  # Define os QLineEdits como apenas leitura

        # Conectar sinais de alteração de texto dos line edits para armazenar os valores
        self.lineEdit_Autor.textChanged.connect(lambda texto: self.atualizar_texto('autor_texto', texto))  # Conecta a mudança de texto do autor
        self.lineEditExibir.textChanged.connect(lambda texto: self.validar_formatar_exibir('exibir_texto', texto, self.lineEditExibir))  # Conecta a mudança de texto do exibir

        # Centralizar o texto em lineEditExibir e lineEditExibir2
        self.lineEditExibir.setAlignment(Qt.AlignmentFlag.AlignCenter)  # Centraliza o texto em lineEditExibir
        self.lineEditExibir2.setAlignment(Qt.AlignmentFlag.AlignCenter)  # Centraliza o texto em lineEditExibir2

        # Limitar o número de caracteres e filtrar caracteres inválidos
        self.lineEdit_Autor.setMaxLength(32)  # Limita o número de caracteres no lineEdit_Autor
        self.lineEdit_Nome.setMaxLength(32)  # Limita o número de caracteres no lineEdit_Nome
        self.lineEdit_Nome.textChanged.connect(self.filtrar_caracteres_invalidos)  # Conecta a mudança de texto no lineEdit_Nome para filtrar caracteres inválidos

        self.lineEdit_Nome.textChanged.connect(self.atualizar_nome_imagem)  # Conecta a mudança de texto no lineEdit_Nome para atualizar o nome da imagem

        # Carregar os links no comboBoxLinks
        self.carregar_links_comboBox()  # Chama a função para carregar os links no comboBoxLinks

        self.comboBoxLinks.currentIndexChanged.connect(self.exibir_icone)  # Conecta a mudança de índice do comboBoxLinks à função exibir_icone
        self.comboBoxLinks.currentIndexChanged.connect(self.atualizar_icones)  # Conecta a mudança de índice do comboBoxLinks à função atualizar_icones

        # Chamar exibir_icone uma vez para carregar o ícone inicial
        self.exibir_icone()  # Chama a função exibir_icone para carregar o ícone inicial

        # Configurar estilo do comboBoxLinks
        self.comboBoxLinks.setStyleSheet("""
            QComboBox {combobox-popup: 0;}
            QComboBox QAbstractItemView {
                min-height: 140px; /* 10 itens */
                max-height: 140px; /* 10 itens */
                min-width: 90px; /* ajuste conforme necessário */
                max-width: 90px; /* ajuste conforme necessário */}
            """)  # Define o estilo do comboBox

    def filtrar_caracteres_invalidos(self, texto):
        """
        Filtra caracteres inválidos no texto do QLineEdit lineEdit_Nome.
        
        Parâmetros:
        texto: str - O texto inserido no QLineEdit lineEdit_Nome.
        
        Funções:
        - Remove caracteres inválidos do texto.
        - Atualiza o texto do lineEdit_Nome se houver alterações.
        """
        caracteres_invalidos = r'\/:*?"\'|'  # Define os caracteres inválidos
        texto_filtrado = ''.join(c for c in texto if c not in caracteres_invalidos)  # Filtra os caracteres inválidos

        # Atualiza o texto do lineEdit_Nome apenas se houver alterações
        if texto != texto_filtrado:  # Verifica se o texto foi alterado após o filtro
            self.lineEdit_Nome.setText(texto_filtrado)  # Atualiza o texto do lineEdit_Nome com o texto filtrado

    def atualizar_estado_itens(self):
        """
        Atualiza o estado dos widgets dependendo da presença de imagens no tableViewFotos.
        
        Funções:
        - Verifica se há imagens no modelo do tableViewFotos.
        - Habilita ou desabilita os widgets lineEdit_Nome, comboBoxLinks, graphicsViewIcones e pushButtonKMZ com base na presença de imagens.
        """
        tem_imagens = self.tableViewFotos.model() is not None and self.tableViewFotos.model().rowCount() > 0  # Verifica se há imagens no modelo do tableViewFotos
        self.lineEdit_Nome.setEnabled(tem_imagens)  # Habilita/desabilita lineEdit_Nome
        self.comboBoxLinks.setEnabled(tem_imagens)  # Habilita/desabilita comboBoxLinks
        self.graphicsViewIcones.setEnabled(tem_imagens)  # Habilita/desabilita graphicsViewIcones
        self.pushButtonKMZ.setEnabled(tem_imagens)  # Habilita/desabilita pushButtonKMZ

    def close_dialog(self):
        """
        Fecha o diálogo atual.
        
        Funções:
        - Fecha a janela de diálogo.
        """
        self.close()  # Fecha o diálogo

    def abrir_screen_overlay(self):
        """
        Abre um diálogo para adicionar ou editar um ScreenOverlay.
        
        Funções:
        - Cria uma instância do diálogo ScreenOverlay com a janela atual como pai.
        - Executa o diálogo de maneira modal.
        """
        dialog = ScreenOverlay(self)  # Cria uma instância do diálogo ScreenOverlay
        dialog.exec()  # Executa o diálogo de maneira modal

    def atualizar_texto(self, line_edit_name, texto):
        """
        Atualiza o texto armazenado de um QLineEdit específico.

        Parâmetros:
        line_edit_name: str - O nome do atributo de classe que armazena o texto do QLineEdit.
        texto: str - O novo texto a ser armazenado.

        Funções:
        - Usa setattr para atualizar o valor do atributo de classe correspondente ao nome do QLineEdit.
        """
        setattr(FotosManager, line_edit_name, texto)  # Atualiza o valor do atributo de classe correspondente ao nome do QLineEdit

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
        setattr(FotosManager, attr_name, texto)  # Armazena o texto validado no atributo de classe correspondente

    def abrir_pasta(self):
        """
        Abre um diálogo para selecionar uma pasta, carrega imagens da pasta selecionada e atualiza a interface do usuário.

        Funções:
        - Abre um diálogo para selecionar a pasta, usando a última pasta acessada.
        - Atualiza a última pasta usada.
        - Registra o tempo de início do processo de carregamento de imagens.
        - Gera uma lista de caminhos completos das imagens na pasta selecionada, com extensões suportadas.
        - Inicializa uma barra de progresso para o processo de carregamento de imagens.
        - Carrega as imagens no TableView com barra de progresso.
        - Remove a barra de progresso ao finalizar.
        - Calcula o tempo de execução do processo de carregamento de imagens.
        - Mostra uma mensagem de sucesso ou erro, dependendo do resultado.
        """
        # Abre um diálogo para selecionar a pasta, usando a última pasta acessada
        pasta = QFileDialog.getExistingDirectory(self, self.tr("Selecione a pasta com as imagens"), FotosManager.ultima_pasta)

        if pasta:
            # Atualiza a última pasta usada
            FotosManager.ultima_pasta = pasta

            # Registra o tempo de início
            tempo_inicio = time.time()

            # Lista de extensões de imagem suportadas
            extensoes = ['.png', '.jpg', '.jpeg', '.bmp']
            # Lista de caminhos completos das imagens
            caminhos_imagens = [os.path.join(pasta, arquivo) for arquivo in os.listdir(pasta)
                                if any(arquivo.lower().endswith(ext) for ext in extensoes)]

            # Inicializa a barra de progresso
            progressBar, progressMessageBar = self.iniciar_progress_bar(len(caminhos_imagens))

            # Carrega as imagens no TableView com barra de progresso
            self.carregar_imagens_no_tableview(caminhos_imagens, progressBar)

            # Remove a barra de progresso ao finalizar
            iface.messageBar().popWidget(progressMessageBar)

            # Calcula o tempo de execução
            tempo_execucao = time.time() - tempo_inicio

            # Mostra uma mensagem de sucesso
            self.mostrar_mensagem(self.tr("Imagens carregadas em {tempo_execucao:.2f} segundos.").format(tempo_execucao=tempo_execucao), "Sucesso")
        else:
            # Mostra uma mensagem de erro se nenhuma pasta foi selecionada
            self.mostrar_mensagem(self.tr("Nenhuma pasta foi selecionada."), "Erro")

    def iniciar_progress_bar(self, total_steps):
        """
        Inicializa e estiliza uma barra de progresso para indicar o carregamento de imagens.

        Parâmetros:
        total_steps: int - O número total de etapas que a barra de progresso representará.

        Funções:
        - Cria uma mensagem de progresso na barra de mensagens do QGIS.
        - Cria e configura uma instância de QProgressBar.
        - Estiliza a barra de progresso.
        - Adiciona a barra de progresso ao layout da barra de mensagens e exibe na interface.
        - Define o valor máximo da barra de progresso com base no número total de etapas.
        - Retorna a barra de progresso e a mensagem de progresso para atualização futura.
        """
        progressMessageBar = iface.messageBar().createMessage(self.tr("Carregando imagens"))  # Cria uma mensagem de progresso na barra de mensagens do QGIS
        progressBar = QProgressBar()  # Cria uma instância da QProgressBar
        progressBar.setAlignment(Qt.AlignmentFlag.AlignLeft | Qt.AlignmentFlag.AlignVCenter)  # Alinha a barra de progresso à esquerda e verticalmente ao centro
        progressBar.setFormat(self.tr("%p% - %v de %m Imagens Carregadas"))  # Define o formato da barra de progresso
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
                min-height: 5px;
            }""")

        # Adiciona a progressBar ao layout da progressMessageBar e exibe na interface
        progressMessageBar.layout().addWidget(progressBar)  # Adiciona a barra de progresso ao layout da mensagem de progresso
        iface.messageBar().pushWidget(progressMessageBar, Qgis.MessageLevel.Info)  # Exibe a mensagem de progresso na barra de mensagens do QGIS

        # Define o valor máximo da barra de progresso com base no número total de etapas
        progressBar.setMaximum(total_steps)  # Define o valor máximo da barra de progresso

        return progressBar, progressMessageBar  # Retorna a barra de progresso e a mensagem de progresso

    def mostrar_mensagem(self, texto, tipo, duracao=3):
        """
        Exibe uma mensagem na barra de mensagens da interface do QGIS.

        Parâmetros:
        texto: str - O texto da mensagem a ser exibida.
        tipo: str - O tipo da mensagem, que pode ser "Erro" ou "Sucesso".
        duracao: int - A duração da mensagem em segundos (padrão é 3 segundos).

        Funções:
        - Obtém a barra de mensagens da interface do QGIS.
        - Exibe uma mensagem de erro ou sucesso com o nível apropriado baseado no tipo fornecido.
        """
        bar = iface.messageBar()  # Acessa a barra de mensagens da interface do QGIS

        # Exibe a mensagem com o nível apropriado baseado no tipo
        if tipo == "Erro":
            # Mostra uma mensagem de erro na barra de mensagens com um ícone crítico e a duração especificada
            bar.pushMessage("Erro", texto, level=Qgis.MessageLevel.Critical, duration=duracao)
        elif tipo == "Sucesso":
            # Cria o item da mensagem
            msg = bar.createMessage("Sucesso", texto)
            
            # Adiciona a mensagem à barra com o nível informativo e a duração especificada
            bar.pushWidget(msg, level=Qgis.MessageLevel.Info, duration=duracao)

    def mostrar_coordenadas(self):
        """
        Exibe as coordenadas, altitude, resolução, data e horário da imagem selecionada no TableView.
        """
        indexes = self.tableViewFotos.selectedIndexes()
        if not indexes:
            return

        index = indexes[0]
        caminho_imagem = index.data(Qt.ItemDataRole.UserRole)
        self.lineEdit_Nome.setText(self.nomes_imagens.get(caminho_imagem, "N/A"))
        try:
            with PIL.Image.open(caminho_imagem) as imagem:
                exif_data = imagem._getexif()
                if not exif_data:
                    raise ValueError(self.tr("Sem dados EXIF"))

                exif = {TAGS.get(k, k): v for k, v in exif_data.items() if k in TAGS}

                gps_info = exif.get("GPSInfo")
                if gps_info:
                    lat = self._get_gps_coordinate(gps_info, 2, gps_info.get(1))
                    lon = self._get_gps_coordinate(gps_info, 4, gps_info.get(3))
                    alt = self._get_gps_altitude(gps_info)

                    # CORREÇÃO: decimal_to_dms espera 'lat' ou 'lon'
                    if isinstance(lat, (int, float)) and isinstance(lon, (int, float)):
                        lat_dms = self.decimal_to_dms(lat, 'lat')
                        lon_dms = self.decimal_to_dms(lon, 'lon')
                    else:
                        lat_dms, lon_dms = "N/A", "N/A"

                    self.lineEditLatitude.setText(lat_dms)
                    self.lineEditLongitude.setText(lon_dms)
                    self.lineEditAltitude.setText(f"{alt:.2f} m" if isinstance(alt, (int, float)) else str(alt))
                else:
                    self.lineEditLatitude.setText("N/A")
                    self.lineEditLongitude.setText("N/A")
                    self.lineEditAltitude.setText("N/A")

                self.mostrar_resolucao_data_horario(caminho_imagem, exif)

        except Exception:
            erro_txt = self.tr("Erro")
            self.lineEditLatitude.setText(erro_txt)
            self.lineEditLongitude.setText(erro_txt)
            self.lineEditAltitude.setText(erro_txt)
            self.lineEditResolucao.setText(erro_txt)
            self.lineEditData.setText(erro_txt)
            self.lineEditHorario.setText(erro_txt)

    def _get_gps_coordinate(self, gps_info, ref_index, ref):
        """
        Converte os valores GPS em coordenadas decimais.

        Parâmetros:
        gps_info: dict - O dicionário contendo as informações GPS extraídas dos dados EXIF.
        ref_index: int - O índice da coordenada específica (latitude ou longitude) nos dados GPS.
        ref: str - A referência da coordenada (N, S, E, W).

        Retorna:
        float - A coordenada convertida em decimal ou "N/A" em caso de erro.

        Funções:
        - Obtém a coordenada GPS do dicionário gps_info usando o índice fornecido.
        - Verifica se a coordenada e a referência estão presentes.
        - Converte a coordenada de graus, minutos e segundos para decimal.
        - Ajusta o sinal da coordenada com base na referência (N, S, E, W).
        - Retorna a coordenada decimal ou "N/A" em caso de erro.
        """
        try:
            # Converte os valores GPS em coordenadas decimais
            coord = gps_info.get(ref_index)  # Obtém a coordenada GPS do dicionário gps_info
            if not coord or not ref:  # Verifica se a coordenada e a referência estão presentes
                return "N/A"

            coord = [float(x) for x in coord]  # Converte os valores da coordenada para float
            coord = coord[0] + coord[1] / 60 + coord[2] / 3600  # Converte a coordenada de graus, minutos e segundos para decimal

            if ref in ['S', 'W']:  # Ajusta o sinal da coordenada com base na referência
                coord = -coord

            return coord  # Retorna a coordenada decimal
        except Exception as e:
            self.mostrar_mensagem(self.tr("Erro ao converter coordenadas: {error}").format(error=str(e)), "Erro")
            return "N/A"  # Retorna "N/A" em caso de erro

    def _get_gps_altitude(self, gps_info):
        """
        Obtém a altitude dos dados GPS dos dados EXIF.

        Parâmetros:
        gps_info: dict - O dicionário contendo as informações GPS extraídas dos dados EXIF.

        Retorna:
        float - A altitude em metros ou "N/A" em caso de erro.

        Funções:
        - Obtém a altitude dos dados GPS usando a chave 6.
        - Verifica se a altitude está presente.
        - Converte a altitude para float.
        - Verifica a referência da altitude (acima ou abaixo do nível do mar) usando a chave 5.
        - Ajusta o valor da altitude se a referência for abaixo do nível do mar.
        - Retorna a altitude ou "N/A" em caso de erro.
        """
        try:
            # A chave para altitude nos dados EXIF é geralmente 6
            alt = gps_info.get(6)  # Obtém a altitude dos dados GPS
            if not alt:  # Verifica se a altitude está presente
                return "N/A"
            altitude = float(alt)  # Converte a altitude para float

            # Verificar a referência da altitude (acima ou abaixo do nível do mar)
            alt_ref = gps_info.get(5, 0)  # Obtém a referência da altitude usando a chave 5
            if alt_ref == 1:  # Ajusta o valor da altitude se a referência for abaixo do nível do mar
                altitude = -altitude

            return altitude  # Retorna a altitude
        except Exception as e:
            return "N/A"  # Retorna "N/A" em caso de erro

    def mostrar_resolucao_data_horario(self, caminho_imagem, exif):
        """
        Exibe a resolução, data e horário da imagem nos QLineEdits correspondentes.

        Parâmetros:
        caminho_imagem: str - O caminho da imagem a ser aberta.
        exif: dict - O dicionário contendo as informações EXIF extraídas dos dados da imagem.

        Funções:
        - Abre a imagem usando PIL e obtém a resolução.
        - Define a resolução nos QLineEdits correspondentes.
        - Obtém a data e a hora em que a foto foi tirada a partir dos dados EXIF.
        - Formata a data e a hora e define nos QLineEdits correspondentes.
        - Em caso de erro, define os QLineEdits como "Erro".
        """
        try:
            with PIL.Image.open(caminho_imagem) as imagem:  # Abre a imagem usando PIL
                # Obtém a resolução da imagem
                width, height = imagem.size  # Obtém a largura e altura da imagem
                self.lineEditResolucao.setText(f"{width}x{height}")  # Define a resolução no QLineEdit correspondente

                # Obtém a data e a hora em que a foto foi tirada
                data_hora = exif.get("DateTimeOriginal")  # Obtém a data e hora dos dados EXIF
                if data_hora:
                    data, hora = data_hora.split(" ")  # Separa a data e a hora
                    ano, mes, dia = data.split(":")  # Separa ano, mês e dia
                    self.lineEditData.setText(f"{dia}/{mes}/{ano}")  # Define a data no QLineEdit correspondente
                    self.lineEditHorario.setText(hora)  # Define a hora no QLineEdit correspondente
                else:
                    self.lineEditData.setText("N/A")  # Define "N/A" no QLineEdit se não houver data
                    self.lineEditHorario.setText("N/A")  # Define "N/A" no QLineEdit se não houver hora

        except Exception as e:
            erro_txt = self.tr("Erro")
            self.lineEditResolucao.setText(erro_txt)
            self.lineEditData.setText(erro_txt)
            self.lineEditHorario.setText(erro_txt)

    def atualizar_nome_imagem(self, texto):
        """
        Atualiza o nome da imagem selecionada no dicionário nomes_imagens da classe FotosManager.

        Parâmetros:
        texto: str - O novo nome da imagem a ser atualizado.

        Funções:
        - Obtém a seleção atual do TableView.
        - Se não houver seleção, retorna sem fazer nada.
        - Obtém o caminho da imagem selecionada.
        - Atualiza o dicionário nomes_imagens com o novo nome para a imagem selecionada.
        """
        indexes = self.tableViewFotos.selectedIndexes()  # Obtém a seleção atual do TableView
        if not indexes:  # Se não houver seleção, retorna
            return

        index = indexes[0]  # Obtém o primeiro índice selecionado
        caminho_imagem = index.data(Qt.ItemDataRole.UserRole)  # Obtém o caminho da imagem do índice selecionado
        self.nomes_imagens[caminho_imagem] = texto # Atualiza o dicionário nomes_imagens com o novo nome

    def remover_imagem(self, caminho_imagem):
        """
        Remove a imagem especificada do TableView e atualiza a interface do usuário.

        Parâmetros:
        caminho_imagem: str - O caminho da imagem a ser removida.

        Funções:
        - Obtém o modelo do TableView.
        - Encontra e remove a linha correspondente à imagem especificada.
        - Remove a imagem do dicionário nomes_imagens.
        - Limpa os QLineEdits após remover a imagem.
        - Seleciona a próxima imagem no TableView, se disponível.
        - Atualiza o estado dos widgets dependentes da presença de imagens no TableView.
        """
        modelo = self.tableViewFotos.model()  # Obtém o modelo do TableView
        current_index = None
        for row in range(modelo.rowCount()):  # Itera pelas linhas do modelo
            item = modelo.item(row)
            if item.data(Qt.ItemDataRole.UserRole) == caminho_imagem:  # Encontra a linha correspondente à imagem especificada
                current_index = row
                modelo.removeRow(row)  # Remove a linha do modelo
                break

        if caminho_imagem in self.nomes_imagens:
            del self.nomes_imagens[caminho_imagem] # Remove a imagem do dicionário nomes_imagens

        # Limpar os line edits após remover a imagem
        self.clear_line_edits()  # Limpa os QLineEdits

        # Selecionar a próxima imagem, se disponível
        if current_index is not None:  # Verifica se uma linha foi removida
            if current_index < modelo.rowCount():
                next_index = modelo.index(current_index, 0)  # Seleciona a próxima linha
            else:
                next_index = modelo.index(current_index - 1, 0)  # Seleciona a linha anterior
            
            if next_index.isValid():
                self.tableViewFotos.selectionModel().select(next_index, QItemSelectionModel.SelectionFlag.SelectCurrent)  # Seleciona a próxima imagem
                self.mostrar_coordenadas()  # Exibe as coordenadas da próxima imagem

        # Atualizar o estado dos itens
        self.atualizar_estado_itens()  # Atualiza o estado dos widgets

    def clear_line_edits(self):
        """
        Limpa o texto de todos os QLineEdits relacionados às informações da imagem.

        Funções:
        - Limpa os QLineEdits para latitude, longitude, altitude, resolução, data, horário e nome da imagem.
        """
        self.lineEditLatitude.clear()  # Limpa o QLineEdit para latitude
        self.lineEditLongitude.clear()  # Limpa o QLineEdit para longitude
        self.lineEditAltitude.clear()  # Limpa o QLineEdit para altitude
        self.lineEditResolucao.clear()  # Limpa o QLineEdit para resolução
        self.lineEditData.clear()  # Limpa o QLineEdit para data
        self.lineEditHorario.clear()  # Limpa o QLineEdit para horário
        self.lineEdit_Nome.clear()  # Limpa o QLineEdit para o nome da imagem

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
            "https://www.gstatic.com/earth/images/stockicons/190201-2016-animal-paw_4x.png",
        ]
        for url in icon_urls:  # Para cada URL na lista
            name = os.path.splitext(os.path.basename(url))[0]  # Extrai o nome do arquivo sem extensão
            self.comboBoxLinks.addItem(name, url)  # Adiciona o nome e a URL ao comboBoxLinks

    def atualizar_icone_selecionado(self):
        """
        Atualiza o ícone selecionado no comboBoxLinks com base na imagem atualmente selecionada no TableView.

        Funções:
        - Obtém a seleção atual do TableView.
        - Se não houver seleção, retorna sem fazer nada.
        - Obtém o caminho da imagem selecionada.
        - Se a imagem selecionada estiver no dicionário icones_imagens, atualiza o comboBoxLinks para o ícone correspondente.
        - Bloqueia e desbloqueia sinais para evitar loops de sinal.
        - Chama a função exibir_icone para atualizar a exibição do ícone no graphicsViewIcones.
        """
        indexes = self.tableViewFotos.selectedIndexes()  # Obtém a seleção atual do TableView
        if not indexes:  # Se não houver seleção, retorna
            return

        index = indexes[0]  # Obtém o primeiro índice selecionado
        caminho_imagem = index.data(Qt.ItemDataRole.UserRole)  # Obtém o caminho da imagem do índice selecionado
        if caminho_imagem in self.icones_imagens: # Verifica se a imagem está no dicionário icones_imagens
            icon_url = self.icones_imagens[caminho_imagem] # Obtém a URL do ícone

            self.comboBoxLinks.blockSignals(True)  # Bloqueia sinais para evitar loops
            self.comboBoxLinks.setCurrentIndex(self.comboBoxLinks.findData(icon_url))  # Atualiza o índice do comboBoxLinks
            self.comboBoxLinks.blockSignals(False)  # Desbloqueia sinais
            self.exibir_icone()  # Chama a função para atualizar a exibição do ícone no graphicsViewIcones

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

    def gms_to_decimal(self, gms, direction):
        """
        Converte coordenadas em formato GMS (graus, minutos, segundos) para decimal.

        Parâmetros:
        gms: str - A coordenada em formato GMS, ex: "50°30'30".
        direction: str - A direção da coordenada ('N', 'S', 'E', 'W').

        Retorna:
        float - A coordenada em formato decimal.

        Funções:
        - Divide a string GMS em graus, minutos e segundos.
        - Converte graus, minutos e segundos para float.
        - Calcula a coordenada em decimal.
        - Ajusta o sinal da coordenada com base na direção (N, S, E, W).
        """
        parts = gms.split('°')  # Divide a string GMS em partes
        degrees = float(parts[0])  # Converte a parte dos graus para float
        minutes = float(parts[1].split("'")[0])  # Converte a parte dos minutos para float
        seconds = float(parts[1].split("'")[1].replace('"', ''))  # Converte a parte dos segundos para float

        decimal = degrees + minutes / 60 + seconds / 3600  # Calcula a coordenada em decimal

        if direction in ['S', 'W']:  # Ajusta o sinal da coordenada com base na direção
            decimal = -decimal

        return decimal  # Retorna a coordenada em formato decimal

    def gerar_excel(self, excel_file_path, imagens_para_incluir):
        """
        Gera um arquivo Excel contendo informações sobre as imagens incluídas.

        O método realiza as seguintes operações:
        1. Itera sobre a lista de caminhos das imagens fornecida em `imagens_para_incluir`.
        2. Para cada imagem, obtém as informações associadas, como nome, latitude, longitude, altitude, data e horário.
        3. Organiza esses dados em uma lista de listas, onde cada sublista contém as informações de uma imagem.
        4. Converte a lista de dados em um DataFrame do pandas, com colunas nomeadas.
        5. Salva o DataFrame em um arquivo Excel no caminho especificado por `excel_file_path`, sem incluir um índice.

        Parâmetros:
        - excel_file_path (str): O caminho completo onde o arquivo Excel será salvo.
        - imagens_para_incluir (list): Lista de caminhos de imagens a serem incluídas no Excel.
        """
        data = []  # Inicializa uma lista para armazenar os dados das imagens

        for caminho_imagem in imagens_para_incluir:  # Itera sobre os caminhos das imagens fornecidos
            info = self.info_imagens.get(caminho_imagem, {}) # Obtém as informações da imagem do dicionário info_imagens
            nome_imagem = self.nomes_imagens.get(caminho_imagem, os.path.splitext(os.path.basename(caminho_imagem))[0]) # Obtém o nome da imagem ou usa o nome do arquivo como fallback

            latitude = info.get("latitude", "N/A")  # Obtém a latitude da imagem ou "N/A" se não estiver disponível
            longitude = info.get("longitude", "N/A")  # Obtém a longitude da imagem ou "N/A" se não estiver disponível
            altitude = info.get("altitude", "N/A")  # Obtém a altitude da imagem ou "N/A" se não estiver disponível
            data_imagem = info.get("data", "N/A")  # Obtém a data da imagem ou "N/A" se não estiver disponível
            hora = info.get("hora", "N/A")  # Obtém o horário da imagem ou "N/A" se não estiver disponível
            data.append([nome_imagem, latitude, longitude, altitude, data_imagem, hora])  # Adiciona uma lista com as informações da imagem à lista de dados

        # Converte a lista de dados em um DataFrame do pandas com as colunas nomeadas
        df = pd.DataFrame(data, columns=[self.tr("Nome"), self.tr("Latitude"), self.tr("Longitude"), self.tr("Altitude"), self.tr("Data"), self.tr("Horário")])

        # Salva o DataFrame em um arquivo Excel no caminho
        df.to_excel(excel_file_path, index=False)

    def exportar_para_kmz(self):
        """
        Exporta os dados das imagens para um arquivo KMZ, incluindo KML e Excel.

        Funções:
        - Seleciona o local para salvar o arquivo KMZ.
        - Gera o conteúdo KML e obtém a lista de imagens a serem incluídas.
        - Adiciona conteúdo ScreenOverlay ao KML, se disponível.
        - Escreve o conteúdo KML em um arquivo temporário.
        - Cria um arquivo KMZ, incluindo o KML e as imagens.
        - Remove o arquivo KML temporário.
        - Gera um arquivo Excel com os dados das imagens.
        - Exibe uma mensagem de sucesso com o tempo de execução.
        - Abre o arquivo KMZ gerado, se houver imagens incluídas.
        - Exibe mensagens de erro, se ocorrerem.
        """
        fileName = self.escolher_local_para_salvar(f"{self.tr('FOTOS')}.kmz", self.tr("KMZ files (*.kmz)"))
        if not fileName:
            return

        kml_content, imagens_para_incluir = self.gerar_conteudo_kml()
        if not kml_content:
            self.mostrar_mensagem(self.tr("Erro ao gerar conteúdo KML."), "Erro")
            return

        # Adiciona conteúdo ScreenOverlay ao KML, se disponível
        if hasattr(self, 'screen_overlay_data') and isinstance(self.screen_overlay_data, dict) and self.screen_overlay_data.get("image_path"):
            screen_overlay_content = self.gerar_conteudo_screenoverlay(self.screen_overlay_data)
            kml_content = kml_content.replace('</Document>', screen_overlay_content + '</Document>')

        # Nome do KML dentro do KMZ (sem arquivo temporário)
        kml_name_in_kmz = os.path.splitext(os.path.basename(fileName))[0] + ".kml"

        tempo_inicio = time.time()

        total_steps = len(imagens_para_incluir) + 2  # +1 KML +1 Excel
        progressBar, progressMessageBar = self.iniciar_progress_bar(total_steps)

        try:
            try:
                # Dica de velocidade:
                # - Para JPG, ZIP_STORED costuma ser mais rápido (sem recompressão)
                # - Se quiser manter compressão, deixe ZIP_DEFLATED + compresslevel=1
                with zipfile.ZipFile(fileName, 'w', compression=zipfile.ZIP_STORED) as kmz:
                    # ✅ grava o KML direto no zip (evita open/write/remove)
                    kmz.writestr(kml_name_in_kmz, kml_content.encode("utf-8"))
                    progressBar.setValue(1)

                    # (Opcional, mas ajuda): evita entradas duplicadas no zip
                    added_arcnames = {kml_name_in_kmz}

                    for i, caminho_imagem in enumerate(imagens_para_incluir):
                        arcname = 'files/' + os.path.basename(caminho_imagem)
                        if arcname not in added_arcnames:
                            kmz.write(caminho_imagem, arcname)
                            added_arcnames.add(arcname)
                        progressBar.setValue(i + 2)

                    # ScreenOverlay no KMZ (se tiver)
                    if hasattr(self, 'screen_overlay_data') and isinstance(self.screen_overlay_data, dict) and self.screen_overlay_data.get("image_path"):
                        overlay_path = self.screen_overlay_data["image_path"]
                        arcname = 'files/' + os.path.basename(overlay_path)
                        if arcname not in added_arcnames:
                            kmz.write(overlay_path, arcname)

                # Gerar o arquivo Excel
                excel_file_path = os.path.splitext(fileName)[0] + ".xlsx"
                self.gerar_excel(excel_file_path, imagens_para_incluir)
                progressBar.setValue(total_steps)

                tempo_execucao = time.time() - tempo_inicio
                self.mostrar_mensagem(self.tr("KMZ exportado com sucesso para {fileName} em {tempo_execucao:.2f} segundos.").format(fileName=fileName, tempo_execucao=tempo_execucao), "Sucesso")

                if len(imagens_para_incluir) > 0:
                    self.abrir_arquivo_no_sistema(fileName)

            except Exception as e:
                self.mostrar_mensagem(self.tr("Erro ao criar o arquivo KMZ: {error}").format(error=str(e)), "Erro")

        finally:
            iface.messageBar().popWidget(progressMessageBar)

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
            '</ScreenOverlay>'  # Fecha o elemento ScreenOverlay
        ]
        
        return '\n'.join(screen_overlay_content)  # Junta todas as partes do conteúdo e retorna como uma única string

    def definir_icone_padrao(self, icon_url):
        """
        Define um ícone padrão para todas as imagens no TableView que ainda não possuem um ícone associado.

        Parâmetros:
        icon_url: str - A URL do ícone padrão a ser definido.

        Funções:
        - Verifica se a URL do ícone é válida.
        - Obtém o modelo do TableView.
        - Itera sobre todas as linhas do modelo.
        - Define o ícone padrão para as imagens que ainda não possuem um ícone associado.
        """
        if not icon_url:  # Verifica se a URL do ícone é válida
            return

        modelo = self.tableViewFotos.model()  # Obtém o modelo do TableView
        if modelo is None or modelo.rowCount() == 0:  # Verifica se o modelo é válido e possui linhas
            return

        for row in range(modelo.rowCount()):  # Itera sobre todas as linhas do modelo
            item = modelo.item(row)  # Obtém o item da linha
            caminho_imagem = item.data(Qt.ItemDataRole.UserRole)  # Obtém o caminho da imagem do item
            if caminho_imagem not in self.icones_imagens:
                self.icones_imagens[caminho_imagem] = icon_url

    def atualizar_icones(self):
        """
        Atualiza os ícones das imagens no TableView com base na seleção atual ou define um ícone para todas as imagens.

        Funções:
        - Obtém a seleção atual do TableView.
        - Se não houver seleção, define o ícone para todas as imagens.
        - Se houver seleção, define o ícone apenas para a imagem selecionada.
        """
        indexes = self.tableViewFotos.selectedIndexes()  # Obtém a seleção atual do TableView
        current_url = self.comboBoxLinks.currentData()  # Obtém a URL do ícone selecionado no comboBoxLinks

        if not indexes:  # Se não houver seleção, define o ícone para todas as imagens
            for caminho_imagem in self.nomes_imagens.keys(): # Itera sobre todas as imagens
                self.icones_imagens[caminho_imagem] = current_url # Define o ícone para a imagem
        else:
            # Define o ícone apenas para a imagem selecionada
            index = indexes[0]  # Obtém o primeiro índice selecionado
            caminho_imagem = index.data(Qt.ItemDataRole.UserRole)  # Obtém o caminho da imagem do índice selecionado
            self.icones_imagens[caminho_imagem] = current_url # Define o ícone para a imagem selecionada

    def atualizar_icone_imagem_selecionada(self):
        """
        Atualiza o ícone da imagem atualmente selecionada no TableView.

        Funções:
        - Obtém a seleção atual do TableView.
        - Se não houver seleção, retorna sem fazer nada.
        - Obtém o caminho da imagem selecionada.
        - Obtém a URL do ícone selecionado no comboBoxLinks.
        - Atualiza o dicionário icones_imagens com o novo ícone para a imagem selecionada.
        - Chama a função exibir_icone para atualizar a exibição do ícone no graphicsViewIcones.
        """
        indexes = self.tableViewFotos.selectedIndexes()  # Obtém a seleção atual do TableView
        if not indexes:  # Se não houver seleção, retorna
            return

        index = indexes[0]  # Obtém o primeiro índice selecionado
        caminho_imagem = index.data(Qt.ItemDataRole.UserRole)  # Obtém o caminho da imagem do índice selecionado
        current_url = self.comboBoxLinks.currentData()  # Obtém a URL do ícone selecionado no comboBoxLinks

        if current_url:  # Se a URL do ícone for válida
            self.icones_imagens[caminho_imagem] = current_url  # Atualiza o ícone da imagem selecionada no dicionário icones_imagens
            self.exibir_icone()  # Chama a função para atualizar a exibição do ícone no graphicsViewIcones

    def carregar_imagens_no_tableview(self, caminhos_imagens, progressBar):
        """
        Carrega imagens no TableView e atualiza a barra de progresso.

        Parâmetros:
        caminhos_imagens: list - Lista de caminhos completos das imagens a serem carregadas.
        progressBar: QProgressBar - Barra de progresso para atualizar durante o carregamento das imagens.

        Funções:
        - Cria um modelo padrão e define os cabeçalhos das colunas.
        - Itera sobre os caminhos das imagens, carregando cada imagem e adicionando ao modelo.
        - Redimensiona as imagens se forem maiores que 160x160 pixels.
        - Extrai e armazena informações EXIF das imagens.
        - Define o ícone padrão para cada imagem carregada.
        - Configura o TableView para exibir as miniaturas das imagens.
        - Conecta sinais para exibir coordenadas e atualizar ícones.
        """
        modelo = QStandardItemModel()  # Cria um modelo padrão
        modelo.setHorizontalHeaderLabels([self.tr("Miniaturas")])  # Define os cabeçalhos das colunas

        icon_url = self.comboBoxLinks.currentData()  # Obtém a URL do ícone selecionado no comboBoxLinks

        for i, caminho_completo in enumerate(caminhos_imagens):  # Itera sobre os caminhos das imagens
            pixmap = QPixmap(caminho_completo)  # Carrega a imagem em um QPixmap
            if pixmap.width() > 160 or pixmap.height() > 160:  # Redimensiona a imagem se for maior que 160x160 pixels
                pixmap = pixmap.scaled(160, 160, Qt.AspectRatioMode.KeepAspectRatio, Qt.TransformationMode.SmoothTransformation)
            item = QStandardItem()  # Cria um item padrão
            item.setIcon(QIcon(pixmap))  # Define o ícone do item como a imagem carregada
            item.setData(caminho_completo, Qt.ItemDataRole.UserRole)  # Define o caminho da imagem como dado do item
            modelo.appendRow(item)  # Adiciona o item ao modelo
            progressBar.setValue(i + 1)  # Atualiza a barra de progresso
            nome_imagem = os.path.splitext(os.path.basename(caminho_completo))[0]  # Obtém o nome da imagem
            self.nomes_imagens[caminho_completo] = nome_imagem # Armazena o nome da imagem
            self.icones_imagens[caminho_completo] = icon_url # Define o ícone padrão para a imagem

            try:
                with PIL.Image.open(caminho_completo) as imagem:  # Abre a imagem usando PIL
                    exif_data = imagem._getexif()  # Obtém os dados EXIF da imagem
                    if exif_data:
                        exif = {
                            TAGS.get(k, k): v
                            for k, v in exif_data.items()
                            if k in TAGS}

                        gps_info = exif.get("GPSInfo")
                        if gps_info:  # Obtém informações de GPS se disponíveis
                            lat = self._get_gps_coordinate(gps_info, 2, gps_info.get(1))
                            lon = self._get_gps_coordinate(gps_info, 4, gps_info.get(3))
                            alt = self._get_gps_altitude(gps_info)
                        else:
                            lat, lon, alt = "N/A", "N/A", "N/A"

                        data_hora = exif.get("DateTimeOriginal", "N/A N/A").split()
                        data = data_hora[0] if len(data_hora) > 0 else "N/A"
                        hora = data_hora[1] if len(data_hora) > 1 else "N/A"

                        width, height = imagem.size  # Obtém a resolução da imagem
                        resolucao = f"{width}x{height}"

                        # FotosManager.info_imagens[caminho_completo]
                        self.info_imagens[caminho_completo] = {
                            "latitude": lat,
                            "longitude": lon,
                            "altitude": alt,
                            "data": data,
                            "hora": hora,
                            "resolucao": resolucao}

            except Exception as e:
                self.mostrar_mensagem(self.tr("Erro ao converter coordenadas: {error}").format(error=str(e)), "Erro")
                return "N/A"

        self.tableViewFotos.setModel(modelo)  # Define o modelo do TableView
        self.tableViewFotos.setItemDelegate(DeleteButtonDelegate(self))  # Define o delegate para o botão de deletar
        self.tableViewFotos.setSelectionBehavior(QAbstractItemView.SelectionBehavior.SelectRows)  # Define o comportamento de seleção para linhas
        self.tableViewFotos.setEditTriggers(QAbstractItemView.EditTrigger.NoEditTriggers)  # Define o comportamento de edição
        self.tableViewFotos.setIconSize(QSize(160, 160))  # Define o tamanho dos ícones

        for row in range(modelo.rowCount()):  # Define a altura das linhas para se ajustar aos ícones
            self.tableViewFotos.setRowHeight(row, modelo.item(row).icon().availableSizes()[0].height())

        header = self.tableViewFotos.horizontalHeader()  # Obtém o cabeçalho horizontal
        header.setDefaultAlignment(Qt.AlignmentFlag.AlignHCenter | Qt.AlignmentFlag.AlignVCenter)  # Define o alinhamento do cabeçalho
        header.setSectionResizeMode(QHeaderView.ResizeMode.Stretch)  # Define o modo de redimensionamento das seções

        modelo.setHeaderData(0, Qt.Orientation.Horizontal, Qt.AlignmentFlag.AlignCenter, Qt.ItemDataRole.TextAlignmentRole)  # Define o alinhamento dos dados do cabeçalho

        selection_model = self.tableViewFotos.selectionModel()  # Obtém o modelo de seleção
        selection_model.selectionChanged.connect(self.mostrar_coordenadas)  # Conecta o sinal de alteração de seleção para exibir coordenadas
        selection_model.selectionChanged.connect(self.atualizar_icone_selecionado)  # Conecta o sinal de alteração de seleção para atualizar ícones

        self.atualizar_estado_itens()  # Atualiza o estado dos itens

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

    def _xml_escape(self, s) -> str:
        """Escapa texto para uso seguro dentro de tags XML (ex: <name>)."""
        if s is None:
            return ""
        s = str(s)
        return (s.replace("&", "&amp;")
                 .replace("<", "&lt;")
                 .replace(">", "&gt;")
                 .replace('"', "&quot;")
                 .replace("'", "&apos;"))

    def gerar_conteudo_kml(self, screen_overlay_data=None):
        """
        Gera o conteúdo KML para todas as imagens carregadas no TableView e, opcionalmente, para o ScreenOverlay.

        Parâmetros:
        screen_overlay_data: dict (opcional) - O dicionário contendo os dados do ScreenOverlay.

        Retorna:
        tuple - Contendo o conteúdo KML como string e uma lista de imagens para incluir no KMZ.

        Funções:
        - Obtém o nome da última pasta usada.
        - Cria a estrutura inicial do documento KML.
        - Itera sobre as imagens carregadas no TableView.
        - Extrai informações EXIF e converte coordenadas para DMS.
        - Adiciona as informações de estilo e marcadores das imagens ao KML.
        - Inclui o ScreenOverlay no KML se fornecido.
        - Retorna o conteúdo KML e a lista de imagens para incluir no KMZ.
        """
        nome_pasta = os.path.basename(FotosManager.ultima_pasta)  # Obtém o nome da última pasta usada
        kml_content = ['<?xml version="1.0" encoding="UTF-8"?>']  # Inicia o conteúdo KML
        kml_content.append('<kml xmlns="http://www.opengis.net/kml/2.2" xmlns:gx="http://www.google.com/kml/ext/2.2" xmlns:kml="http://www.opengis.net/kml/2.2" xmlns:atom="http://www.w3.org/2005/Atom">')
        doc_name = self._xml_escape(f"{nome_pasta}.kmz")
        kml_content.append(f'<Document id="feat_1"><name>{doc_name}</name>')

        kml_content.append('<open>1</open>')  # Define o documento como aberto por padrão

        imagens_para_incluir = []  # Lista de imagens para incluir no KMZ
        modelo = self.tableViewFotos.model()  # Obtém o modelo do TableView

        if modelo is None or modelo.rowCount() == 0:  # Verifica se o modelo é válido e possui imagens
            self.mostrar_mensagem(self.tr("Nenhuma imagem carregada no TableViewFotos"), "Aviso")  # Exibe uma mensagem de erro
            return None, None  # Retorna None se não houver imagens

        largura_imagem = self.lineEditExibir.text() if self.lineEditExibir.text() else "1400"  # Obtém a largura da imagem
        shp_id = 1  # Inicializa o ID do shapefile

        for row in range(modelo.rowCount()):  # Itera sobre as imagens carregadas no TableView
            item = modelo.item(row)  # Obtém o item da linha
            caminho_imagem = item.data(Qt.ItemDataRole.UserRole)  # Obtém o caminho da imagem do item
            nome_imagem = self.nomes_imagens.get(caminho_imagem, os.path.splitext(os.path.basename(caminho_imagem))[0])  # Obtém o nome da imagem

            if caminho_imagem not in self.info_imagens: # Verifica se as informações da imagem estão disponíveis
                self.mostrar_mensagem(self.tr("Informações da imagem não encontradas para {caminho_imagem}").format(caminho_imagem=caminho_imagem), "Erro")  # Exibe uma mensagem de erro
                continue  # Pula para a próxima imagem

            info = self.info_imagens[caminho_imagem] # Obtém as informações da imagem
            latitude = info["latitude"]
            longitude = info["longitude"]
            altitude = info["altitude"]
            data = info["data"]
            hora = info["hora"]
            resolucao = info["resolucao"]

            if latitude == "N/A" or longitude == "N/A":  # Verifica se as coordenadas são válidas
                self.mostrar_mensagem(self.tr("Coordenadas inválidas para a imagem {caminho_imagem}").format(caminho_imagem=caminho_imagem), "Erro")  # Exibe uma mensagem de erro
                continue  # Pula para a próxima imagem

            # Converter latitude e longitude para DMS
            latitude_dms = self.decimal_to_dms(latitude, 'lat')
            longitude_dms = self.decimal_to_dms(longitude, 'lon')

            autor_texto = self._xml_escape(FotosManager.autor_texto)  # serve como “escape” seguro também pro HTML simples

            foto_label = self._xml_escape(self.tr("FOTO"))
            latitude_label = self._xml_escape(self.tr("Latitude"))
            longitude_label = self._xml_escape(self.tr("Longitude"))
            altitude_label = self._xml_escape(self.tr("Altitude"))
            data_label = self._xml_escape(self.tr("Data"))
            horario_label = self._xml_escape(self.tr("Horário"))

            autor_html = (
                f'<td style="text-align:right; font-size:12px; color:blue;"><b>{foto_label}: {autor_texto}</b></td>'
            ) if autor_texto else ''  # Cria o HTML do autor se disponível

            icon_url = self.icones_imagens.get(caminho_imagem, self.comboBoxLinks.itemData(0))  # Obtém a URL do ícone

            # Adiciona o estilo do marcador ao KML
            kml_content.append(
                f'<Style id="stylesel_{shp_id}">'
                f'<BalloonStyle>'
                f'<text><![CDATA[<div style="width:100%"><table width="100%"><tr><td><b>{latitude_label}:</b> {latitude_dms} <b>{longitude_label}:</b> {longitude_dms} <b>{altitude_label}:</b> {altitude}{"m" if altitude != "N/A" else ""}</td>{autor_html}</tr></table></div>'
                f'<p><b>{data_label}:</b> {data} <b>{horario_label}:</b> {hora}</p>'
                f'<div style="width:{largura_imagem}px;"><table width="100%" cellpadding="0" cellspacing="0"><tbody><tr><td><img width="100%" height="auto" src="files/{os.path.basename(caminho_imagem)}"></td></tr></tbody></table></div>'
                f']]></text>'
                f'<displayMode>default</displayMode>'
                f'</BalloonStyle>'
                f'<IconStyle>'
                f'<Icon>'
                f'<href>{self._xml_escape(icon_url)}</href>'
                f'</Icon>'
                f'</IconStyle>'
                f'</Style>')

            # normalize a altitude
            alt_coord = None
            if isinstance(altitude, (int, float)):
                alt_coord = float(altitude)
            elif isinstance(altitude, str):
                try:
                    alt_coord = float(altitude.strip())
                except Exception:
                    alt_coord = None

            # Monta coordinates SEM altitude quando ela não for numérica
            if alt_coord is None:
                coords_txt = f"{longitude},{latitude}"
            else:
                coords_txt = f"{longitude},{latitude},{alt_coord}"

            nome_imagem_xml = self._xml_escape(nome_imagem)

            # Adiciona o marcador da imagem ao KML
            kml_content.append(
                f'<Placemark id="feat_{shp_id}">'
                f'<name>{nome_imagem_xml}</name>'
                f'<styleUrl>#stylesel_{shp_id}</styleUrl>'
                f'<Point id="geom_{shp_id}">'
                f'<coordinates>{coords_txt}</coordinates>'
                f'</Point>'
                f'</Placemark>')

            imagens_para_incluir.append(caminho_imagem)  # Adiciona a imagem à lista de imagens para incluir no KMZ
            shp_id += 1  # Incrementa o ID do shapefile

        # Adicionando o ScreenOverlay se fornecido
        if screen_overlay_data:  # Verifica se os dados do ScreenOverlay foram fornecidos
            kml_content.append(self.gerar_conteudo_screenoverlay(screen_overlay_data))  # Adiciona o ScreenOverlay ao KML

        kml_content.append('</Document>')  # Fecha o documento KML
        kml_content.append('</kml>')  # Fecha o elemento KML

        self.mostrar_mensagem(self.tr("Geração do conteúdo KML concluída."), "Sucesso")  # Exibe uma mensagem informativa

        return '\n'.join(kml_content), imagens_para_incluir  # Retorna o conteúdo KML e a lista de imagens para incluir no KMZ

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

        # Cancel / X / Esc => apenas fechar (sem apagar dados)
        self.buttonBox.rejected.connect(self.reject)

        # OK => salvar
        self.buttonBox.accepted.connect(self.aceitar)

        # Botão explícito para apagar o overlay (sem depender do Cancel)
        self.buttonRemove = self.buttonBox.addButton(self.tr("Remover"), QtWidgets.QDialogButtonBox.ButtonRole.DestructiveRole)
        self.buttonRemove.clicked.connect(self.remover_imagem)

    def _sync_parent_screen_button(self):
        """Sincroniza o botão do pai com o estado atual de parent.screen_overlay_data."""
        p = self.parent()
        if not p or not hasattr(p, "pushButton_Screen"):
            return

        data = getattr(p, "screen_overlay_data", None)
        tem_overlay = isinstance(data, dict) and bool(data.get("image_path"))

        if tem_overlay:
            p.pushButton_Screen.setText(self.tr("ScreenOverlay ✓"))
            p.pushButton_Screen.setStyleSheet("color: blue;")
        else:
            p.pushButton_Screen.setText(self.tr("ScreenOverlay"))
            default_style = getattr(p, "pushButton_Screen_default_style", "")
            p.pushButton_Screen.setStyleSheet(default_style if default_style else "")

    def reject(self):
        """Cancel / X / Esc: fecha sem salvar e restaura UI do pai."""
        self._sync_parent_screen_button()
        super(ScreenOverlay, self).reject()

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

        # x' = sx*x
        # y' = -sy*y + sy*oh   (flip + "desce" pra manter a base em y=0)
        t = QtGui.QTransform(sx, 0, 0, -sy, 0, sy * oh)
        self.pixmap_item.setTransform(t)

        # mantém eixos coerentes com tamanho atual
        self.adicionar_linhas_eixos()

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

        self.label.setText(_translate("Dialog", "OverlayXY:"))  # Define o texto do QLabel self.label como "OverlayXY:"
        self.label_5.setText(_translate("Dialog", "x"))  # Define o texto do QLabel self.label_5 como "x"
        self.label_3.setText(_translate("Dialog", "Pixels:"))  # Define o texto do QLabel self.label_3 como "Pixels:"
        self.label_4.setText(_translate("Dialog", "x"))  # Define o texto do QLabel self.label_4 como "x"
        self.checkBoxPropocao.setText(_translate("Dialog", self.tr("Manter Proporção")))  # Define o texto do QCheckBox self.checkBoxPropocao como "Manter Proporção"
        self.pushButtonReseta.setText(_translate("Dialog", self.tr("Resetar")))  # Define o texto do QPushButton self.pushButtonReseta como "Reseta"
        self.pushButtonAdd.setText(_translate("Dialog", self.tr("Adicionar")))  # Define o texto do QPushButton self.pushButtonAdd como "Adicionar"

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
        # Aplica flip + escala no item sem destruir a orientação
        self._apply_pixmap_transform(largura, altura)

        self.transform_state = self.graphicsView.transform()  # Salvar o estado da transformação após adicionar a imagem

        # Aplica flip + escala no item sem destruir a orientação
        self._apply_pixmap_transform(largura, altura)

        # Depois que o tamanho final ficou “definido”, sincroniza OverlayXY
        if getattr(self, "_pixels_edited_by_user", False):
            self._sync_overlayxy_from_pixels()
            self._pixels_edited_by_user = False

    def adicionar_linhas_eixos(self):
        """
        Adiciona linhas horizontais e verticais no QGraphicsView para indicar os eixos da imagem.
        
        Funções:
        - Verifica se o item do pixmap existe.
        - Obtém as coordenadas da origem da imagem.
        - Cria e adiciona uma linha horizontal se não existir, ou atualiza a posição da linha existente.
        - Cria e adiciona uma linha vertical se não existir, ou atualiza a posição da linha existente.
        """
        if not self.pixmap_item:  # Verifica se o item do pixmap existe
            return

        # Coordenadas da origem da imagem
        x_origem, y_origem = self.pixmap_item.pos().x(), self.pixmap_item.pos().y()  # Obtém as coordenadas da origem da imagem

        largura = self._safe_int(self.lineEditPX.text(), default=self.original_pixmap.width(), min_val=1)
        altura  = self._safe_int(self.lineEditPY.text(), default=self.original_pixmap.height(), min_val=1)

        # Cria e adiciona a linha horizontal, se não existir
        if not self.linha_horizontal:
            self.linha_horizontal = self.graphicsView.scene().addLine(
                x_origem, y_origem, x_origem + largura, y_origem, QtGui.QPen(QtCore.Qt.GlobalColor.red, 3)
            )  # Cria e adiciona a linha horizontal
        else:
            # Atualiza a posição da linha existente
            self.linha_horizontal.setLine(
                x_origem, y_origem, x_origem + largura, y_origem
            )  # Atualiza a posição da linha horizontal existente

        # Cria e adiciona a linha vertical, se não existir
        if not self.linha_vertical:
            self.linha_vertical = self.graphicsView.scene().addLine(
                x_origem, y_origem, x_origem, y_origem + altura, QtGui.QPen(QtCore.Qt.GlobalColor.blue, 3)
            )  # Cria e adiciona a linha vertical
        else:
            # Atualiza a posição da linha existente
            self.linha_vertical.setLine(
                x_origem, y_origem, x_origem, y_origem + altura
            )  # Atualiza a posição da linha vertical existente

    def resetar_valores(self):
        """
        Restaura os valores originais da imagem e dos controles do diálogo.
        - X/Y (OverlayXY) volta para 0x0
        - Pixels volta para o tamanho original
        """
        if not self.original_pixmap:
            return

        # ✅ reset do gatilho (não sincroniza overlay a partir de pixels aqui)
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

        # ✅ OverlayXY deve ficar 0x0 sempre no reset
        self.lineEditX.blockSignals(True)
        self.lineEditY.blockSignals(True)
        self.lineEditX.setText("0")
        self.lineEditY.setText("0")
        self.lineEditX.blockSignals(False)
        self.lineEditY.blockSignals(False)

        # Redefinir a cena do graphicsView
        scene = QtWidgets.QGraphicsScene()
        self.graphicsView.setScene(scene)

        self.pixmap_item = scene.addPixmap(self.original_pixmap)
        self.original_pos = (0, 0)
        self.pixmap_item.setPos(0, 0)

        # aplica tamanho original
        self._apply_pixmap_transform(largura, altura)

        self.linha_horizontal = None
        self.linha_vertical = None
        self.adicionar_linhas_eixos()

        self.graphicsView.fitInView(scene.itemsBoundingRect(), Qt.AspectRatioMode.KeepAspectRatio)

        # Adiciona o "✓" azul ao pushButton_Screen
        self.parent().pushButton_Screen.setText(self.tr("ScreenOverlay ✓"))
        self.parent().pushButton_Screen.setStyleSheet("color: blue;")

    def atualizar_posicao_imagem(self):
        if not self.pixmap_item:
            return

        x = self._safe_int(self.lineEditX.text(), default=0, min_val=0)
        y = self._safe_int(self.lineEditY.text(), default=0, min_val=0)

        # se o texto estava inválido e foi “consertado”, evita re-entrada
        self.lineEditX.blockSignals(True)
        self.lineEditY.blockSignals(True)
        self.lineEditX.setText(str(x))
        self.lineEditY.setText(str(y))
        self.lineEditX.blockSignals(False)
        self.lineEditY.blockSignals(False)

        self.pixmap_item.setPos(x, y)

        # mantém eixos coerentes com nova posição
        self.adicionar_linhas_eixos()

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

        x  = self._safe_int(self.lineEditX.text(),  default=0, min_val=0)
        y  = self._safe_int(self.lineEditY.text(),  default=0, min_val=0)
        px = self._safe_int(self.lineEditPX.text(), default=1, min_val=1)
        py = self._safe_int(self.lineEditPY.text(), default=1, min_val=1)

        self.screen_overlay_data = {
            "screenXY": (x, y),
            "overlayXY": (1, 1),
            "sizeXY": (px, py),
            "rotationXY": (0, 0),
            "image_path": self.image_path}

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

            self.lineEditX.setText(str(screen_overlay_data["screenXY"][0]))
            self.lineEditY.setText(str(screen_overlay_data["screenXY"][1]))
            self.lineEditPX.setText(str(screen_overlay_data["sizeXY"][0]))
            self.lineEditPY.setText(str(screen_overlay_data["sizeXY"][1]))

            self.atualizar_posicao_imagem()  # Atualiza a posição da imagem
            self.redimensionar_imagem()  # Redimensiona a imagem

    def adicionar_imagem(self, caminho_imagem=None):
        """
        Adiciona uma imagem ao QGraphicsView.
        - X/Y (OverlayXY) inicia 0x0
        - Pixels inicia com o tamanho da imagem
        """
        if not caminho_imagem:
            formatos = self.tr("Imagens (*.png *.jpg *.jpeg *.bmp)")
            caminho_imagem, _ = QFileDialog.getOpenFileName(self, self.tr("Selecione uma imagem"), self.last_opened_folder, formatos)

        if not caminho_imagem:
            return

        self.last_opened_folder = os.path.dirname(caminho_imagem)
        self.image_path = caminho_imagem

        pixmap = QPixmap(caminho_imagem)
        self.original_pixmap = pixmap

        scene = QtWidgets.QGraphicsScene()
        self.graphicsView.setScene(scene)

        self.pixmap_item = scene.addPixmap(pixmap)
        self.original_pos = (0, 0)
        self.pixmap_item.setPos(0, 0)

        largura = pixmap.width()
        altura = pixmap.height()

        # ✅ reset do gatilho (não sincroniza overlay a partir de pixels aqui)
        self._pixels_edited_by_user = False

        # Pixels: set por código (sem sinais)
        self.lineEditPX.blockSignals(True)
        self.lineEditPY.blockSignals(True)
        self.lineEditPX.setText(str(largura))
        self.lineEditPY.setText(str(altura))
        self.lineEditPX.blockSignals(False)
        self.lineEditPY.blockSignals(False)

        # ✅ OverlayXY deve iniciar 0x0
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