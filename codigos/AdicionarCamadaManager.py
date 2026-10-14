from qgis.core import QgsProject, QgsCoordinateReferenceSystem, QgsField, QgsFields, QgsFeature, QgsPoint, QgsWkbTypes, QgsVectorLayer, QgsGeometry, QgsPointXY
from qgis.PyQt.QtCore import Qt, QTimer, QEvent, QMetaType, QCoreApplication
from qgis.PyQt.QtWidgets import QDialog, QHeaderView, QComboBox
from qgis.PyQt.QtGui import QStandardItemModel, QStandardItem
from qgis.gui import QgsProjectionSelectionDialog
from qgis.PyQt import uic
from typing import List
import os
import re

try:
    import win32com.client
except ImportError:
    win32com = None

FORM_CLASS, _ = uic.loadUiType(os.path.join(
    os.path.dirname(__file__), 'AdicionarCoordExcel.ui'))

class CamadaManager(QDialog, FORM_CLASS):
    def __init__(self, parent=None):
        """Constructor."""
        super(CamadaManager, self).__init__(parent)
        # Configura a interface do usuário a partir do Designer.
        self.setupUi(self)
        # Altera o título da janela
        self.setWindowTitle(self.tr("Adicionar Camada Excel"))

        # Preenche combo na abertura do diálogo
        self._atualizar_combo_pasta()

        # Auto-refresh “leve”: dispara sob demanda + intervalos maiores
        self._refresh_busy = False
        self._refresh_interval_active_ms = 8000     # enquanto o diálogo está em uso
        self._refresh_interval_idle_ms = 15000    # quando não há planilhas abertas

        self._timer_refresh = QTimer(self)
        self._timer_refresh.setSingleShot(True)
        self._timer_refresh.timeout.connect(self._refresh_tick)

        # Se o usuário clicar/der foco no combo, atualiza na hora
        self.comboBox_Pasta.installEventFilter(self)

        # agenda 1º refresh imediato
        self._schedule_refresh(0)

        # permite quebra de texto nas células
        self.tableViewDados.setWordWrap(True)

        # cabeçalhos
        hv = self.tableViewDados.horizontalHeader()
        vv = self.tableViewDados.verticalHeader()

        # colunas: esticam para preencher a largura disponível
        hv.setSectionResizeMode(QHeaderView.ResizeMode.Stretch)

        # linhas: ajustam a altura ao conteúdo
        vv.setSectionResizeMode(QHeaderView.ResizeMode.ResizeToContents)

        hh = self.tableViewDados.horizontalHeader()
        # permite que o usuário arraste as seções
        hh.setSectionsMovable(True)
        # define modo inicial como Interactive (pode redimensionar manualmente)
        hh.setSectionResizeMode(QHeaderView.ResizeMode.Interactive)

        # SRC atual do projeto
        proj_crs = QgsProject.instance().crs()
        self.lineEdit_SRC.setText(f"{proj_crs.authid()} - {proj_crs.description()}")
        self.lineEdit_SRC.setReadOnly(True)   # evita edição direta, opcional

        # mensagens de erro apenas para leitura
        self.textEdit_Erros.setReadOnly(True)

        # botão começa desabilitado
        self.pushButtonAdicionar.setEnabled(False)

        # Conecta os sinais aos slots
        self.connect_signals()

    def tr(self, message):
        """
        Traduz textos deste diálogo.
        O contexto precisa ser estável para o Qt Linguist encontrar as traduções.
        """
        return QCoreApplication.translate("CamadaManager", message)

    def _texto_sem_planilha(self):
        """
        Texto padrão para quando não há planilha aberta.
        Centralizar isso evita comparações quebradas quando o idioma muda.
        """
        return self.tr("Nenhuma planilha aberta")

    def connect_signals(self):

        self.comboBox_Pasta.currentIndexChanged.connect(self._on_pasta_changed)

        # sempre que mudar X, Y ou Z, refaz os combos para manter unicidade
        self.comboBoxX.currentIndexChanged.connect(self._atualizar_combos_xyz)
        self.comboBoxY.currentIndexChanged.connect(self._atualizar_combos_xyz)
        self.comboBoxZ.currentIndexChanged.connect(self._atualizar_combos_xyz)

        self.pushButtonSRC.clicked.connect(self._selecionar_crs)

        self.pushButtonAdicionar.clicked.connect(self._adicionar_camada_pontos)

        self.pushButtonFecha.clicked.connect(self.close)

    def closeEvent(self, event):
        if hasattr(self, "_timer_refresh"):
            self._timer_refresh.stop()
        super(CamadaManager, self).closeEvent(event)

    def showEvent(self, event):
        """
        Sempre que o diálogo for exibido, atualiza a lista de pastas
        de trabalho do Excel abertas.
        """
        super(CamadaManager, self).showEvent(event)
        # Atualiza o combo
        self._atualizar_combo_pasta()

        # Se houver algo válido no combo, dispara o carregamento automático
        if self.comboBox_Pasta.isEnabled():
            idx = self.comboBox_Pasta.currentIndex()
            if idx >= 0:
                # reutiliza o slot que já preenche o tableViewDados
                self._on_pasta_changed(idx)

        self._schedule_refresh(0)

    def _listar_workbooks_excel(self) -> List[str]:
        """
        Retorna os nomes dos workbooks abertos numa sessão já em execução do Excel.
        Se o Excel não estiver aberto ou não expor Workbooks, devolve [].
        """
        if win32com is None:  # pywin32 ausente
            return []

        try:
            # Conecta APENAS a uma instância já existente
            excel = win32com.client.GetActiveObject("Excel.Application")
        except Exception:
            # Excel não está rodando
            return []

        # Alguns ambientes podem não expor 'Workbooks' direito
        try:
            wbs = excel.Workbooks
            count = wbs.Count
        except AttributeError:
            return []

        nomes = []
        for i in range(1, count + 1):  # coleção COM é 1-based
            wb = wbs.Item(i)
            nome = os.path.basename(wb.FullName) if wb.FullName else wb.Name
            nomes.append(nome)
        return nomes

    def _atualizar_combo_pasta(self) -> None:
        """
        Atualiza o comboBox_Pasta sem alterar a seleção corrente
        se ela ainda existir e apenas quando a lista realmente muda.
        """
        # Coleta arquivos abertos
        excel_files = self._listar_workbooks_excel()

        # Remove duplicatas mantendo a ordem
        arquivos_vistos = list(dict.fromkeys(excel_files))

        texto_sem_planilha = self._texto_sem_planilha()

        if not arquivos_vistos:
            arquivos_display = [texto_sem_planilha]
        else:
            # Aqui usa a lista sem duplicatas
            arquivos_display = [f"(Excel) {a}" for a in arquivos_vistos]

        # Verifica se a lista mudou
        atuais = [self.comboBox_Pasta.itemText(i)
                  for i in range(self.comboBox_Pasta.count())]

        if arquivos_display == atuais:
            # Nada mudou → não faz nada
            return

        # Guarda seleção corrente
        selecao_atual = self.comboBox_Pasta.currentText()

        # Bloqueia sinais / repaints durante a troca
        self.comboBox_Pasta.blockSignals(True)
        self.comboBox_Pasta.setUpdatesEnabled(False)

        # recria itens
        self.comboBox_Pasta.clear()
        if arquivos_display == [texto_sem_planilha]:
            self.comboBox_Pasta.addItem(texto_sem_planilha)
            self.comboBox_Pasta.setEnabled(False)
        else:
            self.comboBox_Pasta.addItems(arquivos_display)
            self.comboBox_Pasta.setEnabled(True)

        # Restaura seleção se o item ainda existir
        if selecao_atual and selecao_atual in arquivos_display:
            self.comboBox_Pasta.setCurrentIndex(
                arquivos_display.index(selecao_atual))

        # reabilita sinais / repaints
        self.comboBox_Pasta.setUpdatesEnabled(True)
        self.comboBox_Pasta.blockSignals(False)

    def _on_pasta_changed(self, index: int):
        """
        Dispara carregamento da primeira aba da planilha selecionada
        Excel para o tableViewDados.
        """
        if index < 0:
            return

        texto = self.comboBox_Pasta.itemText(index).strip()
        if texto == self._texto_sem_planilha():
            self._limpar_tableview()
            return

        # identifica origem pelo prefixo inserido em _atualizar_combo_pasta
        if texto.startswith("(Excel)"):
            arquivo = texto.replace("(Excel)", "", 1).strip()
            self._carregar_excel(arquivo)
        else:
            self._mostrar_erro(self.tr("Formato não reconhecido."))

    def _limpar_tableview(self):
        vazio = QStandardItemModel(0, 0, self.tableViewDados)
        self.tableViewDados.setModel(vazio)

        self._atualizar_estado_botao_adicionar()

    def _fmt(self, v):
        """
        Converte o valor para string:
        • int ou float inteiro  -> '123'          (sem '.0')
        • float não-inteiro    -> '123,456'      (ponto→vírgula p/ BR-pt)
        • None ou ''           -> ''             (vazio)
        • textos               -> preserva acentos e corrige mojibake comum
        """
        if v is None or v == "":
            return ""
        if isinstance(v, (int, float)):
            # se for "inteiro exato", corta a parte decimal
            if float(v).is_integer():
                return str(int(v))
            # caso contrário formata e troca ponto por vírgula
            return str(v).replace(".", ",")

        return self._corrigir_texto_encoding(str(v))

    def _score_mojibake(self, texto: str) -> int:
        """
        Pontua sinais típicos de texto UTF-8 lido como Latin-1/Windows-1252.
        Ex.: 'DendÃª', 'CajÃ¡', 'EmbaÃºba'.
        """
        if not isinstance(texto, str):
            return 0

        marcadores = ("Ã", "Â", "�", "â€", "â€“", "â€”", "â€˜", "â€™", "â€œ")

        return sum(texto.count(m) for m in marcadores)

    def _corrigir_texto_encoding(self, valor):
        """
        Corrige textos que chegam como mojibake, sem mexer em textos já corretos.
        Ex.: 'DendÃª' -> 'Dendê', 'CajÃ¡' -> 'Cajá', 'EmbaÃºba' -> 'Embaúba'.
        """
        if valor is None:
            return ""

        if not isinstance(valor, str):
            return valor

        texto = valor
        score_original = self._score_mojibake(texto)

        # Se não há sinal de texto corrompido, mantém como está
        if score_original == 0:
            return texto

        # Tenta reconstruir o texto que foi lido com codificação errada
        for enc in ("latin1", "cp1252"):
            try:
                corrigido = texto.encode(enc).decode("utf-8")
            except UnicodeError:
                continue

            if self._score_mojibake(corrigido) < score_original:
                return corrigido

        return texto

    def _try_float(self, v):
        """
        Tenta converter vários formatos de número (BR/US) para float.
        Retorna float ou None se não for número.
        """
        if v is None or v == "":
            return None

        # bool é int em Python; não queremos tratar True/False como número
        if isinstance(v, bool):
            return None

        if isinstance(v, (int, float)):
            return float(v)

        s = str(v).strip()
        if not s:
            return None

        # normalizações básicas
        s = s.replace("\u00A0", " ")     # NBSP
        s = s.replace(" ", "")          # remove espaços (inclui "1 234,56")
        s = s.replace("−", "-")         # menos unicode

        # negativo por parênteses: (123,45)
        neg = False
        if s.startswith("(") and s.endswith(")"):
            neg = True
            s = s[1:-1].strip()

        # negativo com sinal no fim: 123,45-
        if s.endswith("-") and len(s) > 1:
            neg = True
            s = s[:-1]

        # remove símbolos comuns (sem ser agressivo demais)
        s = s.replace("R$", "").replace("$", "").replace("€", "").replace("£", "").replace("%", "")
        s = s.strip()
        if not s:
            return None

        # se tem vírgula e ponto: decide pelo separador decimal mais à direita
        if "," in s and "." in s:
            if s.rfind(",") > s.rfind("."):
                # 1.234,56  -> remove '.' e troca ',' por '.'
                s = s.replace(".", "").replace(",", ".")
            else:
                # 1,234.56  -> remove ',' e mantém '.'
                s = s.replace(",", "")
        else:
            # só vírgula: no BR normalmente é decimal
            if "," in s:
                if s.count(",") > 1:
                    # 1,234,567 -> milhares
                    s = s.replace(",", "")
                else:
                    s = s.replace(",", ".")
            # só ponto: no BR pode ser milhares (1.234) ou decimal (1234.56)
            elif "." in s:
                # se for "milhar clássico" (1.234 ou 12.345 ou 123.456 etc), trata como milhares
                if re.fullmatch(r"[+-]?\d{1,3}\.\d{3}", s) or s.count(".") > 1:
                    s = s.replace(".", "")

        try:
            num = float(s)
            return -num if neg else num
        except Exception:
            return None

    def _is_number(self, v) -> bool:
        return self._try_float(v) is not None

    def _carregar_excel(self, nome_arq: str):
        """
        Abre o workbook que já está aberto no Excel, lê apenas a primeira aba
        e exibe no tableViewDados. Colunas 100% numéricas ficam somente-leitura.
        """
        # Conexão COM
        if win32com is None:
            self._mostrar_erro(self.tr("pywin32 não instalado; não consigo ler Excel."))
            return

        try:
            xl = win32com.client.GetActiveObject("Excel.Application")
        except Exception:
            self._mostrar_erro(self.tr("Excel não está em execução."))
            return

        # Procura o workbook já aberto
        wb = None
        for w in xl.Workbooks:
            if os.path.basename(w.FullName) == nome_arq or w.Name == nome_arq:
                wb = w
                break

        if wb is None:
            self._mostrar_erro(self.tr(f"Workbook '{nome_arq}' não encontrado."))
            return

        # Coleta dados
        sht = wb.Sheets(1)  # primeira aba
        usados = sht.UsedRange
        dados = usados.Value  # tupla 2-D

        if not dados:
            self._mostrar_erro(self.tr("Planilha vazia."))
            return

        n_rows = usados.Rows.Count
        n_cols = usados.Columns.Count

        # Identifica colunas que contêm cabeçalho válido
        keep_cols = []
        for c in range(n_cols):
            cabecalho = dados[0][c]
            tem_cabecalho_vazio = any(
                (cabecalho is None,
                    cabecalho == "",
                    isinstance(cabecalho, (int, float))))

            if not tem_cabecalho_vazio:
                keep_cols.append(c)

        # Cabeçalhos filtrados, já corrigindo acentos/codificação
        headers = [
            "Null"
            if (dados[0][c] is None
                or dados[0][c] == ""
                or isinstance(dados[0][c], (int, float)))
            else self._corrigir_texto_encoding(str(dados[0][c]))
            for c in keep_cols]

        headers = self._headers_unicos(headers)

        # Detecta colunas numéricas já filtradas
        numeric_cols = {
            i
            for i, c in enumerate(keep_cols)
            if all(
                (dados[r][c] in (None, "") or self._is_number(dados[r][c]))
                for r in range(1, n_rows))}

        # Monta modelo
        modelo = QStandardItemModel(
            max(0, n_rows - 1),
            len(keep_cols),
            self.tableViewDados)

        for i, nome in enumerate(headers):
            modelo.setHeaderData(i, Qt.Orientation.Horizontal, nome)

        for r in range(1, n_rows):
            for i, c in enumerate(keep_cols):
                valor = dados[r][c]

                # Aqui passa pelo _fmt, que também corrige textos com acento quebrado
                item = QStandardItem(self._fmt(valor))

                if i in numeric_cols:
                    item.setFlags(item.flags() & ~Qt.ItemFlag.ItemIsEditable)

                modelo.setItem(r - 1, i, item)

        # Aplica ao view
        self.tableViewDados.setModel(modelo)
        self.tableViewDados.resizeRowsToContents()
        self._ajustar_colunas()

        # Atualiza combos e validações
        self._atualizar_combos_xyz()

        for cb in (self.comboBoxX, self.comboBoxY, self.comboBoxZ):
            self._validar_coluna_xyz(cb)

        # Validação de coerência com o CRS
        self._validar_xy_por_crs()

        self._atualizar_estado_botao_adicionar()

    def _headers_unicos(self, headers: list[str]) -> list[str]:
        """
        Garante que os cabeçalhos sejam únicos.
        Duplicados recebem sufixo _2, _3, ...

        Ex.: ["Null", "Null", "X"] -> ["Null", "Null_2", "X"]
        """
        vistos: dict[str, int] = {}
        saida: list[str] = []

        for h in headers:
            base = self._corrigir_texto_encoding("" if h is None else str(h)).strip()

            if base == "" or base.lower() == "none":
                base = "Null"

            n = vistos.get(base, 0) + 1
            vistos[base] = n

            saida.append(base if n == 1 else f"{base}_{n}")

        return saida

    def _schedule_refresh(self, ms: int) -> None:
        """Agenda um refresh sem empilhar timers."""
        if not self.isVisible():
            return
        if hasattr(self, "_timer_refresh") and self._timer_refresh.isActive():
            return
        self._timer_refresh.start(max(0, int(ms)))

    def _refresh_tick(self) -> None:
        """Executa refresh com proteção contra reentrada e com intervalos adaptativos."""
        if not self.isVisible():
            return

        # Evita reentrada
        if getattr(self, "_refresh_busy", False):
            self._schedule_refresh(self._refresh_interval_active_ms)
            return

        self._refresh_busy = True
        try:
            self._atualizar_combo_pasta()
        finally:
            self._refresh_busy = False

        # Se não há planilhas, pode checar bem mais devagar
        if (
            self.comboBox_Pasta.count() == 1
            and self.comboBox_Pasta.itemText(0) == self._texto_sem_planilha()):

            self._schedule_refresh(self._refresh_interval_idle_ms)
        else:
            self._schedule_refresh(self._refresh_interval_active_ms)

    def eventFilter(self, obj, event):
        # Ao interagir com o combo, atualiza imediatamente (sensação de “sempre atual”)
        if obj is getattr(self, "comboBox_Pasta", None):
            if event.type() in (QEvent.Type.MouseButtonPress, QEvent.Type.FocusIn):
                self._schedule_refresh(0)
        return super(CamadaManager, self).eventFilter(obj, event)

    def hideEvent(self, event):
        # Ao ocultar o diálogo, para de consumir CPU
        if hasattr(self, "_timer_refresh"):
            self._timer_refresh.stop()
        super(CamadaManager, self).hideEvent(event)

    def _colunas_numericas(self, matriz_dados) -> set[int]:
        """
        Recebe a matriz de dados (lista/tupla de linhas, sem cabeçalho)
        e devolve o conjunto de índices de colunas 100% numéricas
        (ignora células vazias).
        """
        num_cols = set()
        if not matriz_dados:
            return num_cols

        n_cols = len(matriz_dados[0])
        for c in range(n_cols):
            numeric = True
            for linha in matriz_dados:
                if c >= len(linha):
                    continue
                v = linha[c]
                if v in (None, ""):
                    continue
                if self._try_float(v) is None:
                    numeric = False
                    break

            if numeric:
                num_cols.add(c)
        return num_cols

    def _mostrar_erro(self, msg: str):
        """
        Exibe uma mensagem de erro no textEdit_Erros em vermelho.
        """
        self.textEdit_Erros.clear()

        self.textEdit_Erros.setStyleSheet("""
            QTextEdit {
                color: #b00020;
                background-color: #fdebec;
                border: 1px solid #d9534f;
                border-radius: 3px;}
        """)

        self.textEdit_Erros.setTextColor(
            Qt.GlobalColor.red)

        self.textEdit_Erros.append(msg)

    def _ajustar_colunas(self):
        """
        Ajusta as colunas para o conteúdo ou para preencher o viewport,
        mas sempre em modo Interactive para permitir redimensionamento manual.
        """
        header = self.tableViewDados.horizontalHeader()
        model = self.tableViewDados.model()
        if model is None:
            return

        n_cols = model.columnCount()
        if n_cols == 0:
            return

        # 1) Modo temporário para medir conteúdo
        for col in range(n_cols):
            header.setSectionResizeMode(col, QHeaderView.ResizeMode.ResizeToContents)
        total_req = sum(header.sectionSize(col) for col in range(n_cols))

        viewport_w = self.tableViewDados.viewport().width()

        # 2) Modo final: sempre Interactive
        for col in range(n_cols):
            header.setSectionResizeMode(col, QHeaderView.ResizeMode.Interactive)

        if total_req < viewport_w:
            # cabe tudo → distribui espaço extra proporcionalmente
            extra = viewport_w - total_req
            per_col = extra // n_cols
            for col in range(n_cols):
                new_w = header.sectionSize(col) + per_col
                header.resizeSection(col, new_w)
            # corrige eventuais pixels restantes no último
            sobr = viewport_w - sum(header.sectionSize(c) for c in range(n_cols))
            if sobr > 0:
                last = n_cols - 1
                header.resizeSection(last, header.sectionSize(last) + sobr)
        else:
            # não cabe → garante largura mínima do conteúdo
            for col in range(n_cols):
                # a sectionSize já foi definida no ResizeToContents
                # mas podemos reforçar chamando resizeSection
                w = header.sectionSize(col)
                header.resizeSection(col, w)

    def _atualizar_combos_xyz(self):
        """
        Popula comboBoxX, comboBoxY e comboBoxZ com colunas numéricas,
        impedindo que a mesma coluna seja usada mais de uma vez.

        Regras:
        - X e Y são obrigatórios.
        - Z é opcional e possui uma opção vazia.
        - Na primeira carga, procura automaticamente:
            X ou x para comboBoxX;
            Y ou y para comboBoxY;
            Z ou z para comboBoxZ.
        - Depois que o usuário retirar o Z, a seleção vazia será mantida.
        """
        model = self.tableViewDados.model()
        if model is None:
            return

        # Cabeçalhos das colunas completamente numéricas.
        numeric_headers = []

        for c in range(model.columnCount()):
            hdr = model.headerData(
                c,
                Qt.Orientation.Horizontal)

            ok = True

            for r in range(model.rowCount()):
                valor = model.index(r, c).data() or ""

                if valor == "":
                    continue

                if self._try_float(valor) is None:
                    ok = False
                    break

            if ok:
                numeric_headers.append(hdr)

        # Verifica se os combos já haviam sido preenchidos.
        z_ja_inicializado = self.comboBoxZ.count() > 0

        # Guarda as escolhas atuais.
        x_atual = self.comboBoxX.currentText()
        y_atual = self.comboBoxY.currentText()
        z_atual = self.comboBoxZ.currentText()

        sel = {
            "X": (
                x_atual
                if x_atual in numeric_headers
                else None),

            "Y": (
                y_atual
                if y_atual in numeric_headers
                else None),

            "Z": (
                z_atual
                if z_atual in numeric_headers
                else (
                    ""
                    if z_ja_inicializado and z_atual == ""
                    else None))}

        combos = [
            ("X", self.comboBoxX),
            ("Y", self.comboBoxY),
            ("Z", self.comboBoxZ)]

        usados = set()

        def encontrar_header(letra, disponiveis):
            """
            Procura X/x, Y/y ou Z/z sem diferenciar maiúsculas
            e minúsculas.
            """
            letra_lower = letra.lower()

            return next(
                (header
                    for header in disponiveis
                    if str(header).strip().lower() == letra_lower),
                None)

        for letra, combo in combos:
            combo.blockSignals(True)
            combo.clear()

            disponiveis = [
                header
                for header in numeric_headers
                if header not in usados]

            # Z sempre recebe uma opção vazia.
            if letra == "Z":
                combo.addItem("")

            # X e Y precisam ter alguma coluna disponível.
            if not disponiveis:
                if letra == "Z":
                    combo.setCurrentIndex(0)
                    combo.setEnabled(True)
                else:
                    combo.setEnabled(False)

                combo.blockSignals(False)
                continue

            escolha = None

            # Mantém uma seleção válida já realizada.
            if sel[letra] in disponiveis:
                escolha = sel[letra]

            # Para Z, mantém vazio quando o usuário retirou a coluna.
            elif letra == "Z" and sel["Z"] == "":
                escolha = ""

            else:
                # Na primeira carga, procura X/x, Y/y ou Z/z.
                escolha = encontrar_header(
                    letra,
                    disponiveis)

                # X e Y usam a primeira coluna disponível como fallback.
                if escolha is None and letra in ("X", "Y"):
                    escolha = disponiveis[0]

                # Para Z, se não existir Z/z, permanece vazio.
                if escolha is None and letra == "Z":
                    escolha = ""

            combo.addItems(
                [str(header) for header in disponiveis])

            if escolha:
                combo.setCurrentText(str(escolha))
                usados.add(escolha)
            else:
                combo.setCurrentIndex(0)

            combo.setEnabled(True)
            combo.blockSignals(False)

        self.textEdit_Erros.clear()

        # X e Y continuam obrigatórios.
        self._validar_coluna_xyz(self.comboBoxX)
        self._validar_coluna_xyz(self.comboBoxY)

        # Z somente será validado quando houver uma coluna selecionada.
        if self.comboBoxZ.currentText():
            self._validar_coluna_xyz(self.comboBoxZ)
        else:
            self.comboBoxZ.setStyleSheet("")

        self._validar_xy_por_crs()
        self._atualizar_estado_botao_adicionar()

    def _validar_coluna_xyz(self, combo: QComboBox) -> bool:
        """
        • Para X e Y: se houver células vazias, pinta o combo de vermelho
          e registra a mensagem.
        • Para Z: células vazias são aceitáveis (assumidas 0),
          portanto nunca gera erro por vazio.
        Retorna True se a coluna está OK, False se há erro.
        """
        model = self.tableViewDados.model()
        if model is None or model.columnCount() == 0:
            return True

        header_txt = combo.currentText()
        if not header_txt:
            combo.setStyleSheet("")
            return True

        # índice da coluna correspondente
        col = next(
            (c for c in range(model.columnCount())
             if model.headerData(c, Qt.Orientation.Horizontal) == header_txt),
            None)
        if col is None:
            combo.setStyleSheet("")
            return True

        # Verificação de vazios
        if combo is self.comboBoxZ:
            # Z aceita vazios -> não gera erro
            combo.setStyleSheet("")
            return True

        # X ou Y: vazios são erro
        vazias = [
            r + 2  # +2 para considerar a linha original da planilha
            for r in range(model.rowCount())
            if (model.index(r, col).data() or "").strip() == ""]

        if vazias:
            combo.setStyleSheet("QComboBox{background-color:#ffcccc;}")
            linhas = ", ".join(map(str, vazias))
            self._mostrar_erro(self.tr(f"Valores ausentes na coluna '{header_txt}' nas linhas: {linhas}"))
            return False

        combo.setStyleSheet("")
        return True

    def _selecionar_crs(self):
        """
        Abre o diálogo padrão de seleção de projeções do QGIS.
        Ao confirmar, o CRS escolhido é exibido no lineEdit_SRC.
        """
        dlg = QgsProjectionSelectionDialog(self)
        # inicializa com o SRC atual do projeto (opcional)
        dlg.setCrs(QgsProject.instance().crs())

        if dlg.exec():          # usuário clicou OK
            crs = dlg.crs()
            self.lineEdit_SRC.setText(f"{crs.authid()} - {crs.description()}")
            # (opcional) armazenar em atributo se precisar usar depois:
            self.selected_crs = crs

        self._validar_xy_por_crs()

        self._atualizar_estado_botao_adicionar()

    def _validar_xy_por_crs(self):
        """
        Valida X e Y conforme o CRS. Se houver qualquer valor fora dos
        limites, pinta os combos X/Y de vermelho e mostra mensagem única.
        """
        model = self.tableViewDados.model()
        if model is None:
            return

        # obtém CRS
        crs_text = self.lineEdit_SRC.text().split(" - ")[0].strip()
        crs = QgsCoordinateReferenceSystem(crs_text) if crs_text else None
        modo_geo = crs.isValid() and crs.isGeographic()
        modo_utm = crs.isValid() and self._crs_is_utm(crs)

        # helper de limite
        def fora_limites(v, eh_x):
            if modo_geo:
                return not (-180 <= v <= 180) if eh_x else not (-90 <= v <= 90)
            if modo_utm:
                return not (100000 <= v < 1000000) if eh_x else not (0 <= v <= 10000000)
            return False

        headers = {
            model.headerData(c, Qt.Orientation.Horizontal): c
            for c in range(model.columnCount())}

        qualquer_erro = False
        for cb, eh_x in ((self.comboBoxX, True), (self.comboBoxY, False)):
            cb.setStyleSheet("")  # reset
            hdr = cb.currentText()
            if hdr not in headers:
                continue
            col = headers[hdr]
            for r in range(model.rowCount()):
                txt = (model.index(r, col).data() or "").strip()
                if not txt:
                    continue
                v = self._try_float(txt)
                if v is None:
                    qualquer_erro = True
                    break

                if fora_limites(v, eh_x):
                    qualquer_erro = True
                    break
            if qualquer_erro:
                cb.setStyleSheet("QComboBox{background-color:#ffcccc;}")

        # mensagem única
        if qualquer_erro:
            self._mostrar_erro(self.tr("As coordenadas estão incoerentes na projeção selecionada"))
        else:
            # se antes havia mensagem, podemos limpar
            self.textEdit_Erros.clear()

        self._atualizar_estado_botao_adicionar()

    def _crs_is_utm(self, crs: QgsCoordinateReferenceSystem) -> bool:
        """
        Detecta UTM de forma robusta:
        - Preferência: projectionAcronym() == 'utm'
        - Fallback: faixas EPSG comuns de UTM (WGS84 e algumas do Brasil)
        """
        if not crs or not crs.isValid() or crs.isGeographic():
            return False

        # 1) melhor sinal: acrônimo da projeção
        try:
            acr = (crs.projectionAcronym() or "").strip().lower()
            if acr == "utm":
                return True
        except Exception:
            pass  # nosec B110

        # 2) fallback por EPSG
        try:
            auth = (crs.authid() or "").strip().upper()  # ex: "EPSG:32723"
            if auth.startswith("EPSG:"):
                code = int(auth.split(":")[1])

                # WGS84 / UTM
                if 32601 <= code <= 32660 or 32701 <= code <= 32760:
                    return True

                # Best-effort: faixas muito comuns em projetos no Brasil (SIRGAS/SAD/variações UTM)
                if 31960 <= code <= 31999 or 29160 <= code <= 29199:
                    return True
        except Exception:
            pass  # nosec B110

        return False

    def _guess_qgs_field(self, value) -> int:
        """
        Devolve o tipo de campo do QGIS (Int, Double ou String).
        """
        if isinstance(value, bool) or value in (None, ""):
            return QMetaType.Type.QString

        if isinstance(value, int) and not isinstance(value, bool):
            return QMetaType.Type.Int

        num = self._try_float(value)
        if num is None:
            return QMetaType.Type.QString

        # se for inteiro exato, pode virar Int
        if float(num).is_integer():
            return QMetaType.Type.Int

        return QMetaType.Type.Double

    def _guess_qgs_field_coluna(self, model, coluna: int):
        """
        Analisa todas as linhas de uma coluna para definir o tipo do campo.

        Regras:
        - Se existir qualquer texto não numérico, o campo será String.
        - Se todos os valores preenchidos forem números inteiros, será Int.
        - Se existir pelo menos um número decimal, será Double.
        - Células vazias são ignoradas.
        - Coluna completamente vazia será String.
        """
        encontrou_valor = False
        encontrou_decimal = False

        for linha in range(model.rowCount()):
            valor = model.index(linha, coluna).data()

            if valor is None:
                continue

            if isinstance(valor, str):
                valor = valor.strip()

            if valor == "":
                continue

            encontrou_valor = True

            # Valores booleanos não devem ser tratados como números.
            if isinstance(valor, bool):
                return QMetaType.Type.QString

            numero = self._try_float(valor)

            # Encontrou letra ou qualquer texto não numérico:
            # toda a coluna precisa ser String.
            if numero is None:
                return QMetaType.Type.QString

            # Se qualquer número tiver parte decimal, o campo será Double.
            if not float(numero).is_integer():
                encontrou_decimal = True

        if not encontrou_valor:
            return QMetaType.Type.QString

        if encontrou_decimal:
            return QMetaType.Type.Double

        return QMetaType.Type.Int


    def _adicionar_camada_pontos(self):
        """
        Constrói e adiciona ao projeto QGIS uma camada de pontos
        baseada no tableViewDados. Usa X/Y obrigatórios, Z opcional.
        """
        model = self.tableViewDados.model()

        if model is None or model.rowCount() == 0:
            self._mostrar_erro(self.tr("Tabela vazia - nada a adicionar."))
            return

        # Índices das colunas X, Y e Z
        headers = {
            model.headerData(c, Qt.Orientation.Horizontal): c
            for c in range(model.columnCount())}

        x_hdr = self.comboBoxX.currentText()
        y_hdr = self.comboBoxY.currentText()
        z_hdr = self.comboBoxZ.currentText() if self.comboBoxZ.currentText() else None

        if not x_hdr or not y_hdr:
            self._mostrar_erro(self.tr("Defina colunas para X e Y antes de adicionar."))
            return

        col_x = headers.get(x_hdr)
        col_y = headers.get(y_hdr)
        col_z = headers.get(z_hdr) if z_hdr else None

        # CRS
        crs_auth = self.lineEdit_SRC.text().split(" - ")[0].strip()

        crs = (
            QgsCoordinateReferenceSystem(crs_auth)
            if crs_auth
            else QgsProject.instance().crs())

        if not crs.isValid():
            crs = QgsProject.instance().crs()

        # Extrai nome da planilha selecionada
        texto = self.comboBox_Pasta.currentText().strip()

        if texto.startswith("(Excel)"):
            nome_layer = texto.replace("(Excel)", "", 1).strip()
        else:
            nome_layer = texto

        # Corrige nome da camada, caso venha com acento quebrado
        nome_layer = self._corrigir_texto_encoding(nome_layer)

        # Criar camada em memória com esse nome
        is_3d = col_z is not None
        wkb = QgsWkbTypes.Type.PointZ if is_3d else QgsWkbTypes.Type.Point

        layer = QgsVectorLayer(
            f"{QgsWkbTypes.displayString(wkb)}?crs={crs.authid()}",
            nome_layer,
            "memory")

        pr = layer.dataProvider()

        # Campos, todos os cabeçalhos da tabela
        fields = QgsFields()

        # Armazena o tipo detectado de cada coluna.
        tipos_campos = []

        for c in range(model.columnCount()):
            # Analisa todas as linhas da coluna, e não apenas a primeira.
            ftype = self._guess_qgs_field_coluna(model, c)
            tipos_campos.append(ftype)

            # Corrige o nome do campo antes de criar o QgsField.
            nome_campo = self._corrigir_texto_encoding(model.headerData(c, Qt.Orientation.Horizontal))

            fields.append(QgsField(nome_campo, ftype))

        pr.addAttributes(fields)
        layer.updateFields()

        # Adicionar feições
        feats = []

        for r in range(model.rowCount()):
            x = self._try_float(model.index(r, col_x).data() or "")
            y = self._try_float(model.index(r, col_y).data() or "")

            if x is None or y is None:
                continue

            f = QgsFeature(layer.fields())

            # Geometria 2D ou 3D
            if is_3d:
                z = self._try_float(model.index(r, col_z).data() or "")

                if z is None:
                    z = 0.0

                geom = QgsGeometry.fromPoint(
                    QgsPoint(float(x), float(y), float(z)))
            else:
                geom = QgsGeometry.fromPointXY(
                    QgsPointXY(float(x), float(y)))

            f.setGeometry(geom)

            # Atributos
            for c in range(model.columnCount()):
                valor_attr = model.index(r, c).data()
                tipo_campo = tipos_campos[c]

                if valor_attr is None:
                    valor_attr = None

                elif isinstance(valor_attr, str):
                    valor_attr = self._corrigir_texto_encoding(
                        valor_attr).strip()

                    if valor_attr == "":
                        valor_attr = None

                # Converte somente quando a coluna foi realmente
                # identificada como numérica.
                if valor_attr is not None:
                    if tipo_campo == QMetaType.Type.Int:
                        numero = self._try_float(valor_attr)

                        if numero is not None:
                            valor_attr = int(numero)

                    elif tipo_campo == QMetaType.Type.Double:
                        numero = self._try_float(valor_attr)

                        if numero is not None:
                            valor_attr = float(numero)

                    else:
                        # Campo String: preserva números, letras e códigos
                        # exatamente como texto.
                        valor_attr = str(valor_attr)

                f.setAttribute(c, valor_attr)

            feats.append(f)

        pr.addFeatures(feats)
        layer.updateExtents()

        # Adiciona ao projeto
        QgsProject.instance().addMapLayer(layer)

    def _atualizar_estado_botao_adicionar(self):
        """
        Atualiza o estado do botão Adicionar e a mensagem de validação.

        O botão será habilitado quando:
        - houver dados na tabela;
        - X e Y estiverem selecionados;
        - o SRC for válido;
        - não houver mensagem de erro.

        Z é opcional.
        """
        model = self.tableViewDados.model()

        mensagem_sucesso = self.tr(
            "Todos os parâmetros estão corretos. A camada pode ser adicionada.")

        # Verifica se existem dados.
        has_data = bool(
            model
            and model.rowCount() > 0
            and model.columnCount() > 0)

        # X e Y são obrigatórios.
        has_x = bool(self.comboBoxX.currentText().strip())
        has_y = bool(self.comboBoxY.currentText().strip())

        # Z não entra na validação porque é opcional.

        # Verifica o SRC.
        crs_texto = self.lineEdit_SRC.text().split(" - ")[0].strip()
        crs = QgsCoordinateReferenceSystem(crs_texto)

        has_crs = crs.isValid()

        # Lê a mensagem atual.
        texto_atual = self.textEdit_Erros.toPlainText().strip()

        # A mensagem verde não deve ser interpretada como erro.
        has_error = bool(
            texto_atual
            and texto_atual != mensagem_sucesso)

        pronto = (
            has_data
            and has_x
            and has_y
            and has_crs
            and not has_error)

        self.pushButtonAdicionar.setEnabled(pronto)

        if pronto:
            self.textEdit_Erros.clear()
            self.textEdit_Erros.setTextColor(
                Qt.GlobalColor.darkGreen)

            self.textEdit_Erros.append(
                mensagem_sucesso)

            self.textEdit_Erros.setStyleSheet("""
                QTextEdit {
                    color: #167c2f;
                    background-color: #e9f7ed;
                    border: 1px solid #49a963;
                    border-radius: 3px;
                }
            """)

        elif texto_atual == mensagem_sucesso:
            # Remove a mensagem verde quando algum parâmetro deixa
            # de estar válido.
            self.textEdit_Erros.clear()
            self.textEdit_Erros.setStyleSheet("")

