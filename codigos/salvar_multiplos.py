from qgis.PyQt.QtWidgets import QDialog, QCheckBox, QDialogButtonBox, QGridLayout
from qgis.PyQt.QtCore import QCoreApplication

class DialogoSalvarFormatos(QDialog):
    """
    DialogoSalvarFormatos cria uma interface de usuário com checkboxes para seleção de formatos de arquivo.
    Ele permite ao usuário escolher um ou mais formatos de arquivo para operações de salvamento.
    """
    def __init__(self, formatos, parent=None):
        """
        Inicializa o diálogo com checkboxes para cada formato disponível e botões OK e Cancelar.
        """
        super(DialogoSalvarFormatos, self).__init__(parent)
        self.setWindowTitle(self.tr("Escolha o(s) Formato(s)"))  # Define o título do diálogo
        self.formatos = formatos  # Dicionário de formatos disponíveis
        self.formatos_selecionados = []  # Lista para armazenar formatos selecionados

        # Layout para caixas de seleção em grade
        grid_layout = QGridLayout(self)  # Cria um layout de grade para o diálogo

        # Caixas de seleção para formatos
        self.caixas_de_selecao = {}  # Dicionário para armazenar as checkboxes
        formatos_keys = list(formatos.keys())  # Lista de chaves de formatos
        for i, formato in enumerate(formatos_keys):
            caixa = QCheckBox(formato, self)  # Cria checkbox para o formato
            grid_layout.addWidget(caixa, i % 4, i // 4)  # Adiciona checkbox à grade
            self.caixas_de_selecao[formato] = caixa  # Armazena checkbox no dicionário
            caixa.stateChanged.connect(self.verificar_selecoes)  # Conecta sinal de alteração

        # Botões OK e Cancelar
        self.botoes = QDialogButtonBox(QDialogButtonBox.StandardButton.Ok | QDialogButtonBox.StandardButton.Cancel, self)  # Cria botões OK e Cancelar
        grid_layout.addWidget(self.botoes, 4, 0, 1, 2)  # Adiciona botões ao layout de grade
        self.botoes.accepted.connect(self.accept)  # Conecta o botão OK a função accept
        self.botoes.rejected.connect(self.reject)  # Conecta o botão Cancelar a função reject

        self.botoes.button(QDialogButtonBox.StandardButton.Ok).setEnabled(False)  # Desativa o botão OK inicialmente

    def tr(self, message):
        """
        Traduz textos deste diálogo.
        O contexto precisa ser estável para o Qt Linguist encontrar as traduções.
        """
        return QCoreApplication.translate("DialogoSalvarFormatos", message)

    def verificar_selecoes(self):
        """
        Habilita o botão OK se pelo menos uma caixa de seleção estiver marcada.
        """
        algum_selecionado = any(caixa.isChecked() for caixa in self.caixas_de_selecao.values())  # Verifica se alguma caixa está marcada
        self.botoes.button(QDialogButtonBox.StandardButton.Ok).setEnabled(algum_selecionado)  # Habilita ou desabilita o botão OK

    def accept(self):
        """
        Armazena os formatos selecionados e fecha o diálogo com um estado de "aceito".
        """
        for formato, caixa in self.caixas_de_selecao.items():
            if caixa.isChecked():  # Se a caixa de seleção estiver marcada
                self.formatos_selecionados.append(self.formatos[formato])  # Adiciona o formato à lista de selecionados
        super(DialogoSalvarFormatos, self).accept()  # Chama a implementação padrão para fechar o diálogo