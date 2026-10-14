# -*- coding: utf-8 -*-
from qgis.PyQt.QtCore import QByteArray, QUrl, QSettings, Qt
from qgis.PyQt.QtWidgets import (QDialog, QVBoxLayout, QHBoxLayout, QGroupBox, QRadioButton, QLabel, QLineEdit, QTextEdit, QPushButton, QMessageBox, QFrame)
from qgis.core import QgsNetworkAccessManager, Qgis
from qgis.PyQt.QtNetwork import QNetworkRequest
from datetime import datetime, timedelta
import platform
import json
import uuid

APP_SCRIPT_ENDPOINT = "https://script.google.com/macros/s/AKfycbzdT1u_2h24zHjFLhHMPtIKgvV6ZBOA8Wnp2u1kZWNLU3NyYAHardUm5R-EgHsUugMT/exec"

INTERVALO_MINIMO_ENVIO_HORAS = 24

# Chave onde ficará salvo o último envio no QSettings do QGIS.
CHAVE_ULTIMO_ENVIO = "TempoSalvoTools/Contato/ultimo_envio"

class DialogoContatoFormSubmit(QDialog):
    def __init__(self, iface=None, parent=None):
        super().__init__(parent)

        self.iface = iface
        self.manager = QgsNetworkAccessManager.instance()
        self.reply = None
        self.idioma = "pt"
        self.settings = QSettings()

        self.setWindowTitle("Contato / Suporte")
        self.resize(520, 430)

        self._montar_interface()
        self._atualizar_textos()

    def _montar_interface(self):
        layout_principal = QVBoxLayout(self)

        self.labelTitulo = QLabel()
        self.labelTitulo.setWordWrap(True)
        layout_principal.addWidget(self.labelTitulo)

        grupo_idioma = QGroupBox("Idioma / Language / Idioma")
        layout_idioma = QHBoxLayout(grupo_idioma)

        self.radioPortugues = QRadioButton("Português")
        self.radioEnglish = QRadioButton("English")
        self.radioEspanol = QRadioButton("Español")

        self.radioPortugues.setChecked(True)

        layout_idioma.addWidget(self.radioPortugues)
        layout_idioma.addWidget(self.radioEnglish)
        layout_idioma.addWidget(self.radioEspanol)

        layout_principal.addWidget(grupo_idioma)

        self.radioPortugues.toggled.connect(
            lambda checked: checked and self._alterar_idioma("pt")
        )
        self.radioEnglish.toggled.connect(
            lambda checked: checked and self._alterar_idioma("en")
        )
        self.radioEspanol.toggled.connect(
            lambda checked: checked and self._alterar_idioma("es")
        )

        self.frameMensagem = QFrame()
        self.frameMensagem.setObjectName("frameMensagem")
        self.frameMensagem.setStyleSheet("""
            QFrame#frameMensagem {
                border: 1px solid #b8b8b8;
                border-radius: 3px;
                background-color: #f5f5f5;
            }

            QFrame#frameMensagem QLabel {
                border: none;
                background: transparent;
                font-weight: bold;
            }

            QFrame#frameMensagem QLabel#labelTextoOrientacao {
                font-weight: normal;
                color: #333333;
                background-color: #ffffff;
                border: 1px solid #d0d0d0;
                border-radius: 3px;
                padding: 8px;
            }

            QFrame#frameMensagem QLineEdit,
            QFrame#frameMensagem QTextEdit {
                background-color: white;
            }
        """)

        layout_frame_mensagem = QVBoxLayout(self.frameMensagem)
        layout_frame_mensagem.setContentsMargins(8, 8, 8, 8)
        layout_frame_mensagem.setSpacing(6)

        self.labelTextoOrientacao = QLabel()
        self.labelTextoOrientacao.setObjectName("labelTextoOrientacao")
        self.labelTextoOrientacao.setWordWrap(True)
        self.labelTextoOrientacao.setMinimumHeight(48)

        self.labelTextoOrientacao.setTextFormat(Qt.TextFormat.RichText)
        self.labelTextoOrientacao.setTextInteractionFlags(
            Qt.TextInteractionFlag.TextSelectableByMouse |
            Qt.TextInteractionFlag.TextSelectableByKeyboard
        )

        layout_frame_mensagem.addWidget(self.labelTextoOrientacao)

        self.labelNome = QLabel()
        self.lineEditNome = QLineEdit()

        self.labelEmail = QLabel()
        self.lineEditEmail = QLineEdit()

        self.labelMensagem = QLabel()
        self.textEditMensagem = QTextEdit()
        self.textEditMensagem.setMinimumHeight(150)

        layout_frame_mensagem.addWidget(self.labelNome)
        layout_frame_mensagem.addWidget(self.lineEditNome)

        layout_frame_mensagem.addWidget(self.labelEmail)
        layout_frame_mensagem.addWidget(self.lineEditEmail)

        layout_frame_mensagem.addWidget(self.labelMensagem)
        layout_frame_mensagem.addWidget(self.textEditMensagem)

        layout_principal.addWidget(self.frameMensagem)

        self.labelAppsScript = QLabel("Google Apps Script")
        self.labelAppsScript.setStyleSheet(
            "font-weight: bold; margin-top: 8px;")
        layout_principal.addWidget(self.labelAppsScript)

        self.labelInfoAppsScript = QLabel()
        self.labelInfoAppsScript.setWordWrap(True)
        layout_principal.addWidget(self.labelInfoAppsScript)

        layout_botoes = QHBoxLayout()

        self.pushButtonEnviar = QPushButton()
        self.pushButtonCancelar = QPushButton()

        layout_botoes.addStretch()
        layout_botoes.addWidget(self.pushButtonEnviar)
        layout_botoes.addWidget(self.pushButtonCancelar)

        layout_principal.addLayout(layout_botoes)

        self.pushButtonEnviar.clicked.connect(self.enviar_mensagem)
        self.pushButtonCancelar.clicked.connect(self.reject)

    def _alterar_idioma(self, idioma):
        self.idioma = idioma
        self._atualizar_textos()

    def _atualizar_textos(self):
        textos = {
            "pt": {
                "titulo": "Envie uma mensagem ao criador do Plugin Tempo Salvo Tools.",
                "nome": "Nome:",
                "email": "E-mail para resposta:",
                "mensagem": "Mensagem:",
                "placeholder_nome": "Digite seu nome",
                "placeholder_email": "Digite seu e-mail",
                "placeholder_mensagem": "Descreva sua dúvida, erro ou sugestão...",
                "info_apps_script": "A mensagem será enviada usando o sistema Google Apps Script.",
                "tooltip_envio": (
                    "Informações enviadas:\n"
                    "- Nome informado\n"
                    "- E-mail para resposta\n"
                    "- Mensagem digitada\n"
                    "- Idioma selecionado\n"
                    "- Origem: Tempo Salvo Tools\n"
                    "- Versão do QGIS\n"
                    "- Sistema operacional\n"
                    "- ID do Plugin\n"
                    "- Data e hora do envio"
                ),
                "enviar": "Enviar mensagem",
                "cancelar": "Cancelar",
                "enviando": "Enviando...",
                "orientacao": (
                    "<b>Use este espaço para enviar dúvidas, sugestões ou relatar possíveis erros "
                    "encontrados durante o uso do plugin.</b><br>"
                    "<b>Limite:</b> (1 mensagem por usuário a cada 24 horas, com limite total de "
                    "50 mensagens por dia).<br><br>"
                    "O plugin está com uma avaliação muito baixa, mas não entendo exatamente a razão, "
                    "pois não recebo feedback indicando o que precisa ser melhorado ou corrigido. "
                    "Por favor, envie uma mensagem com suas observações, sugestões ou relatos de problemas. "
                    "Sua contribuição pode ajudar muito a melhorar o plugin."
                ),
            },
            "en": {
                "titulo": "Send a message to the creator of the Tempo Salvo Tools plugin.",
                "nome": "Name:",
                "email": "Reply e-mail:",
                "mensagem": "Message:",
                "placeholder_nome": "Enter your name",
                "placeholder_email": "Enter your e-mail",
                "placeholder_mensagem": "Describe your question, error or suggestion...",
                "info_apps_script": "The message will be sent using the Google Apps Script system.",
                "tooltip_envio": (
                    "Information sent:\n"
                    "- Provided name\n"
                    "- Reply e-mail\n"
                    "- Typed message\n"
                    "- Selected language\n"
                    "- Source: Tempo Salvo Tools\n"
                    "- QGIS version\n"
                    "- Operating system\n"
                    "- Plugin ID\n"
                    "- Date and time of submission"
                ),
                "enviar": "Send message",
                "cancelar": "Cancel",
                "enviando": "Sending...",
                "orientacao": (
                    "<b>Use this space to send questions, suggestions, or report possible errors "
                    "found while using the plugin.</b><br>"
                    "<b>Limit:</b> (1 message per user every 24 hours, with a total limit of "
                    "50 messages per day).<br><br>"
                    "The plugin currently has a very low rating, but I do not fully understand the reason, "
                    "as I do not receive feedback indicating what needs to be improved or corrected. "
                    "Please send a message with your observations, suggestions, or problem reports. "
                    "Your contribution can greatly help improve the plugin."
                ),
            },
            "es": {
                "titulo": "Envíe un mensaje al creador del plugin Tempo Salvo Tools.",
                "nome": "Nombre:",
                "email": "Correo para respuesta:",
                "mensagem": "Mensaje:",
                "placeholder_nome": "Escriba su nombre",
                "placeholder_email": "Escriba su correo",
                "placeholder_mensagem": "Describa su duda, error o sugerencia...",
                "info_apps_script": "El mensaje será enviado usando el sistema de Google Apps Script.",
                "tooltip_envio": (
                    "Información enviada:\n"
                    "- Nombre informado\n"
                    "- Correo para respuesta\n"
                    "- Mensaje escrito\n"
                    "- Idioma seleccionado\n"
                    "- Origen: Tempo Salvo Tools\n"
                    "- Versión de QGIS\n"
                    "- Sistema operativo\n"
                    "- ID del plugin\n"
                    "- Fecha y hora del envío"
                ),
                "enviar": "Enviar mensaje",
                "cancelar": "Cancelar",
                "enviando": "Enviando...",
                "orientacao": (
                    "<b>Use este espacio para enviar dudas, sugerencias o informar posibles errores "
                    "encontrados durante el uso del plugin.</b><br>"
                    "<b>Límite:</b> (1 mensaje por usuario cada 24 horas, con un límite total de "
                    "50 mensajes por día).<br><br>"
                    "El plugin actualmente tiene una valoración muy baja, pero no entiendo exactamente la razón, "
                    "ya que no recibo comentarios que indiquen qué debe mejorarse o corregirse. "
                    "Por favor, envíe un mensaje con sus observaciones, sugerencias o reportes de problemas. "
                    "Su contribución puede ayudar mucho a mejorar el plugin."
                ),
            },
        }

        t = textos[self.idioma]

        self.labelTitulo.setText(t["titulo"])
        self.labelTextoOrientacao.setText(t["orientacao"])
        self.labelNome.setText(t["nome"])
        self.labelEmail.setText(t["email"])
        self.labelMensagem.setText(t["mensagem"])
        self.labelInfoAppsScript.setText(t["info_apps_script"])

        # self.labelAppsScript.setToolTip(t["tooltip_envio"])
        self.labelInfoAppsScript.setToolTip(t["tooltip_envio"])
        # self.pushButtonEnviar.setToolTip(t["tooltip_envio"])

        self.lineEditNome.setPlaceholderText(t["placeholder_nome"])
        self.lineEditEmail.setPlaceholderText(t["placeholder_email"])
        self.textEditMensagem.setPlaceholderText(t["placeholder_mensagem"])

        self.pushButtonEnviar.setText(t["enviar"])
        self.pushButtonCancelar.setText(t["cancelar"])

    def _texto_idioma(self):
        if self.idioma == "en":
            return "English"
        if self.idioma == "es":
            return "Español"
        return "Português"

    def _qgis_version(self):
        try:
            return Qgis.QGIS_VERSION
        except Exception:
            return "Não identificado"

    def _tr(self, chave, **kwargs):
        """
        Retorna textos traduzidos conforme o idioma selecionado no diálogo.
        """
        textos = {
            "pt": {
                "titulo_campos_obrigatorios": "Campos obrigatórios",
                "msg_campos_obrigatorios": "Preencha nome, e-mail e mensagem antes de enviar.",

                "titulo_email_invalido": "E-mail inválido",
                "msg_email_invalido": "Informe um e-mail válido para resposta.",

                "titulo_apps_script_nao_configurado": "Google Apps Script não configurado",
                "msg_apps_script_nao_configurado": "Configure a URL do Google Apps Script no arquivo DialogoContatoFormSubmit.py.",

                "titulo_token_nao_configurado": "Token não configurado",  # nosec B105
                "msg_token_nao_configurado": "Configure o APP_SCRIPT_TOKEN no arquivo DialogoContatoFormSubmit.py.",  # nosec B105

                "titulo_erro_envio": "Erro no envio",
                "msg_erro_rede": "Não foi possível enviar a mensagem.\n\nErro: {erro}",

                "titulo_limite_diario": "Limite diário atingido",
                "msg_limite_diario": "O limite diário de mensagens foi atingido. Tente enviar novamente amanhã.",

                "titulo_envio_nao_confirmado": "Envio não confirmado",
                "msg_envio_nao_confirmado": (
                    "O servidor respondeu, mas não confirmou o envio da mensagem.\n\n"
                    "Status HTTP: {status_http}\n\n"
                    "Resposta:\n{mensagem}"
                ),

                "msg_mail_send_error": "Não foi possível enviar a mensagem neste momento. Tente novamente mais tarde.",
                "msg_busy": "O servidor está ocupado no momento. Tente novamente em instantes.",
                "msg_unauthorized": "Requisição não autorizada.",
                "msg_missing_fields": "Nome, e-mail e mensagem são obrigatórios.",
                "msg_invalid_email": "E-mail inválido.",
                "msg_wait_base": "Você já enviou uma mensagem recentemente. Aguarde antes de enviar outra.",
                "msg_wait": "{mensagem}\n\nAguarde aproximadamente {tempo}.",

                "titulo_mensagem_enviada": "Mensagem enviada",
                "msg_mensagem_enviada": "Mensagem enviada com sucesso.",
            },

            "en": {
                "titulo_campos_obrigatorios": "Required fields",
                "msg_campos_obrigatorios": "Please fill in your name, e-mail, and message before sending.",

                "titulo_email_invalido": "Invalid e-mail",
                "msg_email_invalido": "Please enter a valid reply e-mail address.",

                "titulo_apps_script_nao_configurado": "Google Apps Script not configured",
                "msg_apps_script_nao_configurado": "Configure the Google Apps Script URL in the DialogoContatoFormSubmit.py file.",

                "titulo_token_nao_configurado": "Token not configured",  # nosec B105
                "msg_token_nao_configurado": "Configure APP_SCRIPT_TOKEN in the DialogoContatoFormSubmit.py file.",  # nosec B105

                "titulo_erro_envio": "Sending error",
                "msg_erro_rede": "The message could not be sent.\n\nError: {erro}",

                "titulo_limite_diario": "Daily limit reached",
                "msg_limite_diario": "The daily message limit has been reached. Please try again tomorrow.",

                "titulo_envio_nao_confirmado": "Sending not confirmed",
                "msg_envio_nao_confirmado": (
                    "The server responded, but did not confirm that the message was sent.\n\n"
                    "HTTP status: {status_http}\n\n"
                    "Response:\n{mensagem}"
                ),

                "msg_mail_send_error": "The message could not be sent at this moment. Please try again later.",
                "msg_busy": "The server is busy at the moment. Please try again shortly.",
                "msg_unauthorized": "Unauthorized request.",
                "msg_missing_fields": "Name, e-mail, and message are required.",
                "msg_invalid_email": "Invalid e-mail address.",
                "msg_wait_base": "You have already sent a message recently. Please wait before sending another one.",
                "msg_wait": "{mensagem}\n\nPlease wait approximately {tempo}.",

                "titulo_mensagem_enviada": "Message sent",
                "msg_mensagem_enviada": "Message sent successfully.",
            },

            "es": {
                "titulo_campos_obrigatorios": "Campos obligatorios",
                "msg_campos_obrigatorios": "Complete nombre, correo y mensaje antes de enviar.",

                "titulo_email_invalido": "Correo inválido",
                "msg_email_invalido": "Informe un correo válido para la respuesta.",

                "titulo_apps_script_nao_configurado": "Google Apps Script no configurado",
                "msg_apps_script_nao_configurado": "Configure la URL de Google Apps Script en el archivo DialogoContatoFormSubmit.py.",

                "titulo_token_nao_configurado": "Token no configurado",  # nosec B105
                "msg_token_nao_configurado": "Configure APP_SCRIPT_TOKEN en el archivo DialogoContatoFormSubmit.py.",  # nosec B105

                "titulo_erro_envio": "Error de envío",
                "msg_erro_rede": "No fue posible enviar el mensaje.\n\nError: {erro}",

                "titulo_limite_diario": "Límite diario alcanzado",
                "msg_limite_diario": "Se alcanzó el límite diario de mensajes. Intente enviarlo nuevamente mañana.",

                "titulo_envio_nao_confirmado": "Envío no confirmado",
                "msg_envio_nao_confirmado": (
                    "El servidor respondió, pero no confirmó el envío del mensaje.\n\n"
                    "Estado HTTP: {status_http}\n\n"
                    "Respuesta:\n{mensagem}"
                ),

                "msg_mail_send_error": "No fue posible enviar el mensaje en este momento. Inténtelo nuevamente más tarde.",
                "msg_busy": "El servidor está ocupado en este momento. Inténtelo nuevamente en unos instantes.",
                "msg_unauthorized": "Solicitud no autorizada.",
                "msg_missing_fields": "Nombre, correo y mensaje son obligatorios.",
                "msg_invalid_email": "Correo inválido.",
                "msg_wait_base": "Ya ha enviado un mensaje recientemente. Espere antes de enviar otro.",
                "msg_wait": "{mensagem}\n\nEspere aproximadamente {tempo}.",

                "titulo_mensagem_enviada": "Mensaje enviado",
                "msg_mensagem_enviada": "Mensaje enviado correctamente.",
            },
        }

        idioma = self.idioma if self.idioma in textos else "pt"
        texto = textos[idioma].get(chave, textos["pt"].get(chave, chave))

        try:
            return texto.format(**kwargs)
        except Exception:
            return texto

    def _validar_campos(self):
        nome = self.lineEditNome.text().strip()
        email = self.lineEditEmail.text().strip()
        mensagem = self.textEditMensagem.toPlainText().strip()

        if not nome or not email or not mensagem:
            QMessageBox.warning(
                self,
                self._tr("titulo_campos_obrigatorios"),
                self._tr("msg_campos_obrigatorios"))
            return False

        if "@" not in email or "." not in email:
            QMessageBox.warning(
                self,
                self._tr("titulo_email_invalido"),
                self._tr("msg_email_invalido"))
            return False

        if not APP_SCRIPT_ENDPOINT or "COLE_AQUI" in APP_SCRIPT_ENDPOINT:
            QMessageBox.warning(
                self,
                self._tr("titulo_apps_script_nao_configurado"),
                self._tr("msg_apps_script_nao_configurado"))
            return False

        return True

    def _client_id(self):
        """
        Cria e mantém um identificador local simples para ajudar no controle antispam.
        Não é uma proteção absoluta, mas ajuda a reduzir envios repetidos comuns.
        """
        chave = "TempoSalvoTools/Contato/client_id"
        valor = self.settings.value(chave, "", type=str)

        if not valor:
            valor = str(uuid.uuid4())
            self.settings.setValue(chave, valor)

        return valor

    def _montar_dados_envio(self):
        nome = self.lineEditNome.text().strip()
        email = self.lineEditEmail.text().strip()
        mensagem = self.textEditMensagem.toPlainText().strip()

        return {
            "client_id": self._client_id(),
            "nome": nome,
            "email": email,
            "mensagem": mensagem,
            "idioma": self._texto_idioma(),
            "origem": "Tempo Salvo Tools",
            "qgis": self._qgis_version(),
            "sistema": platform.platform(),
            "data_hora": datetime.now().strftime("%Y-%m-%d %H:%M:%S")}

    def _ultimo_envio(self):
        """
        Retorna a data/hora do último envio salvo no QSettings.
        """
        valor = self.settings.value(CHAVE_ULTIMO_ENVIO, "", type=str)

        if not valor:
            return None

        try:
            return datetime.fromisoformat(valor)
        except Exception:
            return None

    def _tempo_restante_bloqueio(self):
        """
        Retorna o tempo restante de bloqueio, ou None se já puder enviar.
        """
        ultimo = self._ultimo_envio()

        if ultimo is None:
            return None

        proximo_envio = ultimo + timedelta(hours=INTERVALO_MINIMO_ENVIO_HORAS)
        restante = proximo_envio - datetime.now()

        if restante.total_seconds() <= 0:
            return None

        return restante

    def _formatar_tempo_restante(self, restante):
        """
        Formata o tempo restante em texto simples.
        """
        total_segundos = max(0, int(restante.total_seconds()))
        horas = total_segundos // 3600
        minutos = (total_segundos % 3600) // 60

        if horas > 0 and minutos > 0:
            return f"{horas} h e {minutos} min"

        if horas > 0:
            return f"{horas} h"

        minutos = max(1, minutos)
        return f"{minutos} min"

    def _mensagem_bloqueio_envio(self):
        """
        Mensagem exibida quando o usuário tenta enviar novamente rápido demais.
        """
        restante = self._tempo_restante_bloqueio()
        tempo = self._formatar_tempo_restante(restante) if restante else ""

        if self.idioma == "en":
            return (
                "You have already sent a message recently.\n\n"
                f"Please wait approximately {tempo} before sending another message. "
                "This helps avoid repeated submissions and keeps support organized."
            )

        if self.idioma == "es":
            return (
                "Ya ha enviado un mensaje recientemente.\n\n"
                f"Espere aproximadamente {tempo} antes de enviar otro mensaje. "
                "Esto ayuda a evitar envíos repetidos y mantiene el soporte organizado."
            )

        return (
            "Você já enviou uma mensagem recentemente.\n\n"
            f"Aguarde aproximadamente {tempo} antes de enviar outra mensagem. "
            "Isso evita envios repetidos e ajuda a manter o suporte organizado."
        )

    def _titulo_bloqueio_envio(self):
        if self.idioma == "en":
            return "Message already sent"

        if self.idioma == "es":
            return "Mensaje ya enviado"

        return "Mensagem já enviada"

    def _registrar_envio_com_sucesso(self):
        """
        Salva o momento do envio apenas quando o servidor responde com sucesso.
        """
        agora = datetime.now().isoformat(timespec="seconds")
        self.settings.setValue(CHAVE_ULTIMO_ENVIO, agora)

    def enviar_mensagem(self):
        if self._tempo_restante_bloqueio() is not None:
            QMessageBox.information(
                self,
                self._titulo_bloqueio_envio(),
                self._mensagem_bloqueio_envio())
            return

        if not self._validar_campos():
            return

        dados = self._montar_dados_envio()

        request = QNetworkRequest(QUrl(APP_SCRIPT_ENDPOINT))

        content_type_header = getattr(QNetworkRequest, "ContentTypeHeader", None)
        if content_type_header is None:
            content_type_header = QNetworkRequest.KnownHeaders.ContentTypeHeader

        request.setHeader(
            content_type_header,
            "application/json"
        )

        request.setRawHeader(
            QByteArray(b"Accept"),
            QByteArray(b"application/json")
        )

        try:
            request.setAttribute(
                QNetworkRequest.Attribute.RedirectPolicyAttribute,
                QNetworkRequest.RedirectPolicy.NoLessSafeRedirectPolicy
            )
        except Exception:
            pass  # nosec B110

        payload = QByteArray(
            json.dumps(dados, ensure_ascii=False).encode("utf-8")
        )

        self.pushButtonEnviar.setEnabled(False)
        self.pushButtonEnviar.setText(
            {
                "pt": "Enviando...",
                "en": "Sending...",
                "es": "Enviando...",
            }.get(self.idioma, "Enviando..."))

        self.reply = self.manager.post(request, payload)
        self.reply.finished.connect(self._finalizar_envio)

    def _erro_reply(self):
        erro = self.reply.error()

        try:
            return int(erro)
        except TypeError:
            return erro.value

    def _finalizar_envio(self):
        self.pushButtonEnviar.setEnabled(True)
        self._atualizar_textos()

        status_http = self.reply.attribute(
            QNetworkRequest.Attribute.HttpStatusCodeAttribute
        )

        resposta_texto = bytes(
            self.reply.readAll()
        ).decode("utf-8", errors="ignore").strip()

        if self._erro_reply() != 0:
            erro = self.reply.errorString()
            self.reply.deleteLater()
            self.reply = None

            QMessageBox.critical(
                self,
                self._tr("titulo_erro_envio"),
                self._tr("msg_erro_rede", erro=erro)
            )
            return

        self.reply.deleteLater()
        self.reply = None

        try:
            dados_resposta = json.loads(resposta_texto) if resposta_texto else {}
        except Exception:
            dados_resposta = {}

        ok = bool(dados_resposta.get("ok"))
        codigo = str(dados_resposta.get("code", "")).lower()
        mensagem_servidor = str(dados_resposta.get("message", "")).strip()

        if codigo == "wait":
            segundos = int(dados_resposta.get("remaining_seconds", 0) or 0)
            tempo = self._formatar_tempo_restante(timedelta(seconds=segundos))

            QMessageBox.information(
                self,
                self._titulo_bloqueio_envio(),
                self._tr(
                    "msg_wait",
                    mensagem=self._tr("msg_wait_base"),
                    tempo=tempo
                )
            )
            return

        if codigo == "daily_quota_exceeded" or codigo == "daily_limit_exceeded":
            QMessageBox.warning(
                self,
                self._tr("titulo_limite_diario"),
                self._tr("msg_limite_diario")
            )
            return

        if codigo == "mail_send_error":
            QMessageBox.warning(
                self,
                self._tr("titulo_erro_envio"),
                self._tr("msg_mail_send_error")
            )
            return

        if codigo == "busy":
            QMessageBox.warning(
                self,
                self._tr("titulo_erro_envio"),
                self._tr("msg_busy")
            )
            return

        if codigo == "unauthorized":
            QMessageBox.warning(
                self,
                self._tr("titulo_erro_envio"),
                self._tr("msg_unauthorized")
            )
            return

        if codigo == "missing_fields":
            QMessageBox.warning(
                self,
                self._tr("titulo_campos_obrigatorios"),
                self._tr("msg_missing_fields")
            )
            return

        if codigo == "invalid_email":
            QMessageBox.warning(
                self,
                self._tr("titulo_email_invalido"),
                self._tr("msg_invalid_email")
            )
            return

        if not mensagem_servidor:
            mensagem_servidor = resposta_texto or "Sem mensagem de retorno."

        if not ok:
            QMessageBox.warning(
                self,
                self._tr("titulo_envio_nao_confirmado"),
                self._tr(
                    "msg_envio_nao_confirmado",
                    status_http=status_http,
                    mensagem=mensagem_servidor
                )
            )
            return

        self._registrar_envio_com_sucesso()

        QMessageBox.information(
            self,
            self._tr("titulo_mensagem_enviada"),
            self._tr("msg_mensagem_enviada")
        )

        self.accept()