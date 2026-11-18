#!/usr/bin/env python3
"""
Mail Diagnostics - DNS, Telnet (SMTP), TLS/OpenSSL y Ping en una sola herramienta.

Requisitos:
    Python 3.9+ con Tkinter 8.6
    pip install --require-hashes -r requirements.txt   (solo dnspython 2.7.0)

Privacidad (ver SEGURIDAD.md):
  * Sin telemetría, sin actualizaciones automáticas, sin servicios de terceros.
  * La app solo se conecta a lo que el usuario escribe: consultas DNS (al resolvedor
    del sistema), conexiones SMTP a los hosts y puertos elegidos, y ping.
  * El EHLO usa la IP local entre corchetes, no el nombre del equipo.
  * Ni la ventana, ni el log, ni el PDF incluyen el nombre del equipo que hizo la prueba.
  * Las credenciales solo se envían dentro de TLS con certificado verificado.
  * El PDF se genera con código propio (sin librerías externas) y sin metadatos.

Notas:
  * La prueba "Telnet" se hace con sockets nativos (telnetlib ya no existe en Python 3.13+).
    Es exactamente lo mismo que `telnet host puerto` + EHLO + QUIT.
  * La prueba "OpenSSL" usa el módulo ssl de Python (la misma librería OpenSSL que usa
    `openssl s_client`), así que no necesitas tener el binario openssl instalado.
    En el log se muestra el comando openssl equivalente por si quieres repetirlo a mano.
  * El usuario y la contraseña se codifican en Base64 (AUTH PLAIN / AUTH LOGIN) como exige
    SMTP. Base64 NO es cifrado: lo que protege las credenciales es el túnel TLS, por eso
    solo se envían después del handshake TLS. Nunca se muestran ni se guardan en el PDF.
  * Cada línea del log se guarda en español y en inglés; "Copiar log" pregunta el idioma.
  * Funciona desde el código fuente (con los launchers) o compilado con PyInstaller para
    macOS, Windows y Linux. Compilado, Python y dnspython van dentro del ejecutable; en el
    primer arranque la app revisa sus componentes y solo pide permiso si falta `ping`.
"""

import base64
import ipaddress
import os
import platform
import queue
import re
import shutil
import socket
import ssl
import subprocess
import sys
import tempfile
import threading
import time
from datetime import datetime, timezone

import tkinter as tk
from tkinter import ttk, messagebox, filedialog, simpledialog
import tkinter.font as tkfont

try:
    import dns.exception
    import dns.resolver
except ImportError:
    # Se abrió el script directamente, sin el launcher que instala la dependencia.
    _root = tk.Tk()
    _root.withdraw()
    messagebox.showerror("Mail Diagnostics",
                         "Falta el componente dnspython.\n\n"
                         "Abre la aplicación con su launcher: revisará los componentes "
                         "y te pedirá permiso antes de instalar lo que falte.")
    sys.exit(1)

APP_TITLE = "Mail Diagnostics"
APP_VERSION = "2.2"
IS_WINDOWS = platform.system().lower() == "windows"

# ---------------------------------------------------------------- Paleta ----
C = {
    "bg": "#0d1117",
    "panel": "#161b22",
    "card": "#1c2128",
    "input": "#22272e",
    "border": "#30363d",
    "log": "#0a0d12",
    "text": "#e6edf3",
    "muted": "#8b949e",
    "accent": "#2f81f7",
    "accent_h": "#4c94f8",
    "ok": "#3fb950",
    "err": "#f85149",
    "warn": "#d29922",
    "info": "#58a6ff",
    "head": "#bc8cff",
    "client": "#79c0ff",
    "server": "#a5b1bd",
}

PDF_COLORS = {
    "header": (90, 40, 160),
    "ok": (20, 120, 40),
    "err": (190, 30, 30),
    "warn": (160, 110, 0),
    "info": (30, 90, 180),
    "client": (20, 80, 150),
    "server": (90, 90, 90),
    "dim": (120, 120, 120),
}

STATUS_TAG = {"OK": "ok", "WARN": "warn", "FAIL": "err"}

# Teclas de función para correr una sola prueba (F5 corre todas las marcadas).
SINGLE_TEST_KEYS = (("F6", "dns"), ("F7", "telnet"), ("F8", "tls"), ("F9", "ping"))


def T(es, en=None):
    """Texto bilingüe (español, inglés). Si no hay inglés, es neutro (igual en ambos)."""
    return (es, es if en is None else en)


def as_pair(text):
    return text if isinstance(text, tuple) else (text, text)


HOST_RE = re.compile(r"^(?=.{1,253}$)[a-z0-9_](?:[a-z0-9_-]{0,61}[a-z0-9_])?"
                     r"(?:\.[a-z0-9_](?:[a-z0-9_-]{0,61}[a-z0-9_])?)*$")


def clean_target(value):
    """Acepta dominios, hosts, URLs o correos y devuelve solo el host."""
    v = value.strip().lower()
    if "://" in v:
        v = v.split("://", 1)[1]
    if "@" in v:
        v = v.rsplit("@", 1)[1]
    v = v.split("/", 1)[0].strip().rstrip(".")
    if v.startswith("[") and "]" in v:          # [IPv6] o [IPv6]:puerto
        v = v[1:v.index("]")]
    elif v.count(":") == 1:                      # host:puerto
        v = v.split(":", 1)[0]
    if v and not v.isascii():                    # dominios con acentos/ñ -> punycode
        try:
            v = v.encode("idna").decode("ascii")
        except UnicodeError:
            pass
    return v


def valid_host(h):
    """Solo nombres de host o IPs. Bloquea, por ejemplo, textos que empiezan con '-'
    y que el comando ping podría interpretar como opciones."""
    try:
        ipaddress.ip_address(h)
        return True
    except ValueError:
        return bool(HOST_RE.match(h))


def ehlo_identity(sock):
    """Identidad para EHLO: la IP local entre corchetes (RFC 5321), nunca el nombre del equipo."""
    ip = sock.getsockname()[0]
    return f"[IPv6:{ip}]" if ":" in ip else f"[{ip}]"


class SimplePDF:
    """Generador de PDF mínimo (texto en A4) escrito a mano, sin librerías externas
    y sin metadatos (autor, programa, fechas)."""

    W, H = 595.28, 841.89
    MARGIN = 40
    FONTS = (("F1", "Courier"), ("F2", "Courier-Bold"), ("F3", "Helvetica-Bold"), ("F4", "Courier-Oblique"))

    def __init__(self, footer=""):
        self.footer = footer
        self.pages = []
        self._new_page()

    def _new_page(self):
        self.ops = []
        self.pages.append(self.ops)
        self.y = self.H - self.MARGIN

    @staticmethod
    def _esc(text):
        b = text.encode("cp1252", "replace")  # WinAnsiEncoding
        return b.replace(b"\\", b"\\\\").replace(b"(", b"\\(").replace(b")", b"\\)")

    def _text(self, x, y, font, size, rgb, text):
        r, g, b = (c / 255 for c in rgb)
        return (b"BT /%s %d Tf %.3f %.3f %.3f rg %.2f %.2f Td (" % (font.encode(), size, r, g, b, x, y)
                + self._esc(text) + b") Tj ET")

    def title(self, text, size=16):
        self.y -= size
        self.ops.append(self._text(self.MARGIN, self.y, "F3", size, (20, 20, 20), text))
        self.y -= size * 0.8

    def line(self, text, rgb=(30, 30, 30), bold=False, size=8):
        lead = size * 1.25
        width = int((self.W - 2 * self.MARGIN) / (size * 0.6))
        indent = " " * min(len(text) - len(text.lstrip(" ")) + 2, width // 2)
        chunks = [text[:width]]
        rest = text[width:]
        while rest:
            n = width - len(indent)
            chunks.append(indent + rest[:n])
            rest = rest[n:]
        for chunk in chunks:
            if self.y - lead < self.MARGIN + 20:
                self._new_page()
            self.y -= lead
            if chunk.strip():
                self.ops.append(self._text(self.MARGIN, self.y, "F2" if bold else "F1", size, rgb, chunk))

    def output(self, path):
        total = len(self.pages)
        objs = {1: b"<< /Type /Catalog /Pages 2 0 R >>"}
        nid = 3
        font_refs = []
        for key, base in self.FONTS:
            objs[nid] = b"<< /Type /Font /Subtype /Type1 /BaseFont /%s /Encoding /WinAnsiEncoding >>" % base.encode()
            font_refs.append(b"/%s %d 0 R" % (key.encode(), nid))
            nid += 1
        kids = []
        for i, ops in enumerate(self.pages, 1):
            foot = f"{self.footer}  |  Pagina {i} de {total}".strip(" |")
            fx = (self.W - len(foot) * 7 * 0.6) / 2
            stream = b"\n".join(ops + [self._text(fx, 22, "F4", 7, (120, 120, 120), foot)])
            objs[nid] = b"<< /Length %d >>\nstream\n" % len(stream) + stream + b"\nendstream"
            objs[nid + 1] = (b"<< /Type /Page /Parent 2 0 R /MediaBox [0 0 %.2f %.2f] /Resources << /Font << %s >> >>"
                             b" /Contents %d 0 R >>" % (self.W, self.H, b" ".join(font_refs), nid))
            kids.append(b"%d 0 R" % (nid + 1))
            nid += 2
        objs[2] = b"<< /Type /Pages /Kids [%s] /Count %d >>" % (b" ".join(kids), total)

        out = bytearray(b"%PDF-1.4\n%\xe2\xe3\xcf\xd3\n")
        offsets = []
        for i in range(1, nid):
            offsets.append(len(out))
            out += b"%d 0 obj\n" % i + objs[i] + b"\nendobj\n"
        xref = len(out)
        out += b"xref\n0 %d\n0000000000 65535 f \n" % nid
        for off in offsets:
            out += b"%010d 00000 n \n" % off
        out += b"trailer\n<< /Size %d /Root 1 0 R >>\nstartxref\n%d\n%%%%EOF\n" % (nid, xref)
        with open(path, "wb") as f:
            f.write(out)


class SMTPProtoError(Exception):
    def __init__(self, es, en):
        super().__init__(es)
        self.pair = (es, en)


class SMTPConversation:
    """Diálogo SMTP en crudo sobre un socket (plano o TLS), registrando todo."""

    def __init__(self, sock, log):
        self.sock = sock
        self.log = log
        self.buf = b""

    def _readline(self):
        while b"\n" not in self.buf:
            chunk = self.sock.recv(4096)
            if not chunk:
                raise ConnectionError("closed")
            self.buf += chunk
        line, self.buf = self.buf.split(b"\n", 1)
        return line.rstrip(b"\r").decode("utf-8", "replace")

    def read_reply(self):
        lines = []
        while True:
            line = self._readline()
            lines.append(line)
            self.log(f"    S: {line}", "server")
            if len(line) < 4 or line[3] != "-":
                break
        last = lines[-1]
        code = int(last[:3]) if last[:3].isdigit() else 0
        return code, lines

    def send(self, cmd, shown=None):
        es, en = as_pair(shown if shown is not None else cmd)
        self.log(T(f"    C: {es}", f"    C: {en}"), "client")
        self.sock.sendall((cmd + "\r\n").encode("utf-8"))
        return self.read_reply()

    def quit(self):
        try:
            self.send("QUIT")
        except Exception:
            pass


# ================================================================== App ====
class MailDiagnosticsApp:
    def __init__(self, root):
        self.root = root
        root.title(APP_TITLE)
        root.geometry("1320x840")
        root.minsize(1080, 700)
        root.configure(bg=C["bg"])

        self.q = queue.Queue()
        self.report = []      # (texto_es, texto_en, tag)
        self.results = []     # (prueba, objetivo, estado, detalle_es, detalle_en)
        self.worker = None
        self.stop_event = threading.Event()
        self.started_at = None
        self.steps_done = 0

        self._pick_fonts()
        self._setup_style()
        self._build()
        root.bind("<F5>", lambda e: self.run_selected())
        root.bind("<Control-Return>", lambda e: self.run_selected())
        for key, test in SINGLE_TEST_KEYS:
            root.bind(f"<{key}>", lambda e, t=test: self.run_tests({t}))
        root.after(40, self._drain_queue)
        if getattr(sys, "frozen", False):   # versión compilada: revisión en el primer arranque
            root.after(400, self.first_run_check)

    # ------------------------------------------------------------ Estilo --
    def _pick_fonts(self):
        fams = set(tkfont.families(self.root))
        ui = next((f for f in ("Segoe UI", "SF Pro Text", "Helvetica Neue", "Inter",
                               "Ubuntu", "Cantarell", "DejaVu Sans") if f in fams), "Helvetica")
        mono = next((f for f in ("Cascadia Mono", "Consolas", "SF Mono", "Menlo",
                                 "JetBrains Mono", "DejaVu Sans Mono") if f in fams), "Courier")
        self.F_UI = (ui, 10)
        self.F_SMALL = (ui, 9)
        self.F_BOLD = (ui, 10, "bold")
        self.F_SECTION = (ui, 11, "bold")
        self.F_TITLE = (ui, 18, "bold")
        self.F_BTN = (ui, 11, "bold")
        self.F_MONO = (mono, 10)
        self.F_MONO_B = (mono, 10, "bold")

    def _setup_style(self):
        s = ttk.Style(self.root)
        s.theme_use("clam")
        s.configure(".", background=C["bg"], foreground=C["text"], font=self.F_UI,
                    bordercolor=C["border"], focuscolor=C["card"], troughcolor=C["panel"])
        s.configure("TFrame", background=C["bg"])
        s.configure("Card.TFrame", background=C["card"])
        s.configure("TLabel", background=C["bg"], foreground=C["text"])
        s.configure("Card.TLabel", background=C["card"], foreground=C["text"])
        s.configure("Muted.TLabel", background=C["card"], foreground=C["muted"], font=self.F_SMALL)
        s.configure("Title.TLabel", background=C["bg"], foreground=C["text"], font=self.F_TITLE)
        s.configure("Sub.TLabel", background=C["bg"], foreground=C["muted"])
        s.configure("Section.TLabel", background=C["card"], foreground=C["text"], font=self.F_SECTION)
        s.configure("Status.TLabel", background=C["card"], foreground=C["muted"], font=self.F_SMALL)

        for w in ("TCheckbutton", "TRadiobutton"):
            s.configure(w, background=C["card"], foreground=C["text"], indicatorbackground=C["input"],
                        indicatorforeground="white", padding=(0, 3))
            s.map(w, background=[("active", C["card"])],
                  foreground=[("disabled", C["muted"])],
                  indicatorbackground=[("selected", C["accent"]), ("active", C["border"])])

        s.configure("TEntry", fieldbackground=C["input"], foreground=C["text"], insertcolor=C["text"],
                    bordercolor=C["border"], lightcolor=C["input"], darkcolor=C["input"], padding=6)
        s.map("TEntry", bordercolor=[("focus", C["accent"])],
              fieldbackground=[("disabled", C["panel"])], foreground=[("disabled", C["muted"])])
        s.configure("TSpinbox", fieldbackground=C["input"], foreground=C["text"], insertcolor=C["text"],
                    background=C["input"], arrowcolor=C["text"], bordercolor=C["border"],
                    lightcolor=C["input"], darkcolor=C["input"], padding=5)
        s.map("TSpinbox", bordercolor=[("focus", C["accent"])])

        s.configure("TNotebook", background=C["bg"], borderwidth=0, tabmargins=(0, 0, 0, 0))
        s.configure("TNotebook.Tab", background=C["panel"], foreground=C["muted"], padding=(18, 9),
                    borderwidth=0, lightcolor=C["panel"], bordercolor=C["bg"], font=self.F_BOLD)
        s.map("TNotebook.Tab", background=[("selected", C["card"])], foreground=[("selected", C["text"])],
              lightcolor=[("selected", C["card"])], expand=[("selected", (0, 0, 0, 0))])

        s.configure("Accent.TButton", background=C["accent"], foreground="white", font=self.F_BTN,
                    padding=(16, 11), borderwidth=0, lightcolor=C["accent"], darkcolor=C["accent"])
        s.map("Accent.TButton", background=[("disabled", C["border"]), ("active", C["accent_h"])],
              foreground=[("disabled", C["muted"])])
        s.configure("TButton", background=C["input"], foreground=C["text"], padding=(10, 7), borderwidth=0,
                    lightcolor=C["input"], darkcolor=C["input"])
        s.map("TButton", background=[("disabled", C["panel"]), ("active", C["border"])],
              foreground=[("disabled", C["muted"])])
        s.configure("Danger.TButton", background="#3d1f20", foreground=C["err"], padding=(10, 7),
                    borderwidth=0, lightcolor="#3d1f20", darkcolor="#3d1f20")
        s.map("Danger.TButton", background=[("disabled", C["panel"]), ("active", "#5a2a2b")],
              foreground=[("disabled", C["muted"])])

        s.configure("Horizontal.TProgressbar", troughcolor=C["input"], background=C["accent"],
                    bordercolor=C["input"], lightcolor=C["accent"], darkcolor=C["accent"], thickness=6)
        s.configure("Vertical.TScrollbar", background=C["input"], troughcolor=C["log"],
                    bordercolor=C["log"], arrowcolor=C["muted"], lightcolor=C["input"], darkcolor=C["input"])

    def _text(self, parent, height, **kw):
        frame = tk.Frame(parent, bg=C["border"], padx=1, pady=1)
        t = tk.Text(frame, height=height, bg=C["input"], fg=C["text"], insertbackground=C["text"],
                    relief="flat", font=self.F_MONO, wrap="none", padx=8, pady=6,
                    highlightthickness=0, selectbackground=C["accent"], undo=True, **kw)
        t.pack(fill="both", expand=True)
        return frame, t

    # ---------------------------------------------------------------- UI --
    def _build(self):
        header = ttk.Frame(self.root, padding=(24, 18, 24, 6))
        header.pack(fill="x")
        ttk.Label(header, text=APP_TITLE, style="Title.TLabel").pack(side="left")
        ttk.Label(header, text="    DNS  ·  Telnet  ·  TLS / OpenSSL  ·  Ping",
                  style="Sub.TLabel").pack(side="left", pady=(7, 0))
        ttk.Label(header, text=f"Versión {APP_VERSION}", style="Sub.TLabel").pack(side="right", pady=(7, 0))
        ttk.Button(header, text="Componentes", command=self.show_components).pack(side="right", padx=(0, 14))

        body = ttk.Frame(self.root, padding=(24, 8, 24, 20))
        body.pack(fill="both", expand=True)
        body.columnconfigure(1, weight=1)
        body.rowconfigure(0, weight=1)

        left = ttk.Frame(body)
        left.grid(row=0, column=0, sticky="nsw", padx=(0, 16))
        right = ttk.Frame(body, style="Card.TFrame", padding=16)
        right.grid(row=0, column=1, sticky="nsew")

        self._build_left(left)
        self._build_right(right)

    def _build_left(self, left):
        nb = ttk.Notebook(left)
        nb.pack(fill="both", expand=True)

        # --- Pestaña Dominios ---
        t1 = ttk.Frame(nb, style="Card.TFrame", padding=18)
        nb.add(t1, text="Dominios")
        ttk.Label(t1, text="Dominios", style="Section.TLabel").pack(anchor="w")
        ttk.Label(t1, text="Uno por línea. Se usan para DNS y, si quieres, para SMTP y Ping.",
                  style="Muted.TLabel", wraplength=390).pack(anchor="w", pady=(2, 8))
        fr, self.domains_txt = self._text(t1, 9)
        fr.pack(fill="both", expand=True)

        ttk.Label(t1, text="Selector(es) DKIM", style="Section.TLabel").pack(anchor="w", pady=(16, 0))
        ttk.Label(t1, text="Opcional, separados por coma (ej. odoo, google, selector1).",
                  style="Muted.TLabel").pack(anchor="w", pady=(2, 6))
        self.dkim_var = tk.StringVar()
        ttk.Entry(t1, textvariable=self.dkim_var).pack(fill="x")

        # --- Pestaña SMTP ---
        t2 = ttk.Frame(nb, style="Card.TFrame", padding=18)
        nb.add(t2, text="SMTP")
        ttk.Label(t2, text="Servidores a probar", style="Section.TLabel").pack(anchor="w")
        self.smtp_mode = tk.StringVar(value="same")
        for val, txt in (("same", "Los mismos dominios de la pestaña Dominios"),
                         ("mx", "El MX principal de cada dominio"),
                         ("custom", "Hosts personalizados (uno por línea):")):
            ttk.Radiobutton(t2, text=txt, value=val, variable=self.smtp_mode,
                            command=self._toggle_custom_hosts).pack(anchor="w")
        fr, self.hosts_txt = self._text(t2, 3)
        fr.pack(fill="x", pady=(4, 0))

        ttk.Label(t2, text="Puertos", style="Section.TLabel").pack(anchor="w", pady=(16, 4))
        pf = ttk.Frame(t2, style="Card.TFrame")
        pf.pack(fill="x")
        self.port_vars = {}
        for i, (p, lbl) in enumerate(((25, "25 SMTP"), (465, "465 SMTPS"), (587, "587 Submission"))):
            v = tk.BooleanVar(value=True)
            self.port_vars[p] = v
            ttk.Checkbutton(pf, text=lbl, variable=v).grid(row=0, column=i, sticky="w", padx=(0, 14))
        cf = ttk.Frame(t2, style="Card.TFrame")
        cf.pack(fill="x", pady=(4, 0))
        self.custom_port_on = tk.BooleanVar(value=False)
        self.custom_port_var = tk.StringVar()
        self.custom_implicit = tk.BooleanVar(value=False)
        ttk.Checkbutton(cf, text="Personalizado:", variable=self.custom_port_on).pack(side="left")
        ttk.Entry(cf, textvariable=self.custom_port_var, width=7).pack(side="left", padx=(6, 12))
        ttk.Checkbutton(cf, text="TLS implícito", variable=self.custom_implicit).pack(side="left")

        ttk.Label(t2, text="Autenticación (prueba TLS/OpenSSL)", style="Section.TLabel").pack(anchor="w", pady=(16, 0))
        ttk.Label(t2, text="Se envía solo dentro de un túnel TLS con certificado verificado. "
                           "Nunca aparece en el log ni en el PDF y no se guarda en disco.",
                  style="Muted.TLabel", wraplength=390).pack(anchor="w", pady=(2, 6))
        af = ttk.Frame(t2, style="Card.TFrame")
        af.pack(fill="x")
        af.columnconfigure(1, weight=1)
        self.user_var = tk.StringVar()
        self.pass_var = tk.StringVar()
        ttk.Label(af, text="Usuario", style="Card.TLabel").grid(row=0, column=0, sticky="w", padx=(0, 10), pady=3)
        ttk.Entry(af, textvariable=self.user_var).grid(row=0, column=1, columnspan=2, sticky="ew", pady=3)
        ttk.Label(af, text="Contraseña", style="Card.TLabel").grid(row=1, column=0, sticky="w", padx=(0, 10), pady=3)
        self.pass_entry = ttk.Entry(af, textvariable=self.pass_var, show="•")
        self.pass_entry.grid(row=1, column=1, sticky="ew", pady=3)
        self.show_pass = tk.BooleanVar(value=False)
        ttk.Checkbutton(af, text="Ver", variable=self.show_pass,
                        command=lambda: self.pass_entry.config(show="" if self.show_pass.get() else "•")
                        ).grid(row=1, column=2, padx=(8, 0))

        of = ttk.Frame(t2, style="Card.TFrame")
        of.pack(fill="x", pady=(10, 0))
        self.verify_var = tk.BooleanVar(value=True)
        ttk.Checkbutton(of, text="Verificar certificado", variable=self.verify_var).pack(side="left")
        self.timeout_var = tk.StringVar(value="10")
        ttk.Spinbox(of, from_=2, to=60, textvariable=self.timeout_var, width=4).pack(side="right")
        ttk.Label(of, text="Timeout (s)", style="Card.TLabel").pack(side="right", padx=(0, 6))
        self._toggle_custom_hosts()

        # --- Pestaña Ping ---
        t3 = ttk.Frame(nb, style="Card.TFrame", padding=18)
        nb.add(t3, text="Ping")
        ttk.Label(t3, text="Destinos", style="Section.TLabel").pack(anchor="w")
        self.ping_domains = tk.BooleanVar(value=True)
        self.ping_smtp = tk.BooleanVar(value=True)
        ttk.Checkbutton(t3, text="Dominios (como están en la pestaña Dominios)",
                        variable=self.ping_domains).pack(anchor="w", pady=(6, 0))
        ttk.Checkbutton(t3, text="Servidores SMTP (según la pestaña SMTP)",
                        variable=self.ping_smtp).pack(anchor="w")
        pf2 = ttk.Frame(t3, style="Card.TFrame")
        pf2.pack(fill="x", pady=(14, 0))
        ttk.Label(pf2, text="Paquetes por destino", style="Card.TLabel").pack(side="left")
        self.ping_count = tk.StringVar(value="4")
        ttk.Spinbox(pf2, from_=1, to=20, textvariable=self.ping_count, width=4).pack(side="left", padx=8)
        ttk.Label(t3, text="Muchos servidores bloquean ICMP: que un ping no responda no significa "
                           "que el servidor esté caído. Si Telnet/TLS conectan, el servidor está vivo.",
                  style="Muted.TLabel", wraplength=390).pack(anchor="w", pady=(16, 0))

        # --- Panel de ejecución ---
        tc = ttk.Frame(left, style="Card.TFrame", padding=18)
        tc.pack(fill="x", pady=(14, 0))
        ttk.Label(tc, text="Pruebas", style="Section.TLabel").pack(anchor="w", pady=(0, 6))
        g = ttk.Frame(tc, style="Card.TFrame")
        g.pack(fill="x")
        self.test_vars = {}
        for i, (key, lbl) in enumerate((("dns", "DNS"), ("telnet", "Telnet"),
                                        ("tls", "TLS / OpenSSL"), ("ping", "Ping"))):
            v = tk.BooleanVar(value=True)
            self.test_vars[key] = v
            ttk.Checkbutton(g, text=lbl, variable=v).grid(row=0, column=i, sticky="w", padx=(0, 16))

        self.run_btn = ttk.Button(tc, text="▶   Ejecutar pruebas   (F5)", style="Accent.TButton",
                                  command=self.run_selected)
        self.run_btn.pack(fill="x", pady=(12, 8))

        ttk.Label(tc, text="Una sola prueba (tecla de función):",
                  style="Muted.TLabel").pack(anchor="w", pady=(0, 4))
        sb = ttk.Frame(tc, style="Card.TFrame")
        sb.pack(fill="x")
        self.single_btns = []
        names = {"dns": "DNS", "telnet": "Telnet", "tls": "TLS", "ping": "Ping"}
        for i, (fkey, test) in enumerate(SINGLE_TEST_KEYS):
            b = ttk.Button(sb, text=f"{names[test]}  ·  {fkey}",
                           command=lambda t=test: self.run_tests({t}))
            b.grid(row=0, column=i, sticky="ew", padx=(0 if i == 0 else 4, 0))
            sb.columnconfigure(i, weight=1)
            self.single_btns.append(b)

        self.auto_pdf = tk.BooleanVar(value=True)
        ttk.Checkbutton(tc, text="Generar PDF al terminar (carpeta 'reportes')",
                        variable=self.auto_pdf).pack(anchor="w", pady=(10, 0))

    def _build_right(self, right):
        top = ttk.Frame(right, style="Card.TFrame")
        top.pack(fill="x", pady=(0, 10))
        ttk.Label(top, text="Resultados", style="Section.TLabel").pack(side="left")
        self.stop_btn = ttk.Button(top, text="■  Detener", style="Danger.TButton",
                                   command=self.stop, state="disabled")
        self.stop_btn.pack(side="right")
        ttk.Button(top, text="Limpiar", command=self.clear_log).pack(side="right", padx=(0, 6))
        self.pdf_btn = ttk.Button(top, text="Exportar PDF", command=lambda: self.export_pdf())
        self.pdf_btn.pack(side="right", padx=(0, 6))
        ttk.Button(top, text="Copiar log", command=self.copy_log).pack(side="right", padx=(0, 6))

        lf = tk.Frame(right, bg=C["border"], padx=1, pady=1)
        lf.pack(fill="both", expand=True)
        inner = tk.Frame(lf, bg=C["log"])
        inner.pack(fill="both", expand=True)
        self.log_txt = tk.Text(inner, bg=C["log"], fg=C["text"], font=self.F_MONO, relief="flat",
                               wrap="word", padx=12, pady=10, highlightthickness=0,
                               selectbackground=C["accent"], state="disabled", cursor="arrow")
        scroll = ttk.Scrollbar(inner, orient="vertical", command=self.log_txt.yview)
        self.log_txt.configure(yscrollcommand=scroll.set)
        scroll.pack(side="right", fill="y")
        self.log_txt.pack(side="left", fill="both", expand=True)

        for tag, color in (("ok", C["ok"]), ("err", C["err"]), ("warn", C["warn"]), ("info", C["info"]),
                           ("client", C["client"]), ("server", C["server"]), ("dim", C["muted"]),
                           ("plain", C["text"])):
            self.log_txt.tag_configure(tag, foreground=color)
        self.log_txt.tag_configure("header", foreground=C["head"], font=self.F_MONO_B)

        bottom = ttk.Frame(right, style="Card.TFrame")
        bottom.pack(fill="x", pady=(10, 0))
        self.progress = ttk.Progressbar(bottom, mode="determinate")
        self.progress.pack(fill="x")
        self.status_var = tk.StringVar(value="Listo. Configura las pestañas de la izquierda y presiona Ejecutar.")
        ttk.Label(bottom, textvariable=self.status_var, style="Status.TLabel").pack(anchor="w", pady=(6, 0))

    def _toggle_custom_hosts(self):
        on = self.smtp_mode.get() == "custom"
        self.hosts_txt.config(state="normal" if on else "disabled",
                              bg=C["input"] if on else C["panel"])

    # --------------------------------------------------------- Acciones --
    def _ask_language(self):
        """Diálogo modal: devuelve 'es', 'en' o None si se cancela."""
        choice = {"lang": None}
        dlg = tk.Toplevel(self.root)
        dlg.title("Copiar log")
        dlg.configure(bg=C["card"])
        dlg.resizable(False, False)
        dlg.transient(self.root)

        frame = ttk.Frame(dlg, style="Card.TFrame", padding=(24, 20, 24, 18))
        frame.pack(fill="both", expand=True)
        ttk.Label(frame, text="¿En qué idioma quieres copiar el log?",
                  style="Section.TLabel").pack(anchor="w")
        ttk.Label(frame, text="Which language should the log be copied in?",
                  style="Muted.TLabel").pack(anchor="w", pady=(2, 16))

        def pick(lang):
            choice["lang"] = lang
            dlg.destroy()

        btns = ttk.Frame(frame, style="Card.TFrame")
        btns.pack(fill="x")
        es_btn = ttk.Button(btns, text="Español", style="Accent.TButton", command=lambda: pick("es"))
        es_btn.pack(side="left", expand=True, fill="x")
        ttk.Button(btns, text="English", style="Accent.TButton",
                   command=lambda: pick("en")).pack(side="left", expand=True, fill="x", padx=(8, 0))
        ttk.Button(frame, text="Cancelar", command=dlg.destroy).pack(fill="x", pady=(8, 0))

        dlg.bind("<Escape>", lambda e: dlg.destroy())
        dlg.protocol("WM_DELETE_WINDOW", dlg.destroy)

        # Centrar sobre la ventana principal
        dlg.update_idletasks()
        x = self.root.winfo_rootx() + (self.root.winfo_width() - dlg.winfo_width()) // 2
        y = self.root.winfo_rooty() + (self.root.winfo_height() - dlg.winfo_height()) // 3
        dlg.geometry(f"+{max(x, 0)}+{max(y, 0)}")
        dlg.grab_set()
        es_btn.focus_set()
        self.root.wait_window(dlg)
        return choice["lang"]

    def copy_log(self):
        if not self.report:
            messagebox.showwarning("Vacío", "No hay nada que copiar.")
            return
        lang = self._ask_language()
        if not lang:
            return
        idx = 0 if lang == "es" else 1
        text = "\n".join(entry[idx] for entry in list(self.report)).strip()
        self.root.clipboard_clear()
        self.root.clipboard_append(text)
        self.status_var.set("Log copiado al portapapeles en español." if lang == "es"
                            else "Log copiado al portapapeles en inglés.")

    def clear_log(self):
        if self.worker and self.worker.is_alive():
            return
        self.log_txt.config(state="normal")
        self.log_txt.delete("1.0", "end")
        self.log_txt.config(state="disabled")
        self.report.clear()
        self.results.clear()
        self.progress["value"] = 0
        self.status_var.set("Log limpio.")

    def stop(self):
        self.stop_event.set()
        self.status_var.set("Deteniendo... (se termina la operación en curso)")

    def run_selected(self):
        tests = {k for k, v in self.test_vars.items() if v.get()}
        if not tests:
            messagebox.showwarning("Sin pruebas", "Selecciona al menos una prueba.")
            return
        self.run_tests(tests)

    def _lines(self, widget, invalid):
        out = []
        for line in widget.get("1.0", "end").splitlines():
            if not line.strip():
                continue
            v = clean_target(line)
            if not valid_host(v):
                invalid.append(line.strip())
            elif v not in out:
                out.append(v)
        return out

    def _snapshot(self, tests):
        """Lee y valida toda la configuración en el hilo de la UI."""
        cfg = {"tests": tests}
        invalid = []
        cfg["domains"] = self._lines(self.domains_txt, invalid)
        cfg["hosts"] = self._lines(self.hosts_txt, invalid) if self.smtp_mode.get() == "custom" else []
        if invalid:
            raise ValueError("Estos valores no son dominios, hosts ni IPs válidos:\n\n  "
                             + "\n  ".join(invalid[:10]))
        cfg["dkim"] = [s.strip() for s in self.dkim_var.get().split(",") if s.strip()]
        cfg["smtp_mode"] = self.smtp_mode.get()
        cfg["ping_domains"] = self.ping_domains.get()
        cfg["ping_smtp"] = self.ping_smtp.get()
        cfg["verify"] = self.verify_var.get()
        cfg["user"] = self.user_var.get().strip()
        cfg["password"] = self.pass_var.get()
        cfg["pdf"] = self.auto_pdf.get()
        try:
            cfg["timeout"] = max(1, int(self.timeout_var.get()))
            cfg["ping_count"] = max(1, min(50, int(self.ping_count.get())))
        except ValueError:
            raise ValueError("El timeout y el número de paquetes deben ser números enteros.")

        ports = [p for p, v in self.port_vars.items() if v.get()]
        cfg["custom_port"] = None
        cfg["custom_implicit"] = self.custom_implicit.get()
        if self.custom_port_on.get():
            try:
                cp = int(self.custom_port_var.get())
                if not 1 <= cp <= 65535:
                    raise ValueError
            except ValueError:
                raise ValueError("El puerto personalizado debe ser un número entre 1 y 65535.")
            cfg["custom_port"] = cp
            if cp not in ports:
                ports.append(cp)
        cfg["ports"] = ports

        smtp_tests = bool(tests & {"telnet", "tls"})
        cfg["needs_hosts"] = smtp_tests or ("ping" in tests and cfg["ping_smtp"])
        needs_domains = ("dns" in tests
                         or (cfg["needs_hosts"] and cfg["smtp_mode"] in ("same", "mx"))
                         or ("ping" in tests and cfg["ping_domains"]))
        if needs_domains and not cfg["domains"]:
            raise ValueError("Escribe al menos un dominio en la pestaña Dominios.")
        if cfg["needs_hosts"] and cfg["smtp_mode"] == "custom" and not cfg["hosts"]:
            raise ValueError("Elegiste hosts SMTP personalizados pero la lista está vacía.")
        if smtp_tests and not ports:
            raise ValueError("Selecciona al menos un puerto en la pestaña SMTP.")
        if "ping" in tests and not (cfg["ping_domains"] or cfg["ping_smtp"]):
            raise ValueError("Elige al menos un destino para Ping.")
        return cfg

    def run_tests(self, tests):
        if self.worker and self.worker.is_alive():
            return
        try:
            cfg = self._snapshot(tests)
        except ValueError as e:
            messagebox.showwarning("Revisa la configuración", str(e))
            return

        if "tls" in tests and cfg["user"] and not cfg["password"]:
            pwd = simpledialog.askstring("Contraseña SMTP",
                                         f"Contraseña para {cfg['user']}:\n(se usa solo para AUTH dentro de TLS)",
                                         show="•", parent=self.root)
            if pwd:
                cfg["password"] = pwd
            else:
                cfg["user"] = ""  # sin contraseña: se omite AUTH

        self.clear_log()
        self.stop_event.clear()
        self._set_busy(True)
        self.started_at = time.perf_counter()
        self.steps_done = 0
        self.worker = threading.Thread(target=self._worker, args=(cfg,), daemon=True)
        self.worker.start()

    def _set_busy(self, busy):
        state = "disabled" if busy else "normal"
        for b in [self.run_btn, self.pdf_btn, *self.single_btns]:
            b.config(state=state)
        self.stop_btn.config(state="normal" if busy else "disabled")

    # ------------------------------------------------ Cola / hilo UI ----
    def _drain_queue(self):
        try:
            for _ in range(500):
                item = self.q.get_nowait()
                kind = item[0]
                if kind == "log":
                    self.log_txt.config(state="normal")
                    self.log_txt.insert("end", item[1] + "\n", item[2])
                    self.log_txt.see("end")
                    self.log_txt.config(state="disabled")
                elif kind == "pmax":
                    self.progress["maximum"] = max(1, item[1])
                    self.progress["value"] = 0
                elif kind == "progress":
                    self.progress["value"] = item[1]
                elif kind == "status":
                    self.status_var.set(item[1])
                elif kind == "done":
                    self._on_done(item[1])
        except queue.Empty:
            pass
        self.root.after(40, self._drain_queue)

    def _on_done(self, cfg):
        cfg["password"] = None   # no conservar la contraseña en la configuración de la corrida
        self._set_busy(False)
        elapsed = time.perf_counter() - self.started_at
        counts = {k: sum(1 for r in self.results if r[2] == k) for k in ("OK", "WARN", "FAIL")}
        self.progress["value"] = self.progress["maximum"]
        msg = (f"Terminado en {elapsed:.1f} s  ·  {counts['OK']} OK  ·  "
               f"{counts['WARN']} advertencias  ·  {counts['FAIL']} fallos")
        if cfg["pdf"] and self.report:
            folder = reports_dir()
            os.makedirs(folder, exist_ok=True)
            ts = datetime.now().strftime("%Y-%m-%d_%H%M%S")
            name = cfg["domains"][0] if len(cfg["domains"]) == 1 else "lote"
            path = os.path.join(folder, f"Mail_Diagnostics_{name}_{ts}.pdf")
            if self.export_pdf(path):
                msg += f"  ·  PDF: {path}"
        self.status_var.set(msg)

    # -------------------------------------------- Helpers del worker ----
    def log(self, text="", tag="plain", en=None):
        """Registra una línea. `text` puede ser str (con `en` opcional) o un par T(es, en)."""
        if isinstance(text, tuple):
            es, en_txt = text
        else:
            es, en_txt = text, (text if en is None else en)
        self.report.append((es, en_txt, tag))
        self.q.put(("log", es, tag))

    def status(self, text):
        self.q.put(("status", text))

    def step(self):
        self.steps_done += 1
        self.q.put(("progress", self.steps_done))

    def result(self, test, target, status, detail):
        es, en = as_pair(detail)
        self.results.append((test, target, status, es, en))

    def stopped(self):
        return self.stop_event.is_set()

    @staticmethod
    def err_text(e, port=None):
        """Devuelve el error como par (español, inglés)."""
        if isinstance(e, SMTPProtoError):
            return e.pair
        if isinstance(e, ssl.SSLCertVerificationError):
            r = e.verify_message or str(e)
            return T(f"Certificado no válido: {r}", f"Invalid certificate: {r}")
        if isinstance(e, ssl.SSLError):
            r = e.reason or str(e)
            return T(f"Error TLS: {r}", f"TLS error: {r}")
        if isinstance(e, socket.gaierror):
            return T("No se pudo resolver el nombre del host", "Could not resolve host name")
        if isinstance(e, (socket.timeout, TimeoutError)):
            es = "Timeout: el puerto no responde (filtrado por firewall o servidor caído)"
            en = "Timeout: port not responding (filtered by a firewall or server down)"
            if port == 25:
                es += ". Muchos ISP y redes corporativas bloquean la salida por el puerto 25"
                en += ". Many ISPs and corporate networks block outbound port 25"
            return T(es, en)
        if isinstance(e, ConnectionRefusedError):
            return T("Conexión rechazada: el puerto está cerrado", "Connection refused: port is closed")
        if isinstance(e, ConnectionResetError):
            return T("El servidor reinició la conexión", "Connection reset by server")
        if isinstance(e, ConnectionError) and str(e) == "closed":
            return T("El servidor cerró la conexión", "Server closed the connection")
        return T(str(e) or type(e).__name__)

    def is_implicit(self, port, cfg):
        return port == 465 or (port == cfg["custom_port"] and cfg["custom_implicit"])

    def _make_resolver(self, timeout):
        # Solo se usa el resolvedor DNS configurado en el sistema. Si no hay ninguno,
        # NO se recurre a servidores públicos de terceros: las consultas fallan y se avisa.
        try:
            r = dns.resolver.Resolver()
        except dns.resolver.NoResolverConfiguration:
            r = dns.resolver.Resolver(configure=False)
            r.nameservers = []
        r.lifetime = timeout
        r.timeout = min(timeout, 5)
        return r

    # -------------------------------------------------------- Worker ----
    def _worker(self, cfg):
        try:
            self.resolver = self._make_resolver(cfg["timeout"])
            tests = cfg["tests"]
            names = [n for k, n in (("dns", "DNS"), ("telnet", "Telnet"), ("tls", "TLS/OpenSSL"),
                                    ("ping", "Ping")) if k in tests]
            local_now = datetime.now()
            utc_now = datetime.now(timezone.utc)
            self.log("=" * 78, "header")
            self.log(T(" REPORTE DE DIAGNOSTICO DE CORREO", " MAIL DIAGNOSTICS REPORT"), "header")
            self.log("=" * 78, "header")
            self.log(T(f" Fecha local : {local_now:%Y-%m-%d %H:%M:%S}",
                       f" Local date  : {local_now:%Y-%m-%d %H:%M:%S}"))
            self.log(T(f" Fecha UTC   : {utc_now:%Y-%m-%d %H:%M:%S} UTC",
                       f" UTC date    : {utc_now:%Y-%m-%d %H:%M:%S} UTC"))
            self.log(T(f" Versión     : {APP_TITLE} {APP_VERSION}",
                       f" Version     : {APP_TITLE} {APP_VERSION}"))
            self.log(T(f" Pruebas     : {', '.join(names)}",
                       f" Tests       : {', '.join(names)}"))
            if tests & {"telnet", "tls"}:
                ports = ", ".join(map(str, cfg["ports"]))
                self.log(T(f" Puertos     : {ports}", f" Ports       : {ports}"))
            if not self.resolver.nameservers:
                self.log(T(" [WARN] El sistema no tiene servidores DNS configurados: "
                           "las consultas DNS fallarán.",
                           " [WARN] The system has no DNS servers configured: "
                           "DNS queries will fail."), "warn")

            hosts = self._resolve_smtp_hosts(cfg) if cfg["needs_hosts"] else []
            ping_targets = []
            if "ping" in tests:
                if cfg["ping_domains"]:
                    ping_targets += cfg["domains"]
                if cfg["ping_smtp"]:
                    ping_targets += hosts
                ping_targets = list(dict.fromkeys(ping_targets))

            total = 0
            if "dns" in tests:
                total += len(cfg["domains"])
            for t in ("telnet", "tls"):
                if t in tests:
                    total += len(hosts) * len(cfg["ports"])
            total += len(ping_targets)
            self.q.put(("pmax", total))

            if "dns" in tests and not self.stopped():
                self.log("")
                self.log("##### DNS " + "#" * 68, "header")
                for d in cfg["domains"]:
                    if self.stopped():
                        break
                    self.status(f"DNS: {d}")
                    self._dns_check(d, cfg)
                    self.step()

            sections = (
                ("telnet", T("TELNET (conectividad SMTP en texto plano)",
                             "TELNET (plain-text SMTP connectivity)"), self._telnet_test),
                ("tls", T("TLS / OPENSSL (cifrado, certificado y autenticación)",
                          "TLS / OPENSSL (encryption, certificate and authentication)"), self._tls_test),
            )
            for key, (t_es, t_en), fn in sections:
                if key not in tests or self.stopped():
                    continue
                self.log("")
                self.log(T(f"##### {t_es} " + "#" * max(4, 71 - len(t_es)),
                           f"##### {t_en} " + "#" * max(4, 71 - len(t_en))), "header")
                if not hosts:
                    self.log(T("  [WARN] No hay servidores SMTP que probar.",
                               "  [WARN] No SMTP servers to test."), "warn")
                for h in hosts:
                    for p in cfg["ports"]:
                        if self.stopped():
                            break
                        self.status(f"{key.upper()}: {h}:{p}")
                        fn(h, p, cfg)
                        self.step()

            if "ping" in tests and not self.stopped():
                self.log("")
                self.log("##### PING " + "#" * 67, "header")
                for t in ping_targets:
                    if self.stopped():
                        break
                    self.status(f"Ping: {t}")
                    self._ping(t, cfg)
                    self.step()

            if self.stopped():
                self.log("")
                self.log(T("[WARN] Ejecución detenida por el usuario.",
                           "[WARN] Run stopped by the user."), "warn")
            self._summary()
        except Exception as e:
            self.log(T(f"[ERROR] Error inesperado: {type(e).__name__}: {e}",
                       f"[ERROR] Unexpected error: {type(e).__name__}: {e}"), "err")
        finally:
            self.q.put(("done", cfg))

    def _resolve_smtp_hosts(self, cfg):
        mode = cfg["smtp_mode"]
        if mode == "same":
            return list(cfg["domains"])
        if mode == "custom":
            return list(cfg["hosts"])
        self.log("")
        self.log(T(" Resolviendo el MX principal de cada dominio...",
                   " Resolving the primary MX of each domain..."), "info")
        hosts = []
        for d in cfg["domains"]:
            try:
                ans = self.resolver.resolve(d, "MX")
                best = min(ans, key=lambda r: r.preference)
                h = str(best.exchange).rstrip(".").lower()
                if not h:
                    self.log(T(f"   {d}: MX nulo (el dominio no recibe correo)",
                               f"   {d}: null MX (domain does not accept mail)"), "warn")
                    continue
                if not valid_host(h):
                    # Un MX viene de la red: se valida igual que lo que escribe el usuario.
                    self.log(T(f"   {d}: MX con nombre no válido, se omite: {h!r}",
                               f"   {d}: MX with an invalid name, skipped: {h!r}"), "warn")
                    continue
                self.log(T(f"   {d} -> {h} (prioridad {best.preference})",
                           f"   {d} -> {h} (priority {best.preference})"))
                if h not in hosts:
                    hosts.append(h)
            except dns.exception.DNSException as e:
                self.log(T(f"   {d}: no se encontró MX ({type(e).__name__})",
                           f"   {d}: no MX found ({type(e).__name__})"), "warn")
        return hosts

    # ------------------------------------------------------------ DNS ----
    def _q(self, name, rtype):
        try:
            return list(self.resolver.resolve(name, rtype))
        except dns.exception.DNSException:
            return []

    def _txt(self, name):
        return [b"".join(r.strings).decode("utf-8", "replace") for r in self._q(name, "TXT")]

    def _dns_check(self, domain, cfg):
        self.log("")
        self.log(f"--- {domain} ---", "header")
        try:
            self.resolver.resolve(domain, "SOA")
        except dns.resolver.NXDOMAIN:
            self.log(T("  [ERROR] El dominio no existe (NXDOMAIN).",
                       "  [ERROR] Domain does not exist (NXDOMAIN)."), "err")
            self.result("DNS", domain, "FAIL", "NXDOMAIN")
            return
        except dns.exception.DNSException:
            pass

        missing = []   # pares (es, en)

        def section(title, items, empty, tag_empty="warn"):
            t_es, t_en = title
            self.log(T(f"  [ {t_es} ]", f"  [ {t_en} ]"), "info")
            if items:
                for it in items:
                    self.log(f"    {it}")
            else:
                e_es, e_en = empty
                self.log(T(f"    {e_es}", f"    {e_en}"), tag_empty)

        section(T("NS - Servidores de nombres", "NS - Name servers"),
                sorted(r.to_text() for r in self._q(domain, "NS")),
                T("Sin registros NS", "No NS records"))
        section(T("A - Dirección IP", "A - IP address"),
                sorted(r.to_text() for r in self._q(domain, "A")),
                T("Sin registro A", "No A record"), "dim")

        mx = sorted(self._q(domain, "MX"), key=lambda r: r.preference)
        section(T("MX - Servidores de correo", "MX - Mail servers"),
                [f"{r.preference:<4} {str(r.exchange).rstrip('.')}" for r in mx],
                T("Sin registros MX: el dominio no puede recibir correo",
                  "No MX records: the domain cannot receive mail"), "err")

        spf = [t for t in self._txt(domain) if t.lower().startswith("v=spf1")]
        section(T("SPF - Anti suplantación", "SPF - Anti-spoofing"), spf,
                T("Sin registro SPF", "No SPF record"))
        if not spf:
            missing.append(T("SPF"))
        elif len(spf) > 1:
            self.log(T("    [WARN] Hay más de un SPF: eso invalida SPF (debe ser uno solo).",
                       "    [WARN] More than one SPF record: this invalidates SPF (there must be only one)."),
                     "warn")
            missing.append(T("SPF múltiple", "multiple SPF"))

        dmarc = [t for t in self._txt(f"_dmarc.{domain}") if t.lower().startswith("v=dmarc1")]
        section(T("DMARC - Política", "DMARC - Policy"), dmarc,
                T("Sin registro DMARC", "No DMARC record"))
        if dmarc:
            tags = dict(p.strip().split("=", 1) for p in dmarc[0].split(";") if "=" in p)
            pol = tags.get("p", "?").strip()
            self.log(T(f"    Política: p={pol}" + ("  (solo monitoreo)" if pol == "none" else ""),
                       f"    Policy: p={pol}" + ("  (monitoring only)" if pol == "none" else "")),
                     "warn" if pol == "none" else "ok")
        else:
            missing.append(T("DMARC"))

        self.log(T("  [ DKIM - Firma criptográfica ]", "  [ DKIM - Cryptographic signature ]"), "info")
        if cfg["dkim"]:
            for sel in cfg["dkim"]:
                recs = self._txt(f"{sel}._domainkey.{domain}")
                cname = self._q(f"{sel}._domainkey.{domain}", "CNAME")
                if recs:
                    for r in recs:
                        shown = r if len(r) <= 120 else r[:117] + "..."
                        self.log(f"    {sel}: {shown}", "ok")
                elif cname:
                    self.log(f"    {sel}: CNAME -> {cname[0].to_text()}", "ok")
                else:
                    self.log(T(f"    {sel}: no encontrado", f"    {sel}: not found"), "warn")
                    missing.append(T(f"DKIM {sel}"))
        else:
            self.log(T("    No se indicó selector", "    No selector provided"), "dim")

        section(T("CNAME - www", "CNAME - www"),
                [r.to_text() for r in self._q(f"www.{domain}", "CNAME")],
                T(f"Sin CNAME para www.{domain}", f"No CNAME for www.{domain}"), "dim")

        miss_es = ", ".join(m[0] for m in missing)
        miss_en = ", ".join(m[1] for m in missing)
        if not mx:
            self.result("DNS", domain, "FAIL",
                        T("sin MX" + (f"; falta {miss_es}" if missing else ""),
                          "no MX" + (f"; missing {miss_en}" if missing else "")))
        elif missing:
            self.result("DNS", domain, "WARN", T(f"falta {miss_es}", f"missing {miss_en}"))
        else:
            self.result("DNS", domain, "OK", T("MX, SPF y DMARC presentes", "MX, SPF and DMARC present"))

    # --------------------------------------------------------- Telnet ----
    def _telnet_test(self, host, port, cfg):
        target = f"{host}:{port}"
        self.log("")
        self.log(f"--- Telnet {target} ---", "header")
        self.log(T(f"  Equivalente: telnet {host} {port}", f"  Equivalent: telnet {host} {port}"), "dim")
        t0 = time.perf_counter()
        try:
            sock = socket.create_connection((host, port), timeout=cfg["timeout"])
        except Exception as e:
            es, en = self.err_text(e, port)
            self.log(T(f"  [ERROR] {es}", f"  [ERROR] {en}"), "err")
            self.result("Telnet", target, "FAIL", (es, en))
            return
        ms = (time.perf_counter() - t0) * 1000
        try:
            ip = sock.getpeername()[0]
            self.log(T(f"  [OK] Conexión TCP establecida con {ip}:{port} en {ms:.0f} ms",
                       f"  [OK] TCP connection established with {ip}:{port} in {ms:.0f} ms"), "ok")
            if self.is_implicit(port, cfg):
                self.log(T("  [INFO] Este puerto usa TLS implícito: el servidor espera un handshake TLS",
                           "  [INFO] This port uses implicit TLS: the server expects a TLS handshake"), "info")
                self.log(T("         y no manda banner en texto plano. El puerto está abierto; el detalle",
                           "         and sends no plain-text banner. The port is open; see the"), "info")
                self.log(T("         está en la prueba TLS/OpenSSL.",
                           "         TLS/OpenSSL test for details."), "info")
                self.result("Telnet", target, "OK",
                            T(f"puerto abierto ({ms:.0f} ms)", f"port open ({ms:.0f} ms)"))
                return
            conv = SMTPConversation(sock, self.log)
            code, _ = conv.read_reply()
            if code != 220:
                self.log(T(f"  [WARN] Banner inesperado (código {code})",
                           f"  [WARN] Unexpected banner (code {code})"), "warn")
                conv.quit()
                self.result("Telnet", target, "WARN", T(f"banner {code}"))
                return
            code, ehlo = conv.send(f"EHLO {ehlo_identity(sock)}")
            ext = {l[4:].split()[0].upper() for l in ehlo[1:] if len(l) > 4 and l[4:].split()}
            conv.quit()
            if code != 250:
                self.result("Telnet", target, "WARN",
                            T(f"EHLO respondió {code}", f"EHLO returned {code}"))
                return
            has_tls = "STARTTLS" in ext
            tls_es = "anuncia STARTTLS" if has_tls else "sin STARTTLS"
            tls_en = "advertises STARTTLS" if has_tls else "no STARTTLS"
            self.log(T(f"  [OK] El servidor responde SMTP correctamente ({tls_es})",
                       f"  [OK] Server responds to SMTP correctly ({tls_en})"), "ok")
            self.result("Telnet", target, "OK",
                        T(f"banner 220, {tls_es} ({ms:.0f} ms)", f"banner 220, {tls_en} ({ms:.0f} ms)"))
        except Exception as e:
            es, en = self.err_text(e, port)
            self.log(T(f"  [ERROR] {es}", f"  [ERROR] {en}"), "err")
            self.result("Telnet", target, "FAIL", (es, en))
        finally:
            sock.close()

    # ------------------------------------------------------ TLS/OpenSSL ----
    def _tls_test(self, host, port, cfg):
        target = f"{host}:{port}"
        implicit = self.is_implicit(port, cfg)
        mode_es = "TLS implícito" if implicit else "STARTTLS"
        mode_en = "implicit TLS" if implicit else "STARTTLS"
        self.log("")
        self.log(T(f"--- TLS/OpenSSL {target}  ({mode_es}) ---",
                   f"--- TLS/OpenSSL {target}  ({mode_en}) ---"), "header")
        cmd = (f"openssl s_client -connect {host}:{port} -servername {host} -crlf" if implicit else
               f"openssl s_client -starttls smtp -connect {host}:{port} -servername {host} -crlf")
        self.log(T(f"  Equivalente: {cmd}", f"  Equivalent: {cmd}"), "dim")
        try:
            status, detail = self._tls_session(host, port, implicit, cfg["verify"], cfg)
        except ssl.SSLCertVerificationError as e:
            reason = e.verify_message or str(e)
            self.log(T(f"  [WARN] Certificado no válido: {reason}",
                       f"  [WARN] Invalid certificate: {reason}"), "warn")
            self.log(T("  Reintentando sin verificar el certificado para revisar el resto...",
                       "  Retrying without certificate verification to check the rest..."), "dim")
            try:
                status, (d_es, d_en) = self._tls_session(host, port, implicit, False, cfg)
                if status == "OK":
                    status = "WARN"
                detail = T(f"cert. no válido ({reason}); {d_es}", f"invalid cert ({reason}); {d_en}")
            except Exception as e2:
                status, detail = "FAIL", self.err_text(e2, port)
                self.log(T(f"  [ERROR] {detail[0]}", f"  [ERROR] {detail[1]}"), "err")
        except Exception as e:
            status, detail = "FAIL", self.err_text(e, port)
            self.log(T(f"  [ERROR] {detail[0]}", f"  [ERROR] {detail[1]}"), "err")
        self.result("TLS", target, status, detail)

    def _tls_session(self, host, port, implicit, verify, cfg):
        """Devuelve (estado, (detalle_es, detalle_en))."""
        ctx = tls_context(verify)
        raw = socket.create_connection((host, port), timeout=cfg["timeout"])
        ehlo_cmd = f"EHLO {ehlo_identity(raw)}"
        sock = raw
        try:
            if implicit:
                sock = ctx.wrap_socket(raw, server_hostname=host)
                self._log_tls_info(sock, verify)
                conv = SMTPConversation(sock, self.log)
                code, _ = conv.read_reply()
                if code != 220:
                    raise SMTPProtoError(f"Banner inesperado ({code})", f"Unexpected banner ({code})")
                code, ehlo = conv.send(ehlo_cmd)
            else:
                conv = SMTPConversation(raw, self.log)
                code, _ = conv.read_reply()
                if code != 220:
                    raise SMTPProtoError(f"Banner inesperado ({code})", f"Unexpected banner ({code})")
                code, ehlo = conv.send(ehlo_cmd)
                if not any("STARTTLS" in l.upper() for l in ehlo):
                    self.log(T("  [ERROR] El servidor no anuncia STARTTLS en este puerto.",
                               "  [ERROR] Server does not advertise STARTTLS on this port."), "err")
                    conv.quit()
                    return "FAIL", T("no ofrece STARTTLS", "STARTTLS not offered")
                code, _ = conv.send("STARTTLS")
                if code != 220:
                    raise SMTPProtoError(f"STARTTLS rechazado ({code})", f"STARTTLS rejected ({code})")
                sock = ctx.wrap_socket(raw, server_hostname=host)
                conv.sock, conv.buf = sock, b""
                self._log_tls_info(sock, verify)
                code, ehlo = conv.send(ehlo_cmd)

            cipher = sock.cipher()
            base = f"{sock.version()} {cipher[0] if cipher else ''}".strip()
            d_es = d_en = base
            status = "OK"

            mechs = set()
            for l in ehlo:
                body = l[4:].strip().upper()
                if body.startswith("AUTH ") or body.startswith("AUTH="):
                    mechs.update(body[5:].split())

            if cfg["user"] and not verify:
                # Nunca mandar credenciales si no se pudo comprobar con quién hablamos
                # (podría ser un intermediario haciéndose pasar por el servidor).
                self.log(T("  [WARN] No se enviaron las credenciales: el certificado no está verificado.",
                           "  [WARN] Credentials were not sent: the certificate is not verified."), "warn")
                status = "WARN"
                d_es += ", AUTH omitido (cert. no verificado)"
                d_en += ", AUTH skipped (cert. not verified)"
            elif cfg["user"] and sock.version() in ("TLSv1", "TLSv1.1"):
                # TLS 1.0 y 1.1 son obsoletos: se reportan, pero no se exponen credenciales.
                self.log(T(f"  [WARN] No se enviaron las credenciales: {sock.version()} es obsoleto.",
                           f"  [WARN] Credentials were not sent: {sock.version()} is obsolete."), "warn")
                status = "WARN"
                d_es += f", AUTH omitido ({sock.version()} obsoleto)"
                d_en += f", AUTH skipped ({sock.version()} obsolete)"
            elif cfg["user"]:
                ok = self._auth(conv, mechs, cfg["user"], cfg["password"])
                if ok is True:
                    d_es += ", AUTH OK"
                    d_en += ", AUTH OK"
                elif ok is False:
                    status = "FAIL"
                    d_es += ", AUTH falló"
                    d_en += ", AUTH failed"
                else:
                    status = "WARN"
                    d_es += ", AUTH no disponible"
                    d_en += ", AUTH not available"
            else:
                if mechs:
                    m = " ".join(sorted(mechs))
                    self.log(T(f"  Mecanismos AUTH ofrecidos: {m}", f"  AUTH mechanisms offered: {m}"), "dim")
                self.log(T("  [INFO] Sin usuario: se omitió la autenticación.",
                           "  [INFO] No username: authentication skipped."), "info")
            conv.quit()
            return status, (d_es, d_en)
        finally:
            for s in (sock, raw):
                try:
                    s.close()
                except Exception:
                    pass

    def _log_tls_info(self, sock, verified):
        cipher = sock.cipher() or ("?", "?", "?")
        self.log(f"  [OK] Handshake TLS: {sock.version()} | {cipher[0]} ({cipher[2]} bits)", "ok")
        cert = sock.getpeercert() if verified else None
        if not cert:
            cert = self._decode_der(sock.getpeercert(binary_form=True))
        if cert:
            subj = dict(x[0] for x in cert.get("subject", ()))
            iss = dict(x[0] for x in cert.get("issuer", ()))
            sans = [v for k, v in cert.get("subjectAltName", ()) if k == "DNS"]
            cn = subj.get("commonName", "?")
            issuer = f"{iss.get('organizationName', '')} {iss.get('commonName', '')}".strip()
            self.log(T(f"  Certificado CN : {cn}", f"  Certificate CN : {cn}"))
            self.log(T(f"  Emisor         : {issuer}", f"  Issuer         : {issuer}"))
            if sans:
                n = len(sans) - 6
                self.log(T(f"  SAN            : {', '.join(sans[:6])}" + (f" (+{n} más)" if n > 0 else ""),
                           f"  SAN            : {', '.join(sans[:6])}" + (f" (+{n} more)" if n > 0 else "")))
            na = cert.get("notAfter")
            if na:
                try:
                    days = int((ssl.cert_time_to_seconds(na) - time.time()) // 86400)
                    tag = "err" if days < 0 else "warn" if days < 15 else "plain"
                    st_es = "VENCIDO" if days < 0 else f"{days} días restantes"
                    st_en = "EXPIRED" if days < 0 else f"{days} days left"
                    self.log(T(f"  Válido hasta   : {na}  ({st_es})", f"  Valid until    : {na}  ({st_en})"), tag)
                except ValueError:
                    self.log(T(f"  Válido hasta   : {na}", f"  Valid until    : {na}"))
        if verified:
            self.log(T("  [OK] Certificado verificado (cadena de confianza y nombre de host)",
                       "  [OK] Certificate verified (chain of trust and host name)"), "ok")
        else:
            self.log(T("  [WARN] Certificado NO verificado en esta conexión",
                       "  [WARN] Certificate NOT verified on this connection"), "warn")

    @staticmethod
    def _decode_der(der):
        if not der:
            return None
        path = None
        try:
            fd, path = tempfile.mkstemp(suffix=".pem")
            with os.fdopen(fd, "w") as f:
                f.write(ssl.DER_cert_to_PEM_cert(der))
            return ssl._ssl._test_decode_cert(path)
        except Exception:
            return None
        finally:
            if path:
                try:
                    os.remove(path)
                except OSError:
                    pass

    def _auth(self, conv, mechs, user, pwd):
        if not mechs:
            self.log(T("  [WARN] El servidor no ofrece AUTH en este puerto "
                       "(normal en el 25 de un MX; usa 587 o 465 para enviar).",
                       "  [WARN] Server does not offer AUTH on this port "
                       "(normal on port 25 of an MX; use 587 or 465 to send)."), "warn")
            return None
        m = " ".join(sorted(mechs))
        self.log(T(f"  Mecanismos AUTH ofrecidos: {m}", f"  AUTH mechanisms offered: {m}"), "dim")
        b64 = lambda s: base64.b64encode(s.encode("utf-8")).decode("ascii")
        if "PLAIN" in mechs:
            token = b64(f"\0{user}\0{pwd}")
            code, lines = conv.send(f"AUTH PLAIN {token}",
                                    shown=T("AUTH PLAIN <usuario+contraseña en Base64 - oculto>",
                                            "AUTH PLAIN <username+password in Base64 - hidden>"))
        elif "LOGIN" in mechs:
            code, _ = conv.send("AUTH LOGIN")
            if code != 334:
                self.log(T(f"  [ERROR] AUTH LOGIN rechazado ({code})",
                           f"  [ERROR] AUTH LOGIN rejected ({code})"), "err")
                return False
            code, _ = conv.send(b64(user), shown=T(f"{b64(user)}   <- usuario '{user}' en Base64",
                                                   f"{b64(user)}   <- username '{user}' in Base64"))
            if code != 334:
                self.log(T(f"  [ERROR] Usuario rechazado ({code})",
                           f"  [ERROR] Username rejected ({code})"), "err")
                return False
            code, lines = conv.send(b64(pwd), shown=T("<contraseña en Base64 - oculta>",
                                                      "<password in Base64 - hidden>"))
        else:
            self.log(T("  [WARN] Solo hay mecanismos no soportados aquí (XOAUTH2, CRAM-MD5...).",
                       "  [WARN] Only unsupported mechanisms available (XOAUTH2, CRAM-MD5...)."), "warn")
            return None

        if code == 235:
            self.log(T(f"  [OK] Autenticación correcta para {user}",
                       f"  [OK] Authentication successful for {user}"), "ok")
            return True
        self.log(T(f"  [ERROR] Autenticación fallida (código {code})",
                   f"  [ERROR] Authentication failed (code {code})"), "err")
        joined = " ".join(lines).lower()
        if code == 535:
            self.log(T("         Usuario/contraseña incorrectos, o el proveedor exige contraseña de",
                       "         Wrong username/password, or the provider requires an app"), "warn")
            self.log(T("         aplicación / tiene SMTP AUTH deshabilitado para la cuenta.",
                       "         password / has SMTP AUTH disabled for the account."), "warn")
        if "smtp auth" in joined and "disabled" in joined:
            self.log(T("         Microsoft 365: SMTP AUTH está deshabilitado para el buzón o el tenant.",
                       "         Microsoft 365: SMTP AUTH is disabled for the mailbox or tenant."), "warn")
        return False

    # ------------------------------------------------------------- Ping ----
    def _ping(self, host, cfg):
        self.log("")
        self.log(f"--- Ping {host} ---", "header")
        n = cfg["ping_count"]
        if IS_WINDOWS:
            cmd = ["ping", "-n", str(n), "-w", str(cfg["timeout"] * 1000), host]
        else:
            cmd = ["ping", "-c", str(n), host]
        self.log(T(f"  Comando: {' '.join(cmd)}", f"  Command: {' '.join(cmd)}"), "dim")
        kwargs = {}
        if IS_WINDOWS:
            kwargs["creationflags"] = getattr(subprocess, "CREATE_NO_WINDOW", 0)
        try:
            proc = subprocess.run(cmd, capture_output=True, timeout=n * (cfg["timeout"] + 1) + 5, **kwargs)
        except FileNotFoundError:
            self.log(T("  [ERROR] El comando ping no está disponible en este equipo.",
                       "  [ERROR] The ping command is not available on this computer."), "err")
            self.result("Ping", host, "FAIL", T("ping no disponible", "ping not available"))
            return
        except subprocess.TimeoutExpired:
            self.log(T("  [ERROR] Ping excedió el tiempo límite.", "  [ERROR] Ping timed out."), "err")
            self.result("Ping", host, "FAIL", T("timeout"))
            return

        raw = proc.stdout + proc.stderr
        try:
            out = raw.decode("oem" if IS_WINDOWS else "utf-8", errors="replace")
        except LookupError:
            out = raw.decode("utf-8", errors="replace")
        lines = [l.rstrip() for l in out.splitlines() if l.strip()]
        for l in lines:
            self.log(f"    {l}", "server")   # salida del sistema: se copia tal cual
        ok = proc.returncode == 0 and "ttl" in out.lower()
        detail = lines[-1].strip()[:70] if lines else ""
        if ok:
            self.log(T("  [OK] El host responde a ICMP", "  [OK] Host responds to ICMP"), "ok")
            self.result("Ping", host, "OK", T(detail))
        else:
            self.log(T("  [WARN] Sin respuesta ICMP (puede estar bloqueado por firewall).",
                       "  [WARN] No ICMP response (may be blocked by a firewall)."), "warn")
            self.result("Ping", host, "WARN", T("sin respuesta ICMP", "no ICMP response"))

    # ---------------------------------------------------------- Resumen ----
    def _summary(self):
        if not self.results:
            return
        self.log("")
        self.log("=" * 78, "header")
        self.log(T(" RESUMEN", " SUMMARY"), "header")
        self.log("=" * 78, "header")
        self.log(T(f"  {'ESTADO':<6} {'PRUEBA':<7} {'OBJETIVO':<32} DETALLE",
                   f"  {'STATUS':<6} {'TEST':<7} {'TARGET':<32} DETAIL"), "dim")
        for test, target, st, d_es, d_en in self.results:
            self.log(T(f"  {st:<6} {test:<7} {target[:32]:<32} {d_es}",
                       f"  {st:<6} {test:<7} {target[:32]:<32} {d_en}"), STATUS_TAG[st])
        c = {k: sum(1 for r in self.results if r[2] == k) for k in ("OK", "WARN", "FAIL")}
        self.log("")
        self.log(T(f"  Total: {c['OK']} OK, {c['WARN']} advertencias, {c['FAIL']} fallos",
                   f"  Total: {c['OK']} OK, {c['WARN']} warnings, {c['FAIL']} failures"),
                 "err" if c["FAIL"] else "warn" if c["WARN"] else "ok")

    # -------------------------------------------------------------- PDF ----
    def export_pdf(self, path=None):
        if not self.report:
            messagebox.showwarning("Sin datos", "Primero ejecuta alguna prueba.")
            return False
        if path is None:
            ts = datetime.now().strftime("%Y-%m-%d_%H%M%S")
            path = filedialog.asksaveasfilename(defaultextension=".pdf", initialfile=f"Mail_Diagnostics_{ts}.pdf",
                                                filetypes=[("PDF", "*.pdf")])
            if not path:
                return False
        try:
            pdf = SimplePDF(footer=f"{APP_TITLE} {APP_VERSION}")
            pdf.title("Reporte de diagnóstico de correo")
            for text, _en, tag in list(self.report):
                pdf.line(text, PDF_COLORS.get(tag, (30, 30, 30)), bold=(tag == "header"))
            pdf.output(path)
            self.log_txt.config(state="normal")
            self.log_txt.insert("end", f"\n[OK] PDF generado: {path}\n", "ok")
            self.log_txt.see("end")
            self.log_txt.config(state="disabled")
            return True
        except Exception as e:
            messagebox.showerror("Error", f"No se pudo guardar el PDF:\n{e}")
            return False

    # ------------------------------------------------- Componentes ----
    def component_report(self):
        """Revisa, sin usar la red, todo lo que la app necesita. Devuelve (líneas, falta_ping)."""
        rows = []

        def row(ok, text):
            rows.append(("[OK]     " if ok else "[FALTA]  ") + text)

        row(True, f"Python {platform.python_version()} "
                  f"({'ejecutable compilado' if getattr(sys, 'frozen', False) else 'código fuente'})")
        tk_ver = str(self.root.tk.call("info", "patchlevel"))
        row(tk.TkVersion >= 8.6, f"Interfaz gráfica Tk {tk_ver}")
        import dns.version
        row(dns.version.version == "2.7.0", f"dnspython {dns.version.version}")
        row(ssl.HAS_TLSv1_2, f"TLS: {ssl.OPENSSL_VERSION}")
        if IS_WINDOWS:
            row(True, "Certificados raíz: almacén de certificados de Windows")
        else:
            n = (system_ca_pem() or "").count("BEGIN CERTIFICATE")
            row(n > 0, f"Certificados raíz del sistema: {n}" if n else
                "Certificados raíz: no se encontraron (la verificación TLS fallará)")
        servers = self._make_resolver(5).nameservers
        row(bool(servers), f"Servidores DNS del sistema: {len(servers)}" if servers else
            "Servidores DNS: el sistema no tiene ninguno configurado")
        has_ping = shutil.which("ping") is not None
        row(has_ping, "Comando ping" if has_ping else "Comando ping: no está instalado")
        return rows, not has_ping

    def show_components(self, first_run=False):
        rows, missing_ping = self.component_report()
        ok = all(r.startswith("[OK]") for r in rows)
        title = "Revisión inicial de componentes" if first_run else "Componentes"
        text = "\n".join(rows) + ("\n\nTodo está listo." if ok else "")
        if ok:
            messagebox.showinfo(title, text, parent=self.root)
        else:
            messagebox.showwarning(title, text, parent=self.root)
        if missing_ping:
            self.offer_ping_install()

    def first_run_check(self):
        """Solo en la versión compilada: la primera vez que se abre cada versión."""
        marker = os.path.join(config_dir(), "selfcheck.ok")
        try:
            with open(marker, encoding="utf-8") as f:
                if f.read().strip() == APP_VERSION:
                    return
        except OSError:
            pass
        self.show_components(first_run=True)
        try:
            os.makedirs(os.path.dirname(marker), exist_ok=True)
            with open(marker, "w", encoding="utf-8") as f:
                f.write(APP_VERSION)
        except OSError:
            pass

    def offer_ping_install(self):
        """Linux: ofrece instalar ping con el gestor de paquetes, solo con permiso."""
        cmd = ping_install_command()
        if cmd is None:
            messagebox.showinfo("ping", "Instala el comando ping con el gestor de paquetes de tu "
                                        "sistema. Las demás pruebas funcionan sin él.", parent=self.root)
            return
        if not messagebox.askyesno(
                "Instalar ping",
                "Falta el comando ping. ¿Quieres instalarlo ahora?\n\n"
                f"Se ejecutará:\n  {' '.join(cmd)}\n\n"
                "El sistema te pedirá tu contraseña de administrador. Las demás pruebas "
                "funcionan sin ping.", parent=self.root):
            return
        try:
            done = subprocess.run(cmd, capture_output=True, timeout=600).returncode == 0
        except (OSError, subprocess.SubprocessError):
            done = False
        if done and shutil.which("ping"):
            messagebox.showinfo("ping", "ping se instaló correctamente.", parent=self.root)
        else:
            messagebox.showwarning("ping", "No se pudo instalar ping (¿se canceló la contraseña?).",
                                   parent=self.root)


# --------------------------------------------- Funciones del sistema ----
CA_BUNDLES = (
    "/etc/ssl/cert.pem",                                  # macOS, Alpine, Arch
    "/etc/ssl/certs/ca-certificates.crt",                 # Debian, Ubuntu
    "/etc/pki/tls/certs/ca-bundle.crt",                   # Fedora, RHEL
    "/etc/pki/ca-trust/extracted/pem/tls-ca-bundle.pem",  # Fedora, RHEL (otra ruta)
    "/etc/ssl/ca-bundle.pem",                             # openSUSE
)
_CA_CACHE = {}
SYSTEM_BIN = "/usr/bin:/bin:/usr/sbin:/sbin"   # solo programas del sistema, nunca del PATH del usuario

def system_ca_pem():
    """Certificados raíz públicos del sistema, en texto PEM, o None.

    La versión compilada lleva su propio OpenSSL, que no sabe dónde guarda cada sistema
    sus certificados. En macOS se leen los llaveros del sistema con el comando `security`
    (incluye raíces corporativas instaladas por la empresa); si no, el archivo de
    certificados de la distribución. En Windows no hace falta: Python usa el almacén de
    Windows. No usa la red."""
    if "pem" in _CA_CACHE:
        return _CA_CACHE["pem"]
    pem = None
    if sys.platform == "darwin":
        try:
            out = subprocess.run(["/usr/bin/security", "find-certificate", "-a", "-p",
                                  "/System/Library/Keychains/SystemRootCertificates.keychain",
                                  "/Library/Keychains/System.keychain"],
                                 capture_output=True, timeout=30)
            if out.returncode == 0 and b"BEGIN CERTIFICATE" in out.stdout:
                pem = out.stdout.decode("ascii", "ignore")
        except (OSError, subprocess.SubprocessError):
            pass
    if pem is None and not IS_WINDOWS:
        for path in CA_BUNDLES:
            if os.path.isfile(path):
                try:
                    with open(path, encoding="ascii", errors="ignore") as f:
                        pem = f.read()
                    break
                except OSError:
                    pass
    _CA_CACHE["pem"] = pem
    return pem


def tls_context(verify):
    """Contexto TLS. Con verificación: certificados del sistema y comprobación del nombre."""
    ctx = ssl.create_default_context()
    if not verify:
        ctx.check_hostname = False
        ctx.verify_mode = ssl.CERT_NONE
        return ctx
    pem = None if IS_WINDOWS else system_ca_pem()
    if pem:
        try:
            ctx.load_verify_locations(cadata=pem)
        except ssl.SSLError:
            pass
    return ctx


def reports_dir():
    """Carpeta de los PDF automáticos. Compilada: Documentos/Mail Diagnostics/reportes."""
    base = os.environ.get("MAILDIAG_REPORTS_DIR")
    if not base:
        if getattr(sys, "frozen", False):
            base = os.path.join(os.path.expanduser("~"), "Documents", APP_TITLE)
        else:
            base = os.path.dirname(os.path.abspath(sys.argv[0]))
    return os.path.join(base, "reportes")


def config_dir():
    """Carpeta de configuración del usuario (solo guarda la marca de revisión inicial)."""
    if IS_WINDOWS:
        base = os.environ.get("APPDATA") or os.path.expanduser("~")
    elif sys.platform == "darwin":
        base = os.path.join(os.path.expanduser("~"), "Library", "Application Support")
    else:
        base = os.environ.get("XDG_CONFIG_HOME") or os.path.join(os.path.expanduser("~"), ".config")
    return os.path.join(base, APP_TITLE)


def ping_install_command():
    """Linux: comando fijo para instalar ping con permiso de administrador (pkexec), o None."""
    if IS_WINDOWS or sys.platform == "darwin" or not shutil.which("pkexec", path=SYSTEM_BIN):
        return None
    for manager, args in (("apt-get", ["install", "-y", "iputils-ping"]),
                          ("dnf", ["install", "-y", "iputils"]),
                          ("zypper", ["--non-interactive", "install", "iputils"]),
                          ("pacman", ["-S", "--noconfirm", "iputils"])):
        path = shutil.which(manager, path=SYSTEM_BIN)
        if path:
            return [shutil.which("pkexec", path=SYSTEM_BIN), path] + args
    return None


def main():
    if IS_WINDOWS:
        try:
            import ctypes
            ctypes.windll.shcore.SetProcessDpiAwareness(1)
        except Exception:
            pass
    root = tk.Tk()
    MailDiagnosticsApp(root)
    root.mainloop()


if __name__ == "__main__":
    main()
