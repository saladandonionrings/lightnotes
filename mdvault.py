#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
mdvault — notes Markdown façon Obsidian, multi-utilisateur, dans le navigateur.
Un seul fichier, aucune dépendance obligatoire.

Chaque utilisateur possède ses propres « espaces » (dossiers de notes privés,
isolés les uns des autres). Personne ne peut lire ou modifier les espaces
d'un autre utilisateur.

Utilisation :
    python3 mdvault.py [DONNEES] [-p PORT] [--host HOTE] [--no-browser]
    python3 mdvault.py [DONNEES] --add-user NOM      créer un utilisateur
    python3 mdvault.py [DONNEES] --passwd NOM        changer un mot de passe
    python3 mdvault.py [DONNEES] --del-user NOM      supprimer un utilisateur
    python3 mdvault.py [DONNEES] --list-users        lister les utilisateurs

    DONNEES : dossier des données (défaut : ./mdvault-data)
        users.json              comptes (mots de passe hachés avec scrypt)
        sessions.json           sessions actives (jetons hachés)
        spaces/<id>/<espace>/   notes de chaque utilisateur

Exposition sur un réseau : utilisez TLS (--cert/--key) ou un reverse proxy
HTTPS (--proxy). --signup ouvre l'inscription publique (fermée par défaut).

Raccourcis principaux (touche « ? » pour la liste complète) :
    Ctrl+K / Ctrl+O   palette : ouvrir, créer, rechercher
    Ctrl+E            basculer lecture / édition
    Ctrl+S            enregistrer (la sauvegarde est aussi automatique)
    Ctrl+\\            afficher / masquer le panneau de gauche
    Alt+N             nouvelle note
    [[                lien avec autocomplétion

Rendu plus complet (notes de bas de page, coloration du code…) :
    sudo apt install python3-markdown python3-pygments
"""

import argparse
import base64
import getpass
import hashlib
import hmac
import html
import json
import mimetypes
import os
import posixpath
import re
import secrets
import shutil
import ssl
import sys
import threading
import time
import traceback
import unicodedata
import urllib.parse
import webbrowser
from html.parser import HTMLParser
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path

try:
    import markdown as _markdown
except ImportError:  # moteur intégré
    _markdown = None

PYG_CSS = ''
if _markdown is not None:
    try:
        from pygments.formatters import HtmlFormatter
        from pygments.styles import get_style_by_name

        def _style(names):
            for n in names:
                try:
                    get_style_by_name(n)
                    return n
                except Exception:
                    pass
            return 'default'
        PYG_CSS = (HtmlFormatter(style=_style(['github-dark', 'monokai'])).get_style_defs('[data-theme=dark] .hl')
                   + '\n' + HtmlFormatter(style=_style(['default'])).get_style_defs('[data-theme=light] .hl'))
    except ImportError:
        PYG_CSS = ''

NOTE_EXT = ('.md', '.markdown')
IMG_EXT = {'png', 'jpg', 'jpeg', 'gif', 'webp', 'svg', 'bmp', 'avif'}
AUDIO_EXT = {'mp3', 'ogg', 'wav', 'm4a', 'flac', 'opus'}
VIDEO_EXT = {'mp4', 'webm', 'mov', 'mkv', 'ogv'}
SKIP_DIRS = {'node_modules', '__pycache__'}

# --- paramètres de sécurité ---
SESSION_IDLE = 12 * 3600          # inactivité maximale d'une session
SESSION_MAX = 7 * 24 * 3600       # durée de vie absolue d'une session
MAX_BODY = 5 * 1024 * 1024        # taille maximale d'une note envoyée
MAX_FORM = 16 * 1024              # taille maximale d'un formulaire
MAX_SPACES = 20                   # espaces par utilisateur
PW_MIN, PW_MAX = 10, 1024
USER_RE = re.compile(r'^[a-z0-9][a-z0-9_.-]{2,31}$')
SPACE_RE = re.compile(r'^[a-z0-9][a-z0-9_-]{0,39}$')
SCRYPT_N, SCRYPT_R, SCRYPT_P = 2 ** 15, 8, 1
HASH_SEM = threading.BoundedSemaphore(2)   # limite la mémoire consommée par scrypt
COMMON_PW = {'motdepasse', 'password', 'password123', '1234567890', '12345678910', 'azertyuiop',
             'qwertyuiop', 'motdepasse1', 'iloveyou12', 'administrateur', 'administrator'}

WIKILINK = re.compile(r'(!?)\[\[([^\[\]|#\n]*)(#[^\[\]|\n]*)?(?:\|([^\[\]\n]*))?\]\]')
TAG = re.compile(r'(?<![\w/&#\[\(\]`\\:="\'])#([^\W\d][\w/\-]*)')
MDLINK = re.compile(r'\]\(\s*<?([^)\s>]+?\.(?:md|markdown))>?(?:#[^)\s]*)?(?:\s+"[^"]*")?\s*\)', re.I)
_FENCE_SRC = r'^[ \t]*```.*?^[ \t]*```[ \t]*\r?$|^[ \t]*~~~.*?^[ \t]*~~~[ \t]*\r?$'
FENCE = re.compile('(' + _FENCE_SRC + ')', re.M | re.S)
CODE = re.compile('(' + _FENCE_SRC + r'|`[^`\n]+`)', re.M | re.S)
FRONT = re.compile(r'\A---[ \t]*\r?\n(.*?)\r?\n(?:---|\.\.\.)[ \t]*(?:\r?\n|\Z)', re.S)
HIGHLIGHT = re.compile(r'==(?=\S)(.+?)(?<=\S)==')
TASK_SRC = re.compile(r'^((?:[ \t]*>)*[ \t]*(?:[-*+]|\d+[.)])[ \t]+\[)([ xX])(\])(?=[ \t]|\r?$)', re.M)
TASK_HTML = re.compile(r'<li>(\s*<p>)?\s*\[([ xX])\](?=\s|<)')

ICONS = {
    'side': '<rect x="3" y="4" width="18" height="16" rx="2"/><path d="M9 4v16"/>',
    'rside': '<rect x="3" y="4" width="18" height="16" rx="2"/><path d="M15 4v16"/>',
    'plus': '<path d="M12 5v14M5 12h14"/>',
    'fileplus': '<path d="M14 3H7a2 2 0 0 0-2 2v14a2 2 0 0 0 2 2h10a2 2 0 0 0 2-2V8z"/><path d="M14 3v5h5M12 11v6M9 14h6"/>',
    'collapse': '<path d="m7 20 5-5 5 5M7 4l5 5 5-5"/>',
    'search': '<circle cx="11" cy="11" r="7"/><path d="m20 20-3.5-3.5"/>',
    'pencil': '<path d="M17 3a2.8 2.8 0 0 1 4 4L7.5 20.5 2 22l1.5-5.5z"/>',
    'eye': '<path d="M2 12s3.5-7 10-7 10 7 10 7-3.5 7-10 7S2 12 2 12z"/><circle cx="12" cy="12" r="3"/>',
    'dots': '<circle cx="12" cy="5" r="1"/><circle cx="12" cy="12" r="1"/><circle cx="12" cy="19" r="1"/>',
    'sun': '<circle cx="12" cy="12" r="4"/><path d="M12 2v2M12 20v2M4.9 4.9l1.4 1.4M17.7 17.7l1.4 1.4M2 12h2M20 12h2M4.9 19.1l1.4-1.4M17.7 6.3l1.4-1.4"/>',
    'moon': '<path d="M21 12.8A9 9 0 1 1 11.2 3a7 7 0 0 0 9.8 9.8z"/>',
    'home': '<path d="M3 10.5 12 3l9 7.5V20a1 1 0 0 1-1 1h-5v-6H9v6H4a1 1 0 0 1-1-1z"/>',
    'trash': '<path d="M3 6h18M8 6V4h8v2M6 6l1 14h10l1-14"/>',
    'chev': '<path d="m9 6 6 6-6 6"/>',
    'file': '<path d="M14 3H7a2 2 0 0 0-2 2v14a2 2 0 0 0 2 2h10a2 2 0 0 0 2-2V8z"/><path d="M14 3v5h5"/>',
    'help': '<circle cx="12" cy="12" r="9"/><path d="M9.5 9a2.5 2.5 0 1 1 3.5 2.3c-.6.3-1 .9-1 1.6V14M12 17h.01"/>',
    'copy': '<rect x="9" y="9" width="12" height="12" rx="2"/><path d="M5 15V5a2 2 0 0 1 2-2h10"/>',
    'cols': '<rect x="3" y="4" width="18" height="16" rx="2"/><path d="M12 4v16"/>',
    'width': '<path d="M3 12h18M7 8l-4 4 4 4M17 8l4 4-4 4"/>',
    'type': '<path d="M4 7V5h16v2M9 19h6M12 5v14"/>',
    'link': '<path d="M10 14a4 4 0 0 0 5.7 0l3-3a4 4 0 0 0-5.7-5.7l-1 1"/><path d="M14 10a4 4 0 0 0-5.7 0l-3 3a4 4 0 0 0 5.7 5.7l1-1"/>',
    'hash': '<path d="M4 9h16M4 15h16M10 3 8 21M16 3l-2 18"/>',
    'user': '<circle cx="12" cy="8" r="4"/><path d="M4 21a8 8 0 0 1 16 0"/>',
    'logout': '<path d="M9 21H5a2 2 0 0 1-2-2V5a2 2 0 0 1 2-2h4M16 17l5-5-5-5M21 12H9"/>',
    'spaces': '<rect x="3" y="3" width="7" height="7" rx="1.5"/><rect x="14" y="3" width="7" height="7" rx="1.5"/><rect x="3" y="14" width="7" height="7" rx="1.5"/><rect x="14" y="14" width="7" height="7" rx="1.5"/>',
    'lock': '<rect x="4" y="11" width="16" height="10" rx="2"/><path d="M8 11V7a4 4 0 0 1 8 0v4"/>',
}


def icon(name, cls='i'):
    return ('<svg class="%s" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" '
            'stroke-linecap="round" stroke-linejoin="round">%s</svg>' % (cls, ICONS[name]))


def esc(s):
    return html.escape(str(s), quote=True)


def slugify(value, sep='-'):
    """Même algorithme que l'extension toc de python-markdown."""
    value = unicodedata.normalize('NFKD', str(value)).encode('ascii', 'ignore').decode('ascii')
    value = re.sub(r'[^\w\s-]', '', value).strip().lower()
    return re.sub(r'[%s\s]+' % sep, sep, value)


# Identifiants utilisés par l'interface : un titre de note ne doit pas pouvoir les masquer.
RESERVED_IDS = {'app', 'side', 'center', 'top', 'main', 'scroller', 'right', 'tree', 'view', 'ntitle', 'words',
                'art', 'editor', 'src', 'preview', 'status', 'pos', 'wc', 'outline', 'outline-n', 'toasts', 'ov',
                'ac', 'peek', 'b-new', 'b-collapse', 'b-switch', 'b-theme', 'b-help', 'b-left', 'b-prev', 'b-more',
                'b-right', 'm-read', 'm-edit', 'q-new', 'q-search', 'mdv'}


def anchor(s):
    s = str(s)[:100]
    return 'u-' + s if s.lower() in RESERVED_IDS or s.lower().startswith('u-') else s


def stem(rel):
    name = rel.rsplit('/', 1)[-1]
    for e in NOTE_EXT:
        if name.lower().endswith(e):
            return name[:-len(e)]
    return name


def is_note(name):
    return name.lower().endswith(NOTE_EXT)


def split_front(text):
    m = FRONT.match(text)
    if m:
        return m.group(1), text[m.end():]
    return '', text


def split_code(text):
    """Liste alternant [texte, code, texte, code, …]."""
    return CODE.split(text)


def front_tags(meta):
    out = set()
    lines = meta.split('\n')
    for i, line in enumerate(lines):
        m = re.match(r'(?i)^(tags?)\s*:\s*(.*)$', line)
        if not m:
            continue
        v = m.group(2).strip()
        if v:
            out.update(x.strip(' "\'#') for x in v.strip('[]').replace(',', ' ').split() if x.strip(' "\'#'))
        else:
            for l2 in lines[i + 1:]:
                m2 = re.match(r'^\s*-\s*(.+)$', l2)
                if not m2:
                    break
                out.add(m2.group(1).strip(' "\'#'))
    return out


def plain_snippet(body, n=150):
    s = WIKILINK.sub(lambda m: m.group(4) or m.group(2), body)
    s = re.sub(r'```.*?```', ' ', s, flags=re.S)
    s = re.sub(r'!\[[^\]]*\]\([^)]*\)', ' ', s)
    s = re.sub(r'\[([^\]]*)\]\([^)]*\)', r'\1', s)
    s = re.sub(r'^\s*#{1,6}\s.*$', ' ', s, count=1, flags=re.M)
    s = re.sub(r'[#>*_`|=~\[\]]+|^\s*[-+]\s', ' ', s, flags=re.M)
    s = re.sub(r'\s+', ' ', s).strip()
    return s[:n] + ('…' if len(s) > n else '')


def atomic_write(p, content):
    p = Path(p)
    tmp = p.with_name('.' + p.name + '.mdvault-tmp')
    with open(tmp, 'w', encoding='utf-8', newline='') as f:
        f.write(content)
    if p.exists():
        try:
            shutil.copymode(p, tmp)
        except OSError:
            pass
    os.replace(tmp, p)


def write_private(p, obj):
    """Écriture atomique d'un fichier JSON lisible uniquement par son propriétaire."""
    p = Path(p)
    tmp = p.with_name('.' + p.name + '.tmp')
    fd = os.open(tmp, os.O_WRONLY | os.O_CREAT | os.O_TRUNC, 0o600)
    with os.fdopen(fd, 'w', encoding='utf-8') as f:
        json.dump(obj, f, ensure_ascii=False, indent=1)
        f.flush()
        os.fsync(f.fileno())
    os.replace(tmp, p)


def read_raw(p):
    with open(p, encoding='utf-8', errors='replace', newline='') as f:
        return f.read()


def ct_eq(a, b):
    """Comparaison en temps constant de deux chaînes."""
    return hmac.compare_digest(str(a or '').encode('utf-8', 'replace'), str(b or '').encode('utf-8', 'replace'))


# --------------------------------------------------------------------------
# Mots de passe
# --------------------------------------------------------------------------

def _b64(b):
    return base64.urlsafe_b64encode(b).decode('ascii').rstrip('=')


def _unb64(s):
    return base64.urlsafe_b64decode(s + '=' * (-len(s) % 4))


def hash_password(pw):
    salt = os.urandom(16)
    pwb = pw.encode('utf-8')
    if hasattr(hashlib, 'scrypt'):
        try:
            h = hashlib.scrypt(pwb, salt=salt, n=SCRYPT_N, r=SCRYPT_R, p=SCRYPT_P, maxmem=64 * 1024 * 1024, dklen=32)
            return 'scrypt$%d$%d$%d$%s$%s' % (SCRYPT_N, SCRYPT_R, SCRYPT_P, _b64(salt), _b64(h))
        except (ValueError, MemoryError):
            pass
    it = 600000
    return 'pbkdf2$%d$%s$%s' % (it, _b64(salt), _b64(hashlib.pbkdf2_hmac('sha256', pwb, salt, it)))


def verify_password(pw, stored):
    try:
        parts = stored.split('$')
        pwb = pw.encode('utf-8')
        if parts[0] == 'scrypt':
            n, r, p = (int(x) for x in parts[1:4])
            ref = _unb64(parts[5])
            h = hashlib.scrypt(pwb, salt=_unb64(parts[4]), n=n, r=r, p=p, maxmem=64 * 1024 * 1024, dklen=len(ref))
        elif parts[0] == 'pbkdf2':
            ref = _unb64(parts[3])
            h = hashlib.pbkdf2_hmac('sha256', pwb, _unb64(parts[2]), int(parts[1]))
        else:
            return False
        return hmac.compare_digest(h, ref)
    except Exception:
        return False


def password_problem(pw, name=''):
    if not isinstance(pw, str) or len(pw) < PW_MIN:
        return 'au moins %d caractères' % PW_MIN
    if len(pw) > PW_MAX:
        return 'trop long'
    low = pw.lower()
    if name and name.lower() in low:
        return 'ne doit pas contenir l\'identifiant'
    if low in COMMON_PW or len(set(pw)) < 4:
        return 'trop facile à deviner'
    return None


# --------------------------------------------------------------------------
# Comptes, sessions, espaces
# --------------------------------------------------------------------------

def _sha(tok):
    return hashlib.sha256(tok.encode('utf-8')).hexdigest()


class Store:
    def __init__(self, data, quota=0):
        self.data = Path(data).expanduser().resolve()
        self.data.mkdir(parents=True, exist_ok=True)
        try:
            os.chmod(self.data, 0o700)
        except OSError:
            pass
        self.spaces = self.data / 'spaces'
        self.spaces.mkdir(mode=0o700, exist_ok=True)
        self.ufile = self.data / 'users.json'
        self.sfile = self.data / 'sessions.json'
        self.lock = threading.RLock()
        self.quota = quota
        self._users, self._umt = {}, None
        self._sess = {}
        self._vaults = {}
        self._usage = {}
        self._dummy = None
        self._load_sessions()

    @property
    def dummy(self):
        if self._dummy is None:
            self._dummy = hash_password(secrets.token_urlsafe(18))
        return self._dummy

    # --- utilisateurs ---
    def _reload(self):
        try:
            mt = self.ufile.stat().st_mtime_ns
        except FileNotFoundError:
            self._users, self._umt = {}, None
            return
        if mt != self._umt:
            with open(self.ufile, encoding='utf-8') as f:
                self._users = json.load(f).get('users', {})
            self._umt = mt

    def _save_users(self):
        write_private(self.ufile, {'version': 1, 'users': self._users})
        self._umt = self.ufile.stat().st_mtime_ns

    def users(self):
        with self.lock:
            self._reload()
            return {k: dict(v, name=k) for k, v in self._users.items()}

    def get(self, name):
        if not isinstance(name, str):
            return None
        with self.lock:
            self._reload()
            u = self._users.get(name)
            return dict(u, name=name) if u else None

    def add_user(self, name, pw):
        h = hash_password(pw)
        with self.lock:
            self._reload()
            if name in self._users:
                raise ValueError('cet identifiant existe déjà')
            uid = secrets.token_hex(12)
            self._users[name] = {'id': uid, 'hash': h, 'pwv': 1, 'created': int(time.time())}
            self._save_users()
        d = self.spaces / uid
        d.mkdir(mode=0o700, exist_ok=True)
        (d / 'notes').mkdir(mode=0o700, exist_ok=True)
        return self.get(name)

    def set_password(self, name, pw):
        h = hash_password(pw)
        with self.lock:
            self._reload()
            u = self._users[name]
            u['hash'], u['pwv'] = h, int(u.get('pwv', 1)) + 1
            self._save_users()
            self.drop_sessions(name)
        return self.get(name)

    def delete_user(self, name):
        with self.lock:
            self._reload()
            u = self._users.pop(name, None)
            if not u:
                return False
            self._save_users()
            self.drop_sessions(name)
            for k in [k for k in self._vaults if k[0] == u['id']]:
                del self._vaults[k]
        d = self.spaces / u['id']
        if d.is_dir() and not d.is_symlink():
            shutil.rmtree(d, ignore_errors=True)
        return True

    # --- sessions (seul le hachage SHA-256 du jeton est conservé) ---
    @staticmethod
    def _alive(s, now):
        return now - s['c'] < SESSION_MAX and now - s['l'] < SESSION_IDLE

    def _load_sessions(self):
        try:
            with open(self.sfile, encoding='utf-8') as f:
                d = json.load(f)
        except (OSError, ValueError):
            d = {}
        now = time.time()
        self._sess = {k: v for k, v in d.items() if isinstance(v, dict) and self._alive(v, now)}

    def _save_sessions(self):
        write_private(self.sfile, self._sess)

    def new_session(self, user):
        tok = secrets.token_urlsafe(32)
        now = time.time()
        with self.lock:
            self._sess = {k: v for k, v in self._sess.items() if self._alive(v, now)}
            self._sess[_sha(tok)] = {'u': user['name'], 'id': user['id'], 'pwv': user['pwv'], 'c': now, 'l': now,
                                     'csrf': secrets.token_urlsafe(32)}
            self._save_sessions()
        return tok

    def session(self, tok):
        if not tok or len(tok) > 128:
            return None, None, None
        k, now = _sha(tok), time.time()
        with self.lock:
            s = self._sess.get(k)
            if not s:
                return None, None, None
            u = self.get(s['u'])
            if not self._alive(s, now) or not u or u['id'] != s['id'] or u['pwv'] != s['pwv']:
                del self._sess[k]
                self._save_sessions()
                return None, None, None
            if now - s['l'] > 120:
                s['l'] = now
                self._save_sessions()
            return k, s, u

    def drop_session(self, key):
        with self.lock:
            if self._sess.pop(key, None) is not None:
                self._save_sessions()

    def drop_sessions(self, name, keep=None):
        with self.lock:
            n = len(self._sess)
            self._sess = {k: v for k, v in self._sess.items() if v['u'] != name or k == keep}
            if len(self._sess) != n:
                self._save_sessions()

    def count_sessions(self, name):
        now = time.time()
        with self.lock:
            return sum(1 for v in self._sess.values() if v['u'] == name and self._alive(v, now))

    # --- espaces ---
    def user_dir(self, user):
        return self.spaces / user['id']

    def list_spaces(self, user):
        d = self.user_dir(user)
        try:
            return sorted(x.name for x in d.iterdir()
                          if SPACE_RE.match(x.name) and x.is_dir() and not x.is_symlink())
        except FileNotFoundError:
            return []

    def vault(self, user, space):
        if not isinstance(space, str) or not SPACE_RE.match(space):
            return None
        p = self.user_dir(user) / space
        if p.is_symlink() or not p.is_dir():
            return None
        key = (user['id'], space)
        with self.lock:
            v = self._vaults.get(key)
            if v is None:
                v = self._vaults[key] = Vault(p, '/s/' + space)
            return v

    def create_space(self, user, space):
        d = self.user_dir(user)
        d.mkdir(mode=0o700, exist_ok=True)
        (d / space).mkdir(mode=0o700)

    def delete_space(self, user, space):
        p = self.user_dir(user) / space
        with self.lock:
            self._vaults.pop((user['id'], space), None)
        if p.is_dir() and not p.is_symlink():
            shutil.rmtree(p)
        self._usage.pop(user['id'], None)

    # --- quota ---
    def usage(self, user):
        now, uid = time.time(), user['id']
        c = self._usage.get(uid)
        if c and now - c[0] < 10:
            return c[1]
        tot = 0
        for dp, dn, fn in os.walk(self.user_dir(user)):
            for f in fn:
                try:
                    tot += os.lstat(os.path.join(dp, f)).st_size
                except OSError:
                    pass
        self._usage[uid] = (now, tot)
        return tot

    def quota_ok(self, user, delta):
        if not self.quota or delta <= 0:
            return True
        if self.usage(user) + delta > self.quota:
            return False
        c = self._usage.get(user['id'])
        if c:
            self._usage[user['id']] = (c[0], c[1] + delta)
        return True


class Limiter:
    """Limite les tentatives de connexion par adresse IP et par identifiant."""
    WINDOW, IP_MAX = 900, 20

    def __init__(self):
        self.lock = threading.Lock()
        self.ip, self.user, self.signup = {}, {}, {}

    def _gc(self, now):
        if len(self.ip) > 5000:
            self.ip = {k: v for k, v in self.ip.items() if v and now - v[-1] < self.WINDOW}
        if len(self.user) > 5000:
            self.user = {k: v for k, v in self.user.items() if now - v[1] < 3600}
        if len(self.signup) > 5000:
            self.signup = {k: v for k, v in self.signup.items() if v and now - v[-1] < 3600}

    def wait(self, ip, user):
        now = time.time()
        with self.lock:
            w = 0
            lst = [t for t in self.ip.get(ip, ()) if now - t < self.WINDOW]
            if lst:
                self.ip[ip] = lst
            else:
                self.ip.pop(ip, None)
            if len(lst) >= self.IP_MAX:
                w = lst[0] + self.WINDOW - now
            c = self.user.get(user)
            if c and c[0] >= 5:
                w = max(w, c[1] + min(900, 30 * 2 ** min(c[0] - 5, 6)) - now)
            return max(0, int(w + 0.999))

    def fail(self, ip, user):
        now = time.time()
        with self.lock:
            self.ip.setdefault(ip, []).append(now)
            c = self.user.get(user, (0, 0))
            self.user[user] = (c[0] + 1, now)
            self._gc(now)

    def ok(self, user):
        with self.lock:
            self.user.pop(user, None)

    def signup_ok(self, ip):
        now = time.time()
        with self.lock:
            lst = [t for t in self.signup.get(ip, ()) if now - t < 3600]
            if len(lst) >= 3:
                return False
            lst.append(now)
            self.signup[ip] = lst
            self._gc(now)
            return True


# --------------------------------------------------------------------------
# Index d'un espace
# --------------------------------------------------------------------------

class Index:
    def __init__(self, root):
        self.notes, self.files, self.all_lower = [], {}, {}
        for dirpath, dirnames, filenames in os.walk(root):
            dirnames[:] = sorted((d for d in dirnames if not d.startswith('.') and d not in SKIP_DIRS), key=str.lower)
            for fn in sorted(filenames, key=str.lower):
                if fn.startswith('.'):
                    continue
                rel = Path(dirpath, fn).relative_to(root).as_posix()
                self.files.setdefault(fn.lower(), []).append(rel)
                self.all_lower[rel.lower()] = rel
                if is_note(fn):
                    self.notes.append(rel)
        self.noteset = set(self.notes)
        self.by_stem, self.by_path = {}, {}
        for rel in self.notes:
            self.by_stem.setdefault(stem(rel).lower(), []).append(rel)
            noext = rel[:-len(rel.rsplit('.', 1)[-1]) - 1]
            self.by_path[noext.lower()] = rel
        self._out = {}

    def resolve_note(self, target, from_rel=None):
        t = urllib.parse.unquote(target).strip().replace('\\', '/').lstrip('/')
        if not t:
            return from_rel
        low = t.lower()
        for e in NOTE_EXT:
            if low.endswith(e):
                low = low[:-len(e)]
                break
        if '/' in low:
            if low in self.by_path:
                return self.by_path[low]
            if from_rel:
                cand = posixpath.normpath(posixpath.join(posixpath.dirname(from_rel).lower(), low))
                if cand in self.by_path:
                    return self.by_path[cand]
            ends = [v for k, v in self.by_path.items() if k.endswith('/' + low)]
            if ends:
                return min(ends, key=len)
            low = low.rsplit('/', 1)[-1]
        cands = self.by_stem.get(low)
        if not cands:
            return None
        if len(cands) > 1 and from_rel:
            d = posixpath.dirname(from_rel)
            same = [c for c in cands if posixpath.dirname(c) == d]
            if same:
                return same[0]
        return min(cands, key=lambda c: (c.count('/'), len(c)))

    def resolve_file(self, target, from_rel=None):
        t = urllib.parse.unquote(target).strip().replace('\\', '/').lstrip('/')
        low = t.lower()
        if low in self.all_lower:
            return self.all_lower[low]
        if from_rel:
            cand = posixpath.normpath(posixpath.join(posixpath.dirname(from_rel), t)).lower()
            if cand in self.all_lower:
                return self.all_lower[cand]
        cands = self.files.get(low.rsplit('/', 1)[-1])
        return min(cands, key=len) if cands else None

    def out_links(self, vault, rel):
        if rel in self._out:
            return self._out[rel]
        info = vault.info(rel)
        res = set()
        if info:
            for t in info['wl']:
                r = self.resolve_note(t, rel)
                if r and r != rel:
                    res.add(r)
            for u in info['ml']:
                r = self.resolve_note(u, rel)
                if r and r != rel:
                    res.add(r)
        self._out[rel] = res
        return res


class Vault:
    def __init__(self, root, base):
        self.root = Path(root).resolve()
        self.base = base
        self.name = self.root.name
        self.lock = threading.Lock()
        self._cache = {}

    def url(self, rel):
        return self.base + '/note/' + urllib.parse.quote(rel)

    def index(self):
        return Index(self.root)

    def info(self, rel):
        p = self.root / rel
        try:
            mt = p.stat().st_mtime_ns
        except OSError:
            return None
        c = self._cache.get(rel)
        if c and c['mtime'] == mt:
            return c
        text = p.read_text(encoding='utf-8', errors='replace')
        meta, body = split_front(text)
        wl, ml, tags = [], [], set(front_tags(meta))
        for i, seg in enumerate(split_code(body)):
            if i % 2:
                continue
            for m in WIKILINK.finditer(seg):
                if m.group(2).strip():
                    wl.append(m.group(2))
            ml.extend(m.group(1) for m in MDLINK.finditer(seg) if '://' not in m.group(1))
            tags.update(m.group(1) for m in TAG.finditer(WIKILINK.sub(' ', seg)))
        c = dict(mtime=mt, text=text, meta=meta, body=body, wl=wl, ml=ml,
                 tags={t.lower() for t in tags if t})
        self._cache[rel] = c
        return c

    def search(self, idx, q, limit=300):
        terms = [t for t in q.lower().split() if t][:12]
        if not terms:
            return []
        tagq = terms[0][1:] if len(terms) == 1 and terms[0].startswith('#') and len(terms[0]) > 1 else None
        results = []
        for rel in idx.notes:
            info = self.info(rel)
            if not info:
                continue
            low, name = info['text'].lower(), rel.lower()
            if tagq:
                if not any(t == tagq or t.startswith(tagq + '/') for t in info['tags']):
                    continue
            elif not all(t in low or t in name for t in terms):
                continue
            score = sum(min(low.count(t), 20) for t in terms) + (50 if all(t in stem(rel).lower() for t in terms) else 0)
            snips, start, t0 = [], 0, terms[0]
            while len(snips) < 3:
                k = low.find(t0, start)
                if k < 0:
                    break
                a, b = max(0, k - 60), min(len(low), k + len(t0) + 80)
                s = esc(info['text'][a:b].replace('\n', ' '))
                for t in terms:
                    s = re.sub('(%s)' % re.escape(esc(t)), r'<mark>\1</mark>', s, flags=re.I)
                snips.append(('…' if a else '') + s + ('…' if b < len(low) else ''))
                start = k + len(t0)
            results.append((score, rel, snips))
        results.sort(key=lambda r: (-r[0], r[1].lower()))
        return results[:limit]


# --------------------------------------------------------------------------
# Assainissement du HTML produit (liste blanche stricte)
# --------------------------------------------------------------------------

SAFE_TAGS = {'a', 'abbr', 'b', 'blockquote', 'br', 'caption', 'code', 'col', 'colgroup', 'dd', 'del', 'details',
             'div', 'dl', 'dt', 'em', 'figcaption', 'figure', 'h1', 'h2', 'h3', 'h4', 'h5', 'h6', 'hr', 'i', 'img',
             'input', 'ins', 'kbd', 'li', 'mark', 'ol', 'p', 'pre', 's', 'samp', 'small', 'span', 'strong', 'sub',
             'summary', 'sup', 'table', 'tbody', 'td', 'tfoot', 'th', 'thead', 'tr', 'u', 'ul', 'var', 'audio',
             'video', 'source', 'iframe', 'q', 'wbr'}
DROP_TAGS = {'script', 'style', 'template', 'noscript', 'title', 'textarea', 'select', 'object', 'embed', 'svg',
             'math', 'iframe', 'frame', 'frameset', 'applet', 'head', 'xmp', 'noembed', 'noframes', 'plaintext',
             'button', 'option', 'canvas', 'dialog', 'portal'}
VOID_TAGS = {'br', 'hr', 'img', 'input', 'col', 'source', 'wbr'}
TAG_ATTRS = {
    'a': {'href', 'data-new', 'data-base'}, 'img': {'src', 'alt', 'width', 'height', 'loading'},
    'input': {'type', 'checked', 'disabled', 'data-i'}, 'audio': {'src', 'controls'},
    'video': {'src', 'controls'}, 'source': {'src', 'type'}, 'iframe': {'src'},
    'td': {'style', 'colspan', 'rowspan', 'align'}, 'th': {'style', 'colspan', 'rowspan', 'align'},
    'col': {'span'}, 'colgroup': {'span'}, 'ol': {'start'}, 'li': {'value'}, 'details': {'open'},
}
GLOBAL_ATTRS = {'class', 'id', 'title', 'lang', 'dir'}
_SCHEME = re.compile(r'^([a-z][a-z0-9+.\-]*):')


def safe_url(v, kind):
    probe = re.sub(r'[\x00-\x20\x7f]+', '', v).lower()
    m = _SCHEME.match(probe)
    if m:
        sch = m.group(1)
        if sch in ('http', 'https') or (kind == 'href' and sch == 'mailto'):
            return v.strip()
        if kind == 'img' and re.match(r'^data:image/(png|jpe?g|gif|webp|avif|bmp);base64,', probe):
            return v.strip()
        return None
    return v.strip()


class _Sanitizer(HTMLParser):
    def __init__(self, base):
        super().__init__(convert_charrefs=True)
        self.base, self.out, self.stack = base, [], []
        self.skip, self.depth = None, 0

    def handle_starttag(self, tag, attrs):
        if self.skip:
            if tag == self.skip:
                self.depth += 1
            return
        a = {}
        for k, v in attrs:
            if k not in a:
                a[k] = '' if v is None else v
        if tag == 'iframe' and not (a.get('class') == 'pdf' and a.get('src', '').startswith(self.base + '/note/')):
            self.skip, self.depth = tag, 1
            return
        if tag in DROP_TAGS and tag != 'iframe':
            if tag not in VOID_TAGS:
                self.skip, self.depth = tag, 1
            return
        if tag not in SAFE_TAGS:
            return
        allowed = TAG_ATTRS.get(tag, set()) | GLOBAL_ATTRS
        res = []
        for k, v in a.items():
            if k not in allowed:
                continue
            if k in ('href', 'src'):
                v = safe_url(v, 'img' if tag == 'img' else k)
                if v is None:
                    continue
            elif k == 'id':
                v = anchor(v)
            elif k == 'style':
                m = re.fullmatch(r'\s*text-align\s*:\s*(left|right|center)\s*;?\s*', v, re.I)
                if not m:
                    continue
                v = 'text-align:' + m.group(1).lower()
            elif k in ('width', 'height', 'colspan', 'rowspan', 'span', 'start', 'value', 'data-i'):
                if not re.fullmatch(r'\d{1,6}', v):
                    continue
            elif k == 'type':
                if tag == 'input' and v.lower() != 'checkbox':
                    return
                if tag == 'source' and not re.fullmatch(r'[\w.+-]+/[\w.+-]+', v):
                    continue
            elif k == 'align':
                if v.lower() not in ('left', 'right', 'center'):
                    continue
            elif k == 'loading':
                v = 'lazy'
            elif k in ('checked', 'disabled', 'controls', 'open'):
                v = ''
            res.append((k, v[:2000]))
        if tag == 'input' and ('type', 'checkbox') not in [(k, v.lower()) for k, v in res]:
            return
        if tag == 'a':
            href = a.get('href', '')
            if re.match(r'^\s*(https?:)?//', href, re.I):
                res.append(('rel', 'noopener noreferrer nofollow'))
        self.out.append('<%s%s>' % (tag, ''.join(' %s="%s"' % (k, esc(v)) if v != '' or k not in
                                                 ('checked', 'disabled', 'controls', 'open') else ' ' + k
                                                 for k, v in res)))
        if tag not in VOID_TAGS:
            self.stack.append(tag)

    def handle_endtag(self, tag):
        if self.skip:
            if tag == self.skip:
                self.depth -= 1
                if not self.depth:
                    self.skip = None
            return
        if tag in VOID_TAGS or tag not in self.stack:
            return
        while self.stack:
            t = self.stack.pop()
            self.out.append('</%s>' % t)
            if t == tag:
                break

    def handle_data(self, data):
        if not self.skip:
            self.out.append(html.escape(data, quote=False))

    def result(self):
        self.close()
        while self.stack:
            self.out.append('</%s>' % self.stack.pop())
        return ''.join(self.out)


def sanitize(markup, base):
    s = _Sanitizer(base)
    s.feed(markup)
    return s.result()


# --------------------------------------------------------------------------
# Rendu Markdown
# --------------------------------------------------------------------------

def render(vault, idx, rel, body, interactive=True):
    return sanitize(_render(vault, idx, rel, body, 0, None, interactive), vault.base)


def _render(vault, idx, rel, body, depth=0, seen=None, interactive=True):
    seen = (seen or set()) | {rel}
    toks = []
    base = vault.base

    def T(h):
        toks.append(h)
        return '@@MDV%d@@' % (len(toks) - 1)

    base_dir = posixpath.dirname(rel)

    def wl(m):
        bang, target, head, alias = m.groups()
        target = target.strip()
        head = (head or '')[1:].strip()
        alias = (alias or '').strip()
        ext = target.rsplit('.', 1)[-1].lower() if '.' in target.rsplit('/', 1)[-1] else ''
        if bang and ext and ext not in ('md', 'markdown'):
            f = idx.resolve_file(target, rel)
            if not f:
                return T('<span class="wikilink missing" title="Fichier introuvable">%s</span>' % esc(target))
            url = esc(vault.url(f))
            if ext in IMG_EXT:
                w = ''
                if re.fullmatch(r'\d+(x\d+)?', alias):
                    w = ' width="%s"' % alias.split('x')[0]
                return T('<img src="%s" alt="%s"%s loading="lazy">' % (url, esc(target), w))
            if ext in AUDIO_EXT:
                return T('<audio controls src="%s"></audio>' % url)
            if ext in VIDEO_EXT:
                return T('<video controls src="%s"></video>' % url)
            if ext == 'pdf':
                return T('<iframe class="pdf" src="%s"></iframe>' % url)
            return T('<a href="%s">📎 %s</a>' % (url, esc(target)))
        dest = idx.resolve_note(target, rel) if target else rel
        label = alias if (alias and not bang) else (target + (' › ' + head if head else '') if target else head)
        if not dest:
            return T('<a class="wikilink missing" href="#" data-new="%s" data-base="%s" '
                     'title="Note inexistante — cliquer pour la créer">%s</a>'
                     % (esc(target), esc(base_dir), esc(label)))
        href = esc(vault.url(dest) + ('#' + anchor(slugify(head)) if head else ''))
        if bang:
            if depth < 2 and dest not in seen:
                info = vault.info(dest)
                inner = _render(vault, idx, dest, info['body'], depth + 1, seen, False) if info else ''
                return T('<div class="embed"><div class="embed-title"><a class="wikilink" href="%s">%s</a></div>%s</div>'
                         % (href, esc(stem(dest)), inner))
            return T('<a class="wikilink" href="%s">↪ %s</a>' % (href, esc(label)))
        return T('<a class="wikilink" href="%s">%s</a>' % (href, esc(label)))

    def tag(m):
        t = m.group(1)
        return T('<a class="tag" href="%s/search?q=%s">#%s</a>' % (base, urllib.parse.quote('#' + t), esc(t)))

    def hl(m):
        return T('<mark>') + m.group(1) + T('</mark>')

    parts = split_code(body)
    for i in range(0, len(parts), 2):
        s = WIKILINK.sub(wl, parts[i])
        s = TAG.sub(tag, s)
        s = HIGHLIGHT.sub(hl, s)
        parts[i] = s
    src = ''.join(parts)

    if _markdown is not None:
        exts = ['extra', 'sane_lists', 'nl2br', 'toc']
        cfg = {'toc': {'slugify': slugify}}
        if PYG_CSS:
            exts.append('codehilite')
            cfg['codehilite'] = {'css_class': 'hl', 'guess_lang': False}
        out = _markdown.markdown(src, extensions=exts, extension_configs=cfg, output_format='html')
    else:
        out = mini_md(src)

    counter = [0]

    def task(m):
        i = counter[0]
        counter[0] += 1
        chk = ' checked' if m.group(2).lower() == 'x' else ''
        data = ' data-i="%d"' % i if (interactive and depth == 0) else ''
        return '<li class="task%s">%s<input type="checkbox" class="task-cb"%s disabled%s>' % (
            ' done' if chk else '', m.group(1) or '', data, chk)

    out = TASK_HTML.sub(task, out)
    out = re.sub(r'@@MDV(\d+)@@', lambda m: toks[int(m.group(1))] if int(m.group(1)) < len(toks) else '', out)
    out = re.sub(r'<blockquote>\s*<p>\[!([\w-]+)\][+-]?[ \t]*([^\n<]*)(?:<br\s*/?>)?\n?',
                 lambda m: '<blockquote class="callout c-%s"><div class="callout-title">%s</div><p>'
                 % (m.group(1).lower(), m.group(2).strip() or m.group(1).capitalize()), out)
    return out


# --- moteur Markdown intégré (utilisé si python3-markdown est absent) -------

LIST_RE = re.compile(r'^(\s*)([-*+]|\d+[.)])\s+(.*)$')
HR_RE = re.compile(r'^\s{0,3}((\*\s*){3,}|(-\s*){3,}|(_\s*){3,})$')
TABLE_SEP = re.compile(r'^\s*\|?\s*:?-+:?\s*(\|\s*:?-+:?\s*)*\|?\s*$')


def _inline(s):
    codes = []

    def code(m):
        codes.append(html.escape(m.group(1), quote=False))
        return '\x01%d\x01' % (len(codes) - 1)

    s = re.sub(r'`([^`]+)`', code, s)
    s = html.escape(s, quote=True)
    s = re.sub(r'!\[([^\]]*)\]\(\s*(?:&lt;)?([^)\s]+?)(?:&gt;)?(?:\s+&quot;.*?&quot;)?\s*\)', r'<img src="\2" alt="\1">', s)
    s = re.sub(r'\[([^\]]+)\]\(\s*(?:&lt;)?([^)\s]+?)(?:&gt;)?(?:\s+&quot;.*?&quot;)?\s*\)', r'<a href="\2">\1</a>', s)
    s = re.sub(r'&lt;(https?://[^\s&]+)&gt;', r'<a href="\1">\1</a>', s)
    s = re.sub(r'(\*\*|__)(?=\S)(.+?)(?<=\S)\1', r'<strong>\2</strong>', s)
    s = re.sub(r'(?<![\w*])\*(?=\S)(.+?)(?<=\S)\*(?![\w*])', r'<em>\1</em>', s)
    s = re.sub(r'(?<![\w_])_(?=\S)(.+?)(?<=\S)_(?![\w_])', r'<em>\1</em>', s)
    s = re.sub(r'~~(?=\S)(.+?)(?<=\S)~~', r'<del>\1</del>', s)
    s = re.sub('\x01(\\d+)\x01', lambda m: '<code>' + codes[int(m.group(1))] + '</code>', s)
    return s


def _block_start(line):
    return bool(re.match(r'\s*(#{1,6}\s|```|~~~|>)', line) or LIST_RE.match(line) or HR_RE.match(line))


def mini_md(src, _depth=0):
    if _depth > 20:
        return '<p>%s</p>' % html.escape(src, quote=False)
    lines = src.split('\n')
    out, i, n = [], 0, len(lines)
    while i < n:
        line = lines[i]
        if not line.strip():
            i += 1
            continue
        m = re.match(r'^\s*(```|~~~)\s*([\w+#.-]*)', line)
        if m:
            fence, lang = m.group(1), m.group(2)
            i += 1
            buf = []
            while i < n and not lines[i].strip().startswith(fence):
                buf.append(lines[i])
                i += 1
            i += 1
            cls = ' class="language-%s"' % esc(lang) if lang else ''
            out.append('<pre><code%s>%s</code></pre>' % (cls, html.escape('\n'.join(buf), quote=False)))
            continue
        m = re.match(r'^\s{0,3}(#{1,6})\s+(.*?)\s*#*\s*$', line)
        if m:
            lvl, txt = len(m.group(1)), m.group(2)
            out.append('<h%d id="%s">%s</h%d>' % (lvl, esc(slugify(txt)), _inline(txt), lvl))
            i += 1
            continue
        if HR_RE.match(line):
            out.append('<hr>')
            i += 1
            continue
        if line.lstrip().startswith('>'):
            buf = []
            while i < n and lines[i].lstrip().startswith('>'):
                buf.append(re.sub(r'^\s*>\s?', '', lines[i]))
                i += 1
            out.append('<blockquote>\n%s\n</blockquote>' % mini_md('\n'.join(buf), _depth + 1))
            continue
        if '|' in line and i + 1 < n and '-' in lines[i + 1] and TABLE_SEP.match(lines[i + 1]):
            def cells(row):
                row = row.strip()
                if row.startswith('|'):
                    row = row[1:]
                if row.endswith('|'):
                    row = row[:-1]
                return [c.strip() for c in row.split('|')]
            aligns = []
            for c in cells(lines[i + 1]):
                aligns.append('center' if c.startswith(':') and c.endswith(':') else
                              'right' if c.endswith(':') else 'left' if c.startswith(':') else '')

            def tr(cs, tg):
                r = []
                for j, c in enumerate(cs):
                    st = ' style="text-align:%s"' % aligns[j] if j < len(aligns) and aligns[j] else ''
                    r.append('<%s%s>%s</%s>' % (tg, st, _inline(c), tg))
                return '<tr>' + ''.join(r) + '</tr>'
            head = cells(line)
            i += 2
            rows = []
            while i < n and '|' in lines[i] and lines[i].strip():
                rows.append(tr(cells(lines[i]), 'td'))
                i += 1
            out.append('<table><thead>%s</thead><tbody>%s</tbody></table>' % (tr(head, 'th'), ''.join(rows)))
            continue
        m = LIST_RE.match(line)
        if m:
            base = len(m.group(1).expandtabs(4))
            ordered = m.group(2)[0].isdigit()
            items = []
            while i < n:
                l2 = lines[i]
                if not l2.strip():
                    j = i + 1
                    while j < n and not lines[j].strip():
                        j += 1
                    if j < n and (len(lines[j].expandtabs(4)) - len(lines[j].expandtabs(4).lstrip())) > base:
                        if items:
                            items[-1][1].append('')
                        i += 1
                        continue
                    if j < n and LIST_RE.match(lines[j]) and len(LIST_RE.match(lines[j]).group(1).expandtabs(4)) == base:
                        i = j
                        continue
                    break
                lm = LIST_RE.match(l2)
                indent = len(l2.expandtabs(4)) - len(l2.expandtabs(4).lstrip())
                if lm and indent == base:
                    items.append([lm.group(3), []])
                elif indent > base and items:
                    items[-1][1].append(l2.expandtabs(4))
                elif items and not _block_start(l2):
                    items[-1][0] += '\n' + l2.strip()
                else:
                    break
                i += 1
            tagname = 'ol' if ordered else 'ul'
            lis = []
            for first, sub in items:
                inner = '<br>\n'.join(_inline(x) for x in first.split('\n'))
                if any(s.strip() for s in sub):
                    ind = min(len(s) - len(s.lstrip()) for s in sub if s.strip())
                    inner += '\n' + mini_md('\n'.join(s[ind:] for s in sub), _depth + 1)
                lis.append('<li>%s</li>' % inner)
            out.append('<%s>\n%s\n</%s>' % (tagname, '\n'.join(lis), tagname))
            continue
        buf = []
        while i < n and lines[i].strip() and not (buf and _block_start(lines[i])):
            buf.append(lines[i].strip())
            i += 1
        out.append('<p>%s</p>' % '<br />\n'.join(_inline(b) for b in buf))
    return '\n'.join(out)


# --------------------------------------------------------------------------
# Interface : CSS
# --------------------------------------------------------------------------

CSS = r"""
:root,[data-theme=dark]{--bg:#1e1e1e;--bg2:#181818;--bg3:#262626;--hover:#2b2b2e;--fg:#dcddde;--fg2:#b8b8bd;--muted:#85858e;--faint:#56565e;
 --accent:#8b7cf6;--accent-h:#b0a5ff;--accent-bg:rgba(139,124,246,.16);--border:#2e2e33;--code:#262628;--mark:rgba(255,208,0,.3);
 --shadow:0 12px 40px rgba(0,0,0,.55);--ok:#4ec98f;--err:#f26d6d;--link:#a99bff;color-scheme:dark}
[data-theme=light]{--bg:#fff;--bg2:#f6f6f7;--bg3:#efeff2;--hover:#e9e9ed;--fg:#222226;--fg2:#45454d;--muted:#73737d;--faint:#a4a4ad;
 --accent:#6d4fe8;--accent-h:#5236d4;--accent-bg:rgba(109,79,232,.11);--border:#e2e2e7;--code:#f3f3f6;--mark:rgba(255,213,0,.5);
 --shadow:0 12px 40px rgba(20,20,40,.16);--ok:#1c9a60;--err:#d63a3a;--link:#5a3ed6;color-scheme:light}
:root{--lw:var(--side-w,272px);--rw:280px;--read-w:760px}
.no-left{--lw:0px}.no-right{--rw:0px}body.noright{--rw:0px}.wide{--read-w:1120px}
*{box-sizing:border-box}[hidden]{display:none!important}
*{scrollbar-width:thin;scrollbar-color:var(--border) transparent}
::-webkit-scrollbar{width:10px;height:10px}::-webkit-scrollbar-thumb{background:var(--border);border-radius:10px;border:2px solid transparent;background-clip:content-box}
::-webkit-scrollbar-thumb:hover{background-color:var(--faint)}
html,body{margin:0;height:100%;overflow:hidden}
body{background:var(--bg);color:var(--fg);font:15px/1.6 Inter,system-ui,-apple-system,"Segoe UI",Roboto,Ubuntu,Cantarell,"Noto Sans",sans-serif;-webkit-font-smoothing:antialiased}
::selection{background:var(--accent-bg)}
a{color:var(--link)}
form.inline{display:contents}
.i{width:18px;height:18px;flex:none}
#app{display:grid;grid-template-columns:var(--lw) minmax(0,1fr) var(--rw);height:100vh;transition:grid-template-columns .18s ease}
.resizing #app{transition:none}

/* ---- panneau gauche ---- */
#side{background:var(--bg2);border-right:1px solid var(--border);display:flex;flex-direction:column;position:relative;min-width:0;overflow:hidden}
.no-left #side{border-right:0}
.side-head{display:flex;align-items:center;gap:2px;padding:9px 8px 4px 14px;min-height:46px}
.vault{flex:1;font-weight:650;color:var(--fg);white-space:nowrap;overflow:hidden;text-overflow:ellipsis;font-size:14px;text-decoration:none}
.ib{display:inline-flex;align-items:center;justify-content:center;width:30px;height:30px;padding:0;border:0;border-radius:6px;background:transparent;color:var(--muted);cursor:pointer;flex:none}
.ib:hover{background:var(--hover);color:var(--fg)}.ib.on{color:var(--accent)}
.searchbtn{display:flex;align-items:center;gap:8px;margin:4px 10px 6px;padding:7px 10px;border:1px solid var(--border);border-radius:8px;background:var(--bg);color:var(--muted);cursor:pointer;font:inherit;font-size:13.5px;text-align:left}
.searchbtn:hover{border-color:var(--faint);color:var(--fg2)}.searchbtn span{flex:1}
kbd{font:11px/1 ui-monospace,SFMono-Regular,Menlo,monospace;padding:3px 5px;border:1px solid var(--border);border-bottom-width:2px;border-radius:4px;color:var(--muted);background:var(--bg3);white-space:nowrap}
.side-nav{display:flex;flex-direction:column;padding:2px 6px 4px}
.side-nav a,.tree-row{display:flex;align-items:center;gap:7px;padding:4px 8px;border-radius:6px;color:var(--fg2);font-size:13.5px;text-decoration:none;cursor:pointer;user-select:none;min-height:28px}
.side-nav a:hover,.tree-row:hover{background:var(--hover);color:var(--fg)}
.side-nav a.on{color:var(--fg);background:var(--hover)}
.side-nav .i{width:16px;height:16px;color:var(--muted)}
.side-scroll{flex:1;overflow:auto;padding:0 6px 14px}
.sec{display:flex;align-items:center;justify-content:space-between;font-size:11px;font-weight:650;letter-spacing:.07em;text-transform:uppercase;color:var(--faint);padding:14px 8px 4px;list-style:none;cursor:default}
summary.sec{cursor:pointer}summary.sec::-webkit-details-marker{display:none}
#tree ul{list-style:none;margin:0;padding:0}
#tree ul ul{margin-left:14px;padding-left:4px;border-left:1px solid var(--border)}
#tree summary{list-style:none}#tree summary::-webkit-details-marker{display:none}
.tree-row .chev{width:14px;height:14px;transition:transform .15s;color:var(--faint)}
#tree details[open]>summary .chev{transform:rotate(90deg)}
.tree-row .name{flex:1;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
.tree-row .add{opacity:0;width:22px;height:22px}.tree-row .add .i{width:15px;height:15px}.tree-row:hover .add{opacity:1}
a.tree-row{padding-left:29px}
a.tree-row.current{background:var(--accent-bg);color:var(--fg);font-weight:550}
.tags-box{padding:2px 6px 8px}
a.tag{display:inline-block;padding:0 8px;margin:2px 1px;border-radius:999px;background:var(--accent-bg);color:var(--link);font-size:12.5px;line-height:1.75;text-decoration:none}
a.tag:hover{background:var(--accent);color:#fff}a.tag .n{opacity:.55;margin-left:4px;font-size:11px}
.side-foot{display:flex;align-items:center;gap:2px;padding:6px 8px;border-top:1px solid var(--border)}
.side-foot .sp{flex:1}.side-foot .muted{font-size:12px;color:var(--faint);padding:0 6px;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
.resizer{position:absolute;top:0;right:-3px;width:7px;height:100%;cursor:col-resize;z-index:3}
.resizer:hover,.resizer.drag{background:linear-gradient(90deg,transparent 2px,var(--accent) 2px,var(--accent) 4px,transparent 4px)}

/* ---- zone centrale ---- */
#center{display:flex;flex-direction:column;min-width:0;overflow:hidden;background:var(--bg)}
#top{display:flex;align-items:center;gap:4px;height:46px;padding:0 8px;border-bottom:1px solid transparent;flex:none;transition:border-color .15s}
#top.scrolled,.editing #top{border-bottom-color:var(--border)}
.crumbs{flex:1;min-width:0;display:flex;align-items:center;gap:6px;color:var(--muted);font-size:13.5px;white-space:nowrap;overflow:hidden;padding:0 6px}
.crumbs .sep{color:var(--faint)}.crumbs b{color:var(--fg2);font-weight:550;overflow:hidden;text-overflow:ellipsis}
.dot{width:7px;height:7px;border-radius:50%;background:var(--accent);flex:none;opacity:0;transition:opacity .2s}.is-dirty .dot{opacity:1}
.seg{display:inline-flex;background:var(--bg3);border-radius:8px;padding:2px;margin:0 4px}
.seg button{display:inline-flex;align-items:center;gap:6px;border:0;background:transparent;color:var(--muted);font:inherit;font-size:13px;padding:4px 11px;border-radius:6px;cursor:pointer}
.seg button .i{width:15px;height:15px}.seg button:hover{color:var(--fg)}
.seg button.on{background:var(--bg);color:var(--fg);box-shadow:0 1px 3px rgba(0,0,0,.28)}
#scroller{flex:1;overflow:auto;min-height:0}
#main{padding:34px 48px 140px}
.content{max-width:var(--read-w);margin:0 auto}
.editing #scroller{overflow:hidden}.editing #main{padding:0;height:100%}

/* ---- note ---- */
.title{font-size:2.15em;font-weight:720;line-height:1.2;letter-spacing:-.01em;margin:0 0 .2em -6px;padding:2px 6px;border-radius:7px;outline:none;word-break:break-word}
.title[contenteditable]:hover{background:var(--hover)}.title:focus{background:var(--bg3)}
.meta{color:var(--muted);font-size:13px;margin:0 0 1.8em;display:flex;gap:6px 16px;flex-wrap:wrap;align-items:center}
.meta .tag{font-size:12px}
details.fm{border:1px solid var(--border);border-radius:8px;padding:6px 12px;margin:-.8em 0 1.8em;font-size:13.5px;background:var(--bg2)}
details.fm summary{cursor:pointer;color:var(--muted)}details.fm pre{margin:6px 0 2px;white-space:pre-wrap;font-size:13px}
.md{font-size:16px;line-height:1.75;color:var(--fg);overflow-wrap:break-word}
.md h1,.md h2,.md h3,.md h4,.md h5,.md h6{line-height:1.3;margin:1.7em 0 .55em;font-weight:680;scroll-margin-top:16px;letter-spacing:-.005em}
.md>:first-child{margin-top:0}
.md h1{font-size:1.8em}.md h2{font-size:1.45em}.md h3{font-size:1.22em}.md h4{font-size:1.08em}.md h5,.md h6{font-size:1em;color:var(--fg2)}
.md h1.dup{display:none}
.md p,.md ul,.md ol{margin:.75em 0}.md li{margin:.25em 0}.md li::marker{color:var(--muted)}
.md ul ul,.md ol ol,.md ul ol,.md ol ul{margin:.2em 0}
.md a{color:var(--link);text-decoration:none}.md a:hover{text-decoration:underline;text-underline-offset:3px}
.md a.missing{color:var(--muted);text-decoration:underline dashed;text-underline-offset:3px;cursor:pointer}
.md strong{font-weight:680;color:var(--fg)}
.md blockquote{margin:1.1em 0;padding:.15em 1.1em;border-left:3px solid var(--accent);color:var(--fg2)}
.md .callout{color:var(--fg);background:color-mix(in srgb,var(--accent) 10%,transparent);border-radius:8px;padding:.4em 1.1em}
.callout-title{font-weight:650;margin:.35em 0 .15em;color:var(--accent);text-transform:capitalize}
.md p:empty{display:none}
.c-warning,.c-caution,.c-attention{--accent:#e3a008}.c-danger,.c-error,.c-bug,.c-failure,.c-fail{--accent:#ef5350}
.c-tip,.c-success,.c-check,.c-done,.c-hint{--accent:#2fb380}.c-question,.c-faq,.c-help{--accent:#ea8a1a}.c-example{--accent:#9b7cf6}.c-quote,.c-cite{--accent:#8a8a92}.c-info,.c-todo{--accent:#3b9ae1}
code,pre,textarea.mono{font-family:"JetBrains Mono","Fira Code",ui-monospace,SFMono-Regular,"DejaVu Sans Mono",Menlo,monospace}
.md code{background:var(--code);padding:.12em .4em;border-radius:5px;font-size:.86em;color:var(--fg)}
.md pre{position:relative;background:var(--code);padding:14px 16px;border-radius:9px;overflow:auto;font-size:13.5px;line-height:1.55;margin:1em 0;border:1px solid var(--border)}
.md pre code{background:none;padding:0;font-size:inherit}
.md .hl{margin:1em 0}.md .hl pre{margin:0}.hl,.hl pre{background:var(--code)!important}
.copy{position:absolute!important;top:6px;right:6px;opacity:0;background:var(--bg3)!important;transition:opacity .15s}
pre:hover .copy{opacity:1}
.md table{border-collapse:collapse;margin:1.1em 0;display:block;overflow:auto;font-size:.94em}
.md th,.md td{border:1px solid var(--border);padding:7px 12px}.md th{background:var(--bg2);font-weight:650;text-align:left}
.md tr:nth-child(even) td{background:color-mix(in srgb,var(--bg2) 55%,transparent)}
.md img,.md video{max-width:100%;border-radius:6px}.md iframe.pdf{width:100%;height:75vh;border:1px solid var(--border);border-radius:8px}
.md hr{border:0;border-top:1px solid var(--border);margin:2.2em 0}
mark{background:var(--mark);color:inherit;padding:.05em .15em;border-radius:3px}
li.task{list-style:none;position:relative}li.task>input{position:absolute;left:-1.55em;top:.42em;margin:0}
li.task>p:first-child{margin:0}
li.task.done{color:var(--muted)}li.task.done>input{opacity:.8}
.task-cb{appearance:none;-webkit-appearance:none;width:16px;height:16px;border:1.6px solid var(--faint);border-radius:4px;background:transparent;cursor:pointer;display:inline-grid;place-content:center;vertical-align:middle}
.task-cb:disabled{cursor:default}.task-cb:not(:disabled):hover{border-color:var(--accent)}
.task-cb:checked{background:var(--accent);border-color:var(--accent)}
.task-cb:checked::after{content:"";width:8px;height:4.5px;border:2px solid #fff;border-top:0;border-right:0;transform:translateY(-1px) rotate(-45deg)}
.embed{border-left:2px solid var(--accent);padding:.3em 1.1em .4em;margin:1.2em 0;background:var(--bg2);border-radius:0 8px 8px 0}
.embed-title{font-size:12.5px;font-weight:600;text-transform:uppercase;letter-spacing:.04em;margin-top:.3em}
.embed .md,.embed{font-size:.96em}

/* ---- panneau droit ---- */
#right{background:var(--bg2);border-left:1px solid var(--border);overflow:auto;min-width:0;font-size:13.5px}
.no-right #right{border-left:0}
.panel{padding:6px 10px 30px}
.panel .sec{padding-top:16px}.panel .sec .n{background:var(--bg3);border-radius:10px;padding:0 7px;font-size:11px;color:var(--muted);letter-spacing:0}
.panel a.item{display:block;padding:5px 8px;border-radius:6px;color:var(--fg2);text-decoration:none}
.panel a.item:hover{background:var(--hover);color:var(--fg)}
.panel .nm{display:block;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
.panel .ctx{display:block;font-size:12px;color:var(--muted);line-height:1.45;margin-top:1px;display:-webkit-box;-webkit-line-clamp:2;-webkit-box-orient:vertical;overflow:hidden}
.panel .empty{color:var(--faint);font-size:12.5px;padding:2px 8px;margin:0}
#outline a{display:block;padding:3px 8px 3px 10px;border-left:2px solid var(--border);color:var(--muted);text-decoration:none;white-space:nowrap;overflow:hidden;text-overflow:ellipsis;font-size:13px}
#outline a:hover{color:var(--fg)}#outline a.active{color:var(--fg);border-left-color:var(--accent)}
#outline .l2{padding-left:20px}#outline .l3{padding-left:30px}#outline .l4,#outline .l5,#outline .l6{padding-left:40px}

/* ---- éditeur ---- */
#editor{height:100%;display:flex;flex-direction:column}
.edwrap{flex:1;min-height:0;display:grid;grid-template-columns:1fr 1fr}
.edwrap.nopreview{grid-template-columns:1fr}.edwrap.nopreview #preview{display:none}
#src{display:block;width:100%;height:100%;resize:none;border:0;outline:none;background:var(--bg);color:var(--fg);
 font:16px/1.75 Inter,system-ui,-apple-system,"Segoe UI",Roboto,Ubuntu,sans-serif;padding:32px max(32px,calc((100% - var(--read-w))/2)) 45vh;tab-size:4;caret-color:var(--accent)}
.mono #src{font-family:"JetBrains Mono","Fira Code",ui-monospace,"DejaVu Sans Mono",monospace;font-size:14.5px;line-height:1.7}
#preview{overflow:auto;border-left:1px solid var(--border);padding:32px 36px 45vh;background:var(--bg)}
.edfoot{height:28px;flex:none;display:flex;align-items:center;gap:18px;padding:0 14px;border-top:1px solid var(--border);font-size:12px;color:var(--muted);background:var(--bg2)}
.edfoot .sp{flex:1}.status.ok{color:var(--ok)}.status.err{color:var(--err);font-weight:600}
#ac{position:fixed;z-index:45;min-width:260px;max-width:440px;background:var(--bg3);border:1px solid var(--border);border-radius:9px;box-shadow:var(--shadow);padding:4px;font-size:13.5px}
#ac div{display:flex;align-items:center;gap:8px;padding:5px 9px;border-radius:6px;cursor:pointer;white-space:nowrap}
#ac div span{overflow:hidden;text-overflow:ellipsis}#ac div.sel{background:var(--accent-bg)}#ac small{color:var(--muted);margin-left:auto;padding-left:12px;overflow:hidden;text-overflow:ellipsis}
#ac .i{width:15px;height:15px;color:var(--muted)}#ac .m,.pitem .m{color:var(--accent-h);font-weight:700}

/* ---- palette, dialogues, menus, toasts ---- */
#ov{position:fixed;inset:0;background:rgba(0,0,0,.5);display:flex;justify-content:center;align-items:flex-start;padding-top:11vh;z-index:50;animation:fade .12s}
@keyframes fade{from{opacity:0}}
.modal{width:min(660px,94vw);background:var(--bg3);border:1px solid var(--border);border-radius:12px;box-shadow:var(--shadow);overflow:hidden;animation:pop .14s ease-out}
@keyframes pop{from{transform:translateY(-6px) scale(.985);opacity:0}}
.modal input.big{width:100%;border:0;border-bottom:1px solid var(--border);background:transparent;color:var(--fg);font:inherit;font-size:16.5px;padding:15px 18px;outline:none}
.plist{max-height:min(440px,58vh);overflow:auto;padding:6px}
.psec{font-size:11px;font-weight:650;text-transform:uppercase;letter-spacing:.07em;color:var(--faint);padding:9px 10px 4px}
.pitem{display:flex;align-items:center;gap:10px;padding:7px 10px;border-radius:7px;cursor:pointer;min-height:36px}
.pitem.sel{background:var(--accent-bg)}.pitem .i{width:16px;height:16px;color:var(--muted)}
.pitem .pn{white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
.pitem .pp{margin-left:auto;padding-left:12px;color:var(--muted);font-size:12.5px;white-space:nowrap;overflow:hidden;text-overflow:ellipsis;max-width:45%}
.pitem .pc{display:flex;flex-direction:column;min-width:0}.pitem .snip{color:var(--muted);font-size:12.5px;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
.pfoot{display:flex;gap:16px;flex-wrap:wrap;padding:8px 16px;border-top:1px solid var(--border);color:var(--muted);font-size:12px}
.pfoot kbd{margin-right:3px}
.dialog{padding:20px}.dialog h3{margin:0 0 6px;font-size:16px}.dialog p{margin:0 0 12px;color:var(--fg2);font-size:14px}
.field{width:100%;padding:9px 12px;margin-top:8px;border:1px solid var(--border);border-radius:8px;background:var(--bg);color:var(--fg);font:inherit;outline:none}
.field:focus{border-color:var(--accent);box-shadow:0 0 0 3px var(--accent-bg)}
.btns{display:flex;justify-content:flex-end;gap:8px;margin-top:18px}
.btn{display:inline-flex;align-items:center;gap:7px;font:inherit;font-size:13.5px;padding:7px 14px;border-radius:8px;border:1px solid var(--border);background:var(--bg);color:var(--fg);cursor:pointer;text-decoration:none}
.btn:hover{border-color:var(--faint)}.btn .i{width:16px;height:16px}
.btn.primary{background:var(--accent);border-color:var(--accent);color:#fff}.btn.primary:hover{filter:brightness(1.08)}
.btn.danger{background:var(--err);border-color:var(--err);color:#fff}
.help table{width:100%;border-collapse:collapse;font-size:13.5px}.help td{padding:6px 4px;border-bottom:1px solid var(--border)}.help td:last-child{text-align:right}
.help h4{margin:14px 0 4px;font-size:11px;text-transform:uppercase;letter-spacing:.07em;color:var(--faint)}
.menu{position:fixed;z-index:45;min-width:240px;background:var(--bg3);border:1px solid var(--border);border-radius:10px;box-shadow:var(--shadow);padding:5px;animation:pop .1s ease-out}
.menu button{display:flex;width:100%;align-items:center;gap:10px;border:0;background:none;color:var(--fg);font:inherit;font-size:13.5px;padding:7px 10px;border-radius:6px;cursor:pointer;text-align:left}
.menu button:hover{background:var(--hover)}.menu button .i{width:16px;height:16px;color:var(--muted)}
.menu .danger,.menu .danger .i{color:var(--err)}.menu hr{border:0;border-top:1px solid var(--border);margin:4px 2px}
.menu .kb{margin-left:auto;color:var(--faint);font-size:11.5px}
#toasts{position:fixed;bottom:18px;right:18px;display:flex;flex-direction:column;gap:8px;z-index:60;pointer-events:none}
.toast{background:var(--bg3);border:1px solid var(--border);border-left:3px solid var(--accent);padding:9px 14px;border-radius:9px;box-shadow:var(--shadow);font-size:13.5px;animation:pop .16s ease-out;max-width:380px}
.toast.err{border-left-color:var(--err)}.toast.ok{border-left-color:var(--ok)}
#peek{position:fixed;z-index:40;width:min(480px,92vw);max-height:360px;overflow:auto;background:var(--bg);border:1px solid var(--border);border-radius:11px;box-shadow:var(--shadow);padding:14px 20px 16px;animation:pop .12s ease-out}
#peek .peek-title{font-weight:700;font-size:15px;margin-bottom:6px}#peek .md{font-size:14px;line-height:1.65}#peek .md h1.dup{display:none}

/* ---- pages ---- */
.page-title{font-size:2em;font-weight:720;margin:0 0 .25em;letter-spacing:-.01em}
.lead{color:var(--muted);margin:0 0 1.4em}
.quick{display:flex;gap:8px;flex-wrap:wrap;margin:0 0 30px}
.cards{display:grid;grid-template-columns:repeat(auto-fill,minmax(230px,1fr));gap:12px}
.card{display:flex;flex-direction:column;gap:4px;padding:13px 15px;border:1px solid var(--border);border-radius:11px;background:var(--bg2);color:var(--fg);text-decoration:none;transition:border-color .15s,transform .15s}
.card:hover{border-color:var(--accent);transform:translateY(-1px)}
.card b{font-weight:620;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
.card p{margin:0;color:var(--muted);font-size:13px;line-height:1.5;display:-webkit-box;-webkit-line-clamp:3;-webkit-box-orient:vertical;overflow:hidden;flex:1}
.card small{color:var(--faint);font-size:12px}
.h3{font-size:12px;font-weight:650;text-transform:uppercase;letter-spacing:.07em;color:var(--faint);margin:0 0 10px}
.sres{display:block;padding:12px 14px;margin:0 -14px;border-radius:9px;color:var(--fg);text-decoration:none}
.sres:hover{background:var(--hover)}.sres b{font-weight:620}.sres small{color:var(--muted);margin-left:8px}
.sres .snip{color:var(--muted);font-size:13.5px;margin-top:3px}
.searchbig{display:flex;gap:8px;margin:0 0 20px}.searchbig .field{margin:0;font-size:15px}

/* ---- connexion, espaces, compte ---- */
html.authpage,html.authpage body{overflow:auto;height:auto;min-height:100%}
.auth-wrap{min-height:100vh;display:flex;justify-content:center;align-items:flex-start;padding:9vh 16px 48px}
.auth-card{width:min(400px,100%);background:var(--bg2);border:1px solid var(--border);border-radius:14px;padding:26px 26px 22px;box-shadow:var(--shadow)}
.auth-wide{width:min(780px,100%)}
.brand{display:flex;align-items:center;gap:9px;font-weight:700;font-size:16px;color:var(--fg);text-decoration:none}
.brand .i{color:var(--accent)}
.auth-h{font-size:1.45em;font-weight:700;margin:18px 0 6px}
.lbl{display:block;font-size:13px;color:var(--fg2);margin-top:14px}
.alert{padding:9px 12px;border-radius:8px;font-size:13.5px;margin:12px 0 4px;border:1px solid var(--border)}
.alert.err{border-color:var(--err);color:var(--err);background:color-mix(in srgb,var(--err) 9%,transparent)}
.alert.ok{border-color:var(--ok);color:var(--ok);background:color-mix(in srgb,var(--ok) 9%,transparent)}
.auth-foot{margin-top:18px;font-size:13px;color:var(--muted);text-align:center}
.topbar{display:flex;align-items:center;gap:8px;margin-bottom:8px;flex-wrap:wrap}.topbar .sp{flex:1}
.topbar .who{color:var(--muted);font-size:13.5px}
.box{border:1px solid var(--border);border-radius:12px;padding:16px 18px 18px;margin:18px 0 0;background:var(--bg)}
.box h2{font-size:15px;margin:0 0 4px}.box p{margin:0;color:var(--muted);font-size:13.5px}
.box.danger{border-color:color-mix(in srgb,var(--err) 45%,var(--border))}
.row{display:flex;gap:8px;flex-wrap:wrap;align-items:flex-end}.row .field{flex:1;min-width:180px}
select.field{appearance:auto}

/* ---- petits écrans ---- */
@media (max-width:1100px){
 :root{--rw:0px}
 #right{position:fixed;top:0;right:0;bottom:0;width:300px;z-index:30;transform:translateX(105%);transition:transform .2s;box-shadow:var(--shadow)}
 .show-right #right{transform:none}
}
@media (max-width:760px){
 :root,.no-left{--lw:0px}
 #side{position:fixed;top:0;left:0;bottom:0;width:min(300px,86vw);z-index:31;transform:translateX(-105%);transition:transform .2s;box-shadow:var(--shadow)}
 .show-left #side{transform:none}
 #main{padding:22px 18px 100px}
 .seg button span{display:none}
 .edwrap{grid-template-columns:1fr!important}#preview{display:none!important}
 #src{padding:22px 18px 45vh}
 .auth-card{padding:20px 16px}
}
"""

# --------------------------------------------------------------------------
# Interface : JavaScript
# --------------------------------------------------------------------------

JS = r"""
(function(){
'use strict';
const MDV=window.MDV,B=MDV.base,NP=B+'/note/',D=document.documentElement;let TOKEN=MDV.csrf;
const NOTES=MDV.notes.map(([p,n])=>({p,n,pl:p.toLowerCase(),nl:n.toLowerCase()}));
const $=(s,r)=>(r||document).querySelector(s),$$=(s,r)=>[...(r||document).querySelectorAll(s)];
const ICON=n=>'<svg class="i" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round">'+(MDV.icons[n]||'')+'</svg>';
const escH=s=>String(s).replace(/[&<>"']/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
const enc=p=>NP+p.split('/').map(encodeURIComponent).join('/');
const dirOf=p=>p.includes('/')?p.slice(0,p.lastIndexOf('/')):'';
const LS={get(k,d){try{const v=localStorage.getItem('mdv-'+k);return v===null?d:JSON.parse(v);}catch(e){return d;}},
          set(k,v){try{localStorage.setItem('mdv-'+k,JSON.stringify(v));}catch(e){}}};
const SK=k=>k+':'+B;
const sc=$('#scroller');

async function api(url,data,retry){
  const h={'X-CSRF':TOKEN};let opt={headers:h,credentials:'same-origin'};
  if(data!==undefined){h['Content-Type']='application/json';opt={method:'POST',headers:h,credentials:'same-origin',body:JSON.stringify(data)};}
  const r=await fetch(B+url,opt);let j={};try{j=await r.json();}catch(e){}
  if(r.status===401||(r.status===403&&j.code==='csrf')){
    if(!retry){try{const c=await fetch('/api/csrf',{credentials:'same-origin'});if(c.ok){TOKEN=(await c.json()).csrf;return api(url,data,true);}}catch(e){}}
    const e=new Error('session expirée — reconnectez-vous dans un autre onglet pour ne rien perdre');e.status=401;throw e;
  }
  if(!r.ok){const e=new Error(j.error||('HTTP '+r.status));e.status=r.status;throw e;}
  return j;
}

/* ---------- toasts ---------- */
function toast(msg,kind,ms){
  let box=$('#toasts');if(!box){box=document.createElement('div');box.id='toasts';document.body.appendChild(box);}
  const t=document.createElement('div');t.className='toast '+(kind||'');t.textContent=msg;box.appendChild(t);
  setTimeout(()=>{t.style.transition='opacity .3s';t.style.opacity='0';setTimeout(()=>t.remove(),320);},ms||2600);
}
const flash=LS.get('flash',null);if(flash){LS.set('flash',null);setTimeout(()=>toast(flash,'ok'),150);}

/* ---------- overlay / dialogues ---------- */
let ovEl=null;
function openOverlay(inner,onClose){
  closeOverlay();ovEl=document.createElement('div');ovEl.id='ov';
  ovEl.innerHTML='<div class="modal">'+inner+'</div>';ovEl._close=onClose;
  ovEl.addEventListener('mousedown',e=>{if(e.target===ovEl)closeOverlay();});
  document.body.appendChild(ovEl);return ovEl.firstChild;
}
function closeOverlay(){if(ovEl){const f=ovEl._close;ovEl.remove();ovEl=null;if(f)f();}}
function ask(title,value,okLabel,hint){
  return new Promise(res=>{let done=false;
    const m=openOverlay('<div class="dialog"><h3>'+escH(title)+'</h3>'+(hint?'<p>'+escH(hint)+'</p>':'')+
      '<input class="field" spellcheck="false" value="'+escH(value||'')+'"><div class="btns"><button class="btn" data-x>Annuler</button>'+
      '<button class="btn primary" data-ok>'+escH(okLabel||'OK')+'</button></div></div>',()=>{if(!done){done=true;res(null);}});
    const inp=$('input',m);inp.focus();inp.select();
    const ok=()=>{const v=inp.value.trim();done=true;closeOverlay();res(v||null);};
    inp.addEventListener('keydown',e=>{if(e.key==='Enter'){e.preventDefault();ok();}});
    $('[data-ok]',m).onclick=ok;$('[data-x]',m).onclick=()=>closeOverlay();
  });
}
function confirmBox(title,text,okLabel,danger,cancelLabel){
  return new Promise(res=>{let done=false;
    const m=openOverlay('<div class="dialog"><h3>'+escH(title)+'</h3><p>'+escH(text)+'</p><div class="btns">'+
      '<button class="btn" data-x>'+escH(cancelLabel||'Annuler')+'</button><button class="btn '+(danger?'danger':'primary')+'" data-ok>'+escH(okLabel||'OK')+'</button></div></div>',
      ()=>{if(!done){done=true;res(false);}});
    const ok=$('[data-ok]',m);ok.focus();
    ok.onclick=()=>{done=true;closeOverlay();res(true);};$('[data-x]',m).onclick=()=>closeOverlay();
  });
}
function showHelp(){
  const k=(a,b)=>'<tr><td>'+a+'</td><td>'+b.split('+').map(x=>'<kbd>'+x+'</kbd>').join(' ')+'</td></tr>';
  const m=openOverlay('<div class="dialog help"><h3>Raccourcis clavier</h3>'+
    '<h4>Général</h4><table>'+k('Palette : ouvrir, créer, rechercher','Ctrl+K')+k('Basculer lecture / édition','Ctrl+E')+
    k('Nouvelle note','Alt+N')+k('Panneau de gauche','Ctrl+\\')+k('Changer de thème','Alt+T')+k('Cette aide','?')+'</table>'+
    '<h4>Édition</h4><table>'+k('Enregistrer (aussi automatique)','Ctrl+S')+k('Gras','Ctrl+B')+k('Italique','Ctrl+I')+
    k('Lien [[…]] avec autocomplétion','Ctrl+K')+k('Case à cocher sur la ligne','Ctrl+Entrée')+k('Surligner ==…==','Ctrl+Maj+H')+
    k('Barrer ~~…~~','Ctrl+Maj+X')+k('Indenter / désindenter','Tab')+k('Désindenter','Maj+Tab')+'</table>'+
    '<p class="muted" style="margin-top:14px;font-size:13px">Tapez <kbd>[[</kbd> pour lier une note, avec autocomplétion. Survolez un lien pour voir un aperçu de la note.</p>'+
    '<div class="btns"><button class="btn primary" data-ok>Fermer</button></div></div>');
  const b=$('[data-ok]',m);b.focus();b.onclick=closeOverlay;
}

/* ---------- menus ---------- */
let menuEl=null;
function closeMenu(){if(menuEl){menuEl.remove();menuEl=null;}}
function openMenu(anchor,entries){
  closeMenu();menuEl=document.createElement('div');menuEl.className='menu';
  entries.forEach(en=>{
    if(!en){menuEl.appendChild(document.createElement('hr'));return;}
    const b=document.createElement('button');if(en.cls)b.className=en.cls;
    b.innerHTML=ICON(en.icon)+'<span>'+escH(en.label)+'</span>'+(en.kb?'<span class="kb">'+escH(en.kb)+'</span>':'');
    b.onclick=()=>{closeMenu();en.act();};menuEl.appendChild(b);
  });
  document.body.appendChild(menuEl);
  const r=anchor.getBoundingClientRect();
  menuEl.style.top=Math.min(innerHeight-menuEl.offsetHeight-8,r.bottom+6)+'px';
  menuEl.style.left=Math.max(8,Math.min(innerWidth-menuEl.offsetWidth-8,r.right-menuEl.offsetWidth))+'px';
  setTimeout(()=>document.addEventListener('mousedown',function h(e){
    if(!menuEl||!menuEl.contains(e.target)){closeMenu();document.removeEventListener('mousedown',h);}}),0);
}

/* ---------- thème et panneaux ---------- */
function themeIcon(){const b=$('#b-theme');if(b){b.innerHTML=ICON(D.dataset.theme==='dark'?'sun':'moon');b.title=D.dataset.theme==='dark'?'Thème clair (Alt+T)':'Thème sombre (Alt+T)';}}
function toggleTheme(){D.dataset.theme=D.dataset.theme==='dark'?'light':'dark';LS.set('theme',D.dataset.theme);themeIcon();}
themeIcon();$('#b-theme').onclick=toggleTheme;
const narrowR=()=>matchMedia('(max-width:1100px)').matches,narrowL=()=>matchMedia('(max-width:760px)').matches;
function toggleLeft(){if(narrowL())D.classList.toggle('show-left');else{D.classList.toggle('no-left');LS.set('left',!D.classList.contains('no-left'));}}
function toggleRight(){if(narrowR())D.classList.toggle('show-right');else{D.classList.toggle('no-right');LS.set('right',!D.classList.contains('no-right'));}}
$('#b-left').onclick=toggleLeft;
const bR=$('#b-right');if(bR)bR.onclick=toggleRight;
sc.addEventListener('mousedown',()=>{D.classList.remove('show-left','show-right');});
const rz=$('#side .resizer');
if(rz)rz.addEventListener('mousedown',e=>{
  e.preventDefault();rz.classList.add('drag');D.classList.add('resizing');
  const mv=ev=>D.style.setProperty('--side-w',Math.min(560,Math.max(190,ev.clientX))+'px');
  const up=()=>{rz.classList.remove('drag');D.classList.remove('resizing');removeEventListener('mousemove',mv);removeEventListener('mouseup',up);
    LS.set('sidew',parseInt(D.style.getPropertyValue('--side-w'))||0);};
  addEventListener('mousemove',mv);addEventListener('mouseup',up);
});
$('#b-help').onclick=showHelp;

/* ---------- arborescence ---------- */
const openSet=new Set(LS.get(SK('open'),[]));
$$('#tree details').forEach(d=>{
  const p=d.dataset.path;if(openSet.has(p))d.open=true;
  d.addEventListener('toggle',()=>{d.open?openSet.add(p):openSet.delete(p);LS.set(SK('open'),[...openSet]);});
});
$('#b-collapse').onclick=()=>{$$('#tree details').forEach(d=>d.open=false);openSet.clear();LS.set(SK('open'),[]);};
const curRow=$('#tree a.current');
if(curRow){const s=$('.side-scroll');s.scrollTop=Math.max(0,curRow.offsetTop-s.clientHeight/2);}
$('#tree').addEventListener('click',e=>{const b=e.target.closest('button.add');if(b){e.preventDefault();e.stopPropagation();newNote(b.dataset.folder);}});

/* ---------- notes : création, récentes ---------- */
async function newNote(base,name){
  if(!name)name=await ask(base?'Nouvelle note dans « '+base+' »':'Nouvelle note','', 'Créer','Astuce : « dossier/nom » pour créer dans un sous-dossier.');
  if(!name)return;
  try{const j=await api('/api/new',{name,base:base||''});location.href=j.url;}catch(e){toast('Création impossible : '+e.message,'err');}
}
$('#b-new').onclick=()=>newNote('');
const qn=$('#q-new');if(qn)qn.onclick=()=>newNote('');
document.addEventListener('click',e=>{
  const a=e.target.closest('a.wikilink.missing[data-new]');
  if(a){e.preventDefault();if(a.dataset.new)newNote(a.dataset.base||'',a.dataset.new);}
});
function pushRecent(p){const r=LS.get(SK('recent'),[]).filter(x=>x!==p);r.unshift(p);LS.set(SK('recent'),r.slice(0,40));}

/* ---------- recherche floue ---------- */
function fuzzy(q,t){
  q=q.toLowerCase().replace(/\s+/g,'');if(!q)return[0,[]];
  const s=t.toLowerCase();let last=-1,score=0;const idx=[];
  const sub=s.indexOf(q);
  if(sub>=0){for(let i=0;i<q.length;i++)idx.push(sub+i);
    return[100+(sub===0?30:0)+(sub>0&&/[\s\/_\-.]/.test(s[sub-1])?15:0)-s.length*0.1,idx];}
  for(const ch of q){const k=s.indexOf(ch,last+1);if(k<0)return null;
    idx.push(k);score+=(k===last+1?6:0)+(k===0||/[\s\/_\-.]/.test(s[k-1])?8:0)-Math.min(k-last-1,6)*0.4;last=k;}
  return[score-s.length*0.1,idx];
}
function hl(name,idx){const set=new Set(idx);let o='';for(let i=0;i<name.length;i++){const c=escH(name[i]);o+=set.has(i)?'<span class="m">'+c+'</span>':c;}return o;}
function go(p,e){if(e&&(e.ctrlKey||e.metaKey))window.open(enc(p),'_blank','noopener');else location.href=enc(p);}

/* ---------- palette ---------- */
function openPalette(initial){
  const m=openOverlay('<input class="big" placeholder="Ouvrir ou créer une note… (ou chercher dans le contenu)" autocomplete="off" spellcheck="false">'+
    '<div class="plist"></div><div class="pfoot"><span><kbd>↑</kbd><kbd>↓</kbd>naviguer</span><span><kbd>↵</kbd>ouvrir</span>'+
    '<span><kbd>Ctrl</kbd><kbd>↵</kbd>nouvel onglet</span><span><kbd>Échap</kbd>fermer</span></div>');
  const inp=$('input',m),list=$('.plist',m);let items=[],sel=0,timer=null,seq=0;
  const noteItem=(n,idx,head)=>({p:n.p,head,act:e=>go(n.p,e),
    html:ICON('file')+'<span class="pn">'+hl(n.n,idx)+'</span><span class="pp">'+escH(dirOf(n.p))+'</span>'});
  function draw(){
    list.innerHTML=items.length?items.map((it,i)=>(it.head?'<div class="psec">'+escH(it.head)+'</div>':'')+
      '<div class="pitem'+(i===sel?' sel':'')+'" data-i="'+i+'">'+it.html+'</div>').join(''):'<div class="psec">Aucune note</div>';
    const s=$('.pitem.sel',list);if(s)s.scrollIntoView({block:'nearest'});
  }
  function compute(){
    const q=inp.value.trim(),out=[];
    if(!q){
      const rec=LS.get(SK('recent'),[]),seen=new Set();
      rec.forEach(p=>{const n=NOTES.find(x=>x.p===p);if(n){out.push(noteItem(n,[],seen.size?null:'Récentes'));seen.add(p);}});
      let first=true;NOTES.forEach(n=>{if(!seen.has(n.p)&&out.length<80){out.push(noteItem(n,[],first?'Toutes les notes':null));first=false;}});
    }else{
      const res=[];
      for(const n of NOTES){let r=fuzzy(q,n.n);if(r){res.push([r[0]+20,n,r[1]]);continue;}r=fuzzy(q,n.p);if(r)res.push([r[0]-10,n,[]]);}
      res.sort((a,b)=>b[0]-a[0]);res.slice(0,50).forEach(([s,n,idx],i)=>out.push(noteItem(n,idx,i?null:'Notes')));
      const ql=q.toLowerCase(),exact=NOTES.some(n=>n.nl===ql||n.pl.replace(/\.(md|markdown)$/,'')===ql);
      let fa=true;
      if(!exact){out.push({action:1,head:'Actions',html:ICON('plus')+'<span class="pn">Créer la note « <b>'+escH(q)+'</b> »</span>',act:()=>newNote('',q)});fa=false;}
      out.push({action:1,head:fa?'Actions':null,html:ICON('search')+'<span class="pn">Chercher « '+escH(q)+' » dans toutes les notes</span>',act:()=>location.href=B+'/search?q='+encodeURIComponent(q)});
    }
    items=out;sel=0;draw();
    clearTimeout(timer);
    if(q.length>=2){const my=++seq;timer=setTimeout(async()=>{
      try{const j=await api('/api/search?q='+encodeURIComponent(q));if(my!==seq)return;
        const extra=j.results.slice(0,6).map((r,i)=>({p:r.path,head:i?null:'Dans le contenu',act:e=>go(r.path,e),
          html:ICON('hash')+'<span class="pc"><span class="pn">'+escH(r.name)+'</span><span class="snip">'+r.snip+'</span></span>'}));
        if(extra.length){const pos=items.findIndex(it=>it.action);items.splice(pos<0?items.length:pos,0,...extra);draw();}
      }catch(e){}},200);}
  }
  inp.addEventListener('input',compute);
  inp.addEventListener('keydown',e=>{
    if(e.key==='ArrowDown'){e.preventDefault();sel=Math.min(items.length-1,sel+1);draw();}
    else if(e.key==='ArrowUp'){e.preventDefault();sel=Math.max(0,sel-1);draw();}
    else if(e.key==='Enter'){e.preventDefault();const it=items[sel];if(it){const ev={ctrlKey:e.ctrlKey,metaKey:e.metaKey};closeOverlay();it.act(ev);}}
  });
  list.addEventListener('mousemove',e=>{const d=e.target.closest('.pitem');if(d&&+d.dataset.i!==sel){sel=+d.dataset.i;$$('.pitem',list).forEach(x=>x.classList.toggle('sel',+x.dataset.i===sel));}});
  list.addEventListener('click',e=>{const d=e.target.closest('.pitem');if(d){const it=items[+d.dataset.i];closeOverlay();it.act(e);}});
  inp.value=initial||'';compute();inp.focus();
}
$('#b-switch').onclick=()=>openPalette();
const qs=$('#q-search');if(qs)qs.onclick=()=>openPalette();

/* ---------- aperçu au survol ---------- */
const peekCache=new Map();let peekT=null,peekEl=null,peekFor=null,peekPend=null;
function hidePeek(){clearTimeout(peekT);peekPend=null;if(peekEl){peekEl.remove();peekEl=null;peekFor=null;}}
document.addEventListener('mouseover',e=>{
  if(e.target.closest('#peek')){clearTimeout(peekT);return;}
  const a=e.target.closest('a.wikilink:not(.missing),.panel a.item,a.card,a.sres');
  if(!a){if(peekEl||peekPend){clearTimeout(peekT);peekPend=null;peekT=setTimeout(hidePeek,280);}return;}
  if(a===peekFor||a===peekPend)return;
  const href=a.getAttribute('href')||'';if(!href.startsWith(NP))return;
  clearTimeout(peekT);peekPend=a;peekT=setTimeout(()=>showPeek(a,href),480);
});
async function showPeek(a,href){
  const path=decodeURIComponent(href.slice(NP.length).split('#')[0].split('?')[0]);
  let d=peekCache.get(path);
  if(!d){try{d=await api('/api/peek?path='+encodeURIComponent(path));peekCache.set(path,d);}catch(e){return;}}
  if(peekPend!==a)return;
  hidePeek();peekFor=a;
  peekEl=document.createElement('div');peekEl.id='peek';
  peekEl.innerHTML='<div class="peek-title">'+escH(d.title)+'</div><div class="md">'+d.html+'</div>';
  document.body.appendChild(peekEl);markDup(peekEl.querySelector('.md'),d.title);
  const r=a.getBoundingClientRect(),w=peekEl.offsetWidth,h=peekEl.offsetHeight;
  let x=Math.min(innerWidth-w-12,Math.max(12,r.left)),y=r.bottom+8;
  if(y+h>innerHeight-12)y=Math.max(12,r.top-h-8);
  if(a.closest('#right')){x=Math.max(12,r.left-w-12);y=Math.min(innerHeight-h-12,Math.max(12,r.top-20));}
  peekEl.style.left=x+'px';peekEl.style.top=y+'px';
  const hash=href.split('#')[1];
  if(hash){const t=peekEl.querySelector('#'+CSS.escape(decodeURIComponent(hash)));if(t)peekEl.scrollTop=t.offsetTop-12;}
}
addEventListener('mousedown',e=>{if(!e.target.closest('#peek'))hidePeek();});
sc.addEventListener('scroll',()=>{$('#top').classList.toggle('scrolled',sc.scrollTop>4);hidePeek();},{passive:true});

/* ---------- améliorations du rendu ---------- */
function markDup(root,title){
  if(!root)return;const f=root.firstElementChild;
  if(f&&f.tagName==='H1'&&f.textContent.trim().toLowerCase()===String(title).trim().toLowerCase())f.classList.add('dup');
}
function enhance(root){
  $$('pre',root).forEach(pre=>{
    if(pre.querySelector('.copy'))return;
    const b=document.createElement('button');b.className='ib copy';b.title='Copier';b.innerHTML=ICON('copy');
    b.onclick=async()=>{const c=pre.querySelector('code')||pre;
      try{await navigator.clipboard.writeText(c.innerText.replace(/\n$/,''));toast('Code copié','ok',1200);}catch(e){toast('Copie impossible','err');}};
    pre.appendChild(b);
  });
}
async function copyText(t,msg){try{await navigator.clipboard.writeText(t);toast(msg||'Copié','ok',1400);}catch(e){toast('Copie impossible','err');}}

/* ---------- raccourcis globaux ---------- */
document.addEventListener('keydown',e=>{
  const mod=e.ctrlKey||e.metaKey,k=e.key.toLowerCase(),ae=document.activeElement,
        typing=ae&&(ae.tagName==='INPUT'||ae.tagName==='TEXTAREA'||ae.isContentEditable);
  if(e.key==='Escape'){if(ovEl){e.preventDefault();closeOverlay();return;}closeMenu();hidePeek();D.classList.remove('show-left','show-right');}
  if(ovEl)return;
  if(mod&&!e.shiftKey&&!e.altKey&&(k==='k'||k==='o'||k==='p')){e.preventDefault();openPalette();return;}
  if(mod&&e.shiftKey&&k==='f'){e.preventDefault();openPalette();return;}
  if(mod&&(e.key==='\\'||e.code==='Backslash')){e.preventDefault();toggleLeft();return;}
  if(e.altKey&&!mod&&e.code==='KeyN'){e.preventDefault();newNote('');return;}
  if(e.altKey&&!mod&&e.code==='KeyT'){e.preventDefault();toggleTheme();return;}
  if(!typing&&!mod&&e.key==='?'){e.preventDefault();showHelp();}
});

/* ---------- page de note ---------- */
const M=$('#main'),NOTE=M.dataset.path||null;
if(NOTE){
  pushRecent(NOTE);
  const view=$('#view'),art=$('#art'),ed=$('#editor'),ta=$('#src'),pv=$('#preview'),wrap=$('.edwrap'),
        st=$('#status'),wc=$('#wc'),ps=$('#pos'),bPrev=$('#b-prev'),tt=$('#ntitle');
  const NAME=tt?tt.textContent.trim():NOTE;
  let mtime=M.dataset.mtime,dirty=false,saving=false,conflict=false,timer=null,ptimer=null;
  const setDirty=v=>{dirty=v;document.body.classList.toggle('is-dirty',v);};
  const setStatus=(t,c)=>{st.textContent=t;st.className='status '+(c||'');};
  const editing=()=>!ed.hidden;
  if(LS.get('nopreview',innerWidth<1300))wrap.classList.add('nopreview');
  bPrev.classList.toggle('on',!wrap.classList.contains('nopreview'));

  function afterRender(){
    markDup(art,NAME);enhance(art);bindTasks();buildOutline();
    const words=(art.innerText.match(/[\p{L}\p{N}’'-]+/gu)||[]).length;const w=$('#words');if(w)w.textContent=words+' mots';
  }
  function bindTasks(){
    $$('input.task-cb[data-i]',art).forEach(cb=>{cb.disabled=false;
      cb.onchange=async()=>{
        try{if(dirty)await save();const j=await api('/api/toggle',{path:NOTE,index:+cb.dataset.i,mtime});
          mtime=j.mtime;ta.value=j.content;cb.closest('li').classList.toggle('done',cb.checked);}
        catch(e){cb.checked=!cb.checked;toast(e.message,'err');}
      };});
  }
  /* plan + suivi du défilement */
  const box=$('#outline');let hs=[];
  function buildOutline(){
    if(!box)return;
    hs=$$('h1,h2,h3,h4,h5,h6',art).filter(h=>h.id&&!h.classList.contains('dup')&&!h.closest('.embed'));
    box.innerHTML=hs.length?hs.map(h=>'<a href="#'+escH(h.id)+'" class="l'+h.tagName[1]+'">'+escH(h.textContent)+'</a>').join(''):'<p class="empty">Aucun titre</p>';
    const c=$('#outline-n');if(c)c.textContent=hs.length;spy();
  }
  function spy(){
    if(!box||!hs.length||editing())return;const top=sc.getBoundingClientRect().top+90;let cur=null;
    for(const h of hs){if(h.getBoundingClientRect().top<=top)cur=h;else break;}
    $$('a',box).forEach(a=>a.classList.toggle('active',!!cur&&a.getAttribute('href')==='#'+cur.id));
  }
  sc.addEventListener('scroll',spy,{passive:true});
  if(box)box.addEventListener('click',e=>{const a=e.target.closest('a');if(!a)return;e.preventDefault();
    const h=document.getElementById(a.getAttribute('href').slice(1));if(h){sc.scrollTo({top:h.offsetTop-20,behavior:'smooth'});history.replaceState(null,'','#'+h.id);}});
  afterRender();

  /* modes */
  function setMode(edit){
    $('#m-read').classList.toggle('on',!edit);$('#m-edit').classList.toggle('on',edit);
    document.body.classList.toggle('editing',edit);view.hidden=edit;ed.hidden=!edit;bPrev.hidden=!edit;
  }
  function openEditor(){
    if(editing())return;
    const ratio=sc.scrollTop/Math.max(1,sc.scrollHeight-sc.clientHeight);
    setMode(true);ta.focus({preventScroll:true});
    requestAnimationFrame(()=>{ta.scrollTop=ratio*(ta.scrollHeight-ta.clientHeight);});
    updatePreview();updateFoot();history.replaceState(null,'',location.pathname+'?edit=1');
  }
  async function closeEditor(){
    if(!editing())return;
    if(dirty)await save();if(dirty)return;
    acHide();
    const ratio=ta.scrollTop/Math.max(1,ta.scrollHeight-ta.clientHeight);
    try{const j=await api('/api/preview',{path:NOTE,content:ta.value,interactive:true});art.innerHTML=j.html;}
    catch(e){location.href=location.pathname;return;}
    setMode(false);afterRender();history.replaceState(null,'',location.pathname);
    requestAnimationFrame(()=>{sc.scrollTop=ratio*(sc.scrollHeight-sc.clientHeight);});
  }
  $('#m-read').onclick=closeEditor;$('#m-edit').onclick=openEditor;
  bPrev.onclick=()=>{wrap.classList.toggle('nopreview');const on=!wrap.classList.contains('nopreview');
    LS.set('nopreview',!on);bPrev.classList.toggle('on',on);updatePreview();ta.focus();};

  /* sauvegarde */
  async function save(force){
    if(saving)return;if(conflict&&!force)return;
    clearTimeout(timer);
    if(!dirty&&!force){setStatus('Enregistré','ok');return;}
    saving=true;setStatus('Enregistrement…');
    const content=ta.value;let err=null;
    try{const j=await api('/api/save',{path:NOTE,content,mtime,force:!!force});mtime=j.mtime;conflict=false;if(ta.value===content)setDirty(false);}
    catch(e){err=e;}
    saving=false;
    if(!err){setStatus(dirty?'Modifié':'Enregistré ✓',dirty?'':'ok');if(dirty)timer=setTimeout(save,800);return;}
    if(err.status===409){
      conflict=true;setStatus('⚠ Modifié sur le disque','err');
      if(await confirmBox('Conflit de modification',"Ce fichier a été modifié ailleurs depuis que vous l'avez ouvert.",'Écraser avec ma version',true,'Recharger la version du disque'))return save(true);
      setDirty(false);location.reload();return;
    }
    setStatus('⚠ '+err.message,'err');toast('Enregistrement impossible : '+err.message,'err',5000);
    if(err.status===401)timer=setTimeout(save,15000);
  }
  async function updatePreview(){
    if(!editing()||pv.offsetParent===null)return;
    try{const j=await api('/api/preview',{path:NOTE,content:ta.value});pv.innerHTML=j.html;markDup(pv,NAME);enhance(pv);}catch(e){}
  }
  function updateFoot(){
    const v=ta.value,pos=ta.selectionStart,before=v.slice(0,pos);
    wc.textContent=(v.match(/[\p{L}\p{N}’'-]+/gu)||[]).length+' mots · '+v.length+' caractères';
    ps.textContent='Ln '+before.split('\n').length+', Col '+(pos-before.lastIndexOf('\n'));
  }
  addEventListener('beforeunload',e=>{if(dirty){e.preventDefault();e.returnValue='';}});
  document.addEventListener('click',async e=>{
    const a=e.target.closest('a[href]');if(!a||!dirty||e.defaultPrevented)return;
    const h=a.getAttribute('href');if(!h||h.startsWith('#')||a.target==='_blank'||e.ctrlKey||e.metaKey)return;
    e.preventDefault();await save();if(!dirty)location.href=a.href;
  });

  /* outils d'édition */
  const ins=t=>{if(t==='')document.execCommand('delete');else document.execCommand('insertText',false,t);};
  function wrapSel(a,b){
    const s=ta.selectionStart,e=ta.selectionEnd,sel=ta.value.slice(s,e);
    if(sel.length>=a.length+b.length&&sel.startsWith(a)&&sel.endsWith(b)){
      ins(sel.slice(a.length,sel.length-b.length));ta.setSelectionRange(s,e-a.length-b.length);return;}
    if(!sel&&ta.value.slice(s-a.length,s)===a&&ta.value.slice(s,s+b.length)===b){
      ta.setSelectionRange(s-a.length,s+b.length);ins('');return;}
    ins(a+sel+b);ta.setSelectionRange(s+a.length,s+a.length+sel.length);
  }
  function lineRange(){
    const v=ta.value,s=ta.selectionStart;let e=ta.selectionEnd;if(e>s&&v[e-1]==='\n')e--;
    const ls=v.lastIndexOf('\n',s-1)+1;let le=v.indexOf('\n',e);if(le<0)le=v.length;return[ls,le];
  }
  function replaceLines(fn,keepCaretEnd){
    const[ls,le]=lineRange(),block=ta.value.slice(ls,le),s=ta.selectionStart,e=ta.selectionEnd;
    const nb=block.split('\n').map(fn).join('\n');if(nb===block)return;
    ta.setSelectionRange(ls,le);ins(nb);
    if(s===e){const p=keepCaretEnd&&!block.includes('\n')?ls+nb.length:Math.max(ls,s+nb.length-block.length);ta.setSelectionRange(p,p);}
    else ta.setSelectionRange(ls,ls+nb.length);
  }
  function indent(out){
    const s=ta.selectionStart,e=ta.selectionEnd,v=ta.value;
    if(s===e&&!out){const ls=v.lastIndexOf('\n',s-1)+1;const line=v.slice(ls,(v.indexOf('\n',s)+1||v.length+1)-1);
      if(!/^\s*(?:[-*+]|\d+[.)])\s/.test(line)){ins('\t');return;}}
    replaceLines(l=>out?l.replace(/^(\t| {1,4})/,''):'\t'+l);
  }
  function toggleTask(){
    replaceLines(l=>{let m;
      if((m=l.match(/^(\s*(?:[-*+]|\d+[.)])\s+)\[([ xX])\](.*)$/)))return m[1]+'['+(m[2]===' '?'x':' ')+']'+m[3];
      if((m=l.match(/^(\s*(?:[-*+]|\d+[.)])\s+)(.*)$/)))return m[1]+'[ ] '+m[2];
      const ind=l.match(/^\s*/)[0];return ind+'- [ ] '+l.slice(ind.length);},true);
  }

  /* autocomplétion [[ ]] */
  const ac=document.createElement('div');ac.id='ac';ac.hidden=true;document.body.appendChild(ac);
  let acItems=[],acSel=0,acStart=-1;
  function caretXY(pos){
    const d=document.createElement('div'),s=getComputedStyle(ta);
    ['boxSizing','width','paddingTop','paddingRight','paddingBottom','paddingLeft','borderTopWidth','borderRightWidth','borderBottomWidth',
     'borderLeftWidth','fontFamily','fontSize','fontWeight','fontStyle','letterSpacing','lineHeight','textTransform','wordSpacing','textIndent','tabSize'
    ].forEach(p=>d.style[p]=s[p]);
    Object.assign(d.style,{position:'absolute',visibility:'hidden',whiteSpace:'pre-wrap',overflowWrap:'break-word',top:'0',left:'-9999px'});
    d.textContent=ta.value.slice(0,pos);const sp=document.createElement('span');sp.textContent=ta.value.slice(pos,pos+1)||'.';d.appendChild(sp);
    document.body.appendChild(d);const r=ta.getBoundingClientRect();
    const x=r.left+sp.offsetLeft-ta.scrollLeft,y=r.top+sp.offsetTop-ta.scrollTop+(parseFloat(s.lineHeight)||24);
    d.remove();return[x,y];
  }
  function acHide(){ac.hidden=true;acItems=[];}
  function acMark(){$$('div[data-i]',ac).forEach(d=>d.classList.toggle('sel',+d.dataset.i===acSel));const s=$('div.sel',ac);if(s)s.scrollIntoView({block:'nearest'});}
  function acUpdate(){
    const pos=ta.selectionStart;if(pos!==ta.selectionEnd){acHide();return;}
    const m=ta.value.slice(Math.max(0,pos-200),pos).match(/\[\[([^\[\]|#\n]*)$/);if(!m){acHide();return;}
    const q=m[1];acStart=pos-q.length;let res=[];
    if(!q){const rec=LS.get(SK('recent'),[]);
      res=NOTES.filter(n=>n.p!==NOTE).map(n=>[-(rec.indexOf(n.p)<0?999:rec.indexOf(n.p)),n,[]]).sort((a,b)=>b[0]-a[0]).slice(0,8);}
    else{for(const n of NOTES){const r=fuzzy(q,n.n);if(r)res.push([r[0],n,r[1]]);}res.sort((a,b)=>b[0]-a[0]);res=res.slice(0,8);}
    acItems=res.map(r=>r[1]);
    const create=q.trim()&&!NOTES.some(n=>n.nl===q.trim().toLowerCase());
    let h=res.map((r,i)=>'<div data-i="'+i+'">'+ICON('file')+'<span>'+hl(r[1].n,r[2])+'</span><small>'+escH(dirOf(r[1].p))+'</small></div>').join('');
    if(create){h+='<div data-i="'+acItems.length+'">'+ICON('plus')+'<span>Lier « '+escH(q.trim())+' » (nouvelle note)</span></div>';acItems.push({n:q.trim(),p:null});}
    if(!acItems.length){acHide();return;}
    ac.innerHTML=h;acSel=0;acMark();ac.hidden=false;
    const[x,y]=caretXY(acStart);
    ac.style.left=Math.max(8,Math.min(x-8,innerWidth-ac.offsetWidth-10))+'px';
    ac.style.top=(y+ac.offsetHeight>innerHeight-10?Math.max(8,y-ac.offsetHeight-30):y+2)+'px';
  }
  function acAccept(i){
    const it=acItems[i];if(!it)return;const pos=ta.selectionStart;
    let name=it.n;if(it.p&&NOTES.filter(n=>n.nl===it.n.toLowerCase()).length>1)name=it.p.replace(/\.(md|markdown)$/i,'');
    const after=ta.value.slice(pos,pos+2);ta.setSelectionRange(acStart,pos);
    ins(name+(after===']]'?'':']]'));if(after===']]'){const p=ta.selectionStart+2;ta.setSelectionRange(p,p);}
    acHide();
  }
  ac.addEventListener('mousedown',e=>{e.preventDefault();const d=e.target.closest('div[data-i]');if(d)acAccept(+d.dataset.i);});

  ta.addEventListener('keydown',e=>{
    if(!ac.hidden&&acItems.length){
      if(e.key==='ArrowDown'){e.preventDefault();acSel=(acSel+1)%acItems.length;acMark();return;}
      if(e.key==='ArrowUp'){e.preventDefault();acSel=(acSel-1+acItems.length)%acItems.length;acMark();return;}
      if(e.key==='Enter'||e.key==='Tab'){e.preventDefault();acAccept(acSel);return;}
      if(e.key==='Escape'){e.preventDefault();e.stopPropagation();acHide();return;}
    }
    const mod=e.ctrlKey||e.metaKey,k=e.key.toLowerCase();
    if(mod&&!e.shiftKey&&!e.altKey){
      if(k==='b'){e.preventDefault();wrapSel('**','**');return;}
      if(k==='i'){e.preventDefault();wrapSel('*','*');return;}
      if(k==='k'){e.preventDefault();e.stopPropagation();wrapSel('[[',']]');acUpdate();return;}
      if(e.key==='Enter'){e.preventDefault();toggleTask();return;}
    }
    if(mod&&e.shiftKey&&k==='h'){e.preventDefault();wrapSel('==','==');return;}
    if(mod&&e.shiftKey&&k==='x'){e.preventDefault();wrapSel('~~','~~');return;}
    if(e.key==='Tab'&&!mod&&!e.altKey){e.preventDefault();indent(e.shiftKey);return;}
    if(e.key==='['&&!mod&&ta.selectionStart===ta.selectionEnd&&ta.value[ta.selectionStart-1]==='['&&ta.value[ta.selectionStart]!==']'){
      e.preventDefault();const p=ta.selectionStart;ins('[]]');ta.setSelectionRange(p+1,p+1);acUpdate();return;}
    if(e.key==='Enter'&&!e.shiftKey&&!mod&&!e.altKey&&!e.isComposing){
      const s=ta.selectionStart;if(s!==ta.selectionEnd)return;
      const ls=ta.value.lastIndexOf('\n',s-1)+1,line=ta.value.slice(ls,s);
      const m=line.match(/^(\s*(?:>\s*)*)([-*+] \[[ xX]\] |[-*+] |(\d+)([.)]) )(.*)$/);if(!m)return;
      e.preventDefault();
      if(!m[5].trim()){ta.setSelectionRange(ls,s);ins('');return;}
      const mk=m[3]?(parseInt(m[3],10)+1)+m[4]+' ':m[2].replace(/\[[xX]\]/,'[ ]');
      ins('\n'+m[1]+mk);
    }
  });
  ta.addEventListener('input',()=>{
    setDirty(true);setStatus('Modifié');clearTimeout(timer);timer=setTimeout(save,800);
    clearTimeout(ptimer);ptimer=setTimeout(updatePreview,200);acUpdate();updateFoot();
  });
  ta.addEventListener('keyup',e=>{if(/^(Arrow|Home|End|Page)/.test(e.key)&&ac.hidden)updateFoot();});
  ta.addEventListener('click',()=>{acUpdate();updateFoot();});
  ta.addEventListener('blur',()=>setTimeout(acHide,150));
  ta.addEventListener('scroll',()=>{acHide();if(pv.offsetParent!==null){const r=ta.scrollTop/Math.max(1,ta.scrollHeight-ta.clientHeight);pv.scrollTop=r*(pv.scrollHeight-pv.clientHeight);}},{passive:true});

  /* renommer / supprimer / menu */
  async function rename(v){
    if(dirty)await save();
    try{const j=await api('/api/rename',{path:NOTE,name:v});setDirty(false);
      LS.set('flash',j.updated?'Renommée — liens mis à jour dans '+j.updated+' note(s)':'Note renommée');
      LS.set(SK('recent'),LS.get(SK('recent'),[]).map(x=>x===NOTE?decodeURIComponent(j.url.slice(NP.length)):x));location.href=j.url+(editing()?'?edit=1':'');}
    catch(e){toast('Renommage impossible : '+e.message,'err');if(tt)tt.textContent=NAME;}
  }
  async function del(){
    if(!await confirmBox('Supprimer « '+NAME+' » ?','La note sera déplacée dans le dossier .trash/ de cet espace.','Supprimer',true))return;
    try{await api('/api/delete',{path:NOTE});setDirty(false);LS.set('flash','Note déplacée dans .trash/');location.href=B+'/';}
    catch(e){toast('Suppression impossible : '+e.message,'err');}
  }
  if(tt){
    tt.addEventListener('keydown',e=>{if(e.key==='Enter'){e.preventDefault();tt.blur();}if(e.key==='Escape'){tt.textContent=NAME;tt.blur();}});
    tt.addEventListener('blur',()=>{const v=tt.textContent.replace(/\s+/g,' ').trim();if(!v||v===NAME){tt.textContent=NAME;return;}rename(v);});
    tt.addEventListener('paste',e=>{e.preventDefault();document.execCommand('insertText',false,(e.clipboardData.getData('text/plain')||'').replace(/\s+/g,' '));});
  }
  $('#b-more').onclick=e=>openMenu(e.currentTarget,[
    {icon:'pencil',label:'Renommer…',act:()=>ask('Renommer la note',NAME,'Renommer','Les [[liens]] des autres notes seront mis à jour.').then(v=>{if(v&&v!==NAME)rename(v);})},
    {icon:'link',label:'Copier le lien [[…]]',act:()=>copyText('[['+NAME+']]','Lien copié')},
    null,
    {icon:'width',label:D.classList.contains('wide')?'Largeur de lecture normale':'Largeur de lecture étendue',act:()=>{D.classList.toggle('wide');LS.set('wide',D.classList.contains('wide'));}},
    {icon:'type',label:D.classList.contains('mono')?'Éditeur : police proportionnelle':'Éditeur : police à chasse fixe',act:()=>{D.classList.toggle('mono');LS.set('mono',D.classList.contains('mono'));}},
    null,
    {icon:'trash',label:'Supprimer',cls:'danger',act:del}
  ]);

  document.addEventListener('keydown',e=>{
    const mod=e.ctrlKey||e.metaKey,k=e.key.toLowerCase();
    if(ovEl)return;
    if(mod&&!e.shiftKey&&k==='s'){e.preventDefault();if(editing())save();else toast('Rien à enregistrer','',1000);}
    if(mod&&!e.shiftKey&&k==='e'){e.preventDefault();editing()?closeEditor():openEditor();}
  });
  if(new URLSearchParams(location.search).has('edit'))openEditor();
  else if(location.hash){const h=document.getElementById(decodeURIComponent(location.hash.slice(1)));if(h)setTimeout(()=>sc.scrollTop=h.offsetTop-20,0);}
}else{
  enhance(M);
}
})();
"""

HEAD_JS = ("(function(){try{var d=document.documentElement,g=function(k,v){var x=localStorage.getItem('mdv-'+k);"
           "return x===null?v:JSON.parse(x);};d.dataset.theme=g('theme','dark');if(g('left',true)===false)d.classList.add('no-left');"
           "if(g('right',true)===false)d.classList.add('no-right');if(g('wide',false))d.classList.add('wide');"
           "if(g('mono',false))d.classList.add('mono');var w=g('sidew',0);if(w)d.style.setProperty('--side-w',w+'px');}catch(e){}})();")

PAGE = """<!doctype html>
<html lang="fr" data-theme="dark"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<meta name="referrer" content="same-origin">
<title>{{TITLE}} · mdvault</title>
<script nonce="{{NONCE}}">{{HEADJS}}</script>
<style>{{CSS}}{{PYG}}</style></head>
<body class="{{BODYCLS}}">
<div id="app">
<aside id="side">
  <div class="side-head"><a class="vault" href="{{BASE}}/" title="Espace « {{VAULT}} »">{{VAULT}}</a>
    <button class="ib" id="b-new" title="Nouvelle note (Alt+N)">{{I_FILEPLUS}}</button>
    <button class="ib" id="b-collapse" title="Tout replier">{{I_COLLAPSE}}</button></div>
  <button class="searchbtn" id="b-switch">{{I_SEARCH}}<span>Rechercher…</span><kbd>Ctrl K</kbd></button>
  <nav class="side-nav">{{NAV}}</nav>
  <div class="side-scroll">
    <div class="sec"><span>Notes</span><span>{{COUNT}}</span></div>
    <div id="tree">{{TREE}}</div>
    {{TAGS}}
  </div>
  <div class="side-foot"><button class="ib" id="b-theme"></button><button class="ib" id="b-help" title="Raccourcis (?)">{{I_HELP}}</button>
    <span class="sp"></span><span class="muted">{{USER}}</span>
    <a class="ib" href="/account" title="Compte">{{I_USER}}</a>
    <form class="inline" method="post" action="/logout"><input type="hidden" name="csrf" value="{{CSRF}}"><button class="ib" title="Se déconnecter">{{I_LOGOUT}}</button></form></div>
  <div class="resizer" title="Glisser pour redimensionner"></div>
</aside>
<div id="center">
  <header id="top"><button class="ib" id="b-left" title="Panneau de gauche (Ctrl+\\)">{{I_SIDE}}</button>
    <div class="crumbs">{{CRUMBS}}</div>{{ACTIONS}}</header>
  <div id="scroller"><main id="main"{{MAINATTR}}>{{MAIN}}</main></div>
</div>
<aside id="right">{{RIGHT}}</aside>
</div>
<script nonce="{{NONCE}}">window.MDV={{MDVJSON}};</script>
<script nonce="{{NONCE}}">{{JS}}</script>
</body></html>"""

AUTH_PAGE = """<!doctype html>
<html lang="fr" data-theme="dark" class="authpage"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<meta name="referrer" content="same-origin"><meta name="robots" content="noindex,nofollow">
<title>{{TITLE}} · mdvault</title>
<script nonce="{{NONCE}}">{{HEADJS}}</script>
<style>{{CSS}}</style></head>
<body><div class="auth-wrap"><div class="auth-card{{WIDE}}">{{BODY}}</div></div></body></html>"""

MSGS = {
    'out': ('ok', 'Vous êtes déconnecté.'),
    'expired': ('err', 'Formulaire expiré : veuillez réessayer.'),
    'deleted': ('ok', 'Compte supprimé.'),
    'space-new': ('ok', 'Espace créé.'),
    'space-del': ('ok', 'Espace supprimé définitivement.'),
    'space-exists': ('err', 'Un espace porte déjà ce nom.'),
    'space-bad': ('err', 'Nom d\'espace invalide : lettres, chiffres, « - » et « _ » (40 caractères max).'),
    'space-max': ('err', 'Nombre maximal d\'espaces atteint (%d).' % MAX_SPACES),
    'pw-ok': ('ok', 'Mot de passe modifié. Toutes les autres sessions ont été fermées.'),
    'pw-bad': ('err', 'Mot de passe incorrect.'),
    'pw-mismatch': ('err', 'Les deux nouveaux mots de passe ne correspondent pas.'),
    'pw-weak': ('err', 'Mot de passe trop faible : au moins %d caractères, sans l\'identifiant, pas trop simple.' % PW_MIN),
    'sess-ok': ('ok', 'Les autres sessions ont été fermées.'),
    'confirm': ('err', 'La confirmation ne correspond pas.'),
    'wait': ('err', 'Trop de tentatives : réessayez dans quelques minutes.'),
    'signup-closed': ('err', 'Les inscriptions sont fermées.'),
}


def build_tree(notes):
    root = {'d': {}, 'f': []}
    for rel in notes:
        node = root
        for part in rel.split('/')[:-1]:
            node = node['d'].setdefault(part, {'d': {}, 'f': []})
        node['f'].append(rel)
    return root


def tree_html(vault, node, current, prefix=''):
    out = ['<ul>']
    for name in sorted(node['d'], key=str.lower):
        path = prefix + name
        op = ' open' if current and current.startswith(path + '/') else ''
        out.append('<li class="dir"><details data-path="%s"%s><summary class="tree-row">%s<span class="name">%s</span>'
                   '<button class="ib add" data-folder="%s" title="Nouvelle note dans ce dossier">%s</button></summary>%s</details></li>'
                   % (esc(path), op, icon('chev', 'chev'), esc(name), esc(path), icon('plus'),
                      tree_html(vault, node['d'][name], current, path + '/')))
    for rel in sorted(node['f'], key=str.lower):
        cls = ' current' if rel == current else ''
        out.append('<li class="file"><a class="tree-row%s" href="%s" title="%s"><span class="name">%s</span></a></li>'
                   % (cls, esc(vault.url(rel)), esc(rel), esc(stem(rel))))
    out.append('</ul>')
    return ''.join(out)


def fmt_time(ns):
    return time.strftime('%d/%m/%Y %H:%M', time.localtime(ns / 1e9))


def count_notes(p):
    n = 0
    for dp, dn, fn in os.walk(p):
        dn[:] = [d for d in dn if not d.startswith('.')]
        n += sum(1 for f in fn if is_note(f) and not f.startswith('.'))
    return n


def safe_next(v):
    v = (v or '').strip()
    if not v.startswith('/') or v.startswith('//') or '\\' in v or re.search(r'[\x00-\x1f\x7f]', v) or len(v) > 2000:
        return ''
    return v


def page_csp(nonce):
    return ("default-src 'none'; script-src 'nonce-%s'; style-src 'self' 'unsafe-inline'; img-src 'self' data:; "
            "media-src 'self'; frame-src 'self'; connect-src 'self'; font-src 'self'; form-action 'self'; "
            "base-uri 'none'; frame-ancestors 'none'" % nonce)


# --------------------------------------------------------------------------
# Serveur HTTP
# --------------------------------------------------------------------------

class Handler(BaseHTTPRequestHandler):
    store = None
    limiter = None
    cfg = {'secure': False, 'signup': False, 'proxy': False, 'hosts': set()}
    server_version = 'mdvault'
    sys_version = ''
    timeout = 30

    def log_message(self, fmt, *args):
        pass

    def log_auth(self, msg):
        sys.stderr.write('%s [auth] %s %s\n' % (time.strftime('%Y-%m-%d %H:%M:%S'), self.client_ip(), msg))

    # --- utilitaires ---
    def send(self, body, ctype='text/html; charset=utf-8', code=200, headers=None, csp=None, frame='DENY'):
        if isinstance(body, str):
            body = body.encode('utf-8')
        self.send_response(code)
        self.send_header('Content-Type', ctype)
        self.send_header('Content-Length', str(len(body)))
        self.security_headers(csp, frame)
        for k, v in (headers or []):
            self.send_header(k, v)
        self.end_headers()
        if self.command != 'HEAD':
            self.wfile.write(body)

    def security_headers(self, csp=None, frame='DENY'):
        self.send_header('Cache-Control', 'no-store')
        self.send_header('X-Content-Type-Options', 'nosniff')
        self.send_header('X-Frame-Options', frame)
        self.send_header('Referrer-Policy', 'same-origin')
        self.send_header('Cross-Origin-Opener-Policy', 'same-origin')
        self.send_header('Cross-Origin-Resource-Policy', 'same-origin')
        self.send_header('Permissions-Policy', 'camera=(), microphone=(), geolocation=(), payment=(), usb=()')
        self.send_header('Content-Security-Policy', csp or "default-src 'none'; frame-ancestors 'none'")
        if self.cfg['secure']:
            self.send_header('Strict-Transport-Security', 'max-age=31536000; includeSubDomains')

    def send_json(self, obj, code=200):
        self.send(json.dumps(obj, ensure_ascii=False), 'application/json; charset=utf-8', code)

    def redirect(self, url, headers=None):
        self.send(b'', 'text/plain', 303, [('Location', url)] + list(headers or []))

    def client_ip(self):
        ip = self.client_address[0] if self.client_address else '?'
        if self.cfg['proxy'] and ip in ('127.0.0.1', '::1'):
            fwd = (self.headers.get('X-Forwarded-For') or '').split(',')[-1].strip()
            if fwd and len(fwd) < 64:
                return fwd
        return ip

    def host_ok(self):
        allowed = self.cfg['hosts']
        if not allowed:
            return True
        h = (self.headers.get('Host') or '').lower()
        hn = h.split(']')[0] + ']' if h.startswith('[') else h.rsplit(':', 1)[0]
        return hn in allowed

    def origin_ok(self):
        host = (self.headers.get('Host') or '').lower()
        o = self.headers.get('Origin') or self.headers.get('Referer')
        if not o or o == 'null' or not host:
            return False
        try:
            return urllib.parse.urlsplit(o).netloc.lower() == host
        except ValueError:
            return False

    def cookies(self):
        out = {}
        for part in (self.headers.get('Cookie') or '').split(';'):
            k, _, v = part.strip().partition('=')
            if k and k not in out:
                out[k] = v.strip()
        return out

    def cn(self, pre=False):
        n = 'mdvpre' if pre else 'mdv'
        return '__Host-' + n if self.cfg['secure'] else n

    def cookie(self, name, val, age):
        return ('Set-Cookie', '%s=%s; Path=/; HttpOnly; SameSite=Strict; Max-Age=%d%s'
                % (name, val, age, '; Secure' if self.cfg['secure'] else ''))

    def load_auth(self):
        self.skey = self.sess = self.user = None
        tok = self.cookies().get(self.cn())
        if tok:
            self.skey, self.sess, self.user = self.store.session(tok)

    def safe(self, rel, note=False):
        if not isinstance(rel, str) or not rel or '\x00' in rel or len(rel) > 1024:
            return None
        if any(part.startswith('.') for part in rel.replace('\\', '/').split('/') if part):
            return None
        root = self.vault.root
        p = (root / rel).resolve()
        if p == root or root not in p.parents:
            return None
        if note and not is_note(p.name):
            return None
        return p

    def rel_of(self, p):
        return p.relative_to(self.vault.root).as_posix()

    def alert(self, code):
        m = MSGS.get(code)
        return '<div class="alert %s" role="status">%s</div>' % (m[0], esc(m[1])) if m else ''

    def auth_page(self, title, body, code=200, headers=None, wide=False):
        nonce = secrets.token_urlsafe(16)
        vals = {'TITLE': esc(title), 'HEADJS': HEAD_JS, 'CSS': CSS, 'NONCE': nonce, 'BODY': body,
                'WIDE': ' auth-wide' if wide else ''}
        self.send(re.sub(r'\{\{(\w+)\}\}', lambda m: vals[m.group(1)], AUTH_PAGE), code=code, headers=headers,
                  csp=page_csp(nonce))

    def topbar(self):
        return ('<div class="topbar"><a class="brand" href="/">%s mdvault</a><span class="sp"></span>'
                '<span class="who">%s</span><a class="btn" href="/">%s Espaces</a><a class="btn" href="/account">%s Compte</a>'
                '<form class="inline" method="post" action="/logout"><input type="hidden" name="csrf" value="%s">'
                '<button class="btn">%s Déconnexion</button></form></div>'
                % (icon('lock'), esc(self.user['name']), icon('spaces'), icon('user'), esc(self.sess['csrf']),
                   icon('logout')))

    def page(self, title, main, right='', current=None, idx=None, mainattr='', crumbs=None,
             actions='', nav_on=''):
        v = self.vault
        idx = idx or v.index()
        counts = {}
        for rel in idx.notes:
            info = v.info(rel)
            for t in (info['tags'] if info else ()):
                counts[t] = counts.get(t, 0) + 1
        tags = ''
        if counts:
            top = sorted(counts.items(), key=lambda x: (-x[1], x[0]))[:80]
            tags = ('<details class="tags-sec" open><summary class="sec"><span>Tags</span><span>%d</span></summary>'
                    '<div class="tags-box">%s</div></details>') % (len(counts), ''.join(
                        '<a class="tag" href="%s/search?q=%s">#%s<span class="n">%d</span></a>'
                        % (v.base, urllib.parse.quote('#' + t), esc(t), c) for t, c in top))
        nav = ''.join('<a href="%s"%s>%s%s</a>' % (href, ' class="on"' if key == nav_on else '', icon(ic), lab)
                      for key, href, ic, lab in (('home', v.base + '/', 'home', 'Accueil'),
                                                 ('search', v.base + '/search', 'search', 'Recherche'),
                                                 ('spaces', '/', 'spaces', 'Espaces')))
        mdv = {'csrf': self.sess['csrf'], 'base': v.base, 'icons': ICONS, 'notes': [[r, stem(r)] for r in idx.notes]}
        nonce = secrets.token_urlsafe(16)
        vals = {
            'TITLE': esc(title), 'CSS': CSS, 'PYG': PYG_CSS, 'JS': JS, 'HEADJS': HEAD_JS, 'NONCE': nonce,
            'MDVJSON': json.dumps(mdv, ensure_ascii=False).replace('<', '\\u003c').replace('>', '\\u003e'),
            'VAULT': esc(v.name), 'BASE': v.base, 'USER': esc(self.user['name']), 'CSRF': esc(self.sess['csrf']),
            'COUNT': str(len(idx.notes)), 'NAV': nav,
            'TREE': tree_html(v, build_tree(idx.notes), current) if idx.notes else
                    '<p class="panel empty" style="padding:4px 8px">Aucune note pour l\'instant.</p>',
            'TAGS': tags, 'MAIN': main, 'RIGHT': right, 'MAINATTR': mainattr,
            'BODYCLS': '' if right else 'noright',
            'CRUMBS': crumbs if crumbs is not None else '<b>%s</b>' % esc(title),
            'ACTIONS': actions,
            'I_FILEPLUS': icon('fileplus'), 'I_COLLAPSE': icon('collapse'), 'I_SEARCH': icon('search'),
            'I_HELP': icon('help'), 'I_SIDE': icon('side'), 'I_USER': icon('user'), 'I_LOGOUT': icon('logout'),
        }
        return re.sub(r'\{\{(\w+)\}\}', lambda m: vals[m.group(1)], PAGE), nonce

    def send_page(self, *a, code=200, **kw):
        body, nonce = self.page(*a, **kw)
        self.send(body, code=code, csp=page_csp(nonce))

    # --- GET ---
    def do_HEAD(self):
        self.do_GET()

    def do_GET(self):
        self._wrap(self._get)

    def do_POST(self):
        self._wrap(self._post)

    def _wrap(self, fn):
        try:
            fn()
        except (BrokenPipeError, ConnectionResetError, TimeoutError, ssl.SSLError):
            pass
        except Exception:
            traceback.print_exc()
            try:
                self.send('Erreur interne du serveur.', 'text/plain; charset=utf-8', 500)
            except Exception:
                pass

    def _get(self):
        if not self.host_ok():
            return self.send('Hôte refusé', 'text/plain; charset=utf-8', 403)
        u = urllib.parse.urlsplit(self.path)
        path = urllib.parse.unquote(u.path)
        q = urllib.parse.parse_qs(u.query)

        def qv(k):
            return (q.get(k) or [''])[0]
        if path == '/favicon.ico':
            return self.send(b'', 'image/x-icon', 204)
        if path == '/robots.txt':
            return self.send('User-agent: *\nDisallow: /\n', 'text/plain; charset=utf-8')
        self.load_auth()
        if path == '/login':
            return self.redirect('/') if self.user else self.login_page(qv('m'), safe_next(qv('next')))
        if path == '/signup':
            if self.user:
                return self.redirect('/')
            if not self.cfg['signup']:
                return self.redirect('/login?m=signup-closed')
            return self.signup_page()
        if not self.user:
            if path == '/api/csrf' or '/api/' in path:
                return self.send_json({'error': 'non connecté', 'code': 'auth'}, 401)
            nxt = self.path if path != '/' else ''
            return self.redirect('/login' + ('?next=' + urllib.parse.quote(nxt, safe='') if nxt else ''))
        if path == '/':
            return self.spaces_page(qv('m'))
        if path == '/account':
            return self.account_page(qv('m'))
        if path == '/api/csrf':
            return self.send_json({'csrf': self.sess['csrf']})
        m = re.match(r'^/s/([^/]+)(/.*)?$', path)
        if m:
            v = self.store.vault(self.user, m.group(1))
            if v is None:
                return self.auth_page('Introuvable', self.topbar() + '<h1 class="auth-h">Espace introuvable</h1>',
                                      code=404, wide=True)
            self.vault = v
            sub = m.group(2)
            if not sub:
                return self.redirect(v.base + '/')
            if sub == '/':
                return self.home()
            if sub.startswith('/note/'):
                return self.note(sub[len('/note/'):])
            if sub == '/search':
                return self.search_page(qv('q')[:500])
            if sub == '/api/peek':
                return self.api_peek(qv('path'))
            if sub == '/api/search':
                return self.api_search(qv('q')[:500])
            return self.send_page('Introuvable', '<div class="content"><h1 class="page-title">Page introuvable</h1></div>',
                                  code=404)
        return self.auth_page('Introuvable', self.topbar() + '<h1 class="auth-h">Page introuvable</h1>', code=404, wide=True)

    # --- pages publiques ---
    def pre_token(self):
        t = self.cookies().get(self.cn(pre=True), '')
        return t if re.fullmatch(r'[\w-]{32,64}', t) else secrets.token_urlsafe(32)

    def login_page(self, msg='', nxt='', err='', name='', code=200):
        pre = self.pre_token()
        signup = ('<div class="auth-foot">Pas encore de compte ? <a href="/signup">Créer un compte</a></div>'
                  if self.cfg['signup'] else '')
        body = ('<div class="brand">%s mdvault</div><h1 class="auth-h">Connexion</h1>%s%s'
                '<form method="post" action="/login"><input type="hidden" name="pre" value="%s">'
                '<input type="hidden" name="next" value="%s">'
                '<label class="lbl">Identifiant<input class="field" name="username" autocomplete="username" '
                'autocapitalize="none" spellcheck="false" required maxlength="32" value="%s"%s></label>'
                '<label class="lbl">Mot de passe<input class="field" type="password" name="password" '
                'autocomplete="current-password" required maxlength="%d"%s></label>'
                '<div class="btns"><button class="btn primary">Se connecter</button></div></form>%s'
                % (icon('lock'), self.alert(msg), '<div class="alert err" role="alert">%s</div>' % esc(err) if err else '',
                   pre, esc(nxt), esc(name), '' if name else ' autofocus', PW_MAX, ' autofocus' if name else '', signup))
        self.auth_page('Connexion', body, code=code, headers=[self.cookie(self.cn(pre=True), pre, 3600)])

    def signup_page(self, err='', name='', code=200):
        pre = self.pre_token()
        body = ('<div class="brand">%s mdvault</div><h1 class="auth-h">Créer un compte</h1>%s'
                '<form method="post" action="/signup"><input type="hidden" name="pre" value="%s">'
                '<label class="lbl">Identifiant (3 à 32 caractères : a-z, 0-9, . _ -)<input class="field" name="username" '
                'autocomplete="username" autocapitalize="none" spellcheck="false" required maxlength="32" '
                'pattern="[a-z0-9][a-z0-9_.\\-]{2,31}" value="%s" autofocus></label>'
                '<label class="lbl">Mot de passe (%d caractères minimum)<input class="field" type="password" name="password" '
                'autocomplete="new-password" required minlength="%d" maxlength="%d"></label>'
                '<label class="lbl">Confirmer le mot de passe<input class="field" type="password" name="password2" '
                'autocomplete="new-password" required minlength="%d" maxlength="%d"></label>'
                '<div class="btns"><button class="btn primary">Créer le compte</button></div></form>'
                '<div class="auth-foot">Déjà inscrit ? <a href="/login">Se connecter</a></div>'
                % (icon('lock'), '<div class="alert err" role="alert">%s</div>' % esc(err) if err else '', pre, esc(name),
                   PW_MIN, PW_MIN, PW_MAX, PW_MIN, PW_MAX))
        self.auth_page('Inscription', body, code=code, headers=[self.cookie(self.cn(pre=True), pre, 3600)])

    # --- pages du compte ---
    def spaces_page(self, msg=''):
        spaces = self.store.list_spaces(self.user)
        cards = ''.join('<a class="card" href="/s/%s/"><b>%s</b><p>%d note(s)</p></a>'
                        % (esc(s), esc(s), count_notes(self.store.user_dir(self.user) / s)) for s in spaces)
        quota = ''
        if self.store.quota:
            quota = ' · %.1f / %d Mo utilisés' % (self.store.usage(self.user) / 1048576, self.store.quota // 1048576)
        body = (self.topbar() + '<h1 class="auth-h">Vos espaces</h1><p class="lead">Chaque espace est un dossier de notes '
                'privé, visible par vous seul%s.</p>%s<div class="cards">%s</div>'
                '<div class="box"><h2>Nouvel espace</h2><form method="post" action="/spaces/new" class="row">'
                '<input type="hidden" name="csrf" value="%s"><input class="field" name="name" required maxlength="40" '
                'placeholder="ex. travail, perso, cours" autocomplete="off" spellcheck="false">'
                '<button class="btn primary">%s Créer</button></form></div>'
                % (quota, self.alert(msg), cards or '<p class="lead">Aucun espace : créez-en un ci-dessous.</p>',
                   esc(self.sess['csrf']), icon('plus')))
        self.auth_page('Espaces', body, wide=True)

    def account_page(self, msg=''):
        csrf = esc(self.sess['csrf'])
        name = esc(self.user['name'])
        spaces = self.store.list_spaces(self.user)
        n = self.store.count_sessions(self.user['name'])
        opts = ''.join('<option value="%s">%s</option>' % (esc(s), esc(s)) for s in spaces)
        hid = '<input type="hidden" name="csrf" value="%s">' % csrf
        body = (self.topbar() + '<h1 class="auth-h">Compte « %s »</h1>%s' % (name, self.alert(msg)) +
                '<div class="box"><h2>Changer de mot de passe</h2><p>Toutes vos autres sessions seront fermées.</p>'
                '<form method="post" action="/account/password">' + hid +
                '<input type="text" name="username" value="%s" autocomplete="username" hidden>' % name +
                '<label class="lbl">Mot de passe actuel<input class="field" type="password" name="current" '
                'autocomplete="current-password" required maxlength="%d"></label>' % PW_MAX +
                '<label class="lbl">Nouveau mot de passe (%d caractères minimum)<input class="field" type="password" '
                'name="password" autocomplete="new-password" required minlength="%d" maxlength="%d"></label>'
                % (PW_MIN, PW_MIN, PW_MAX) +
                '<label class="lbl">Confirmer<input class="field" type="password" name="password2" '
                'autocomplete="new-password" required minlength="%d" maxlength="%d"></label>' % (PW_MIN, PW_MAX) +
                '<div class="btns"><button class="btn primary">Changer le mot de passe</button></div></form></div>'
                '<div class="box"><h2>Sessions</h2><p>%d session(s) active(s), y compris celle-ci.</p>' % n +
                '<form method="post" action="/logout-all">' + hid +
                '<div class="btns"><button class="btn">Déconnecter les autres sessions</button></div></form></div>' +
                ('<div class="box danger"><h2>Supprimer un espace</h2><p>Toutes les notes de l\'espace seront '
                 'effacées définitivement.</p><form method="post" action="/spaces/delete">' + hid +
                 '<label class="lbl">Espace<select class="field" name="space" required>%s</select></label>' % opts +
                 '<label class="lbl">Mot de passe<input class="field" type="password" name="password" '
                 'autocomplete="current-password" required maxlength="%d"></label>' % PW_MAX +
                 '<div class="btns"><button class="btn danger">Supprimer l\'espace</button></div></form></div>'
                 if spaces else '') +
                '<div class="box danger"><h2>Supprimer le compte</h2><p>Le compte et tous ses espaces seront '
                'effacés définitivement.</p><form method="post" action="/account/delete">' + hid +
                '<label class="lbl">Retapez votre identifiant<input class="field" name="confirm" required '
                'autocomplete="off" spellcheck="false" maxlength="32"></label>'
                '<label class="lbl">Mot de passe<input class="field" type="password" name="password" '
                'autocomplete="current-password" required maxlength="%d"></label>' % PW_MAX +
                '<div class="btns"><button class="btn danger">Supprimer mon compte</button></div></form></div>')
        self.auth_page('Compte', body, wide=True)

    # --- pages d'un espace ---
    def home(self):
        v = self.vault
        idx = v.index()
        for name in ('index', 'readme', 'home', 'accueil'):
            for rel in idx.notes:
                if '/' not in rel and stem(rel).lower() == name:
                    return self.redirect(v.url(rel))
        recent = sorted(idx.notes, key=lambda r: -(v.info(r) or {'mtime': 0})['mtime'])[:24]
        cards = ''.join('<a class="card" href="%s"><b>%s</b><p>%s</p><small>%s%s</small></a>'
                        % (esc(v.url(r)), esc(stem(r)), esc(plain_snippet(v.info(r)['body'])),
                           esc(posixpath.dirname(r) + ' · ') if '/' in r else '', fmt_time(v.info(r)['mtime']))
                        for r in recent)
        main = ('<div class="content"><h1 class="page-title">%s</h1><p class="lead">%d notes</p>'
                '<div class="quick"><button class="btn primary" id="q-new">%s Nouvelle note</button>'
                '<button class="btn" id="q-search">%s Rechercher <kbd>Ctrl K</kbd></button></div>'
                '%s<p class="lead" style="margin-top:28px;font-size:13px">Astuce : créez une note <code>index</code> '
                'à la racine pour en faire la page d\'accueil de cet espace.</p></div>'
                % (esc(v.name), len(idx.notes), icon('fileplus'), icon('search'),
                   ('<div class="h3">Modifiées récemment</div><div class="cards">%s</div>' % cards) if cards else
                   '<p>Cet espace ne contient encore aucune note.</p>'))
        self.send_page('Accueil', main, idx=idx, nav_on='home')

    def backlink_ctx(self, idx, src, target):
        info = self.vault.info(src)
        if not info:
            return ''
        for i, seg in enumerate(split_code(info['body'])):
            if i % 2:
                continue
            for m in WIKILINK.finditer(seg):
                if m.group(2).strip() and idx.resolve_note(m.group(2), src) == target:
                    ls = seg.rfind('\n', 0, m.start()) + 1
                    le = seg.find('\n', m.end())
                    line = seg[ls:le if le >= 0 else len(seg)].strip()
                    line = WIKILINK.sub(lambda mm: mm.group(4) or (mm.group(2) + (mm.group(3) or '')), line)
                    line = re.sub(r'^(?:[#>*+\-]+\s*|\d+[.)]\s*)+|\[[ xX]\]\s*', '', line)
                    return line[:180]
        return ''

    def send_file(self, p):
        ctype = mimetypes.guess_type(p.name)[0] or 'application/octet-stream'
        major = ctype.split('/')[0]
        if major == 'text':
            ctype = 'text/plain; charset=utf-8'      # jamais interprété comme HTML/JS
        inline = major in ('image', 'audio', 'video', 'text') or ctype == 'application/pdf'
        size = p.stat().st_size
        self.send_response(200)
        self.send_header('Content-Type', ctype)
        self.send_header('Content-Length', str(size))
        csp = "default-src 'none'; img-src 'self' data:; media-src 'self'; style-src 'unsafe-inline'; frame-ancestors 'self'"
        if ctype != 'application/pdf':
            csp += '; sandbox'
        self.security_headers(csp, 'SAMEORIGIN')
        disp = 'inline' if inline else 'attachment'
        self.send_header('Content-Disposition', "%s; filename*=UTF-8''%s" % (disp, urllib.parse.quote(p.name)))
        self.end_headers()
        if self.command != 'HEAD':
            with open(p, 'rb') as f:
                shutil.copyfileobj(f, self.wfile, 256 * 1024)

    def note(self, rel):
        v = self.vault
        p = self.safe(rel)
        if p is None or not p.is_file():
            return self.send_page('Introuvable', '<div class="content"><h1 class="page-title">Note introuvable</h1>'
                                  '<p class="lead">%s</p></div>' % esc(rel), code=404)
        rel = self.rel_of(p)
        if not is_note(p.name):
            return self.send_file(p)

        idx = v.index()
        info = v.info(rel)
        body_html = render(v, idx, rel, info['body'])
        title = stem(rel)
        folders = rel.split('/')[:-1]
        crumbs = ''.join('<span>%s</span><span class="sep">/</span>' % esc(f) for f in folders) + \
            '<b>%s</b><span class="dot" title="Modifications non enregistrées"></span>' % esc(title)
        actions = ('<div class="seg"><button id="m-read" class="on" title="Lecture (Ctrl+E)">%s<span>Lecture</span></button>'
                   '<button id="m-edit" title="Édition (Ctrl+E)">%s<span>Édition</span></button></div>'
                   '<button class="ib" id="b-prev" title="Aperçu côte à côte" hidden>%s</button>'
                   '<button class="ib" id="b-more" title="Plus d\'actions">%s</button>'
                   '<button class="ib" id="b-right" title="Panneau de droite">%s</button>'
                   % (icon('eye'), icon('pencil'), icon('cols'), icon('dots'), icon('rside')))
        tags_meta = ''.join('<a class="tag" href="%s/search?q=%s">#%s</a>' % (v.base, urllib.parse.quote('#' + t), esc(t))
                            for t in sorted(front_tags(info['meta'])))
        fm = ('<details class="fm"><summary>Propriétés</summary><pre>%s</pre></details>'
              % esc(info['meta'])) if info['meta'].strip() else ''
        main = (
            '<div id="view" class="content">'
            '<h1 class="title" id="ntitle" contenteditable="plaintext-only" spellcheck="false" title="Cliquer pour renommer">%s</h1>'
            '<div class="meta"><span>Modifiée le %s</span><span id="words"></span>%s</div>%s'
            '<article class="md" id="art">%s</article></div>'
            '<div id="editor" hidden><div class="edwrap"><textarea id="src" spellcheck="true" lang="fr" '
            'placeholder="Commencez à écrire…  ([[ pour lier une note)">\n%s</textarea>'
            '<div id="preview" class="md"></div></div>'
            '<div class="edfoot"><span id="status" class="status">Sauvegarde automatique</span><span class="sp"></span>'
            '<span id="pos"></span><span id="wc"></span><span><kbd>?</kbd> raccourcis</span></div></div>'
        ) % (esc(title), fmt_time(info['mtime']), tags_meta, fm, body_html, esc(read_raw(p)))

        back = sorted((n for n in idx.notes if n != rel and rel in idx.out_links(v, n)), key=str.lower)
        outl = sorted(idx.out_links(v, rel), key=str.lower)
        right = '<div class="panel"><div class="sec"><span>Plan</span><span class="n" id="outline-n">0</span></div><div id="outline"></div>'
        right += '<div class="sec"><span>Rétroliens</span><span class="n">%d</span></div>' % len(back)
        if back:
            for b in back:
                ctx = self.backlink_ctx(idx, b, rel)
                right += '<a class="item" href="%s" title="%s"><span class="nm">%s</span>%s</a>' % (
                    esc(v.url(b)), esc(b), esc(stem(b)), '<span class="ctx">%s</span>' % esc(ctx) if ctx else '')
        else:
            right += '<p class="empty">Aucune note ne pointe ici.</p>'
        right += '<div class="sec"><span>Liens sortants</span><span class="n">%d</span></div>' % len(outl)
        right += ''.join('<a class="item" href="%s" title="%s"><span class="nm">%s</span></a>'
                         % (esc(v.url(o)), esc(o), esc(stem(o))) for o in outl) or '<p class="empty">Aucun lien.</p>'
        right += '</div>'
        attr = ' data-path="%s" data-mtime="%s"' % (esc(rel), info['mtime'])
        self.send_page(title, main, right, current=rel, idx=idx, mainattr=attr, crumbs=crumbs, actions=actions)

    def search_page(self, q):
        v = self.vault
        idx = v.index()
        results = v.search(idx, q)
        body = ''.join('<a class="sres" href="%s"><b>%s</b><small>%s</small>%s</a>'
                       % (esc(v.url(r)), esc(stem(r)), esc(posixpath.dirname(r)),
                          ''.join('<div class="snip">%s</div>' % s for s in sn)) for _, r, sn in results)
        info = ('%d résultat(s)' % len(results)) if q.strip() else \
            'Astuce : <kbd>Ctrl K</kbd> cherche aussi en direct, depuis n\'importe quelle page. Tapez <code>#tag</code> pour filtrer par tag.'
        main = ('<div class="content"><h1 class="page-title">Recherche</h1>'
                '<form class="searchbig" action="%s/search"><input class="field" name="q" value="%s" placeholder="Mots à chercher, ou #tag" autofocus>'
                '<button class="btn primary">%s Chercher</button></form><p class="lead">%s</p>%s</div>'
                % (v.base, esc(q), icon('search'), info, body))
        self.send_page('Recherche' + (' : ' + q if q else ''), main, idx=idx, nav_on='search')

    def api_peek(self, rel):
        p = self.safe(rel, note=True)
        if p is None or not p.is_file():
            return self.send_json({'error': 'note introuvable'}, 404)
        rel = self.rel_of(p)
        info = self.vault.info(rel)
        self.send_json({'title': stem(rel), 'html': render(self.vault, self.vault.index(), rel, info['body'],
                                                           interactive=False)})

    def api_search(self, q):
        idx = self.vault.index()
        res = self.vault.search(idx, q, limit=8)
        self.send_json({'results': [{'path': r, 'name': stem(r), 'snip': sn[0] if sn else ''} for _, r, sn in res]})

    # --- POST ---
    def _post(self):
        if not self.host_ok():
            return self.send_json({'error': 'hôte refusé'}, 403)
        if not self.origin_ok():
            return self.send_json({'error': 'origine refusée'}, 403)
        path = urllib.parse.urlsplit(self.path).path
        try:
            n = int(self.headers.get('Content-Length') or 0)
        except ValueError:
            n = -1
        is_api = path.startswith('/s/')
        if n < 0 or n > (MAX_BODY if is_api else MAX_FORM):
            self.close_connection = True
            return self.send_json({'error': 'requête trop volumineuse ou invalide'}, 413)
        raw = self.rfile.read(n) if n else b''
        ctype = (self.headers.get('Content-Type') or '').split(';')[0].strip().lower()
        self.load_auth()

        if not is_api:
            if ctype != 'application/x-www-form-urlencoded':
                return self.send_json({'error': 'type de contenu refusé'}, 415)
            try:
                form = {k: v[0] for k, v in urllib.parse.parse_qs(raw.decode('utf-8', 'replace'), keep_blank_values=True,
                                                                  max_num_fields=20).items()}
            except ValueError:
                return self.send_json({'error': 'formulaire invalide'}, 400)
            if path == '/login':
                return self.do_login(form)
            if path == '/signup':
                return self.do_signup(form)
            if not self.user:
                return self.redirect('/login')
            back = '/account' if path.startswith('/account') or path == '/logout-all' or path == '/spaces/delete' else '/'
            if not ct_eq(form.get('csrf'), self.sess['csrf']):
                return self.redirect(back + '?m=expired')
            fn = {'/logout': self.do_logout, '/logout-all': self.do_logout_all, '/spaces/new': self.do_space_new,
                  '/spaces/delete': self.do_space_delete, '/account/password': self.do_password,
                  '/account/delete': self.do_account_delete}.get(path)
            if not fn:
                return self.send_json({'error': 'route inconnue'}, 404)
            return fn(form)

        if not self.user:
            return self.send_json({'error': 'session expirée', 'code': 'auth'}, 401)
        if not ct_eq(self.headers.get('X-CSRF'), self.sess['csrf']):
            return self.send_json({'error': 'jeton CSRF invalide', 'code': 'csrf'}, 403)
        if ctype != 'application/json':
            return self.send_json({'error': 'type de contenu refusé'}, 415)
        m = re.match(r'^/s/([^/]+)/api/(\w+)$', path)
        v = self.store.vault(self.user, m.group(1)) if m else None
        if v is None:
            return self.send_json({'error': 'route inconnue'}, 404)
        self.vault = v
        try:
            data = json.loads(raw or b'{}')
        except ValueError:
            return self.send_json({'error': 'JSON invalide'}, 400)
        if not isinstance(data, dict):
            return self.send_json({'error': 'JSON invalide'}, 400)
        name = m.group(2)
        if name == 'preview':
            return self.api_preview(data)
        fn = {'save': self.api_save, 'new': self.api_new, 'rename': self.api_rename, 'delete': self.api_delete,
              'toggle': self.api_toggle}.get(name)
        if not fn:
            return self.send_json({'error': 'route inconnue'}, 404)
        with v.lock:
            fn(data)

    # --- authentification ---
    def check_pre(self, form):
        c = self.cookies().get(self.cn(pre=True), '')
        return bool(c) and ct_eq(c, form.get('pre'))

    def verify(self, user, pw):
        with HASH_SEM:
            ok = verify_password(pw or '', user['hash'] if user else self.store.dummy)
        return ok and user is not None

    def do_login(self, form):
        name = (form.get('username') or '').strip().lower()[:64]
        pw = (form.get('password') or '')[:PW_MAX]
        nxt = safe_next(form.get('next'))
        if not self.check_pre(form):
            return self.redirect('/login?m=expired')
        ip = self.client_ip()
        wait = self.limiter.wait(ip, name)
        if wait:
            self.log_auth('connexion bloquée (%s)' % name)
            return self.login_page(nxt=nxt, name=name, code=429,
                                   err='Trop de tentatives : réessayez dans %d min.' % max(1, (wait + 59) // 60))
        user = self.store.get(name)
        if not self.verify(user, pw):
            self.limiter.fail(ip, name)
            self.log_auth('échec de connexion (%s)' % name)
            return self.login_page(nxt=nxt, name=name, code=401, err='Identifiant ou mot de passe incorrect.')
        self.limiter.ok(name)
        self.log_auth('connexion (%s)' % name)
        tok = self.store.new_session(user)
        self.redirect(nxt or '/', [self.cookie(self.cn(), tok, SESSION_MAX), self.cookie(self.cn(pre=True), '', 0)])

    def do_signup(self, form):
        if not self.cfg['signup']:
            return self.redirect('/login?m=signup-closed')
        if not self.check_pre(form):
            return self.redirect('/signup')
        name = (form.get('username') or '').strip().lower()[:64]
        pw, pw2 = form.get('password') or '', form.get('password2') or ''
        if not USER_RE.match(name):
            return self.signup_page('Identifiant invalide : 3 à 32 caractères (a-z, 0-9, . _ -).', name, 400)
        prob = password_problem(pw, name)
        if prob:
            return self.signup_page('Mot de passe refusé : %s.' % prob, name, 400)
        if not ct_eq(pw, pw2):
            return self.signup_page('Les deux mots de passe ne correspondent pas.', name, 400)
        if not self.limiter.signup_ok(self.client_ip()):
            return self.signup_page('Trop d\'inscriptions depuis cette adresse : réessayez plus tard.', name, 429)
        try:
            user = self.store.add_user(name, pw)
        except ValueError:
            return self.signup_page('Cet identifiant n\'est pas disponible.', '', 409)
        self.log_auth('inscription (%s)' % name)
        tok = self.store.new_session(user)
        self.redirect('/', [self.cookie(self.cn(), tok, SESSION_MAX), self.cookie(self.cn(pre=True), '', 0)])

    def clear_headers(self):
        return [self.cookie(self.cn(), '', 0), ('Clear-Site-Data', '"cache", "storage"')]

    def do_logout(self, form):
        self.store.drop_session(self.skey)
        self.log_auth('déconnexion (%s)' % self.user['name'])
        self.redirect('/login?m=out', self.clear_headers())

    def do_logout_all(self, form):
        self.store.drop_sessions(self.user['name'], keep=self.skey)
        self.redirect('/account?m=sess-ok')

    def check_password_form(self, pw):
        """Vérifie le mot de passe de l'utilisateur connecté (opérations sensibles)."""
        ip, name = self.client_ip(), self.user['name']
        if self.limiter.wait(ip, name):
            return 'wait'
        if not self.verify(self.user, pw):
            self.limiter.fail(ip, name)
            self.log_auth('mot de passe incorrect (%s)' % name)
            return 'pw-bad'
        self.limiter.ok(name)
        return None

    def do_password(self, form):
        err = self.check_password_form(form.get('current'))
        if err:
            return self.redirect('/account?m=' + err)
        pw = form.get('password') or ''
        if password_problem(pw, self.user['name']):
            return self.redirect('/account?m=pw-weak')
        if not ct_eq(pw, form.get('password2')):
            return self.redirect('/account?m=pw-mismatch')
        user = self.store.set_password(self.user['name'], pw)   # ferme toutes les sessions
        self.log_auth('mot de passe changé (%s)' % user['name'])
        tok = self.store.new_session(user)
        self.redirect('/account?m=pw-ok', [self.cookie(self.cn(), tok, SESSION_MAX)])

    def do_space_new(self, form):
        name = slugify(form.get('name') or '')[:40].strip('-_')
        if not SPACE_RE.match(name):
            return self.redirect('/?m=space-bad')
        spaces = self.store.list_spaces(self.user)
        if name in spaces:
            return self.redirect('/?m=space-exists')
        if len(spaces) >= MAX_SPACES:
            return self.redirect('/?m=space-max')
        try:
            self.store.create_space(self.user, name)
        except FileExistsError:
            return self.redirect('/?m=space-exists')
        self.redirect('/s/%s/' % name)

    def do_space_delete(self, form):
        space = form.get('space') or ''
        if space not in self.store.list_spaces(self.user):
            return self.redirect('/account?m=confirm')
        err = self.check_password_form(form.get('password'))
        if err:
            return self.redirect('/account?m=' + err)
        self.store.delete_space(self.user, space)
        self.log_auth('espace supprimé (%s/%s)' % (self.user['name'], space))
        self.redirect('/?m=space-del')

    def do_account_delete(self, form):
        if (form.get('confirm') or '').strip().lower() != self.user['name']:
            return self.redirect('/account?m=confirm')
        err = self.check_password_form(form.get('password'))
        if err:
            return self.redirect('/account?m=' + err)
        self.store.delete_user(self.user['name'])
        self.log_auth('compte supprimé (%s)' % self.user['name'])
        self.redirect('/login?m=deleted', self.clear_headers())

    # --- API d'écriture d'un espace ---
    def _target(self, name, base):
        name = (name or '').strip().replace('\\', '/').strip('/') if isinstance(name, str) else ''
        if not isinstance(base, str):
            base = ''
        if not name or '\x00' in name or len(name) > 512:
            return None, 'nom vide ou trop long'
        if not is_note(name):
            name += '.md'
        rel = posixpath.normpath(name if ('/' in name or not base) else posixpath.join(base, name))
        if rel.startswith('..') or any(part.startswith('.') for part in rel.split('/')):
            return None, 'nom invalide'
        p = self.safe(rel, note=True)
        return (p, None) if p else (None, 'chemin invalide')

    def api_save(self, d):
        p = self.safe(d.get('path'), note=True)
        content = d.get('content', '')
        if p is None or not isinstance(content, str):
            return self.send_json({'error': 'chemin invalide'}, 400)
        old = 0
        if p.exists():
            cur = str(p.stat().st_mtime_ns)
            if d.get('mtime') and str(d['mtime']) != cur and not d.get('force'):
                return self.send_json({'error': 'fichier modifié ailleurs', 'mtime': cur}, 409)
            with open(p, 'rb') as f:
                if b'\r\n' in f.read(65536):
                    content = content.replace('\r\n', '\n').replace('\n', '\r\n')
            old = p.stat().st_size
        if not self.store.quota_ok(self.user, len(content.encode('utf-8')) - old):
            return self.send_json({'error': 'quota de stockage dépassé'}, 413)
        if not p.exists():
            p.parent.mkdir(parents=True, exist_ok=True)
        atomic_write(p, content)
        self.send_json({'ok': True, 'mtime': str(p.stat().st_mtime_ns)})

    def api_preview(self, d):
        p = self.safe(d.get('path'), note=True)
        content = d.get('content', '')
        if p is None or not isinstance(content, str):
            return self.send_json({'error': 'chemin invalide'}, 400)
        rel = self.rel_of(p)
        _, body = split_front(content)
        self.send_json({'html': render(self.vault, self.vault.index(), rel, body, interactive=bool(d.get('interactive')))})

    def api_new(self, d):
        p, err = self._target(d.get('name'), d.get('base') or '')
        if err:
            return self.send_json({'error': err}, 400)
        if not p.exists():
            if not self.store.quota_ok(self.user, 4096):
                return self.send_json({'error': 'quota de stockage dépassé'}, 413)
            p.parent.mkdir(parents=True, exist_ok=True)
            atomic_write(p, '')
        self.send_json({'url': self.vault.url(self.rel_of(p)) + '?edit=1'})

    def api_rename(self, d):
        src = self.safe(d.get('path'), note=True)
        if src is None or not src.is_file():
            return self.send_json({'error': 'note introuvable'}, 404)
        old_rel = self.rel_of(src)
        dst, err = self._target(d.get('name'), posixpath.dirname(old_rel))
        if err:
            return self.send_json({'error': err}, 400)
        if dst.exists() and dst != src:
            return self.send_json({'error': 'une note porte déjà ce nom'}, 409)
        new_rel = self.rel_of(dst)
        idx = self.vault.index()
        new_stem = stem(new_rel)
        if len(idx.by_stem.get(new_stem.lower(), [])) > (1 if stem(old_rel).lower() == new_stem.lower() else 0):
            new_target = new_rel.rsplit('.', 1)[0]   # nom ambigu : on écrit le chemin
        else:
            new_target = new_stem
        updated = 0
        for n in idx.notes:
            info = self.vault.info(n)
            if not info or not any(idx.resolve_note(t, n) == old_rel for t in info['wl']):
                continue
            np_ = self.vault.root / n
            raw = read_raw(np_)

            def fix(m):
                if m.group(2).strip() and idx.resolve_note(m.group(2), n) == old_rel:
                    return '%s[[%s%s%s]]' % (m.group(1), new_target, m.group(3) or '',
                                             '|' + m.group(4) if m.group(4) is not None else '')
                return m.group(0)
            parts = FENCE.split(raw)
            for i in range(0, len(parts), 2):
                parts[i] = WIKILINK.sub(fix, parts[i])
            new_raw = ''.join(parts)
            if new_raw != raw:
                atomic_write(np_, new_raw)
                updated += 1
        dst.parent.mkdir(parents=True, exist_ok=True)
        os.rename(src, dst)
        self.send_json({'url': self.vault.url(new_rel), 'updated': updated})

    def api_delete(self, d):
        p = self.safe(d.get('path'), note=True)
        if p is None or not p.is_file():
            return self.send_json({'error': 'note introuvable'}, 404)
        trash = self.vault.root / '.trash'
        trash.mkdir(exist_ok=True)
        dest = trash / p.name
        k = 1
        while dest.exists():
            dest = trash / ('%s (%d)%s' % (p.stem, k, p.suffix))
            k += 1
        shutil.move(str(p), str(dest))
        self.send_json({'url': self.vault.base + '/'})

    def api_toggle(self, d):
        p = self.safe(d.get('path'), note=True)
        if p is None or not p.is_file():
            return self.send_json({'error': 'note introuvable'}, 404)
        cur = str(p.stat().st_mtime_ns)
        if d.get('mtime') and str(d['mtime']) != cur:
            return self.send_json({'error': 'fichier modifié ailleurs, rechargez la page'}, 409)
        raw = read_raw(p)
        m = FRONT.match(raw)
        head, body = (raw[:m.end()], raw[m.end():]) if m else ('', raw)
        try:
            target = int(d.get('index', -1))
        except (TypeError, ValueError):
            return self.send_json({'error': 'index invalide'}, 400)
        count, done = [0], [False]

        def flip(mm):
            i = count[0]
            count[0] += 1
            if i == target:
                done[0] = True
                return mm.group(1) + (' ' if mm.group(2).lower() == 'x' else 'x') + mm.group(3)
            return mm.group(0)
        parts = FENCE.split(body)
        for i in range(0, len(parts), 2):
            parts[i] = TASK_SRC.sub(flip, parts[i])
        if not done[0]:
            return self.send_json({'error': 'case introuvable'}, 400)
        new_raw = head + ''.join(parts)
        atomic_write(p, new_raw)
        self.send_json({'ok': True, 'mtime': str(p.stat().st_mtime_ns), 'content': new_raw.replace('\r\n', '\n')})


# --------------------------------------------------------------------------
# Ligne de commande
# --------------------------------------------------------------------------

def ask_password(name):
    for _ in range(3):
        pw = getpass.getpass('Mot de passe pour « %s » : ' % name)
        prob = password_problem(pw, name)
        if prob:
            print('  Refusé : %s.' % prob)
            continue
        if getpass.getpass('Confirmer : ') != pw:
            print('  Les mots de passe ne correspondent pas.')
            continue
        return pw
    sys.exit('Abandon.')


def main():
    ap = argparse.ArgumentParser(description='Notes Markdown multi-utilisateur dans le navigateur.')
    ap.add_argument('dossier', nargs='?', default='mdvault-data', help='dossier des données (défaut : ./mdvault-data)')
    ap.add_argument('-p', '--port', type=int, default=8765, help='port (défaut : 8765)')
    ap.add_argument('--host', default='127.0.0.1', help='adresse d\'écoute (défaut : 127.0.0.1)')
    ap.add_argument('--no-browser', action='store_true', help='ne pas ouvrir le navigateur')
    ap.add_argument('--signup', action='store_true', help='autoriser l\'inscription publique (désactivée par défaut)')
    ap.add_argument('--quota', type=int, default=200, metavar='MO', help='quota par utilisateur en Mo (0 = illimité, défaut : 200)')
    ap.add_argument('--cert', help='certificat TLS (PEM) pour servir en HTTPS')
    ap.add_argument('--key', help='clé privée TLS (PEM)')
    ap.add_argument('--proxy', action='store_true',
                    help='derrière un reverse proxy HTTPS local : cookies Secure, IP lue dans X-Forwarded-For')
    ap.add_argument('--allow-host', action='append', default=[], metavar='NOM',
                    help='nom d\'hôte accepté dans l\'en-tête Host (répétable)')
    g = ap.add_argument_group('gestion des comptes')
    g.add_argument('--add-user', metavar='NOM')
    g.add_argument('--passwd', metavar='NOM')
    g.add_argument('--del-user', metavar='NOM')
    g.add_argument('--list-users', action='store_true')
    args = ap.parse_args()

    os.umask(0o077)
    store = Store(args.dossier, quota=max(0, args.quota) * 1024 * 1024)

    if args.list_users:
        us = store.users()
        for n, u in sorted(us.items()):
            print('%-32s créé le %s  espaces : %s' % (n, time.strftime('%d/%m/%Y', time.localtime(u.get('created', 0))),
                                                     ', '.join(store.list_spaces(u)) or '—'))
        if not us:
            print('Aucun utilisateur.')
        return
    if args.add_user:
        name = args.add_user.strip().lower()
        if not USER_RE.match(name):
            sys.exit('Identifiant invalide : 3 à 32 caractères (a-z, 0-9, . _ -).')
        if store.get(name):
            sys.exit('Cet identifiant existe déjà.')
        store.add_user(name, ask_password(name))
        print('Utilisateur « %s » créé (espace « notes »).' % name)
        return
    if args.passwd:
        name = args.passwd.strip().lower()
        if not store.get(name):
            sys.exit('Utilisateur inconnu.')
        store.set_password(name, ask_password(name))
        print('Mot de passe modifié ; les sessions de « %s » ont été fermées.' % name)
        return
    if args.del_user:
        name = args.del_user.strip().lower()
        if not store.get(name):
            sys.exit('Utilisateur inconnu.')
        if input('Supprimer « %s » et TOUTES ses notes ? Tapez son nom pour confirmer : ' % name).strip().lower() != name:
            sys.exit('Abandon.')
        store.delete_user(name)
        print('Utilisateur supprimé.')
        return

    if bool(args.cert) != bool(args.key):
        sys.exit('Erreur : --cert et --key vont ensemble.')
    local = args.host in ('127.0.0.1', 'localhost', '::1')
    hosts = {h.strip().lower() for h in args.allow_host if h.strip()}
    if local:
        hosts |= {'127.0.0.1', 'localhost', '[::1]'}
    Handler.store = store
    Handler.limiter = Limiter()
    Handler.cfg = {'secure': bool(args.cert) or args.proxy, 'signup': args.signup, 'proxy': args.proxy, 'hosts': hosts}

    if not store.users() and not args.signup:
        print('Aucun utilisateur pour l\'instant.')
        if sys.stdin.isatty():
            name = input('Identifiant du premier utilisateur : ').strip().lower()
            if not USER_RE.match(name):
                sys.exit('Identifiant invalide : 3 à 32 caractères (a-z, 0-9, . _ -).')
            store.add_user(name, ask_password(name))
            print('Utilisateur « %s » créé.' % name)
        else:
            print('Créez-en un avec : python3 %s %s --add-user NOM' % (sys.argv[0], args.dossier))

    server = None
    for port in range(args.port, args.port + 20):
        try:
            server = ThreadingHTTPServer((args.host, port), Handler)
            break
        except OSError:
            continue
    if server is None:
        sys.exit('Erreur : aucun port libre à partir de %d.' % args.port)
    server.daemon_threads = True
    if args.cert:
        ctx = ssl.SSLContext(ssl.PROTOCOL_TLS_SERVER)
        ctx.minimum_version = ssl.TLSVersion.TLSv1_2
        ctx.load_cert_chain(args.cert, args.key)
        server.socket = ctx.wrap_socket(server.socket, server_side=True, do_handshake_on_connect=False)

    shown = 'localhost' if args.host in ('127.0.0.1', '0.0.0.0', '::') else args.host
    url = '%s://%s:%d/' % ('https' if args.cert else 'http', shown, server.server_address[1])
    print('📚 mdvault — données : %s' % store.data)
    print('   %s   (Ctrl+C pour quitter)' % url)
    if _markdown is None:
        print('   (rendu intégré ; pour un rendu plus complet : sudo apt install python3-markdown python3-pygments)')
    if not local and not args.cert and not args.proxy:
        print('   ⚠  Accessible depuis le réseau SANS chiffrement : les mots de passe circulent en clair.\n'
              '      Utilisez --cert/--key, ou un reverse proxy HTTPS avec --proxy.')
    if args.signup:
        print('   ⚠  Inscription publique activée.')
    if not args.no_browser and local:
        threading.Timer(0.6, lambda: webbrowser.open(url)).start()
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        print('\nAu revoir.')
    finally:
        server.server_close()


if __name__ == '__main__':
    main()
