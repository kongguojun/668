import base64
import json
import re
import threading
import time
import secrets
from collections import OrderedDict
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from urllib.parse import urlsplit, urljoin, unquote
from urllib.request import Request, urlopen, build_opener, ProxyHandler
from urllib.error import URLError

try:
    from base.spider import Spider as BaseSpider
except ModuleNotFoundError as error:
    if error.name not in ("base", "base.spider"):
        raise
    BaseSpider = object

try:
    from Crypto.Cipher import AES as NativeAES
except ImportError:
    NativeAES = None


class _PureAES128:
    """纯 Python AES-128，供无 pycryptodome/cryptography 的壳使用。"""

    _S = (
        99,124,119,123,242,107,111,197,48,1,103,43,254,215,171,118,202,130,201,125,250,89,71,240,
        173,212,162,175,156,164,114,192,183,253,147,38,54,63,247,204,52,165,229,241,113,216,49,21,
        4,199,35,195,24,150,5,154,7,18,128,226,235,39,178,117,9,131,44,26,27,110,90,160,82,59,214,
        179,41,227,47,132,83,209,0,237,32,252,177,91,106,203,190,57,74,76,88,207,208,239,170,251,67,
        77,51,133,69,249,2,127,80,60,159,168,81,163,64,143,146,157,56,245,188,182,218,33,16,255,243,
        210,205,12,19,236,95,151,68,23,196,167,126,61,100,93,25,115,96,129,79,220,34,42,144,136,70,
        238,184,20,222,94,11,219,224,50,58,10,73,6,36,92,194,211,172,98,145,149,228,121,231,200,55,
        109,141,213,78,169,108,86,244,234,101,122,174,8,186,120,37,46,28,166,180,198,232,221,116,31,
        75,189,139,138,112,62,181,102,72,3,246,14,97,53,87,185,134,193,29,158,225,248,152,17,105,
        217,142,148,155,30,135,233,206,85,40,223,140,161,137,13,191,230,66,104,65,153,45,15,176,84,
        187,22
    )
    _RCON = (0x00,0x01,0x02,0x04,0x08,0x10,0x20,0x40,0x80,0x1B,0x36)

    def __init__(self, key: bytes):
        if len(key) != 16:
            raise ValueError("AES-128 only")
        self._rk = self._expand(key)

    def _expand(self, key: bytes):
        s = self._S
        w = list(key)
        for i in range(4, 44):
            t0, t1, t2, t3 = w[-4], w[-3], w[-2], w[-1]
            if i % 4 == 0:
                t0, t1, t2, t3 = s[t1], s[t2], s[t3], s[t0]
                t0 ^= self._RCON[i // 4]
            base = (i - 4) * 4
            w.extend((w[base] ^ t0, w[base + 1] ^ t1, w[base + 2] ^ t2, w[base + 3] ^ t3))
        return w

    @staticmethod
    def _xtime(a: int) -> int:
        return ((a << 1) ^ 0x1B) & 0xFF if (a & 0x80) else ((a << 1) & 0xFF)

    def encrypt_block(self, block: bytes) -> bytes:
        s = list(block)
        rk = self._rk
        for i in range(16):
            s[i] ^= rk[i]
        for rnd in range(1, 10):
            s = [self._S[b] for b in s]
            s = [s[0], s[5], s[10], s[15], s[4], s[9], s[14], s[3],
                 s[8], s[13], s[2], s[7], s[12], s[1], s[6], s[11]]
            for c in range(4):
                i = c * 4
                a, b, c0, d = s[i], s[i + 1], s[i + 2], s[i + 3]
                t = a ^ b ^ c0 ^ d
                u = a
                a ^= t ^ self._xtime(a ^ b)
                b ^= t ^ self._xtime(b ^ c0)
                c0 ^= t ^ self._xtime(c0 ^ d)
                d ^= t ^ self._xtime(d ^ u)
                s[i], s[i + 1], s[i + 2], s[i + 3] = a, b, c0, d
            off = rnd * 16
            for i in range(16):
                s[i] ^= rk[off + i]
        s = [self._S[b] for b in s]
        s = [s[0], s[5], s[10], s[15], s[4], s[9], s[14], s[3],
             s[8], s[13], s[2], s[7], s[12], s[1], s[6], s[11]]
        for i in range(16):
            s[i] ^= rk[160 + i]
        return bytes(s)

    def decrypt_block(self, block: bytes) -> bytes:
        s = list(block)
        rk = self._rk
        for i in range(16):
            s[i] ^= rk[160 + i]
        for rnd in range(9, 0, -1):
            s = [s[0], s[13], s[10], s[7], s[4], s[1], s[14], s[11],
                 s[8], s[5], s[2], s[15], s[12], s[9], s[6], s[3]]
            s = [self._SI[b] for b in s]
            off = rnd * 16
            for i in range(16):
                s[i] ^= rk[off + i]
            for c in range(4):
                i = c * 4
                a, b, c0, d = s[i], s[i + 1], s[i + 2], s[i + 3]
                s[i] = _MUL14[a] ^ _MUL11[b] ^ _MUL13[c0] ^ _MUL9[d]
                s[i + 1] = _MUL9[a] ^ _MUL14[b] ^ _MUL11[c0] ^ _MUL13[d]
                s[i + 2] = _MUL13[a] ^ _MUL9[b] ^ _MUL14[c0] ^ _MUL11[d]
                s[i + 3] = _MUL11[a] ^ _MUL13[b] ^ _MUL9[c0] ^ _MUL14[d]
        s = [s[0], s[13], s[10], s[7], s[4], s[1], s[14], s[11],
             s[8], s[5], s[2], s[15], s[12], s[9], s[6], s[3]]
        s = [self._SI[b] for b in s]
        for i in range(16):
            s[i] ^= rk[i]
        return bytes(s)


_PureAES128._SI = tuple(_PureAES128._S.index(value) for value in range(256))
_MUL2 = tuple(_PureAES128._xtime(value) for value in range(256))
_MUL4 = tuple(_MUL2[value] for value in _MUL2)
_MUL8 = tuple(_MUL2[value] for value in _MUL4)
_MUL9 = tuple(_MUL8[value] ^ value for value in range(256))
_MUL11 = tuple(_MUL8[value] ^ _MUL2[value] ^ value for value in range(256))
_MUL13 = tuple(_MUL8[value] ^ _MUL4[value] ^ value for value in range(256))
_MUL14 = tuple(_MUL8[value] ^ _MUL4[value] ^ _MUL2[value] for value in range(256))


def _decrypt(data, key, iv):
    if not data or len(data) % 16:
        raise ValueError("AES密文长度无效")
    if NativeAES is not None:
        plain = NativeAES.new(key, NativeAES.MODE_CBC, iv).decrypt(data)
    else:
        cipher = _PureAES128(key)
        plain = bytearray()
        previous = iv
        for offset in range(0, len(data), 16):
            block = data[offset:offset + 16]
            plain.extend(left ^ right for left, right in zip(cipher.decrypt_block(block), previous))
            previous = block
        plain = bytes(plain)
    padding = plain[-1]
    if not 1 <= padding <= 16 or plain[-padding:] != bytes([padding]) * padding:
        raise ValueError("AES填充无效，接口或密钥可能已变化")
    return plain[:-padding]


def _media_type(data):
    if data.startswith(b"\xff\xd8\xff"):
        return "image/jpeg"
    if data.startswith(b"\x89PNG\r\n\x1a\n"):
        return "image/png"
    if data.startswith((b"GIF87a", b"GIF89a")):
        return "image/gif"
    if data.startswith(b"RIFF") and data[8:12] == b"WEBP":
        return "image/webp"
    return ""



from html import unescape
from html.parser import HTMLParser
from urllib.parse import quote

SITES = ("https://yv6e.zekpkeusp.cc", "https://fe0g.zekpkeusp.cc", "https://huangguoai.com")
SITE = SITES[0]
UA = "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 Chrome/120.0.0.0 Safari/537.36"
MEDIA_KEY, MEDIA_IV = b"f5d965df75336270", b"97b60394abc2fbe1"
CATEGORIES = [("ranks/hot", "排行榜"), ("ai-duanju", "AI成人短剧"), ("ai-manju", "AI成人漫剧")]


def text(value):
    return unescape(re.sub(r"<[^>]+>", "", str(value or ""))).strip()


class Page(HTMLParser):
    """Read cards, episode anchors and videoInitialData without external packages."""
    def __init__(self, source):
        super().__init__(convert_charrefs=True)
        self.cards, self.anchors, self.headings = [], [], []
        self.card = self.anchor = None
        self.depth = 0
        self.hidden = []
        self.heading = None
        self.script = None
        self.initial_raw = ""
        self.meta_pic = ""
        self.feed(source)
        try:
            self.initial = json.loads(self.initial_raw) if self.initial_raw else {}
        except ValueError:
            self.initial = {}

    def handle_starttag(self, tag, attrs):
        a = dict(attrs)
        classes = a.get("class", "").split()
        # Inactive tabs can keep their cards in a separate template.
        if tag == "template" or (tag == "div" and (self.hidden or "hidden" in a or "hg-search-suggest" in classes)):
            self.hidden.append(tag)
        if self.hidden:
            return
        if tag == "div":
            if "hg-drama-card" in classes or "hg-rank-item" in classes:
                title = (a.get("data-track-title") or "").strip() if "hg-rank-item" in classes else ""
                self.card = {"id": "", "title": title, "pic": "", "remarks": ""}
                self.cards.append(self.card)
                self.depth = 0
            if self.card is not None:
                self.depth += 1
        if tag == "a":
            self.anchor = {"url": a.get("href", ""), "ep": a.get("data-ep-id", ""), "text": "", "class": a.get("class", "")}
            self.anchors.append(self.anchor)
            m = re.search(r"/(?:video|detail)/(\d+)(?:/|$)", self.anchor["url"])
            if self.card is not None and m:
                self.card["id"] = m[1]
        if tag == "img" and self.card is not None and not self.card["pic"]:
            self.card["pic"] = a.get("data-src") or a.get("src", "")
        if tag in ("h1", "title"):
            self.heading = [tag, ""]
        if tag == "meta" and (a.get("property") or a.get("name")) == "og:image":
            self.meta_pic = a.get("content", "")
        if tag == "script" and a.get("id") == "videoInitialData":
            self.script = True

    def handle_data(self, data):
        if self.hidden:
            return
        if self.script:
            self.initial_raw += data
        if self.anchor is not None:
            self.anchor["text"] += data
        if self.heading is not None:
            self.heading[1] += data

    def handle_endtag(self, tag):
        if self.hidden:
            if tag == self.hidden[-1]:
                self.hidden.pop()
            return
        if tag == "script":
            self.script = None
        if tag == "a" and self.anchor is not None:
            if self.card is not None and self.anchor["text"].strip():
                if "title" in self.anchor["class"] or not self.card["title"]:
                    self.card["title"] = self.anchor["text"].strip()
            self.anchor = None
        if self.heading is not None and tag == self.heading[0]:
            self.headings.append(self.heading)
            self.heading = None
        if tag == "div" and self.card is not None:
            self.depth -= 1
            if self.depth <= 0:
                self.card = None


class Spider(BaseSpider):
    def __init__(self):
        self.site = SITE
        self.sites = list(SITES)
        self.timeout = 20
        self.opener = None
        self.picture_server = None
        self.picture_thread = None
        self.picture_lock = threading.RLock()
        self.pictures = OrderedDict()
        self.picture_tokens = {}
        self.picture_cache = OrderedDict()

    def getName(self):
        return "黄果短剧·Python设备版"

    def init(self, extend=""):
        if isinstance(extend, str) and extend.strip():
            extend = json.loads(extend) if extend.lstrip().startswith("{") else {"site": extend}
        if isinstance(extend, dict):
            self.timeout = max(3, min(30, int(extend.get("timeout", 20))))
            site = str(extend.get("site") or SITE).rstrip("/")
            if urlsplit(site).scheme not in ("http", "https") or not urlsplit(site).hostname:
                raise ValueError("无效的黄果网站地址")
            self.site = site
            self.sites = [site] + [value for value in SITES if value != site]
            proxy = str(extend.get("proxy") or "").strip()
            if proxy:
                parsed = urlsplit(proxy)
                if parsed.scheme != "http" or not parsed.hostname or not parsed.port:
                    raise ValueError("proxy 请填写 HTTP 代理地址，例如 http://192.168.31.12:7890")
                self.opener = build_opener(ProxyHandler({"http": proxy, "https": proxy}))
            else:
                self.opener = None

    def _open(self, request, timeout):
        if self.opener is not None:
            return self.opener.open(request, timeout=timeout)
        return urlopen(request, timeout=timeout)

    def _headers(self, site=None):
        return {"User-Agent": UA, "Referer": (site or self.site) + "/",
                "Accept": "*/*", "Accept-Language": "zh-CN,zh;q=0.9"}

    def _html(self, address):
        parsed = urlsplit(urljoin(self.site + "/", address))
        path = parsed.path + ("?" + parsed.query if parsed.query else "")
        errors = []
        for site in [self.site] + [value for value in self.sites if value != self.site]:
            try:
                request = Request(site + path, headers=self._headers(site))
                with self._open(request, timeout=self.timeout) as response:
                    data = response.read(6 * 1024 * 1024 + 1)
                    encoding = response.headers.get_content_charset() or "utf-8"
                if len(data) > 6 * 1024 * 1024:
                    raise ValueError("黄果网页过大")
                source = data.decode(encoding, errors="replace")
                if not any(marker in source for marker in ("hg-drama-card", "hg-rank", "videoInitialData", "hg-web-", "hg-card-grid")):
                    raise ValueError("线路未返回黄果内容页面")
                self.site = site
                return source
            except Exception as error:
                errors.append(site + ": " + str(error))
        raise ValueError("黄果线路请求失败：" + "; ".join(errors))

    def _list(self, source):
        page = source if isinstance(source, Page) else Page(source)
        cards = page.cards
        if not cards:
            cards = [{"id": m.group(1), "title": a["text"].strip(), "pic": "", "remarks": ""}
                     for a in page.anchors
                     if (m := re.search(r"/(?:video|detail)/(\d+)(?:/|$)", a["url"])) and a["text"].strip()]
        result, seen = [], set()
        for card in cards:
            if not card["id"] or not card["title"] or card["id"] in seen:
                continue
            seen.add(card["id"])
            result.append({"vod_id": card["id"], "vod_name": card["title"],
                           "vod_pic": self._picture(card["pic"]), "vod_remarks": card["remarks"]})
        return result

    def homeContent(self, filter):
        return {"class": [{"type_id": key, "type_name": name} for key, name in CATEGORIES]}

    def homeVideoContent(self):
        return {"list": self._list(self._html("/"))}

    def categoryContent(self, tid, pg, filter, extend):
        tid = str(tid).strip("/")
        if tid not in dict(CATEGORIES) and tid != "home":
            raise ValueError("未知分类")
        return self._listing("/" if tid == "home" else "/" + tid + "/", pg)

    def _listing(self, path, pg):
        page = max(1, int(pg or 1))
        address = path + (str(page) + "/" if page > 1 else "")
        parsed = Page(self._html(address))
        items = self._list(parsed)
        next_path = path + str(page + 1) + "/"
        base = self.site + address
        next_page = page + 1 if any(urlsplit(urljoin(base, link["url"])).path == next_path
                                    for link in parsed.anchors) else page
        return {"list": items, "page": page, "pagecount": next_page, "limit": len(items) or 20,
                "total": (next_page - 1) * (len(items) or 20) + len(items)}

    def searchContent(self, key, quick=False, pg="1"):
        if not str(key).strip():
            return {"list": [], "page": 1, "pagecount": 1}
        return self._listing("/search/video/" + quote(str(key).strip(), safe="") + "/", pg)

    def detailContent(self, ids):
        result = []
        for video_id in ids:
            video_id = str(video_id)
            if not video_id.isdigit():
                raise ValueError("无效视频编号")
            default = self.site + "/video/" + video_id + "/"
            page = Page(self._html(default))
            episodes = {}
            for a in page.anchors:
                address = urljoin(self.site + "/", a["url"])
                m = re.search(r"/(?:video|detail)/" + video_id + r"/(?:ep-(\d+)/?)?", urlsplit(address).path)
                if not m:
                    continue
                number = a["ep"] or m.group(1)
                if not number:
                    n = re.search(r"\d+", a["text"])
                    number = n.group() if n else "1"
                if str(number).isdigit():
                    episodes.setdefault(int(number), address)
            if not episodes:
                episodes[1] = default
            title = next((v for t, v in page.headings if t == "h1"), "")
            title = title or next((v for t, v in page.headings if t == "title"), video_id)
            result.append({"vod_id": video_id, "vod_name": text(title),
                           "vod_pic": self._picture(page.initial.get("coverSrc") or page.meta_pic),
                           "vod_play_from": "黄果", "vod_play_url": "#".join(
                               "第%d集$%s|||%d" % (number, address, number) for number, address in sorted(episodes.items()))})
        return {"list": result}

    def playerContent(self, flag, id, vipFlags=None):
        parts = str(id).split("|||")
        address = urljoin(self.site + "/", parts[0])
        if urlsplit(address).netloc not in {urlsplit(site).netloc for site in self.sites} or not re.search(r"/(?:video|detail)/\d+/", urlsplit(address).path):
            raise ValueError("无效剧集地址")
        number = parts[1] if len(parts) > 1 else "1"
        video_id = re.search(r"/(?:video|detail)/(\d+)/", urlsplit(address).path).group(1)
        play, reason = "", ""
        # 网页里的 epPlaySrcs/videoSrc 现在是空的，播放地址改由播放接口下发。
        if number.isdigit():
            try:
                play = self._playback(video_id, number)
            except ValueError as error:
                reason = str(error)
        if not play:
            # 接口不可用时退回旧的网页内嵌地址。
            source = self._html(address)
            data = Page(source).initial
            sources = data.get("epPlaySrcs") or {}
            play = sources.get(number, "") if isinstance(sources, dict) else ""
            # Do not silently play another episode when an explicit mapping exists.
            if not play and not sources:
                play = data.get("videoSrc", "")
                if not play:
                    m = re.search(r'https?://[^\s\'"<>]+\.m3u8(?:\?[^\s\'"<>]*)?', source.replace(r"\/", "/"))
                    play = m.group() if m else ""
        play = unescape(str(play)).replace(r"\/", "/").replace(r"\u0026", "&")
        play = urljoin(self.site + "/", play) if play else ""
        if urlsplit(play).scheme not in ("http", "https"):
            raise ValueError("黄果未返回当前集播放地址，网站结构或访问状态可能变化" + ("（" + reason + "）" if reason else ""))
        return {"parse": 0, "jx": 0, "url": play, "header": self._headers()}

    def _playback(self, video_id, number):
        errors = []
        for site in [self.site] + [value for value in self.sites if value != self.site]:
            try:
                headers = self._headers(site)
                headers.update({"Content-Type": "application/json", "Origin": site})
                request = Request("%s/api/videos/%s/episodes/%s/playback" % (site, video_id, number),
                                  data=b"{}", headers=headers)
                with self._open(request, timeout=self.timeout) as response:
                    body = response.read(1024 * 1024 + 1)
                if len(body) > 1024 * 1024:
                    raise ValueError("播放接口响应过大")
                result = json.loads(body.decode("utf-8-sig"))
                data = result.get("data") if isinstance(result, dict) else None
                if not isinstance(data, dict) or result.get("status") != 1:
                    raise ValueError(str(isinstance(result, dict) and result.get("msg") or "播放接口未返回数据"))
                # 不匹配时宁可报错，也不要悄悄播成别的集。
                if str(data.get("id")) != str(video_id) or str(data.get("ep")) != str(number):
                    raise ValueError("播放接口返回的剧集不匹配")
                streams = data.get("streams")
                play = streams.get("main") if isinstance(streams, dict) else ""
                if not play:
                    raise ValueError("播放接口未返回地址")
                self.site = site
                return str(play)
            except Exception as error:
                errors.append(site + ": " + str(error))
        raise ValueError("黄果播放接口请求失败：" + "; ".join(errors))

    def isVideoFormat(self, url):
        return False

    def manualVideoCheck(self):
        return False

    def localProxy(self, param):
        return [404, "text/plain", b"Video plays directly from CDN"]

    def _start_picture_server(self):
        with self.picture_lock:
            if self.picture_server is not None:
                return self.picture_server.server_port
            owner = self

            class Handler(BaseHTTPRequestHandler):
                def do_GET(self):
                    token = urlsplit(self.path).path.removeprefix("/image/")
                    try:
                        mime, data = owner._picture_data(token)
                        self.send_response(200)
                        self.send_header("Content-Type", mime)
                        self.send_header("Content-Length", str(len(data)))
                        self.send_header("Cache-Control", "private, max-age=3600")
                        self.end_headers()
                        self.wfile.write(data)
                    except (BrokenPipeError, ConnectionResetError):
                        pass
                    except Exception:
                        self.send_error(502, "Image unavailable")

                def log_message(self, *args):
                    pass

            self.picture_server = ThreadingHTTPServer(("127.0.0.1", 0), Handler)
            self.picture_server.daemon_threads = True
            self.picture_thread = threading.Thread(target=self.picture_server.serve_forever, daemon=True)
            self.picture_thread.start()
            return self.picture_server.server_port

    def _picture(self, address):
        if not address:
            return ""
        address = urljoin(self.site + "/", str(address))
        if urlsplit(address).scheme not in ("http", "https"):
            return ""
        port = self._start_picture_server()
        with self.picture_lock:
            if address not in self.picture_tokens:
                token = secrets.token_hex(16)
                self.picture_tokens[address] = token
                self.pictures[token] = (address, self.site)
                while len(self.pictures) > 1024:
                    old_token, (old_address, _) = self.pictures.popitem(last=False)
                    self.picture_tokens.pop(old_address, None)
                    self.picture_cache.pop(old_token, None)
            token = self.picture_tokens[address]
            self.pictures.move_to_end(token)
        return "http://127.0.0.1:%d/image/%s" % (port, token)

    def _picture_data(self, token):
        with self.picture_lock:
            if token in self.picture_cache:
                self.picture_cache.move_to_end(token)
                return self.picture_cache[token]
            address, site = self.pictures[token]
        with self._open(Request(address, headers=self._headers(site)), timeout=self.timeout) as response:
            data = response.read(4 * 1024 * 1024 + 1)
        if len(data) > 4 * 1024 * 1024:
            raise ValueError("封面过大")
        mime = _media_type(data)
        if not mime:
            data = _decrypt(data, MEDIA_KEY, MEDIA_IV)
            mime = _media_type(data)
        if not mime:
            raise ValueError("不是有效封面")
        with self.picture_lock:
            self.picture_cache[token] = (mime, data)
            while sum(len(value[1]) for value in self.picture_cache.values()) > 8 * 1024 * 1024:
                self.picture_cache.popitem(last=False)
        return mime, data


    def destroy(self):
        with self.picture_lock:
            server = self.picture_server
            self.picture_server = None
            self.pictures.clear()
            self.picture_tokens.clear()
            self.picture_cache.clear()
        if server is not None:
            server.shutdown()
            server.server_close()

