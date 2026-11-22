import base64
import json
import re
import threading
import time
import secrets
from collections import OrderedDict
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from urllib.parse import urlsplit, urljoin, unquote
from urllib.request import Request, urlopen
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


SITES = ("https://ygdj1.com", "https://www.yeguodj.com", "https://yeguodj.com")
UA = "Mozilla/5.0 (iPhone; CPU iPhone OS 17_0 like Mac OS X) AppleWebKit/605.1.15 (KHTML, like Gecko) Version/17.0 Mobile/15E148 Safari/604.1"
API_KEY, API_IV = b"2acf7e91e9864673", b"1c29882d3ddfcfd6"
MEDIA_KEY, MEDIA_IV = b"f5d965df75336270", b"97b60394abc2fbe1"
CATEGORIES = [("explore", "发现"), ("rank", "排行榜"), ("dushi", "都市"),
              ("xiandai", "现代"), ("xiaoyuan", "校园"), ("gudai", "古代"),
              ("xiangcun", "乡村"), ("zhichang", "职场"), ("chongsheng", "重生"),
              ("chuanyue", "穿越"), ("xitong", "系统"), ("nixi", "逆袭"), ("mogai", "魔改")]
BACKGROUNDS = {"dushi": 40, "xiandai": 39, "xiaoyuan": 47, "gudai": 41, "xiangcun": 42, "zhichang": 44}
SETTINGS = {"chongsheng": 26, "chuanyue": 27, "xitong": 28, "nixi": 53, "mogai": 56}


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


def _decode_response(body):
    result = json.loads(body.decode("utf-8-sig"))
    for _ in range(3):
        if not isinstance(result, dict):
            break
        value = result.get("data")
        if not isinstance(value, str) or len(value) <= 20:
            break
        encrypted = base64.b64decode("".join(value.split()), validate=True)
        plain = _decrypt(encrypted, API_KEY, API_IV).rstrip(b"\0").strip()
        result = json.loads(plain.decode("utf-8"))
    return result


def _unwrap(value):
    for _ in range(4):
        if isinstance(value, dict) and isinstance(value.get("data"), (dict, list)):
            value = value["data"]
        else:
            break
    return value


def _number(value, default=1):
    try:
        return max(1, int(value))
    except (TypeError, ValueError):
        return default


def _first(item, *keys, default=""):
    return next((item[key] for key in keys if item.get(key) is not None and item[key] != ""), default)


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


class Spider(BaseSpider):
    def __init__(self):
        self.sites = list(SITES)
        self.site = self.sites[0]
        self.timeout = 20
        self.picture_server = None
        self.picture_thread = None
        self.picture_lock = threading.RLock()
        self.pictures = OrderedDict()
        self.picture_tokens = {}
        self.picture_cache = OrderedDict()

    def getName(self):
        return "野果短剧·设备版"

    def init(self, extend=""):
        if isinstance(extend, str) and extend.strip():
            extend = json.loads(extend) if extend.strip().startswith("{") else {"site": extend}
        if isinstance(extend, dict):
            self.timeout = max(3, min(30, int(extend.get("timeout", 20))))
            if extend.get("site"):
                site = str(extend["site"]).rstrip("/")
                parsed = urlsplit(site)
                if parsed.scheme not in ("http", "https") or not parsed.hostname or parsed.query or parsed.fragment:
                    raise ValueError("无效的野果站点地址")
                self.sites = [site] + [address for address in SITES if address != site]
                self.site = site

    def _headers(self, site=None):
        site = site or self.site
        return {"User-Agent": UA, "Referer": site + "/", "Origin": site,
                "Accept": "*/*", "Accept-Language": "zh-CN,zh;q=0.9"}

    def _api(self, path, params):
        errors = []
        for site in [self.site] + [address for address in self.sites if address != self.site]:
            try:
                headers = self._headers(site)
                headers["Content-Type"] = "application/json;charset=UTF-8"
                request = Request(site + "/api.php" + path, data=json.dumps(params, separators=(",", ":")).encode(), headers=headers)
                for attempt in range(2):
                    try:
                        with urlopen(request, timeout=self.timeout) as response:
                            body = response.read(4 * 1024 * 1024 + 1)
                        break
                    except (URLError, TimeoutError, ConnectionError):
                        if attempt:
                            raise
                if len(body) > 4 * 1024 * 1024:
                    raise ValueError("接口响应过大")
                result = _decode_response(body)
                payload = _unwrap(result)
                if not isinstance(payload, (dict, list)):
                    raise ValueError("接口未返回有效数据")
                if isinstance(result, dict) and result.get("errcode") not in (None, 0, "0"):
                    raise ValueError(str(result.get("msg") or "上游返回错误"))
                self.site = site
                return payload
            except Exception as error:
                errors.append(urlsplit(site).hostname + ": " + str(error)[:120])
        raise RuntimeError("野果接口请求失败：" + "; ".join(errors))

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
        with urlopen(Request(address, headers=self._headers(site)), timeout=self.timeout) as response:
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

    def _item(self, item):
        if not isinstance(item, dict):
            return None
        video_id = str(_first(item, "video_id", "id")).strip()
        if not video_id:
            return None
        return {"vod_id": video_id, "vod_name": str(_first(item, "title", "video_title", "name", default=video_id)),
                "vod_pic": self._picture(_first(item, "cover", "cover_img", "pic")),
                "vod_remarks": str(_first(item, "update_status", "serialize_status_text", default=""))}

    def _items(self, payload):
        if isinstance(payload, list):
            rows = payload
        elif isinstance(payload, dict):
            rows = payload.get("list") or payload.get("top_list") or []
            if not rows:
                modules = payload.get("modules", [])
                modules = modules.get("list", []) if isinstance(modules, dict) else modules
                for module in modules:
                    if isinstance(module, dict):
                        rows.extend(module.get("list", []) if isinstance(module.get("list"), list) else [module])
        else:
            rows = []
        result, seen = [], set()
        for row in rows:
            item = self._item(row)
            if item and item["vod_id"] not in seen:
                seen.add(item["vod_id"])
                result.append(item)
        return result

    def homeContent(self, filter):
        return {"class": [{"type_id": key, "type_name": name} for key, name in CATEGORIES],
                "list": self.homeVideoContent()["list"]}

    def homeVideoContent(self):
        payload = self._api("/api/home/homePage", {})
        if isinstance(payload, dict):
            combined = list(payload.get("top_list") or [])
            modules = payload.get("modules") or {}
            modules = modules.get("list", []) if isinstance(modules, dict) else modules
            for module in modules:
                if isinstance(module, dict):
                    combined.extend(module.get("list", []) if isinstance(module.get("list"), list) else [module])
            combined.extend(payload.get("list") or [])
            items = self._items(combined)
        else:
            items = self._items(payload)
        if not items:
            items = self._items(self._api("/api/theater/exploreList", {"page": 1, "limit": 24}))
        return {"list": items[:48]}

    def categoryContent(self, tid, pg, filter, extend):
        page = _number(pg)
        params = {"page": page, "limit": 24}
        if tid in BACKGROUNDS:
            params["background"] = BACKGROUNDS[tid]
        if tid in SETTINGS:
            params["setting"] = SETTINGS[tid]
        path = "/api/theater/videoRank" if tid == "rank" else "/api/theater/exploreList"
        items = self._items(self._api(path, params))
        return {"list": items, "page": page, "pagecount": page + (1 if len(items) >= 24 else 0), "limit": 24, "total": 9999}

    def searchContent(self, key, quick=False, pg="1"):
        page = _number(pg)
        if not str(key).strip():
            return {"list": [], "page": page, "pagecount": page, "limit": 0, "total": 0}
        items = self._items(self._api("/api/search/result", {"keyword": key, "page": page}))
        return {"list": items, "page": page, "pagecount": page + (1 if len(items) >= 20 else 0), "limit": 20, "total": 9999}

    def detailContent(self, ids):
        video_id = (ids[0] if ids else "") if isinstance(ids, (list, tuple)) else ids
        if not video_id:
            return {"list": []}
        payload = self._api("/api/playlet/detail", {"video_id": int(video_id) if str(video_id).isdigit() else video_id})
        if not isinstance(payload, dict):
            raise ValueError("剧集详情无效")
        episodes = payload.get("episodes") or []
        links = []
        if not episodes:
            episodes = [{"sort": number} for number in range(1, min(1000, _number(_first(payload, "episode_count", "total_serial", default=1))) + 1)]
        for index, episode in enumerate(episodes, 1):
            number = _first(episode, "sort", "episode", "index", default=index)
            token = {"video": str(video_id), "episode": str(number),
                     "real_id": str(_first(episode, "id", "episode_id", "video_episode_id", "nid")),
                     "url": str(_first(episode, "video_url", "url", "play_url"))}
            encoded = base64.urlsafe_b64encode(json.dumps(token, separators=(",", ":")).encode()).decode().rstrip("=")
            title = re.sub(r"[$#\r\n]", "", str(episode.get("title") or "第%s集" % number))
            links.append(title + "$yg2:" + encoded)
        item = {"vod_id": str(video_id), "vod_name": str(payload.get("title") or video_id),
                "vod_pic": self._picture(_first(payload, "cover", "cover_img")),
                "vod_content": str(_first(payload, "description", "intro")),
                "vod_remarks": "全%d集" % len(links), "vod_play_from": "野果设备直连", "vod_play_url": "#".join(links)}
        return {"list": [item]}

    def playerContent(self, flag, id, vipFlags=None):
        if not str(id).startswith("yg2:"):
            raise ValueError("无效的野果剧集标记，请重新进入详情")
        encoded = id[4:]
        episode = json.loads(base64.urlsafe_b64decode(encoded + "=" * (-len(encoded) % 4)))
        video_id, number, real_id = episode["video"], episode["episode"], episode.get("real_id", "")
        address = episode.get("url", "")
        if not address:
            numeric_video = int(video_id) if video_id.isdigit() else video_id
            numeric_episode = int(number) if number.isdigit() else number
            params = dict.fromkeys(("ep", "sort", "episode", "index", "page"), numeric_episode)
            params.update(video_id=numeric_video, vid=numeric_video)
            if real_id:
                value = int(real_id) if real_id.isdigit() else real_id
                params.update(dict.fromkeys(("episode_id", "epid", "eid", "nid", "id", "video_episode_id"), value))
            payload = self._api("/api/playlet/play", params)
            if not isinstance(payload, dict):
                raise ValueError("播放接口未返回对象")
            choices = payload.get("episodeAll") or []
            selected = next((item for item in choices if str(_first(item, "sort", "index", "episode")) == number), None)
            if selected is None and real_id:
                selected = next((item for item in choices if str(_first(item, "id", "episode_id", "nid")) == real_id), None)
            if selected is None and number.isdigit() and 0 <= int(number) - 1 < len(choices):
                selected = choices[int(number) - 1]
            address = str(_first(selected or {}, "video_url", "url", "play_url") or _first(payload, "video_url", "url", "play_url"))
        address = urljoin(self.site + "/", address) if address else ""
        if urlsplit(address).scheme not in ("http", "https"):
            raise ValueError("未取得当前集的播放地址")
        return {"parse": 0, "jx": 0, "playUrl": "", "url": address, "header": self._headers()}

    def isVideoFormat(self, url):
        return False

    def manualVideoCheck(self):
        return False

    def localProxy(self, param):
        return [404, "text/plain", b"Video plays directly from CDN"]

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

