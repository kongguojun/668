
import base64
import binascii
import gzip
import hashlib
import hmac
import json
import os
import random
import re
import struct
import threading
import time
import uuid
import urllib.error
import urllib.parse
import urllib.request

try:
    from base.spider import Spider as BaseSpider
except Exception:
    class BaseSpider(object):
        pass

__version__ = "1.0.0"

PC_UA = ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
         "(KHTML, like Gecko) Chrome/131.0.0.0 Safari/537.36")
MOB_UA = ("Mozilla/5.0 (Linux; Android 13; Pixel 7) AppleWebKit/537.36 "
          "(KHTML, like Gecko) Chrome/120.0 Mobile Safari/537.36")
IPHONE_UA = ("Mozilla/5.0 (iPhone; CPU iPhone OS 18_7 like Mac OS X) "
             "AppleWebKit/605.1.15 (KHTML, like Gecko) Version/18.7 "
             "Mobile/15E148 Safari/604.1")


# ---------------- 基础小工具 ----------------

def _s(v):
    if v is None:
        return ""
    if isinstance(v, bool):
        return "true" if v else ""
    return str(v).strip()


def _pick(d, *keys):
    if not isinstance(d, dict):
        return ""
    for k in keys:
        v = d.get(k)
        if v is None or v is False:
            continue
        s = str(v).strip()
        if s:
            return s
    return ""


def _pick_int(d, *keys):
    if not isinstance(d, dict):
        return 0
    for k in keys:
        v = d.get(k)
        try:
            n = int(float(str(v).strip()))
            if n:
                return n
        except Exception:
            continue
    return 0


def _abs(base, href):
    try:
        return urllib.parse.urljoin(base, _s(href))
    except Exception:
        return _s(href)


def _strip_tags(s):
    s = _s(s)
    s = re.sub(r"(?is)<script.*?</script>", " ", s)
    s = re.sub(r"(?is)<style.*?</style>", " ", s)
    s = re.sub(r"(?s)<[^>]+>", " ", s)
    s = re.sub(r"\s+", " ", s)
    return s.strip()


_EP_PATTERNS = [
    re.compile(r"第\s*0*(\d+)\s*[集话期]"),
    re.compile(r"(?:更新至|共|全)\s*0*(\d+)\s*[集话期]"),
    re.compile(r"(?i)(?:episode|ep)\s*#?\s*0*(\d+)"),
]


def _ep_no(title, default=0):
    t = _s(title)
    for p in _EP_PATTERNS:
        m = p.search(t)
        if m:
            try:
                return int(m.group(1))
            except Exception:
                pass
    return default


def _q(s):
    return urllib.parse.quote(_s(s), safe="")


def _uq(s):
    return urllib.parse.unquote(_s(s))


def _md5(s):
    if isinstance(s, str):
        s = s.encode("utf-8")
    return hashlib.md5(s).hexdigest()


def _sha256(s):
    if isinstance(s, str):
        s = s.encode("utf-8")
    return hashlib.sha256(s).digest()


# ---------------- AES（纯 Python，支持 128/192/256，CBC/ECB，加解密） ----------------
# 小 JSON 解密走纯 Python 足够快；pycryptodome / javax.crypto 存在时自动用快的。

def _aes_build_sbox():
    sbox = [0] * 256
    isbox = [0] * 256
    # GF(2^8) 求逆
    def _xt(a):
        return ((a << 1) ^ 0x1B) & 0xFF if (a & 0x80) else (a << 1) & 0xFF
    inv = [0] * 256
    a = 1
    for _ in range(255):
        inv[a] = 1
        a = _xt(a)
    # 构造 exp/log 求完整逆元
    exp = [0] * 512
    log = [0] * 256
    x = 1
    for i in range(255):
        exp[i] = x
        log[x] = i
        x = _xt(x) ^ x
    for i in range(255, 512):
        exp[i] = exp[i - 255]
    full_inv = [0] * 256
    for i in range(1, 256):
        full_inv[i] = exp[255 - log[i]]
    for i in range(256):
        v = full_inv[i]
        s = v
        for r in (1, 2, 3, 4):
            s ^= ((v << r) | (v >> (8 - r))) & 0xFF
        s = (s ^ 0x63) & 0xFF
        sbox[i] = s
        isbox[s] = i
    return sbox, isbox


_AES_SBOX, _AES_ISBOX = _aes_build_sbox()
_AES_RK = {}


def _aes_xtime(a):
    return ((a << 1) ^ 0x1B) & 0xFF if (a & 0x80) else (a << 1) & 0xFF


def _aes_gmul(a, b):
    p = 0
    while b:
        if b & 1:
            p ^= a
        a = _aes_xtime(a)
        b >>= 1
    return p & 0xFF


def _aes_expand_key(key):
    key = bytes(key)
    ck = _AES_RK.get(key)
    if ck:
        return ck
    nk = len(key) // 4
    nr = {4: 10, 6: 12, 8: 14}[nk]
    rcon = (0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40, 0x80, 0x1B, 0x36)
    w = [list(key[i:i + 4]) for i in range(0, len(key), 4)]
    for i in range(nk, 4 * (nr + 1)):
        t = w[i - 1][:]
        if i % nk == 0:
            t = t[1:] + t[:1]
            t = [_AES_SBOX[b] for b in t]
            t[0] ^= rcon[i // nk - 1]
        elif nk > 6 and i % nk == 4:
            t = [_AES_SBOX[b] for b in t]
        w.append([w[i - nk][j] ^ t[j] for j in range(4)])
    rk = [b for word in w for b in word]
    _AES_RK[key] = (rk, nr)
    return rk, nr


def _aes_add_rk(s, rk, off):
    return [s[i] ^ rk[off + i] for i in range(16)]


def _aes_shift_rows(s, inv=False):
    o = [0] * 16
    for r in range(4):
        for c in range(4):
            o[r + 4 * c] = s[r + 4 * ((c - r) % 4 if inv else (c + r) % 4)]
    return o


def _aes_mix_col(s, inv=False):
    o = [0] * 16
    for c in range(4):
        a0, a1, a2, a3 = s[4 * c], s[4 * c + 1], s[4 * c + 2], s[4 * c + 3]
        if inv:
            o[4 * c] = (_aes_gmul(a0, 14) ^ _aes_gmul(a1, 11) ^
                        _aes_gmul(a2, 13) ^ _aes_gmul(a3, 9))
            o[4 * c + 1] = (_aes_gmul(a0, 9) ^ _aes_gmul(a1, 14) ^
                            _aes_gmul(a2, 11) ^ _aes_gmul(a3, 13))
            o[4 * c + 2] = (_aes_gmul(a0, 13) ^ _aes_gmul(a1, 9) ^
                            _aes_gmul(a2, 14) ^ _aes_gmul(a3, 11))
            o[4 * c + 3] = (_aes_gmul(a0, 11) ^ _aes_gmul(a1, 13) ^
                            _aes_gmul(a2, 9) ^ _aes_gmul(a3, 14))
        else:
            o[4 * c] = (_aes_gmul(a0, 2) ^ _aes_gmul(a1, 3) ^ a2 ^ a3)
            o[4 * c + 1] = (a0 ^ _aes_gmul(a1, 2) ^ _aes_gmul(a2, 3) ^ a3)
            o[4 * c + 2] = (a0 ^ a1 ^ _aes_gmul(a2, 2) ^ _aes_gmul(a3, 3))
            o[4 * c + 3] = (_aes_gmul(a0, 3) ^ a1 ^ a2 ^ _aes_gmul(a3, 2))
    return o


def _aes_enc_block_py(blk, rk, nr):
    s = _aes_add_rk(list(blk), rk, 0)
    for rnd in range(1, nr):
        s = [_AES_SBOX[b] for b in s]
        s = _aes_shift_rows(s)
        s = _aes_mix_col(s)
        s = _aes_add_rk(s, rk, 16 * rnd)
    s = [_AES_SBOX[b] for b in s]
    s = _aes_shift_rows(s)
    s = _aes_add_rk(s, rk, 16 * nr)
    return bytes(s)


def _aes_dec_block_py(blk, rk, nr):
    s = _aes_add_rk(list(blk), rk, 16 * nr)
    for rnd in range(nr - 1, 0, -1):
        s = _aes_shift_rows(s, inv=True)
        s = [_AES_ISBOX[b] for b in s]
        s = _aes_add_rk(s, rk, 16 * rnd)
        s = _aes_mix_col(s, inv=True)
    s = _aes_shift_rows(s, inv=True)
    s = [_AES_ISBOX[b] for b in s]
    s = _aes_add_rk(s, rk, 0)
    return bytes(s)


def _pkcs7_pad(data):
    n = 16 - (len(data) % 16)
    return bytes(data) + bytes([n] * n)


def _pkcs7_unpad(data):
    data = bytes(data)
    if not data or len(data) % 16:
        raise ValueError("bad pkcs7 length")
    n = data[-1]
    if n < 1 or n > 16 or data[-n:] != bytes([n] * n):
        raise ValueError("bad pkcs7 padding")
    return data[:-n]


def _aes_crypt_fast(data, key, iv, encrypt, mode_cbc):
    """pycryptodome 优先，其次 javax.crypto（真机），最后纯 Python。"""
    data, key = bytes(data), bytes(key)
    try:
        from Crypto.Cipher import AES
        if mode_cbc:
            c = AES.new(key, AES.MODE_CBC, bytes(iv))
        else:
            c = AES.new(key, AES.MODE_ECB)
        return c.encrypt(data) if encrypt else c.decrypt(data)
    except Exception:
        pass
    try:
        from java import jclass
        Cipher = jclass("javax.crypto.Cipher")
        SecretKeySpec = jclass("javax.crypto.spec.SecretKeySpec")
        IvParameterSpec = jclass("javax.crypto.spec.IvParameterSpec")
        trans = "AES/%s/NoPadding" % ("CBC" if mode_cbc else "ECB")
        c = Cipher.getInstance(trans)
        ks = SecretKeySpec(key, "AES")
        if mode_cbc:
            c.init(1 if encrypt else 2, ks, IvParameterSpec(bytes(iv)))
        else:
            c.init(1 if encrypt else 2, ks)
        return bytes(c.doFinal(data))
    except Exception:
        pass
    rk, nr = _aes_expand_key(key)
    enc = _aes_enc_block_py if encrypt else _aes_dec_block_py
    out = bytearray()
    prev = bytes(iv) if (mode_cbc and not encrypt) else None
    prev_enc = bytes(iv) if (mode_cbc and encrypt) else None
    for off in range(0, len(data), 16):
        blk = data[off:off + 16]
        if mode_cbc and encrypt:
            blk = bytes(blk[i] ^ prev_enc[i] for i in range(16))
            e = enc(blk, rk, nr)
            out.extend(e)
            prev_enc = e
        elif mode_cbc:
            d = enc(blk, rk, nr)
            out.extend(bytes(d[i] ^ prev[i] for i in range(16)))
            prev = blk
        else:
            out.extend(enc(blk, rk, nr))
    return bytes(out)


def _aes_cbc_encrypt(data, key, iv):
    return _aes_crypt_fast(_pkcs7_pad(data), key, iv, True, True)


def _aes_cbc_decrypt(data, key, iv):
    return _pkcs7_unpad(_aes_crypt_fast(data, key, iv, False, True))


def _aes_ecb_decrypt(data, key):
    return _pkcs7_unpad(_aes_crypt_fast(data, key, b"\x00" * 16, False, False))


def _aes_cbc_decrypt_nopad(data, key, iv):
    return _aes_crypt_fast(data, key, iv, False, True)


# ---------------- HTTP 层 ----------------
# urllib 主用；Python 栈被目标按 TLS 指纹丢弃时，回落 App 自带 OkHttp（真机）。

_JAVA_CLIENT = [None]


def _java_client():
    if _JAVA_CLIENT[0] is not None:
        return _JAVA_CLIENT[0] or None
    try:
        from java import jclass
        Builder = jclass("okhttp3.OkHttpClient$Builder")
        TimeUnit = jclass("java.util.concurrent.TimeUnit")
        b = Builder()
        b.followRedirects(True)
        b.followSslRedirects(True)
        b.connectTimeout(12, TimeUnit.SECONDS)
        b.readTimeout(30, TimeUnit.SECONDS)
        b.writeTimeout(12, TimeUnit.SECONDS)
        _JAVA_CLIENT[0] = b.build()
    except Exception:
        _JAVA_CLIENT[0] = False
    return _JAVA_CLIENT[0] or None


def _java_fetch(url, headers=None, data=None):
    """返回 (status, headers_dict, body)；失败返回 None。"""
    client = _java_client()
    if client is None:
        return None
    try:
        from java import jclass
        ReqBuilder = jclass("okhttp3.Request$Builder")
        rb = ReqBuilder()
        rb.url(str(url))
        ctype = "application/x-www-form-urlencoded"
        for k, v in (headers or {}).items():
            lk = str(k).lower()
            if lk == "content-type":
                ctype = str(v)
                continue
            if lk in ("content-length", "host", "cookie"):
                continue
            try:
                rb.header(str(k), str(v))
            except Exception:
                pass
        if data is not None:
            MediaType = jclass("okhttp3.MediaType")
            RequestBody = jclass("okhttp3.RequestBody")
            rb.post(RequestBody.create(MediaType.parse(ctype), bytes(data)))
        resp = client.newCall(rb.build()).execute()
        code = 0
        try:
            code = int(resp.code())
        except Exception:
            pass
        h = {}
        try:
            mm = resp.headers().toMultimap()
            for e in mm.entrySet():
                vals = []
                try:
                    for v in e.getValue():
                        vals.append(str(v))
                except Exception:
                    pass
                h[str(e.getKey()).lower()] = vals
        except Exception:
            pass
        out = b""
        try:
            bd = resp.body()
            if bd is not None:
                out = bytes(bd.bytes())
        except Exception:
            pass
        try:
            resp.close()
        except Exception:
            pass
        return code, h, out
    except Exception:
        return None


class _Resp(object):
    def __init__(self):
        self.status = 0
        self.headers = {}
        self.body = b""
        self.url = ""

    def text(self, encoding="utf-8"):
        return self.body.decode(encoding, "ignore")


def _parse_set_cookies(header_vals, jar):
    for hv in header_vals or []:
        part = _s(hv).split(";", 1)[0]
        if "=" in part:
            k, v = part.split("=", 1)
            k = k.strip()
            if k:
                jar[k] = v.strip()


class _Session(object):
    """带 Cookie 罐的会话；fetch 返回 _Resp。"""

    def __init__(self):
        self.cookies = {}
        self._lock = threading.Lock()

    def _cookie_header(self):
        with self._lock:
            items = ["%s=%s" % (k, v) for k, v in self.cookies.items()]
        return "; ".join(items)

    def fetch(self, url, method="GET", headers=None, data=None,
              timeout=12, max_body=8 << 20):
        headers = dict(headers or {})
        ck = self._cookie_header()
        if ck and "cookie" not in {k.lower(): 1 for k in headers}:
            headers["Cookie"] = ck
        if "user-agent" not in {k.lower(): 1 for k in headers}:
            headers["User-Agent"] = PC_UA
        resp = _Resp()
        resp.url = url
        # 1) urllib
        try:
            req = urllib.request.Request(url, data=data, headers=headers,
                                         method=method.upper())
            with urllib.request.urlopen(req, timeout=timeout) as r:
                resp.status = r.status
                raw_h = {}
                try:
                    for k, v in r.headers.items():
                        raw_h.setdefault(k.lower(), []).append(v)
                except Exception:
                    pass
                resp.headers = raw_h
                body = r.read(max_body + 1)
                if len(body) > max_body:
                    raise ValueError("body too large")
                resp.body = body
                try:
                    resp.url = r.geturl()
                except Exception:
                    pass
        except Exception:
            # 2) 真机 OkHttp 回退
            jr = _java_fetch(url, headers=headers, data=data)
            if not jr:
                raise
            resp.status, resp.headers, resp.body = jr
            if len(resp.body) > max_body:
                raise ValueError("body too large")
        _parse_set_cookies(resp.headers.get("set-cookie"), self.cookies)
        # 部分站点不看 Accept-Encoding 直接发 gzip/deflate，中央解压
        try:
            enc = [_s(x).lower() for x in resp.headers.get(
                "content-encoding", [])]
            if resp.body[:2] == b"\x1f\x8b" or any(
                    "gzip" in x for x in enc):
                resp.body = gzip.decompress(bytes(resp.body))
            elif resp.body[:2] == b"\x78\x9c" or any(
                    "deflate" in x for x in enc):
                import zlib
                resp.body = zlib.decompress(bytes(resp.body))
        except Exception:
            pass
        return resp

    def get_text(self, url, headers=None, timeout=12):
        return self.fetch(url, headers=headers, timeout=timeout).text()

    def get_json(self, url, headers=None, timeout=12):
        return json.loads(self.fetch(url, headers=headers,
                                     timeout=timeout).text())

    def post_json(self, url, obj, headers=None, timeout=12):
        h = dict(headers or {})
        h["Content-Type"] = "application/json; charset=utf-8"
        data = json.dumps(obj, ensure_ascii=False).encode("utf-8")
        return json.loads(self.fetch(url, method="POST", headers=h, data=data,
                                     timeout=timeout).text())

    def post_form(self, url, fields, headers=None, timeout=12):
        h = dict(headers or {})
        h["Content-Type"] = "application/x-www-form-urlencoded"
        data = urllib.parse.urlencode(fields).encode("utf-8")
        return self.fetch(url, method="POST", headers=h, data=data,
                          timeout=timeout).text()


# ---------------- 站源框架 ----------------

class _SrcErr(Exception):
    """站源级可预期错误（接口变化/失效/加密等），Spider 会隔离。"""
    pass


def _tid(src, cat):
    return "%s::c::%s" % (src, _q(cat))


def _did(src, sid):
    return "%s::d::%s" % (src, _q(sid))


def _pid(src, sid, ep):
    return "%s::p::%s::%s" % (src, _q(sid), _q(ep))


def _split_tid(tid):
    head, _, cat = _s(tid).partition("::c::")
    return head, _uq(cat)


def _split_did(did):
    head, _, sid = _s(did).partition("::d::")
    return head, _uq(sid)


def _split_pid(pid):
    s = _s(pid)
    head, _, rest = s.partition("::p::")
    sid, _, ep = rest.partition("::")
    return head, _uq(sid), _uq(ep)


def _vod_item(src_id, sid, title, pic="", remark="", content=""):
    return {
        "vod_id": _did(src_id, sid),
        "vod_name": _s(title),
        "vod_pic": _s(pic),
        "vod_remarks": _s(remark),
        "vod_content": _s(content),
    }


def _vod_detail(src, sid, title, pic="", remark="", content="",
                year="", area="", actor="", chapters=()):
    """chapters: [(epkey, eptitle)]"""
    play_url = "#".join(
        "%s$%s" % (_s(t) or ("第%d集" % (i + 1)), _pid(src.id, sid, k))
        for i, (k, t) in enumerate(chapters))
    return {
        "vod_id": _did(src.id, sid),
        "vod_name": _s(title),
        "vod_pic": _s(pic),
        "vod_remarks": _s(remark),
        "vod_content": _s(content),
        "vod_year": _s(year),
        "vod_area": _s(area),
        "vod_actor": _s(actor),
        "vod_play_from": src.name,
        "vod_play_url": play_url,
    }


def _err_text(e):
    """把网络异常翻译成用户能看懂的一句话（用于列表/详情空时的说明）。"""
    try:
        if isinstance(e, urllib.error.HTTPError):
            code = int(getattr(e, "code", 0) or 0)
            if code in (401, 403, 412, 429):
                return "站点拒绝了本机网络访问（HTTP %d），换网络或稍后再试" % code
            return "站点返回 HTTP %d" % code
        if isinstance(e, urllib.error.URLError):
            return "网络连不上：%s" % (getattr(e, "reason", "") or "超时")
    except Exception:
        pass
    if isinstance(e, _SrcErr):
        return str(e)
    return "%s: %s" % (type(e).__name__, str(e)[:80])


class _Src(object):
    id = ""
    name = ""
    cats = [("", "推荐")]  # [(catid, catname)] 静态分类

    def __init__(self):
        self.sess = _Session()
        self.last_err = ""

    # -- 以下按需覆盖 --
    def home(self, pg):
        """返回 (items, has_more)。"""
        return self.cat("", pg)

    def cat(self, catid, pg):
        raise _SrcErr("本站源暂无目录")

    def detail(self, sid):
        raise _SrcErr("本站源暂无详情")

    def play(self, sid, ep):
        """返回 (media_url, headers_dict)。"""
        raise _SrcErr("本站源暂无播放")

    def search(self, key, pg):
        raise _SrcErr("本站源不支持搜索")


_SOURCES = []


def _register(cls):
    _SOURCES.append(cls())
    return cls


def _find_src(src_id):
    for s in _SOURCES:
        if s.id == src_id:
            return s
    return None


# ============================================================
# 红果（___3_shu0.py，hongguoduanju.com，base64 内嵌，无需外部文件）
# 本类做适配。排第一位。
# ============================================================
_hgmod = None
_HG_IMPORT_ERR = ""
try:
    import base64 as _b64m, types as _tmod
    _hg_raw = _b64m.b64decode(
        "IyAtKi0gY29kaW5nOiB1dGYtOCAtKi0KZnJvbSBfX2Z1dHVyZV9fIGltcG9ydCBhbm5vdGF0aW9ucwppbXBvcnQgYmFzZTY0CmltcG9ydCBiaW5hc2NpaQppbXBvcnQgYmlzZWN0CmltcG9ydCBoYXNobGliCmltcG9ydCBqc29uCmltcG9ydCBvcwppbXBvcnQgbHptYQppbXBvcnQgcmFuZG9tCmltcG9ydCByZQppbXBvcnQgc3RydWN0CmltcG9ydCB0ZW1wZmlsZQppbXBvcnQgY29uY3VycmVudC5mdXR1cmVzCmltcG9ydCB0aHJlYWRpbmcKaW1wb3J0IHRpbWUKZnJvbSBjb2xsZWN0aW9ucy5hYmMgaW1wb3J0IE1hcHBpbmcKZnJvbSBodHRwLnNlcnZlciBpbXBvcnQgQmFzZUhUVFBSZXF1ZXN0SGFuZGxlciwgVGhyZWFkaW5nSFRUUFNlcnZlcgpmcm9tIGh0bWwucGFyc2VyIGltcG9ydCBIVE1MUGFyc2VyCmZyb20gdHlwaW5nIGltcG9ydCBBbnkKZnJvbSB1cmxsaWIucGFyc2UgaW1wb3J0IHBhcnNlX3FzLCBxdW90ZSwgdXJsZW5jb2RlLCB1cmxwYXJzZQppbXBvcnQgcmVxdWVzdHMKdHJ5OgogICAgZnJvbSBjcnlwdG9ncmFwaHkuaGF6bWF0LnByaW1pdGl2ZXMgaW1wb3J0IGhhc2hlcwogICAgZnJvbSBjcnlwdG9ncmFwaHkuaGF6bWF0LnByaW1pdGl2ZXMuY2lwaGVycyBpbXBvcnQgQ2lwaGVyLCBhbGdvcml0aG1zLCBtb2RlcwpleGNlcHQgSW1wb3J0RXJyb3I6CiAgICBoYXNoZXMgPSBOb25lCiAgICBDaXBoZXIgPSBhbGdvcml0aG1zID0gbW9kZXMgPSBOb25lCnRyeToKICAgIGZyb20gQ3J5cHRvLkNpcGhlciBpbXBvcnQgQUVTIGFzIENyeXB0b0FFUwpleGNlcHQgSW1wb3J0RXJyb3I6CiAgICBDcnlwdG9BRVMgPSBOb25lCnRyeToKICAgIGZyb20gYmFzZS5zcGlkZXIgaW1wb3J0IFNwaWRlciBhcyBfQmFzZVNwaWRlcgpleGNlcHQgRXhjZXB0aW9uOgogICAgdHJ5OgogICAgICAgIGltcG9ydCBzeXMgYXMgX3N5cwogICAgICAgIF9zeXMucGF0aC5hcHBlbmQoIi4uIikKICAgICAgICBmcm9tIGJhc2Uuc3BpZGVyIGltcG9ydCBTcGlkZXIgYXMgX0Jhc2VTcGlkZXIKICAgIGV4Y2VwdCBFeGNlcHRpb246CiAgICAgICAgY2xhc3MgX0Jhc2VTcGlkZXI6CiAgICAgICAgICAgIHBhc3MKCiMgRm9uZ01pL1RWQm94IOeahCBDaGFxdW9weSDnjq/looPmnKrlv4XluKYgY3J5cHRvZ3JhcGh577yM5aSa5pWw5aOz5Y+q5bimIHB5Y3J5cHRvZG9tZeOAggojIOe7n+S4gOWFpeWPo++8jOmBv+WFjeiwg+eUqOeCueebtOaOpeS+nei1luafkOS4gOS4quW6k+OAggppZiBDaXBoZXIgaXMgbm90IE5vbmU6CiAgICBBRVNfQkFDS0VORCA9ICJjcnlwdG9ncmFwaHkiCmVsaWYgQ3J5cHRvQUVTIGlzIG5vdCBOb25lOgogICAgQUVTX0JBQ0tFTkQgPSAicHljcnlwdG9kb21lIgplbHNlOgogICAgQUVTX0JBQ0tFTkQgPSAibm9uZSIKCmNsYXNzIF9QdXJlQUVTMTI4OgogICAgIiIi57qvIFB5dGhvbiBBRVMtMTI477yM5L6b5pegIHB5Y3J5cHRvZG9tZS9jcnlwdG9ncmFwaHkg55qE5aOz5L2/55So44CCIiIiCgogICAgX1MgPSAoCiAgICAgICAgOTksMTI0LDExOSwxMjMsMjQyLDEwNywxMTEsMTk3LDQ4LDEsMTAzLDQzLDI1NCwyMTUsMTcxLDExOCwyMDIsMTMwLDIwMSwxMjUsMjUwLDg5LDcxLDI0MCwKICAgICAgICAxNzMsMjEyLDE2MiwxNzUsMTU2LDE2NCwxMTQsMTkyLDE4MywyNTMsMTQ3LDM4LDU0LDYzLDI0NywyMDQsNTIsMTY1LDIyOSwyNDEsMTEzLDIxNiw0OSwyMSwKICAgICAgICA0LDE5OSwzNSwxOTUsMjQsMTUwLDUsMTU0LDcsMTgsMTI4LDIyNiwyMzUsMzksMTc4LDExNyw5LDEzMSw0NCwyNiwyNywxMTAsOTAsMTYwLDgyLDU5LDIxNCwKICAgICAgICAxNzksNDEsMjI3LDQ3LDEzMiw4MywyMDksMCwyMzcsMzIsMjUyLDE3Nyw5MSwxMDYsMjAzLDE5MCw1Nyw3NCw3Niw4OCwyMDcsMjA4LDIzOSwxNzAsMjUxLDY3LAogICAgICAgIDc3LDUxLDEzMyw2OSwyNDksMiwxMjcsODAsNjAsMTU5LDE2OCw4MSwxNjMsNjQsMTQzLDE0NiwxNTcsNTYsMjQ1LDE4OCwxODIsMjE4LDMzLDE2LDI1NSwyNDMsCiAgICAgICAgMjEwLDIwNSwxMiwxOSwyMzYsOTUsMTUxLDY4LDIzLDE5NiwxNjcsMTI2LDYxLDEwMCw5MywyNSwxMTUsOTYsMTI5LDc5LDIyMCwzNCw0MiwxNDQsMTM2LDcwLAogICAgICAgIDIzOCwxODQsMjAsMjIyLDk0LDExLDIxOSwyMjQsNTAsNTgsMTAsNzMsNiwzNiw5MiwxOTQsMjExLDE3Miw5OCwxNDUsMTQ5LDIyOCwxMjEsMjMxLDIwMCw1NSwKICAgICAgICAxMDksMTQxLDIxMyw3OCwxNjksMTA4LDg2LDI0NCwyMzQsMTAxLDEyMiwxNzQsOCwxODYsMTIwLDM3LDQ2LDI4LDE2NiwxODAsMTk4LDIzMiwyMjEsMTE2LDMxLAogICAgICAgIDc1LDE4OSwxMzksMTM4LDExMiw2MiwxODEsMTAyLDcyLDMsMjQ2LDE0LDk3LDUzLDg3LDE4NSwxMzQsMTkzLDI5LDE1OCwyMjUsMjQ4LDE1MiwxNywxMDUsCiAgICAgICAgMjE3LDE0MiwxNDgsMTU1LDMwLDEzNSwyMzMsMjA2LDg1LDQwLDIyMywxNDAsMTYxLDEzNywxMywxOTEsMjMwLDY2LDEwNCw2NSwxNTMsNDUsMTUsMTc2LDg0LAogICAgICAgIDE4NywyMgogICAgKQogICAgX1JDT04gPSAoMHgwMCwweDAxLDB4MDIsMHgwNCwweDA4LDB4MTAsMHgyMCwweDQwLDB4ODAsMHgxQiwweDM2KQoKICAgIGRlZiBfX2luaXRfXyhzZWxmLCBrZXk6IGJ5dGVzKToKICAgICAgICBpZiBsZW4oa2V5KSAhPSAxNjoKICAgICAgICAgICAgcmFpc2UgVmFsdWVFcnJvcigiQUVTLTEyOCBvbmx5IikKICAgICAgICBzZWxmLl9yayA9IHNlbGYuX2V4cGFuZChrZXkpCgogICAgZGVmIF9leHBhbmQoc2VsZiwga2V5OiBieXRlcyk6CiAgICAgICAgcyA9IHNlbGYuX1MKICAgICAgICB3ID0gbGlzdChrZXkpCiAgICAgICAgZm9yIGkgaW4gcmFuZ2UoNCwgNDQpOgogICAgICAgICAgICB0MCwgdDEsIHQyLCB0MyA9IHdbLTRdLCB3Wy0zXSwgd1stMl0sIHdbLTFdCiAgICAgICAgICAgIGlmIGkgJSA0ID09IDA6CiAgICAgICAgICAgICAgICB0MCwgdDEsIHQyLCB0MyA9IHNbdDFdLCBzW3QyXSwgc1t0M10sIHNbdDBdCiAgICAgICAgICAgICAgICB0MCBePSBzZWxmLl9SQ09OW2kgLy8gNF0KICAgICAgICAgICAgYmFzZSA9IChpIC0gNCkgKiA0CiAgICAgICAgICAgIHcuZXh0ZW5kKCh3W2Jhc2VdIF4gdDAsIHdbYmFzZSArIDFdIF4gdDEsIHdbYmFzZSArIDJdIF4gdDIsIHdbYmFzZSArIDNdIF4gdDMpKQogICAgICAgIHJldHVybiB3CgogICAgQHN0YXRpY21ldGhvZAogICAgZGVmIF94dGltZShhOiBpbnQpIC0+IGludDoKICAgICAgICByZXR1cm4gKChhIDw8IDEpIF4gMHgxQikgJiAweEZGIGlmIChhICYgMHg4MCkgZWxzZSAoKGEgPDwgMSkgJiAweEZGKQoKICAgIGRlZiBlbmNyeXB0X2Jsb2NrKHNlbGYsIGJsb2NrOiBieXRlcykgLT4gYnl0ZXM6CiAgICAgICAgcyA9IGxpc3QoYmxvY2spCiAgICAgICAgcmsgPSBzZWxmLl9yawogICAgICAgIGZvciBpIGluIHJhbmdlKDE2KToKICAgICAgICAgICAgc1tpXSBePSBya1tpXQogICAgICAgIGZvciBybmQgaW4gcmFuZ2UoMSwgMTApOgogICAgICAgICAgICBzID0gW3NlbGYuX1NbYl0gZm9yIGIgaW4gc10KICAgICAgICAgICAgcyA9IFtzWzBdLCBzWzVdLCBzWzEwXSwgc1sxNV0sIHNbNF0sIHNbOV0sIHNbMTRdLCBzWzNdLAogICAgICAgICAgICAgICAgIHNbOF0sIHNbMTNdLCBzWzJdLCBzWzddLCBzWzEyXSwgc1sxXSwgc1s2XSwgc1sxMV1dCiAgICAgICAgICAgIGZvciBjIGluIHJhbmdlKDQpOgogICAgICAgICAgICAgICAgaSA9IGMgKiA0CiAgICAgICAgICAgICAgICBhLCBiLCBjMCwgZCA9IHNbaV0sIHNbaSArIDFdLCBzW2kgKyAyXSwgc1tpICsgM10KICAgICAgICAgICAgICAgIHQgPSBhIF4gYiBeIGMwIF4gZAogICAgICAgICAgICAgICAgdSA9IGEKICAgICAgICAgICAgICAgIGEgXj0gdCBeIHNlbGYuX3h0aW1lKGEgXiBiKQogICAgICAgICAgICAgICAgYiBePSB0IF4gc2VsZi5feHRpbWUoYiBeIGMwKQogICAgICAgICAgICAgICAgYzAgXj0gdCBeIHNlbGYuX3h0aW1lKGMwIF4gZCkKICAgICAgICAgICAgICAgIGQgXj0gdCBeIHNlbGYuX3h0aW1lKGQgXiB1KQogICAgICAgICAgICAgICAgc1tpXSwgc1tpICsgMV0sIHNbaSArIDJdLCBzW2kgKyAzXSA9IGEsIGIsIGMwLCBkCiAgICAgICAgICAgIG9mZiA9IHJuZCAqIDE2CiAgICAgICAgICAgIGZvciBpIGluIHJhbmdlKDE2KToKICAgICAgICAgICAgICAgIHNbaV0gXj0gcmtbb2ZmICsgaV0KICAgICAgICBzID0gW3NlbGYuX1NbYl0gZm9yIGIgaW4gc10KICAgICAgICBzID0gW3NbMF0sIHNbNV0sIHNbMTBdLCBzWzE1XSwgc1s0XSwgc1s5XSwgc1sxNF0sIHNbM10sCiAgICAgICAgICAgICBzWzhdLCBzWzEzXSwgc1syXSwgc1s3XSwgc1sxMl0sIHNbMV0sIHNbNl0sIHNbMTFdXQogICAgICAgIGZvciBpIGluIHJhbmdlKDE2KToKICAgICAgICAgICAgc1tpXSBePSBya1sxNjAgKyBpXQogICAgICAgIHJldHVybiBieXRlcyhzKQoKICAgIGRlZiBkZWNyeXB0X2Jsb2NrKHNlbGYsIGJsb2NrOiBieXRlcykgLT4gYnl0ZXM6CiAgICAgICAgZGVmIG11bChhLCBiKToKICAgICAgICAgICAgcCA9IDAKICAgICAgICAgICAgZm9yIF8gaW4gcmFuZ2UoOCk6CiAgICAgICAgICAgICAgICBpZiBiICYgMToKICAgICAgICAgICAgICAgICAgICBwIF49IGEKICAgICAgICAgICAgICAgIGhpID0gYSAmIDB4ODAKICAgICAgICAgICAgICAgIGEgPSAoYSA8PCAxKSAmIDB4RkYKICAgICAgICAgICAgICAgIGlmIGhpOgogICAgICAgICAgICAgICAgICAgIGEgXj0gMHgxQgogICAgICAgICAgICAgICAgYiA+Pj0gMQogICAgICAgICAgICByZXR1cm4gcAoKICAgICAgICBzID0gbGlzdChibG9jaykKICAgICAgICByayA9IHNlbGYuX3JrCiAgICAgICAgZm9yIGkgaW4gcmFuZ2UoMTYpOgogICAgICAgICAgICBzW2ldIF49IHJrWzE2MCArIGldCiAgICAgICAgZm9yIHJuZCBpbiByYW5nZSg5LCAwLCAtMSk6CiAgICAgICAgICAgIHMgPSBbc1swXSwgc1sxM10sIHNbMTBdLCBzWzddLCBzWzRdLCBzWzFdLCBzWzE0XSwgc1sxMV0sCiAgICAgICAgICAgICAgICAgc1s4XSwgc1s1XSwgc1syXSwgc1sxNV0sIHNbMTJdLCBzWzldLCBzWzZdLCBzWzNdXQogICAgICAgICAgICBzID0gW3NlbGYuX1NJW2JdIGZvciBiIGluIHNdCiAgICAgICAgICAgIG9mZiA9IHJuZCAqIDE2CiAgICAgICAgICAgIGZvciBpIGluIHJhbmdlKDE2KToKICAgICAgICAgICAgICAgIHNbaV0gXj0gcmtbb2ZmICsgaV0KICAgICAgICAgICAgZm9yIGMgaW4gcmFuZ2UoNCk6CiAgICAgICAgICAgICAgICBpID0gYyAqIDQKICAgICAgICAgICAgICAgIGEsIGIsIGMwLCBkID0gc1tpXSwgc1tpICsgMV0sIHNbaSArIDJdLCBzW2kgKyAzXQogICAgICAgICAgICAgICAgc1tpXSA9IG11bChhLCAweDBFKSBeIG11bChiLCAweDBCKSBeIG11bChjMCwgMHgwRCkgXiBtdWwoZCwgMHgwOSkKICAgICAgICAgICAgICAgIHNbaSArIDFdID0gbXVsKGEsIDB4MDkpIF4gbXVsKGIsIDB4MEUpIF4gbXVsKGMwLCAweDBCKSBeIG11bChkLCAweDBEKQogICAgICAgICAgICAgICAgc1tpICsgMl0gPSBtdWwoYSwgMHgwRCkgXiBtdWwoYiwgMHgwOSkgXiBtdWwoYzAsIDB4MEUpIF4gbXVsKGQsIDB4MEIpCiAgICAgICAgICAgICAgICBzW2kgKyAzXSA9IG11bChhLCAweDBCKSBeIG11bChiLCAweDBEKSBeIG11bChjMCwgMHgwOSkgXiBtdWwoZCwgMHgwRSkKICAgICAgICBzID0gW3NbMF0sIHNbMTNdLCBzWzEwXSwgc1s3XSwgc1s0XSwgc1sxXSwgc1sxNF0sIHNbMTFdLAogICAgICAgICAgICAgc1s4XSwgc1s1XSwgc1syXSwgc1sxNV0sIHNbMTJdLCBzWzldLCBzWzZdLCBzWzNdXQogICAgICAgIHMgPSBbc2VsZi5fU0lbYl0gZm9yIGIgaW4gc10KICAgICAgICBmb3IgaSBpbiByYW5nZSgxNik6CiAgICAgICAgICAgIHNbaV0gXj0gcmtbaV0KICAgICAgICByZXR1cm4gYnl0ZXMocykKCgoKX1B1cmVBRVMxMjguX1NJID0gdHVwbGUoe3Y6IGkgZm9yIGksIHYgaW4gZW51bWVyYXRlKF9QdXJlQUVTMTI4Ll9TKX1baV0gZm9yIGkgaW4gcmFuZ2UoMjU2KSkKCgpkZWYgX3B1cmVfY3RyX2RlY3J5cHQoa2V5OiBieXRlcywgY291bnRlcjogYnl0ZXMsIGRhdGE6IGJ5dGVzKSAtPiBieXRlczoKICAgIGlmIG5vdCBkYXRhOgogICAgICAgIHJldHVybiBiIiIKICAgIGlmIGxlbihjb3VudGVyKSA8IDE2OgogICAgICAgIGNvdW50ZXIgPSBjb3VudGVyLmxqdXN0KDE2LCBiIlwwIikKICAgIGVsc2U6CiAgICAgICAgY291bnRlciA9IGNvdW50ZXJbOjE2XQogICAgYWVzID0gX1B1cmVBRVMxMjgoa2V5KQogICAgY3RyID0gaW50LmZyb21fYnl0ZXMoY291bnRlciwgImJpZyIpCiAgICBvdXQgPSBieXRlYXJyYXkoKQogICAgZm9yIG9mZnNldCBpbiByYW5nZSgwLCBsZW4oZGF0YSksIDE2KToKICAgICAgICBrcyA9IGFlcy5lbmNyeXB0X2Jsb2NrKGN0ci50b19ieXRlcygxNiwgImJpZyIpKQogICAgICAgIGN0ciA9IChjdHIgKyAxKSAmICgoMSA8PCAxMjgpIC0gMSkKICAgICAgICBjaHVuayA9IGRhdGFbb2Zmc2V0Om9mZnNldCArIDE2XQogICAgICAgIG91dC5leHRlbmQoYyBeIGsgZm9yIGMsIGsgaW4gemlwKGNodW5rLCBrcykpCiAgICByZXR1cm4gYnl0ZXMob3V0KQoKCmRlZiBfcHVyZV9jYmNfZGVjcnlwdChrZXk6IGJ5dGVzLCBpdjogYnl0ZXMsIGRhdGE6IGJ5dGVzKSAtPiBieXRlczoKICAgIGlmIG5vdCBkYXRhOgogICAgICAgIHJldHVybiBiIiIKICAgIGlmIGxlbihkYXRhKSAlIDE2OgogICAgICAgIGRhdGEgPSBkYXRhWzogbGVuKGRhdGEpIC0gKGxlbihkYXRhKSAlIDE2KV0KICAgIGFlcyA9IF9QdXJlQUVTMTI4KGtleSkKICAgIHByZXYgPSAoaXZbOjE2XSBpZiBsZW4oaXYpID49IDE2IGVsc2UgaXYpLmxqdXN0KDE2LCBiIlwwIikKICAgIG91dCA9IGJ5dGVhcnJheSgpCiAgICBmb3IgaSBpbiByYW5nZSgwLCBsZW4oZGF0YSksIDE2KToKICAgICAgICBibG9jayA9IGRhdGFbaTppICsgMTZdCiAgICAgICAgZGVjID0gYWVzLmRlY3J5cHRfYmxvY2soYmxvY2spCiAgICAgICAgb3V0LmV4dGVuZChkIF4gcCBmb3IgZCwgcCBpbiB6aXAoZGVjLCBwcmV2KSkKICAgICAgICBwcmV2ID0gYmxvY2sKICAgIHJldHVybiBieXRlcyhvdXQpCgoKZGVmIF9hZXNfY3RyX2RlY3J5cHQoa2V5OiBieXRlcywgY291bnRlcjogYnl0ZXMsIGRhdGE6IGJ5dGVzKSAtPiBieXRlczoKICAgIGlmIG5vdCBkYXRhOgogICAgICAgIHJldHVybiBiIiIKICAgIGlmIEFFU19CQUNLRU5EID09ICJjcnlwdG9ncmFwaHkiOgogICAgICAgIGRlY3J5cHRvciA9IENpcGhlcihhbGdvcml0aG1zLkFFUyhrZXkpLCBtb2Rlcy5DVFIoY291bnRlcikpLmRlY3J5cHRvcigpCiAgICAgICAgcmV0dXJuIGRlY3J5cHRvci51cGRhdGUoZGF0YSkgKyBkZWNyeXB0b3IuZmluYWxpemUoKQogICAgaWYgQUVTX0JBQ0tFTkQgPT0gInB5Y3J5cHRvZG9tZSI6CiAgICAgICAgY2lwaGVyID0gQ3J5cHRvQUVTLm5ldygKICAgICAgICAgICAga2V5LCBDcnlwdG9BRVMuTU9ERV9DVFIsIG5vbmNlPWIiIiwgaW5pdGlhbF92YWx1ZT1jb3VudGVyCiAgICAgICAgKQogICAgICAgIHJldHVybiBjaXBoZXIuZGVjcnlwdChkYXRhKQogICAgcmV0dXJuIF9wdXJlX2N0cl9kZWNyeXB0KGtleSwgY291bnRlciwgZGF0YSkKCgpkZWYgX2Flc19jYmNfZGVjcnlwdChrZXk6IGJ5dGVzLCBpdjogYnl0ZXMsIGRhdGE6IGJ5dGVzKSAtPiBieXRlczoKICAgIGlmIG5vdCBkYXRhOgogICAgICAgIHJldHVybiBiIiIKICAgIGlmIEFFU19CQUNLRU5EID09ICJjcnlwdG9ncmFwaHkiOgogICAgICAgIGRlY3J5cHRvciA9IENpcGhlcihhbGdvcml0aG1zLkFFUyhrZXkpLCBtb2Rlcy5DQkMoaXYpKS5kZWNyeXB0b3IoKQogICAgICAgIHJldHVybiBkZWNyeXB0b3IudXBkYXRlKGRhdGEpICsgZGVjcnlwdG9yLmZpbmFsaXplKCkKICAgIGlmIEFFU19CQUNLRU5EID09ICJweWNyeXB0b2RvbWUiOgogICAgICAgIHJldHVybiBDcnlwdG9BRVMubmV3KGtleSwgQ3J5cHRvQUVTLk1PREVfQ0JDLCBpdikuZGVjcnlwdChkYXRhKQogICAgcmV0dXJuIF9wdXJlX2NiY19kZWNyeXB0KGtleSwgaXYsIGRhdGEpCgoKU0lURSA9ICJodHRwczovL2hvbmdndW9kdWFuanUuY29tIgpFUElTT0RFX1BSRUZJWCA9ICJoZy1lcGlzb2RlLXYxOiIKIyDnuqLmnpzmr4/pm4bop4bpopHmqKHlnovmjInmuIXmmbDluqbov5Tlm57lpJrmnaHni6znq4vnur/ot6/vvIgzNjAvNDgwLzU0MC83MjAvMTA4MO+8ie+8jAojIOavj+adoeW4piBtYWluX3VybCArIGJhY2t1cF91cmwg5Y+MIENETiDkuI7ni6znq4vliqDlr4bmnZDmlpnjgILov5nph4zmiormuIXmmbDluqbkvZzkuLoKIyBUVkJveCDlpJrnur/ot6/mmrTpnLLvvJvlhoXlsIHpn7Mv6KeG6L2o5Zyo6Kej5a+GIF9yZXdyaXRlX21vb3Yg5pe25aSp54S25YWo6YOo5L+d55WZ44CCCl9IR19RVUFMSVRZX0xJTkVTID0gKAogICAgKCIxMDgwIiwgIue6ouaenOi2hea4hSIpLAogICAgKCI3MjAiLCAgIue6ouaenOmrmOa4hSIpLAogICAgKCI1NDAiLCAgIue6ouaenOagh+WHhiIpLAogICAgKCI0ODAiLCAgIue6ouaenOa1geeVhSIpLAogICAgKCIzNjAiLCAgIue6ouaenOaegemAnyIpLAopCl9RVUFMSVRZX0xJTkVfTkFNRV9UT19RID0gewogICAgIui2hea4hSI6ICIxMDgwIiwgIumrmOa4hSI6ICI3MjAiLCAi5qCH5YeGIjogIjU0MCIsCiAgICAi5rWB55WFIjogIjQ4MCIsICLmnoHpgJ8iOiAiMzYwIiwgIjEwODAiOiAiMTA4MCIsICI3MjAiOiAiNzIwIiwKICAgICI1NDAiOiAiNTQwIiwgIjQ4MCI6ICI0ODAiLCAiMzYwIjogIjM2MCIsCn0KCgpkZWYgX3NwbGl0X2VwaXNvZGVfdG9rZW4odG9rZW46IHN0cikgLT4gdHVwbGVbc3RyLCBzdHJdOgogICAgIiIi5oqKICdoZy1lcGlzb2RlLXYxOjxxPjo8dmlkPicg6Kej5p6Q5Li6ICjmuIXmmbDluqYsIHZpZCnvvJvlhbzlrrnml6fmoLzlvI8gJ2hnLWVwaXNvZGUtdjE6PHZpZD4n44CCIiIiCiAgICBib2R5ID0gc3RyKHRva2VuIG9yICIiKQogICAgaWYgYm9keS5zdGFydHN3aXRoKEVQSVNPREVfUFJFRklYKToKICAgICAgICBib2R5ID0gYm9keVtsZW4oRVBJU09ERV9QUkVGSVgpOl0KICAgIGlmICI6IiBpbiBib2R5OgogICAgICAgIGhlYWQsIHRhaWwgPSBib2R5LnNwbGl0KCI6IiwgMSkKICAgICAgICBpZiBoZWFkLmlzZGlnaXQoKToKICAgICAgICAgICAgcmV0dXJuIGhlYWQsIHRhaWwKICAgIHJldHVybiAiMTA4MCIsIGJvZHkKCiMg5a6Y572R5pCc57SiIFNTUiDlm7rlrprnuqYgMTAg5p2h5LiU5Yeg5LmO5LiN6K6kIHBhZ2XvvJvnlKjlpJrlhbPplK7or43ova7mjaLlrp7njrDigJznv7vpobXigJ0KX0FJX01BTkpVX0tFWVdPUkRTID0gWwogICAgIkFJ5ryr5YmnIiwgIkFJ5Yqo55S7IiwgIkFJ55+t5YmnIiwgIkFJ5Yqo5ryrIiwgIua8q+WJp0FJIiwgIuS6jOasoeWFg0FJIiwgIkFJ5ryr55S7IiwgIuWKqOeUu+efreWJpyIsCl0KCgojIC0tLS0g5pys5py66Kej5a+G57yT5a2YICsg6Ieq5Yqo5riF55CGIC0tLS0KX0hHX0NBQ0hFX0RJUiA9IE5vbmUKX0hHX0NBQ0hFX01BWF9GSUxFUyA9IDggICAgICAgICAgIyDmnIDlpJrkv53nlZnpm4bmlbAKX0hHX0NBQ0hFX01BWF9CWVRFUyA9IDQwMCAqIDEwMjQgKiAxMDI0ICAjIOaAu+WuuemHj+e6piA0MDBNQgpfSEdfQ0FDSEVfTUFYX0FHRSA9IDYgKiAzNjAwICAgICAjIOi2hei/hyA2IOWwj+aXtuiHquWKqOWIoAoKCmRlZiBfaGdfY2FjaGVfZGlyKCkgLT4gc3RyOgogICAgZ2xvYmFsIF9IR19DQUNIRV9ESVIKICAgIGlmIF9IR19DQUNIRV9ESVIgYW5kIG9zLnBhdGguaXNkaXIoX0hHX0NBQ0hFX0RJUik6CiAgICAgICAgcmV0dXJuIF9IR19DQUNIRV9ESVIKICAgIGNhbmRpZGF0ZXMgPSBbXQogICAgIyDkvJjlhYggQXBwIOWPr+WGmee8k+WtmOebruW9le+8iE9L5b2x6KeGIC8gRm9uZ01pIOW4uOingei3r+W+hO+8iQogICAgZm9yIHJvb3QgaW4gKAogICAgICAgICIvZGF0YS91c2VyLzAvY29tLmZvbmdtaS5hbmRyb2lkLm9rdHYvY2FjaGUiLAogICAgICAgICIvZGF0YS9kYXRhL2NvbS5mb25nbWkuYW5kcm9pZC5va3R2L2NhY2hlIiwKICAgICAgICAiL2RhdGEvdXNlci8wL2NvbS5mb25nbWkuYW5kcm9pZC50di9jYWNoZSIsCiAgICAgICAgIi9kYXRhL2RhdGEvY29tLmZvbmdtaS5hbmRyb2lkLnR2L2NhY2hlIiwKICAgICAgICAiL3NkY2FyZC9BbmRyb2lkL2RhdGEvY29tLmZvbmdtaS5hbmRyb2lkLm9rdHYvY2FjaGUiLAogICAgICAgICIvc2RjYXJkL0FuZHJvaWQvZGF0YS9jb20uZm9uZ21pLmFuZHJvaWQudHYvY2FjaGUiLAogICAgICAgICIvc2RjYXJkL0Rvd25sb2FkIiwKICAgICk6CiAgICAgICAgY2FuZGlkYXRlcy5hcHBlbmQob3MucGF0aC5qb2luKHJvb3QsICJoZ19jZW5jX2NhY2hlIikpCiAgICB0cnk6CiAgICAgICAgY2FuZGlkYXRlcy5hcHBlbmQob3MucGF0aC5qb2luKHRlbXBmaWxlLmdldHRlbXBkaXIoKSwgImhnX2NlbmNfY2FjaGUiKSkKICAgIGV4Y2VwdCBFeGNlcHRpb246CiAgICAgICAgcGFzcwogICAgdHJ5OgogICAgICAgIGNhbmRpZGF0ZXMuYXBwZW5kKG9zLnBhdGguam9pbihvcy5nZXRjd2QoKSwgImhnX2NlbmNfY2FjaGUiKSkKICAgIGV4Y2VwdCBFeGNlcHRpb246CiAgICAgICAgcGFzcwogICAgZm9yIHBhdGggaW4gY2FuZGlkYXRlczoKICAgICAgICB0cnk6CiAgICAgICAgICAgIG9zLm1ha2VkaXJzKHBhdGgsIGV4aXN0X29rPVRydWUpCiAgICAgICAgICAgIHRlc3QgPSBvcy5wYXRoLmpvaW4ocGF0aCwgIi53IikKICAgICAgICAgICAgd2l0aCBvcGVuKHRlc3QsICJ3YiIpIGFzIGZoOgogICAgICAgICAgICAgICAgZmgud3JpdGUoYiIxIikKICAgICAgICAgICAgb3MucmVtb3ZlKHRlc3QpCiAgICAgICAgICAgIF9IR19DQUNIRV9ESVIgPSBwYXRoCiAgICAgICAgICAgIHJldHVybiBwYXRoCiAgICAgICAgZXhjZXB0IEV4Y2VwdGlvbjoKICAgICAgICAgICAgY29udGludWUKICAgIF9IR19DQUNIRV9ESVIgPSB0ZW1wZmlsZS5ta2R0ZW1wKHByZWZpeD0iaGdfY2VuY18iKQogICAgcmV0dXJuIF9IR19DQUNIRV9ESVIKCgpkZWYgX2hnX2NhY2hlX3BhdGgodmlkOiBzdHIsIHF1YWxpdHk6IHN0cikgLT4gc3RyOgogICAgc2FmZSA9IHJlLnN1YihyIlteMC05QS1aYS16Xy1dIiwgIiIsIHN0cih2aWQpKVs6NDBdCiAgICBxID0gcmUuc3ViKHIiW14wLTlBLVphLXpdIiwgIiIsIHN0cihxdWFsaXR5IG9yICJxIikpWzo4XQogICAgcmV0dXJuIG9zLnBhdGguam9pbihfaGdfY2FjaGVfZGlyKCksICIlc18lcy5tcDQiICUgKHNhZmUsIHEpKQoKCmRlZiBfaGdfY2FjaGVfbGlzdCgpIC0+IGxpc3Q6CiAgICByb290ID0gX2hnX2NhY2hlX2RpcigpCiAgICBmaWxlcyA9IFtdCiAgICB0cnk6CiAgICAgICAgbm93ID0gdGltZS50aW1lKCkKICAgICAgICBmb3IgbmFtZSBpbiBvcy5saXN0ZGlyKHJvb3QpOgogICAgICAgICAgICBpZiBub3QgbmFtZS5lbmRzd2l0aCgiLm1wNCIpOgogICAgICAgICAgICAgICAgY29udGludWUKICAgICAgICAgICAgZnAgPSBvcy5wYXRoLmpvaW4ocm9vdCwgbmFtZSkKICAgICAgICAgICAgaWYgbm90IG9zLnBhdGguaXNmaWxlKGZwKToKICAgICAgICAgICAgICAgIGNvbnRpbnVlCiAgICAgICAgICAgIHRyeToKICAgICAgICAgICAgICAgIHN0ID0gb3Muc3RhdChmcCkKICAgICAgICAgICAgZXhjZXB0IEV4Y2VwdGlvbjoKICAgICAgICAgICAgICAgIGNvbnRpbnVlCiAgICAgICAgICAgIGZpbGVzLmFwcGVuZCh7InBhdGgiOiBmcCwgInNpemUiOiBzdC5zdF9zaXplLCAibXRpbWUiOiBzdC5zdF9tdGltZSwgImFnZSI6IG5vdyAtIHN0LnN0X210aW1lfSkKICAgIGV4Y2VwdCBFeGNlcHRpb246CiAgICAgICAgcmV0dXJuIFtdCiAgICBmaWxlcy5zb3J0KGtleT1sYW1iZGEgeDogeFsibXRpbWUiXSkgICMg5penIC0+IOaWsAogICAgcmV0dXJuIGZpbGVzCgoKZGVmIF9oZ19jYWNoZV9jbGVhbnVwKGZvcmNlOiBib29sID0gRmFsc2UpIC0+IE5vbmU6CiAgICAiIiLmjInml7bpl7QgKyDmlbDph48gKyDkvZPnp6/oh6rliqjmuIXnkIbmnKzmnLrnvJPlrZjjgIIiIiIKICAgIHRyeToKICAgICAgICBmaWxlcyA9IF9oZ19jYWNoZV9saXN0KCkKICAgICAgICBpZiBub3QgZmlsZXMgYW5kIG5vdCBmb3JjZToKICAgICAgICAgICAgcmV0dXJuCiAgICAgICAgIyAxKSDov4fmnJ/liKDpmaQKICAgICAgICByZW1haW4gPSBbXQogICAgICAgIGZvciBpdGVtIGluIGZpbGVzOgogICAgICAgICAgICBpZiBpdGVtWyJhZ2UiXSA+IF9IR19DQUNIRV9NQVhfQUdFIG9yIGl0ZW1bInNpemUiXSA8PSAwOgogICAgICAgICAgICAgICAgdHJ5OgogICAgICAgICAgICAgICAgICAgIG9zLnJlbW92ZShpdGVtWyJwYXRoIl0pCiAgICAgICAgICAgICAgICBleGNlcHQgRXhjZXB0aW9uOgogICAgICAgICAgICAgICAgICAgIHBhc3MKICAgICAgICAgICAgZWxzZToKICAgICAgICAgICAgICAgIHJlbWFpbi5hcHBlbmQoaXRlbSkKICAgICAgICAjIDIpIOi2hemHj+WIoOmZpOacgOaXpwogICAgICAgIHRvdGFsID0gc3VtKHhbInNpemUiXSBmb3IgeCBpbiByZW1haW4pCiAgICAgICAgd2hpbGUgcmVtYWluIGFuZCAobGVuKHJlbWFpbikgPiBfSEdfQ0FDSEVfTUFYX0ZJTEVTIG9yIHRvdGFsID4gX0hHX0NBQ0hFX01BWF9CWVRFUyk6CiAgICAgICAgICAgIG9sZCA9IHJlbWFpbi5wb3AoMCkKICAgICAgICAgICAgdHJ5OgogICAgICAgICAgICAgICAgb3MucmVtb3ZlKG9sZFsicGF0aCJdKQogICAgICAgICAgICBleGNlcHQgRXhjZXB0aW9uOgogICAgICAgICAgICAgICAgcGFzcwogICAgICAgICAgICB0b3RhbCAtPSBvbGRbInNpemUiXQogICAgICAgICMgMykg5riF55CG5q6L55WZIHRtcAogICAgICAgIHJvb3QgPSBfaGdfY2FjaGVfZGlyKCkKICAgICAgICBmb3IgbmFtZSBpbiBvcy5saXN0ZGlyKHJvb3QpOgogICAgICAgICAgICBpZiBuYW1lLmVuZHN3aXRoKCIudG1wIikgb3IgbmFtZSA9PSAiLnciOgogICAgICAgICAgICAgICAgdHJ5OgogICAgICAgICAgICAgICAgICAgIG9zLnJlbW92ZShvcy5wYXRoLmpvaW4ocm9vdCwgbmFtZSkpCiAgICAgICAgICAgICAgICBleGNlcHQgRXhjZXB0aW9uOgogICAgICAgICAgICAgICAgICAgIHBhc3MKICAgIGV4Y2VwdCBFeGNlcHRpb246CiAgICAgICAgcGFzcwoKCmRlZiBfaGdfY2FjaGVfY2xlYXJfYWxsKCkgLT4gTm9uZToKICAgIHRyeToKICAgICAgICByb290ID0gX2hnX2NhY2hlX2RpcigpCiAgICAgICAgZm9yIG5hbWUgaW4gb3MubGlzdGRpcihyb290KToKICAgICAgICAgICAgZnAgPSBvcy5wYXRoLmpvaW4ocm9vdCwgbmFtZSkKICAgICAgICAgICAgdHJ5OgogICAgICAgICAgICAgICAgaWYgb3MucGF0aC5pc2ZpbGUoZnApOgogICAgICAgICAgICAgICAgICAgIG9zLnJlbW92ZShmcCkKICAgICAgICAgICAgZXhjZXB0IEV4Y2VwdGlvbjoKICAgICAgICAgICAgICAgIHBhc3MKICAgIGV4Y2VwdCBFeGNlcHRpb246CiAgICAgICAgcGFzcwoKCmRlZiBfaGdfY2FjaGVfZ2V0KHZpZDogc3RyLCBxdWFsaXR5OiBzdHIpIC0+IGJ5dGVzIHwgTm9uZToKICAgIF9oZ19jYWNoZV9jbGVhbnVwKEZhbHNlKQogICAgcGF0aCA9IF9oZ19jYWNoZV9wYXRoKHZpZCwgcXVhbGl0eSkKICAgIHRyeToKICAgICAgICBpZiBvcy5wYXRoLmlzZmlsZShwYXRoKSBhbmQgb3MucGF0aC5nZXRzaXplKHBhdGgpID4gNjQ6CiAgICAgICAgICAgICMg6K+75pe25Yi35pawIG10aW1l77yM6YG/5YWN5Yia5pKt5Y+I6KKr5b2T6L+H5pyf5YigCiAgICAgICAgICAgIHRyeToKICAgICAgICAgICAgICAgIG9zLnV0aW1lKHBhdGgsIE5vbmUpCiAgICAgICAgICAgIGV4Y2VwdCBFeGNlcHRpb246CiAgICAgICAgICAgICAgICBwYXNzCiAgICAgICAgICAgIHdpdGggb3BlbihwYXRoLCAicmIiKSBhcyBmaDoKICAgICAgICAgICAgICAgIHJldHVybiBmaC5yZWFkKCkKICAgIGV4Y2VwdCBFeGNlcHRpb246CiAgICAgICAgcmV0dXJuIE5vbmUKICAgIHJldHVybiBOb25lCgoKZGVmIF9oZ19jYWNoZV9wdXQodmlkOiBzdHIsIHF1YWxpdHk6IHN0ciwgZGF0YTogYnl0ZXMpIC0+IE5vbmU6CiAgICBpZiBub3QgZGF0YSBvciBsZW4oZGF0YSkgPCA2NDoKICAgICAgICByZXR1cm4KICAgIHBhdGggPSBfaGdfY2FjaGVfcGF0aCh2aWQsIHF1YWxpdHkpCiAgICB0cnk6CiAgICAgICAgX2hnX2NhY2hlX2NsZWFudXAoRmFsc2UpCiAgICAgICAgdG1wID0gcGF0aCArICIudG1wIgogICAgICAgIHdpdGggb3Blbih0bXAsICJ3YiIpIGFzIGZoOgogICAgICAgICAgICBmaC53cml0ZShkYXRhKQogICAgICAgIG9zLnJlcGxhY2UodG1wLCBwYXRoKQogICAgICAgIF9oZ19jYWNoZV9jbGVhbnVwKEZhbHNlKQogICAgZXhjZXB0IEV4Y2VwdGlvbjoKICAgICAgICB0cnk6CiAgICAgICAgICAgIGlmIG9zLnBhdGguZXhpc3RzKHBhdGggKyAiLnRtcCIpOgogICAgICAgICAgICAgICAgb3MucmVtb3ZlKHBhdGggKyAiLnRtcCIpCiAgICAgICAgZXhjZXB0IEV4Y2VwdGlvbjoKICAgICAgICAgICAgcGFzcwoKCmRlZiBfYWVzX2lzX2Zhc3QoKSAtPiBib29sOgogICAgcmV0dXJuIEFFU19CQUNLRU5EIGluICgiY3J5cHRvZ3JhcGh5IiwgInB5Y3J5cHRvZG9tZSIpCgoKZGVmIF9hZXNfaXNfZmFzdCgpIC0+IGJvb2w6CiAgICByZXR1cm4gQUVTX0JBQ0tFTkQgaW4gKCJjcnlwdG9ncmFwaHkiLCAicHljcnlwdG9kb21lIikKCgpkZWYgX2h0dHBfZ2V0X2J5dGVzKHVybDogc3RyLCBoZWFkZXJzOiBkaWN0IHwgTm9uZSA9IE5vbmUsIHRpbWVvdXQ6IGludCA9IDYwKSAtPiBieXRlczoKICAgIGggPSBkaWN0KGhlYWRlcnMgb3Ige30pCiAgICByID0gcmVxdWVzdHMuZ2V0KHVybCwgaGVhZGVycz1oLCB0aW1lb3V0PXRpbWVvdXQpCiAgICByLnJhaXNlX2Zvcl9zdGF0dXMoKQogICAgcmV0dXJuIHIuY29udGVudAoKCmRlZiBfcHJvYmVfY29udGVudF9sZW5ndGgodXJsOiBzdHIsIGhlYWRlcnM6IGRpY3QgfCBOb25lID0gTm9uZSwgdGltZW91dDogaW50ID0gMzApIC0+IGludDoKICAgIGggPSBkaWN0KGhlYWRlcnMgb3Ige30pCiAgICB0cnk6CiAgICAgICAgciA9IHJlcXVlc3RzLmhlYWQodXJsLCBoZWFkZXJzPWgsIHRpbWVvdXQ9dGltZW91dCwgYWxsb3dfcmVkaXJlY3RzPVRydWUpCiAgICAgICAgaWYgci5zdGF0dXNfY29kZSA8IDQwMDoKICAgICAgICAgICAgY2wgPSByLmhlYWRlcnMuZ2V0KCJDb250ZW50LUxlbmd0aCIpIG9yIHIuaGVhZGVycy5nZXQoImNvbnRlbnQtbGVuZ3RoIikKICAgICAgICAgICAgaWYgY2wgYW5kIHN0cihjbCkuaXNkaWdpdCgpOgogICAgICAgICAgICAgICAgcmV0dXJuIGludChjbCkKICAgIGV4Y2VwdCBFeGNlcHRpb246CiAgICAgICAgcGFzcwogICAgdHJ5OgogICAgICAgIGhoID0gZGljdChoKQogICAgICAgIGhoWyJSYW5nZSJdID0gImJ5dGVzPTAtMCIKICAgICAgICByID0gcmVxdWVzdHMuZ2V0KHVybCwgaGVhZGVycz1oaCwgdGltZW91dD10aW1lb3V0KQogICAgICAgIGNyID0gci5oZWFkZXJzLmdldCgiQ29udGVudC1SYW5nZSIpIG9yIHIuaGVhZGVycy5nZXQoImNvbnRlbnQtcmFuZ2UiKSBvciAiIgogICAgICAgICMgYnl0ZXMgMC0wLzEyMzQ1CiAgICAgICAgaWYgIi8iIGluIGNyOgogICAgICAgICAgICB0b3RhbCA9IGNyLnNwbGl0KCIvIilbLTFdLnN0cmlwKCkKICAgICAgICAgICAgaWYgdG90YWwuaXNkaWdpdCgpOgogICAgICAgICAgICAgICAgcmV0dXJuIGludCh0b3RhbCkKICAgICAgICBjbCA9IHIuaGVhZGVycy5nZXQoIkNvbnRlbnQtTGVuZ3RoIikgb3IgIjAiCiAgICAgICAgaWYgc3RyKGNsKS5pc2RpZ2l0KCkgYW5kIGludChjbCkgPiAxOgogICAgICAgICAgICByZXR1cm4gaW50KGNsKQogICAgZXhjZXB0IEV4Y2VwdGlvbjoKICAgICAgICBwYXNzCiAgICByZXR1cm4gMAoKCmRlZiBfZG93bmxvYWRfcmFuZ2UodXJsOiBzdHIsIHN0YXJ0OiBpbnQsIGVuZDogaW50LCBoZWFkZXJzOiBkaWN0IHwgTm9uZSwgdGltZW91dDogaW50KSAtPiB0dXBsZVtpbnQsIGJ5dGVzXToKICAgIGggPSBkaWN0KGhlYWRlcnMgb3Ige30pCiAgICBoWyJSYW5nZSJdID0gImJ5dGVzPSVkLSVkIiAlIChzdGFydCwgZW5kKQogICAgbGFzdF9lcnIgPSBOb25lCiAgICBmb3IgYXR0ZW1wdCBpbiByYW5nZSgzKToKICAgICAgICB0cnk6CiAgICAgICAgICAgIHIgPSByZXF1ZXN0cy5nZXQodXJsLCBoZWFkZXJzPWgsIHRpbWVvdXQ9dGltZW91dCkKICAgICAgICAgICAgaWYgci5zdGF0dXNfY29kZSBub3QgaW4gKDIwMCwgMjA2KToKICAgICAgICAgICAgICAgIHJhaXNlIFJ1bnRpbWVFcnJvcigicmFuZ2UgaHR0cCAlcyIgJSByLnN0YXR1c19jb2RlKQogICAgICAgICAgICBkYXRhID0gci5jb250ZW50CiAgICAgICAgICAgIGlmIG5vdCBkYXRhOgogICAgICAgICAgICAgICAgcmFpc2UgUnVudGltZUVycm9yKCJlbXB0eSByYW5nZSBib2R5IikKICAgICAgICAgICAgcmV0dXJuIHN0YXJ0LCBkYXRhCiAgICAgICAgZXhjZXB0IEV4Y2VwdGlvbiBhcyBlcnI6CiAgICAgICAgICAgIGxhc3RfZXJyID0gZXJyCiAgICAgICAgICAgIHRyeToKICAgICAgICAgICAgICAgIHRpbWUuc2xlZXAoMC4yNSAqIChhdHRlbXB0ICsgMSkpCiAgICAgICAgICAgIGV4Y2VwdCBFeGNlcHRpb246CiAgICAgICAgICAgICAgICBwYXNzCiAgICByYWlzZSBSdW50aW1lRXJyb3IoInJhbmdlICVzLSVzIGZhaWxlZDogJXMiICUgKHN0YXJ0LCBlbmQsIGxhc3RfZXJyKSkKCgpkZWYgX211bHRpX2Rvd25sb2FkKHVybDogc3RyLCBoZWFkZXJzOiBkaWN0IHwgTm9uZSA9IE5vbmUsIHRpbWVvdXQ6IGludCA9IDkwLCB3b3JrZXJzOiBpbnQgPSA0KSAtPiBieXRlczoKICAgICIiIuWkmuWIhueJh+W5tuihjOS4i+i9ve+8jOWksei0peWImeWbnumAgOaVtOaWh+S7tuWNlee6v+eoi+OAgiIiIgogICAgaGVhZGVycyA9IGRpY3QoaGVhZGVycyBvciB7fSkKICAgIHRvdGFsID0gX3Byb2JlX2NvbnRlbnRfbGVuZ3RoKHVybCwgaGVhZGVycywgdGltZW91dD1taW4oMzAsIHRpbWVvdXQpKQogICAgIyDlpKrlsI/miJbmnKrnn6Xplb/luqbvvJrnm7TmjqXmlbTkuIsKICAgIGlmIHRvdGFsIDw9IDAgb3IgdG90YWwgPCAyICogMTAyNCAqIDEwMjQ6CiAgICAgICAgcmV0dXJuIF9odHRwX2dldF9ieXRlcyh1cmwsIGhlYWRlcnMsIHRpbWVvdXQ9dGltZW91dCkKCiAgICAjIOWIhueJh+Wkp+WwjyAxfjJNQu+8jOe6v+eoi+aVsOmZkOWItgogICAgd29ya2VycyA9IG1heCgyLCBtaW4oaW50KHdvcmtlcnMgb3IgNCksIDYpKQogICAgY2h1bmsgPSBtYXgoMSAqIDEwMjQgKiAxMDI0LCBtaW4oMiAqIDEwMjQgKiAxMDI0LCB0b3RhbCAvLyB3b3JrZXJzKSkKICAgIHJhbmdlcyA9IFtdCiAgICBzdGFydCA9IDAKICAgIHdoaWxlIHN0YXJ0IDwgdG90YWw6CiAgICAgICAgZW5kID0gbWluKHRvdGFsIC0gMSwgc3RhcnQgKyBjaHVuayAtIDEpCiAgICAgICAgcmFuZ2VzLmFwcGVuZCgoc3RhcnQsIGVuZCkpCiAgICAgICAgc3RhcnQgPSBlbmQgKyAxCgogICAgcGFydHM6IGRpY3RbaW50LCBieXRlc10gPSB7fQogICAgdHJ5OgogICAgICAgIHdpdGggY29uY3VycmVudC5mdXR1cmVzLlRocmVhZFBvb2xFeGVjdXRvcihtYXhfd29ya2Vycz13b3JrZXJzKSBhcyBwb29sOgogICAgICAgICAgICBmdXRzID0gWwogICAgICAgICAgICAgICAgcG9vbC5zdWJtaXQoX2Rvd25sb2FkX3JhbmdlLCB1cmwsIHMsIGUsIGhlYWRlcnMsIHRpbWVvdXQpCiAgICAgICAgICAgICAgICBmb3IgcywgZSBpbiByYW5nZXMKICAgICAgICAgICAgXQogICAgICAgICAgICBmb3IgZnV0IGluIGNvbmN1cnJlbnQuZnV0dXJlcy5hc19jb21wbGV0ZWQoZnV0cyk6CiAgICAgICAgICAgICAgICBzLCBkYXRhID0gZnV0LnJlc3VsdCgpCiAgICAgICAgICAgICAgICBwYXJ0c1tzXSA9IGRhdGEKICAgIGV4Y2VwdCBFeGNlcHRpb246CiAgICAgICAgIyDlubbooYzlpLHotKXlm57pgIAKICAgICAgICByZXR1cm4gX2h0dHBfZ2V0X2J5dGVzKHVybCwgaGVhZGVycywgdGltZW91dD10aW1lb3V0KQoKICAgIGJ1ZiA9IGJ5dGVhcnJheSgpCiAgICBmb3IgcywgZSBpbiByYW5nZXM6CiAgICAgICAgcGllY2UgPSBwYXJ0cy5nZXQocykKICAgICAgICBpZiBwaWVjZSBpcyBOb25lOgogICAgICAgICAgICByZXR1cm4gX2h0dHBfZ2V0X2J5dGVzKHVybCwgaGVhZGVycywgdGltZW91dD10aW1lb3V0KQogICAgICAgIGJ1Zi5leHRlbmQocGllY2UpCiAgICBpZiBsZW4oYnVmKSA8IHRvdGFsICogMC45NToKICAgICAgICAjIOaYjuaYvuS4jeWujOaVtAogICAgICAgIHJldHVybiBfaHR0cF9nZXRfYnl0ZXModXJsLCBoZWFkZXJzLCB0aW1lb3V0PXRpbWVvdXQpCiAgICByZXR1cm4gYnl0ZXMoYnVmKQoKCgpfTUFOSlVfS0VZV09SRFMgPSBbCiAgICAi5ryr5YmnIiwgIuWKqOa8q+efreWJpyIsICLkuozmrKHlhYMiLCAi5ryr55S755+t5YmnIiwgIuWbvea8q+efreWJpyIsICLml6XmvKsiLCAi5Yqo5oCB5ryrIiwgIuWKqOeUu+WJpyIsCl0KClZJREVPX1VSTCA9ICJodHRwczovL2FwaTUtbm9ybWFsLXNpbmZvbmxpbmViLmZxbm92ZWwuY29tL25vdmVsL3BsYXllci9tdWx0aV92aWRlb19tb2RlbC92MS8iClVBID0gIk1vemlsbGEvNS4wIChMaW51eDsgQW5kcm9pZCAxMikgQXBwbGVXZWJLaXQvNTM3LjM2IChLSFRNTCwgbGlrZSBHZWNrbykgQ2hyb21lLzEyNi4wIFNhZmFyaS81MzcuMzYiCkFQUF9VQSA9ICJjb20ucGhvZW5peC5yZWFkLzcxMzMyIChMaW51eDsgVTsgQW5kcm9pZCAxNjsgemhfQ047IDI1MDUzUlQ0N0M7IEJ1aWxkL0JQMkEuMjUwNjA1LjAzMS5BMzsgQ3JvbmV0L1RUTmV0VmVyc2lvbjowNDY1Nzc5NSAyMDI2LTAxLTIzIFF1aWNWZXJzaW9uOmM2N2U5ODM0IDIwMjUtMDktMDgpIgpNRURJQV9VQSA9ICJjb20ucGhvZW5peC5yZWFkLzcxMzMyIgoKCgoKX0hUTUxfRkVUQ0hfQVRURU1QVFMgPSAzCgpfSFRNTF9GRVRDSF9CQUNLT0ZGX1NFQ09ORFMgPSAxLjUKCl9SQU5HRV9GRVRDSF9BVFRFTVBUUyA9IDMKCl9SQU5HRV9GRVRDSF9CQUNLT0ZGX1NFQ09ORFMgPSAwLjgKCmNsYXNzIEhvbmdndW9QbHVnaW5FcnJvcihSdW50aW1lRXJyb3IpOgogICAgcGFzcwoKZGVmIF90ZXh0KHZhbHVlOiBBbnkpIC0+IHN0cjoKICAgIHJldHVybiBzdHIodmFsdWUgb3IgIiIpLnN0cmlwKCkKCmRlZiBfZmlyc3QoKnZhbHVlczogQW55KSAtPiBzdHI6CiAgICBmb3IgdmFsdWUgaW4gdmFsdWVzOgogICAgICAgIGlmIGlzaW5zdGFuY2UodmFsdWUsIChsaXN0LCB0dXBsZSkpOgogICAgICAgICAgICByZXN1bHQgPSBfZmlyc3QoKnZhbHVlKQogICAgICAgIGVsaWYgaXNpbnN0YW5jZSh2YWx1ZSwgTWFwcGluZyk6CiAgICAgICAgICAgIHJlc3VsdCA9IF9maXJzdCgKICAgICAgICAgICAgICAgIHZhbHVlLmdldCgidXJsIiksCiAgICAgICAgICAgICAgICB2YWx1ZS5nZXQoInVyaSIpLAogICAgICAgICAgICAgICAgdmFsdWUuZ2V0KCJzcmMiKSwKICAgICAgICAgICAgICAgIHZhbHVlLmdldCgiZG93bmxvYWRfdXJsIiksCiAgICAgICAgICAgICAgICB2YWx1ZS5nZXQoIm1haW5fdXJsIiksCiAgICAgICAgICAgICAgICB2YWx1ZS5nZXQoImJhY2t1cF91cmwiKSwKICAgICAgICAgICAgICAgIHZhbHVlLmdldCgiYmFja3VwX3VybF8xIiksCiAgICAgICAgICAgICAgICB2YWx1ZS5nZXQoInBsYXlfYWRkciIpLAogICAgICAgICAgICAgICAgdmFsdWUuZ2V0KCJ1cmxfbGlzdCIpLAogICAgICAgICAgICApCiAgICAgICAgZWxzZToKICAgICAgICAgICAgcmVzdWx0ID0gX3RleHQodmFsdWUpCiAgICAgICAgaWYgcmVzdWx0OgogICAgICAgICAgICByZXR1cm4gcmVzdWx0CiAgICByZXR1cm4gIiIKCmRlZiBfanNvbl9yZXNwb25zZShyZXNwb25zZTogcmVxdWVzdHMuUmVzcG9uc2UpIC0+IEFueToKICAgIHJlc3BvbnNlLnJhaXNlX2Zvcl9zdGF0dXMoKQogICAgdHJ5OgogICAgICAgIHJldHVybiByZXNwb25zZS5qc29uKCkKICAgIGV4Y2VwdCBWYWx1ZUVycm9yIGFzIGV4YzoKICAgICAgICByYWlzZSBIb25nZ3VvUGx1Z2luRXJyb3IoIuS4iua4uOWTjeW6lOS4jeaYryBKU09OIikgZnJvbSBleGMKCmRlZiBfZ2V0X2h0bWwodXJsOiBzdHIsICosIGF0dGVtcHRzOiBpbnQgPSBfSFRNTF9GRVRDSF9BVFRFTVBUUykgLT4gc3RyOgogICAgbGFzdF9lcnJvcjogRXhjZXB0aW9uIHwgTm9uZSA9IE5vbmUKICAgIGZvciBhdHRlbXB0IGluIHJhbmdlKG1heCgxLCBhdHRlbXB0cykpOgogICAgICAgIHRyeToKICAgICAgICAgICAgcmVzcG9uc2UgPSByZXF1ZXN0cy5nZXQoCiAgICAgICAgICAgICAgICB1cmwsCiAgICAgICAgICAgICAgICBoZWFkZXJzPXsKICAgICAgICAgICAgICAgICAgICAiVXNlci1BZ2VudCI6IFVBLAogICAgICAgICAgICAgICAgICAgICJBY2NlcHQtTGFuZ3VhZ2UiOiAiemgtQ04semg7cT0wLjkiLAogICAgICAgICAgICAgICAgfSwKICAgICAgICAgICAgICAgIHRpbWVvdXQ9MzAsCiAgICAgICAgICAgICkKICAgICAgICAgICAgcmVzcG9uc2UucmFpc2VfZm9yX3N0YXR1cygpCiAgICAgICAgICAgIHJlc3BvbnNlLmVuY29kaW5nID0gcmVzcG9uc2UuZW5jb2Rpbmcgb3IgInV0Zi04IgogICAgICAgICAgICByZXR1cm4gcmVzcG9uc2UudGV4dAogICAgICAgIGV4Y2VwdCBFeGNlcHRpb24gYXMgZXJyb3I6ICAjIHRyYW5zaWVudCBwcm94eS9ETlMvcmVhZCBmYWlsdXJlcwogICAgICAgICAgICBsYXN0X2Vycm9yID0gZXJyb3IKICAgICAgICAgICAgaWYgYXR0ZW1wdCArIDEgPCBtYXgoMSwgYXR0ZW1wdHMpOgogICAgICAgICAgICAgICAgdGltZS5zbGVlcChfSFRNTF9GRVRDSF9CQUNLT0ZGX1NFQ09ORFMgKiAoYXR0ZW1wdCArIDEpKQogICAgcmFpc2UgSG9uZ2d1b1BsdWdpbkVycm9yKGYiZmV0Y2ggZmFpbGVkOiB7dXJsfSIpIGZyb20gbGFzdF9lcnJvcgoKZGVmIF9yb3V0ZXJfZGF0YShodG1sOiBzdHIpIC0+IGRpY3Rbc3RyLCBBbnldOgogICAgbWF0Y2ggPSByZS5zZWFyY2gociIoPzp3aW5kb3dcLik/X1JPVVRFUl9EQVRBXHMqPVxzKiIsIGh0bWwpCiAgICBpZiBub3QgbWF0Y2g6CiAgICAgICAgcmFpc2UgSG9uZ2d1b1BsdWdpbkVycm9yKCLpobXpnaLmsqHmnInot6/nlLHmlbDmja4iKQogICAgdHJ5OgogICAgICAgIHZhbHVlLCBfID0ganNvbi5KU09ORGVjb2RlcigpLnJhd19kZWNvZGUoaHRtbFttYXRjaC5lbmQoKSA6XSkKICAgIGV4Y2VwdCBqc29uLkpTT05EZWNvZGVFcnJvciBhcyBleGM6CiAgICAgICAgcmFpc2UgSG9uZ2d1b1BsdWdpbkVycm9yKCLpobXpnaLot6/nlLHmlbDmja7op6PmnpDlpLHotKUiKSBmcm9tIGV4YwogICAgaWYgbm90IGlzaW5zdGFuY2UodmFsdWUsIGRpY3QpOgogICAgICAgIHJhaXNlIEhvbmdndW9QbHVnaW5FcnJvcigi6aG16Z2i6Lev55Sx5pWw5o2u5qC85byP6ZSZ6K+vIikKICAgIHJldHVybiB2YWx1ZQoKZGVmIF9tZWRpYV91cmwoaXRlbTogTWFwcGluZ1tzdHIsIEFueV0pIC0+IHN0cjoKICAgIHJldHVybiBfZmlyc3QoCiAgICAgICAgaXRlbS5nZXQoIm1haW5fdXJsIiksCiAgICAgICAgaXRlbS5nZXQoImJhY2t1cF91cmwiKSwKICAgICAgICBpdGVtLmdldCgiYmFja3VwX3VybF8xIiksCiAgICAgICAgaXRlbS5nZXQoInBsYXlfYWRkciIpLAogICAgICAgIGl0ZW0uZ2V0KCJ1cmwiKSwKICAgICkKCmRlZiBfc3BhZGVfdmFsdWUoaXRlbTogTWFwcGluZ1tzdHIsIEFueV0pIC0+IHN0cjoKICAgIGVuY3J5cHRfaW5mbyA9IGl0ZW0uZ2V0KCJlbmNyeXB0X2luZm8iKQogICAgaWYgbm90IGlzaW5zdGFuY2UoZW5jcnlwdF9pbmZvLCBNYXBwaW5nKToKICAgICAgICBlbmNyeXB0X2luZm8gPSB7fQogICAgcmV0dXJuIF9maXJzdChpdGVtLmdldCgic3BhZGVfYSIpLCBlbmNyeXB0X2luZm8uZ2V0KCJzcGFkZV9hIikpCgpkZWYgZGVyaXZlX2NvbnRlbnRfa2V5KHNwYWRlX2I2NDogc3RyKSAtPiBieXRlczoKICAgIHJhdyA9IF9iNjQoc3BhZGVfYjY0KQogICAgaWYgbGVuKHJhdykgPCAzOgogICAgICAgIHJhaXNlIEhvbmdndW9QbHVnaW5FcnJvcigic3BhZGVfYSDlpKrnn60iKQogICAgdjggPSBsZW4ocmF3KSAtIChyYXdbMF0gXiByYXdbMV0gXiByYXdbMl0pICsgNDcKICAgIGlmIHY4IDw9IDAgb3IgMSArIHY4ID4gbGVuKHJhdyk6CiAgICAgICAgdjggPSBsZW4ocmF3KSAtIDEKICAgIGlmIHY4IDwgMzM6CiAgICAgICAgcmFpc2UgSG9uZ2d1b1BsdWdpbkVycm9yKCJzcGFkZV9hIOmVv+W6puW8guW4uCIpCiAgICB2YWx1ZSA9IGJ5dGVhcnJheShyYXdbMSA6IDEgKyB2OF0pCiAgICB2YSwgdmIgPSA4NSwgMjQ2CiAgICBmb3IgaW5kZXggaW4gcmFuZ2UodjgpOgogICAgICAgIHByZXZpb3VzID0gdmEgaWYgaW5kZXggJiAxIGVsc2UgdmIKICAgICAgICBpZiBpbmRleCAmIDE6CiAgICAgICAgICAgIHZhID0gdmFsdWVbaW5kZXhdCiAgICAgICAgZWxzZToKICAgICAgICAgICAgdmIgPSB2YWx1ZVtpbmRleF0KICAgICAgICB2YWx1ZVtpbmRleF0gPSAoLTIxIC0gYmluKGluZGV4KS5jb3VudCgiMSIpICsgKHByZXZpb3VzIF4gdmFsdWVbaW5kZXhdKSkgJiAweEZGCiAgICB0cnk6CiAgICAgICAgcmV0dXJuIGJpbmFzY2lpLnVuaGV4bGlmeShieXRlcyh2YWx1ZVsxOjMzXSkuZGVjb2RlKCJhc2NpaSIpKQogICAgZXhjZXB0IChWYWx1ZUVycm9yLCBiaW5hc2NpaS5FcnJvcikgYXMgZXhjOgogICAgICAgIHJhaXNlIEhvbmdndW9QbHVnaW5FcnJvcigic3BhZGVfYSDlr4bpkqXmnZDmlpnml6DmlYgiKSBmcm9tIGV4YwoKZGVmIF9maW5kX2JveChkYXRhOiBtZW1vcnl2aWV3LCBmb3VyY2M6IGJ5dGVzLCBzdGFydDogaW50KSAtPiB0dXBsZVtpbnQsIGludF06CiAgICBmb3IgaW5kZXggaW4gcmFuZ2UobWF4KDQsIHN0YXJ0KSwgbGVuKGRhdGEpIC0gNCk6CiAgICAgICAgaWYgZGF0YVtpbmRleCA6IGluZGV4ICsgNF0gIT0gZm91cmNjOgogICAgICAgICAgICBjb250aW51ZQogICAgICAgIHNpemUgPSBzdHJ1Y3QudW5wYWNrKCI+SSIsIGRhdGFbaW5kZXggLSA0IDogaW5kZXhdKVswXQogICAgICAgIGlmIHNpemUgPT0gMSBhbmQgaW5kZXggKyAxMiA8PSBsZW4oZGF0YSk6CiAgICAgICAgICAgIHNpemUgPSBzdHJ1Y3QudW5wYWNrKCI+USIsIGRhdGFbaW5kZXggKyA0IDogaW5kZXggKyAxMl0pWzBdCiAgICAgICAgaWYgOCA8PSBzaXplIDw9IDVfMDAwXzAwMCBhbmQgaW5kZXggLSA0ICsgc2l6ZSA8PSBsZW4oZGF0YSk6CiAgICAgICAgICAgIHJldHVybiBpbmRleCAtIDQsIHNpemUKICAgIHJldHVybiAtMSwgMAoKZGVmIF9ib3hfYm9keShkYXRhOiBtZW1vcnl2aWV3LCBmb3VyY2M6IGJ5dGVzLCBzdGFydDogaW50KSAtPiBtZW1vcnl2aWV3IHwgTm9uZToKICAgIG9mZnNldCwgc2l6ZSA9IF9maW5kX2JveChkYXRhLCBmb3VyY2MsIHN0YXJ0KQogICAgcmV0dXJuIGRhdGFbb2Zmc2V0ICsgOCA6IG9mZnNldCArIHNpemVdIGlmIG9mZnNldCA+PSAwIGVsc2UgTm9uZQoKZGVmIF9wYXJzZV90cmFjaygKICAgIG1vb3Y6IG1lbW9yeXZpZXcsCiAgICB0cmFja19vZmZzZXQ6IGludCwKKSAtPiB0dXBsZVtsaXN0W2ludF0sIGxpc3RbaW50XSwgbGlzdFtpbnRdLCBsaXN0W2ludF0sIGludCwgaW50XSB8IE5vbmU6CiAgICBpZiB0cmFja19vZmZzZXQgPCAwOgogICAgICAgIHJldHVybiBOb25lCiAgICBzdGJsX29mZnNldCwgXyA9IF9maW5kX2JveChtb292LCBiInN0YmwiLCB0cmFja19vZmZzZXQgKyA4KQogICAgaWYgc3RibF9vZmZzZXQgPCAwOgogICAgICAgIHJldHVybiBOb25lCiAgICBzdHN6ID0gX2JveF9ib2R5KG1vb3YsIGIic3RzeiIsIHN0Ymxfb2Zmc2V0KQogICAgc3RjbyA9IF9ib3hfYm9keShtb292LCBiInN0Y28iLCBzdGJsX29mZnNldCkKICAgIGNvNjQgPSBfYm94X2JvZHkobW9vdiwgYiJjbzY0Iiwgc3RibF9vZmZzZXQpCiAgICBzdHNjID0gX2JveF9ib2R5KG1vb3YsIGIic3RzYyIsIHN0Ymxfb2Zmc2V0KQogICAgc2FpeiA9IF9ib3hfYm9keShtb292LCBiInNhaXoiLCBzdGJsX29mZnNldCkKICAgIHNhaW8gPSBfYm94X2JvZHkobW9vdiwgYiJzYWlvIiwgc3RibF9vZmZzZXQpCiAgICBpZiBhbnkodmFsdWUgaXMgTm9uZSBmb3IgdmFsdWUgaW4gKHN0c3osIHN0c2MsIHNhaXosIHNhaW8pKSBvciAoCiAgICAgICAgc3RjbyBpcyBOb25lIGFuZCBjbzY0IGlzIE5vbmUKICAgICk6CiAgICAgICAgcmV0dXJuIE5vbmUKICAgIGFzc2VydCBzdHN6IGlzIG5vdCBOb25lIGFuZCBzdHNjIGlzIG5vdCBOb25lCiAgICBhc3NlcnQgc2FpeiBpcyBub3QgTm9uZSBhbmQgc2FpbyBpcyBub3QgTm9uZQogICAgZGVmYXVsdF9zaXplID0gc3RydWN0LnVucGFjaygiPkkiLCBzdHN6WzQ6OF0pWzBdCiAgICBzYW1wbGVfY291bnQgPSBzdHJ1Y3QudW5wYWNrKCI+SSIsIHN0c3pbODoxMl0pWzBdCiAgICBzaXplcyA9ICgKICAgICAgICBbZGVmYXVsdF9zaXplXSAqIHNhbXBsZV9jb3VudAogICAgICAgIGlmIGRlZmF1bHRfc2l6ZQogICAgICAgIGVsc2UgWwogICAgICAgICAgICBzdHJ1Y3QudW5wYWNrKCI+SSIsIHN0c3pbMTIgKyBpbmRleCAqIDQgOiAxNiArIGluZGV4ICogNF0pWzBdCiAgICAgICAgICAgIGZvciBpbmRleCBpbiByYW5nZShzYW1wbGVfY291bnQpCiAgICAgICAgXQogICAgKQogICAgY2h1bmtfdGFibGUgPSBzdGNvIGlmIHN0Y28gaXMgbm90IE5vbmUgZWxzZSBjbzY0CiAgICBhc3NlcnQgY2h1bmtfdGFibGUgaXMgbm90IE5vbmUKICAgIGNodW5rX2NvdW50ID0gc3RydWN0LnVucGFjaygiPkkiLCBjaHVua190YWJsZVs0OjhdKVswXQogICAgY2h1bmtfd2lkdGggPSA0IGlmIHN0Y28gaXMgbm90IE5vbmUgZWxzZSA4CiAgICBvZmZzZXRzID0gWwogICAgICAgIGludC5mcm9tX2J5dGVzKAogICAgICAgICAgICBjaHVua190YWJsZVsKICAgICAgICAgICAgICAgIDggKyBpbmRleCAqIGNodW5rX3dpZHRoIDogOCArIChpbmRleCArIDEpICogY2h1bmtfd2lkdGgKICAgICAgICAgICAgXSwKICAgICAgICAgICAgImJpZyIsCiAgICAgICAgKQogICAgICAgIGZvciBpbmRleCBpbiByYW5nZShjaHVua19jb3VudCkKICAgIF0KICAgIGVudHJ5X2NvdW50ID0gc3RydWN0LnVucGFjaygiPkkiLCBzdHNjWzQ6OF0pWzBdCiAgICBlbnRyaWVzID0gWwogICAgICAgICgKICAgICAgICAgICAgc3RydWN0LnVucGFjaygiPkkiLCBzdHNjWzggKyBpbmRleCAqIDEyIDogMTIgKyBpbmRleCAqIDEyXSlbMF0sCiAgICAgICAgICAgIHN0cnVjdC51bnBhY2soIj5JIiwgc3RzY1sxMiArIGluZGV4ICogMTIgOiAxNiArIGluZGV4ICogMTJdKVswXSwKICAgICAgICApCiAgICAgICAgZm9yIGluZGV4IGluIHJhbmdlKGVudHJ5X2NvdW50KQogICAgXQogICAgY2h1bmtfc2FtcGxlcyA9IFswXSAqIGNodW5rX2NvdW50CiAgICBmb3IgaW5kZXgsIChmaXJzdF9jaHVuaywgc2FtcGxlc19wZXJfY2h1bmspIGluIGVudW1lcmF0ZShlbnRyaWVzKToKICAgICAgICBlbmQgPSBlbnRyaWVzW2luZGV4ICsgMV1bMF0gLSAxIGlmIGluZGV4ICsgMSA8IGxlbihlbnRyaWVzKSBlbHNlIGNodW5rX2NvdW50CiAgICAgICAgZm9yIGNodW5rIGluIHJhbmdlKGZpcnN0X2NodW5rIC0gMSwgbWluKGVuZCwgY2h1bmtfY291bnQpKToKICAgICAgICAgICAgY2h1bmtfc2FtcGxlc1tjaHVua10gPSBzYW1wbGVzX3Blcl9jaHVuawogICAgc2Fpel9mbGFncyA9IGludC5mcm9tX2J5dGVzKHNhaXpbMTo0XSwgImJpZyIpCiAgICBzYWl6X2N1cnNvciA9IDEyIGlmIHNhaXpfZmxhZ3MgJiAxIGVsc2UgNAogICAgaWYgbGVuKHNhaXopIDwgc2Fpel9jdXJzb3IgKyA1OgogICAgICAgIHJldHVybiBOb25lCiAgICBkZWZhdWx0X2F1eF9zaXplID0gc2FpeltzYWl6X2N1cnNvcl0KICAgIGF1eF9jb3VudCA9IHN0cnVjdC51bnBhY2soIj5JIiwgc2FpeltzYWl6X2N1cnNvciArIDEgOiBzYWl6X2N1cnNvciArIDVdKVswXQogICAgYXV4X3NpemVzID0gKAogICAgICAgIFtkZWZhdWx0X2F1eF9zaXplXSAqIGF1eF9jb3VudAogICAgICAgIGlmIGRlZmF1bHRfYXV4X3NpemUKICAgICAgICBlbHNlIFsKICAgICAgICAgICAgaW50KHNhaXpbc2Fpel9jdXJzb3IgKyA1ICsgaW5kZXhdKQogICAgICAgICAgICBmb3IgaW5kZXggaW4gcmFuZ2UoYXV4X2NvdW50KQogICAgICAgICAgICBpZiBzYWl6X2N1cnNvciArIDUgKyBpbmRleCA8IGxlbihzYWl6KQogICAgICAgIF0KICAgICkKICAgIGlmIGxlbihhdXhfc2l6ZXMpICE9IGF1eF9jb3VudDoKICAgICAgICByZXR1cm4gTm9uZQogICAgc2Fpb19mbGFncyA9IGludC5mcm9tX2J5dGVzKHNhaW9bMTo0XSwgImJpZyIpCiAgICBzYWlvX2N1cnNvciA9IDEyIGlmIHNhaW9fZmxhZ3MgJiAxIGVsc2UgNAogICAgb2Zmc2V0X3dpZHRoID0gOCBpZiBzYWlvWzBdID09IDEgZWxzZSA0CiAgICBpZiBsZW4oc2FpbykgPCBzYWlvX2N1cnNvciArIDQgKyBvZmZzZXRfd2lkdGg6CiAgICAgICAgcmV0dXJuIE5vbmUKICAgIGVudHJ5X2NvdW50ID0gaW50LmZyb21fYnl0ZXMoc2Fpb1tzYWlvX2N1cnNvciA6IHNhaW9fY3Vyc29yICsgNF0sICJiaWciKQogICAgaWYgZW50cnlfY291bnQgPCAxOgogICAgICAgIHJldHVybiBOb25lCiAgICBhdXhfb2Zmc2V0ID0gaW50LmZyb21fYnl0ZXMoCiAgICAgICAgc2Fpb1tzYWlvX2N1cnNvciArIDQgOiBzYWlvX2N1cnNvciArIDQgKyBvZmZzZXRfd2lkdGhdLAogICAgICAgICJiaWciLAogICAgKQogICAgcmV0dXJuIHNpemVzLCBvZmZzZXRzLCBjaHVua19zYW1wbGVzLCBhdXhfc2l6ZXMsIGF1eF9vZmZzZXQsIHNhbXBsZV9jb3VudAoKZGVmIF9yZXBsYWNlX2ZvdXJjYyhkYXRhOiBieXRlYXJyYXksIG9sZDogYnl0ZXMsIG5ldzogYnl0ZXMpIC0+IE5vbmU6CiAgICBwb3NpdGlvbiA9IDAKICAgIHdoaWxlIFRydWU6CiAgICAgICAgcG9zaXRpb24gPSBkYXRhLmZpbmQob2xkLCBwb3NpdGlvbikKICAgICAgICBpZiBwb3NpdGlvbiA8IDA6CiAgICAgICAgICAgIHJldHVybgogICAgICAgIGRhdGFbcG9zaXRpb24gOiBwb3NpdGlvbiArIGxlbihvbGQpXSA9IG5ldwogICAgICAgIHBvc2l0aW9uICs9IGxlbihuZXcpCgpkZWYgX3JlcGxhY2Vfc2luZihkYXRhOiBieXRlYXJyYXkpIC0+IE5vbmU6CiAgICBwb3NpdGlvbiA9IDAKICAgIHdoaWxlIFRydWU6CiAgICAgICAgcG9zaXRpb24gPSBkYXRhLmZpbmQoYiJzaW5mIiwgcG9zaXRpb24pCiAgICAgICAgaWYgcG9zaXRpb24gPCAwOgogICAgICAgICAgICByZXR1cm4KICAgICAgICBpZiBwb3NpdGlvbiA+PSA0OgogICAgICAgICAgICBzaXplID0gc3RydWN0LnVucGFjaygiPkkiLCBkYXRhW3Bvc2l0aW9uIC0gNCA6IHBvc2l0aW9uXSlbMF0KICAgICAgICAgICAgZW5kID0gcG9zaXRpb24gLSA0ICsgc2l6ZQogICAgICAgICAgICBpZiA4IDw9IHNpemUgPCA1MF8wMDAgYW5kIGVuZCA8PSBsZW4oZGF0YSk6CiAgICAgICAgICAgICAgICBkYXRhW3Bvc2l0aW9uIDogcG9zaXRpb24gKyA0XSA9IGIiZnJlZSIKICAgICAgICAgICAgICAgIGRhdGFbcG9zaXRpb24gKyA0IDogZW5kXSA9IGIiXHgwMCIgKiBtYXgoMCwgZW5kIC0gcG9zaXRpb24gLSA0KQogICAgICAgICAgICAgICAgcG9zaXRpb24gPSBlbmQKICAgICAgICAgICAgICAgIGNvbnRpbnVlCiAgICAgICAgcG9zaXRpb24gKz0gNAoKZGVmIGRlY3J5cHRfbXA0X2NlbmMoZGF0YTogYnl0ZXMsIGNvbnRlbnRfa2V5OiBieXRlcykgLT4gYnl0ZXM6CiAgICBpZiBsZW4oY29udGVudF9rZXkpICE9IDE2OgogICAgICAgIHJhaXNlIEhvbmdndW9QbHVnaW5FcnJvcigiQ0VOQyDlr4bpkqXplb/luqbplJnor68iKQogICAgcmVzdWx0ID0gYnl0ZWFycmF5KGRhdGEpCiAgICBpZiBsZW4ocmVzdWx0KSA8IDE2OgogICAgICAgIHJhaXNlIEhvbmdndW9QbHVnaW5FcnJvcigiTVA0IOaVsOaNrui/h+efrSIpCiAgICBtb292X3N0YXJ0LCBtb292X3NpemUgPSBfZmluZF9ib3gobWVtb3J5dmlldyhyZXN1bHQpLCBiIm1vb3YiLCAwKQogICAgaWYgbW9vdl9zdGFydCA8IDAgb3IgbW9vdl9zaXplIDwgODoKICAgICAgICByYWlzZSBIb25nZ3VvUGx1Z2luRXJyb3IoIk1QNCBtb292IOi2iueVjCIpCiAgICBtb292ID0gbWVtb3J5dmlldyhyZXN1bHQpW21vb3Zfc3RhcnQgOiBtb292X3N0YXJ0ICsgbW9vdl9zaXplXQogICAgdHJhY2tzOiBsaXN0W2ludF0gPSBbXQogICAgdHJhY2tfc2VhcmNoID0gMAogICAgd2hpbGUgVHJ1ZToKICAgICAgICB0cmFjaywgdHJhY2tfc2l6ZSA9IF9maW5kX2JveChtb292LCBiInRyYWsiLCB0cmFja19zZWFyY2gpCiAgICAgICAgaWYgdHJhY2sgPCAwOgogICAgICAgICAgICBicmVhawogICAgICAgIHRyYWNrcy5hcHBlbmQodHJhY2spCiAgICAgICAgdHJhY2tfc2VhcmNoID0gdHJhY2sgKyBtYXgodHJhY2tfc2l6ZSwgOCkKICAgIGRlY3J5cHRlZF9zYW1wbGVzID0gMAogICAgZm9yIHRyYWNrIGluIHRyYWNrczoKICAgICAgICBwYXJzZWQgPSBfcGFyc2VfdHJhY2sobW9vdiwgdHJhY2spCiAgICAgICAgaWYgcGFyc2VkIGlzIE5vbmU6CiAgICAgICAgICAgIGNvbnRpbnVlCiAgICAgICAgc2l6ZXMsIG9mZnNldHMsIGNodW5rX2NvdW50cywgYXV4X3NpemVzLCBhdXhfb2Zmc2V0LCBzYW1wbGVfY291bnQgPSBwYXJzZWQKICAgICAgICBhdXhfc2l6ZSA9IHN1bShtYXgoc2l6ZSwgOCkgZm9yIHNpemUgaW4gYXV4X3NpemVzKQogICAgICAgIGlmIG5vdCBzYW1wbGVfY291bnQgb3IgYXV4X29mZnNldCA8IDAgb3IgYXV4X29mZnNldCArIGF1eF9zaXplID4gbGVuKHJlc3VsdCk6CiAgICAgICAgICAgIGNvbnRpbnVlCiAgICAgICAgYXV4ID0gcmVzdWx0W2F1eF9vZmZzZXQgOiBhdXhfb2Zmc2V0ICsgYXV4X3NpemVdCiAgICAgICAgc2FtcGxlX2luZGV4ID0gMAogICAgICAgIGF1eF9pbmRleCA9IDAKICAgICAgICBmb3IgY2h1bmtfaW5kZXgsIGNodW5rX29mZnNldCBpbiBlbnVtZXJhdGUob2Zmc2V0cyk6CiAgICAgICAgICAgIGN1cnJlbnQgPSBjaHVua19vZmZzZXQKICAgICAgICAgICAgZm9yIF8gaW4gcmFuZ2UoY2h1bmtfY291bnRzW2NodW5rX2luZGV4XSk6CiAgICAgICAgICAgICAgICBpZiBzYW1wbGVfaW5kZXggPj0gc2FtcGxlX2NvdW50IG9yIHNhbXBsZV9pbmRleCA+PSBsZW4oc2l6ZXMpOgogICAgICAgICAgICAgICAgICAgIGJyZWFrCiAgICAgICAgICAgICAgICBzaXplID0gc2l6ZXNbc2FtcGxlX2luZGV4XQogICAgICAgICAgICAgICAgaWYgY3VycmVudCArIHNpemUgPiBsZW4ocmVzdWx0KToKICAgICAgICAgICAgICAgICAgICByYWlzZSBIb25nZ3VvUGx1Z2luRXJyb3IoIk1QNCDmoLfmnKzotornlYwiKQogICAgICAgICAgICAgICAgaWYgc2FtcGxlX2luZGV4ID49IGxlbihhdXhfc2l6ZXMpOgogICAgICAgICAgICAgICAgICAgIHJhaXNlIEhvbmdndW9QbHVnaW5FcnJvcigiTVA0IOi+heWKqeS/oeaBr+aVsOmHj+S4jei2syIpCiAgICAgICAgICAgICAgICBlbnRyeV9zaXplID0gbWF4KGF1eF9zaXplc1tzYW1wbGVfaW5kZXhdLCA4KQogICAgICAgICAgICAgICAgaXYgPSBieXRlcyhhdXhbYXV4X2luZGV4IDogYXV4X2luZGV4ICsgbWluKGVudHJ5X3NpemUsIDgpXSkubGp1c3QoCiAgICAgICAgICAgICAgICAgICAgOCwgYiJcMCIKICAgICAgICAgICAgICAgICkgKyBiIlwwIiAqIDgKICAgICAgICAgICAgICAgIHJlc3VsdFtjdXJyZW50IDogY3VycmVudCArIHNpemVdID0gX2Flc19jdHJfZGVjcnlwdCgKICAgICAgICAgICAgICAgICAgICBjb250ZW50X2tleSwgaXYsIGJ5dGVzKHJlc3VsdFtjdXJyZW50IDogY3VycmVudCArIHNpemVdKQogICAgICAgICAgICAgICAgKQogICAgICAgICAgICAgICAgY3VycmVudCArPSBzaXplCiAgICAgICAgICAgICAgICBzYW1wbGVfaW5kZXggKz0gMQogICAgICAgICAgICAgICAgYXV4X2luZGV4ICs9IGVudHJ5X3NpemUKICAgICAgICAgICAgICAgIGRlY3J5cHRlZF9zYW1wbGVzICs9IDEKICAgIGlmIG5vdCBkZWNyeXB0ZWRfc2FtcGxlczoKICAgICAgICByYWlzZSBIb25nZ3VvUGx1Z2luRXJyb3IoIk1QNCDmsqHmnInlj6/op6Plr4bnmoQgQ0VOQyDmoLfmnKwiKQogICAgbW9vdl9idWZmZXIgPSBieXRlYXJyYXkocmVzdWx0W21vb3Zfc3RhcnQgOiBtb292X3N0YXJ0ICsgbW9vdl9zaXplXSkKICAgIF9yZXN0b3JlX2NlbmNfY29kZWNzKG1vb3ZfYnVmZmVyKQogICAgX3JlcGxhY2Vfc2luZihtb292X2J1ZmZlcikKICAgIHJlc3VsdFttb292X3N0YXJ0IDogbW9vdl9zdGFydCArIG1vb3Zfc2l6ZV0gPSBtb292X2J1ZmZlcgogICAgcmV0dXJuIGJ5dGVzKHJlc3VsdCkKCk1FRElBX0hFQURFUlMgPSB7IlVzZXItQWdlbnQiOiBNRURJQV9VQSwgIlJlZmVyZXIiOiAiaHR0cHM6Ly9ub3ZlbC5zbnNzZGsuY29tLyJ9CgpfU1RSRUFNX1BPUlRfUkFOR0UgPSAoOTk5MCwgMTAwMDApCl9TVFJFQU1fQ0hVTksgPSAxIDw8IDIwCl9TVFJFQU1fSEVBRF9QUk9CRSA9IDEgPDwgMTYKX1NUUkVBTV9UVExfU0VDT05EUyA9IDkwMApfU1RSRUFNX01BWF9TRVNTSU9OUyA9IDQKX1NUUkVBTV9TVEFURTogZGljdFtzdHIsIEFueV0gPSB7InBvcnQiOiAwLCAic2VydmVyIjogTm9uZSwgInNlc3Npb25zIjoge319Cl9TVFJFQU1fTE9DSyA9IHRocmVhZGluZy5STG9jaygpCgoKZGVmIF90b3BsZXZlbF9ib3hlcyhidWY6IGJ5dGVzKSAtPiBsaXN0W3R1cGxlW2ludCwgaW50LCBieXRlc11dOgogICAgYm94ZXM6IGxpc3RbdHVwbGVbaW50LCBpbnQsIGJ5dGVzXV0gPSBbXQogICAgY3Vyc29yID0gMAogICAgd2hpbGUgY3Vyc29yICsgOCA8PSBsZW4oYnVmKToKICAgICAgICBzaXplID0gc3RydWN0LnVucGFjaygiPkkiLCBidWZbY3Vyc29yIDogY3Vyc29yICsgNF0pWzBdCiAgICAgICAgZm91cmNjID0gYnl0ZXMoYnVmW2N1cnNvciArIDQgOiBjdXJzb3IgKyA4XSkKICAgICAgICBpZiBzaXplID09IDE6CiAgICAgICAgICAgIGlmIGN1cnNvciArIDE2ID4gbGVuKGJ1Zik6CiAgICAgICAgICAgICAgICBicmVhawogICAgICAgICAgICBzaXplID0gc3RydWN0LnVucGFjaygiPlEiLCBidWZbY3Vyc29yICsgOCA6IGN1cnNvciArIDE2XSlbMF0KICAgICAgICBpZiBzaXplIDwgODoKICAgICAgICAgICAgYnJlYWsKICAgICAgICBib3hlcy5hcHBlbmQoKGN1cnNvciwgc2l6ZSwgZm91cmNjKSkKICAgICAgICBjdXJzb3IgKz0gc2l6ZQogICAgcmV0dXJuIGJveGVzCgoKZGVmIF9yYW5nZV9nZXQodXJsOiBzdHIsIHN0YXJ0OiBpbnQsIGVuZDogaW50KSAtPiB0dXBsZVtieXRlcywgaW50XToKICAgIGhlYWRlcnMgPSBkaWN0KE1FRElBX0hFQURFUlMpCiAgICBoZWFkZXJzWyJSYW5nZSJdID0gImJ5dGVzPSVkLSVkIiAlIChzdGFydCwgZW5kKQogICAgZXhwZWN0ZWQgPSBlbmQgLSBzdGFydCArIDEKICAgIGxhc3RfZXJyb3I6IEV4Y2VwdGlvbiB8IE5vbmUgPSBOb25lCiAgICBmb3IgYXR0ZW1wdCBpbiByYW5nZShfUkFOR0VfRkVUQ0hfQVRURU1QVFMpOgogICAgICAgIGlmIGF0dGVtcHQ6CiAgICAgICAgICAgIHRpbWUuc2xlZXAoX1JBTkdFX0ZFVENIX0JBQ0tPRkZfU0VDT05EUyAqIGF0dGVtcHQpCiAgICAgICAgdHJ5OgogICAgICAgICAgICByZXNwb25zZSA9IHJlcXVlc3RzLmdldCh1cmwsIGhlYWRlcnM9aGVhZGVycywgdGltZW91dD02MCkKICAgICAgICBleGNlcHQgcmVxdWVzdHMuUmVxdWVzdEV4Y2VwdGlvbiBhcyBlcnJvcjoKICAgICAgICAgICAgbGFzdF9lcnJvciA9IGVycm9yCiAgICAgICAgICAgIGNvbnRpbnVlCiAgICAgICAgaWYgcmVzcG9uc2Uuc3RhdHVzX2NvZGUgbm90IGluICgyMDAsIDIwNik6CiAgICAgICAgICAgIGxhc3RfZXJyb3IgPSBIb25nZ3VvUGx1Z2luRXJyb3IoCiAgICAgICAgICAgICAgICAi5aqS5L2T5YiG54mH6K+35rGC5aSx6LSlICVzIiAlIHJlc3BvbnNlLnN0YXR1c19jb2RlCiAgICAgICAgICAgICkKICAgICAgICAgICAgY29udGludWUKICAgICAgICBib2R5ID0gcmVzcG9uc2UuY29udGVudAogICAgICAgICMg5LiK5ri45YG25Y+R6L+U5Zue55+t5YyF77yb55+t5LqO6K+35rGC6ZW/5bqm5pe26YeN6K+V77yM6YG/5YWN5pKt5pS+5Zmo5pS25Yiw5oiq5pat5pWw5o2u44CCCiAgICAgICAgaWYgbm90IGJvZHkgb3IgKHJlc3BvbnNlLnN0YXR1c19jb2RlID09IDIwNiBhbmQgbGVuKGJvZHkpIDwgZXhwZWN0ZWQpOgogICAgICAgICAgICBsYXN0X2Vycm9yID0gSG9uZ2d1b1BsdWdpbkVycm9yKAogICAgICAgICAgICAgICAgIuWqkuS9k+WIhueJh+mVv+W6puS4jei2syAlZC8lZCIgJSAobGVuKGJvZHkpLCBleHBlY3RlZCkKICAgICAgICAgICAgKQogICAgICAgICAgICBjb250aW51ZQogICAgICAgIHRvdGFsID0gMAogICAgICAgIGNvbnRlbnRfcmFuZ2UgPSByZXNwb25zZS5oZWFkZXJzLmdldCgiQ29udGVudC1SYW5nZSIpIG9yICIiCiAgICAgICAgaWYgIi8iIGluIGNvbnRlbnRfcmFuZ2U6CiAgICAgICAgICAgIHRhaWwgPSBjb250ZW50X3JhbmdlLnJzcGxpdCgiLyIsIDEpWzFdLnN0cmlwKCkKICAgICAgICAgICAgaWYgdGFpbC5pc2RpZ2l0KCk6CiAgICAgICAgICAgICAgICB0b3RhbCA9IGludCh0YWlsKQogICAgICAgIGlmIG5vdCB0b3RhbDoKICAgICAgICAgICAgbGVuZ3RoID0gcmVzcG9uc2UuaGVhZGVycy5nZXQoIkNvbnRlbnQtTGVuZ3RoIikgb3IgIiIKICAgICAgICAgICAgdG90YWwgPSBpbnQobGVuZ3RoKSBpZiBsZW5ndGguaXNkaWdpdCgpIGVsc2UgMAogICAgICAgIHJldHVybiBib2R5LCB0b3RhbAogICAgcmFpc2UgbGFzdF9lcnJvciBvciBIb25nZ3VvUGx1Z2luRXJyb3IoIuWqkuS9k+WIhueJh+ivt+axguWksei0pSIpCgoKZGVmIF9mZXRjaF9tb292KHVybDogc3RyKSAtPiB0dXBsZVtpbnQsIGludCwgYnl0ZXNdOgogICAgcHJvYmUsIHRvdGFsID0gX3JhbmdlX2dldCh1cmwsIDAsIF9TVFJFQU1fSEVBRF9QUk9CRSAtIDEpCiAgICBpZiBub3QgdG90YWw6CiAgICAgICAgcmFpc2UgSG9uZ2d1b1BsdWdpbkVycm9yKCLlqpLkvZPmgLvplb/luqbmnKrnn6UiKQogICAgbW9vdl9zdGFydCA9IDAKICAgIG1vb3Zfc2l6ZSA9IDAKICAgIGZvciBvZmZzZXQsIHNpemUsIGZvdXJjYyBpbiBfdG9wbGV2ZWxfYm94ZXMocHJvYmUpOgogICAgICAgIGlmIGZvdXJjYyA9PSBiIm1vb3YiOgogICAgICAgICAgICBtb292X3N0YXJ0ID0gb2Zmc2V0CiAgICAgICAgICAgIG1vb3Zfc2l6ZSA9IHNpemUKICAgICAgICAgICAgYnJlYWsKICAgIGlmIG5vdCBtb292X3NpemU6CiAgICAgICAgcmFpc2UgSG9uZ2d1b1BsdWdpbkVycm9yKCLmnKrmib7liLAgbW9vdiDpobblsYLnm5IiKQogICAgaWYgbW9vdl9zdGFydCArIG1vb3Zfc2l6ZSA+IHRvdGFsOgogICAgICAgIHJhaXNlIEhvbmdndW9QbHVnaW5FcnJvcigibW9vdiDotornlYwiKQogICAgaWYgbW9vdl9zdGFydCArIG1vb3Zfc2l6ZSA8PSBsZW4ocHJvYmUpOgogICAgICAgIHJldHVybiB0b3RhbCwgbW9vdl9zdGFydCwgYnl0ZXMocHJvYmVbbW9vdl9zdGFydCA6IG1vb3Zfc3RhcnQgKyBtb292X3NpemVdKQogICAgbW9vdiwgXyA9IF9yYW5nZV9nZXQodXJsLCBtb292X3N0YXJ0LCBtb292X3N0YXJ0ICsgbW9vdl9zaXplIC0gMSkKICAgIGlmIGxlbihtb292KSAhPSBtb292X3NpemU6CiAgICAgICAgcmFpc2UgSG9uZ2d1b1BsdWdpbkVycm9yKCJtb292IOWIhueJh+mVv+W6puS4jeespiIpCiAgICByZXR1cm4gdG90YWwsIG1vb3Zfc3RhcnQsIG1vb3YKCgpkZWYgX29yaWdpbmFsX2Zvcm1hdF9uZWFyKGRhdGE6IGJ5dGVhcnJheSwgZW50cnlfcG9zOiBpbnQsIGRlZmF1bHQ6IGJ5dGVzKSAtPiBieXRlczoKICAgICIiIuS7jiBzYW1wbGUgZW50cnkg5ZCO55qEIHNpbmYvZnJtYSDor7vlj5bljp/lp4vlm5vlrZfnrKbnoIHvvIhhdmMxL2h2YzEvbXA0YSDnrYnvvInjgIIiIiIKICAgIGJsb2IgPSBieXRlcyhkYXRhW2VudHJ5X3BvcyA6IG1pbihsZW4oZGF0YSksIGVudHJ5X3BvcyArIDgwMCldKQogICAgaWR4ID0gMAogICAgd2hpbGUgVHJ1ZToKICAgICAgICBwb3MgPSBibG9iLmZpbmQoYiJmcm1hIiwgaWR4KQogICAgICAgIGlmIHBvcyA8IDA6CiAgICAgICAgICAgIHJldHVybiBkZWZhdWx0CiAgICAgICAgaWYgcG9zICsgOCA8PSBsZW4oYmxvYik6CiAgICAgICAgICAgIGZtdCA9IGJ5dGVzKGJsb2JbcG9zICsgNCA6IHBvcyArIDhdKQogICAgICAgICAgICBpZiBmbXQgbm90IGluIChiIiIsIGIiXHgwMFx4MDBceDAwXHgwMCIsIGIiZW5jdiIsIGIiZW5jYSIpIGFuZCBhbGwoMzIgPD0gYyA8IDEyNyBmb3IgYyBpbiBmbXQpOgogICAgICAgICAgICAgICAgcmV0dXJuIGZtdAogICAgICAgIGlkeCA9IHBvcyArIDQKCgpkZWYgX3Jlc3RvcmVfY2VuY19jb2RlY3MoZGF0YTogYnl0ZWFycmF5KSAtPiBOb25lOgogICAgIiIi5oqKIGVuY3YvZW5jYSDov5jljp/kuLogZnJtYSDkuK3nmoTnnJ/lrp7nvJbnoIHvvIzpgb/lhY3kuIDlvovmlLnmiJAgaHZjMSDlr7zoh7Tlj6rmnInlo7Dpn7PjgIIiIiIKICAgIHBvcyA9IDAKICAgIHdoaWxlIFRydWU6CiAgICAgICAgcG9zID0gZGF0YS5maW5kKGIiZW5jdiIsIHBvcykKICAgICAgICBpZiBwb3MgPCAwOgogICAgICAgICAgICBicmVhawogICAgICAgIGRhdGFbcG9zIDogcG9zICsgNF0gPSBfb3JpZ2luYWxfZm9ybWF0X25lYXIoZGF0YSwgcG9zLCBiImF2YzEiKQogICAgICAgIHBvcyArPSA0CiAgICBwb3MgPSAwCiAgICB3aGlsZSBUcnVlOgogICAgICAgIHBvcyA9IGRhdGEuZmluZChiImVuY2EiLCBwb3MpCiAgICAgICAgaWYgcG9zIDwgMDoKICAgICAgICAgICAgYnJlYWsKICAgICAgICBkYXRhW3BvcyA6IHBvcyArIDRdID0gX29yaWdpbmFsX2Zvcm1hdF9uZWFyKGRhdGEsIHBvcywgYiJtcDRhIikKICAgICAgICBwb3MgKz0gNAoKCmRlZiBfcmV3cml0ZV9tb292KG1vb3Y6IGJ5dGVzKSAtPiBieXRlczoKICAgIHJlc3VsdCA9IGJ5dGVhcnJheShtb292KQogICAgX3Jlc3RvcmVfY2VuY19jb2RlY3MocmVzdWx0KQogICAgX3JlcGxhY2Vfc2luZihyZXN1bHQpCiAgICByZXR1cm4gYnl0ZXMocmVzdWx0KQoKCmRlZiBfc2FtcGxlX3RhYmxlKG1vb3Y6IGJ5dGVzLCBtb292X3N0YXJ0OiBpbnQpIC0+IGxpc3RbdHVwbGVbaW50LCBpbnQsIGJ5dGVzXV06CiAgICB2aWV3ID0gbWVtb3J5dmlldyhtb292KQogICAgc2FtcGxlczogbGlzdFt0dXBsZVtpbnQsIGludCwgYnl0ZXNdXSA9IFtdCiAgICB0cmFja19zZWFyY2ggPSAwCiAgICB3aGlsZSBUcnVlOgogICAgICAgIHRyYWNrLCB0cmFja19zaXplID0gX2ZpbmRfYm94KHZpZXcsIGIidHJhayIsIHRyYWNrX3NlYXJjaCkKICAgICAgICBpZiB0cmFjayA8IDA6CiAgICAgICAgICAgIGJyZWFrCiAgICAgICAgdHJhY2tfc2VhcmNoID0gdHJhY2sgKyBtYXgodHJhY2tfc2l6ZSwgOCkKICAgICAgICBwYXJzZWQgPSBfcGFyc2VfdHJhY2sodmlldywgdHJhY2spCiAgICAgICAgaWYgcGFyc2VkIGlzIE5vbmU6CiAgICAgICAgICAgIGNvbnRpbnVlCiAgICAgICAgc2l6ZXMsIG9mZnNldHMsIGNodW5rX2NvdW50cywgYXV4X3NpemVzLCBhdXhfb2Zmc2V0LCBzYW1wbGVfY291bnQgPSBwYXJzZWQKICAgICAgICBhdXhfbGVuZ3RoID0gc3VtKG1heChzaXplLCA4KSBmb3Igc2l6ZSBpbiBhdXhfc2l6ZXMpCiAgICAgICAgYXV4X2xvY2FsID0gYXV4X29mZnNldCAtIG1vb3Zfc3RhcnQKICAgICAgICBpZiBhdXhfbG9jYWwgPCAwIG9yIGF1eF9sb2NhbCArIGF1eF9sZW5ndGggPiBsZW4obW9vdik6CiAgICAgICAgICAgIHJhaXNlIEhvbmdndW9QbHVnaW5FcnJvcigiQ0VOQyDovoXliqnkv6Hmga/kuI3lnKggbW9vdiDlhoXvvIzml6Dms5XmtYHlvI/op6Plr4YiKQogICAgICAgIGF1eCA9IG1vb3ZbYXV4X2xvY2FsIDogYXV4X2xvY2FsICsgYXV4X2xlbmd0aF0KICAgICAgICBzYW1wbGVfaW5kZXggPSAwCiAgICAgICAgYXV4X2luZGV4ID0gMAogICAgICAgIGZvciBjaHVua19pbmRleCwgY2h1bmtfb2Zmc2V0IGluIGVudW1lcmF0ZShvZmZzZXRzKToKICAgICAgICAgICAgY3VycmVudCA9IGNodW5rX29mZnNldAogICAgICAgICAgICBmb3IgXyBpbiByYW5nZShjaHVua19jb3VudHNbY2h1bmtfaW5kZXhdKToKICAgICAgICAgICAgICAgIGlmIHNhbXBsZV9pbmRleCA+PSBzYW1wbGVfY291bnQgb3Igc2FtcGxlX2luZGV4ID49IGxlbihzaXplcyk6CiAgICAgICAgICAgICAgICAgICAgYnJlYWsKICAgICAgICAgICAgICAgIGlmIHNhbXBsZV9pbmRleCA+PSBsZW4oYXV4X3NpemVzKToKICAgICAgICAgICAgICAgICAgICByYWlzZSBIb25nZ3VvUGx1Z2luRXJyb3IoIkNFTkMg6L6F5Yqp5L+h5oGv5pWw6YeP5LiN6LazIikKICAgICAgICAgICAgICAgIGVudHJ5X3NpemUgPSBtYXgoYXV4X3NpemVzW3NhbXBsZV9pbmRleF0sIDgpCiAgICAgICAgICAgICAgICBpbml0aWFsX3ZlY3RvciA9IGJ5dGVzKAogICAgICAgICAgICAgICAgICAgIGF1eFthdXhfaW5kZXggOiBhdXhfaW5kZXggKyBtaW4oZW50cnlfc2l6ZSwgOCldCiAgICAgICAgICAgICAgICApLmxqdXN0KDgsIGIiXDAiKSArIGIiXDAiICogOAogICAgICAgICAgICAgICAgc2FtcGxlcy5hcHBlbmQoKGN1cnJlbnQsIHNpemVzW3NhbXBsZV9pbmRleF0sIGluaXRpYWxfdmVjdG9yKSkKICAgICAgICAgICAgICAgIGN1cnJlbnQgKz0gc2l6ZXNbc2FtcGxlX2luZGV4XQogICAgICAgICAgICAgICAgYXV4X2luZGV4ICs9IGVudHJ5X3NpemUKICAgICAgICAgICAgICAgIHNhbXBsZV9pbmRleCArPSAxCiAgICBpZiBub3Qgc2FtcGxlczoKICAgICAgICByYWlzZSBIb25nZ3VvUGx1Z2luRXJyb3IoIm1vb3Yg5Lit5rKh5pyJ5Y+v6Kej5a+G55qEIENFTkMg5qC35pysIikKICAgIHNhbXBsZXMuc29ydCgpCiAgICByZXR1cm4gc2FtcGxlcwoKCmNsYXNzIF9TdHJlYW1TZXNzaW9uOgogICAgIiIi5oyJIFJhbmdlIOmAkOWdl+aLieWPluWKoOWvhiBNUDTvvIzovrnkuIvovrnop6MgQ0VOQ++8jOS+m+acrOWcsOaSreaUvuWZqOebtOi/nuOAgiIiIgoKICAgIGRlZiBfX2luaXRfXygKICAgICAgICBzZWxmLAogICAgICAgIHVybDogc3RyLAogICAgICAgIGNvbnRlbnRfa2V5OiBieXRlcywKICAgICAgICB0b3RhbDogaW50LAogICAgICAgIG1vb3Zfc3RhcnQ6IGludCwKICAgICAgICBtb292OiBieXRlcywKICAgICkgLT4gTm9uZToKICAgICAgICBpZiBsZW4oY29udGVudF9rZXkpICE9IDE2OgogICAgICAgICAgICByYWlzZSBIb25nZ3VvUGx1Z2luRXJyb3IoIkNFTkMg5a+G6ZKl6ZW/5bqm6ZSZ6K+vIikKICAgICAgICBzZWxmLnVybCA9IHVybAogICAgICAgIHNlbGYuY29udGVudF9rZXkgPSBjb250ZW50X2tleQogICAgICAgIHNlbGYudG90YWwgPSB0b3RhbAogICAgICAgIHNlbGYubW9vdl9zdGFydCA9IG1vb3Zfc3RhcnQKICAgICAgICBzZWxmLm1vb3ZfcGxhaW4gPSBfcmV3cml0ZV9tb292KG1vb3YpCiAgICAgICAgc2VsZi5tb292X2VuZCA9IG1vb3Zfc3RhcnQgKyBsZW4obW9vdikKICAgICAgICBzZWxmLnNhbXBsZXMgPSBfc2FtcGxlX3RhYmxlKG1vb3YsIG1vb3Zfc3RhcnQpCiAgICAgICAgc2VsZi5vZmZzZXRzID0gW2l0ZW1bMF0gZm9yIGl0ZW0gaW4gc2VsZi5zYW1wbGVzXQogICAgICAgIHNlbGYuY3JlYXRlZCA9IHRpbWUudGltZSgpCgogICAgZGVmIGV4cGlyZWQoc2VsZikgLT4gYm9vbDoKICAgICAgICByZXR1cm4gdGltZS50aW1lKCkgLSBzZWxmLmNyZWF0ZWQgPiBfU1RSRUFNX1RUTF9TRUNPTkRTCgogICAgZGVmIF9wYXRjaChzZWxmLCBidWZmZXI6IGJ5dGVhcnJheSwgYmFzZTogaW50KSAtPiBOb25lOgogICAgICAgIGVuZCA9IGJhc2UgKyBsZW4oYnVmZmVyKSAtIDEKICAgICAgICBpbmRleCA9IG1heChiaXNlY3QuYmlzZWN0X3JpZ2h0KHNlbGYub2Zmc2V0cywgYmFzZSkgLSAxLCAwKQogICAgICAgIHdoaWxlIGluZGV4IDwgbGVuKHNlbGYuc2FtcGxlcyk6CiAgICAgICAgICAgIG9mZnNldCwgc2l6ZSwgaW5pdGlhbF92ZWN0b3IgPSBzZWxmLnNhbXBsZXNbaW5kZXhdCiAgICAgICAgICAgIGluZGV4ICs9IDEKICAgICAgICAgICAgaWYgb2Zmc2V0ID4gZW5kOgogICAgICAgICAgICAgICAgYnJlYWsKICAgICAgICAgICAgaWYgb2Zmc2V0ICsgc2l6ZSA8PSBiYXNlOgogICAgICAgICAgICAgICAgY29udGludWUKICAgICAgICAgICAgZmlyc3QgPSBtYXgob2Zmc2V0LCBiYXNlKQogICAgICAgICAgICBsYXN0ID0gbWluKG9mZnNldCArIHNpemUgLSAxLCBlbmQpCiAgICAgICAgICAgIHNraXAgPSBmaXJzdCAtIG9mZnNldAogICAgICAgICAgICBjb3VudGVyID0gKAogICAgICAgICAgICAgICAgKGludC5mcm9tX2J5dGVzKGluaXRpYWxfdmVjdG9yLCAiYmlnIikgKyBza2lwIC8vIDE2KQogICAgICAgICAgICAgICAgJiAoKDEgPDwgMTI4KSAtIDEpCiAgICAgICAgICAgICkudG9fYnl0ZXMoMTYsICJiaWciKQogICAgICAgICAgICBwYWRkaW5nID0gc2tpcCAlIDE2CiAgICAgICAgICAgIHBsYWluID0gX2Flc19jdHJfZGVjcnlwdCgKICAgICAgICAgICAgICAgIHNlbGYuY29udGVudF9rZXksCiAgICAgICAgICAgICAgICBjb3VudGVyLAogICAgICAgICAgICAgICAgYiJcMCIgKiBwYWRkaW5nICsgYnl0ZXMoYnVmZmVyW2ZpcnN0IC0gYmFzZSA6IGxhc3QgLSBiYXNlICsgMV0pLAogICAgICAgICAgICApCiAgICAgICAgICAgIGJ1ZmZlcltmaXJzdCAtIGJhc2UgOiBsYXN0IC0gYmFzZSArIDFdID0gcGxhaW5bcGFkZGluZzpdCiAgICAgICAgaWYgYmFzZSA8IHNlbGYubW9vdl9lbmQgYW5kIGVuZCA+PSBzZWxmLm1vb3Zfc3RhcnQ6CiAgICAgICAgICAgIGZpcnN0ID0gbWF4KGJhc2UsIHNlbGYubW9vdl9zdGFydCkKICAgICAgICAgICAgbGFzdCA9IG1pbihlbmQsIHNlbGYubW9vdl9lbmQgLSAxKQogICAgICAgICAgICBidWZmZXJbZmlyc3QgLSBiYXNlIDogbGFzdCAtIGJhc2UgKyAxXSA9IHNlbGYubW9vdl9wbGFpblsKICAgICAgICAgICAgICAgIGZpcnN0IC0gc2VsZi5tb292X3N0YXJ0IDogbGFzdCAtIHNlbGYubW9vdl9zdGFydCArIDEKICAgICAgICAgICAgXQoKICAgIGRlZiByZWFkX3JhbmdlKHNlbGYsIHN0YXJ0OiBpbnQsIGVuZDogaW50KSAtPiBieXRlczoKICAgICAgICByYXcsIF8gPSBfcmFuZ2VfZ2V0KHNlbGYudXJsLCBzdGFydCwgZW5kKQogICAgICAgIGlmIG5vdCByYXc6CiAgICAgICAgICAgIHJhaXNlIEhvbmdndW9QbHVnaW5FcnJvcigi5aqS5L2T5YiG54mH5Li656m6IikKICAgICAgICBidWZmZXIgPSBieXRlYXJyYXkocmF3KQogICAgICAgIHNlbGYuX3BhdGNoKGJ1ZmZlciwgc3RhcnQpCiAgICAgICAgcmV0dXJuIGJ5dGVzKGJ1ZmZlcikKCiAgICBkZWYgaXRlcl9yYW5nZShzZWxmLCBzdGFydDogaW50LCBlbmQ6IGludCk6CiAgICAgICAgY3Vyc29yID0gc3RhcnQKICAgICAgICB3aGlsZSBjdXJzb3IgPD0gZW5kOgogICAgICAgICAgICBzdG9wID0gbWluKGN1cnNvciArIF9TVFJFQU1fQ0hVTksgLSAxLCBlbmQpCiAgICAgICAgICAgIGJsb2NrID0gc2VsZi5yZWFkX3JhbmdlKGN1cnNvciwgc3RvcCkKICAgICAgICAgICAgeWllbGQgYmxvY2sKICAgICAgICAgICAgY3Vyc29yICs9IGxlbihibG9jaykKCgpkZWYgX3N0cmVhbV9zZXNzaW9uKHZpZGVvX2lkOiBzdHIsIGNvbmZpZzogTWFwcGluZ1tzdHIsIEFueV0sIHF1YWxpdHk6IHN0ciA9ICIxMDgwIikgLT4gIl9TdHJlYW1TZXNzaW9uIjoKICAgIHF1YWxpdHkgPSBxdWFsaXR5IGlmIHF1YWxpdHkgaW4gX1FVQUxJVFlfTElORV9OQU1FX1RPX1EgZWxzZSAiMTA4MCIKICAgIGNhY2hlX2tleSA9ICIlc3wlcyIgJSAodmlkZW9faWQsIHF1YWxpdHkpCiAgICB3aXRoIF9TVFJFQU1fTE9DSzoKICAgICAgICBzZXNzaW9ucyA9IF9TVFJFQU1fU1RBVEVbInNlc3Npb25zIl0KICAgICAgICBmb3Iga2V5IGluIFtrZXkgZm9yIGtleSwgaXRlbSBpbiBzZXNzaW9ucy5pdGVtcygpIGlmIGl0ZW0uZXhwaXJlZCgpXToKICAgICAgICAgICAgc2Vzc2lvbnMucG9wKGtleSwgTm9uZSkKICAgICAgICBzZXNzaW9uID0gc2Vzc2lvbnMuZ2V0KGNhY2hlX2tleSkKICAgIGlmIHNlc3Npb24gaXMgbm90IE5vbmU6CiAgICAgICAgcmV0dXJuIHNlc3Npb24KICAgIG1vZGVsID0gTm9uZQogICAgcm93cyA9IE5vbmUKICAgIGxhc3RfZXJyOiBBbnkgPSBOb25lCiAgICBmb3IgX2Rldl9pZHgsIChfZGlkLCBfaWlkKSBpbiBlbnVtZXJhdGUoX2RldmljZV9jYW5kaWRhdGVzKGNvbmZpZywgMykpOgogICAgICAgIHRyeToKICAgICAgICAgICAgbW9kZWwgPSBfdmlkZW9fbW9kZWwodmlkZW9faWQsIHsiZGV2aWNlX2lkIjogX2RpZCwKICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAiaW5zdGFsbF9pZCI6IF9paWR9KQogICAgICAgIGV4Y2VwdCBFeGNlcHRpb24gYXMgbW9kZWxfZXJyOgogICAgICAgICAgICBtb2RlbCwgcm93cyA9IE5vbmUsIE5vbmUKICAgICAgICAgICAgbGFzdF9lcnIgPSBtb2RlbF9lcnIKICAgICAgICAgICAgY29udGludWUKICAgICAgICByb3dzID0gX3ZpZGVvX2xpc3RfZnJvbV9tb2RlbChtb2RlbCkKICAgICAgICBpZiByb3dzOgogICAgICAgICAgICBicmVhawogICAgICAgIGxhc3RfZXJyID0gSG9uZ2d1b1BsdWdpbkVycm9yKCJ2aWRlb19saXN0IOS4uuepuu+8iOiuvuWkhyMlZO+8iSIgJSAoX2Rldl9pZHggKyAxKSkKICAgIGlmIG5vdCByb3dzOgogICAgICAgIHJhaXNlIEhvbmdndW9QbHVnaW5FcnJvcigi5pKt5pS+5qih5Z6L5Y+W5rWB5aSx6LSl77yaJXMiICUgbGFzdF9lcnIpCiAgICBfLCBpdGVtID0gX3NlbGVjdF9xdWFsaXR5KHJvd3MsIHF1YWxpdHkpCiAgICB1cmwgPSBfbWVkaWFfdXJsKGl0ZW0pCiAgICBzcGFkZSA9IF9zcGFkZV92YWx1ZShpdGVtKQogICAgaWYgbm90IHVybCBvciBub3Qgc3BhZGU6CiAgICAgICAgcmFpc2UgSG9uZ2d1b1BsdWdpbkVycm9yKCLmkq3mlL7mqKHlnovnvLrlsJHlnLDlnYDmiJblr4bpkqXmnZDmlpkiKQogICAga2V5X3NlZWQgPSBfa2V5X3NlZWRfZnJvbV9tb2RlbChtb2RlbCkKICAgIGlmIGtleV9zZWVkOgogICAgICAgIHRyeToKICAgICAgICAgICAgdXJsID0gX2RlY3J5cHRfc3BhZGVfdXJsKHVybCwga2V5X3NlZWQpCiAgICAgICAgZXhjZXB0IEhvbmdndW9QbHVnaW5FcnJvcjoKICAgICAgICAgICAgcGFzcwogICAgdG90YWwsIG1vb3Zfc3RhcnQsIG1vb3YgPSBfZmV0Y2hfbW9vdih1cmwpCiAgICBzZXNzaW9uID0gX1N0cmVhbVNlc3Npb24odXJsLCBkZXJpdmVfY29udGVudF9rZXkoc3BhZGUpLCB0b3RhbCwgbW9vdl9zdGFydCwgbW9vdikKICAgIHdpdGggX1NUUkVBTV9MT0NLOgogICAgICAgIHNlc3Npb25zID0gX1NUUkVBTV9TVEFURVsic2Vzc2lvbnMiXQogICAgICAgIHdoaWxlIGxlbihzZXNzaW9ucykgPj0gX1NUUkVBTV9NQVhfU0VTU0lPTlM6CiAgICAgICAgICAgIHNlc3Npb25zLnBvcChuZXh0KGl0ZXIoc2Vzc2lvbnMpKSwgTm9uZSkKICAgICAgICBzZXNzaW9uc1tjYWNoZV9rZXldID0gc2Vzc2lvbgogICAgcmV0dXJuIHNlc3Npb24KCgpfUkFOR0VfVU5TQVRJU0ZJQUJMRSA9ICJ1bnNhdGlzZmlhYmxlIgoKZGVmIF9wYXJzZV9yYW5nZSh2YWx1ZTogc3RyLCB0b3RhbDogaW50KSAtPiBBbnk6CiAgICAiIiLop6PmnpAgUmFuZ2Ug5aS044CC6L+U5ZueIChzdGFydCwgZW5kKeOAgU5vbmXvvIjlv73nlaXvvInmiJYgX1JBTkdFX1VOU0FUSVNGSUFCTEXjgIIiIiIKICAgIHRleHQgPSAodmFsdWUgb3IgIiIpLnN0cmlwKCkubG93ZXIoKQogICAgaWYgbm90IHRleHQuc3RhcnRzd2l0aCgiYnl0ZXM9Iik6CiAgICAgICAgcmV0dXJuIE5vbmUKICAgIHNwZWMgPSB0ZXh0WzY6XS5zcGxpdCgiLCIpWzBdLnN0cmlwKCkKICAgIGlmICItIiBub3QgaW4gc3BlYzoKICAgICAgICByZXR1cm4gTm9uZQogICAgbGVmdCwgcmlnaHQgPSBzcGVjLnNwbGl0KCItIiwgMSkKICAgIGlmIG5vdCBsZWZ0OgogICAgICAgIGlmIG5vdCByaWdodC5pc2RpZ2l0KCk6CiAgICAgICAgICAgIHJldHVybiBOb25lCiAgICAgICAgbGVuZ3RoID0gbWluKGludChyaWdodCksIHRvdGFsKQogICAgICAgIGlmIG5vdCBsZW5ndGg6CiAgICAgICAgICAgIHJldHVybiBfUkFOR0VfVU5TQVRJU0ZJQUJMRQogICAgICAgIHJldHVybiB0b3RhbCAtIGxlbmd0aCwgdG90YWwgLSAxCiAgICBpZiBub3QgbGVmdC5pc2RpZ2l0KCk6CiAgICAgICAgcmV0dXJuIE5vbmUKICAgIHN0YXJ0ID0gaW50KGxlZnQpCiAgICBlbmQgPSBpbnQocmlnaHQpIGlmIHJpZ2h0LmlzZGlnaXQoKSBlbHNlIHRvdGFsIC0gMQogICAgZW5kID0gbWluKGVuZCwgdG90YWwgLSAxKQogICAgaWYgc3RhcnQgPj0gdG90YWwgb3Igc3RhcnQgPiBlbmQ6CiAgICAgICAgcmV0dXJuIF9SQU5HRV9VTlNBVElTRklBQkxFCiAgICByZXR1cm4gc3RhcnQsIGVuZAoKCmNsYXNzIF9TdHJlYW1IYW5kbGVyKEJhc2VIVFRQUmVxdWVzdEhhbmRsZXIpOgogICAgcHJvdG9jb2xfdmVyc2lvbiA9ICJIVFRQLzEuMSIKICAgIHNlcnZlcl92ZXJzaW9uID0gImhnLXN0cmVhbSIKCiAgICBkZWYgbG9nX21lc3NhZ2Uoc2VsZiwgKmFyZ3M6IEFueSkgLT4gTm9uZToKICAgICAgICByZXR1cm4gTm9uZQoKICAgIGRlZiBfcGFyYW1zKHNlbGYpIC0+IGRpY3Rbc3RyLCBzdHJdOgogICAgICAgIHBhcnNlZCA9IHVybHBhcnNlKHNlbGYucGF0aCkKICAgICAgICBxdWVyeSA9IHBhcnNlX3FzKHBhcnNlZC5xdWVyeSkKICAgICAgICB2aWRlb19pZCA9IChxdWVyeS5nZXQoInZpZCIpIG9yIHF1ZXJ5LmdldCgiaWQiKSBvciBbIiJdKVswXQogICAgICAgIGlmIG5vdCB2aWRlb19pZDoKICAgICAgICAgICAgdmlkZW9faWQgPSBwYXJzZWQucGF0aC5yc3BsaXQoIi8iLCAxKVstMV0uc3BsaXQoIi4iKVswXQogICAgICAgIHJldHVybiB7CiAgICAgICAgICAgICJ2aWQiOiB2aWRlb19pZCBpZiB2aWRlb19pZC5pc2RpZ2l0KCkgZWxzZSAiIiwKICAgICAgICAgICAgInF1YWxpdHkiOiAocXVlcnkuZ2V0KCJxIikgb3IgWyIxMDgwIl0pWzBdLAogICAgICAgICAgICAiZGV2aWNlX2lkIjogKHF1ZXJ5LmdldCgiZGlkIikgb3IgWyIiXSlbMF0sCiAgICAgICAgICAgICJpbnN0YWxsX2lkIjogKHF1ZXJ5LmdldCgiaWlkIikgb3IgWyIiXSlbMF0sCiAgICAgICAgfQoKICAgIGRlZiBfZmFpbChzZWxmLCBjb2RlOiBpbnQsIG1lc3NhZ2U6IGJ5dGVzKSAtPiBOb25lOgogICAgICAgIHNlbGYuc2VuZF9yZXNwb25zZShjb2RlKQogICAgICAgIHNlbGYuc2VuZF9oZWFkZXIoIkNvbnRlbnQtVHlwZSIsICJ0ZXh0L3BsYWluOyBjaGFyc2V0PXV0Zi04IikKICAgICAgICBzZWxmLnNlbmRfaGVhZGVyKCJDb250ZW50LUxlbmd0aCIsIHN0cihsZW4obWVzc2FnZSkpKQogICAgICAgIHNlbGYuc2VuZF9oZWFkZXIoIkNvbm5lY3Rpb24iLCAiY2xvc2UiKQogICAgICAgIHNlbGYuZW5kX2hlYWRlcnMoKQogICAgICAgIHRyeToKICAgICAgICAgICAgc2VsZi53ZmlsZS53cml0ZShtZXNzYWdlKQogICAgICAgIGV4Y2VwdCBPU0Vycm9yOgogICAgICAgICAgICBwYXNzCgogICAgZGVmIGRvX0hFQUQoc2VsZikgLT4gTm9uZTogICMgbm9xYTogTjgwMiAtIOagh+WHhuW6k+Wbnuiwg+WRveWQjQogICAgICAgIHNlbGYuX3NlcnZlKGJvZHk9RmFsc2UpCgogICAgZGVmIGRvX0dFVChzZWxmKSAtPiBOb25lOiAgIyBub3FhOiBOODAyIC0g5qCH5YeG5bqT5Zue6LCD5ZG95ZCNCiAgICAgICAgc2VsZi5fc2VydmUoYm9keT1UcnVlKQoKICAgIGRlZiBfc2VydmUoc2VsZiwgYm9keTogYm9vbCkgLT4gTm9uZToKICAgICAgICByb3V0ZSA9IHVybHBhcnNlKHNlbGYucGF0aCkucGF0aAogICAgICAgIGlmIG5vdCByb3V0ZS5lbmRzd2l0aCgiLm1wNCIpOgogICAgICAgICAgICBzZWxmLl9mYWlsKDQwNCwgYiJub3QgZm91bmQiKQogICAgICAgICAgICByZXR1cm4KICAgICAgICBwYXJhbXMgPSBzZWxmLl9wYXJhbXMoKQogICAgICAgIGlmIG5vdCBwYXJhbXNbInZpZCJdOgogICAgICAgICAgICBzZWxmLl9mYWlsKDQwMCwgYiJtaXNzaW5nIHZpZCIpCiAgICAgICAgICAgIHJldHVybgogICAgICAgIHRyeToKICAgICAgICAgICAgc2Vzc2lvbiA9IF9zdHJlYW1fc2Vzc2lvbigKICAgICAgICAgICAgICAgIHBhcmFtc1sidmlkIl0sCiAgICAgICAgICAgICAgICB7CiAgICAgICAgICAgICAgICAgICAgImRldmljZV9pZCI6IHBhcmFtc1siZGV2aWNlX2lkIl0sCiAgICAgICAgICAgICAgICAgICAgImluc3RhbGxfaWQiOiBwYXJhbXNbImluc3RhbGxfaWQiXSwKICAgICAgICAgICAgICAgIH0sCiAgICAgICAgICAgICAgICBwYXJhbXNbInF1YWxpdHkiXSwKICAgICAgICAgICAgKQogICAgICAgIGV4Y2VwdCBFeGNlcHRpb246CiAgICAgICAgICAgIHNlbGYuX2ZhaWwoNTAyLCBiIm1lZGlhIHNlc3Npb24gZmFpbGVkIikKICAgICAgICAgICAgcmV0dXJuCiAgICAgICAgcmF3X3JhbmdlID0gc2VsZi5oZWFkZXJzLmdldCgiUmFuZ2UiKSBvciAiIgogICAgICAgIHJlcXVlc3RlZCA9IF9wYXJzZV9yYW5nZShyYXdfcmFuZ2UsIHNlc3Npb24udG90YWwpCiAgICAgICAgaWYgcmVxdWVzdGVkIGlzIF9SQU5HRV9VTlNBVElTRklBQkxFOgogICAgICAgICAgICBzZWxmLnNlbmRfcmVzcG9uc2UoNDE2KQogICAgICAgICAgICBzZWxmLnNlbmRfaGVhZGVyKCJDb250ZW50LVR5cGUiLCAidGV4dC9wbGFpbjsgY2hhcnNldD11dGYtOCIpCiAgICAgICAgICAgIHNlbGYuc2VuZF9oZWFkZXIoIkNvbnRlbnQtUmFuZ2UiLCAiYnl0ZXMgKi8lZCIgJSBzZXNzaW9uLnRvdGFsKQogICAgICAgICAgICBzZWxmLnNlbmRfaGVhZGVyKCJDb250ZW50LUxlbmd0aCIsICIwIikKICAgICAgICAgICAgc2VsZi5zZW5kX2hlYWRlcigiQ29ubmVjdGlvbiIsICJjbG9zZSIpCiAgICAgICAgICAgIHNlbGYuZW5kX2hlYWRlcnMoKQogICAgICAgICAgICByZXR1cm4KICAgICAgICBzdGFydCwgZW5kID0gcmVxdWVzdGVkIGlmIHJlcXVlc3RlZCBlbHNlICgwLCBzZXNzaW9uLnRvdGFsIC0gMSkKICAgICAgICBzZWxmLnNlbmRfcmVzcG9uc2UoMjA2IGlmIHJlcXVlc3RlZCBlbHNlIDIwMCkKICAgICAgICBzZWxmLnNlbmRfaGVhZGVyKCJDb250ZW50LVR5cGUiLCAidmlkZW8vbXA0IikKICAgICAgICBzZWxmLnNlbmRfaGVhZGVyKCJBY2NlcHQtUmFuZ2VzIiwgImJ5dGVzIikKICAgICAgICBzZWxmLnNlbmRfaGVhZGVyKCJDb250ZW50LUxlbmd0aCIsIHN0cihlbmQgLSBzdGFydCArIDEpKQogICAgICAgIGlmIHJlcXVlc3RlZDoKICAgICAgICAgICAgc2VsZi5zZW5kX2hlYWRlcigKICAgICAgICAgICAgICAgICJDb250ZW50LVJhbmdlIiwKICAgICAgICAgICAgICAgICJieXRlcyAlZC0lZC8lZCIgJSAoc3RhcnQsIGVuZCwgc2Vzc2lvbi50b3RhbCksCiAgICAgICAgICAgICkKICAgICAgICBzZWxmLmVuZF9oZWFkZXJzKCkKICAgICAgICBpZiBub3QgYm9keToKICAgICAgICAgICAgcmV0dXJuCiAgICAgICAgdHJ5OgogICAgICAgICAgICBmb3IgYmxvY2sgaW4gc2Vzc2lvbi5pdGVyX3JhbmdlKHN0YXJ0LCBlbmQpOgogICAgICAgICAgICAgICAgc2VsZi53ZmlsZS53cml0ZShibG9jaykKICAgICAgICBleGNlcHQgKEJyb2tlblBpcGVFcnJvciwgQ29ubmVjdGlvblJlc2V0RXJyb3IpOgogICAgICAgICAgICBzZWxmLmNsb3NlX2Nvbm5lY3Rpb24gPSBUcnVlCiAgICAgICAgZXhjZXB0IEV4Y2VwdGlvbjoKICAgICAgICAgICAgc2VsZi5jbG9zZV9jb25uZWN0aW9uID0gVHJ1ZQoKCmRlZiBfc3RhcnRfc3RyZWFtX3NlcnZlcigpIC0+IGludDoKICAgIHdpdGggX1NUUkVBTV9MT0NLOgogICAgICAgIGlmIF9TVFJFQU1fU1RBVEVbInBvcnQiXToKICAgICAgICAgICAgcmV0dXJuIGludChfU1RSRUFNX1NUQVRFWyJwb3J0Il0pCiAgICAgICAgZm9yIHBvcnQgaW4gcmFuZ2UoX1NUUkVBTV9QT1JUX1JBTkdFWzBdLCBfU1RSRUFNX1BPUlRfUkFOR0VbMV0pOgogICAgICAgICAgICB0cnk6CiAgICAgICAgICAgICAgICBzZXJ2ZXIgPSBUaHJlYWRpbmdIVFRQU2VydmVyKCgiMTI3LjAuMC4xIiwgcG9ydCksIF9TdHJlYW1IYW5kbGVyKQogICAgICAgICAgICBleGNlcHQgT1NFcnJvcjoKICAgICAgICAgICAgICAgIGNvbnRpbnVlCiAgICAgICAgICAgIHNlcnZlci5kYWVtb25fdGhyZWFkcyA9IFRydWUKICAgICAgICAgICAgdGhyZWFkaW5nLlRocmVhZCh0YXJnZXQ9c2VydmVyLnNlcnZlX2ZvcmV2ZXIsIGRhZW1vbj1UcnVlKS5zdGFydCgpCiAgICAgICAgICAgIF9TVFJFQU1fU1RBVEVbInBvcnQiXSA9IHBvcnQKICAgICAgICAgICAgX1NUUkVBTV9TVEFURVsic2VydmVyIl0gPSBzZXJ2ZXIKICAgICAgICAgICAgcmV0dXJuIHBvcnQKICAgIHJldHVybiAwCgpkZWYgX2I2NCh2YWx1ZTogc3RyKSAtPiBieXRlczoKICAgIHRleHQgPSBfdGV4dCh2YWx1ZSkKICAgIHRleHQgKz0gIj0iICogKC1sZW4odGV4dCkgJSA0KQogICAgdHJ5OgogICAgICAgIHJldHVybiBiYXNlNjQuYjY0ZGVjb2RlKHRleHQpCiAgICBleGNlcHQgKFZhbHVlRXJyb3IsIGJpbmFzY2lpLkVycm9yKToKICAgICAgICByZXR1cm4gYmFzZTY0LnVybHNhZmVfYjY0ZGVjb2RlKHRleHQpCgpkZWYgX2JyYW5jaF9vbmVfYnl0ZXMoKSAtPiBieXRlczoKICAgIGlmIG5vdCBoYXNhdHRyKF9icmFuY2hfb25lX2J5dGVzLCAidmFsdWUiKToKICAgICAgICBfYnJhbmNoX29uZV9ieXRlcy52YWx1ZSA9IGx6bWEuZGVjb21wcmVzcyhiYXNlNjQuYjg1ZGVjb2RlKF9CUkFOQ0hfT05FX0I4NSkpCiAgICByZXR1cm4gX2JyYW5jaF9vbmVfYnl0ZXMudmFsdWUKCl9CUkFOQ0hfT05FX0I4NSA9ICgKICAgICd7V3A0OFNeeGs5PUdMQEUwc3RXYTc2MVNNYlQ4JGo7Ui13TnsjXmhvdWY3UUlJVlU3PEV3KjZDMz8mdlFSN2BWaXhNSVpIOUh5elNSTilkZ3Q1SHNPRmwpKkA2aFN4R21xNWFBJwogICAgJ1FxY1RKPnVFWHQzY2E/QCteKys4PGB2ZFdhUzFhIV4oQDNwaUhOXlVEZWFedXR6Jm02OFB3SylsYSo0M1UqbU5ZVH5BejN2V1JSOU1AdTklYD58YG9UdVZBbXs2WGJpNzxCe0wnCiAgICAnKzklfUV7e1I0dFc7TiRpVHV1UGdKYHU7dFo/cUUjNmZ7SiZnTXt6bG9DWFpvRy1ocXVvTWojSTFzclk/QiZ+cDl4Z2JVemJAITUqNFM3bWEmeSM+aVVvVyk2ckpfQk95TElwTCcKICAgICd4T0R5REVPSERVeSlIcl4kaEVFb2REJGhiR3JaUUlFdThgVGJfSDt+Wj5WTVdLVzV+cC1oT050WkpvaSp1JnRPPW02OSFaPlY3RWArV2BGJXJCNlpgPjlKKlNKJUF6cWduYTtqJwogICAgJ3B5THhaaTt5Y0phTX5qPG8lSHw3IXdgP1l5RW03aTZwTW5XeHV3NHpgfkI2VUtSfHdZQDJnbDxpWHJKRGR7XzEqJHFwO2liTU59eElMPCpHaSRhSV9Ub084bmlEWnxXNnV6MSEnCiAgICAnJSlPZnUzcWZScTFoMXBfXzBnfHZxRyg/O2FQNzYjYC0qQFdzVGJTYzk4IUFMODN3dF80cV5OSHFTa1k/RCZrbzUzaV97Rjlufmxfe3heNUN7SHxmTUFJWDRmYHdiN0VSalozeScKICAgICcrIztWTUh1NVA9SnYzJnlwXi1BU0RUWFlDJSRUeE43bj9qLT14c1kwNjc2eU1RKWVXZVlrRzNKRDw+Xz50e0hoQUl4Q140KD84JlZjVXg9dXgocXJnY0lBWFU1WW9zYz96MSQoJwogICAgJ0ZxZlB8KTIkdmUoJn11dzsodXhkTz5FNmRNTW5eYDc5ZVRtQ19CPXFrT0JeeT0xQThzUWk8TWdXfmZEZFcwdDR7XjxJak1eSj94PCZaMU0pcFlPJnVFQSF5Unc/TnBfRW9pe28nCiAgICAnVjlkRCVWQTZ4Kmc+aiNoNTs0fSsjSUxufiMjUWg1VjgtJWxgQ2djeTB1N0RSIU4kMDdRMCNCV1o5aWNQPGE1VWlMKkhTI2lXO1FpUnspdXQ4JmM5aWJDdFJecy1odnhUPEI1SScKICAgICdwWkYqPDNNejY4NUl7NUJuMDNlN0AmRCV4ZWEwK29CaUk9I0F5XjM4RDM3NyU8UXVNWi1PKiVUdjs4fD1YN2tAQlI5fm03aUV8QD94JXpsUTNORTk2OFM7K1lAT0tUSU8xblJRJwogICAgJyUkUGxtRzI2RVdHJmhzTChBOEt2enIqUzVBeSZnd1JeUXM1RVB8bG1KYzs2ZVh7NSszPi1XM1BeWFFZWSl8WGE8NXYkXmBwfG5hVkxXXio0eD5vVGYkfT8yJXs2YkR9O2x7d3AnCiAgICAnVVh4Jj57TzxKfnh9fD4oIVYxOHA5M3hCV181K0gjeWV1MDN2UmpFU0xYRCRBOXt5VlF3ailJKE5vaE8+T1JyVGpQRUF7P0RBVTBkeFNYIUs3NDcxe01jSFh3TmktSDtvKmZTeycKICAgICdBXnUlP3l8R0ghUmojeUx1THRgIW88S2YpWShacE40VHozPGZPYCMkREU3YkYtJW9xRHN0KjNfRFdnOG5aaUVmTDBPZyQ8aTlYUmdzeD8yXkc+dHtqWUxZWHxhKXRBRz58YWhRJwogICAgJyhDdlQ0cjhuRytlMWM9VVM1Izw7NHFpZVFLbUZ9diNMaXI1RXxkbz9EaE5aRFNhMzJkfDhKQCtqamEmUEcjfXtzPlFBdFdAUFYkVT9xPSgxWEU5YyNWJF93ZyticCZWJkIpZUUnCiAgICAnd3xFNyUmQD1mVzQ2JUtRVHxoeC02KF43QDtHU0F1UWlWQUtXanskPU48RGtvK1R1Xn4mX2c0ayZ0V3lUK1JpQUJlcyVjezJHbFppem5+LW1sJWwmSGVDUTdZODl7KntGaEZKJCcKICAgICclQTBUNU9rOVlUcVUhWWBGT0QwVmxsPDkzR0FVdkV3e2YjI1M1TmFAXzwmLWdeQzg7WE5QO0puczRQNGA5RyZPdVZ5OUZ7eWV9OXBaWEZCR2FWezlHcVdzZUZYWERrdi1KdHIjJwogICAgJ1hgdjUqPFZ9dTdXekFATGxJSXRwViZMJURudSFCYFRsel5mTyR8JjRFY3JeZjVAbHxQayo/bGBRMGtgPWAoSjl9bVRQIW94WEt8NStnPmlGYVZ8LV50Oz5VK2UqcH1wVXhzR2cnCiAgICAnUjw7Q0BBPEAjQj8xYklkZyR5SSt5QTZBeFkyM2NQYTEyQTc5I0Z2KSE9aDBOK0dSczBLZzA3OGB9Sng3NmtrbUYyPzdgZlUkTHQ4bTNANT5MVXA3KU1jYU9GMyVsZUpRTUEoVicKICAgICd6I2o7UEMkTiEyWXdpRHAkRmRaRTNCNilhTkJZVWEoVE5hb3k4WH49YnlCSGFiXipudjklKn1SZjU0Y2FfYjBBWG9SX0czYUA2USNaRnBVXjY/fjNTOSZufG95RFQ9eSstYVNoJwogICAgJ25fQG14cTA7S2tJe040PWFPajB3LUc7VDF7NXxqVWt+cnBZdX1+biZ4ZVhPTlJ7eEB3PXd4b0lqT2gzXmN3cDYjKl96TnpLd0dtdCVnUzlyP0Y4Y01qS1QkbEJ8YnIrNTF5QjInCiAgICAnPXdaVjdmeTdEe2AoMjkjYDZRI1FJYSVobSlpcz5LRF9yeSNfSCotRip8Wj8lUXY4V3JqQFg9ZG97cD0qeDNGekA3d1M3QDBifn4tbkBVZmRlXnlMcXRRQ20/ME9gRGE2bm4taicKICAgICdyOVBvZzJmakFGd1k8Z2VsYCYhKyREQU5ETFpmYElLaGc0QlpHUGRFWVgxbiE4clMrZ1E3bFB7P3tLTzQ1dnNVdTJkUzcqK2xHYmNrP0wqLWc5MW1wRWF2JVYlSlkxO21AN2JiJwogICAgJyF+OCpAKFBtSXgkaE00KWtRRCMtTjlsX3NVOFVwUXlxOyMhMmNSNjRHcjl9M0JJbXFWKFAhcDZ1dz9LJUVeJX5gMkYqUC1XSVEzdXcta0lrNG08OEBSWUY1VytYaG9ReGBwNmsnCiAgICAnKzlJI3tFfTg+SUpreVElcTY0MzZuRjl0I0xzejt9YiRocDV7XykkX0R3WmVjOEQmeEpwVTQhLShzfWIxMTJOSUs3Mlh0dnJyR1gyMn15fjNfaXJveyZNbmhFVEErRGFLP1hpKCcKICAgICdRMEpfJmRGZUo1IzdmSyNrdDdlXmVAYzFEN2lPc2Q3WSR+d3NSVEojcWl8XihoI3lXZDJ9RklVOEI5SUdeejxYNzRedE8tNnVyKF5DWjEzQVdgVUZiQ3tQZSVAKW9JTjQ1TXFJJwogICAgJ1BIZHE5RCFLYnplKlA/aCFPQykzcWlCIWw/NDlXUz8pckh2b0d0RnhhcGApdzE9dGY4QU1RNUlmckczITkqKHVRcD4mLTkwNykqKGohKHFYamlMYlBeI31AfHczM2s0Rn5gN20nCiAgICAnS35mTGJSJWQ/eiVobChNKk0jQjYpK2V6JkQzJEpEWWc1QUYydkRNUEVFMkc7ZHQtUCFndEUhcWFKNDElVGp4Z2hTQElCVXdVRUliQkJ8QUo0P2hxfUJMYXZKK158Rl5zRTgwbycKICAgICd1TEE/Qjk2biFZaWMrOWpXUTZiYUx4fCtQMEJqQ0tKUDZDbUtEdDVHc3NXczFvZWtIRzRpZnhMQUtHYCplYmFFPS01a29iTUJ9UHo7UjBSRXFOLXh9cTMlVyRCKmpCP0V7QSVCJwogICAgJzJNaHpLMSV1b3VtejF0cGFgezljaktxZ1lvKEAxfHooTilQZUd2SWlibG4+cmtTQWx0O0BUalo0Nm1WRS1QeE9SMTs7MERsb3BweXNZWmw8bGlLQlJLUnQ/OSRZUGE7KzNUfU8nCiAgICAndGsoMnJDeyhkWlFgeW0rcnFQXnx3cjBPST5lNkd8QSFQfD9iQjFUN3dDYnpmMDF0KG5FVUdyRldqZU1scmFafX5PJVhufjNTYElqPzNYaFpKajQ0cl5uPV5WMStOJjRsYnhHbycKICAgICcwIXgpQHUxT2gyRzU1OEt6b3pfeFJ2XkBSK1NnYEN6N0cqSHJydTx1KTNNJk1IZWFyVW84KnE9VG18cT5GI2RaVzImQEdyNUg3d1hzJkxBej80d0U3YFV3QlRSa2VNWS13Jn54JwogICAgJ3hZUHQ9YnpmKDg5ZmZwZVJAZGFaQkg+K2kmOUFRWHo4QWc+UVl+KUNBIWNtSGdIPEFEYXZpWik1ZFlKdWorfWh4bEhhb25oYGx6RSR2fFRaMkY/dH0xaUs2dzM7eHgzaWBrNUUnCiAgICAnM2ZUOCRoKSQ5Z2w1OXBqbjkhV3l5KENpU20pZklUcWpqX0hDNmJCKnhxTlVWQEYlXjtBSkd7Jk4jdXBIeilxezJlR3RKezNWdCp+P242bWJJNT8zdHQmJmtqbFNeSmtgNUFLaycKICAgICdzdEMmRiF9ZXYmKHk/dyZCaiNwTDx4dUZxWmxnQ1BkQT0/UHYwU3Q1QzlAYHBeJSt9PlBWYENNNCZXWGlBQT1wJTtIU0VeSThoeUhiQEhiSmxLbTkoQjwmcnZ4SWRXSiFSYWBXJwogICAgJ2hCVDFkI3tlIz5jejl5OXNVOVo+RkQ1V2h1P2RqeWQkel5Mc0BtfnJzXyMzQSpWJD9oRmxtTzZwMHV6fjh3UC0tTCsmI1Q5LVhpWEtKNEFRJThyMGpLMWI2aCo5V2kkLSo1X2wnCiAgICAnTyNnZyFLJXkldW0oS25SbU8pPTJKbGNGK1h9aFA3R257dkBBVys5ISs/RDQmczNkendKPzx9MEN6RnNIdylJYHFAZiN4fTclZylTQ3ZpUj1kJU0hUm11MEU2NClwOClvZH5KOycKICAgICdgdUFWeDNoeChabVQmWkI1Rk5fI04tUzlFbyFnJUd1elFiJWJvYTFBcjVSSGtUKnw/RkRUNTMwcnhieGR6QXxVWWIwd1NCbSU3UW5AbmVlQGd6PT54VT08e18tcVNmdzV1aUw7JwogICAgJ013MnRAWCpJQHY1Z3llTztBendedm5xIWpaTDxlZUMjWUdveVIlRkZHZ0t4Nz5DVFklWXskakVuVFVobWxFPnZXYSZ4Ul5kYWVJZ3RQUzl0QFV4TSs1RChqUXRRX0sjbT57aVUnCiAgICAnTz9MKExzazM8JksmVW1zIVY0KCEweyY2ekAhdV4wSSUyaWt2TXVDdj9NJW9eUlU0aUw5VWw9VHFgUXFAWXxnbHtvRlZ+UGd7MyF0IzA/PlBiXkBmfDNvK0RrY0wzYD1VJiY5OScKICAgICduMWlwVTtrKDYkTnoyNmQzK1g5a0QyWGE7KTtmPXFtYGlUOCFAJlF1KmNKNWlfQEhkO1c0T04yI15AfnJ0fG9pUkVwZDF6YzBmTHZMI2QoKEt0YTZCSTN2QW4tVkB4WlY2P2d3JwogICAgJ0JGKz4qIzNadm0kaVowJipMNHhGZj5QNjVGc0B3JitDI3dNXnM0MWxSSmxUPjNPVUsrSHxeTShse2dtckFtIypWSW8qSXspNilgTnpyNiFubXcjN2w7YT07VG42bHkydlM3PSEnCiAgICAnNH5mRV9yOSk5JiQ3Um5TbWFVSGxlRU0pZ3NHUilVZVBJMlo7ZXdPMD9VezRIal5OU3BQP1pLVFMxbnl+I3VwNmkqSnZNSUJ4ZmptNiFMSThHV1hTKV80fkdQMFRjYGtAUkhsYicKICAgICc/SCp5ejBSbyslUmBKfHtIdHNFJXh4Ynh8ayp7NW9feFpmRC00YnRlcnVDYWgxZXBAMXZsdjZedUN5MX1ge2ZwVzQyQGArTXU7Vj9sJHlQdWpkPzx8ZGcoeVhuRXNDKSMxPygkJwogICAgJ3pLSSEpV0p7X28tK3pgJT5nQEdDV2F9djk4MWh8d3lHeD0lb05vJDRHQ1pHczZ0LSRteXtSfn5WVCktfHQweE9tRkgqbUcqfnpncyN0QiZQO1ptb3BRQ35eMiVrPnswZDxwfTMnCiAgICAneWl1UVUja2wlcU1ASkBvMXMkMD9BSSQrYWB0dVJKdFY0aDJ4Q0RhT01BMjY2Km5NfUUyezskSmNWTU9UZGxFdE5KdkA/SS0yTCVAMnE9VkNVcnlzV019ZkYlaWFEMGUrcHQpTycKICAgICc4Y0RWU2kkajA5M18zWCZCRkxiYjxlaGotPkl3Zlp8OGhrYzU2dG5pJjJQQlNwZik+aHczQz16LT8ra1FiI2QyNihvMTdhc2txPlc0UHJ9OzAhSkUjQHN4T0Y5bXkyKWg8O2NiJwogICAgJ3FUNnBHJCVrNitmPUZoV2FtOX1jUVJYWk41d2xVJCVVMXZjWntqSXJpdV5oKDBNKnhRcm1+YjR4ditBKTIqaHt8Kk9VWkhSc3xmfClHRUthJipnfilXMlR0VEBzcCFZaX5KcDYnCiAgICAnd2okemU3UWgtbm4tZDdmKjxUdmE+NDs7Rmg/RGBwMWljUzg2RippQTl6dGotV0QkPjc5JWdzQiMxRmJHe18+NUxzWWE/WDY5QDhzM3hke2JFcjxOfiRZPmA2WVUwI3V4MCkrKycKICAgICdfJUBwMVd+U3U4bUl1JlNEeWpuIUc1UXJ8OEt8TmI5fUpGSm9qUSs2cF47dyt1VDZsbnlLdFpTPTNlbFIpYGhsPm5GVl9zPDZeaDsrKDMqNClZRmI7dVBoMnNFKDt4a3c9byh7JwogICAgJ3JZdE40U0B6ZHlCNyZ6X2FXUVo7MCUwRSo0OE1gQGFBVEVkUkBWMTMrajs1WWhWP25pSCtVPDNJVlMpa2x8dj5uO1RVNkUoakc4NG1eKlp0MkhGJXlaNjA5MjFyMjV3QW9ldlUnCiAgICAnZm1rQDZGaEdzSWxNSzFDc1Y4Sm00Pz4tfXNXNG5VX3hvdn0lYXtROzBHQmw+KyUtIXI0YDltck93NiFEX3p5M0t3YTZefnJDa3BeQTFDMXwtSnYqbDlNPXAodG9ZNj5qfFh9RicKICAgICcmSipXLUUkTG9gSypOZDxFb0hPLVR9Mjszc2FvYyRoJH5DZ2E/RDI8KiY1SGc0NndWM14mdX1lSmhrWHxhZ2tlUzg7Q0JLN2lUWE1sIUAhejMjWGYyeCp6Km5GKUI3Tl5VPVZ4JwogICAgJ0IxfVhTV196JHRKaHJ4KihEbXJyKFpwZTY/Yk1vRVV9SGQkNW5xMDJkOzhCVXNHLTkhPTxHTzBSfF5pYjNwKzAlYH15dV92fkojVTF5cHY1eWs8d0o+TyoqZUJ+VGlZYFhNU08nCiAgICAnanchMnRnRUBGY2JOUzlIUmkjfWdzKj5DUldWZ2paK1dITHNsTSVMe3pMbFg4PE8qVSprSFRPMTBiS1EhcnooKFUlIXp1bm17KjtVNHZgZj10a2lfR1lTbl8oV0EyUThQPVVrNycKICAgICdZU05NYHYkQ3tUXk5SIUh4OWFrMzJPZjZFUU1edmlyayZNdF8hZ1NDd3B0fGM8Qng3TChQUW9WelEkdHAqMSRRbl87d2N9Z355enctZHVEV3VodmBfU1E7QDtXKXN3TUBtNFZiJwogICAgJ1c4QWV6Vm4jTjkkZVlIWj5rPlVBRXJmRz56NklJMnsxYy1OTDFHfilJXm0+IzY/NiU9TmRjeFZuRCNuaTN1V3VpKWp4OUM0PVd+a0xZfE9lKmJld1N8TjgqIUF8I3goJCErbVInCiAgICAnJmdhRFV7QSZlQSZUSn5Yd1FgRmwlTnJkWDRJUzEwdWkyYFdmRVF+YkhlPnwwa3k5cjtRZUtiLT5XSEJga1A8WistcmItdjYlMH4zbTc/c2lgKCREUChVZ1ZOYlhzY0EtejdUJicKICAgICdCWHFZfHFZcCs1cz9wLXRWOUtBVGAlTHAmNUZHK3ZkJEtzTyRxPihCK2JaPEVpfnpyKzMpYnRQOD4tWlYhcnpPdFBPWnQ4VHpwbjk3ZVErd0xoOVRsISkpeHp7LWIyfWtrRSlYJwogICAgJ0VKRzFHPEEyWGpnKX5JZT4zSVBKUEQ7STZzdUAqO04ofXohbzcraD5jQWx7akVjWjI8cEZyZGhjYkstJkklOCFpQVNBfjlCYHZEekxOM3ZXYGM4ODM8QlQkTV5nUzMtIyZeV0knCiAgICAnTGFQR0dHfEU7dCZnNDYpZDtAQmxMJlkqM1RTfkZvbW94eVklVn1Qaz0hUy09TVZee2BfNEhiTS1oOVlwOFRDKloxfSp7bDwhVSlQWUxAamNAPS1pMHtRSzZ7cEU4eTNBQyNicCcKICAgICdsOXlkdzFieF5hKkBAb3tFe3tsb3pReG0qemIyXzsmOXQoNz9YSWNycFgkKF96eHZjdkdFPzIoNHBNRyMtX1olKXU3TShYIz10P1ZxRFVtbngkcWtQeDVwNDMmZUt8R0BlO0UqJwogICAgJ2JqUUxLIVUlJTZUb3UjQ1pqd258Vy1UfFBUfUE4TENQYShMQDduJTFtPmxmQ0ozTmUwTktEQkdnaXR9TFlvT1Ntc2wxZWYwUEVsbG1qKkBKcyNyNncwOExoOStiU2VvbSRfKiEnCiAgICAnNXxyNlk0RHh9SlBhcENfUkF7VkFUfCtacEtFRW9BQDQpYDRTNnBtQ0tHU1pUVHJSTlJCQFY3LXVjRGJHNG5NXm9KbEEpaDk3c2BoPn5jJmlDezJpZyFkMSNNc3wyRXBJNDxwZycKICAgICc1e2srdWFwVWJYJjB8JDk2bytMVShWSStWWWpHdFZxSVYkVWgzYDdKaUE/bllUQWlgPlZTK2JEK0dTKF50ZGw1K3hLNm5KKCZiNXhVfm93aTJ3eHRKd3VRZlpNOU1Pd3gwUyZZJwogICAgJzBNfHRCTjFQK19TWSNCU0NDd1BxVTRrVzdVKDhjMEYmVzRuRjF4Y0E5MWYpQiN6entnTDMqI3c3aXpobnE+Km8tdmN7bUxBNVFUXllGSSpyaTEyQStHb1QoKjRzRHw7RGkzTDsnCiAgICAnZGR2QW1HLWwtWDtaQVZvNXhmZ00ybSNMaXAyVGZXJWtKP2QqdEFKRHVvO0IwRWNXfW1yJGQrfmZRSTx7IWlHUWUwfHhhdEV9ZVU0dz1zdkJwSFI8ZlAoNldvRnkmRlQ4TkdWOCcKICAgICcoJlErN1k7JW1id0RYeUF0TWp7I15SUm4/eDs4Y1J3M19TS09VaFFZYSErcTFPV3FJbGopSlpyT1ReMXUkQnU7JFl7M25FeWM3Iyg5T2VscnVwKTR5eDZ3fX0ybkpSRDRPfClzJwogICAgJyVyQntfK25mZEs1ZU5kY0JXYFo5QklvZCtJTXdzY2xVeG4oIWJwMlAwQzdTRDhfRUExcStJQmlreXVUSEV5dyEzeHVJSmFUdmZiOGM3RVBjZ18xUSFDfkkrVHVgJGRRXnt0RDgnCiAgICAnZ1VSXkZAO3xwVkkoPjluVjlMNGN0NS1FRypRMnZPaDd8UXZZQGZzdS1teDQ9KTIkVyZIJUJ2KjZQa3FvIVgpc0dValoqdz8oJGNsdTFCS05SIWN2bSZsX0E0IVFhTWpIPCl8OCcKICAgICdufjYySy05KDduVUd2dVgpOzBRRnZmc2pfX3VoSThPO2tkZjxMM1YqSVBSenpESGZ8bHk1UitZJHshRVFHP1BwbUxtWmN5N257dTUkVWEwUXVJKDJ5WnNxO3FQVmRDfXBlcV4wJwogICAgJ3o8QHBqenNge3NBcT1FaUd1OVp1K3ckWkcwc3MoOzUxZjhidylkaTg3WmI1ditOZzY3RGZhU0g9SU9eO0FZaTZ0a3RecVVIUjs3ZyhrP1ZlZnVgXnhvUU40I1UpJS1KQjs4RU0nCiAgICAnZlFUYGFHJkhgTEZvUjhxT30yYmVeNmBnbU07bj9IX1RVOU80TSlCRTYoek52eHkmdERRS0t9UkBHeT9hOHJ2VTd2aFokKStlaSMhUVFKK0dqeU4xfFQ9KUstJUZHSFFBfU0oKycKICAgICd7Q0sreHQ0UiRZWWdZUGtaKyhKV2lPNEl3VHVtcUQrdkBmPz0pd19DdmZ0UU1hPlRGa2dPSGVAcU9uRlJTRUp0WFVKcHUrTFhuUipONHZgUTgzbDJ7bTE8ITdjdjQrZUt6UnBWJwogICAgJzIoJHc8UUotNU9QZVE2U2JzM2BvVXNnby1TSW99YGFNSTVSNzA5RXR8M2tid3lvaEt0cWtreTgtU2lOVS1nJjxYcWk1eCYhLUhoT29OdzhsZjNnUn1IZ0lDeFZ2aV8ja1NDOSknCiAgICAnd0IhQXkrVj9vQjc3R3IzcUNRUEVwRmBzez0rJXt+NzdNKFF6JW1TP0okcmo4UklKaHEqa340S3NudkJGWmkpRjI9PGo5YnY7TmBjSzcxeHNkXlU9KWBpbWZPR3ZPSTZ5Q0w5dCcKICAgICd1JmBlWGExI1M+cHZzcFUqJlVSRXBhZ0N2ZyhsS2ttK2psS2lufXBGVnljWEU2TCV3KHZIJjF9YmFJOWhCd3B6aT5JPGMzdj5PNDY2PD9JUGJaUT0kSlJ+dzd4cCprKlZGYWNkJwogICAgJ0V2JEJARCtReWtzVTc9Nj43TCVAJXtfNTBTajklQFh6ZUFBT3FpcD0jZnE/eWtuNHEpMih8Rnw/SG5VVjU7RyU+bEcqbX1BdTt4UEZRNCgrajspLTFTRF45QnRGakVeTz96fXcnCiAgICAndVV8IW02SHkjejJNPlVibGdUTGVhRiVgOGYxNndrVD48VWkrVFNwfWU3MFkzbDZAWnl3ajBEdj11UWQqSzk/S1JhZy15TEhqaTAjUCFgcH0+Zm5LYkViP2VAZW1+cz5YdHR5SycKICAgICcpVGNlS0hRLX5Ubnp7aytncnBpLXgyVDtLPXlNX14lU2BpREVlITF7bGolZyFHfnRkUEljfUYxVjduOH04TmsqfncyN1NSNzBSSygjIyFCWl5ARzYtWFFFYjxYakNteUplV3wyJwogICAgJ1hYMD45dHwzKHVCRzc0YUMmNWdNaDx9fF9MOEBSck92dDFxbl5LeUs1QCplQUVyRE1NYXxING1scGVYfjtQQEVJd14jJTgkRnMzVyo1eUshTypoenFjYi1eQHBIbXhiWU8/aTcnCiAgICAnJiU0eCFjPmVffS1GPG5XUmhCUiUzPTIpeHpDSHNeezxLN3gqbXw8MzI2I3c5IXpgeWVyVzF9eGU1VVh1aT9BMmVqOVlHb1glZ1RiTDAzZFQhKEUoc2Y+JUdHUzZaM3YlYnFBOScKICAgICc0JmRDNig3R3VRQWFPN3s9PnIlMG5YQFEqdGMlUV5iTUU1eCFebz05ZTJEWEdtUmRWP3RLKlplYFUqdmReQ2MpaTZHPSUybHU2U0EzMjlqNDRwTTMyMz5RfWFXNk99VElOfVBKJwogICAgJyhZXkVLbWlBSHd0fVplWGo7QiQpUDtXM3FHamYqejZLPlI2e3M0dWZhYSUkNDdlJmQzMmF7NyU3YF49YWxqPE5QaFpAaHJ6aHc7YSMxOFghI3ozO1g+bGRPSW9fN19gOVBNZlYnCiAgICAnPDg2fjlSSzExTzJEcjJAVmZlcUopaWNFcihvVmh7anJoKjxHRW9KfHR0fDVeTD5vNlc3Wk5DZjhqby1rYT8qMjx2KkFydlc/MjhscylePj5jOXpXejR8cEpeJGNvSF9fNX59PScKICAgICdNaikyKHMjcGF3NjlmezsqY3cySiFxdXJNezdRd2EhJG5vTjUpPFkjMWlXcztxOFVDfjJvYmg8YTM8dDlMeUVnRXhxPHlFZlQ0TW0oQytMRSRtNnMzJFZTOWJLa2ZRKUVXMHxAJwogICAgJyFseXNwQ2RHZH0qfUx5U2E9bW99bG1eVTc7JWhjNl9iKmBrKkE+UFRjcClFb1poUEApTXlqdT96eX1jdjZ4MGQwSitnZH43LUJ5aXNMSXxPPlh+PFheMmI3K3V5WD9ed3xReSMnCiAgICAnY29kOHh0VHVjQTl1USNCRVZPTFhAXlpaSkR5bV5UQSZHXlVPZC1CTjMmakZPJXpwYTFxQVFCUSQyJEt3WUZMN2duYz8xfE5DdEJVKWM1ZyoreStPPzlHUG4lMEJQdnRFWSZaaycKICAgICdZOTA2TFp7dndFRDEqQUs1cEdVRillISpmMEZQZ0QoRWNzK0YwUjwpcXFSayleV2NyQWhnYV9lI1FhS1U3O3RETWowUWkwKXlDViFLJkEmfVYrell4OXcjYVRIb096NldzXk5PJwogICAgJ2V9QEw1eF5sZHpAa19tUU05PWRoU3hZRnIqSzFwZEYmPUxSM0ZUUXo9bTByRD5IQ3RKUk8lPWI5N1AzTT1pWW9SOTUwMUUrZnx6aGtkakItbWw1dWxZTEpteSQ7WH0pSlUkKzMnCiAgICAnenlOVD1zfCZaUGJeJlJSb1BFN1d5dHp0XjVpXi1peU9GUU97Mm4xTWpBcjY4aSNsWWpRTlo+ND1lb29MK3pwTSZFNEprdjZONkFLcURqOTx6REE4dmI+aEVGMkgzZilFaHFwaCcKICAgICdJJGAmMTl+eHB8S3RoUUs+OHR8RE9BRjBGcSZBVW5UTXVmNlFgbmBWc1ZFKF80TH5FIWNsfUZRRGc9VytASElrdWNJOVEyJVBZPlhgcSk3UCFsZj5mUG00JnlYNSZhJWJaS0V5JwogICAgJ219RlJyeEhnIWwxJHk5eTxlVnlXV1VMWGxEb0MyaiNAWHhtWEdPKzBGPlNzJHVraiZ+dHdCO3BfP2hBYWI8TT9BY1g4S0UyPlFgfTlNZ3Q5WTIzT0YzQSZYXz5vR2k8biM7JGonCiAgICAnQkVYZW56MEBoeCU3PysxJFMpQChfJiZPK2c4eDx+RT5HWFQ+dFVlPkxBR342ZDd7PjI9VkE/JGoyc3Ztakk5TG5jYUdWWFBmakt7SjlmREtKfTdaKyg3JVN5OzxaTD5aP2c7SycKICAgICc3cllxfGNPPk1hXkEoIWZzTHBjYE92KCQ4NSg9X2FKVGNIej52ZnZqKThMSWJfdmtlcUJqZGlkZGFRbCRDZ3NAO3hBa0AtJXBqWjc7Vm5JRm9EN3dlY2M0N1BqPFJQb2tFVT13JwogICAgJ2t7aCVJK0c+UzR6PEFPfDtoJWs4YEpMaDw+ODFFTHM4fiN1MWt1OHlAND8xRXpSfX5EXjFYYy1eWjJ7YD1oTWxBTmJ6c3tvNiNAUzJUIV8tYl5+VmB6eFE0a0tCXm1IRio7cionCiAgICAnNllASDw8Q3NKYSNPcTk7WSpUNjYtKyhPV0JPYip+JC1oR1koSzcjZz9oJkxVUFR7aFUzVlQ2KjJpMCgrdWlSb1VzJntyV2I3P3k4Yyphbzc8OHFubCVGQCEzemh7OEZgJEdnJicKICAgICdiNiopazVqNj5kJnkoV2YoWSZxOHp5eUtCbHZ5fV9ZJkl7JSFmIyREZ3JzfUY+UUdoKmhuMn0jV05zdDYhUT93eiVwMFc2bmpSPj5jejZhK05vPDB2UyFHPU4hNFlebytxLSpVJwogICAgJ3lEJEBwIWl8JElAYHtYO3YxZlh8azV6Kkp7VGFMOFJLYilUIXZwaV9nZCQ/bU9TZEcpJTNxYzRpeDQ2U2ZQO2VaTSNJaSgoPStXZSElc0txM1VDWG1FRWlge2VZOyhgcm1kcVYnCiAgICAnOTsoeTF7Nm5pcVdqJCt6UGVnND9NWV9fRVJlT3xLR2oyfUklTk9iQm1pRUt4e0NCIW89U0l2NFpVMktKT01oc15aUXFiczdvYmw5Xnw4KXtYcWFOcCsoMDM5Jl4wMDBTYV5oJicKICAgICcyNCV1MVNHZHtYO18mamh8MV58ejN0JUwtPXhQKlYhdSV3X2AkSWVnVXh2PjM5QGt1K2FKaUNxMUR5VzZheWx7U0xVVlIyNjh7Y1o3JG9oKFlofnBBYWJDOUMzYD5CXjhpM2p3JwogICAgJ2NneWFUMSpkJTtWJngyP1FHWlNwSnlOK0A3Tz9XXyl6V1hOMzRFb2V6JWM8fF40bXU8X0tQb0NSdmpva202OWlKNEFDSmBgOEopd0s2e3w5ZEw9MntDNn4mZlNIYyF+NHgmbUgnCiAgICAnX21eaW1hRHxFekZjb3chVl55fENJflQ2fTFgc0NIe1pxTGBMR3xydmw3VWVMdE9PWUBpZEBiYyR7MGRuRkNCR3cofX1wNWtBKnFCKj9nXkF2NTUzU05lV35DT2A5I3ByflB+cScKICAgICclMih6MT5xJistWCUqSkplYlcjX01ENDxyXitJYUU+TjhXWmshdSktcnNyKDVIMiMpMT47aUM7QCo4SV5CPCpffHE9VDJ0T3RwbStLPUZlMyVQMmB5bXN6O0dSNTlHYiY+c3JXJwogICAgJ2sjbHdpIXgzUTFNP15RXzxjSWlzSFV6VEpZJE4zeilBOVYpS1MldVV5QW05YD96dVVYb1E4dkVnMG43V3JsST9sKkFGOHp6PmVudU9IPVgqOWN9KGxlS2hBLXFROzQ2Ml8hIyonCiAgICAnUGU/cjtNXzROd2ZkNi1gWF9GYiE2UFQtO3p0LStPPV5KemAtSlIxVkBCNEk+ZVIraG8wMHM2ZUQ7OUZnU0xxSDF3ViVARl4kZ3M+Yl96eGZ2dWx2fDt6SXdlWjVWYmJjYSRCNicKICAgICdzQCNCNkpFUnpRdnNVUTVGT3JYNj5UYSNSVlRibUBrbTAodXRHJktlMWhjdjQ8Q3ZIe21HeSZJTGZCVEEwbzhaWjF5TXt4JUheT3I1amY2Sj89TC04ZGBZYTJtPSh1VEdPKERhJwogICAgJytPTSliUnpXQHhCZCgzeGtXeU03U2s1Jj4memRyOD03QVgrQ2I4IWlVdmA/JENxKn1EVE94Yj55WWB2N0NkMV5sQkYqR1FUSGM8bGBtPjhjdVgqXnxkbWJwciM3dHQ2SiR0YDInCiAgICAnaCljJnowM2dzfT5lV3FvOX5Cc0R6WXc4Vlo2dCY5PHJfY2JfUEw8aXUxS34mcDx4NE9iVU9AbikmX3BWKChIUDhqKCE0V3d9LWItQGwzI2p6b0peelcpSm80Nk4rcmFTVXpoZScKICAgICdvNHdyVFNaZztMSjFoNEl7fCNRJSg3LUo8NkR8QCRzM3AmT0RVbzw9N19rJU89MEBDQVJTezg7X2ZZJjZyUEpzeVFzZE49N0RUdXNjKnptZlRTVyM5LWUlRWdpRTlLUUFrNWt3JwogICAgJ1AjKXMlaHxCYD8lN0ZScmxBRGJZNWlec0VaP01mMnpjZHF7QF9mWURgXmg9TGIrVGY+PGIqdGEpJH4qPyR3WUszZTgzYiFlJTtKTkZ4QDB6cU96S1Fadld3cSRCV3k2JDlBUEknCiAgICAnVlpGdyVkS25OUzVHe143JGFmQUtMbExUdFB3UUNNNjF2PGlhVTdpODRIR0xmWHNtUWxhazVSSjQzfCVpMHNnUSFzP0dTPm9CLWtkO219Yz5JemQ3dkF1I3huWVo8P2h6fmYmXycKICAgICdNTys3fXBAfFZsV3koYDtybH1lQ3ZASHBLOUBtVXA9TV41dWFFMFo0YD1fQ1dhMkBoSlY8dipCPU4lVldsPWJGaWk+VE97YSkqWXpBc1heUXcoQFhaan0paT9HMDduViQmSTt1JwogICAgJyUtfWdJQUlRUEw3UDtNMiZ0cEwjXkt9YXFHJW9ORkowNjE9YDd2TzR4LVpBYkpjWHxSa0VANjcpO0k+fXAoNy1PdDYxbT41YHBqUkgjOHlJK0VubXRVTUBnMXwzb0ktOG83a1EnCiAgICAnWEZ4SjNYe35lcDsqNU8+Oz9HQ0dOZjNJaytoYkR8bERvfTxfTDA+R0NvMWNPa0FCYTRMITw8Zm1KIUJRP0hmLThWIWRyOElPRVAkRn16WkJjUlZvbF5EIy07LX5FcTA/bD5lVScKICAgICdEaVJaeUBEZGZLOF9IO0EyUkJteUJ1NVptRlJtfEtoXjlDWDJEYz9jNkIpfmIoNHAwTFgteC1ARHNlVH1qRGBeZmNPT1I5alZrLXdaRWBOVEM8bDJaUUpXUzdUdlNoZyVaKCpFJwogICAgJ3J7VDtEYjQtWilXandgMWMlVTFnYk45Xk9BUVFrbD4/eiF+U2t6eHoyLTQxMHt1cjReUDxmKXZ8RFp9dF8xMzJrU2N3Xm5pLXQlOWs5WE1yV0FDKlJvTVkwZ1AyfGw3d2w/Q0knCiAgICAnZlg9UiVxQT1kWFhDRnQ7MiVaM2g5PCtuVyg1R1dVJU8rRHlVNXhORF94TSsoM3A0Z2dTdVd8YXRIdV5+eSlIMCZFfEl1WXNYcWgzaH0qUDtmbiY4V3lvWGk/VilsYV42ek9LdScKICAgICcwdlBwNkhhbUwlel8+MTdDWnNNNWNBcEpSX1V7KjM2UmgwaDFxbGczYGt1eG1qMSY0Yl8tV3xGP09RRE1nfklTTW5lY14+a1p1WWVkKW4pZVlDVDtCO3Q/djZvJj5DU3tkSUptJwogICAgJ2grc3JJYz1yS1V4KlBCJlJlUUIxUCptPXxnPlheLThuQGNfbTReM2lIcEZ+QlIyajFFSTc0bnYrQ1Q9SmBtTlNLMGk/KmVzdn56SEFXSzF4K1olWXo1JSlPYXMhYkA7T15HK1AnCiAgICAnU2N6JCZwJl5mZmB4WGVNbz8lZ1h6UWttMyM9SHVNR0s/RnptTCFDPyVCI018Mmt7RyZfdkMpNE9aVk0yOCN3LVVhUjBoaTtYWGQwMXFyN3UtdzZqUG1YeHZeRzY2OTxibVVeZycKICAgICdrK01IP2F5LU9EOXxXOzxtRiQ3eT45Y2RxX3hBN21TQDNCLW84QW1XMUxmUTEtLWpVPGw4cG84QihSTUlvITwhRmJ7TGgmMXtTZ3ErVWgxZE9HTjs0V0Ara3tCb2pmSHByJlVBJwogICAgJ29PJXQzWU5pZ05sPGFDTWQ5Rkg3eHo3YHdfUjh2ZHNuZztJRHthTipPb0YkanFrVEIzSUViMlg0QDRga3RgZTNCK0ZWemNOPn0lbkRFUW5SYXAxTFN7P1V+YzREcFVIaFkwUzYnCiAgICAnQTI1JHNqJkF9LXZsbyFeQWo3dXVIZkpvNEFGOSZAYVFjQkpHeHdCczFnU1dWeF91RVJVfkwqNVMlQVdjMHh7fnkqXkhBZWB0dlM4QntsaEwhOzRfdylgaHxHZH0yQzNsTm5YdicKICAgICdEJWopLXNjK2cwWXFuPTQ/TDkoTlB9NEU5YWQmcncxKWxJJUFWKitqN3NFdG50NEE1cE4qe0MoSmYmPDd4TjF9OyQyPl9QT1E7PklsJigyMk5rTFFgQm91LV9gT0koNCFKV1RMJwogICAgJ1JYWmlyY1ZDfUp5cT4yTTR6PSpGKEpqP1R7WnY+QFh7aCEyYUFxPGp5cDdGUmIyYzlvSV4wVjQ2dCVXZmhGaztjZCNxdHNsKzU0MVZETERpYTtUZVpnKE9ncEQja182TU1CQzknCiAgICAnVktNb3lqLS1ibEJOdz5JYE8rem5pdVpJZXstYW1OYXdock9zbGs1YmxUVElYeWVnKSs+cnw9P1FyPC10IUVIU01xbGhKSTQlTmttM2haX1ktPHw7SW1fMjw+UT9jZjNZQ1RwfScKICAgICd4RDlVRlBSNkdSKlA2Wmh6UzI1RGlQNCZUU0Q8b1FwVCE2R3M+N0NlJC0tNnFiVl9uP1JGPys+JDhJMng1K31XeSFARDMlekBYJUohIW5TLXFtcyRxKVlPcmphTkdAM0YySmVJJwogICAgJ0IxMUc4OWMjIVFSZEVpbDNTUzJEY254MWlETng0cHdSN3hkUCROSyk3YiFGUG9jWT5fa0BxfHVhOFI7NilKM1FrMGgrWUxfaVJFTkhfIUx1OVJQM2gzX2tzeF5MUE5tWGxZIXsnCiAgICAnN3lgLXNrclJlPTBebnFVRU0lWktte1QrWUZnK3thbWFgSCRVZk91fFdvfXt+UWBCU0E2YkJgJngzYmFKU3ZpbWlCZChCNVpSQz9udElmO0ZEaV5+fEZTfnZOO2I3fVNBakVRRScKICAgICdOVHF1MzB4eTFAV28lOHJ8NHZnYntZcmQwO2lONUU2akloNVJxdjRXXmgjZ1QtN0BNS0ZaOTN2YF8zQTtKTj11Q1laYVkkTWJIfj0yUVNXS09hKFctOGVsNFJycXJ3fTBVcXZXJwogICAgJ1B7Zzw/QnQoKktASCkzUHdnc0oyRkFkJXdoTVlEYCNEezBzeHB4IVk+MGUrQzV8K0ROS0ZVSmNhc0tLallBcHRHJTd1UlRTUjw0PmxIUVdKQWhUdmwlbVJmOUp8RjJqQTFWQ1QnCiAgICAnZ057M2NBP1I5N1BxbSNXM3hiSUVnXzJuQzsyeDFUPVZucDV0VHdQe0p1OU45QnVmQ25maHJXTHhuYlZhPk5iZzl7dTRUTVhrOys8WE8pMT5TRHJqbk5eemRJN0tAI0woR1d9cicKICAgICcxJD1sPW5pPmp5YXJObWM8ODJaNGApWDN5eSV3XjVpMFkqSmZheXhKX1FhLTA0P3ZoNkZrOHMmYCtlajU2S2tXPTQ5QD1eQEYwN0NzVU13NypqaGd2JTQrUH5ibCpDU3p7IVU+JwogICAgJzB0djxrU15ZKXZwalowNlUqZVRQTjg7bElBNE5Obz9EZENRdlM4PzV3My1AOz0rRXYlTGw3RWoheCRMTyRzej9uQEk0fiR8MGBMYFNRXztrWjVDU1k8S3hhMF5pOXV8c3x+TncnCiAgICAnMX41SGJwdWRkUV5Mcz4wTTIhaERqY0JrUmBIQ25tfE00X1pkMzVkITNKbH1peX1jQHxLV1dSSXI9QXleaTZxfSN1QnxzYEcrNntENyE7R08+UG5SSWNtOEMyPGxZenZUPmxKJScKICAgICdnLVF4eGA9XjxCe141NzNFcWNsI3BXdFQocGUkTzVNUWxCeGtKR3R5ZEVpUU41eVhveUl+NCN1a0haZ0M2X2hxYW91RWVpRURWXlNWfSZnZF98S2cyaUJSfXJxVmFwbSV4dmtzJwogICAgJytfZD82Ujs4e05lP2x0JjkmOGh8YmVwXyV3c2thcy1TMDMtPERkIz9jUkFjWD1mUWkpLX4lJnZkaV93enVjPWIwLUNuMTVQQ3hEdGA5aXxrUn1QKEl4PWN6YFctcGhDTkgqfEMnCiAgICAnJH47P3dNVFhpMVdyJWlPR20mJmB0alYzMGYtOXppIT9SZyQhQTU+dzhIVSV5bm0tNDNuWWlpaGVQWW45SE94XlI7NUhQcnBQZHReO3QqaUMwT2Y3Z0t9Q2hsMUZQb0VPQWBfXicKICAgICdtMTdjPms7MjM8blJWIylLPGU5elo9KyMyMCVkfGtQNms/LVNtZTwpQztfczU0NkV6WXVqSWg4OERfTVZ3VXo2SD8+VUljSEhiTjktSCooKmM1Xzw7NHs5VCN2NihXekYzJHQ7JwogICAgJ0VZajktM0dUZUpCR1ppRk5LZlo1bComTT5zbTA8V2ZHcHdMIVEyfGwkJmY9aDw8KVRMOWNSUmglKHIjPGAqQ0FQWUFoS0dfRHUzVDlXMFFZIVJ4UnNqQFMrR0o9X3NDPlZkcE4nCiAgICAnTUUhfDFFSTBpN0RDIX1qIUY9TzB7ciN8ZTtUbU45eDkjViskP0Q/QDhrQnJDNyt9SnlYXjVyJGwoNkZfb2xxK2ZRc0RTYC16aWZfNGR0M2YpPGJldWhHZUxQZlpvJktMQVBNdycKICAgICdNPShnOzc5QkpoTVF3eCM1KkpSVF5TOFFRditwKUd6TCZRfiQ+QzVJRGQpYTlsT3woVkdhI1NRRDZ1ZkI+cmg7UVhWayMpSENEPkJzPUsjOW9MYFQob2RZc3M+aHVqN0s0YzFJJwogICAgJ3kqU35AdSEmYHpYUi0ob1ErdTd5e0lCKz81N0lsVkheUXBrKmw3eDE/Kmp3cTJAQXspVH5lTHNoYnx6VEF4PmB7KSUyaH52Y01BaiYrUENMdH4hNHpxN1VETU8zWnd4aGZHQkAnCiAgICAndVdZc2lMN0w4eXV6RU9ZWFF0P0lDcml8IXRsaU1BTSsjaEAkY0FRI2ZvaVFua1k/ZS1jVnNmJGFKPjV7cjRSKDktRmtvP0pLJnE2Z2hKezVmK00oMjx2a3EwaUwoZTgkS1p3KCcKICAgICcrZCUwNjB4MCU+ZjxwaUdDTEtecj9MTkZGeVV7ayYwazd9UmdIeF5VNCooZF5rV25EKlNieVNZMChpenh0djk1d2NKKWlwS1VqPCQzJG5UdncleTc9aFYlVSokPlFlZllMR01eJwogICAgJ1R+VW1oNTNMazg3MEo0Nip+T3ghS1BueHBgaUQjUzMzPytLZHxmZERTOGQ0JlRENGdlcG52Pn4odUBVTD47ZVpHIWlNVmFVcUJ5QFlGcitCTk88STdabW9rWHZ2ZXc0YGhINUcnCiAgICAnYG9aenBVUlNPcFR2X0lDczFBYmdFYFdmMURPQHE/aCtrLWd5NXYtT19CUCVwUUNiXnFiXiRfYithZkxpQXkldHpAaTlAVyYhfmh4KC1TU0YlQCpkfEd2Z2N+eT5hM0hoTXEpRScKICAgICctMTgmc3M+dXBwUmJHRnpQXjxXeyZ3SUtfMipUO0JJPzNvN29kdn5FVVBfI2Vne0tjPk1waXU9NCteP0A7bStLWWpEUkZve3phfV5re2E8VTlma2FtM2xabyUxdigrKHdfTlhwJwogICAgJz97KHNIdVBaSF9oUnN2K2ZORkwqRlc5fkk5fSR0dWNWTlRHdmdhbWxjMlI3fFl7b2w1Ml9OS3gyJXYqRlZNSDs1T1loQT82KmJVaGp+Ki1na0deNC1BQGJ+SzhhamExaiZyZ2AnCiAgICAnbSMrMHdDaWZLfGFzX31XakBMPlE+WXlHUEFLOU00M0ZEKChudXNXMElUKitseX0xJEA4cEkrYyU0OWFhY15iK1BIeTB2ZjRzO3pZdXJpYCkrSE83PU8oJFNIZ0dLM2RSUyFSXycKICAgICcldFZsTG5VcTx+Pz0oaHo7UVVCMXVZei1QTHhLV2cyTTdiKCVoVko3JE5WOEtoQ3FjO0tGdUVkY1pjSFNeJTV2NlRGfj9NdTZJTWhIZ2Q5KEtqWGs9TmVjVz1ET2lNMzx0UTVvJwogICAgJ3dAQjwoYFJEbWNRKH5MYyZ0d1MlV3puaG5AWFQjK3hCfD9Ye2NTeDBRR2o+TFg2XiMleFNDP29KTTtgdy1sbS04RE5ZKTJqZCpRT3Y7X0Mzb3hqMlZRWXgkNHU5SHlDTXQqMDInCiAgICAnPlRiVndeS1Q+K3R4TVNXP2dFMzg7cGV1ezdhSl8jUSVZcCRybmdlZTFqI0tRbXxwbyNPRE96VjdgSHdUeD5OSjt6NWhnX3pTdmRldlV5RTIwbnBQbFRCJkAmaGteV053O1FlNScKICAgICc5P3JsdkwlPlI9VWVhdVBMX00yciEzcmBGNnxANSY9R3U+dFBFJFBQZUo9LUNsUW02dllUZTwhMGV4YS1PdSVYbj9lQ0g9PV5EYk8hN0N5IVBoMGZeaVFGJmNZZGo4IWhFUGU7JwogICAgJ2xZKjF6IVFUc0xpQ3U0WkBHR0wrYD1kPlJwUm0pYVhgSkxnK0gjfWRAYERxKFV8Si1mbzVMbWUmXmBzKXQ9QFZgb19tYUcmWnF8QUpXQFQ7aH5SPipwRVFKJiF7IzNIUnpvI3YnCiAgICAnUTg1YnwmdHY7UmpgSiNYTFhrdERJd3VgRnZ1KD5MWXp8ZVNEKCpyOVg+cXswUW1ueTxgJC1CJkshb3dyY21rJmBQYERUZCgpaHc7OUtQa1hTbn1sVUArNzJUKitjOVghcCFEPScKICAgICckSypPUCFUcX1zRVgmPik7QFdKVzN1TFZ5bl5qajBHVXEocT4rK3dNcTd3R28xZ1NjNU5rNlRwVkc8OSleSGNLSkBqKXFgQkN4M1hxRkZIR2o+VFRoa1pkMCohRVlpUEk/SytuJwogICAgJ15yRTtFSHN9QCN2Y3A3XlNPdmcoWUQ5M013T0MzalNCOyh4Kk5SbHZ7aFp7NSZfYnNpQmdOa0ZLOGk9RS1nZitaKEskUE9HTjxlSGdIPSR5RmtKfHphTjVrX01SdCU0NmdPNFMnCiAgICAnPEY8TiNeO2NUfklLZGZAemNGSztHfmF+MjV1I2xYODFpZzF1eD41WFM7JSUmZkFaQTRKfXI2YkdFYjZKRjhPQkw8MTFEPXFsLSpjMExUd2tIKFpMYVUlK0trdGhIISFMcGA5NicKICAgICcjaW4jMGc7OWk/JTtUdEFSOSNyMEl7OHJqKSg1RU1pemJKTik3fnV+dU1aXi1MMmk/SVZCM0V8anAxRjspYVMjbnZHQ3J5PHZmM1JjaGAwKWZhU2crbHBeJHM0bUQhNTlzPDAjJwogICAgJ0B8ZSkjeVdTQUcjaEptO0VYNHUqYVA+c3Zsd2RhZDkmI3dab1BXOzk5Y2pTaWV7U3V3YU9KX1hnWndgNnplXndESCh5XjlpdEopQ3RyT0lqWDlMe3lOMkgya1YlaXBedXloMjInCiAgICAndnU7QndIZCRJWi1yQnheeWo9dHs/alhDd2UtPz9qTHdCZ0IqYiVkYjlZQH0qU0JqN0VrUlFETFJAISNtRC02c1lAN15pVklXO0BkbDg/dlMzRk1AJU8/PzZ7MjdNJW1AQEx7cScKICAgICdiSnwteXl4eFk1Pnl7RVRVb0tJRzM0WUdYX3c3fUU9dEFrJlhJPGBUKERKPXZFWDhTYlhAcjw2cTQrRHcrJUgpdjl3K2xqLXtNenpLWjRmdXxKJT5ed287M0BLS0JsbVlOPSFuJwogICAgJ1JeRyQyRVBsSUEyd2xRVSE1KU5ZcCZobTstcE19VkokcGpebnpnNWZZbld4U3hEKiV6Z1p+aUhmWCp7fS03VSZvNDZlbUJvRGokYkAqN2BxaTlxJVdWMyorNnFhbG9rZkNWZFgnCiAgICAnIys7PT1vV3M2XmUpTnYyYXRRdVRpI0A+TiVwTCVHSkw8UHRMeCQ1X3ZYKztYIys1S3o7ZENWSFg0PTsqNzFrXm1MWFo2QE11SH5BeG8yS0B1Kzk4e2VAaH13NlBBMVp7QT5RYycKICAgICdgSmV2UzBheCFwMVA5e35CfGg/Y0xMYD1HWkApT1VhTDwoVl58WGZueF8+dVV2PCVGMCNyQkNWYDkzezJyLW8maD4zaThHVWpxSDtJKz4oK1UzXzVSe159KzYwTmEqWGAjT2ZRJwogICAgJz88bDxGQVowdVM5WFBFdD49fCZ8UX1+TXhJM3pAWTIyOF99ZVNiQz5Je2Zuc2Z6YUtAcTxza31FTyUjN3EpbCYrTytfckcwY0ZxTiplcm9NNEQ/bFUoZTlqSmMmVF5hMU9XeVQnCiAgICAnJH52dF57QC1KIWUzZzxmKDMjWlJoTzN5aiUqPm5aSEJhfDxHJC1lKjVBdElRYCMrI3ckbXhsOTZFPDNwQHtlPFRtTmIxc3dfSFplbkFvSCVUMHtSdE9NMHQ+eEQtM01zMjZxRicKICAgICcpcUQ9fm8ycllXN14lRndIKEF3YEdNVUZxTUFJUTc4PjRJVGpwPV5xP1k3LURaIXZkPGxIdDEtN31TN3lFM0VuVChObFdnMDs8UXcpcmB8ZWpQe2JGcExgK2dsPzt7YFFgPGlzJwogICAgJzczKTw1aXdZQjgwNj4yVUhlVzR0d01QMiF4N0VQe2BpKkdiPVZ0ZG5jSFloVShTJXg0dkEpZ1dPOWNKPmV2X0BxXnMkQEh1ZWxPcXp4XiUyb2N8PDdmdGJpJiM/bCNMYEgzKjEnCiAgICAnQW1TVjMob3ZAYytiR0BURThKJGdLVFVkS01JeUw3QSFaeyZ3O3hCUkg5WXNBZG03PHt6Xy0tR1ZEK0hoNytHdlVqIVU8S1ZxaGhFSW1UTUtYOEY4RHB3RDwqLV8+WTNBITwlYicKICAgICdwVz8zVVYoNjQhRVAlWWxzMUZqdnVkSUZjaDhYVlpnTHRyMCVxfnJUdlA0a1B2KWZkQXooZHEzT0hMdVlQbWlwKHtVJC1ENHl8KGR7VWJLemJjKGpUKzJRJmpPJTMofWxgdXxmJwogICAgJ2ZfLWMtYGImRm5ud3hvfmBqVGV0dkkpczZPbnV8YnhJcD9OPm9+U141YGFMMyVNZmBZPHJeUloxNXh3dVJrMmomRkRrdCtzVTdZT2BIOTlvNkg3RXhjLWZ9LSlZLWFlZnByfHsnCiAgICAnOGcyMkUrc09uREJ4KHZMXng2RXFTMGxuZEBvRkVVLSpTNkh2TDF+eWFSYUwzX1Y/TWg4SllldjBjeTNqLTZhMnJSQkJGTEVBOGpBekR3cllEeiF4OWdIQG54NWFCOW9AKUR9cycKICAgICdSWF4hb3Z+Xl5iaSlmPzIxPGg0RGt3dGgpOU92VnM9akgmVXVwd0o1OUwmVllqTTw2NikhIT5BZiVLVEQ5O1Yxe0VPMCl4ITtELVExa1Q+IXMxVylQPW5ATno/YGlVQHBZb3pPJwogICAgJ1ZwTl9icjlLXyQhUHA/JDkmXytsX0I7bkBySihTLSUtb2JyU3d7MUZ3el8hdWp3bSg0UnBpOXJEd1Vsent+Y3kwLXZgX1gwaWwwckltbnVvQmowbENOZVRGWHQlc14mI2l8SEInCiAgICAnIUA2djdOK0d8fiMxcmlRcjB1PGIyOCRmRkQrTHYlZGtlPD9SJkkrZWRzYDM8SD4hQF9XJSNpN0oxSWprUmIwM2Y1dyVPKiFHJTB5RDlsUiQ+WSs3O1k3VXN+PE5MQFRaOTtCZCcKICAgICdZOSoxNng/I149THJAVUFPM2RFO3socEpLK0FUPEpiWmU9UVZpbz8xKXVTNllfdiVGS0RAbHEwI2xpazFoQlZya2pyI1ZrfDclZEA4bTN5ZVkwfk02cmp8e2U8RFBZIWtWSmBFJwogICAgJ0l5Y1AzRXRkeGJtK3UtP2YyKHlPRkAtPjhwO2kjPj1yUU1NYjt6XysqTVQ4SFV7Vl9BKVFpfjE4WUMxKz59T1c2YzN4Kz42KzdfWXBhelotSyROeHNKanhlTFp+YCYkenhFeyEnCiAgICAnQV5JZT01fiRSdDxzN3RWKEohUGp1aDhLPk82RztQNmw1WWM8bjNIbkNJWm9lVFRAVGNmVlYoaVdpME9zVGRNUFp5a31CUFJ+RHRFbCZtTF9SZz05T2lGKjE0YzUreFp1dmBuLScKICAgICdjZHdnRkVZUFgkeE0/ZWB5SmFFcGZscnlNXyZSMzhJbWVwfjdsdDlAX1QwI1V1ZTQyZSpRWEFLQEBHWSM/KG97cEVEQChHJnc8bFhvbko/N3hSOyk9MWRfY2F0cWVeXzFWN3U3JwogICAgJ29iOHp6bFQwI15ARmxoREhDJmR1ODQ9RkVwOVdPSStfKSpTPjMlVW5mN34zJTAleVU8ZkJqOVBabX1PQCU8ZT54SjJ4RUxfXkpYIXBOfDwwfEMhZ2h7SE1pakNvQ3ItJFdAa2MnCiAgICAnQitUdDxYWF52bVBDbksjQTlCIyFNT3YhQ0JMaH11PTFOTUA7KndtVEhmQmpnJnB5QGFyS21WZC1qS3hJNilnaztuN2I0NHF3d0d3TUI4Wmt3YUhsblE+YlY1UFNUME5tZExJUycKICAgICcySm1VRT8wVntsMWt7KiotaUpHMmdzan5nQCt5MiswUHZMcFlBbEhEKTtQOTRnU0R1VihoSVlDOEl4aEdJKSUxUWV7bWpQKTRtSEdDN1UpRiRueHk+KTM5dGF4Z29EJkRYeiRxJwogICAgJ1BiOzc2JTItdWZuaUE1S1laWDJyUiZVfFhfYVJDJlNSI2ZGLStrfWMockgwZTs1VzB9Y1BJcmVmKnlifSQ5eVA4MV9qSFdxNEE3JnRPZ0BBNH02Nm8+MkI/QmN5RDQ0SmdRTlknCiAgICAnKyM8QFJGPXNIdEJtISYmOHkwYn1RajRMTlk/aypgLT9QcCQ4ZzM5e1MkLXtpe21wfmg2QTBsUllxMUhrdlotZ2FEQTtNXkdWdUhHdXU8KCRjKiZ9STNob2smMDEqNzt0cTZtcCcKICAgICdFT1ZCPGZDPChrTmotMmkqUXRucEpQeSNkdFNDMnthOVRxVE5rfUwxSWpkMEkheXMzNDEpVDxlO0N4KH5YTzl6I2YrVmJZTD01TU5DbXRIRz1mZ004P3BVe1lmc0JBYzA0UUYxJwogICAgJ3BhUU5KdkE8MTJOKmlrbm1BQVZPcmQ3fGlzUkBwYHZ2KWMkR3JxNyU/QkxrSFBNQHhxLUl+emQ0WkhqeTBfZEIkcV8+I0NyZipCS15EUWpeQVY3YlFISExZTk4rdmNfZil3IWQnCiAgICAnQ2lvTCpXRX5lVSs1JTdMQUgwYTI7KnN6fFkxRHNoRntzcURuZUFaSTlDWD89bkV3WFFlPnlIQkQyUXAwR2hiKjxkSFBYRis9OFRRTVhLKlZNSk03TiV9NGp6R1lGLXlAfntXUScKICAgICd6fHdFUWdFWkxyO2dgVGFgKWg7VUcmOW1JYWByKndJJC1WNCZ6cTVgVFpwVjVsbkFvQU1uKEpNVGl5TzYke2AlbzNsZXlGVm1wdTFFQUpkJDR0RyhhPE9RPkAwPyNCMCUmdENFJwogICAgJ1VFcmsyLUp0fCokZn1rOGwtVyhrRDRleVFuVnwtMHMob0RtQnoyVUlpPyVWNkF1KVJPZiE/RjRQdTc/NnFmeUR2c2xWcWlEVUZ9KFE+dXw7WjZoNns3ZTxMSWFsUzxIMXhqSDAnCiAgICAnbCk8JVN4OEMlPGtPYzFXSiZxTUd0eTY4UzZPIT5qVGgjJC1YTGd9NSFJSWlEUD4pNnBENmZydVFQV3k/UjI+bHZuSzwzITtkKW9fej87YEEzZGVmbjVXMD9RVCFeRWcjM28qPycKICAgICdoKjdiQjIhRlhuI2VeNTFeeHpmQ3J9RWJnSW8qK3FUYCNBV0VtbTxoX2QxaWRsMG4+MVZ2USheOHs/cXlMYVpMNTNlKS13bF8jZkdDMGU9PkwzYW90NGxQN3VAQz5aPFpSXnB7JwogICAgJ0YtIVlTOStMV1FJdnQ9SzNFWmlMbjVGXjBYV3BMZjU0TTByUF5kVTsjRG53WmFhTTd2K3pfTV9zZjgjeTEwUTlLemUhfHlvTnYqTk5WV3RpLV5lT21sI0x8PXIxbj1XRmxQTn0nCiAgICAnYztyd2leUlNwa3grXyFPaGQ7PCpZaHVfLVAjYlZVNzdoKzxqZVdVRjRuO2BMSTMmWWxTdXQ/PlEyZFBUI0JiPUIqISp7MjlpISpfaG09KGk+VUlMWSkzbShZPW4qbHc4LUxKVycKICAgICdARVA4a1FLbk5NQlhvYE9Ka2FuPldBelQ/a1FmfXIyTjZIJUN4aXdBNWtoaSRTKXIoVXE3bUAjV3RFWWY5XmRGajc4IS09bnc2dXchWWw2MTkjQUBDUFViI3EwMGQoKkZraFhiJwogICAgJ04zZEF2aHZobDYlXlFkRmU+TSpjcGlfaDlKcj5CR0kmUiYwNlB5P0hVYm1AWDQoU0hSTjZBdCFYS0BtMCtrXzg7KFVpZnckdVp8RXcla19pYF9RfjA3bzNEK0M0dj17VClXKEknCiAgICAnLVRGUysrbkVrSiFkenJJJV88eW5xMVEhXm5PZEp1VmJ+Nk5tNXUyeEUpZ0xIZHRtfHxFYUdmSmJrUG0qdEAqbEc0YGElck4rUlB5azRvZTk8NUtreTJ9a2F+RTshS3hDPiRLPScKICAgICdqITQ4Z1VDNjw1IzZOQ0Y0Z01gMztabCMoQnVMKWRVYjZ7QFNucFhFcVlYd0pJMHFzX2xjUCQyPSVoZmxuJVA0U1U9bm8lUVRwTWBFaXZGR2dIaVlBRD83MHhTIyhxJUp2JSEwJwogICAgJ3hWZzslN090X2JxNVA0SURxLTEyS0BycWwkVEo3WXtqY3RuNStOJF48QCV2c14hcm45VTxmbWgrPThCaFhJP2BZbWFsTmtJZCZmPFl5YD1kUEJVV3xhc0UqQno1TEhgc04za0onCiAgICAnY1g3RTU/eCROZkh4dWZTdz5rYiRedn1JOHc+bjwoWStYI2toZiRkeDxgRCsoPXllQWd8SmdfRU9rZjRuWHVDeyMzeythVlk0bSNVWTBySCphWGtFKUJ4cG8/alBDbmk9cEAzPycKICAgICdZPVoxZyVHaDUjRkxNZWBmOWEqYmA5ZEcmMk1UZjZsd2RYUyhQNGAxc1QrR2ZedjJrNHRHRkwyRndzdTsrTjxmQVI9a3UwNT53eX5afnVndHReUTxCejlJKU1MR2whYnVSSnFoJwogICAgJztGZyM5ZDQkNGdLdjw4QncjIUg7Uy1xYEpxVFZ9PjhIdik0Xm5TcExhMDJhcUtteDdGUWhgSWxrbDJhUTlRRH50YCFvUUdMN0I0UkNNKTcpRkN3aXUtRih+M1drNT5LP3YjP2knCiAgICAnUGhHM2A1UHE+OWx6LVEhUiR8MlVBLThPc3JAeSheMGdsZCpiR2ExZSktI0dUTz1zQ19GeFlXcmIhQ3JkZ1R4QWZJZDM2PyR3a3FCKm5OQ2hKUkljXyRQOCohZWRMdz9OQiNtXycKICAgICdJT2o5dmNjUigtcTQjbERAZ0ZoVypOX2U0NGpMMXo+NFU+fSNfMGVwdT10YkltZSFwPjwwJUh7VzN6aD0zX0pPLU5ZTHRNfEtnXmhMK2taNUEoTyE5ISYzKXN7en1tV0NqMHcqJwogICAgJ1gqNkVKQjEjI0tfM0JaKHFKTVYqdF8/aWVzP3FjYVZRQ040Z3JtIUt4cFAwTXp+OUphPVJuSHdXcDgzbCVeJj5lcEdOUlZLbCZFR2hRNVQlO1c5I2hAVGRASXJteDR4WWc0Y2InCiAgICAnbzM8KUFnUVZWLU5lcnBNMUlUaTRCa2NQMTN9eHJtKXZIRlhtZmghITAqcXRvYCNvSDdrbXJqSSg0OHtTZVc5QCY5TlVZZityUmZ7QDgrQnZLdmpYWWwpN205RX0xcXpeREJgJScKICAgICc8JGF3bl5eLWJ2Tngka2llRDNoajFiJEZKVW5oVUswaUxrfUkwP1QyRk1oRkRCNW5zSDNnOTg/UXtgdXxSdz0xSGxncXpgZjY8fEhnPENhaj1Wa0l8Y2NidW5BUGpRemo0c35KJwogICAgJ1RLX0ZmJEJzaVVEPm9AIzhLVXc+K2NKdl9Zc007dHoxblBJWilgTX1gRj0pRytpKnA3IzVMJjBNbmUkQVBqWDkkMiFkVGRKTUN4TjdjP0BeUnk7M1B2OXJ+QWcxKmdWOCpZNGonCiAgICAneCEocW1NSS1OYHklV1MpRzhHQHhHcHktWjs3e3J7aVFgZnF5fXNtMXoyZ015XjRqK0dJPklOfWNsVHhwP0JOYylONzd3I0B6MmxLK1UoT31fQSo3NVpwcTgwdFZgaWQyd1d7fScKICAgICc7blR7NV9ITXdiPXwzc05RXy1adlcwXmtoYGxNNk12JUk4em09TTNvSikoKk54Tis5dFNiOXhuR2gha2JTZjVUeWJHbmxzUSRWQ3JtKyRLalNFeytPQk05QEVtanFyTVV4fT4rJwogICAgJy04Yz1Ac1p7RiUwZVNKSG5fbFgtMHcpd1duSU9rWVlvNSh+Kz9kV1EkWGE8WEMqcz9XdFM7ZyU5PCZ6IWMyeSZMaSZkVjlUPUZudU0jNnUqJjs3Wn5wSFRfWVJlI0c9bDNCV0onCiAgICAnUVpZRkFIT0RuRzFjdWQmQkV9dGlqNk98ZEI/SEdVWXN9Pk1GZTE1RzRDU1BqNH1uREtsTjFeNjcyPUxOQG9AOzVITT9nRDA1eHxYTSpmN2BDekcpLUU+QXB8Jk16TFo4LWZsaScKICAgICdLYHktVGdMaXAoSFFsdjdtZUJ1aW1hblhabGNwe0sraFVzVE9xSkFfdzs8O1NSR1p9KlRUUjNOPXJHVjlUUjJeZHM8KzYxalVrI0ElR0o4ZGc1S1ZSM0o+PDJmMXgyPiVoTThKJwogICAgJ0syeiRhXnU4PEQ1Q1ZDQWxDZnEta0llcmdtbWw+STBNKG5RVS0kTXpGek15bVc9YzhwUEJ8MkVhRGJFODdYaD5SNVJ5QHRvYXVXa1Q5ZGA0OWt4ZC1tUjwmZ2tPXkd0an1SIVEnCiAgICAnRkVLfFUzeEZscW9TRWpjR084Pl47O1lxWnFyLSNQVm85KiVnQzNhP0M1MVJtLWFDVmU7c2hhVHY4YD0lUkh5c3gyQiUyPmNffUZ1YlJqQUErNEh1Tkl6dzxOPCNufj1yRHxUdCcKICAgICcmcDFYO2lVamkjakJVciVEbXFgSjxYJX5Wd0RZeGhWX20zUFg3NT1ubDhOdVlqV1g1UUg+TjsrMzZAK0R4USY3eV5JRHx0UHxFQ0tuSWIpKCoqOWNhY2BFcFF2cG19d3ZnNT9+JwogICAgJ0deT19EYUB9Z084SXoyQz97UX0wMkMzQ09WQW1sbSs2Y2ROOEkyc3dfKnhjfUt7WkJjKURZbENpNkJtPz9RUHZzT1QoPUBWWDB8cjFjRn0+VXAtZWJvTkFlI0cwJSU8dFd6d1cnCiAgICAnVzZkVS0yKGBQTykxckM7MH5Ofmo/TiZIR3tXbXgxcVpfKS0/aXVEN1NUIUxtIVgwI0dWdy1lS3tHQTAlOHgoS3xhZHpXTVdoTGxXS3Emb1dRd3w8P2hnQWEoZmxjZEtUPlVOTicKICAgICd7aj1GSTl+SStqNztFQkJYQ059S0tPU3FIKFYkWmpHLWM9bjRnJjVJOUdTM34/ITNkXyRxZDxgPD9fTncjT09nRTZVWEh4PzdqfFJ0LWw7Q3pkfERBUCtwdTwwa1B2ZktsdFE/JwogICAgJ1l3Sy1aJGlBNGE4NkBQNXtofjRYQCNHKWw9Y2YjOGBfb288Uz1DfGtnJCpFdV4+V2BUPlJwQz4wTSR6c0REbyRhakw5S1Y7JGUpJT4xRnFuMUxDUktxUHRTPmBue3NuYDNQaFgnCiAgICAnbVFDbWU2P3J7JTx9Tz95JSt2P0ZtZyQ9YVFyJmlOWlFeSVZecmRye25ZRUF4SkJKbGgmPXN5YWdhRnFSJHdzPDY8ZjxJKDlKVkZBMnYrZT14JChMWEN5cVBNWlleUzBTRE1sTicKICAgICcpeGY2biQ9eVlwdXM9aSlYfmh+PHsxQzUld3B7fTI/fFNPNTF+PW5ELUteTmpsYWtwI2JKcmlybXoyI0lkYi05Z05xJmBYeH1qZCh6NT82THJHKDYqPiFARCRiREAtMEY/ZiU8JwogICAgJyErfjQhWnZJZUFIJSFie0A7fj4hJUtPRj16Mn5UNHtBTClpUXxAeiU7RytidVo9K1ZhXmtaPy1zP344UHh4YVMhP1JhaHtkdnBJPGd2TmppZiU7OyY0amBRbFR2Z0s+MlQ4VU0nCiAgICAnTXhubHh4KHhkb297K2tGe01pU2w5bHRBfEpPSl9OLW9jYj9sc0ktTXVNJEArdkdOLWpQMDFDWT8hZFVhVEw4QjAwNy1HYll2YkdAdjg/dzdlMVlTbEQ1RFV3I1YrZ19ZdHw1eycKICAgICcoaFR5TClTJHwpTl5Xez1wdSpsVkk9JE9nUUZzMHxFR1dxcGFIUCZMaGRnTSMxbiRRX3ZSKTRHUG9nMDVCSWg/XkNsOUhjUXU2UHlYXkVHdmQwfFVTS1FHdWdwYVc3ZkByM1VjJwogICAgJz8kJSg2eDlHKzhGKjgkOEU1dmFSMTw+I2YzR15ufDBXP25mcTxlYTFYfDkodlNsX3dzU0ZCZlFlXyljVjVwSkdfKFY7N1JVUz9FcWMyTCM5RmFhIWJsclY3KFFffX1RRTNjTisnCiAgICAnZ2RId3wyKVJCPlV4SzlzcSV6fjBiRz4qRUo1ak5CIXl6fV9jM18mNmE2RkR7RDRQKGM7NTBhZ1U7dFQ3U2B6OV5vTSlGcHMoMy1vTDs2bXU4P2tUa3lRSCE7OHxaRz9kfTFDeScKICAgICcqJl9yamRIUTYmYUYydj1TPDZAU1o4KztNSnF+Qz5BSEQxbilvcG1JeVJgMDQwISshZ15IVng7cyZHVihPODYjRUledSY1PWo3ZFo+KzJhRVRARSF2RGlDdjtMWE0pRXVLcTIjJwogICAgJ0lsZmAxIUZEeyV1WXYkUVJFKVomTWA/SzhfNHZDZUwyJDh+REVnbTghR2tsfi1kQEJYbjwwY2dgWSpKdyFFJitNZ14xUTNmVFVOVjs0M35zX3wyZCp5ezlCIXtzSyRJYzd0OGInCiAgICAnRXJFS2NXR3slZkZtbUg7Nk9KbHhlOF5WaE13dHxrd0QzKUgpTy1HYFBMST1iNGZpcncqQHxmeTJAeDg7MUEmQmR4OWFhOEN8fkZTLXMpSUdvdSp4K2l6eEM+TFJad3NSNk0xPScKICAgICdeUnFONStqfXxUNkFueSEwUHs+fmxURmlIKHIxWTlBTTxDKCooRDJQWFB+KHVzUio9XitxTSp9KkglcXU0OEZaTjFTZXJpKG5WREM4Wkl3SGYkdVltVCpLUCVXWkZOKDJTb0RQJwogICAgJzs7YGBsMGJBMi1FWV5remQ3a1I8XjR5dH4meCkteTkoJlpyMy12RVcrfWglYzVaWWdKPEVzKmVSXzxuN1dRaS05VEwoKGpsT3ghNk50QlZRI2tfRjZaWjsxZj5BYUphSUVvTW8nCiAgICAnQnJ7P0h0JjhtM0R4RXdrX3QyS3E7QURSO3R2cUVuOHsqYUdgcW0jd3dweyY9JHxvJWU/UFNsUDg+eXp+SjJHb1U+LXVVQWZKYlVLayV6SWZnSEZSXko5bGQqYUVSNnBvVjxqIScKICAgICc4MWdIPTxjZFZSel9AbiM8RjV1RXNzbk5WQHo1QDg1TkByP0FYNjRKb3V3V31wdnN8NCUqcHBvdT8qa3tPVzlkQW99TSVjKHJ8cTllNFhFdDxkOEA2PT9FblYrKT8lQVB8Wjd1JwogICAgJzBsPk85WFNqbUpjM0hrMlpaVUgkKXVqZW9AT35MNUtBK3xsdj43SW9hYEVIeldFUWR9P1BrQnBjcUo7fTJpa2h2eERmSHpTPnVUXjZVRnh1UGFFRmgpdk1HaGxfQyZMbmdQb3knCiAgICAnUyZKfjJlPEhtSHBhKWpkcEJhTyNlZnhmajckOE8mNWE7RVFIMVVIUmd1WjJve0FII04xSWhCYUVmJl5nN047RUZ0aChnfk5FJXl9O0Q1WG5YKS1JRjtGYHR3Nm4qdE5fJiY/TCcKICAgICdTT0ZzU1Zpez5GVCQ+an1BLWc1ZyN6fG1KP3N2KHpfKEtYTUg+OVNYP3xZUU1OakFHYTM/N3M8Y1gxWEQlIW08MEIpblJtY1g3JkY7c1phLV9ZYVNURmhNTXQqaSV2I018X0FlJwogICAgJ0F2QCtDV3hUQThoe1UtK2FAWWZQbzFoTytgU1NgTU1sQXhMUEMzPnRuUElqMStHb0FmXkg8VnNXYio1NnNsejUzVlZtcGAmV2c/Rmd7PjUkaHwzUjJaSjR2YG1jeTB+PElZKCYnCiAgICAnP1U+bXpDfDMkKno5T0xxVUAke1ZAKl9jMG8oajhRYiNBVmBmU2hEXnJjMUNqeUJUaUtNI25JbFMyRVJvMX5YdjdISjYlKz1CIzwmTWR7WCZzako9NWxBWFVkQF9qdUNRV19PQicKICAgICdhNG5aTlM8dnRQcVFWYnpmMnwhRE9OPElRN0YrPmJPKkFMP1I4WUNWVUk8JVpOUSpnKUx0NnZIP0RNXytNK3U7cU4zPEs8Z2tFcT4kT2cqZnRzaWN2NFpfQUkjcUk/IU1jPWdkJwogICAgJ189czgpN2BqRSkmYCg5eWVONmRPdXd+bm1EMVoyTmNyWGxGQW42bkZUKDVFRClZbSEpMX15ZzVrUjt+Wk9DOGs0ZmVOMUN4YmtLJDJST2R9PV9hZ2BPMFE0LS1jMzd8M2c4VlgnCiAgICAnbjMydiQ/ejlSeFl0emBwcWFAYXI0R2RGeiFIVW5EPnZ3K0Z3aSkmK2E7Qz8yUiNPeH1vemRPQEdRK0deTHxyPk1zQWpOb3pzR2JBdTB3KSNuVWE7aSUmMXE3V1Y1c2loYXA1OCcKICAgICc9bEh3WnQycF5nVmFjYUZvczF3PzdPPEBIUF8tRj82QipAZU96Mn57cSpYJnZSVW47LXNzPzR3MSVsTVE/IWJxUmluN15VNnY9TXB2YGZGWW0xOzY4YSpRNEc2b3FuK2BMQ35DJwogICAgJ0VUYUphekREMU93ak5FME5mTSZRZjJjO1EoXjxuTD1eITBwJEhOaVVnbn5sdWNmOXJzaWY/PERTO2tjPEI5SXE+MX13Qnd4KClMJjRsUz9ZdlphdjVjUSY/R3lSWmg3TitsRUwnCiAgICAnYDstcXItbTNOYT1BYnBOUndCS0VfeV9FKFVobnFQLXQ+SCFxbDZjej9rR3BYb15mXzFsKkByRzd3Sz5sLU42RmZZMXYyMzdRdjUtSXV7I3xFdzFWYUdpK1lJbiZOK3lxUGI9MycKICAgICc4Nn09MyNQMmx4ZEo5bEozSFBORG0hQVZ3T0ItZ3pqUFR7bUEpODJkLS13KjltXnd4eVZHeHE3MHRGOGNYMmJoZTlgX1F6aDlnfnBPY2dVaD40fDhUZHBBZz1Ucjd4OFBiRDBGJwogICAgJ2hGNjE8V0lkNG9pN0lpMk5GYnEjTElsaWZPOTwpKlROPDhwUmd7ajIqPVMhaT1qRVQlUnJoVHFGeDhzWHA7VEdlZX5DWnkmIy1OQjlwdG9JSWtZX2ZgY2lYQm9ie2Z1LTJmYXMnCiAgICAnb2BhKSM0OCZ9bDAhejl2SWUoKk8jUkRUNjgoQGlUV0Q2JUV6QVFSOHReYDVvdG10Ki1WPH4kJTNyMmtEK2hAdSt0KEM8MSsxQnFvKSFraH5yUlFQOFI8MT5aZFlLQEY+NShSMScKICAgICdRQjFRMHNzay1aTWglYksqR0p9UWhGVFkzQzshSkVNUjYqUC1XMD1EITU/WEdST1BTV2sqRFpHdGkqZGZGQ2olJU1WVkJURH1FXiQxWjlzQHEmRlVKSih8NzU/UEB0Ni01aGRhJwogICAgJzJhNFZiYmo0bytXQ0hibmFpRClEXmZqJVVIamg5WXdFWlBycHxXJD80JFh8dyhldylpRH5Id2hORnFTdiRMNldebk1gS1VMPllSdklKVnBIUGZvU2V5JGE1dWgwUk5xa3Rta1EnCiAgICAnUXZUVis/ZkdVP2RHMFp9Uz4kYkhAVklwYW5aP0BvalJjfi03Zn4qNWczISNQKkdgSSR5dTgtUmRoPUU4VForNGBJcE5ySkAxeGMxa3RYOF90N2JqNWU0VT1TakxAeyZabV5fVycKICAgICcjNi1SIz0jZVdxQVB1RE1TOzF1PkVke25JKzY2d3xSM2RoKCl+UGJ2JFV4O1opR1JJTj1fPmthUmY1YzsobS16LVY7NUZ7bDFKZGlvPnFzTEMjO0J9dH5ndXhJVzNEYnR1aFU/JwogICAgJ1QralIzUyhVZFQhck0hVkxnQkh+OSR2S2RYXjNsekAmT0M+bTx3UW5pUTlmR3tMSm5NO203e352VGZjcGR1YEYqaz9IbUtJUzheVXw0WHY/NUQoZnRefW5PZDdeUDB+eFEwU1cnCiAgICAnPnV4YWBLU2BoZUZyRUJlKyZDY2ghQih3U2lgYmNBMDhxMC1SakM2cGBUdU0pZWlVPTIlZFREb3tzP2xYRks/aGpsMXNGfHNwfWhpS2BBKWZeYUJsKz9pbD5zSjhgS3d5eEhKRScKICAgICdWeCFUPlYpWSFlbXtOV2xCKW5mUTRDXiZkYmpHRCZGRUJKYSpYWUgkV1FYSCgxdTwlKnZETyZXcns2e1B2MHdiazhCd3pibilKUH5uazdOeWlyQHp+bE1YJWNYPChXYyp2OWkoJwogICAgJ2soPUs+U1paPlFiRUs3T2peO312RDNSRyRNS2lROHFWMl49M28/UkJ2R1Z3XmcrXjZQMV5IWnRXR1ZSKT1MVEdidT9VVSN2OzN5X2hWfE02cEg/JVpVbjV0WHBiXlVYeHo0RnMnCiAgICAnNXZFYF8/eFgjbG5eQjVsOylLUz5RJVp7U2gtVnpSQlBMeWolcnRDYnU8O0Y9LT5Jek13eCkhRFc1ZUc0JCtja2hOc1REJjB8ZTEqMS0qYXdkeU13SXQxSjMyajxAWHFAaH4pUCcKICAgICc7UDJNcWFiUDNwd15SKGhPTDNALSpFST0zKlZVb313KCh9YjNhKj1nQHUhUCppPEZ9a256V0lhS3FCdWU5ITYpeXkoOyUtKmdAeWZteENXMjJNdHEyMm9uMl8pXylxfDd9c15tJwogICAgJzFMO2g5bXBKJkxYR2RMQCUhNnAjM3szbkMkY3gpRmZrMzRvNUloTyozXyReMypLdTRkQjV2MEBTelFPfkFydkZZVTFWQFdtIz8oX0xrNXQ1KCk/PldJX1AhNmhjNT14Mk9AVlEnCiAgICAnekd9bV5TfSkhdyp8JU83QmQ7S05ZeVRvdzlVUz9MIU0+N3JxM097RCZ1RXxQRDAxWHRRe3J9MHlZYz43UDt7VUM0X3ljaGskWV9PRD49WHIpaXVaI0F5QnFIYH1ZdXwzfFozcicKICAgICdqJHhKaVItUk5WXnhYS1hIeiZYNUVEMWt8Sz5hWkVxUHJsPDA3MGdxeXJANlYobGw5Y0lmc1NJLXx1UnFlTkFMO2RQY3tmZyYxbFQ9Qj58Rkp2Vz18YGJKZml0WSlfODBEYEJIJwogICAgJzNnaFhAZkFYWHRWe3g8UVpzaHEmTllETlRLQjVQVkQ5d1FLLUttfklWekhAUkY5JWg3RX5tK0pyUHlKdzlmTGxPTUI/N29DbklrcTk0P0lBPUk2Mzx5RklNI2dsdWkqYEd2eDInCiAgICAnSHleI3ZGQWtZTSlZM19BMz17SmdJJkNDV0U/SiZYX3tsdT9CMjBlWG0qbGtiSGpWNWpSZnxPKDtpSkY+NGhVVyZOKHVQcSVvYXp5PTdBeXN7ZiMmQHpxNSU9Zj5LNUpoal98IScKICAgICc7KyZheSElen1kKkF+dWBKbk1pOCYmfSRiZmBCRyk1cig8NyNkfWp8dUY4cEZxZ0EkcCUxbUB1Vkd8eSNeSTJrYCR7M3soV2olO091PHJwT2N2eG42Qm0xOEpFYTYwX3c3Wj82JwogICAgJzdVYGEzenY5ZWc7JFdBYlRfciYmbiY2fSs/Ujt4KW5iNkc+M1dDTztWby00MzVHWGk7Sn1PPzs3Qk1OST5YZFNvTENwPTVfYDtpYXlhZEpAPDRFRThIREdxMGo0JmNiZTFVWG8nCiAgICAnZnQmYV4xaXVDbHdEZWdfbjszYFdgUUBCV1dTKXlAJU9gQml4ZGI2e0lVbyZVSylodjQxLU0+c3F2N2s1PXhANEJKY14pS0hURFhqMEJYOG9rMldgbWg4dXQ0YEpjNylIJVFqVicKICAgICdwRj8xcUJXM3RQI2JZST1KXnZ6cUJAKVN2ZiMtY2xudyNLXzJUUT4oQzF1WEJZWiNUM0JYVXktbERMfl4mLW5fV2FLWStRZ2hWc1MkV2crR2xmUyhoMjM2YnBaUntDdHdQaWp3JwogICAgJ2FieD9VTj9UJVlzbmp7KmJVc2RyaTtxP3tqWCpEZ3g1UVBPQSQ0b3d8RHR9N2lnO2JxaklHU3ZKTDFTamU3QkxLJCQ0bmAofkgrVUwqLWloIzN1bSt1V2VtMjF8SSNhM1hkSjInCiAgICAnOENNO1NEPllSbjJSWll0ekRXPFdkWXdaKCRVLWw7ekNfOVYoe0RIY25gcjJ8czFDUjBrQCZtPEQxTk8pR0hYMGJfeVBfN0tHb0I+K2B5UDt7aTsoNjR4UTJ7M0szMkRCfWw9QScKICAgICdtNj5pUmo7KXJBdH5wdGp0QjtLMCV3IVlucSVNRlA2WUpWUGVMfHojMWU4YXlSaFZzJEFDRSlJKUA2cWEqP3U/Qj1LRCtqN3dsIXZgV3ctcjlFcSU0QDRkPUpmNXkhKi1qWVdTJwogICAgJyg7ckg3PkRaWG9RZjZFSDc9OGo8OVRiPTFKcHhLckk3bnFQbHBOMmxEbnZhc0haQFlJWVZuIWA8SCtILTMycWRyWXE4M1VTYlk2TlFQJk9EPE8kMmFXLXhMVV5yP0F+JlNzc2gnCiAgICAnaGtZYkRaO25wMTVuUmcyUl9BdD8zRFMlbSliNkg9d3R8O3xDOHpzeV5adWhCUDlve0ljbXNNPE5DRD07eVhwaHI7TTkqbk1SYFh+bDItRHdTT1Rfe3d1dG51cmJFdmUobTs4XycKICAgICc9SDklU2JIMiNud0xocTtONXpyYyhnTWVKbiZgUEBaRDg+WUNXe0EySEMhU2NpMDEra0okTSQ2PVhBUFcrblpxYWhhPDM+XiU+bFQka2VrVUhybXJ4ZCNPYGNEP0pnTkJLdHJsJwogICAgJ29mITBTdmxQT0FmTVVFc0NFeDVkNHNNeC1vUURPZktJUDIhQSNzTD9DPzExaUIpM1JeOWQ0N01gX1AqcDU8MnR3KXFCJTBjbyhOeV9ad2F0QSE5V34yM3VWc01+cUlJWSY2fkEnCiAgICAnUXRNUjEtR1lzKSZobWI9QF8jfllZfX5MayQlTUhMVTNiX01Mb0lwQUVJJCpXRWg0VElhY3E7ZT02Sj5DbWBIaUVkO2Z6fiYtez5PP2xnISl1I1N1VG9ibXs3VV9MdTg2SGNjMScKICAgICdOZnMxN1pKUGVXelNwNGg1UiR6KjwlM3AlSWFZcFY1JD1sTDBGWF9mWGRtNmxVelBsYDhmfTlkemBKYUNFQ34qUSV3Rl8wVTg9dXw4UjYpRiF2a3xZUkUzYnV6WHhYcUl7NVlGJwogICAgJ2gpS0BnU1dMPWJSPS17cDMqUTFvPSp3dkBGZ2dZbzFffUItZSh5QjtHZm5wd1dLRkVONUg2NXQyQ2lLeXJMNVZpTmQoKH5ybjBCZSs5Kkx0WWhxNWV5RUFERzNtSXRNUFZOO14nCiAgICAna0NmamE5dWI2fTtqVm9fMkRSd0AwNmpkfDJqVDczbShPVV5SJVh1dCtGWU9iZWNgdlVaYXhQOHtudj4mbCNvXnZJQClXb2cmUCp4UG9fRCNjRHtoVXw1a0xibmJDSH1PLTxXdScKICAgICdYaV5NKkk8QGBvK2wtTjVJTmJiamZZSU4+PU5kRUtRTUJjWCVVTG15TH5nVGdQUDNgRDlGYkFfOz44JnhoWWotWEZjUThpWjYlT1A+IXZITWEwei0kYDcwY21VPF42bzkyK005JwogICAgJyshSHpVWiVgT15QcCZuRz5xbjBwS0wxZVc+WGROIzR2bGt0cVNjfCthMFZBbjtGcEpuPzBrcXRgPCgoNHc0LXw5MkFyQj09X01mXyRgJXViRD5vQHwwPFJ4fEZsZEAqdE8mSEonCiAgICAnM3I1K05FTCs3c2pvZGNXTD1wdGxGOGIjaFZsX3JjQUFFYjZrQEpJYUpMMHpASEJBbjJFO0Fpe092SitARG92X0NyUHI3e3BnQHh0LWtQezYyb21ld2xDUmFvXz9FdTVuR3V1aycKICAgICczemQ2Szh0RSUoPj9+cGVzTzUwfE1rMnNgaCo8RzViZj9sKD1rbmsrVm1ifDVFbndPPFY0N3xBOzQ8c1c2aC1QZGgoTlIwc3JGTzR0U1ZNJD15T2xYSGFKb1FlJThqTlcjfWlYJwogICAgJ14tb3BlanhhZTw8SUNoOXEzTmhqKXtxaVk9dVhiZypLek0yQSEjSkNecyEtejVzNiUoUnVXOzs/RXJ6QDdTb0t0WmBhUSRKRy1DYSVtR3NDeE07bWxVOyRSRmprQmhvJGZQMkMnCiAgICAnX042VF96YGtBZXNBMnRAWCtmeEh3JV9iVypkXnZ3OzdUWC1VO2FvM0MpSWU4I1VfNG1LcktNTUFPQXN6NShDJm1mam5AVV8oIX4lLWwmWk57b2E3Sl4wJVhqbmUyUjdvbUxtZicKICAgICd4Xns9WXYxVzBFN1IwTCZhUzhVJVhwTE9uO2NARENxdDFwZFpsaFFlYFZobD14K2R4cUJ7QzxQVT80M19ndCU2ezF7fUJZYztqQlR0ZypqfWMweVc4RGJvMWpCI3EleSZOKHdVJwogICAgJ3prbHpJRTcyUS0mY0AqT01UcEQzXypIXmVKdSgjUDRWdnRSOHNLZTk8KnAoOGtBMiVEdU1GIWc7XlF0ciZveE41VHJWYTVRVjwwS0JVR0N1MUBGY1Zyb2dGUWl2M2F+JVRqKFEnCiAgICAnU15YUWJ3cD1LZ24we2IrVlVMbnZ0NURXMHd2dUhqaGUhK1NOcUxGOVlXM3opR3tYfHtveShBTnZQJnViTno3I0NhbkRwQHc0YnpON0gpX1NhSFU4M0tAfmdJMVl8YklpR3pVeycKICAgICc2KFpiSEplfVNGVX5XRU42NVlMaURwRjNPcU9AKFh6RTJUTzE+aXZXb3hEXkpFMzMmNF5+WVN1SUYmKCVIcWVEQz0oPlleSGhuSTw/T2UqeCFHMUY1VyZrPDQ8O1R3dCtneGAyJwogICAgJzAmQSRyPndeR2g+RHtyXjZebUF8ZSg/KSEzMEdjPGw/eFQ8JStfT3E+SWwyUXxEa152MlNHR3I+R0g8Q0tRWChJWD5PIUkhNE1lKWZhKEAyKj4rXnppdFMkZWM2JD9gPkBgK0InCiAgICAncytxKnYqaGAoTWJsQ251SEI5RW82JHJ+V1NzPTBXV3lFdTRSSlZ1N1UpcyktMmIzY1FAdjQ7UjkkPXFJa3R2RjU5QX4zWnReY1d0Z1BKSj9FZyglPmRsVGZaTGthKHJoZWokOycKICAgICdpPmZ1JmdpdWpeQmJNVkdCTEohZkhrbW17TjlNPnNNKEpCdyohYEYjTHYkSytBe0phbSk5dDFENV9FX2Q0Qn4xP1p3ckU9ZUB9RnRUN008LXZtUmg0ZXl2NSl5cFhZIWR5VFNzJwogICAgJ0hRNjExQHhjVDlINSNiWDY+dkllcD1CckVpU1JjcVZzclc4NnJhRShiTFB1P1B7LXhSbDExVT9Yam1vS1FKTXxAYU5zOEd7NUtgTWhENlYoQmVvSEEpYmBLNzhuQHA5I3hqUjgnCiAgICAnTHVFTWB0bm4+U0VqQ0teJHh3RystMFZ4IzhlKUtaQE9IRVpWZT1tYDR+WTR+bTN0e35yQG4pMiVvZlVpYGRtNWxGPXcoV3M4TW5tWC1wRGNtdVVYbDRsKThQWEBBWGI1MFFLPicKICAgICc3aD84ZkV6RWR7O2NVTWdqSTlqQWBIfGk0aiYja2t7OURSemYmaU1BWnZzKHI1JH1EIXZOIyQ+WExJSncoeTR0OHs5MmJtMjhONmZhJFI9dTN4WnE7UDRwZjs7SWJxZ2lrJTZlJwogICAgJ0hDLVFhTHJDT0BhTDhYb1VxTW1HalFJI0dVVXd3ZT87XyF2aDZOfDA1T2NpOFU5ZyhwcD88bVpkb35kUXRhVWp6ent5bENwPklTI29feHtoXiNaZEElIWFhcCZqVFNiR2BYa1knCiAgICAndnkrNmkkO1BnRGwya3ZTV0JleXpzdzZqQktNRSZBKW9GQFFvaXRTd0hIZUgrRUpkJD9KZ3h4TlV+cn1GZGNxZSZ1S0FKaEhkbDJgYDtiejx2WEBpTUY1U2Bma1BrMTBYRGorbCcKICAgICdkTSpQdk4xeFNWR3lUcDwtMTlKVCV8MmdxKj4kOzZIR01SJEx5RXZkK1Z5I3hVfTd6RCt0ZTtQZUByby1jV3ZvSEVSMEZsO25qbEgrYkNXR3M0ZzRQZXxvbXR6M0NVaGReVXpMJwogICAgJ0s9SEtyc2YkYDU1bmMtaSUlS2YxdzB3d3tIaFZQV2kjPCEyX1gkMVM0OEVKSzc9TjVZNEp6KihBMSZpQTF+VlhSKHwtNHN4O0c0WlA7dmImPT5DRyohMExTWChEcSR1Qj9EX34nCiAgICAnQiNNNGkwZnR4Y05KRHY0WldKVm9Ael5RPlR8T29mKlpUJTYhRG1+I2xEbV5pOGlVMXRBaEswaF5+QTl1XkRJK2dYQnZfLSNaO00wcU14MGhPND1kezljI3JQSnZPJSNqTTRnTScKICAgICdtSHNOKmQ4JGJLYFM2VCVPcVpUXyFSenV+e1JUbV9pTmFTeloqVngzS0B4ayRYfW8rNHpaY196UmBiN0EoYD0kX0VoVkc1QDtAKSVhSEBkR3B6bU0oNUsrTU1OPlV7SG5eNTBhJwogICAgJz5ZXzc/WmE8SHZNV1BLX2EoUWElSj92JShvPH5IQCErcm5BSXpqM1FvTEc0VmhrSjEzanh0Pj1zJU57bjB8Q3VGRVp6NDUjTEtfPj1kaiU8UzZKOVYrUTxmYEBGZShjVzB1PjAnCiAgICAnIyg4bEVoP2krQVZmUElWdTIwcDsjPnEpR2Moc2o9JFR3WDV6VVFJR2w8QmFjdFpAZzVCci0+SmNpNn51ZXd6Z3gzamUweFh2U0N3NX4xI21jdG9VWmAzTj4mbTk/OFR5MCYrJCcKICAgICdVTCZlaTRGPnpJJWNlVCs3ZU98d2x8dXFZYUY2UENvMUUqeHN3WXBDc0goazI9Q0NNT0dRNH48NGRGVjZXIXtYRGlybmgkbihNMVAtWClwe0BpXlJ3O09GUV95SEprVVFrR0gtJwogICAgJ3lHamhEJkhvakteWldAV2xucmZadC1wcDs2PG56QlpzKHA7cCFMZzcqeS0+dytKRikjUn1ySHU8VHFwQlAyMGxCZT9iOzt5bHlnR0N+LXRzKiFyNzhMZ35odHVQXjhXP051U3UnCiAgICAnQz1SOzBpMnNZXnRPJk5LI1k4PTRlbTUpY28yZVd3KnI5KnBgSDFlUlI7bWZHYG43Y2J1TihleTMwRGNOKT9IPldedFpAeVpYQDFgO0MkSkp5ZmtROVQ+Mj8+Z18jYUp6eGo0VCcKICAgICdIOFVoaksyYFd+U0loPXJyUUojMWlCbXpCMDdATyleSD1oQ3h9PFozOyZfVFQ5bnNKbCF0dDE8NjdPNFVHeFd1X3I3ZzdpVlZQan1lMjg8MS1CQWtBNG4jXmRkT2N4ZShHIytFJwogICAgJ0w5K0s0WFhZYjVIfX0xaiRPMEhqaVk2WmEoZGRFKXM0MXJfP2R8aVBXPitPYHlNdmkwZkVVTHB1eHllP1l1Zj1aTSY5U2QwZXBQKXFLUShJRiZvaXF7UkUwSTt4YVlwckF1SmEnCiAgICAnd3A9YTt6V0UkSShDRWpIbWl5WmNMJmBLKUNXZVFmUT4lWlRzQVIoY2ZsQmUkMXFmPT5RXnBWZEJvQEJPS1JHLVRsUXpuTjlKaDgjeVJ8SCVJYD1tantfey1nbjkkb3NeYk53QycKICAgICdRLT41X15YendXOHA+aXxqYlYpXzM1MkY2e1MyQURZJE1aQG15aHNfKkxAdDZZMTFAUztCMmtBUHM8V303d2VscTl+MSlPazhLZWVMMn44O3QwJnlfSlQ/Rz9YJDNDI3cqcWhzJwogICAgJ0Q0OHR8UU0qLWt0ZXteOWxhOzIzRUQydXFUMXpga1dNbil+aEJIRil0RnEhb1NpJVprZ0R3NFpefUVrWHlJYyk9d1hVQl8+MGtgenk/UFRxdXxYMiE2MXpjP3p+JWtkLXliO2cnCiAgICAnZTV+aFVtQjFWRiYrd080WmVmP1BNV1NBNUYjKHtgQ1NMWSo/WnNvSERwZjkxLVkkfmM0P3dXZW1VKkdMZyR8cWZyc3c/VTdzWFUhM0daMlY4JkJnSCtPY1JeRihlYy1gI2FENScKICAgICdwJSZVZnQ0fUk9X0QzUilnPHBAdXtkdEJ8S0RlUnA0NER0ZWkkPlY8UVNDJUs5dnQ+SW0/VyFeeypGU19Ke1h3fmpGJGMxJjJCO3Y3UFE8IzVKSjRocihpSn0pd3cmdFVJfFA2JwogICAgJzd2KV52Nl5pcGs1M1Rfd2NYNnBkaHlmcGs/Uk9teHVYPiRmPHVBOWIyZW5COWRHKFREVS1IJXpxVilCZnE0K2IpYn13biNTVjJxeXBnaCNmTnNvcVhyP3NRUmBsfDE8cEJ8bU4nCiAgICAna0d3TUxOO2M5SmZ5PmNlWDQ3RT9NZmY5RCk1eF5zJk43dy0xVU9PQkRIfURpWi1eJCtSO3JhJUZMYS1uX3gmVGwkUm5lJmFSZ2VgTDh0fWwyZjZYQ3kxe2EhWVljU2BhZC1LUScKICAgICdaTCQkWXYzMmEmMl5ebFV1ZkEzSncwMmhlQTxpTipFVk9NaUl8TDJ5Mz89MzEkWVBNRSQmcXpSaSlKVD8qcz5pfVUtOWY4VXtCK25iYEJ4e3tQQHskRzZJLShQOUk1NG5qV2YqJwogICAgJzVOQ0RXKUI3QUF1PVc/XyZVVFc2SHE7THdTSTt2KSlQWVNxVEQ3JGNDMXEqdmxzZSgoaTZqOVMtRFVKZShnRDlQVyYoJDBlbSp1ajA7WSNsfERgZ3lvVmxTdEZ2KkJ1Z3d8fEMnCiAgICAnOUspNjx6V3QhTmxjZmN1cUpkYlh4NV97fEA8Znp3T0AjTURDMjg9fWMmRSk+WSNzRVB3eUA7T09GejxGYVZKbDxOYV4rJGUkZVc1Q25Fel8xd1JaJDVPJH1GantxRlh7JW5OeicKICAgICdKdn1rSXVvOFFIbT0lTC1CbzdAQndIX3xwX2Rkd2J0VGM/QikmOHxqMmwkZjYhP1FeRCY/ZFhPNCVxc3llcyRURiVDYj8jPGowb30hMHBkcVpfV3RqKldeUG1PRnQpJlUjUiVSJwogICAgJ1h9QSlgJnhDM0luZUc2fGRKWD1GZ35lNFI2RTtUKlYmKEc0KGdPbH5ESDU7SyUoJHpyfDVjUWluNE1sKHBHZXdTamNjNFBiZm0jV3cmMTB+b3hjaGxCa2FHcVAkaWY5SlZCc2InCiAgICAndCYxWkM1WShMSnpjbmpuJkxHezRJfWBGJXN8bC1WNWBgV095Iy0pJTQoVk05VnljPnlVRFRTekM4cDleOT1mX285bmNnTyRrVj4/TWBFJiNydEFfdGZNVk8rSGhXKiYkU3lpZycKICAgICd5bjZHVS1wUUtGRjBZSCVsIW0xKkZBYzZ5cHF1K2BpR1gkNGE5MzZ1dzYjR2dIZCk7PS1Ya1BgV2B7JG9GUTk+fTJwWVFXZEgtSS1OOWl+V19XVnslNHZFRmwtVXZkSDk0bUJPJwogICAgJ0tZR1ZrMn04cEZ4bVdFNlQ3RStsMDRFP0JmMmxzYjxOQ1hkUFpZdVo3QEokYGhoUVA9IWc3elA8UH04N0VKXkRxPFk5S3tDO0ZgblMyJERgLVBgcjMmdipsV0NnQHJ4P01NdGMnCiAgICAnPFRxIykpM1QrNjNUPWt7Pmx4Q2YkWiotNShGOVZuTmgrVHtiPCtFPHJ0MXZgd2VDdWxpQDtIPTd7NSVhbExHbUU7PlZuWSlYOFArLTZua21UPV5nLTE1PzNrezJSOz9xfXl2MycKICAgICdNd09yMEd7dkhWX2RHNkV7Kk5ZQCVfQG9QQn5zfTBjWXYjV1pMV1BHeiNKVDYqcjt0V3R2NWt3aC0qdFdCO3g2RUF+dU17QU9UYnNaMm9DcW0hTiZ9OChEQGo/MncpblFRKUJQJwogICAgJ3JYNyRuRWt9U0w8Yl8maW9QcUtVb3RLTWhuOFY0O18wVkBwQzk7IVFSakBrR1ZGekxRcHZDa0g5SCt3ZjNXdmt5dy1uTTEra1g8NGYhPndXZDtXNGNvaz1EUmJ7Qk1AbHFicmAnCiAgICAnRVhxfSVDdiNTJDNiP3AySCR1Njw0RDR3ZzVSV0hOUTUwP3JsNWVgeWA5MXc9Y1o3QlU0OCttWjtATSZLKkEqe3JabmJ+YHtOOXNXczBEO3x0ZiM2QGB+fGQ3WT0/e0ktZDBsbicKICAgICcwYSYlbzdqPk1iTmopSTRHOFAkKGk3RjRtQTk1T1MrVDM8KCFEcjV7eXY4WTA9VyhgJGVvfUohUlZIYUF6cElCaHpTcFo4ekVjQkpzWlAoQF96WDg5NVMyKFVINkFLKU10STdqJwogICAgJ3VGTHF0aGtUenxCJmVBe3R4cUBxUCl+X3RINmIoYSR0Ml95QFdXbiNNc0NEJDNpVEJjPmZWWVFqPFBlSE5EbFBjIXBmcS14M3N0PTgpLXszWjxyRnNaK280RXd9eXFiJDZQVEgnCiAgICAnRCQjWCRLTEl8aik9YjwoZklaYW5rM3E7WWpXbl9GeVV0bDV4KjNvRGpPKzNCOFVXKjR4JUNlXzh9XzQwT1c4JUt4I3BVdFZvZk1QQj5iPWp3SjwtcVJ8d296OUxVWWpWPFE2MCcKICAgICdCTGJeYit6JUU2ZzV1cn5MPSNZJEx8VSZDYiEqZnN6dm04YXZVaTUkd1ZaR1c/eUFFTFJTPWtgTmB0dnhsWkAmcl90UD54ZnVzUDA3clpQS1haZGcyS1dGemZ0KURwI3ZacFcyJwogICAgJ2oqM2FNe0h5ejNrTn51RE8kTUcrUUpMKmBDT3lScjdFKH1gMiE5LUpPY2V1JnRnLUZybmlZMns5Q357UHw2Tm4lWn1EV155bEJOIzh6c0dvLTh4Xi0zYU1UTDVsKWwpKipITCgnCiAgICAnRkxTJFlsbF9lSCg/ST93NnkoaDdzcW8mQGRSbG4yeXotQ2k2RHs3Y0ZWTkVTZC08OF4tUFk9YjtWZUAyUDxLeW1sN1NLWilKbldWdUZDdXxBQGRXVWM4JldoMEBAdmlFTiVvSScKICAgICcxbkUxKz9LU290MD07MD9ednpwP2A4SEFGZ2YjRjVsNlpHZ3pqZUAjVVh7NndjSSF0Xnp7bylgSHx+JlolM15mckRKenB7UU5WeiY+aiVEUG4qKFBqS3hfSXNEIXheOVl6Kj9KJwogICAgJ2dvQXM7dz8zcGV0VWNeeVRiXyFvT357NSlORCgxaUltI1VKVE9Kd1FaQkpCeSthRVooZHdUPyRQS1otKjBDOGNUPlc5RkBNLVYlant8dX1rVXwlIS0rSVhrVUkjeHpKdUVsWjcnCiAgICAnYGhFRUBLUU5VK3lofGI2MUBrOW15PjRKZ3RHO0t2KUNkS0hjaWd7Q29gan13ViYxPm10PE1ZO2MjNFBpYm9CT3VGT0YoX3h4eCFSZ3NwNlBrYHErY1JOcT1AMD9vZ3xKKT4zSicKICAgICdNP31LYTJjcnVOOCVAb0p3S1pvY2J7cikqSkZPMGk0KyRfRnEtJilUeSN2ZkczNllrIzJiQ2c5bip5NkNKYnVfPClnMy0wSWxkMTFaS14rMU8qKHVPS2pUbURnPUpfQGxgQWg2JwogICAgJzl4QDE+KGAmRCZAUzEwMCZmfnppZzAxe21pTH1iZkRDZXVfIXg1bVFRSFk3aGhWPHhIe3R5I3A2WjY0Q1Axe1hDYFo1ciZSYmdYIVUrRCpYczhPKmYrSnhhZkAhPytSeG1RMWknCiAgICAnbWMpRUwyRXtfe1BvY35saDE+ZihWaFc/JEZ1czY+dnRwWDtjeDFtS1R4fUhAaERQe1JWYXIwNlNGLSs7VUMrQCVaLXRhZkhVJm81PTE9MipqQjJ7NDQ2VU1xQVFzcl9eKS1ReCcKICAgICcpeXw5bUZ1PDd4aVFnQigqTW02QjAqPnlWRkZBcnk3fVl5fExONCspPXFpaVZTdDtCVkpASG0xZ303K2FgZD1oPzxfQGZRb357ZFhmakdxeTd+QCNKWUU/ZldnbXZzKzFVQXU2JwogICAgJ3U9QigkV3NQY3RTMlNwdzxpPnVjKlN7TEwjVDdaSU1rKTFLU30+Xl8lST9qNE9wSyFpaEJtVnhGT0xHS2l9ajt8WGtySFkkYyF3TzEkQnBaTXZSbmo0KzZDM15zaFV5az9OKjgnCiAgICAnPXp9dXIhc0tDUUUyMnJAcmlzQl4/OWghYzdkdXdLSXBvJGttdWN9Tk8pSjhobmU3YVYzUkdhcVVBSkpLanZNTEpwYVFtQHJHc3dATWNJXjdzQFB3KzlnRGA5Qz5OP2VgX3MrZScKICAgICdrTTQrZEUpZ0RBQng/dnNzSExTWGoyTy01JGlHRzFORG1zVmUtYzZFQV9QT3dtMyFnS2U8Rz96RU5ubiZ6PyZhRVBtR1lWSkQ1ZHltbylscHtCcyU2Z14lP35gOCt4YmMmUHg+JwogICAgJyt4YTx7RThTbFItZjI5OSo4PyhuTXVuMm9JanpPQzxyRkUqRWF3NlFTVit5WUJ9cEkldU0zYU9UX002Vkg0USlFd3NURjQhJiFMWTlaQFN0KzFmd3UkJWIxZXxMZX1GaiUkVSUnCiAgICAndGtPWS12VFIqO2g/Yj5GMGQtI2kyeG84MTJPeSk1LWBZWnE+I1F1dFRUYlVGPmp3RWN3NTlBYj1ycG0qLURMX0hgWHJzaGkzQVJZN3JfPj1YQHRMM21KQntNdWJgXzYpTHc2bCcKICAgICdqcH5ndTJeOXJsRSF5PVowYUszZjN7SGFfYFNtWFQyfGVFd2Q3MlJ6PGBIcjleZkJkfl9KSnB9Q29iVFpZeGJhakVTZ2EtIyFFJEo3I041Y05xZ3R+RCNWfmlSNVZxUjZQdXJ4JwogICAgJ0dLQnJPTz0leyQ4JD9MWiMxSDdSTW9VJlZxKV9wdjlNKzA7Vjw8UkBTciZiK01fKXhqTHI3WnN0e1ZUMWxyQjV1WkxUd2wlY2cxLUotdU9xbnlqSGBzVndUeztEZnYhJXR4aiUnCiAgICAnZXolN1FySz5lbGJDX31ocmh4RXpVTyZpdno0V3I/Zis1dVZIO3I8dW5DYHVsYC1ZMmtlRiF8VUlhT1V9UjYzZDtuaUNReEB3RnE4I2M+JkRkZVBocDA2aSFxbjFBNiVSNUtySScKICAgICdlSmZ7QzZnZUdzWStrUVByVkc7ND8+bylmSCFOJHtQd3x9djA5S21BVFFPX3dEO1ZwdjNXRFNhI0ExfnAwfX4hZFU7KmpCVmckZmVEdjs7VUhANDIjNz03RlRZJGIhRXhzIWkrJwogICAgJ1BkT3Q7ayVFVXxUckVfa2l6Vmo9ZlotRylLSjNCV2c9VDUkRXRXa0lZflFCSko7MHhEd0RFeDVJNj5wb3l4VmdASGs2JFR4KDVSaCV4K3NUbnlPYGZGVD84OSsoKE0hOXhqV20nCiAgICAnMW8oTUxBWW17ZCFXPHdtJStAX1BnUV9aNENVKGZwQyZ1V2A1PCFGNXwzU1decGpZWlolcyQxS1o3Iyo0JSl3Z19mMmJLZDtvcFc8KDxfWFpJTF9vKStAN1FheVRhSD16fFg2YicKICAgICchMXd4JFhBLV9SKyh2aT4lcHtwK3QzZz9nRmc7MG8+K2EoWGpRMztEen0xZWRsIW85aHUpMjQzNnRtUHp6ZjIqJV4zYTd1anI4PWJIQlhfQC1EY3BaU19CWURhV0dfWUFHV1hQJwogICAgJ0hEVEV7OEZNQ3oxcH1NSGokYit3a1V2enRueU03TXdzeDcoSDlDeTVfdlopfW18RT8+UyUjdChTKn5aVyNuSVY8VFNaaWNuX2VsNG9qc28mezYxaD1DYCojZjEhcTlQKXp+Nz8nCiAgICAnal55Ykwrck8+QyFGPk9OTVpIRnc/KStDP2g+X0RNWGBoUHNPaTIhe1FyMD9HbDhkXl9qJFhzKEw5fiZuTih6RD5eTlp6YD5kMCpDaFV8bDVKSEhHeFJ0dT1QTmd0XnBPPi0lSScKICAgICdeKCtfMF5MWGFTIWNuSj0oTTM+fnlpSUZhPVk4Q2kyeHtkbGpXR3xec2ROc24mcUgqQT9wfTBDQUZhaG1DMj5uRGp+JGBjeXN+YThIME8wRUljcUlJQD5RTGp3NDBDNENVKDZnJwogICAgJ2llSUx3TSg5UnlBTmo/Jlg4dyFuVyhGUk51czg5Tl98ciFAKVdARD02Q1d+SzN1c0U4Kit0XmZWVUhnSWQyeyVVdUVNXz8xPS1XUzkhaUVQWGFuKTJRcDM1e1YoSjteI1NmYksnCiAgICAnN2lKRmMmcG9uVHBnZ2Y3ZmohM1lqMk94Q1Q9NHJxNSk8NHJuMXgrLTFmWl4mZ3U0QjFweldqVXZFRjQreEg2TU9fJG9ARUo/RFZsUEotO3VPd19aPVJRQmpqd2dgZXk7JTcxdScKICAgICdZWCtoSUkoYzdUP0FEdShxeiFUPjVFRCVIVXU0R2hKX1dsPmBDJjN2Zzc1XllFWmFTfTVyWXU9TVNBSUZpdyo5YGxjXyUmMX51dDFFbCRQK2ducHJjMH5sbHNtR2JBRjZyRl5tJwogICAgJ2V7SCtLcH5SIVhBeEd3eGNgQldGZytldzc3U04mflU9IWBpbTNEdiZNXjM3MSlHQXY1dipye0lYPUplemFTISptRUwmV0wydTJMeFlBP2RHNip9eihxUWhAWE5hUG5lcDBqJSMnCiAgICAnSXRGX3toZXtRcDFvRUQqeklEfVgmbCYxMFgqO21MUCU1SDRKflAzYXk0ODRRNTQhfno3VjhzRnkobXxmX3AkJWpPXiFIaDMyV3QyKn5mTnpLVHlOdzV5SUleajd7TzYzdzRuSicKICAgICdtJExUNmtMNSlWdmpDYU08O2VgeDxPeUt9T3M3bSghR2haNHNJakh0O2B2eVJgZlZ3c0YpJXBAcXVVdXstdih4dDA8eEsoS3tPb05mUGEtIWdBSWRMZm9nT01uI3w2IVc0MTBBJwogICAgJ05ufHQtaHI8SShWUytPT1VGfEBCb3V1MkNTRURMSyVLPWAlc300SkwoQmk8YylLbGZSV1pKaVglP1pUc0hwc3lZYU90bTJxZHRtNlYjYl9+SCkhOWgzQyNwYW19Z01GSGFBMkcnCiAgICAnVHhGJWJgI148MmRVZD9PX28hRHVCfGhCKmokVjhjMHVwQldtRWAqZjlnS0dMZX55KkAyPSt0WEotJnw9VTRqb3Y+QDdKMzsqYzV0MWtJb1l1Ql9kQkJSZzglI3BGfX4mTTxiWicKICAgICdqPjZoeEVIcz9CbzRofnhzPnBCbmhZUClHWm1yRX4oQ0hkQ0FqeEBZRDJaTFl5M1I/NlZgbnlyUEd3eFpAU3wkdE9tLXp1TUZzNTVNSldZd0Z1RU53ViglXnYqKXspM3IkMVRDJwogICAgJ3dedzRxNVZFcD5PbmFNfWR7c3cxPnJlcjhFVkdrQCRLZSFAR2dMe0ctYW8xeXJLcHVeWjx6I2UxXjBGWlBHWl5sJFJyMVU9SUFlUzVtZHtfQjtESFNjeUohP2ZyRDtCd2x3QGknCiAgICAnd2Q7eWZVUXtyKHduUXdlMHczazw0bVFzPHorSWE4aXJKU1ImI2ZEIWxHT1F6Vi1+cDdCNnpSaFIrI212SWNtWWZeQH0lWiZYVTV0eGh1TUBARk1eWitzX3I2PT0qS1lxKTFtMicKICAgICdqJkAmT2JOZVJXKHRlTiZyXmtBUik2bUJXdnFtT01JSCFlUHIoU0JQVSF5aVBnWXR5aXkhNyFWcjRFNl81a3NiakI+QFFMJm4tIWFlJj8/WVFiaz41Plc0UXxre1hEbERvVTN1JwogICAgJ1l+VlB+em9adjQ+S217QEZQcXJ9QXNxZ0wkY2d9UHRYZSRveThASzJTPntLfWteYVRJVyY8VTE1Vz02X0Y/eHNPU2FARll0UWJKQkJCZk4oU2xkNmlvMEBeQTJaM3JDa3hrJmUnCiAgICAnRV92eHJkOCNHKC17WmFORHlQWT9IdnpiMzVCJUV3d1BfSThVR2pfKXB0UzBrbmJZXiNIdmdzPTxHVjdTMT5HeXplQEpuPSUzUVFtcHNwfkNHS0FmIzt4NCFgTlQ8fmVSa3BrZScKICAgICdjPjtxT3c1THsjcUR7Zk9jaip4KiYkS1JTdzsyZElqUj9UKGwyUGteczJ4JllSMlFRX0xSI3dNUGFpIWtPaW89YWVZM0leWSRMQihOcUhCYDxObmp1WiEmRUpqIUdsX21+VjE8JwogICAgJypxYnUmKlpre2t5b21YWE5XV3IhLX0tempJcGpXX2g4ZXdWNEhWT249UXt+K3NaKGlld1JwSVlibk0wWl9JSktMU0V9XnJve15NeG1nSyhyPXQ1JERnTmVvYW5RNmFxWHZuJEAnCiAgICAncW1zdVZHb0xKWlEqMTY1NVAmaEE3d2pFc3FRLVhsNzJXailHbldIMiFCbmJJIzNzbVlhZzBTNiFQVTxOMWJpKnNMQTEyJllyTXQmMmB6KEJUdCVVQj1AIWxVS2s2bWZKLWBRbycKICAgICc2d0UoNkpNWlU7ZW5VS14xX1YzMDhVSWZvQnw4Jl5DTyZncEJKVDRLMkN3Kz5CVnZxP2YwNGFeZy0+K2VeMVlPazJubV9JSTZKUTdaOXFAKzw0K153KmVlX2l1dkMyaVMyaFFPJwogICAgJ2FoQXdfIVJlbkg7I2ZSVEkzNVooe3k3I29mYSRqPUpgQXdueCZ4RCQrajNEWFJebGphPDlmPDl6SiFUT3lYaW0lMiFDaGl5aERwNkFMeklyaWc4ZCViWFA2fkBLKzBuNSpFcFQnCiAgICAnbUwqRj9abE0oTyR9ZCNNI2ckS3w2UWBuK21VdVBmUERnNCo9YHQjKXRudUkrTyhtM05CQFNRamhXVWwxYWZ8eV5Hc3ArMHF8UXQ5ZEZ0eWI0MVQlKHU/XyVhZldxRDJ2WSVlYScKICAgICd0O0lGbEo1aW4zQzUkPSpPRk1Nanp7OVJaND5sUT08VXw4STlMdTcrRX07a05vRWl2O0peeE9zUj9LeEFaRUh6Zk5We1AoJCFQKyNUc21MfW9UODJFaGooXypTakspa3AtZWo/JwogICAgJ29iWnNhKkdUR31KbTtaT2gmPX1iSXRCTXtHWipmRD9QQ05qS25GSUVKfmM3I0JUTn5NczlEczlwZUBfVyRYMD1pUFhwKkMoZmw1UHdsMFkmNTkxZGFyYmdPIzNgdFZmR2stOGQnCiAgICAnK1pQeDBHN3gpQTdzWj5IMUNnSVgzRFRDJGM4Z0dSSHF2eStkWm5ycU5mRSMyO3V0OTc4JCF9dWF0bVU2OFlFRygrTWRFTjMtP0xGMiY9aVYtISMjalpJVHp0NEdRX012TGh+ZicKICAgICdoJmBWZl9VPUF8cntPJWdBe14zU3pQJkRwQTN5NFVSQnFfOUBjOHx6MDA0QT96X15zbkhuRzFZcEBkSHAjXmdOaUMtYUthKWkqdUdlI2NNTD9EKXAkPE5TWnIkP2ZqfnpHPFFxJwogICAgJz1jdnlxYjMxbEdRaTs+STslTz1VUCFAUCh1VXZyQG4jV012WkNKRGJGdzc3YnFfPCZiVTErPnNFcHohSms/IUdpcTk7MkpzcjF2aV9wZ0RTYmcla0tPT1l5NTFPaUpOcEoxJkknCiAgICAncXBPPjhyfVpmV2huS1p3RXNYV0BjYCM9e15kdTllQ2gwc3RNfkk/djBlT0t0REBxN0lUVUU9U2VSdE0zeUFLfX0hcD9aYj5XZHNsJE5odF84bjlTcWhHdG49Qihldj1KYyQ5VycKICAgICdTLTYmT2dWR2xFYVNIdUY/IVF2XmRlVCZIbEgtVVNjcUZDO14xYFYlNDI0SV96bmpjVCRuRGlqckNYMk5vTU5pTjkhI25ZemclI2FDbH00MzwrNzQtYGlsb3dAYXUmSnVXWkdGJwogICAgJzBoPGA9Nz4xUUgoe19AQ2JvakMmPT5yZDFATk80V0tyRVhPPnp4Q3pqMUo5ST5GeGw/TC1rKHdFJXJrKj1QWlk1b2FjJV9PWH1YV3U5QyFVPjE0d0ZIeX19KWthMEw4dz9gPjcnCiAgICAnUW4tKHtBczskeVdLMWhsZ0w5dCZvM2NyN3MrRUhBLUNfWGk8THA2KkBycDAyailyUGV4WUlRQG1yY3coQnJreE1EY2JQUDNzMFYzclZHSzJHcWJJX2BtTXlScWkxWmNLel9vWScKICAgICcremNIKF4tKT9YUU9HekBgVj5aKz17UE8zM3hRfE5wdzFnMThhUU5YbE40Myo5RUleRXE1Qnh7Jm8lZWJRP3QhOFduZEZ+UzNEQD5lbj01dHAyQzVmZkIyVlpjVHVaYz09NFNzJwogICAgJ2R2THMhOFctKVdKZ1phR15Zb0kjYW9vdHhzSFFiNWxqNFF+Z2FWeSNqMipFfElZejZOZWV+a2t0P0k/R2soNz0zYFFYeiZRSF42S25BYjZBN0E8NUhIMTcqcCRscU0yampySFAnCiAgICAnNSlBZiM8RXhYYk5II3pTPXp9ZD4+YFhwV2ZqNHVZPDtILV5iOWgoJCN9UmUzTkBYYjY/fSpQNSYxMFYhaW55a1AqYHE9Q1d7R09ART5CakBCKWNuMWBNQGxQT2IzVnU8S3FibicKICAgICd2bU9lcHlFdD08cjZoWjlTMz5zKlhpOSExVGg1ZVZqNGI1aGFtNyhya3w/Y0w0V0I/NDkpcys2P31tMlNiP1BJcDN0TkJjNlcpdDd4bEF1MmpPO2EoQnZGQyhRQl5qTGdNQilzJwogICAgJ0AxTDNBKC02ZGYzNEM5UmlDNX4lbkRmJlh7ZFZkey1peCNDUHVFRCF1NENSWChQJH4/RGFZX0g5c0d7V01pQlR3WTJYclMqTk8lJFk2OEVhRWt9Xz80PTFHQ1M3cFIlUChKWn4nCiAgICAnQF4+S2laSSRnT1pvdkN9d2plTlJCQClVX0YoJUM3Jlc3eXhZSCpicjIwYUl3WWUpSyVLZWlkTENUWG9XPCslOUFYYGxEfCRrVkl0cH5KKkJNdHJXI3NCcmEqREt3OTw9MiFKaycKICAgICc/Y04rRCp2MnB9K0Y7YS1TbVUmO0RJQlo5YDZBN1dIOSN3bEgzJXk4akclSSpDQ3cxVTVjKSh4KEJyTj8pKnBqWCp+aF9KZ2Q+KzF0JXJJN2FGNUskOFVtYE5lU3dAWC08O0QlJwogICAgJzYkMThFMGpQVEsoa0NoaDZsaWxSZmIodiYydmt3KD0rRVkqQmNDN3JyKHpJTD1uUTBuKnR3PDIxNz5ab2hVdUBpPz9hXnNFJF8qYCFwbGdfPDZfdiRId0Z4bnhkSyREQXowe20nCiAgICAnNkEmb0txMGFfNHs2SG9VbEcqRjI/SFJeVTJNfDxPTUlEJTIwV0dXUnI/JShfSTx5TFdwZkxEbTF0LXJZJlNffkdDLTRTJnh2cWVnV2F4fmk5eDVXekpzNXM2JSNLPz85TUgkQycKICAgICd6SWM5WT1kYkJta3Nla3FWZkRSVyNVUHsjX341Q3JpWTJVbXtTQEsyWiZmbU91Z043N2p9eStFRnFWSF5jVTs5VVhzNSN8UktwNU4/YC1DO15JXj1YTyM3PDVmeyhzZEZRdzZqJwogICAgJypYNk1eLXNVWWVLLT9RVDkqM1UqS2VyaWJhZmBkSkZUcStZUHA0blhMbihJKWo7PlYwWklQRWxweFFqNVNhfDd2ND8pbF8jazRzcmpeNnU4X3lTI348YEdXaSFyUGFCKGR6WWgnCiAgICAnOXBWVjRMczdDNDZFdHk2PWI8KWYlOzIwP3BOd3FYN1hlZTUjbV4tVyhSWlc8dUVfTzJNZXZPP1BsMWtFO0VzJWtuVjcmcF97JUxUYXhfUnw2fnZqUSVkOHVVa0ApV1JuJW9fUycKICAgICcoQFE0LXJMQXVzbzI1UlgrMjBSajkkUjUmezhtV3g3S1duWnVGO3p3ZWpkdDwlZGdvNl9YbyNrNCM1NFZ7ZStWfmIlV21oeHcrfEVscFNJNS04Zy16djdgR3BmflNUQD0wRSghJwogICAgJ1Z0P0hoTko2YF56PVUqcXpRUHZuKGdlRnhlJFkqWVJYTG90MFJVNzVsUVFGYkxwXj00VSR+aVQ3JCh7VlBHdk9mUXdIISZWI0plKFFldT59JCNXTSthOHUmPCEySjQrMXp3Iz8nCiAgICAnS1Vacz8mT3IzMz84JkV1OT5aRj4pYVMjNVNEbFE3ZGNzfTw2aFRsZmZ2KzY8SEMyPlBkM1ZVQUFzUCFic2g5VEBrYWBUaSpQfnZnNDx1OVNIc1o1WW1ZcVNUa0FKb21SeWFreScKICAgICdkcGxZZDF1dzRAbSNBazRhcEl1QmVwYTcteXFCd0E4SEI4SWIwQDVaPGEtMlZVMUxgNUB8TjNjNmVIIyVeYzdPbnR0MWRMZUpWbUBibEghc3F4e2Y5ckxWSHhFaTROcElYYDFCJwogICAgJ0xOMUdLNipDY28lS2BoY2Z1PVFUMjc0YE8oS21rfFZudXtyR3c9bkVGSCZgRkQrMVQ3TFg2cl5kT191QV9PXnFSNiomUylkQDR6YjI0KnItQWQofEcxT3pPPyk/cytXK2UmQGUnCiAgICAnNnhURndUVWB1N0txcD9TOERHS0FtezF9Vz5qISpDKzE/dTEtT1FhbnkmP2B8NXs/ZyVSJGZVSihDbSM3YVo4ajZoSDJFZEBFcSVNXkF3RjVsMD55OVc1Jlp8QEhfKTMrI01qdScKICAgICdAajxFe29ab2MoYWU0TjlqcSV5VzQwVUlRWCVsamVFZGpePXdxPj8hY01vKUJ2fHpEITNqJllhXyk1aGw4Yz5rTyt+P3F1RnlxJTI/d2czJkFTdGl1Un4mJTxKYDNEZkZ3V30/JwogICAgJy16eVVTZU1pMXc1bSFBb0k+XjY8PElKb01AYHdHI2JiS3BpK25nSHFnaEVvI1dXP3dNc29KU3FWbjROY2RRZmIwdT4/eWJNMGlTcDB3WVdmO2Y4K2NOeV5vcStCeWZqMSFXbzYnCiAgICAnXztscGRydUcjWEQ5fVBJQ2NUTHRVPTReWm1tU3xWPDhpfVJraTx5TzY1ZiVOPGJ9PmRpLUJKbUlmeHFDbDUwNUQhYHVwNmVSYXMxTFFvamdyYjZeWlA2PCZvKGhxfk83cS19JCcKICAgICdWVnA9e0l5Zil1QWs/YiZAVXozX254WVZ9bWFDX0Y4aHdSYFBiP0RIPTBhbV5LQmVIJVI8QVpqMEdMVSlgcGthaGBKUkN4JHZ+UkF6N054S1drT1RZRlZtWFlkQjRvQEsocHs9JwogICAgJ0w+PD9fc1AjYmplfj1tNTQ7Qk56OFYxUUIqRkxnanZxJEViKXA0SjsqfTR9ejJMb0lFR3koTFcrRktTY15uVG9VYEMoUG1ZI1ImPjZSZz1GTkN8cCQyaGMkKyZ7YG0mNVVfX3MnCiAgICAnaW9Jb3ZDNW0hTkJjMG1URkgtek1jNTdgUko/NXdGd2s9bXloTWkmalMqUVA8OyV+IV9Se08/M2AzRFAxSTlVTyZwQmx3ZEtCRnY4eCotcW5jb3ozPzNnQHRVOyVNZHlNWmdPOCcKICAgICdxfGxvUD5tKGApVnpqPUZIdUtBJWMxczB3LTtHY2FSKUV8cD1DYFp1PSsodnxWRWJTJDk4fn0ycnJLT3J1YiYrdUh3RjMtTzFtNnlERkBvcjVNTyp4ZShecFZJIXJoSFY9dk45JwogICAgJ0MwSE1NNWhLTkU0Z1MoRygrYEdUOFJmZ352Kyl0fEtNMClwWXktQz5eQHRfP1BPakh4ZipGdy09OXstT3BzSG0hcmcja2F0fThPbSVae0ZBeUpjVjd7enxBaF9CI0AhVmo3dEYnCiAgICAnR2lXcX1lOHI5S3tzZy1OWjtSbmA8LU8zUGNQNClfLSRAUiskVCFTcWdlPTRqeXBUKD1PJnlGVHVzZ05pait3KTNRckpabVZsYml0SDE7Vl84cDI5OWUwdyE0en4/NippfUlIVScKICAgICdpU3tzfHVBSjB+RWtfNnNKcHFVPXZaQDxyP31od2spflZLajJRZ3Z9THtjTmo1RzdtfVdBeXReLXdZRzxwQH01JkYtUz52dkw8K3xnYFBOYWFQWUZudn1CPllqITVCPnh7UEp+JwogICAgJ2x7OXcmKk05UzFnVkh4SHVadSlOZWojU1RmQ3QxalVOPngwLV9JWXtmRlJ9Ukd9d1BNejclMShySnA2bkQ/I1hJdU4kZnlAc3VgTVcjMkdzVkUlSnUrUV8lKDltUkRpP2xwYn0nCiAgICAnPCNoRDFvPXh8cjNsbm5xSXhpSypXRGY+dVpFK0FraHBodEhrdEtacSVqaik8dTZnV3FSYDhSengyRypSISNmPTVkJC14WTF5NnhVQEJLZCRie1lhSUtSWkZvc3VkbXNvY3p1KCcKICAgICdWWlNPJjt6KTtsQDkqamRkaGohYXlzUCY9JlVAZ2k0VUYzSW4mYkxGXn1SPkRBek1wNjQ9THFeP1VLVSg8ZUw0ZSNOWSNpQjN9TTJXJntNOD5GfU89OUMhfEZQcDF2M3lVdDk4JwogICAgJzJKMGhTKVAxX3ZxQXU9RTlgcHc7QUc0Sj4xVEkrJjtmJXNLOUZ0X3xMeGA8bXFkUjRXQm4od3JNfGBYI0xmdVdyPkwheDdkNzUwM0dRWXQtY1dnYW49KTg5dE1SSVNuV1FoSjcnCiAgICAnelF2aEE/Tk1CaWIoKz4xSD5aU1dkX3ZMWT9eTnBsSm5lZkh4TGZMZDNKNn0lRX0lR2hBUj5EMUZHdWpzRXhgWng2PEJmUD0xY0UzcHc1QTxMJkJWN2taeCVBTDBndE4zPFdVNScKICAgICdVeyFFJDE1QU9FdFV7dlc7O0tSbHlTSGlsPz0oZkROdD0oJWJ5I3VFUT1yKUlRU0dCfT92djc9STFefWorPmJYOSVMcV8+ZnhnRjVZfWlFclc8VnpAK2B3bXlWS0ZjN15vUlpaJwogICAgJ2k+cFkmUVZoTXhjS0Z2VmxZYCFkYW1pVi1JK0AoS1lxKmg3VGMjPX5WWFBgSjNjdHZMPmc2UlIwSntsKFp0e3BeanE3WENxJSY+KDhSb2ZJV0NEWCZINEIwS2opO3lQPl4jIzEnCiAgICAnKmg4KE0wZFhrVEdIOGduYEt8VUBGaDMkQnhhMiZhaXU1WE9VLUcxXztOZz5YUWR0ZSFaVmheOVV0dldjPjcjYUcxVzlYMV9RaVlDZFJ1clNZJFJqKV45RX5fI1EhRDthbWcmeScKICAgICc7JGdtayleOXR3bXIlRE5UWEk3fTdzYnZ6Q3R0OHpBeUJkaSFeP0tFRUI7Umk+NShSJTgpPExRVEY5Z0A3SElWSENXemxTdyotNVdgKmg5Y0tgTX1uWTVSYT9HJXpJVF9vbWYlJwogICAgJzJEQH12PGdUPDtBPU0ofSFVNXBSZXVYIXRBTFZJfjgtQElzR1p0MXVzYE09d2c5M1ZrJnFea1ByVlFFKD4oXkA/O1diVTM+WTNFK1omN3xeczdFMWEkUDhEdipIQSpRPyRoKkQnCiAgICAnYT9hPEJ2JVVrPUduMiozQHdrRGdGLVgjRCg/X0E5QkM0bUpWI195eCEtdHUjTik5NC1PYHlOakBlUF92bEZ3Y0lBVWNeK2h4RmVnWE5iTz95a1NhbVpifDV+cno8aTc+cWg+RycKICAgICdfS15qdElqJSZJPlYzVDJuaFZganA/ZmRkNEUkSiF5TTJhVlBfRCM4JD0rSWRTcG1Jak8hMG0jZmBwPU8wLWh7QVErPT9+LWFoRk1rYDZtKkdFQ240YD8qckp3ajNCaGpNKytyJwogICAgJ19Se3p1Z0txdEI/TS07VURwOGwocX1NK3FSKVh5P0RjLXJOOEx+IWc/Qz9zQjw5NTd1TmZVZj5Jfi0+Uj5SME5SJkFSO3hpbGsjJVZrPVN0SWFDTkd0NllUVUxLQTJvPW5KaU8nCiAgICAnKGRuOCV3Y0BTKEVEV1BNazVaajxxe2p5K2pzYGRnTWNFTWFiJTJKeCViK0NQSV92Y3Zrc0RXWj0/RU16cEttcilQOVUkbXRLQlckJSQ5NTR4KzJ6M2VKNE1gLWl6SEJWYmFleicKICAgICcjWEVRJChhfFBGdylSK0NHPGJ7fmtibDAwIS04SDxoRyVDbmpaYyYyX2RHRXVIJjJzKzRabDEhIzhWc3RmKSs8NVJkZlAlakg4SWR8SHY4JUsjIUQ4UHIwJkBWZnVOfk4wO2lrJwogICAgJ0gyaiRFNSNaK05XTHxEPkAofjkkbXYmfk08VGBFWEhWQUYpcTVRNWRydzNATkRteEJUNldvYTkqcCh4RT42PUFGJkJlQGkjMiF8XjB1PlhVeXkqKkBsYUVVTmMwJUJLeEtieDwnCiAgICAncjJTczFLdGBIV24malFWP1JlbnV0YHsxX0xxfGYmWTlaaHk0KkRAQiZNQFNCTm8rdEh7Q2B4Vj4wMHslJntOOWtGZik7RXY3STQ+dUsoPCRKT243JDVmbFptUXEmMlB0P1g8cScKICAgICd1NmQoV2kxdXVDJFQmZFRMO0RmJVNnRiYtOGZGP3d3V1IkKiZ5Pjd9K2ZyZj5GMFd1PWxteVhxa0otb0I2PU5nUy1hdz9QZz80JCloMzYtKT1BUFQ5KHwrTWVhRF9qLUkxN14kJwogICAgJ1h+dSRnKTd1diRad3x7YHpxOUB2WTsxWGdkY0A9THF+NHhWWnpiRmtAWWxzTEw1WTk+dmZvTy00VUxYYkpISjRPd25OaV8rKHBYMj1BVExFVCtKTEBYRXY5MldjKXs1XzItd0MnCiAgICAnNDk4RSMwdCFzYXJaYHY8SEFSe0wrTVVXYEt+QUk0aGZ6VXJNI0dQSEUlTnArVTBVYWc/e3RWXksmT0s1SSpYVTd1O2o9RERtS35+RG0kYypGO0RJZ2s/TCNAJUdjKH12JTkzMycKICAgICdjUFJVYD4tSkAoT1VLZiNKR2RvfHs4JF5ZN1RUVUlERmJvZml3bHkreStPMVZVQUVXbj5JT2JlLSgwX1pSM3BLYj9JbnlgZzRjTFpgfU82PCFpbSZ+cSRzRSFGNmNtRSpCUllsJwogICAgJ212VmZNYyZ6eTheZXczWXpWPXp8Kn5CPVBYO2lKM2FFZGh3UVUwQD03QDNjMXJ9O2ppMU94Wm9TVDJudyFeISt+ezA/KyZuKmhHKzxxcFYqUWB+eiR7aTNlRWJOe0VKYjIwfHUnCiAgICAnbV9aOzZvTjV0ci0xeEM7aSU2VE5VRUk9PCN9VEUhSn5LfHV7ODdpSmE/PmojeW91IWMxZnZCQDVRQGprVHI4ZHhmI0U1O3ZoKXNzdVc3QU8+c09zT29AQlB5ckIhVzBFQXMhQycKICAgICdjfSY/aCpMMzsyOWJme2B3MkduVXktNmArQEl0VSNtbD02XyZ1SzhIe15GNz1SZzwkaSlucEZUXikjNC1hT2hVbWRMP3JYTyE+YSVPUipNcUVEfjUtdDReUXZ5NU1JRTB1KktvJwogICAgJ2QhMFYoa25pTjVXM24xNF5ObE02X1NtdD5YRGBMQjFOZCtkWl99SnBSKHklJj5zc3JzK1ZUJEN7KGh5eDM+b180TWZAaHBmI3Z+KWs7MGpRTTl3Mzh3SHhkYXAhLUpgLVA0TjknCiAgICAneyhHMXs7YztwTFQwMERiS15tWH1eSG5UXileSVpkeShxJHNNP15+QmxiRkhtd0pZPHRGVFBOdzckP2stdkEtMTRGfSY4K25ScXEkNGZ4bkdqYzlDIVZoUyhJc2BPPUtxZG5+KCcKICAgICclYDhEN2o/Oyl2QUAoVG9UeWNzbGxRb082UEZJSisjQTUqJF5HTEtzcDlqQ1FySXtLJnFGPjNQMmclcXwwK340RGZLRG1aRHU5eVM7fUdneTRjcERYe2d8WShCZyRORXQmYE9gJwogICAgJ0N+MUZ4M1o7MzxJb3gxdyYmNkdyeUg3I2h5bGlDK2Y5OyZnNEYtXkozWDVIQ04mfF5gYGYoYzsya31Jc1VMKVRgO0M2T0dvPWc5MEB9YHVscm1rJWBiWWAqZ0lhXyRnN3M1fVgnCiAgICAnT0NAa2ZwLT5iZXNadi1ITGBDRk56ZV5PSnZ4Y208Mn1zUz8jeUdBPHdjZndkSWFkOHZpam40aCp4ZzJCZSN2IXxvP3lvMGRQZyh3KT1DPVNCfTspIUNvZjM9PD5YT2xRaXd+LScKICAgICcqUihueW5DbVAjUSYxPT9TbXw5Sl5QclNFTnZUOVFifkp9KmVtPzAlPVdgRihAKm9TeTc2ISQ1Uz03dEtfb1ZHP15VcHlgbFQhKmFmM0xtX04hMT9NRkRuJTxRSnp7cyFWfCE3JwogICAgJ2FHYHYtTkt5K247aipWYmZmc159ZjNhTj5NK2YpS01+Zm1JJDEqclZXaEsxP2I2Yy07a0shVlRvIXNVdU0tVCQoK3d2c0JKNGBpQktAI1llX0w1bTBxa3dIKTdVezlyKmpmPGsnCiAgICAnaUFzflQrLXBqc0U/RkYhbXotUGtWMjQ/TGNSTz1TeXJkLS1gcF97WUV+dzY7bW12fnwjUENtejNIOShmQ3dKc0B7bFJ3QipMaWdXNTUmRkllT1ItNjdUKk51PTAwUjRqcE93PCcKICAgICdadCQtI2AzKGBxcU9+fVdxc35HIVFzNnoqVSM4MEtHKmJiPU5Ad3ZXX3RmaXo1VzJUOEQtZExqekRqc3I5KGJBI2J4KFI8fDgwTzshZUhYJUVDVnYqTlBxI0BPVk4zTypKYFA5JwogICAgJz5ld2p7Q180Jnt6bHc/ZysyKVJ0TzV6WH5HQkk3JkpqU2ZjSlJ5R0ctSDNeSSQtKDFpWiNJRzlNe0Y3PE1kTUI+OEIzWERBc2tLcUw+KzkzcWhDQVUhcD45R25iNXFYUH4/fm4nCiAgICAnbF9aNG5SJXV9MCgxTFlUR2JIJD42dHM/aXNeMTVkUiU4UStOPWwwZ2w4NVBONUx3cDtHIVdrVnQ5ZzhvPHVLTiZBekJDKG5JYyg7PTticUtOUkMjfGtLUWhsVy04ZDQhITY2OCcKICAgICdaSnxkc0EmamVAT0dxJmMoISpMZlRaN29rLShuc3AwKVh+O2hlOUEjJERoYiQqS09MNjRRfiZUQE9SP1Y2VmA8OWlCfCh0XjEpRVI/amB2VFNhPH5aXjQpdmorXlRsa3xKKT5SJwogICAgJzsjU0Nqe253dTlUZXRtSjxlJjhpNU9OeT96aTdQQHp2bFI4elhlfXlXO3ZVKVpXTSYxXm5SKHg5R1o1Oz98ZjFSRCMyJGAlcWQ/MlhDXyk3Pjd2WGw1fEomcUZuJEYxZzgja3gnCiAgICAnP1A/ZTEhb3RibiZYZyZtSlR7Vmo+X2RNKEBpQHg+dUtHTnx5MmYlM2tQV2U/c1c3ekAyIzB4UnRhSjxDc1V7MGVrUm04SHRhbHV7U2QpRmxPRWQwYTtOM3tmP01QQS00bzhaTCcKICAgICcqe0xlQUYteyM3fDh9NXwoN293IyZ9ajBFV2M7YiZFWjRaPmpZWHk4I1Z0fkB3PGd9dk1zNS04MkhmRGZ0bWN2U2tZa2Z8YDQkRTFTXjZGbk9GQEdIJUdfdDkzJCQjZ3pha1RhJwogICAgJ0tVIzRYKGB3MDh1UHlpMypRUD9CLXtKKGs4KHEpO2wxV2QmYzR9OTg9MWFzdkh8SCtnVn4yYkBeYlYhJXJuSj94az1aalRHJmdedj8mcThvVHd1UUowKGh4KG1+TFRaWCh5SkAnCiAgICAnV0V6QldeUSooPjxLTytLeGVOc0hsbHRFPU5uWHMrKFJjWUgjYiU3OCVtdWhNUHBZZFZsM1F0ZTtEOzdDX30/WVZnWEVvVilVR3R7MDJ+ZnYkPXxacSZ0QnleWmtJYk5aViNsOScKICAgICczdHVFSHZuYHs+TC0/VStTR249e2pvb3hUM29kUSpecmY+fU9TZUtAdCU/VnxGSns0JkhkdnlXVyZGdCFnSCg+fm0lPStFQV9SUEl5ZmUpLTQ4bUdgPSFZWD5JXysrdDdRR34/JwogICAgJ2U3QWQpKT89JX5LU3BwNVE+WXdTSGtvV0dETilJLXVCKkRXaXc2cDFITXMqQ1V3KkQhMz9zU0ByUld6R3pZcDswbVVITCs5fjZzeUk0K3FATUBITX01dH53cVNFKWNCSEV7aGUnCiAgICAnJDQ+JCNgUn1MenBPaiY8K1YmQVFKQlhrJFRAOCt7WWlmTSFqRENEN1gybEVWekBEWTx4Y0x3YmM/RHgyXnZGfjstUjg0USQ0YTV+elctMllhZ2NWNHpTN1BIVGh0JlFzNFFMKycKICAgICc+JjxuMFdSP0lwWiNfU1A5bUppI3g4Vz8qUWROLVMlNTMjVXRjQ2ohViNrM31iLVVMSTVPSE9IQmZPbUR1SG0ta3hLfn52O1dRMC1RUVgqJkItOTxabkFkdjR2NmtJdS1TcCVgJwogICAgJyZ9aTg2ZWY3YTtlemJ7PEJ7eGk/LUg9UjxGciR4V3h0VGVaOTBHSlhMQUgoJWpOLTJaXl4pVUAqV31mckwmX1J2UEI1KUthVCRqdXRtUFcpeCpYb3AqUEQqYFRte1I+bXFOSWwnCiAgICAnOGxfcH5INFQmSDYoPzVJY0FLVHN0RCZPKD9XNjRoYDhoPDtqfnZjJGxFWGAtcWAyPz13cGEpV0lYe2lTRTN2NDhEWFJwYHEhdHBYelQlQ1JEWXItNSF0PE4wYjdecVNoWG4/bicKICAgICdgUXxiZEY9aFpAZSNaWGdUcGdIcl5nRWxeVyVhUll5QXtKSlU/SjRDeytiZ3ZMeDc4eShLaUNuTF8lVFk5UGZiNVR0YlN6YmpzVm5hbG59Qmw8aGpgMT1ne3MtekFiMnAjZnkpJwogICAgJz9nSVklb318c1RiR0piK3tFYU9LR31LRm1OSmdPRlpIMS1+ckUhdWNQMTtgQkBrZiF8bH50TTdldE00QntHdH1tbXYpeGM1OSt0UytgPSVAcXlAPEh4cGRSZEAhSGA0XzdqYngnCiAgICAnTjlDcGM+KyFNOClmRGZzVGotemplNWxLPDV6I2RfajwmJkZYRyh3Si1mTUBaaVRxdW95RDVgQUwzYTQjWFdaM3RCNkdiaStFZmt1bFclZztLUUdvM3g3aH5pRTNUMXg8az4wSCcKICAgICdIdD1IU3ExMzl0SHB2UChtR1R6TUxmLUJuJTYzfnR5dzArMkAzfFg7WV51OShUXlkxPj9efVYrP2RJQEc4QWh0WjxxTCtCeEdWZlFLRj1CPjY/ejZpMHBfVVRGTUt1UG9gVGhuJwogICAgJ2Y/Zj5LKUBkK2BfYmJ3eWBZTWxUIzRpYXFVUkRNTm1xeG5ea1VBQns1MS0pQiN7fSZ3c2VafF9ZQUI1SlR3WkFjbCZ3NDg2KEgmQ0FyZF9Sa21jOHwhOWtffVd1d09hNlFBYCQnCiAgICAnc2ZyX2ZHMikzRUY5dWRCPk4rYnwtal4hZU57NCY/bUtkMDVkVHZhPGExfTxNO2F0ZjgpaVJGU2lwRVoqMmsrI3UoYj5JbmhjP2BYOFp1dD9jYntQUGk5K3k8I2w/cUlgPTVKWScKICAgICdWPHAyajNuRiM1WlI3VTBieVlEUlIzPClJQ3EzWE4oUSQyeWg9PWplYk83YXcrVCVaSl99STZ+dXUzZCU5K1gkYWh+cTU/PjNIK1BCPDJLWVhzT0JtPztCXzB4Oz5AZzJae1ZvJwogICAgJ14xSjQkM2E1VypaVXktdEomI0NrNSNzWkxLTT5zaDRIcWRGRCpuQCY2eXd+eEFnUVROPXFMejd3T1lwTTBEeWl9JGstdnhYWn5oS0ZaMVBldlp9LXpBSXZXPTxZcUlRdn43cDknCiAgICAnXj8raypjfjY/Vkw2fU5oVWR0emVkKmQwPUlAbGtuNT8tNng5YV9zcV5LTEoxblJuSWFuJEpBaUgwcUNiQS1mK3k0aiZtMm50TmF4fEhaMj9aYzR8eW4lNyNAZVopaTkle0cjOScKICAgICd1VEZ0Z0F+d1Z4SzwzNTlwYCZKXjVeT08zN08tLU1USWUkMSU1VS1IVzNOWTdMMVdaPFE1cy1WQ2gwNTMhYnVBTk9pblFTMzskQzZEeERJMT5SOFRoKyhMTEJheGh9ZGprJD14JwogICAgJ017NFBMaTt9dEhfRjQ8fkJhQSNma1IoNGNIdkdLUmhHbEFUb0tnYSZTNFpYMzZScjhmNUY0VkNaclMqPTVESSpmdHhXNW5XQVUlPjBpVSFfTGN3LSZWI0tqc2BFbVRwbEtMJD4nCiAgICAndE99SmV1PT13az1kdmhpNj4wTnAyTXdHKj1fayVwMlMkKXcyJVd+d3pDUjNUdHRwLSVAWj8wcFpGS1lOQXYoJil4NUl+SG9edForQDVIUk52Qjxydi1nM2ZaUDNJekBYTFp+bScKICAgICchdmMtS3ojJklEWWNYKEhxNXROXj97NWZCSVF2UENyc0RWMyMtdC1NejRMSUxYYVYmeThlPVdhPl50RHI3P3YyZWhGYz5fSl5ZVV44cU8qMjZDLUBQNCRUejgjYyE4ditBKjtzJwogICAgJypWR0k7e0VgWDlpOUxfN3JFKiRlPWNnQGMpVVEpYTZNTn5gQyY4JXd6aDRmdHM4WFdnS0t7eEp3KndwdVhpdmNzTVhpSDIkTz4ldmU+eGolcUVmZCFZb0VPeEApVDtxWGhQdVMnCiAgICAnbSpTWWpVfDtYdEdJX3QwTWdMQz5yKmUkP0wqS3dgQ31+LTh0fE5ScllGc1ctanRfQ0NKS0tzK0FgbjFYNCFXJitZdWtXSz80JSple2AyKGdvQVglQEdFTERvYDVUT3BvSCQ8YycKICAgICd3VndhaVZ4RV9KUjV1aUMlMF5lMEVqOF5pVCleaE4wQjJpPis4SzUhOEBRdHA2RWBNalRyQXo3P3Y0WnwmckJhXkdpSj0rZlUyRyFtIXx6JkRmUCF1MHgkTns7c08oanJLYlpvJwogICAgJ2RGQWZQWik2NWk/aFZodz5ndiE3fEh7NHptWCEmNGN7TFNLNFU+KH0jMmFWTXg7K013I2JXajR6aTZFUUZGckYxNGY0dTFLVjRYK2Y7bnN8KUxAfXNQYFpNcjZWNDdDSlc+WTUnCiAgICAnMlp7aUxidT9TMGwzNWhrVXU2VlRyRzV4ZlRXUkIxRU05fCllIVNufkkxU3YqK2lnbUo4P09WJjU+eTdmSVh+TkVzJW5XcnFKa01WPSRRdUFacDhvVFd2YigtXkMjTDw7VEhMYScKICAgICc4Kks5cVR5ZD18Qm0mZ0s0ejZvUS0oPUxsUCohZnVRNmckPSs2alhNKGVQdWxtOERWIzlPPDxrXkY8JH1GdGo9dk9qWjRqTSo9bH49JFU8Mmd9d313aHAhRE5MVTlqSXRMRXtvJwogICAgJ3ktSHc1K19WVCN1WU8tVHBuKz16WG8tejZuSUFZTThBJEZ2dGEjNXllOWwhaG9KNVFAMloqNCNmNndCMShmOWc0TTJ5O05IYSRaRGtofnx1emV1T1M+cWc8X0tUUG1aS3VlKmYnCiAgICAnaEFian53U3opc3poPnhreWRJTFhuSGwzdV9JQ2t8TjJUN044S0pAdUh0UWNHQ0ZwbXR1YE1PKDN7IylAbDgqM1hHXkBxbXo3aDx3RzlFIXQzSGw1fmEjbG9oaEF2VVAxXz01ZScKICAgICd6KmtjMWhyR2l0VmVGcW44a1YwdHJLY3NtR1NKRmQ/RzZEVCVBaV40UWM4amxBWSZ3JCFmSCgqazstZFpIWFhxZ15QM2Z7KWo0KHF5QFdGR3hicC1oRiFrYyliaCtyY05LKVp2JwogICAgJ2RkbzJ4YU8xP0VJdGEzWkYyOWk/SXg9fjNSZVoxbEhyV0hVdktMfFdETyshQnVDM3RMeFY9PWp2bmd8bzkmWSpCTktoZDtGfnlacWArNC1EQk41QDhodnRxVTxOOFBOZjYpdCUnCiAgICAnPFBMKmgtayZqJXAySnNsUE9UPWJvU0Y7VVNAV0B2VXIoT1k0cGIrKStQNVBVP0NfellCb3p2aGQlZCpqK3ZBTFVmWUAmbyhtaU0hVl47aGZpUDZ8bXNwQk1KOHFhMSpSSHZYPycKICAgICd4WGJUZUZ0X2wjdTEwTXIreVo4a1VJUjlVR1ZDI0Mjd3g1N0BvTnw1XlJ6SWRjKmNzQDh3fD47WCVWSWBVfExtbnlHLU9mYEEtPCk/VTB7JUslNkJ4MCRlU0pRfn5aczRXT2w7JwogICAgJzIwSzNPbDVjUGlxNVVxQzlfcShWeXFUYTFIOSNEdykhYT90NzE/JTY/aE1rWnUoYzc7TjY9b1EkTkg8cyhyZz4yX35aMmpXK2NRKEhPeVgoWTJgc1pTYHh+UWkybmJ7YysqdjInCiAgICAnekp1Rk91UFBPN0liPH4teXFyIzFaUWZNQz8hUHl6TDNZbkEyY2F+PHh5ajJDP3E/dDUqcndQUjZhQ2w9KXk9OEA0YFEpYmQlM25NUXYoNW9LbC17fU5KSkVNTT8zI24+PW0/YScKICAgICc3IXJ3NHF3aytTVUAkV0c+TXtCUi1PPCVfYGd9SkBzPzZuYTFjKDZ6TDFZd2Q8YERhSiFFQnVUMn1AMUw7LWZgSlBgekB6QEdPNGluIz0henZQaz9aclRiaWRQai0yYkFUYE1xJwogICAgJ0ZvRmpqVUlqJnBvJTtxOzxLbCFgKll7X0A2ZlclX3VmYXU1e301JitkQ1paa09FSC1QckRKWmhHQTMkam1rNEJ6bWJ7ajZGTE9PRmpjQjBlcHhUWDYoUFg/aGk+QX1QalYpNX4nCiAgICAnX2x8JEI9ZDtQQUpWRmZHQiM3YGZ7LSVgX0syJk43JTcmdStRaXpxb0NNbFBEa29uSXZnfXJCPnNtY2NaYmR2e0lxZHQ2cnJWO31NbGpKTTxwRWhmdypBcX4peXxBMXo7VCYoSicKICAgICcrQihDTkwxWnJmZ15Hb0UtMXMzRGBhbkpqRVRHYTRBZSVwMCtfOXpZVHNPU3x5KVp9XlRsKXVFT1YhR0woblRYNl84NUM1VkR5OUl6I2hFemJNYDIrJChyZkZXPyhqNTwmTzBaJwogICAgJzQ+fjdPRWtvMnhQa2wmPyp8JSU0PCVwPXhgOSlZZWlOfTxCNGRLWSZXZV9RQiVkR35TTSVqS151dnUkUUVYXj5WdFc4VmxaYWpNbV5BTz0wNl5hTHNJJThkNCF9JFlGViNFcTUnCiAgICAnI05nQX0zQj9qX3ZhO0M/fER7emNDd2R0fjdKdVRJMitPZlgjTS1CP0lndjdZXnIqKCkxUXdtO1h3fkRuPzlGNC00fkZ1Xl90OHROWXt0UngmVUtDUk9hN1QxQnY/ODNGJW9gWicKICAgICdBN3dmR0NIU21TSlFrd2pScz8yY0MpSjM4VSZ8JkJzRUNMfEFXYz45aHd0KmdGWGxBe3c4cUV2KyZ0UHlxTmhJV2NAfmtjNHI8ZVEmJGE/M1llMHFXdCQmN04xN3pUTWhrfE94JwogICAgJ140a2pIZm1TI09tP0ZuYTtVIzlgUShXcDc5UU9CQ2A5NmxhY3ZvIzRKUmNHQkc3eyhRdVFFKEFGJXJGP29PVDUlSi1zfSpNZGJRNXdqMjFHQ2hIVnJ7Tm5wVitFV0VhJlYzPnonCiAgICAnQzdGK2paYlQlaF4zN00taHQmPnlKRmVjRnBqQCg+c3NlVEdqb35PX0Emd3pgYVY9STg/USFKTjh8NEk0aCtyKEMkITFyQiRAeTBrb1RpTmNET0EyUFJuLSVAYE5ITkdPMiYpdCcKICAgICdNZ3tFaSE4N192K3Ikc28+I2dQc3VIVzwlQU5UTEBPSF97QWEoPytATFNYYnE2aGc2bWIyJlZYO0ExMX57eil2WnR1I0F+alk3fVQtOVd0SEVPPWtIck00TVNtR3pARiRZRXEqJwogICAgJ29fV1JGT2dPZX1XQnVNMEQ0e1FMdkZ2RCoxNzF3N2liV3ooJWNjfktTXkE5K1AwbEdNVjJrbGF6N251VSR2fnYwRDEyZ2FhfkNORlZ+MnI1Pj5nSigqUkZmeihwPTZDI0JnekonCiAgICAnOSRpdTdSUCNMeT4kYyZtSzJ6aC1KPEVRPU5GM3clakd6KypBPWgyc0ZDUzZAZCRLPUxYLWVqc2dHQ2ZgPHRnSDdpRzlNIWBYNnZQWmYqJDUzKXpSYVZqVnlTN3JhVEUwbGUjMScKICAgICdVT3hMdiZyJSVFRCheJE57WVkwaW11NiRSSVhfYChee2R5X0tZT3ZpVFA3IUpEalhRPUtpQkJsYXNFXkQyfkkhO0VZRXNrcWkpN35EcllsRV5eVjU3RlZyVWpwNXAob3QjKWA/JwogICAgJ2U8Q0d6e012N0pqWXo8ZFJNKTM9amxPTD9YMTtpdWVBNip+YTcyTEAmfGR0Xll4WFMtMzYrPiNEe2lZdjRjUGdCOTM8aDJVTl8temFKSCt8LW93SCp5WW8zWlh2fiEldVhfb0EnCiAgICAnZl5edEItV35qSWo2UkxXczhtSmk1JVhlLURGYk01KnQrcmVAV3lAS3hLOzshOSUzbCtwQERPQnk/T2F2aGBVeDVpZ0x8cntsemZjRypxX3Buan5UUHBERVBHJTIjfWY9VGZhKScKICAgICdJKlBlWTZ5dk53VXlQN0ArI3k3SlB0eTJ2cXRYdU1TNFJfK1F6RH5VJXhpdk8yZThPO2x0JGZDbDRaJFdkQypAVU5eMHZuVHpJPU94PlVveitnWkc5bF9xYk5XN2ZKaFUqbE49JwogICAgJ0YjUUpxdGR0e3c8XlBAZj4yUnI4MkZPfT1IKmVpVHQ3YD1WIXlxUWV4SkdYSGJ1T2ZpJSlIWnlhSj9oZUNoe1JrZTJCcCE1SFUoUChLJT4mJGR3QE5NY19uKXd2elFAME01enQnCiAgICAnOSYrelpNa3ZkcXBFJGBPLWRMa1glY092UW4rTGU8ekV4aWA8OEBgVWkkOVpQWH5BMDl5OXFCdlJGPSFYTSgwZk45Qm1saVErP0xmWFEjXkZOfHBWQ083YmVwe05ebzFpV2V1TycKICAgICctdz1aSUhSOSpkYSszfipvU20/ckpjVEUtKThBNWptPUReNzs0clNXbVlyYnxVWjxnWlY1TWllU1E5K0dUQytOPCh2cUtvJEFSQjBiamVMNTd+WiU0ciZvSCNMZGVsMWFfUmptJwogICAgJyZUNEdGLVVYWEZtJEMkcjhaMHFvR280KlNIUmJOX0lqWWE8RWlHUTNpPWNEN1F8Qmw2e3BMcyZkI2ZfTVF6XiNXKShjSkhXVkM5ZzhzZlhFd3tXMlZzZUAqQVJtMTFkI15DSTYnCiAgICAnPi0mezlya0JwTC1oMn4hSSROenpONmxMT213SyE+UUh6ek5sPTlvQF99cmhzYnNAdFJjX2ckJUFyJllMeUBzOCokSEBZdGFtel8jSyhFUzJUb3czbmtsRkViNVAxPExhfGIlQScKICAgICczfnpHLWkwfEIreHpBUn4zJllYTjdGaiEkczIpYytoV3U9YHJWeTs8XzY3dyptSyN+aU5NYENBKHg3QGlVIXcqdlFId19pX0w+OyQrQVl4ZjstKlRzciNBYDtPUDIoek1XaFBeJwogICAgJ0l5P1VFOGRZKk52RSRgeTI1cFIhRnxCfDMhRFQ1ZTc2dGhFTHUzci1CaWRlaWN6ZlpKPjtvKmUtV2o9aVhTeiM4IypBNz95fjFnPU48fDRKQ3s1LVRFKjF5KGlUaGxRSHc2MmgnCiAgICAnQVJ9UklaJiNBbUNEXzVNJn0+QzBtSnwqOVdze2V0NXtgfiZyTWpQfGdnJDQ3O1FSfSVZO1c8QTxMcG1Sd2ZjKzAlOEFGenNfWUM3cmIwYX1KTUlYQXNBQn1TKihITUUjRH1xRCcKICAgICc1ZDVXNktkNmp+UGdFVWFGPWAkNDx1ZkZwPkJuPDU3SH5ELUlrUXd5ZjVzaFphSnlqe2JrJl5yNlZQNmd0S1JnWXIwbXx7WXRUeiZlVChSfnJ9UXZ7QzxhNU9ST2xyaTI2Jkp8JwogICAgJ1ptMXBoaUh5UkBlQVlqZDxBPFFGPTYjKmVfI24pSHE3K2xuS3RSRE11aT5IK0o7TSl3dChVbXJLKEdnWklNOCYmalNtSTQ5cG9LJF8+Kk1acGBURWs2TUMkXlFKdVFJMU9qTHInCiAgICAndG1NWE5OLVQtVzVvMUJrVFJQTSpPQVV4Mkk+fFErTU4jTzQ1O0NEWUYrO25yQCN0RVB5SDtGKDQlNyhVYHRna3JtcHdhbWE+Xk8qKmdHbTAhfmU9QkljcE1aNX1iblU/RjRgOCcKICAgICduPyQhZFgpPUdNbz1DXkVKJjtMeWhkIWhSbH1jSmowMGgleXstSFdNJkF8PnZ5SHUqfCplRTBkdDY4NWQmZz43QnB4VWooPWtUI3wxeSFsOWdpPX10UnJHWnlHPyl4elFLPFQhJwogICAgJ08+Z01NaEIkUTJaJTRTM3M2fW5QNCliZTdKT05BS2pmM20lQm5wZyY5YjdAdEFrKXI7QC1EPUlTVGRySiFNT29LKkIwRUVBNzw9cCRXeHooZDYpQ1Q8bD9yRyspNGM2JlM5VGYnCiAgICAnWld+bitibXJZS2hyXm04bnlhciE/ejBPS0JULTslVj5BTmgwWjY/R1kxdlB6SEBPZHxCeSNvMz1jRGlMPGRmPmRTaSZUaXRtcmR8MzZCUjdMMnJXUFRgRiRAJDE9K1RKQmU/cycKICAgICckMCo1Tz5EWHU5ZlFzV1FVTGNhfjRnOHIhJl94c3dSVCg4JXtSczghJDJtbyl0PHRmKzh1QWJqODNzUGFSbER8JnR8RE5xI3spUFJyPjlRNU9JNT9hJTMpOT9ETWJKYD1zZ2gzJwogICAgJyt0cVAoMC1ZYUhTeGVjRHBYSXNMTkx0UEI9YkJBVjByXkRoVX1tSDtNaiZoSzx5QlNZYnh1V3hiTTg5PzdXJllvbDd7bkRhLVZsV2YjI0ZOdShUWk5aemNGaCFiQTRrKTU+SlQnCiAgICAnYXhBSGF6RC0wSjM7V0RXUSZpYk87IzdYV1ctJXtyVkdmKnk2NTJkNTN0Sz1zZ0tmU01kWiYlNDhyRFEjSDhNM3dCbTR7T2BLaXtvWSs7cWg3Z0hfY3FAU3QwYno1azRLaWNSVCcKICAgICdkfWYocTBTQTdibVFAckxJcCklX2AmTDFJNUtZR2d6Y3p0TEMwJCtfXzB2I3RDbT5KJUU2RkZPfEc9VjdnP0B0KntIbkFOPyY+cz1zaEliTHFnX2xxVWs0N1pOYSNDaEg3ciZrJwogICAgJ3N7KjVtKXYkK0hUP2UoOFVCbGFAVXZOdWdTNjVQVD4hNGVOSGxHSk9yVGh1ckNNUkpDWiheZldhfGZ4N1I2RnY4IWlYaEozb05YJGRLZTIqbWR3K3RxLU95TjVEWmotQmZvcH4nCiAgICAnKTxEJWJ1R0hWc3VLKFZrTnhBdmo9U3IoREY4SlM/d0VobGghO3p3JVAtcmlEa2hYdkQ1MzZtV3pQIT1YXnIzdVV3dlI1KytAOFlqQk10T0hpRio3dWMxaiVfLVQ3eEdDKlMpcycKICAgICdabEBwKHtOfTJ2VFN7JXN4fV9fcVYzZ3E1Q25xRVIxNHJTOzxKT0QkTlhiK3RETVU/NDl2diRTWTV8KU5BKS1URkkxbFIkaUkrZUAlTDNLUTZSOF59dzZCKDdzMEUwMXlBaDR3JwogICAgJ15DMjwpcmgtZENqfEs4RyloMT9kWkZ8VDdXWExwVDlRajJRN1o/WX1xTSUwXldONU9jdHkyWERlQXpwV29HX2JaN3VZX3JyY1ZJaTNYWkVEK24pT08pbXE9UU9TQUt4b0xwVGsnCiAgICAnYVREU2BXdTVMIShCVVV2KTR3SDdLMSMtWjFxNHY+MnJQXjcmcGpxWGBYaktRdXZOSXhken19TDhRZE44cnZHfWU5WGVpPjhrKmtyNkUkTHN0M0swKXFIYU15aCp1azI5YjlSRScKICAgICcwTU8tSDA3U150QyRjc2tqfH04SCt9PWdFTUhuPE4+VlpEdClsPHBHIVdiPV5Qc21xSXB3QD5aKjIjKng4QWAoWEp5bWVLcUNxampUa2ZkVT1PaVlHY3Z2d1lxeE5JSEdgaDxUJwogICAgJ0lDPn0wVDs3TCFvTSU9YGJDLTZ+eHotdk4rNGxrP1NmTGw/Y1QhWnVOXy1xT2xrRnVRcUtqVX5fNjIzcXgxd3t5d3l9KCteWXAwVUFjNjB9NTN5Z3h5U04makdiYjNjJkF8JDEnCiAgICAnNGFHakZwP1VLUDBjcVF1OyQ8XmZKXjcrU1lTVHAwO0Myc0xHRyRuOGJuV3VsLSM4LXlNV3Z9dyFYYW13IVZuJkEpakwqfWVlTUI4d0kjZ0llI2BCWGlEQFpMWjtrbj93fD1zKycKICAgICdZVkE9YGduVzNVKkgxLSswTlZvR249fkckI0kpU21MdCZ7MD4pd1B3JWRZfnoma1FrOTh9byZNJVRlRF5mTkc2eDU/aTBxKzE1clFyZU53Iz5gaTErTG9MNlkrSjkrY3MxPGV0JwogICAgJ3l+PEx6SHMwS2FyTGctTGpAPmtLezA2U2AqRiMtWloqcTU2TkU5XmktcCslXz0ycTZGZEVnczlZY05YT2QtV0l0SEUwfXw0bUxSemdYMFF5SjFAJEYpUj1uRj9nQUtyPTQ9KnwnCiAgICAnRlIrQnJiT15nUCFoSzwmJnd5ZCNDZW18NUJ3fTQqU2UhRXZtdiVPcTQzcVNRbEQ7bHteJFJuN0xzMyt1akczPUtGaEIycEt8bm5kbFU2TzUpYTt6Km5mIys/SmN8KSlpdnNuRScKICAgICdRPT14ZTg5TGBvdnN+JitOOzdOPWR4Vj9tVWJvY2BVZHQqPXotM1g+MiNnUHZeKHA2VjBGPmFnRWxwM2QzeTJlS3JueldjREgqRFNRLXVtU0Aqd29sd1o8dExLcyRKSyFPKUNIJwogICAgJ0VRbGhaLV8oVTVoIUFycl9MI3tJN0lJYCRDRmtpJnkqYVFrbjhVYSFTakRTRW4hUCR9e18tUTR0KmZfPSsxczFJMz5CfGFtSXp4Q293clFocTg7QnZxYFYxLWtMQTNjcnwxPFonCiAgICAnOUptViVkWCEzJEcpZXdWd3hYREFqb1hQWUc4emQ9QFJPRSQ9PytCWEdUQSZETzB8cFhqSCFfanooUUtVYSl6c2JPMHtSfFpwVHI+QD5HMjNse085TW8zPlA5aEE9bklHcGI3QCcKICAgICchbWFHJm9zdy0qM14hKGw9aXE0fE1qPXNJZj9zKV9GfFIyR1VJZ0xMRnJtVlBkU2hiKml9VWRicjR8UmpJIzNzZSUlOTMpd2N6Pi0jZDs2elorLXBjKm0wd3ZuZD1tTmFGc0N9JwogICAgJ2sqWFhxU1ljRW0+ViRFeStPe19id081a1BAWnJOXkF7TTdFZFcwIVd8OENgQWlLJlVSUUtCdE1YOHpadik8Q2F9PkoqMCRjYFltfjE0WlhtbDlUSlVhXitPVSY8UStCLXQ1cWEnCiAgICAnJW5zJjtiTEVPeGd4ejkkX09ETlJra0V7KkNqUWcrKTFkK31VSWkhKFlwMz4qSCFsSkthQnUzZjFTVmB4UyVHJXkxNGVeTnhsZzk2KHFSaGpZKjtJPiVuMGhoYzQxRWJzP2BJVScKICAgICdVPmdgbzhNZUdARmw/O3dTKm1fJGBCdWF8Vj0kNSUlYmw9cWgobmwwM0ZldDNsUXV9cENASis7PTk+RFQxXjRtb3VtJk4yJWtROWFtREQrZld7IXNjS3poaStYOWokZjg5YGVjJwogICAgJ2t5Rlg/QVNgLVlvREMpKzN0Wn0/R29BbTdGJVIkeCVJfTxfWVpObmpYcGElTzVaOGwteFM2b2k/KzNjUVJWOXNFPEQ+dU1sQXAkMClhRTsoNCgyayNEUWpkNkNuXzZtUXJzPGknCiAgICAnc3p4c0E2Sm1DfShYWU5jdDdfYH5DZUZzZFlZX0RRbGJgSEwzUWojMGgzSDUpZEgtKjtyQEFQM0pzTEU7NmkyZHxuKG1AJilQRXpHcWR6KyM4UGpAJHtJX2h1QlA5RFBBQ354PicKICAgICdYRnNRYExNdWZCbU5XMUptVVkoa1dRUzZxZiZFbiUrK2ZKRTVAMykrdz0mSWs2PG4wJFdIZHp2bXJEc3JORStJMWV0JmUwczNsTTRHXk5BSXptSn4/QHdoXm4jTTEwYXd+ZmVFJwogICAgJ0JzRiRea0tFWSF2aVJlMVY/KVlaTXBRNHE5YjxJPyNyaz99PmZiaWRsb15JZFdhYi1OfDE7WmpkWU5Gc0AoQmsybVpnTUptPURKVEc8LUNMRG81eCN7OSUwaiZjJDAqO2AwYzInCiAgICAnZVh0e25udH1je1VffTVUNHUmMUJscG5zWFc5Sit6bHVeXmpWVm41aURMLSV5a0ZEV2lMbz0xakdrNCppcWshalQ2TlgqQyl2Q2ZYPCEkeV5yK2w1QENOYX5ZaG5nflBEQ2d7ZycKICAgICd6a2BpQjVIbjxhezNEJTwmTilqLU03N1lIez1KUUBwSWpOJHZsKSZKPHFOP0Z1eEQyMllqOH0qWTUoYU1rWShrJWBpZzZFXiUoIUNqKH1PekskczVPOSFkISZqWDRxZTBCJTMxJwogICAgJz0rVlI2N2w5dnlubUdfNnNkOSgrOFQqc04/QyV7KldkZklQbXJlVkBsZiRRYT98QWcoV3ZZc34leT0+PWU3b1FIMCk0Z2ViJnVYPHVmJU5HN3RKTV5UZnstK2pXRHdFbEx6TzUnCiAgICAncmhAOURENk5XRlckUnZ3IXZnZW0/P0c2VSFSV1BuS3IyYCpza1M9P1cxRWxIdWpPPVptOWR1WXNPPHhULTxKPEBpdChCayUqKkNoeU9zaD5sfl5UUUVDejNrJWdkMDB6X088WScKICAgICdiJG5hc3U2NEpHNDlgPVRZREFWblZsUUxWaUR0bShQKz1gQTNoP29+bT1AJWB8Q0tRcEs1Rm5SRCM/KDFVYXtnaWRjb305P316NU49QHBPPWtiUVdLXjU8JDBMX0U1ckomWWpBJwogICAgJyF2RSgwckNMKkt0d3F4YHMyPEJ1aVhta1g0KigzcHJQUmB3OCZIYU9DUC17cGBOTDl3X3VhRCpuTnpRPDchN2JFaUAtRDxFPGR6ejdhIzk2ajFGQStVTFBZTk04MHQtUihiYS0nCiAgICAnI2U1UHEpa3J2ZypzfDMzdXcxZFVPNFNWJTZGUlohZipyeVQqRE1GcThBdkp6RXlyRXpRZUU5NzU9VzcwOHM8ZVdvSmJ6NUhxY1p0QitPdlR7JihIbUN5ND4pM1Q+KnA4XkR6QicKICAgICdidUlrOzRWemwxQjxtZ185VnV0NUA5YHJRZG9EZnh7PERwV3tvSUxOdndGd3BaZUt3QS10KUQlMjVMWWspamU+VThqPiRIbVA+fnc7YCkzJXhmZ3dTY0NfTT5hK1d0RmYoUE8jJwogICAgJ1ZKQiF+VDQtSmY2bH5PbmNMcStYQHooN3l5X3dWaTFOJiVuLUdSUkpPZkxDZVZJNF9BZjErWF4/VmEwSG5keHEpYis0VSt1OVVTM0tWbyg4QWhCJChjNm1lYD9fJHcxZ0kmTkwnCiAgICAneVAxcW48d35ZWTROV0MzNVlpMTtSbnBUT2Fsdn0raFZRLWlIdmt5ZV93JnU8JGYhSV95djFkTXlhbVdfO25sfkRuISFtantnRm5wOCN6X3AjbiF1ZF45bHUzaHwqRl9NPn1eVicKICAgICdGQFhnVVg1JVVIIytyTSRmdWZ6e2AoeGtDRUB5U0JsNzNDcnR1VVh3c1dMNUMxezFXRVgxMDFJNU9BNnFIMElFM0pLYGVwcEgmK0xISzthRWh4N3NtazBYN3RAdmxiPWA7VihUJwogICAgJyhKfVp+bmdUUF5yfExyU0YjdFU9dGdSWV9uQjRvbzx8eDlAb3hzPT01RFBLTnp8U18ySCpMOTJtLUsmcW5HPVJGbkpFZ31RRisxYUA/N3Bje3ZFPTl4d3huZXs/MGZjXzBzVzcnCiAgICAnO215XjYtcm5XLW9PNVkoUVkta2RIM21EaXBES358YnNvNWJKTG5pc2tOTFlqUDJXOXwkKVEqSnJCLURyX3h+VHpUTVJLYzRAZTcqa2pnemh1UXI8VlFYVUdAaFIhe01uKGpmNycKICAgICc8bjw5VTA/LTZOcm0pb3FRRHcoQCglZmRmZW5GPzkrJFk5X3BwJipRUkBIezRWIyhsPG5RN1h4TjI9KHVfaSs3aUdFVUcjciQ0PTchbCM2bjUlYTJ6cXRIVWAhVTdXJGM8Xm0kJwogICAgJ1V+VV48TSEjZE9ZM0glcjRVOGhtKGdyVClIKUJ7NTRUQnZqbG5FaTRSU3BNSHFPTGdrbUNiVlc2PzQyNFB+Uzk5SzQrU2ojSm95JVYyJVFtSCh8bUt7Ozx3eF5sQmRNb302UWwnCiAgICAnOXd6TjZsNG5mREtucEJ3czdGVU57Ml5pYnc8cnNKQjgweT1CMFVTaSVBPz1JOX5GPEtgfG1iVGIwSHxOYUxGLSszbmNVeUYkWWlOQ191JCNWKk1VdShVRX01NHp7TUxQUFJ+PicKICAgICdDbTV7KDhyZGhaTjZoSWIoTXJ7YyF1JS0pNG49d3JZYWFJbDNsNj0jMG9eNWwldDdkcylTfjlFTk5vTWBpWCtAaXckaSZTZDRLOUptMC16cTkwR2Z8IXl3Wkw+QnpLfjwqcyg+JwogICAgJ2ZsKjJQR21iQiokQyYrbmNvV0Y0WlVsckpiZ2o+Y2xPZXltJFMpKCpuZX0tajxzNG4zWTFON25Sc3MpRlM1Yks1T144eCR0ZVR3TW5PJDdpSkBUTER6LX02blg1ayhwSCFWQ0UnCiAgICAndEl0ZFdJKl99KE5WXiR9QEdWQUlffW5VK0hBSHtAbWI3LSQ9IVBTTThtJDtMXlY/cG0hZiFYKERWKEwxVT9yP3VUNUdXUXA3cnpLb1doTXgoIWl9d3REOz1jXj9oVDJ7VlpfYScKICAgICdsT3Aoam5FN1gmT3ZrX3doVj9VJSR2X1kzQ21NQXFXUF5eJndLM2pnUndWWjJ1Mi1hVSticWM2N2NuLT9TR0hRJS0oeSFtZTJ7WmoxJSo4T3dkJGQ4KHhsPXtlNWh4TVJjMWk9JwogICAgJ0JVYU9VWmdNZDcjRFcwRiFLWTEhTDE4dDA5eWV3fU0kKnhzNHdSc2lod1pBcXNwQDE1O1I/TUpMUmVaXyN8OEZEUyleKilvR0pTdzgxTHBLJVA7ZzI4IzZyeyhpQ1Q3KWxnaHAnCiAgICAnYWNGPTJ5bVRxNXV9KTtyJip1eXQqNztedHlNIUpnQF51YD9fcXNzb2I3b2Y7Vmkxan0qUTc9YHFKQ3BPbVdGWlYmZWxyVVlOfktEJCh9QlV5V2pxZCZJfm5aMUBEKT5VbU42YScKICAgICdyUiVnITJXaXUmSzgqIy1AVEZ0TCtrfXYkZn0pSyFtaSstIzFvUzdgVktQc1F1aHhTJTEyckMhbC0kc1NXa1dxI0tARkBOTEwmYUF3TSN5YHQ1TEJVQEZRYHRJcyY1ekFvWmk8JwogICAgJ0p5Y2ReMDNiRilhNUEhYWB+P1lFQEx6KTd3c2orSk9HdUEjPnxKKzZMM0g2TjBPNEBwTVVHfkZsfHRuSD9eKzwlViZRMDAhMEIkUzk+ZGVkOWMtaUUtd1hJekkqI35PWnkxQ34nCiAgICAnakJqSGpDPmJlX01BKTxEMXNAVEghTGt2VDZvWVpHSWRaIyEhbjVkd3p8ZnROdl5OMipNcn4qbWtKKCZYMU9IQCVjYiE+QTReKj5TNk58TWclNChlWGMjMypmPCY+UW57Mj1tPCcKICAgICd4aUctZmF+TVpwNTU2XlV5aittPk0xSW90cytnMyNVMUZoXnghV1BaMH1FKWt2Xy1LTk1NPTRaQkxRMSVLNTNKQ0pnRipYSzlAOV8pZm1MbmR6a3Q3cF4ka1RyQHNMKzRYakQ8JwogICAgJ1RnVmd+U28tZV9qYUpnWl59X3NkJllRXnozaUJBaSVBdFY5czQtVk0yYFVQX21eP25HSEtRfVZGfV9FeXUkX3N3aXdRNGEmWW5vTDFjWV5ucjwhOGpBSGxRd3hVaXl9SVFMSGgnCiAgICAnWkZyZWVAWWN9R1V+cXNYY3kkJHY5M0J3PkdAITA2elR1dlE1R3RYWiQzNW42MFpxIVpKPSVtfislTkB1TVElO1JWIXIocUZMK2t0N3ZuYWRNQS11I1B3cXhAXj01U3F7aDYqSScKICAgICdLNjY5SjBrWnB2UWZHQG1QRT1ZUy0lQG1sTCZfX1gqeSZsazJGc3c/YntBOXcta1NmKzJNTXYweU9VLUgrYyV2RFEoT34kNDZqJnJwTU54JCg3MTk5T2RBY0s0X3E8azAwMnZsJwogICAgJypyY3x1PzxKdUNjMlA2SGUzO3ZSYXAzbzdlZk5LWTc1JFBAMHxWb1U5ZXpXbzNjMWIpOXsod2VAUCFUZGlye0VBMFp5eng9eytJZDZJVmNTS3pncSRMeVAhbyhHPjNLZGIxSmknCiAgICAnTzA3ZXgtYXQpaXEjXzRvVkwkNis1Rk52VFE/e1REV3t9eUZmU0R9RGAxSHxvX2o2PyhGMG42Y0U2a3JYaDN1UnFzfmd3KiprK1dUWj1VSElAbStlZEgpMFhGe3wyV0s+VShXMycKICAgICdIWWRNbz9pO289ejFBJE08S2BGSjxsXjRrKzdxY1ZKZGx3JTU1ZFQxe0F0TmhgRChFKzMkYn5IR2FPVEJXR01KJWpweDlNSiFkKEk2VChLTHs7cld8eEpGI29eVGBFeSskc3Y/JwogICAgJ0ZjbGhzdGQkO3JsPSFUfkdwIURIT1FYR1NaaWVLXnF5bkg4M1g1fjZZbSlFYVNrMVdaSCVjMl49b0ZiTEppLXRKWSM4SiZiZV5LK0MmSSg3PykkKW0kTHxmZj1eaXg/QEwrRiQnCiAgICAnUVdyY3B5cjc3JChvUnNfQ3slSnIlY2IrKUtHck9KUXE5PkFJfGV9PEJJY0o2JStrVStOIXFvemNVNj1UYlpFdX1qfkc1V2pJUU5NR1lHZ1M3bCVRSXhYNzJUeDIrQkh1bFg7ZycKICAgICdVRzI9a0E+MV9RZiF9SXVfLWdTQFRCSVI/c1RMdFRvPT44dCVXWSl8K0ArNEBwM0g+REEpd0g+OHVXbG1lfHZtI3kwNTA/I3olMXZWSDZ4WFJsKnt8QSthXnB2SDJtU255PT04JwogICAgJzt7OEB6O2tufW89e2B9N3dQZnlBV09QJHUzen5mcTUhVkNkX0pERT0zVjl5emg2c31UR3t6dGRVSypaJGVCQyp4OTd1ZmFjMiFzQFNOUVNIVm5HMjdEOTFhJiFjN1pfTVV3QTsnCiAgICAnUGpzNURHTE80Pi1HVElCJExEI2M5Kko/VF9uZTdVdSZIRDhQcWBzeU9eNXY0bT9OX3dnTXkmdDtZN2s+NzxPeFJARFhmMUU3bWBmU08/I21XUTk2VyVvRDZXQTA1PkZ5NWZHMScKICAgICdeYSZjT1FnVUspX2pzQH4wYko0bGVTPkNNX3EtZGYmbnZtSXkpcWd5KWpnYThINmRxMyFEdUR1XjtXJV91JExQaHYweCV0ZXd3JmpYdjkhWGh4fjxOLVQqZl9KdClCbjIzbEpBJwogICAgJ3B9Y1I3NzRlWWVrREF8T2pmQTFCe0tCWVg2dX5VbmxmNnNnPXl1KmFOdUZZaGU8JUI8K3RKM2h0P0JYNmJnXj1WQHs0JiMlSWdPbClHS008VVAzajdfT050UTFuSiZsYH5QNG0nCiAgICAneDQ0bG1PMX1IdmtrPTY2dHQ0YzRKeT9LUWRlYH5XbHdpckktJnFeMjEjJXNha1ZRcGooODE9P217O2BfMHMtajhUODFIYVpWNCsjb0ghZGQhNi1kbER0NlRBJkVaTzJeVmN2NScKICAgICdraTUkQkNeZj05QzF2ZDBvJF9WSG1BSnN8KW9QNVQqcUZfYTt8RDchUjJsY25gMVNxJjNmU0EmVnhVPmRHPCF8QTJ4OCEyZ1M/RHlhPT5nfkJeITA2dSZSRkhEdFNza1JkPXJIJwogICAgJzZleHcpY0x2KCFhJmhtYmJENjdzUTsmUjA/aFgobDIlWlV2aSRzTFphTjJ3OU9zfDw1aTwhRFhITGRBUzdBKzlXJHtQPTBWM2AyQUhtelJoSSZOSC1qfS04NVVtLWFHRHMrJVQnCiAgICAna3h0c0N2NUJ9QmFeKj5vX2VKYipBVWZmb0Y3OV5eYHFEeW5oaUpUdjw5SmRPZ31CUDJ3XnxtTCZoUEdfez5VaERhcTFFUUVWMk9QOH51USR2X2god2hDWnpfaCFIK3dzPjtQRycKICAgICchQGRlPXEtd18kdDJaPD4lQnVvTD11MmBrWjV8Qi1oe19KTmJ1NVZAZjVqRGUwUSVhQVExb31YMnFlNlR0eiNsQilUWUYqYlgyZDskdiRQRSVrJTtWK0ZMKDhRUk9pNTxYTmJvJwogICAgJ1pTQ31qR1QlTF83UTNQWXVwJCt+VDkmVDw5OUdPNDhJdEBZWk4qMUhwYz5TV0t1ck5VI3kmdUVYcnp6YXl+M2dqYlRpWk1aYzE9VTxvczBUQCNjWmsmTENXd2dRXjNkRmIzKSknCiAgICAnXm0xI1pZR1pKeEF0UVYhUGVQY0xtbXBDNysoU05iRy0ybDVuYyR4Pi1ObiNPYDI7fm1MfmoybFlxKEtsY3RBQlMlWCojPz9BQUtaZUtIZkw1Rk5oel52Mm98d1dgWURwQXo1NScKICAgICd3JHQxWkBWQzJSb1h4UnxJVnhTTEJqTUE9YGIycFhYQiZjRXluYmthWmBhK3RSNF5pdlFsQ0QpMlYzVnk1NT1kayNac0E+VH09e1FHXmpKJSNTUk1LPGZSMFIybVopZVhLfjhUJwogICAgJ0NeMnZwaCklWHo3dXh7MENNPzA+Wlo2LUtFVF9fTWp8aD1saUxlJk9XZzZUO0kjdHozJFRzUjxCOWxpVDxZKntpJl91S3dXTmQkNVZGQDclPWd2MEE/Zj8jQ01+ekZWYX4yVXknCiAgICAnPHR+I1ljT1k3ZWswK2JmI2JSM1paUWp2QylNKSpJIT43PV5peXh6WmMrfX14NkxeMkdGcSZIPiV4bm1SWn5xSylQRWp7TCoqNnpCY3NiR2FuV3BpQUNBLWBLN2FVYHFZfFF1VicKICAgICcmcFQhNDVKZCpUQ19BfnNCTHleYCZnbklnXytRRHM/SCZ+T0ZlVX5WVjRYeW9kYj9lbHEqekhvc3FzM1pBLUdzNzdIe14zZ2YoO0J4JlV+QzQlel9OMHM/Si1IOEZaPUdJQEc2JwogICAgJ3M0TjY+eGg5eDI/bkNzTk5ZTShQSEcldCphamhhZ2prezwrMSoyI1VeIWpRflVlQDs+RmdBaz4tYlcpYVFFYDRhOWZPOSRWMEleXl8pLTRYJHw4SUJFWWtAaWN2WnJpSjBQX2QnCiAgICAnQjwqYztuMERsRz1vKjZRby0jRm9nflBTTl4oZk0hajB9NzgxKylpRDtoTVVBdEE7Z0UxTjFXWlk4VjlpNENOJXskOT1kZkZxJnFMMmpqdjJiPkhIOTRNRklqWHVrXklPV0NmRScKICAgICc9d3dAUW1ibG1lal49MmwyUEA9cTBjQWdqYFk0cz17c3Q5KVlHaFlAN2lfbyQ+WWlWWiQ9JWdzP0BSRW4pOXQrfWFPI1h6RVA8PD5PSnRtRUchNSt7QXZJZz89MkU4QytTRTdhJwogICAgJy0jPmdnOVpackxoQ2BIX0o+VThPb1U+MUNTbElmU0gzISg3SWlmcEw+PWQ/JmJ9IWdiIz9SeTBEN2orSmBEOG4pRjR2OXIlUlE1UkUpJWpnQ09uYiExMyojeG1+UjBKQ21WPiMnCiAgICAnWVVhI05KQXkqYm5rUU1LeCFhVjZ6QF5LblRaMHFAaz5BNUVeKW03bnU+QSNSJSkwcF5eOGdvPTY1P0h3cj9jdFZAVUFJaVhATiVQZEhiayNUamAzQUw5QDxsTU43UFY8V3RSMycKICAgICdKIT1tZ18oSDt4O3UxKistYk5OQ3o1VWYqXkQ0aX5Ack5kKHtAZUBgWTB6RTZFaVM5VyQmdnxhWF8jRFJTckM1eFM/P2AxU15QWkNsQkg3M05FVCUyXztQUikzPTY9P3FJeWM8JwogICAgJyVMTUxLKjFncVBkQX0pPkB9NlFUWmgxSCVLfCNwVjxVWj54aWtVakB2fHl0JmxTKWNreWM0LXAlYDd7d3UqNnFqTlNsZ1ZWPSkwUVpQd25AVy1AI1A9cCg9QGVURVYrNnlTeEwnCiAgICAnO1o1NXZ0OG90I0BMV31xS2QxekxqKWt2LWl5az0tKkhrTSFuQEdoNGVuZTc3PXZnVktqWSM8X2c8ZXtiOSoxSEwmb3RNKztOdiZNUk1oVHNXSER5N0omK0hlWEFrQyZtRUZ7NCcKICAgICdMS1U7VDNQNkojalgxLXFeY08kOERUYXs2ZCVSSG1QamcleW5rKlRVbl5DWWNfZ2xzI0RkaWVzWisyMkY4TzJkaz9MPis3Pk9GPDRYcXFKV0BsXiomQnNAXn4jfDchWllXampGJwogICAgJ0UxUzZkdHlxJUVHe1YwX0lZVDltIWR3YVJlMk8rPisoLV93PHx7dzVwVitOQjw5MTZealpVe1VxVkpzYClxKUYpcX1wbyE0aF4/KSkybVhzLXtBVHJTJGF5eSQ+NV8+NXR8NXgnCiAgICAnNmV+JWpZXzlwOTNHTEc4YWhRfWZqajEhWWA0VzUlYVBpUG9iejExNXd7UGg5V2JaTzVXRGxCfEF9X0hWZElrYVNKZU52TU10NX1+WkpvRShKJSp5I0g8SHtpVXxpYCRDPHlZTCcKICAgICc7MFk0QWI9azhhS0tQKE5zdCNDN1NmXkpHdUs8bXI8QWJ1YnA3RE5WNk8wPX1CSjRxRGBeRTxKcXA9SmRuKiZwRXp0R3AyYHdxbGVkajVfbC1jQk9sM05KOyY0Nn5BO0s8NEtOJwogICAgJz50XyNYRTFHKTZNQTc7VUh8YVZpRUhTZGRERHREKyZaSGA+TVRGfWAzWTFObi1BSzNJelNMfHdLSXdVQW0pQU40Z3FmcEJBMj1YN1J0SWczN3puUVV2SlNINipSajMtIz8xcVInCiAgICAnN013Rk10YlFofmgzTCo9Y0lVTmxVbmZhallec2p2QStsNiFXMGRDKm9rdE4ocCVPcU1Zfmk1KkZHdnRIeG88S3syQ2RaQU09VVZTJlF4MGRpR0g7NyRWYUxWWmVxdGxLenYmRycKICAgICdGKyFLY0NCb145X3FrOHRYJHdVeD5PR002b1BVbUxsSTA7ZSllNE56PXtiYGx6amItX0duVD5iJi1DWW4lKF44OT5FO3I0Yk5vNngrYz1HJG8tSlUtZVlENmJve21VflA1M1Z+JwogICAgJ1pkNEVES1d3Q3g9dVZgZHZPR1l4MjdwMkdIWlF4KEghNEk8dWM3PVJQcjV1ZmxjSVkhOEVOMiU4ZEtufUp0dD9pdmZJfmcpTW87RUhyPy04QS0yTjVseVA/IWBUU15kRngkPFQnCiAgICAnIUo7VU1oNjE2SlhBSkFGV0hlZiFmVVJ8Typ3ZHF1NXVlb1BQYm80fD15d0Q3RyRrQDAhMnV9NEs8ISMkO3ZNJE9DbCpGLVF0PEcjWGNzPG1CVzFwaSEkcmYmO1BvSSRzUih4SCcKICAgICdQT0IzTio2d185IyVNbFR5S3soR2xXKDRGKmFOM2tQUlVBV1N1ayRzTm8lcmhEPT17MGJmdigkSFhkR3JvYFpYbEh1QkhZaHYmPn4kbE4+JFp4bElNMlo9Q1hWOFcrUS03UmZYJwogICAgJyR0MnkwZD8hKUxtSVQrQyN1TGE5LWckQ31zK3JrTVVLOSFTWFNRWjhMUTUmYlJRPVJXTXpvLXFYQClneEZVa3NpaTh2JD5DYDZYNzdOQFY8ZkBIbj5kI0VpZiV9fjBwblF9QVMnCiAgICAnPDhhck1OUl80aThMRSQhOE5Wc1BSeWtGODtCdldtTUB6U3lYeztFJk50R0NvcTd3ST9mMmhiMj4yfChLNW84MCpTZFpvWjxqd0crVlFaPH1HKXRkbDlrNV5FPyZvKkVaZS1DcCcKICAgICcoSD53I3BfWGIwZVA0TVd4STsmckg4QkM+QXElMTBLS0hGTUJ1eyMqeFNgbyY9SXh1KmM2OUsybWFuRWxJNSt5TGFYZ0EwQHRMTlMpMmRoQXE0alE8I159TlhfdTJuMXF9JUgpJwogICAgJ3V4Kkp5TVJ3ZFc1UiFidjE/R31HWGwyfnB6SylqdVZgdGhkVVV3Y3VmP1J4QU1tfV9GWk5nJHhRNEo+fTFyVWQ0ZDFoa1k8TzU1bzlzSThoQTJabCF0b3dpcCsteTs3V3FudjgnCiAgICAnVCY/RmlxYkV0azFVanEwPF5hPD9Gdll9PSh1cE99QCk0aSZxcU9XZCp4Zm5xcEgtd0tAaldHbmN0aWVEM1c0QFFBOGRoWWgzXn1AXyhkUTYoSXRfVjVsSj5gPnZXSyk2UDZnficKICAgICc+b2RnUl53P15KR31XaT5OMkEpeiprVSpyTylPZFQyTHVmU3RETC17PWx3Z0BuWUA4eTNZKmowb2k4QFBWNWVnMFc+ZU9JTXpAbGY9b3RTZFliYmNEY2V6MnBfcXpWYm1ndWlfJwogICAgJyU0YiNFYGxte2Ioc0pfSSl1PTh1V2BTcmFRYWs8VV9HUXhiK1VkbWc+UyFKPCEkUTxEZjFXK0h2SWxPcmBIM0taVHJ1NHM1bnVfdjdncUh7LUp6KkN7RXFOfmdWPUk9RVExUk4nCiAgICAnOHJxT3EkSmQqclN+SD4kbyhoU0ZjV3VCNHlZYiMlcHNePnM2WmwjQlR7PXIxe2sqemB0YHdifiswbEBVdmI9SUdAKEp+KUlIelQkQ0FVTjVEaU18cHZ7SCZGZSRYTUU5VFlQaycKICAgICdFMFFuWWh5ZyRLPTs0UyohJWpMKE5IUTlJNF5qPzlRaUlsYShXR1VPTDJzPHlfRD5FNmBYWDk1dkxGMXR6JEI3Y0hUZF9kdUstMztpZzFkbXI/bCUwM2BtSGljKGI5QUM4aklmJwogICAgJ2R1c1dsNDYkNUllV2ElbipBPmJjNWxRRFRgfjNwelpBZ1FFPU8xc2U3dVAqWD9pUXIzOWBeYn1RY2dYVWlYSnZURF81IVhKUnxGbXxDOylENlNZckFEd3AoPyFKKXo9NVpkXkgnCiAgICAnenpzTDVSPGk1UCY9NzYjUz9mJncqLVUwMldjbyV4PmJXYiRRZzZQQWArbiE/JXQraktQckRuX1BMejhaeVIqcjRobDlmSk80WHBxWE9pdzE7aUVQTj9OfXdZeD9WZTdmbVVuaycKICAgICdIdXhBOz0mYSQrNnRVfUwpfHpkYDRZezNNKUUycFEydj81TGpgYk1vUkJOfUJ8RDxsSGVTekFkajk0RzkmVkc+JSRRRCZvLV8oRVVlQ2x4WEB3KCspbWF3QyZzX3o8NSRHVlJ7JwogICAgJzlMR05GRmgrREY+VWdXLUZuPGghezMxKktra0Y/cFMyQWJxTGQoWEEhVjhjdXooKWdPeyFiYDdDIX0+dXJsPWB4O3U1VHk5aGlCKl5AeTV0YEpTP21TcUBURGF+TztxeWheQ2AnCiAgICAna2N4ai1pSkh6cm97YkJOK2ptMG5UQWwjdSh7TkJPYXIoNk04b09oMWdLSnhKR3p4QThoLXlJdjhTXjJ+bmNoWDsyZ18mSz5jJkJ1c1RJN09maFJnK0E7WD8qaVE4VWA+dU0laScKICAgICcrak80aD50aE4jTjAyZyQpbiFjPWoqfCh+YEptXj8mQztlSyQ3UlZ5YWtCSytBYngxNVAoJCo5TyhUdStoQjhQN2FrYDdLITJ1ejxrYGQje3Iwdj87VFlyNng7WF9AKWI4THJGJwogICAgJykyYUZCUHBEdHJRU2A8QGw7RWpsc2Jxb0FDaXFSPUNAOHdobXJxcXMhS0t4XypOantWRDdRdlQ/MzcoWi0wRFV2ITVQPm05MUZNYkA8JGNiJkdkLU02ejNSWXJ9RzJVbWdgSTwnCiAgICAnR21uR1QlWlNpS1JkPWxtenYpe1A+cz0zcG9WbHVfQXhVJWY3a24oJEotUG9DNlZ3PTk7UVFSbUAmKmBNYlVrKGAkfmJOM29Xeld2TGtUcnJvSih8OUt+WUxxYDcxYH5ASnFBNicKICAgICcxTnFSKUhNdXJkdChEcHNgeFErLU9iMXhmQkEjUFdXUiNkU1cocnNgRWIqcEl2MEBlcGheT2xSPUFYZDRqQmdyRiV4MWFQJVBCNWhPZ1NBR1F3diFJQ1EodmtLUzdGUUh6NksmJwogICAgJyNrNil3a3g/M1otQX5JUm1ubjVHVmlTLWlsWH5+cHJ4ZlhxITw4aWpHeSZqRnsrfk5pcVMwQXVsZEU1Uzd8d3tXUEpkayVXO1QqNz1sLXtpMns/ZEl2OV9YRmIldV9QI35+en0nCiAgICAnMnFuPj1Na2Q1Mk0kYSRGUDMpMipxXjJrWSpMP1J2eGVZJnImJlh3N143fWYkVnY9P0tvSW81M1YpVnBIV0M5M2o+VXV5eVVRVnpkOFFxN0IjdVhleExPQCoxe2Y5bzcmNnhXRycKICAgICdTWiYyXkVDcClHalFJKi1GUlMlN00rPmY4bTx1NXA1ZTtwNUQ+LTckZ3BMOEtAZVVSal81fEZXMm1rNSttT1VpcjIoMWhGV2JXKyQhYyk1YCpfX0xOXnB2O2xrPnw7bXstUk80JwogICAgJ2coZCsyWk8/TTZOeXEtSnAtZFFRMjRDYktFYj99dWRQZj9wUig8bXAmcUd0d2dsWmNlQi1RT1grT2ZfaVN7RVhMI1RQPlAxeG40N0Y2fU5qenIhbmR6Pzl4dUVnaTR7JEZtRFInCiAgICAnR3tWJTU5aXpDMWtGPlU2Jn1IUGRqSUJFe3NINm58Ui0tSEd6QSZLVWhVfkFeaFhwZz8xdGA3OCVxJnFve0QzS15zaz9jRytxTU5MOGhxUz4/NS1QKD5GUlR0R356a31HM09MUCcKICAgICd7WWJjVGJ8Z3JjMFMxZWB3fW1+dFA0KjEqS3Z2RClzJUdsRnBrX0tsJU1Xej1zQUcoWk9KX01QTE9MZ043K0F4PUoyUnErMmYkPWJ7eis8a2tWKTUzQFpBJk5uZEdXMnFLbWRKJwogICAgJ1MkQ207Vll+TkhiWTRGUXo8OCUyRE00ZzlaendHQD1TSikyc18jVj92diYtPVBIU20oOEh1KktzUXFjRkV3NXFTTS04bE0wJSh2NnZSYmFjPiptfFNNVjdeOFhKPllOMmJVJSgnCiAgICAnWl5XUVVBVXNHRTZUZklXJkVvfm9MUCVTOFoqbWB0cz8pfFBGNj9qRF5vaHlDZS1YZHBzbVNXQjxicVc2SGorSSRnMzBEYiY8SDVQKVpKfGMlKjMmTkwxdjclTXZ4cFRTfmgjRicKICAgICdsS1ZJYURJe2lBTTsrfUw/QWoxJGhCdntLKHhad1VZfT1ZQD41OFBheU18LX00Jjhmc0pUO3NpVEJ2O1JIIW90d3o1e1ZzJUNBNjJlO2E9ZkV+MWR0M21fViMkSiQqJm1AJUwzJwogICAgJ199Qz04MWJDZWhIOGh1M1FEaiRTPT4palFDe2VyP2Y9U3hVPX1NTCh4PXlQeio0X35eajFPaWNAUFhoR3VKcj9VVykyZmUrfj8rejBLXi1WellaYkUlXj9kYUMtZHtfJD84Tl8nCiAgICAndnFHa25INjFVWEVZamVSLXxpJWZeSUwyVG0lQj1lMGZTPyN5MHtyJEZ4QXBOPktOKnVpQlpuTEUlWElSaW4pQGVEYVI9KDhIUEkzMXk7eV5XOzdKJEYmKT5PT3J6XzB3eDxnRicKICAgICc4WFV6SmdtSEA2eEA9JlQ7PnRzViM+M1RSZyFKKkU7TyslMUpOcHYrSGRNaGA2bVklb287VTRGS1EweVJKR1phWTYze0ghMzRZcigtQDluaVMpSWRaQVVUUl9ORzdXP2gpSTMmJwogICAgJ0o1YmRVKmJfKGdPJVdKMUtQcVlubXo5O2dqX0FnampnbUA/U2gkb297djF+WFcrNTRTRFk/VjYzajJgMk00JmEhQytzOGNKYGQjTXJFKkw3YzUoWVhYVnpiZTFiXms2Pmp5TkMnCiAgICAnSHFrdEVLLT5WYzBfVlp8ZiRNUjcpS3VlYFo4KXByZ3VyPFkleGNJQUVoKTlPWDlIPGZFO0tCZSpgI3FhWmB7aCsodTJQdUxDWXN+PX01by0jQSspdCNffktYbnVlKDVoM0VsVycKICAgICdrJHZFMUUyN2hKO0hUem1acTQ2PVBlQjJDOVg2M0lSdU9zezE2fFo8XzJDQSlkRFR5ZV5rJXFxJT45PFpfXjxGci1RYyshbFd2NzRnWSpRdzRVfHdaKVpZVDAkTEJKeWMjR1c8JwogICAgJ2BIY2NiYUVOSklOZVlHJStfbTkxLTErRDtCak9Va1hjcXswQVZpOHFgNnU2I1lvMFk9c2UkK3V1Wld7OzxLK2xEaWBYPDR3NGwhUXokV2ZXWlJ6STYxb0VuanhraFcyazJ9I3snCiAgICAnK05gbT80U3J1aUItQWJ7MXd3a147QnlrXnJDanhYOCVQSk5fPGhXfWk7aSp4NEFzOyNnOyUlSmg5REBfWS14cjNEQUYpN1hLNlZWUkx4ej1VI0hrUlFCNlgxLSRtbV98QnNuVScKICAgICdQWDdiRXsrZUJrYHAjOzIqM0UtTUgwdklpVEhRfm5WailhVWxiNmI1eF8yZzQ7WkZSJTBNenAjNmlKR3NXT3tVdT42KmpPTCtXK35tUGBUaFM/azYjPnw4UUghbWl4NHUqSDY2JwogICAgJ0I0ZiNfSmE2cWRsfT5pLVBQQiRpcCQmY3ZxeyhTflAxekVKWitNcCRQRGtwNU8+Kis+IU94JC15PGhGQ3BiJXdyYDIlODJgeD9LQUxTcGtfNlVofVRHIXQ2SWFvWmJfU3h9NyMnCiAgICAnK3p1b09VaEJfKk9pcVcwZVFNZ35gSGNVVVdUUjVla3BYUjFgY259KFc1RStMdHBwPTRXSmxhZkl4ak0kWGl6OXl3eiFmPWNZeVheNilRNzQ8dWRBWEhBUmlGO0BAbSFrO2kwJCcKICAgICdnaiNpTClEbmpYJU56Yis/cTBKfGB3YFl9WUw5XnRiNT0pZkhFYSU3SihxaUlWT2k9TXZ7byhJdmd7cU9aJVcxYT1VeWA0WkpYaT5La05acEwzSGJsQ3o/MDJaYjs1cD8zNEw3JwogICAgJ3BYSU5IT3dBNUpURUo9Rjs5N1BVdDJlWDshUzg+OGJwbGU7KSRPUTtePit5bzYxbkM/PyEzeSZqN1IkPzxzQyNMR20mP2FScU5TKHBLUDN4cnskU3t2LTBhe043TyNsQm5eJWUnCiAgICAncz5kIUYmY2lLIW55KzU9VGluO35lVmYtN1B8LVMmbDIrM15tVHpyeHprXmpIYV8oQD1HQEJmbkpkVVpGXyVlbmNoSyM/cUxkYVdWeGE2I0NHODg9PFNpcXErYS1mJXRHSyp8dCcKICAgICctPEFZeDJxK0didm1NU0Q5dnA/KnRFaWR8YEBAJW94RXN3eVNWZExRXkl8ZH5qWFA4VDZrJUUlZ2xPK2RxMUNYeFZzdXN7WEZNREp5YENrYWdhWHZtSn1AaCNYa3BFSUlEO0AhJwogICAgJ2NjRloxe04+OWx5KCRwc2dPPGg4SWg/SG12elR+MEUqI2JHUWFPWHVBJmsjZUNrXiYha0dmbjs5PXNEfUFjNENvRmh9TlU/Nz1TbnE1fmBQTndwTlZmdFZTeVI5QTFfdlkkYnInCiAgICAnK2lEencydG5gM2BpQ01GS2IjQD9DJmRlVGl9UzZodWQrZExsUDElLWJWKk5hNTsjOEJUfWtPJmA9YEF6RnZMQmo0NlZIR0ImQEdBPlRaPC1DY3t5NF9oWVBFKUtXI3M5flZvRicKICAgICc0VEF+NlJwQG5pVkNQe0dVNSUpfSEoMihsUF90QnRAfWJ1THdLZXRhVnkxWnp4OXJhVDViZy1yU3BiRTR6YGxiYFI/blQqYnZ2SlM5SiRQPHpARGB5KD1kKmAqeDx8fFR+Q3QmJwogICAgJ2BBbVBwY1BwUEZBfFY7WmNzSzE2TlVFZyVDajJ6UXJzUVZIdGVRLTw1eS0qdj5tU0QpZWdOP0w+WGFpVVk8bnJKd0pjVzJxO2tiUXB4cGpSUFh4SUIqKnUtVT9DPTd3PyhAaUEnCiAgICAndHtJT0V8NX1pTU5oN3hpIWIzOW03VCQ4UCpOZmAyNmZjMzhQezkqfSRDQipAMX12dGJ0dWZ7UHJJSy0mYDs2TW9AKDx0RSlWKmZAbEk8KSV0aSVfeU8hPG99Q287S3UzR2NSYScKICAgICdBO1ZQY3ZkKEIpXzZzKnhiUnxkJTBQQGw9UCNBaio8MCl8Kl9HMXVEbkdIKlFTS1BTWDlFR1lUcHk3S083KE02VmooLTxTLUY3eD1vbHZycTYzOGU3bj9GVnZHQXx1PlFGQVF+JwogICAgJ1gpJmVFZy1XejwmUF99PE97aTVAaG09dkRtc2BSO0hFYyUxSVdOaSkmenIhelpmQT5MXzZTazBNVVlHWjB4fjklbEpDNCh2Q1c5LTBKSDktbWZSSzNNKGR0OGl8M3E9WmJTPzcnCiAgICAncl8kS2REPz8zOUxXPypkVFE+Z1RuJFpTSjAzY0Q9UG9sViRIYTxgIVlncStlOXIpVGRUaG5pQypadnohYU42MXY9UTV2JjBPcmFPN15ULVRHUH1hMUFTdG4kU1kmZmNmU0N7JicKICAgICdwUTwhbmdnQEJGMWhUZ3NzZnRUVG9YK0gzZj9sO35xPGUqIVhmPTVAKWFySGRZSSpNdXNLcT5Oa1Q4UWxDZ1ZjNXNiaXZ4RWgmaEV4TklARXNZT0NDUkdmJWE+OHx4fTAjbGlSJwogICAgJ0xUUXwjWCFQRDdpOF5kOVhFMiVTO25zWjl1anFPIXc1KGBQRlNzPGg+RXtpQHlrJGJ1P3BHMXcmRnZOTm50fH1acXtRRjBWezVVNkw+I0UtemJpUlYkdzleaksxayQ7SElHOEMnCiAgICAnJUJVJW9meUAqQFlBJUsoNERQU2BNQXlFZTQzUXc7WiF3YTFuK3dBVnVoTXtFTH5LeTt7PlpYMnB7UzRgVEs3eCEzcnBrVDduZWBgejA/PmpPQjY4VnVDajZXYHZgQXMoSmU/fCcKICAgICdKYUBGM09tKiZSRk57UmpLVzk4P3lsPCh8WFNhfiQrREgoPTFyVE8+K1JiIyVvPXdXOGdVUSZHVChmI2NkTzBvRi1gNyVGemQkUH18SHlxK052RjR5e0pIMiRGKihwPHJ6S0tmJwogICAgJ1pfUnNjKSUmSTZLcU8qS3R9VDhTVi1BdH5uJmplT2JGVlcqWHpJN3wydy1Ta3p3cDFZdCFZYTwxcntGSUVVMD4yMWxHUCt6eCpOPFMlXiN9Smg+a2V6WTBibnNLdXxtTzlNOzEnCiAgICAnV15LbW40TC0yQHIwVER3PGhGemBKd1hsc2JiMDBoaEpaU3EmdTNvWng5dyQzVHxBJTxKJDl6QWwkTF43JFR0USR1VW44RmtpSSNtZT9aSHZgMVJQUkVSdUs3Nih0TkY3QEFRWicKICAgICczUkB0OTRfXkhfQ1RpJWRxYzlHd0ZEcilJRyl0em49M01ycShHJWghezFkYkd4Ty1vUXQ1cmNXPUBoWXA+Xk9tR3NyWnJ4Rj9SRnB1Szt8bFdtezsleFQ3X1JjJmImJiUhSTJTJwogICAgJ3pKTG9OeGYmYH1OfDlCKWpQazdrYUk/cUxkI1hYVUJgYFImRylSI1FOcihUVk1sc2coe0IwTTc0TGIrJCs8VFpNTit5e2tNeSU+T3NsQX1nTEN6XjMmNFVrNjRoSnlvNl55fUcnCiAgICAnMjZlZHBNNFEzaFI5ZDhTb356WS1UJWtEOExAaERtMl9Cdl54MGdJM0xFO0Ahe25sTElNeT0qRmpCSXtUYnF9cWFUODVZVTxIeHpeOGExUXYyYX4mZDJ5fGMxPEN9dEhmKUdhZicKICAgICdZN0N6WWtAQiRYQ1E5ZXloLUpUMUwzd31AamxmPEMmZmc3QURaQnk0VXUoR3tkc0xDdWJHdWZabG5ONV9Nfnk9UnYjQ0gyWmY7UmckblQmalpJI3ZDYSMmR0skJXl6Z2EkWlJ8JwogICAgJ05RZXtyTTFFY31KSz5ydzZ1YFVrRz5FeFgpSUZ2UGBKTjFaVCVJSGhLdCl3ZEVMM2JHN1ZNPDNOYXswcGcoRE9XQGU0KGAkKmRedXZLS01gJVpBY2pMcjZvK0JOdyZTZCl4PHcnCiAgICAnQStoRWpCfGl1clU7cjIwa1k4WHBXTGNmeXdLPTNvQnhDU1loVHBOVno3V0xYaU5WRzBWaHExcCNkQSQ1K2NaejROK1NfJHV7Nmx6bG47STkpd1Y7T15+Mk0jVHdpKndpVGpfOScKICAgICduOzdMYzZCJDImbDhYUz5YfENBVWQ5WkBHSzhmfTQtZEdQOCRMfiNgZitweXUrT0pFRGlBNU5rWUIpfUlRfilDY2E/R0UqQFItNE8jfn1iZEBzdjlRJCRPIVFRKFQjaE9jNStEJwogICAgJ2wrP0o/NWhxQD91QGU2YlNmWjVAVHp8TlYmWmQ5Z3lrOzVgYH07Pkg1eThzQ2lMM2FYT2t6SWReUnlIJEBfUXs2bSk3TU95MGVjPUhnWT12VWY9WDh0WU9OVE0xQWJaS1JzTVYnCiAgICAnajwtell1ZT4xKlplRjJQPGJGTzU4X0VubiY1OCRIZGc5TmdJfks0QWlJKjB4cCkodzRVbSRLZlUkclYpQmJeKWl4dUZQT21pUWVTe2h4Nk09SEw5PUApPXVCSnQrQGY0JjktKicKICAgICdDYF9IeUIlQXNeN21FZkVESCVFaHZseUJOcmpOYm5xeUtZdHlqODJYd1otRWVJU2pnaG1Qdk8rdXdiZEpZMmUjeD9TJjN8a3FiK0pRbiRKbHE4X2JtRjd+Iz1ETmlnN0tDJHdhJwogICAgJ2M7TUZLQVEhP0RKbXhAdnp5YX5LK19yc2w3S3s4e013JVpJcGczVzwzfSRhd0o0cVo2bis2Xm5tNDBScW1ra356aiF8X0NoQnQlQyomVFduST1VRm9DUFB3NUNFfGVRN3MkVTAnCiAgICAneTZgZlM2VkpxMWhwckN+U3pGaTd8SzIxeFdlZ1dkVVJGV2RXMDtlMGg7dDBaYldWYX1VZ0YoZ3B9NzAlbXJiJkIkRDhNJGMoak5EOHpXZjhkZGV4aD81ZCMzPEJsV3dTfE03TicKICAgICdsfC1SYDFPZTZRcWNkQFYkciFXbjVwdHFXPHN6eTx4cnRIV3c/d1QmWXpiJmN6PGpeVTNaYmE7SEgoK3VJUW93U0N7RnA9Z3Y/Z0wqOXghRkhWSGMtQzJuaHVFbEhjZWI5SEFgJwogICAgJ3U9JWZjRWZ1b1pKUkUyb0khPkF9Y2UkcU5LQC0tJVEtUXRkaCQ1PTQ5QVNJO2pSQ08qQTl5akh1PG5CN2h0N3M4d1EpYTs+IXhHVj4mJHp0MDtNYkNZJk9VeG5sanpMd21KJngnCiAgICAnNWYmJClfUXFgRUw+WShMUFQzKDwkNk5PZSFCNDMjTj0kemIjd2ZfWGBmNm1DdXVEJmxuXi1QWjdfbVRGVmtSYjZfRTAtYiVxV2p+LXVDLXxoNWJSLVREJWxlekpEakZFUygmVycKICAgICc0UjFhVmUpczI5VVoxJVRyJSUjI2k5QkEwWT1KIXxkIXtmc3VhZCFUJlFLIU9FTTB5WkxBZS1idU5tUytsJHc+dWBpMm9YME5lPnFUWWxFTnczck5VSXwleG1WfWhhclBoQ1BiJwogICAgJz8tT0UzTjZ5cEtAK0xkZT0/a3kyJkRqNW10cGokXzheJHJiZj88fCNjU01gWHFpLVVQc0R1NDRLZEZMK09STT8xdSNmV1VGc1FgMlNuY2kyPEt1P01ZSVJ+TEdmckE+SGtaITEnCiAgICAnK2NEbmErOG0mfDxOWnNiclVNUlM8UyN5Zmc+MEdiPEspfSNvZT1kc3pPcHg0Y1d5MTZpelFSMXB8fE9LZFFncj5QLSkkYzR8MCpsPFZlNDZCam9ER1BudSs7eUBAcXZqOTlsUicKICAgICdXUFdhI3trWHh0YE5hQmc1Q3coXkBCTFJXIX5wfXc+WENFeWl5fFAtdjZPRytXOyg5KGd4cFR5Plh4fEo0Tns8WnRvdzJPP3J9RXQocjUoQlBQUy1eRWg9dl8wM0t2QHk0QC1JJwogICAgJ0VwRXBRSkVzQihiP09EaDVmUDkjaUhTel43Zl8jIzJ1Y0RQVmBYZXNAI3I3aT0obD5Tey1lckhraE03Jjw0VEh+dGtNZCZnUj94a29jXn5yd3Vyamp2bHFUcDg1QDBWVG8wO0MnCiAgICAnUypPS0hxc1YhO3V7V24qTGZZc2RQSSFpUUVGQ3JOYCYwdWQ9WnB7UHsrYDhZKSFJaCNpOClHWkJYQXFqVjNwSF5RKTlLODZpOVJTQXNYdXlae2lsNXIzWTluXl5IV0doVk8wRicKICAgICd5dyRNJXBXazw7TUhfbzRMT3g1c0pkTVdhPW19fEQpbHdJfGYoa2FVNkIoPWt4KEx9TjY1TVlRTkEtLS1lTlpWbDF3fnk8Y1clVE4hbSFVMip2dTJ4RS1TMzEwU1Q3cWdBU1VlJwogICAgJ21yblRfTzlOJEklVDxgY04rWmxRUmZoTD4kKzg9MnNHJCE5K3hVZEtfcWg3YzZfcFRoaGAoWXokVl9OZ0FBXilWQiRYYTVZSXA7bEcqVyZ6Zno3OT16emQqNWxXZFA8UiptOWsnCiAgICAnWGpEKlZYUy02UkxzMm1+RjVHbWBTaWVOUGxXN2daTXhIYFhaYXl8U2B9aThHOGRTU2M7ZWUoPyRCZ2EkbHI1YlZNPGNyRndeLTVeKHxSWjw2RXhyOFVwbD5uWj88UFV6KWV4ZycKICAgICdQJXNIN19NXlA1eDB5ZXozPVNDdjJZeVI/c0wtcjsleEIya1RNWWFiX2pLUHxkWj1ENWxgUH5KJHxoMzMqPkt3TkNrKm5acHc+eksjWj4/cHRuaFJVNkdXZnZBU0QjZzlQeUR2JwogICAgJytyY0g5KkNFZ349PHU+NmNBdVVtRjNwJFZwYn02P3hRIWRsaEcmYHx0Mj9IUGVEUypQZmZWVnF5KCQxPVhOLT14dGpaPmY+YlE+dDReIT9uSnpjVk8wbHd+YTN0fjxiel5HOTEnCiAgICAnVEYlWFQwcXMzTnl3SXhhOylpSm5tTVg5bjlFSHBHdVhPND8rRzs1U241eWJDIXx2dXs8dmpfMjByKDhCTG14R2pIKlJ3byN0I0JsZ0plIXtUXlo+b0w7T2F5ZHtifDBYRXwtVycKICAgICcxO2xPV012LWhuN197bTklcnZ9PD5kZ194K1FBbzYhNDQrNGpSNylYNDVZd3FYcENxQXg+PSNNOXN6KEpxZSVTKWZmQmk4bis1eWBfVlglUiRJdn1hSCppWiF2UzI0I3FnUVZGJwogICAgJzxYXjYrRi1Oan5xUlckY1pfK2p7MUM9N3RtYF5gZlA1NlZOUFp1VFZEVH5hbCtyJU03XkdEZVdVfk8hcz1YbD1WNU1LOHFTVXxeTURmek1TS35jRllVPlVBM3ZwYVlQNXIhNi0nCiAgICAnVUtrZFlyaTw8MkthV3RQNCFvcmwlWlhYY05iTnBwcj5NUHNYKVlfS0JaQig7dkF7OHxBaXImclpEfHxJNE43UyNqfTJ2U2tsYUFJVSNmY3BDZHpnK1JKNyh7dGNxYmEkbHstfScKICAgICc+bzdxQllYQ30yIWhCflNoXzUzWV9TVChXSjhHUio8fms/fVUkXjxkSUBQKzg+QDJQMnloV0t2QzlMPWFnKktXdD1eZGt0ZU1Bd0ZWcEp5LT9rMD17RDYreitKRFpyJEJiZXBSJwogICAgJ0RYczZEZn1vezBteG5GWHVwY3RkRTw0PE9GUXxfU0BhfnJAR3B7RmJzWG9WcG04RWNiamxKYkczbSQjZldHMTtXQmpvZlZScStgZ2xXVj4jPWwmNDVIe3pxeEdhMl5oP3x6aUYnCiAgICAnYlkxQF9jSy1nNnspOU1tRlBKRUMmTihjP0gpKlleRzZVKDhNdkl7cEE9KGh9ZSN7Pz9jIUxvdD9ZOH5hbWteS2xFVkQ+MWxPd3xUTWU2Sj02fGVXQVdKUTQqNXllfUhjJDxWVScKICAgICdBNDBrUmhAdiMjLVFoeWlrR0h7MVNFM0NWdFpnQzNYSHF8RWIqVTtvQjAoPkl6U1I3SWZgUWYqbDllPHMmMUdGM25wS1hQYmJmKD17d2RoTWZaXmNpe2BmeERuVGBAY2dXXikjJwogICAgJ2NxcEA4SEFMS05jKCQ8RzE8a15uQj5hYVQ2ezheakM0XmxzUygrdWpMOEB1ST07LVFmc2VeR092SnIoSzBBdDNnWGJRIWlMOTZaUj4xKXVzZjsrUXdodWNuTHdkOCEjWSFmaG0nCiAgICAnJHFFclJAcj1PcWBSalV9UDxkaSlwbUtOdTFXS0VeO3ZeRlBPRmNUUFl2JWQ1aytDMjgkJHlARDg0dlBuaklMLUBnP3kqRC13Jk52e0djbCo2aHJ8NT12UU56Nk40dn5YJWdtaCcKICAgICdza2dEWDQ3JnJtTHheSkxSPXxnaUJTQCZYNyNeRFNVVmBRayZnQX5BRkpNQUlTSzg5M0M3OTB9dCtjdlJXJDhjTnArJWc9MVBrSkh4T0lPUUtgfTx2LS1DfTw9QDBXbDtZdClOJwogICAgJyFmRXB9VWZWZzBoRHNgKC1hcylraEByMG88blhYSE51anNLUSR2NkU/LTUtOTNaRUpmNE5zYzZHKC1EfCQ/ZTNgdGxNbkZZWnBXQiQwPWkzeUUqZFdMWmN8LXxFdjtaU1pebXonCiAgICAnYnNyeWN2NGUkMmZyY0RXSXRLYkVMYHMwMntDKnxtP2RLc303N3V4cyE/MXVtc241KnBrMFp9NjFTR2xDVFVQJXdLaHFgNVdrUHA7JkV6MHpEX21kfXM8Vm9tLVFuTUdDR3c3cycKICAgICdwaFlOaG9rKFVXZjd0QVA2WGFeYnd+TldUbzZBK0tCdlVuWWMqQWFeTFRNTG9kQUs8UXZhNjVAdkgjank+I3lBWXhpO2RkQyolbDdOUkFBZihURlBOOEcqfjl2RFk2bzFMVkppJwogICAgJzxicChnaXU4dzNOOU52NGk1dnhJNT1AKn5iYHBmaCVFeTZCPll3cHkoIyM4VVYtZmI5Yjd7WW1wOChna0dCenAxJnVHMUs+MmhCeng1KmBpenVkRVRJNV9eUE0xflZ8OStSdEUnCiAgICAnMm5BPUYoQlkoX1dIWiVaJVZ4PVEha019aUlrJndER0NxPnRRJDI0JS0qPjx0NiNFa3UtN3ApOVd6MFpBSSQpaDxybUsqU1BuQkhKNl5sd0NTcjFEaz1XOy0tVnVwVj44d05OZScKICAgICc4PUA3ajwlKDFiWDB7RXo/PU92MFRZbkNwdjVwT2hoK2FyfXRva0VeeGB2M2MtOWNAYntCO3IwTUc8JCNVakQrd2lCWUJjcnpfUDVSdjgoRzZ5MVlwI0YhIWdhSntscEA/JkQxJwogICAgJ1plUGxCdlpLcWFTSjgtJnRGZzlSLWx7I1dmZXg5RG16cWs/cF92VGEhPzNsaEM7bHBeeDs1aUxfMDEhISRVb09Yai0oWUJ6TTkmO09vSTZwKVRRRERUISVOQkJHKHooSkAtM1AnCiAgICAnM2kySDdzfEZ8WShXU2NiKEBLcldwMUJ2e3IhREBsRVQjUChORE9LYXUhcFM9MTJGRSFCe1ZrYj4/djNDciZiWUheVCZiUyU+V3o2Y3UxMlIya1BAeDc7XzNJSWB+Wis9VlBoNicKICAgICdQdkI4MUdCQU9rWilYblRpdXV9am1paiU2dTJgUVY+aEFYQy01dkMlI2Nxe249cXxxe3soTCQ/QzNlNEpVWipKMkJubSRXWiNGKW9iO14wT0UxdG9SdjxPVkw7SEMjZCY+WSVzJwogICAgJ1FYI2V2JXdUJSZWKzclP2oqJC1EVUJSWEpaaz8+KDBXVT94NClkVSNuMVEjP1JvaURla3FgNHNzVX4ySitCfV9mO3MoSWduTHkoaSVuTCh5V2heUDwhaysmUW1lSENzaD9KI3knCiAgICAnXnRMZGB0alk4SjdRcUIwZzg+PGlWPVY3ZEl8QmM8ZFZMdyYqejcwPmdDKkV5Jld9cnUmZjc3Z2ptYFUrKmFtfjdwRkFsQnhmdGt3eyZgS0RNTGMpWWdNWERqSjlrNVNvTE9zQCcKICAgICdtSlFZIUhFSzx3IWBxXzIqVFhoXi0pNVpxPz1GUyMrWjxUVWpadlQ1V0glZkxPIV5mczx7UjI8IWRqdDNqb1NrODdBcjE7NjhpK0UqRW1BU255MTl4Z2ZYNVMwIVooN18rTGxFJwogICAgJ3BMXnhFTEN6OTtVfkM9VXZ5b1oxa2Y5ISZGNkE5M3tNWH5YOFJ6fXNpeDEtX2t0KGZOSVFrUnhnPyNJM3RzNXlKcnZJbVNBZTZ4TzdHaEpqVHF3LWhTPW08dGtIMkskY0dJMGAnCiAgICAnbiglMGhFSERMfW1gRWM2N01udm9CTz1CcWkoRXBTSE5ZNm1YTUY5YSFZT05NTnd7QmNGfT89Sz9QRU51eWgzQ0lkcnNsJWREdjheJSFgRjA+QGtnaGtjfGFGaUVzU2d1aiY8TCcKICAgICdFe14tTWo/dy1yTE53UHZUVG5QaWVQcGFIJFNydkxMY31NbD5nYCMrRk14NEZ0N2ImUWsrRURmaDNCfExUU05hYj9RfFR2V2A0VVU1JSt4KGh3fnJMUkFzYTM3OGh6e3t1TndAJwogICAgJyl3QCo+O2F4YGRIRWF1QEYhJClKO0VQOVRZeCU4QURDS1NgTUIoaXc0PTg1dT52eiV0NGV+OVkwY3c+ZE5YWC1vYkJuZkJeREtFTTghMTtOKih7M28oY342ezc3fUwkMWJPX3knCiAgICAnZkFjZ29YRGxXe09+QHQxaCFqU3taKWd8JT9HbEA2T3gofF9hNFM7Y3swMjs7Y1A0WWdZc3xJUWVkNGxfRyN4WUd2Iy1pMWoxbFg+bF5lcG1wS2B+b0JWYENuY15jMWZoX2w+TCcKICAgICdyKyM1UVNXU0t9dWE7O0U3Z0tnO0BaVjt5azA7VVVVbDZ7QFZYM3Qle2NhMyVRKmYkJDB2fjFFViFZRFk8Uj1qPDlGVD9iV0tBKnRZO0BhY2FRVEsxNHBgakVqd2xsPThkQj4yJwogICAgJyQ/cUFoTTFGPzM5YVVzQmdiYjt7PjwyfU9EJWk7X3VPSWVwK2N8V3tPUU1IJCloKDhKXig1YGIzS04rKHZGeT9gcjdMUFFlZGhaP3w2PjMtVElobSRSdlpTSSU3TSNHdWEjMVMnCiAgICAnNCNBbiZIc09vZWJ5YUM+aX1McFRVU1lBcDJNIyphJDVMMXRaTFJVam9AclJGcEMkZ18+IzBFWVRLfHFRd1hnIXRBZ2Nkeko7czMyV0dRb0lecyMmTXUxemtQR3V7S1EwNFAlVicKICAgICducSN7fEs4dVJ3TmFfdFl7bWl7MjxrVld9MCtufnZTeFhYP3dKMldTZ2NLcn1fY30rK2RUO3xUPTYkPWlyTVRaN042aypmO1p7az44aEIheHxCZih8cD5hdj4oPGA9TDVFM0lRJwogICAgJzY2UzheKHdQN3NgfFVpU1gmO0x6PTBNKkdHTFF6a2c0VUJkTUlPS1VTVnB+MGNsaEdOKmw4VmxsK2lmVyhJVX5selI+PFZ5Uml7aHZ9fjN5YjFtTm5YZFVOdTBwUHFNajsoKmAnCiAgICAnVEc/WkoyNmAoeXROUkJRPGZjO0w2UkdmR0hNbE15QkFGdktjVHpVOCVoZWRMXktyfnd5dDx9JSFiOWVFLXt4UTFyWXN6OVZSZmh5SGF2NkcobT1wLWhjVXckO3tteFkydFl1IycKICAgICdJUzFhfEtqKXcpYjNIKDA8bSR1WGx0JkVMWnx2ZHQ9MT5aJHhjKUc/eFl6KkVPWSstclUhR3tGcVliX0Rxfj1GdWItbzNhZ2B8amgrJmt1VT5nTFUtbkZUeWJBcWNzNXl7XkFiJwogICAgJ0oleVJzcTVgVW5ufmN6K2BScHB8O08yKGhPTFEzQUNqPFdraSVNWWJ6I2JedEkweVZpci1EV09ZMlFHVVlLRkIjVXsoZUohTUNBPE02REt5I2l7PEtOVz8wcHopJmtDUClOSmonCiAgICAnJDgxbio4IT8qN2dKJjRIcmdXKUdQb2doaz5ONksyd09VdnJfK0hsZWYrWXkpS3taLXZ4ZWkzWSR0LSRGcTV2NUl3MUhgITE9cVoyOWNpXkduIWVWe0s/IW0teVBjJGlCe3hvTicKICAgICdrWlkjVWR2OUZwdyU0WFJBSmwjeGVRbkUwNCpCWCFAVU5YQ0lKaGReOyg/Xn4zVWVVfHJzPiRPJHZ6R1RUTz1leENlSkdOP0ZeP0MxbHRCSkM1Zys7NzBXZVR2dk4yWkBGTHBXJwogICAgJzY5dzxFe3pYUVprKDI9eENjISZmdVdXQz5ObVlyN3NyLX5eT2l0IXZXRi1yakA4TEZMSzlCXntVeGpCUnNBRmkrWTA4eS01PXsyNE1VIWt6ZW02VD9xdmwqeHk9YFZ2TEBfPT8nCiAgICAnJHJzUVFifjMyeS07ZjU7cW1xdn02NHZJczJuRmdEVWV1RitofVYlTCkxbyt2QWM+ZEJONWVRWE15VmI3JjFsKWEwQjhyRHE1ZTZEeCloTiNoVzBYVlE5SS03TGYpZVNuY0VTZycKICAgICdXUDVZUzI4VFh0TyUkTEZfYikhfmcqM01gPHJIZX0mTEtmKHJDcihjYE1eJDY9OUZufFNeM14wYlFOXmpLOFRNVVo+KHBLU2o3IylSWj9PeEY4dVF4OFVFLSM9d3QzNUN9cHBsJwogICAgJ2NuaiFQYzU9QCshNTAlPV9BSE1uWkYhZkQ0NllZMkUhal91OFd5PS1HJihZOU5gJVNzWSRxSyU7Yl9OJSZVOEdOSlk2YytMJUBAeV4mUnx5UFh1VnkoM1JqZjJ4aDM9KHw9fjInCiAgICAnaXZAJXl4dVk1e24+OThpaWU3PTBAVTFUXncoQ0V6X29DMGxLTU43T1FhWCl0KGt8ZTEhOTwjT3NaJlZGNDhkeDkwQjBeVGV4XiRjcE9sX3xQe2lDeWJNUVI0XmVDZU0hVEt4OCcKICAgICdLPF95SHY2R2lZbmZ9OzFaNlNfSTxRbUwhZ0xZQEl3VTFOZXhwJjA2ZHlXemMtUip5THJ9IylDTTJmPGItNyYpVUhWWVRvdiMzZ1lGeVN5U2BhYmE9dWBJbiZtbUwmekRoSjwpJwogICAgJ1h5ZDVMZmU8b0R1VXc0R1FCO0c7SlRhd3daMTNYS1VXQytQTU1Jbm5vc151WjE4aEwyJDFFbmFlK1dYM1RMcnt+RGdsO24mUDV0MVh2Z2VpPXBsPSNZQGRBVWJfOUp3aTlHSWUnCiAgICAnO01rRTFRJnR0ZXdlbm1SJWJXN3Q0X3VQMVFoQHRka3w/XyhTUVhRZ1EmekMxeCU0YmVqTk9gfDZwTkpRMmNWTmNGUTBARG94Jil+WXdYczJySFFMRStRI3hCdEVvY2FYajA3KicKICAgICdxKyh3anolUGk0TmkzJn09cX5QIW9vcGtUZWpUUl5ad0xoKUdVKUp+IXhWbFlzP00qVmpzezt6eGg2IyZjNEMhO2BiTzlAeHclfCMtLUxOcXd5O0h4TXBuSXJ1JDRINGtYK2dnJwogICAgJ2pFR1EjfEJUNDtiVF5fSzZeQkRIa0BwLWB5QnM9VyhkVF9xSTJ4OSQhdDVBU1ZvPWtzVVpsI2lNNmcjTWtgfF50aVVnek4yK0Ilcz1nVXF4JCphVmhiX1ZqNkE2VkhreWJaNG4nCiAgICAnIzYjUUp4P2hvVm9ZaT17JG1+SHdZY3xtRDRIeTspX0dGKF5QWlIzQjkkPnBOQWJlRm9yJGd8ZTl+cSspUWQ/Z1JkViNWYm5TRlF4ZGxhI3lLOUdiPiN5YjlwN0gya3c8Jl5fPycKICAgICdQWmxrPil9RUZuSjFKWm8rVmVyemduRE41dHhtfHpLV3lYSTw/NzN3SlpQVm1vOGR4WWJGLURzRH0meF88VHhXdE56bitxJTQtS3xJe14rYld9MGoqKVd4bmdkfFohTUJjXyMzJwogICAgJzd9K0YqdSlYZTtRfGZpYyZ5ODlrUkc+cz44aU4rTSNuLUwqVCMheHpxZVgkYUV9S1pFRCNgc2VAbzV9SHB4alVvJldtMyo1SnhBciYmfnxveV9OS00hZjA4OGVhTSNKeF9+ZVYnCiAgICAnKT0yWDg5PEtEUUVnNmhRcjFLaE0mPVU5WDN+MTElVVk/MmY7NmYpOWlRWHF6TC1hTzNjb2spT2dPKHUxdF5VNHN3aFB+YFZlbzJ8Sz1sOTE3bVM3ZXo8Kjs7X0srdGF3VGB1TicKICAgICclYnl9Vz0yeiNtJkM/Vk9yNmNCaTgzKWQraWhoWnd2JmUhfnw0ckIqVEJteTBBb1dybTBaNERReihiMClFemV2SGRtcW5xMkw7WG5NMndsYThJbH5vdXcxVj9DYD0qTXMoTjFHJwogICAgJ0ZORUBFaVJePVNPeVFLSChAeGlVR0JaYnotZmlwfm5TR1FEVS1+bUN2Qis3SlpobT5YUjE/IXcoV2JPVDBraSRmWmB6RCpGPk1hfUxHaFBoQEdDaD0teWh4Kks8eDQ/V1VvemEnCiAgICAnc2JnJF9pY0kqYWtxZnUtJm5gJHZ2RHBJMGNZfUl0dH4pOXJ7eFRMIzFTdkA8P1FVPzRpOTs8K0xIUWUhNjFfMFk/SC1MRmAoZChkWEtJWmV4VWQyeEpsR1F+Y25JLWpaaDRmRScKICAgICdXeit2ZSliV04+R2VBRzAxbG11OyFfVnxVWX45Rlo8LXdHWG5Lcntab0dxe3wqTGIpNE5ePm4zJjhLOFU/SWtSLThFZ147eHV9YmZLSn5rS0pUX0VLc2NUe0J8NjxKP2dwbzhJJwogICAgJ05uP1QjcHtebH0oYTV3ODZVTVpuOzEwdXAkVVh4WlNebDZobkEoXmY2T2RmUyhuWjA3bnpTeHdSNndBbSFeUz47XntGcGEwVDgyTGplMVE7PWpzazkkREg3SmxBdCVZTmg3KyMnCiAgICAnWVFZI0BnJFU9SzUqYVlsQD5QNSFEbVJUKWR+ITB2LTQjO0pQK0g9TXEqNGtZaG1FTEFkTDx+S09NRy1oSWhaPThaajdwKTB1WCZiPnVDdVVSM19PeVd7RUY/UCZZS2V6dXlJVycKICAgICc2VSt1WSk0N05zJnp6dWFRJFk/YV5efWA2WEZAP3R0NiNWSU0xa15UV3NaeEc9b2FRKjx+O3N9Q0NHYzIkKHpEaWp+WFAxWkZaXl8tKE05akh5RnYje1NKbWhjMSR5VzErPnZ9JwogICAgJ2N6O0VXSzAkZGlWPGZuM15PcU5+ajw4T1hDQyN6X2BpSWcmQXV3dndEemx0WkwrKXJVZlZRRWdlZ3k1ZXtEPk9jUXR3N0VGTWxPU3JKS0c7dmxEIzhIYTFWUmYmPFMjQkorIzcnCiAgICAnQDdTUHh3SFE4eClXTUF7blVpV2clZEB6R20yQ3J6KHdjOH1JfUxycFB6NlViO0x5PHNuaHlLTjc0X2FTcXtQWXZaTURhPCg4LX1qeXpJUmt1UExrVCREOT1UPnt4O2FkIWVEbScKICAgICd3dHMxalE8JWRePFRFWkNZT0FUKGM5SCVDJmxuezdnK1c1dDMhPkQoQDBRWXNAdDc2QT4kSzspbzl5ZDk3dkZAKEU5JTtuQnJNMXt5KTxOTG80fEZZMSs+dSZTKWNvPEApXkU4JwogICAgJzVZfE91YkB9KUpMSzA7amVERlJQPUw2UnMxa15hNE9WRGZyQ1lBd2lsa15ySHdtSE9nTSF1aUlwcWtqcnV3RWpoOUVNNnM1ZXtFdk1UclEhZH5eOUY3QUFIMitte0tgej5ZfVQnCiAgICAnO2w1fmYtM28rTWJJPFRyZXl9NlhAcTRtenMkdVZ6TFVKN0lZZFNkIVN3Ynt+NX5kJlEmfnxXVVhBSTNSelphSjVhMFg0MG9TMHw0TW1Lcjgock1HUXdxQl4peyFOen5MUGB0QicKICAgICdaUzdESzlteCV5RCQleENFRTNPLTJvWEw7RzgraWNKOUEmJDY2VjlDSmhkQTUlbXk1U0N1QmxqQDV5SFJZXmVeaWc0S1k5ZVNia2w7VkNeM2Jtfjs5aS1FQHtmYyFEWnFlZG5MJwogICAgJ15KajZNTWF+cmo1NUZ5OGJHZzNNJDErM350PWxyUipGYGchOFJRKyYycyNhVnpEOzBXcTtHZn5DbmxeLWIocEBhdFYpcDx7dnZlZGNJIzdBYyFCTj0jfTlBQFRUOyMyQGs4MUonCiAgICAnQCNgcEJzIXU3TTQ8XkVqPk5KbjRZJmY7Ynk2ekNPXjREQD56ZVJEUmx0Qk9aOTBGdDEqbVh2NmVvMXMyTV51fSR2NmhXWGgtUENeOFhoPUZxdiVMSkJfdnlXUXg0ZWtgWEdNaycKICAgICdTbXgtZVpUa2c5a1BuQFJqPWUwVEA7JSRHWT8zWk9DMUwpMk5Ybl9abDk7Km1mPzBRb0p6Y0ZVaGhlYXg7RTBIUEU1RXxkJCghemcpaFlicks/JVBrYDxiUS0te1A2K1o4akFmJwogICAgJ2wwKWJ+cm45fjJGKkxDNFBsSlFOVCRUc05IVGVjMEA2NG1XeFZAaj82cDM4IypHbThiTVN5fiFhZ2g5aEB2PFp4YmQhT0UydDxMcFZJbyVKIUV+YyNUaWdhbE8mZmZUPCtNKWYnCiAgICAnKytnaiRWVFZJaDJhQV9KWUBXaTtiNiFhNTJ0e2JMNnIxQDg8bEU9Sipke21VdCphM1omejVfdikwMlIjJXJ2JlNFPTEkYmBJPH05Ki18eENsblhrQTlQSVFLek9gYSFLPSp5WScKICAgICdnTlQ4PVRkMVdZJVdjPUM2cUw4bihse0F2PG9SVFpnKW9XPyUtSGQhT05VajFnT0IjV1c2Z2c4MlM/ais/fVVTIXZ9cDFtU34oaVEtX05raV5GZndrQi1QNzd3JGYtfmRwelVGJwogICAgJ3FkTDVPQz8yOXplfjdBXjl9Zm9pLTxWVSRiNiFEUWlZKXF3TWJrZXMhN0dvUmNyZ2dTITdjMVpnQWI3fWdGQ0U2NyhvcVc3aCF1IW1ydGwjI18lNHNHZit3WGhDdyNrQ0x6U00nCiAgICAnSDNLJWk4bkZDV1hoWSU/KWdBfUktfWFUcGA+PGBjWDNmTHo4Rkw/KShIbFZAdGhJcm13YzxvKEkyNnBJLTBrNF5LRzAwcDBXYnFeb0BFN3dZQWh5ZClsMD0xbk92cSEwPnRTKicKICAgICdhWkk4V2ZVYnY9dFF6bkB3Mi16Y0spfEs1RmRTMUdBJj5wbjRpfHlzRjctKXZWLVY2UXUtfX5WZDA9WXY0IXlUeCR5eEFvR3A5RTtvalpjUk9ebXppITxsSGlVWl5mYDZPVVd3JwogICAgJ3FfSTV+ciFfOVh5KW5XMFFKbitWMjluTFU7Zi1gVU0jSlJaZDJET3FaeV5oPFkxQyl5YD9ZMCRxMkJxITIoT0JxQG9aJU89cWdKVEc2Y1N8SUVII2orIXFLeTMxfmlhPE5IVGMnCiAgICAnOEcwYCpLMX5gank5eCNwKHV9T1VwNGRlMjs1PSReYD91flB6VzZ1X1ZsbHk5UGNBe3N2R2Z3T01PPWE8RylGY3w0WUcpNmhsMlhlaEJ0fH07dXxHUXU3bUNFayZ1dWBiVDQybCcKICAgICdFVUFXKXw2UyRVbz1Zakk+Y3g2fW1lQXpXP0pAYF5WMGpCbkI3aW0xNWVvcVJgOzg4YHBHT14pPG5OSXUrRkIxc0JjTG5gTmpaY0R5dlVsamZ+czh6c2FSWmVneTZxZXB+ZCg2JwogICAgJ1lSPCErJGdLS3J0YXhYZlcmZT95JXJJJU1lekBPYmRwUWlnMEooYnJaWXBRP0hwRz4yLWxUc2MrJGdqVThTOD5HSXVFZy1ObntvQUh1TkhZQCF2QmZga008MypFUjx1YEtGWDUnCiAgICAnRWVeZnd5V08qMnluJT9HYDwzTGwkcm4/RHsxI0VFQ2U5a20xZCs2cSQzOXdVXypQfipvMEcyRmQxY15Ue0I1NHBkVVgjVDAlbjZ9ZzB1cT87ey02SDdTKCtPJHhTWGFQKihCKScKICAgICc4Pk0lLV58fD5wJUdEUkpEK0xULUw2QGFuWHFnMTY/NzU1OVVIfElYayFKZkUqZVdSI1czTjFoPTsrN1gqUVJjQTBhI2lWa1BwMD0mUERGJCFRJCMxMHxvUmRReUkzOHMpUHdVJwogICAgJzQ4cDBmNXVmZ3gtcjZiTF9hX3hVRHtQZW9yLUNaYC1pVHxnNG0ybFctOS1EWndYbDUlclpgWFBCak56b0duakxOaFdZQiZyfWVoI1E2ZDhYakBXYUVlRFkoK2g0cEpsbk8qaUYnCiAgICAncWRQUUZOZiRXWnVLd2V0U1EzK2psWU9IT3ReZF5hRitXaCQ0SjEqWG8zQEpQZT5me1gqZTdpSy1ESGheek0oUVUpaWpBIURnKyFYVkplc1MwPmleazRAVDE2cig1az5XaiN2aCcKICAgICdpPzc7OVomfXZ6c0F2Y18jdzFRPjNWal9rNCtGXmhGS084Qy1HeHcmQHEwTmNiJUs9P2FLZHZ+YlhHWkg/fFI2XklaSFAyZElvKnJjVDlGVDR+QTBib1ZxS05DJExsY2pqbzRPJwogICAgJytXYCVLK2peZl82Z3ZCM18ka2gmKXwldjg0dyhiMSg4ZXQlcDBNK284QHFURFg5NyU1akY7NEFwK20wc2NAP0l0cX0wYHNhUVAhUUw4MW8mY3lYPD95aXtNTVpxTCR8JmxjSzcnCiAgICAnbjc1YWYyb0ApR1p3SSVpakpKMGpvdWJ6PT1BM1J0dExfOFI+PD5qe1k5WDY3ND1MZSgxNG4/MnVpKTxqY0MyQ15NQDtGfEZ8ZElsWnw9Ml9lbHszOEJ3NmNwLXt3QXEwK0VFWicKICAgICc4TnZ4IT5KfHBjRGRoUj5eN3ZtdjREaTZKZW1fOV4lRis/eXpuSVhmNVlSQSpUJFcqO1g0V0hiU35EbzhabntleVNHc20+OUhJZnZPZEFDUEJAQiEzNkl9Y2koczhJWDk9MCNfJwogICAgJylFazhSZ3NSdiMhTXxMcXArNlcrPD1FZURga3VEXkA+WEReYkpQNHlGRFJ0ISM9YF5zWmBCfXBWXj9TZzA+KnxeazU5MztuMSFeKVFaJSU+czN0d1RZP05wOHE2NCo4cUE/V3EnCiAgICAncTctVFowczRUTyVkNTNOR29YQUloU2BxWHNiWHZZM0ZTekI/QiQxSSNCRlpqIWBoTnoxY2gtQCVkeHx4dEpjd0NGbk54PVAyMCEhMVYtRXxWRnkkU2p0dztLP21lanlLUT1XQicKICAgICdeamBIRG0rWX5ycGBOO2hTV15xZHQxbEk1Rn4rNTZwTjR3fl5vNENJTEFBVHJmfVJeZGc0bmE/fEZwbWhHdDBnUUQhX1N2LWhUbVljKnMrQkZUWVVZeEJ1I08xREYzOGJvckQqJwogICAgJ3hMRDtOZ1JEcTx6R307fGxgUFUlRH0xfU9tLSVlUyRvSE5tIyNibTxPSWB6ZCEpWHNodT84THstO016VUFHfDxXbnpZV09UPkN3JTtDMCl0ODBZSEE7T0EhbUY8YzFOJTFGNTMnCiAgICAnUiNnXytlWHRaKDRJY1M+RGhIKmVeUzYtUVB1QDdTKjclYytnc2dqdXJfaWdxYTFxb19iPzNCKSY/cWM5Y25FY3kqQkd0RC1hK1hFX3R2VmJaaDdXYUp5ZnNKIUtFWTQ9bEo/LScKICAgICdGKVI/d1Y5dW8zemgzKUdjbj17WC1Wbl9HemNrZlE7V2BXcmYhOCRnejZpfTg/ZXZyZHleK3sjSVc2KztIeHQwNz5qeWZDRFZAdHxwcmlwRXJZPzgrYk54Vz5xYlUjR0ZVRDE3JwogICAgJ29vITNDZ1Y1O0AwSGV+NWNhRWdIaiU3JHlKR2NDU0R5JGxxSEU9XitoJE9xdSlvTGNNKCFrQTBTcjZpZHhJR2hzMk1LajNrVSZDS3l4KjtCNXBLI2Q9V1c4eVdZbHtlQDliflMnCiAgICAnRkF7dnpXYVpzcE08YW90P05Nb3ArTTl7ZiNjRGhmMD4wX1llM2pJTjAlMnl6dzRnUWVUbnIwPjtDR1YkTDIwOW1PbztrRkxkPDh0Uz52dihYWDNwOV4rfmxfKEQ/QCRyX1UycycKICAgICdDTjhwWiVSeENNUF98eHckeGRoSC1idF5EJDZueE0lVUU1UjRtTjBATzU3MjE3O3B8cTA9dTYxNWJpQXl0S2lKRGNMQXA7O30qZlV1WGVPM2VURFZGZTRIeyROI05hTiRwKGxMJwogICAgJ0c7S15IZnVHYXxuZkRjRypnSEN8WCYtc3IqZH5HTmheTiVSdTcpPDJwbj1LdC0mPXFBbDEqS2JYQnJnciZ6bikrX35tRV5mKXlBZWJrKzxvdkk1MF9XR3k4UFJ6Znx7fEV5TkgnCiAgICAnVXFpfDQ/OysyITwxe2FRbHc+YnRSazgpQCNoKkhzZExtT3UwP2Fye0pqP29OSUlLfUtyUSRTckY4OE9ZS2hAIUFfK0J4Kkw4VzRhdyZaO2wqQjBhJTBvWF54Q3FyY0xARm9QKCcKICAgICd5PkA2Pm9MalEjQjROYmZoRk5OaE56bEZjN1k4TVJrcyNeK1NRPk5VYDJPVyVvJmJ+PCZkO0skPFhqOGdjfmY1NkxVRnYkKH5QTyo3JWJzS25gTU4mbHdFVz5nYjhXdE9eQWUlJwogICAgJ2FWYCh7M35QXm0/cXw/VHQ+Jk9Pe3U/Q0hGSX5lJCkyRHE9OVlPPGNEJlJQVmkwO2h+cDFRPz4+ZzI8PTA/Xz5tbl9tR3FmZ3VTM1d3MVJEK2BrRjZDOUF5emB8VzBjLTchVGYnCiAgICAnYTMkIVJVNGV2PVVecjY2VWpvcHsyN0NaNjNzUDBxKzxDRkRCU3J0V2VZYT9VendhaG9UalAjfFBnSmNVaUVPOE9yJkx5SDAjZ3RWTUk9aiQpdER1ZkgzaWteXzJ9KT9zPl8oVScKICAgICdwU2Z9SmEoOUA5XzJ5eEN5QlpAYklgSU9CUj1EaXJeZlBIU09fe0pYOGpUaGtTRHl4emB7Mzh+TV4kT15QPmBCWVM0RSVLQHdsIXs7cl4+JSNQfD42Y3l5Nn09SzJTbTBQRkZlJwogICAgJ205TCt8MmNkaXBQKD9mXnN3KyFFU1EpNFhDa3clKmJDPWI7KW8tcn4hR29CYDtXMGA7dEhKYWtkczBUSmVQND1nWXAwI0U4cW1mQnUoZGMoSWxOUkNHbD19eilxUlFMcmpNQ24nCiAgICAnKCsoMXclbTU2WFhudjlFPVd+fDwkcUBXdXBCeV53N1pIZz1LcSokRGJvd0EzbUNGOHRiP3JOIz5HREEoKDR4LUMoSldlWGl4blQxWm4zP0hfdVRQMiU5RUpwcko1KG0pVzxiSCcKICAgICdwSGc7JFBINns5c0VrS1ljMFZjbE5VQD1aKnhqJlg2YEkpSnlYMjl4VXJfI2NQMU8mdTNtYkN2I0EhRlBodGEzWHJ5ejlMNzRKTUFaM0ZwYWYqYWV2eFpPWlI4PF9ZY0hnZyN6JwogICAgJ0pXWDA2b3ViamsjI3s3TVJGS2wwUjkmaiZ1Vi0jKzN8QV4mYlc5dyhWNVFTbDh1MklkeGo0WDhIfUcpd3d7aFVhaVo4fDtKMDBTO1ZzMj0oditeMEBHSiM9RzZjciVabyExN08nCiAgICAncUxQa25LQHB4bVgwZTtARnV6e0hsaGwyIWlQaEVOcVkrd14pe2Q9XzFFKzdNMSF6PWI8NjF9V3ZkciZ4azA3dXdEZmU1T2lMbGhZU3hLbDs+Pz9sPjdndHo3dyU0MWhecX16ZScKICAgICdYe3FAZ15WS2FhT15RWW9SJDwxI2NYdE9xUkY1NFFwRGlzVlN7JEo9PERWKCtvMT1QZCgxTl9CWnNCTmFjTDY2ZiV4PTZodWoqTjs/d3BCRnxJT0tsPCZfU0pXUnM5QVA3IWxtJwogICAgJyl4S0R8NyZSXillbmhlY1BiOHlYejVRfGBSWCFrfE4/OE0rJG07KUBUTTRmNEk/O0Z+TD8wMTtTZWRoZjVHWnAxNUR4KFokKjNvVSN3Ui1tSEViRSYmS1NHJCp3eDZhXiRJZz8nCiAgICAnTEZDRkIrNmx9U2MrP3RVYGE2JnE5OXY5UDQ0aUY8Zy0qJmRySkkqOz4oWj56dEwxYVp6VjY9dSZZcmhATExAKVczTEF8RVlsMnNodCZDUWw/VHhwQCo1SkpoanVpJk8mQHN2KycKICAgICc/bmorSzBKQ35RJUlYUHxIeyN5RGpFZERfT1RReSVQV2BTVz4xUWIoXi09I056cUVNI3UpfjA/K0N0MWwqNVYyRmRQdW0hcDFgQGxBRys3I3t+a1g7enVwZDhgNlNVbVFKR0l1JwogICAgJ1R2R2dsYVpjPkU8dm9wO2NAYWV+MWVwPFBVX2IxdjB4UlVUak5vZjNxOT1BNms9Z254X19iK2VrKWVBKzNYYUJOYVI/czsmdTxnT2ljbVlBbCZBRmZuOENmeHpJczMwNmhzJSknCiAgICAnPkVWPk1Pd3FCQz1QYUUjNHl+S0dGMGw2LXh5WlkycXlsfDRIMyRYJCNMMD84aElLU28wWE0rJkheTnZBSENIfDYxalBlcnQ2TGBiU2NwTi03bVI8WXNZITJpRkVFWlE4b08lQCcKICAgICdBbWdTTkkzbD9lWT4mVzJhJkdEVio8UUZYTSNxKFFvY0dLVntQVn49O2x3MVVYQGFUO01LZ0c2R0QkMz9zeUZhSWZgN1RyTkx7KDlGJVd0YHRRUW9APzQqNkwxcjdea1liTyRmJwogICAgJ1BtSENmMWtFIUJsczVAc0wjTW4qKG9GN1N2WE5CZ0w5MmpgZn5xQyhhc25CYmJUbntxTUF9PyV7K157cUBpNVJDQlc0PT05NXx9ITByR1RHWnJTVUdpeE9vTUYoMiZEcVgjUGknCiAgICAneGhsd0h3I34maz1qXi0yNWo1SmBQe2pZWClYU3U8QyRRdT1sVm5CISl5MHdmP158XkZhPDU5a2JobGxRI2MwWk1YPj5DUFF5T0grNj8/TEA1OG5iPmspaTlZSnk1d0tJfCNsUycKICAgICd6eE5aPEpxTW1vMllQcSNrQTJ8IyE1enE0X31eZ28jP1EmMy1Jcio1SUxNeHlCVFE4WHo4PHdtMFo1bSFXNXlsTShaJXpHTVFeXzVPPHgkVldNRTJ4WlNLcXw/Qk1jK0smdzF1JwogICAgJ19WRll0JG9XT2RZYXUhJWlmcU5fSGtmOWA5fFp+UmpTalpKMUdBIUQ5WillRFN5fFk1OGRkc3d1am5Qd2lsLTd1ZFcmN2NKcFImMmVmVGg4Oyl8ZXNISUYmbXlIZnI5e2o8RmgnCiAgICAnOD5hdm14ZE9xVHBGfHAyblNrbXRjfH0wTms0NlVoNTJsK3NtRTdjaFRTVXZLY000IU9eP1dfKnkkU2tHS3JTaVQ5a2pWcm9vSGdTOW89ZG5aNz9ZZE1DfX5Rb34lSXJxVXM5PicKICAgICdyOUJMMnFGIStNY04qV0xLck0jbzFZRGpVYzsrRlBMaFBGSHBlfERgU0xGe00odzRMN001Y2hyWT1wWTVBdk9CeGRHMnF4d1JxSGp5NWJ1PG82M2RFeXlYTHlaSW0/TUtnNEdXJwogICAgJyU8Q01TTjs5dkoqUHktODZDSDRAWS1jYTtxdmg/RjVuM0pGQHl4d1V2K3dMVU9UTSU2MHZ0flVJU15DZUU2djxrP0dmOWU9T00pT3pUMC1WbCFea1BPaCR4diZufmk0YX1yWXsnCiAgICAnV208Njs1Vm1tTl5QNDl3K0UqMlZaY2xKSVJIIT1JIzI1Jj5ASGdoNXhZcnhCVW1MZktBOzYkRiM1aXZTPEROSWsoS3FXNyNxX0RAI3dATkJFTE45NHFmR2RkO0hgSmJHb2wlUScKICAgICdKSFMyQ3FJY3FOJXNiPWEkPG5RMG5BUkIkLTM5dD1SeD8oTVp2eEw4a150Z2k7aFA+djBEWDlgNUx+bTcoVzZmUE4hWGNAPHNBM3s5NEBubSFGVjB9V35CcCkzUTJ0Zjhnb0o8JwogICAgJ1ZWPkAtc2o8M3EjLTl5SDZBaTN4QjZMWXxTSiZQRWo4RCVmPGltRSopeFMpMT5pVH5nOXQrMCZ0UUt6M0trYzNpcCh7ISs7bn1jRFJPUlNSUD1eV3Y2ZmcrKyVTaDRJbTVKP0AnCiAgICAnKHdqQTw0d3cmUXZseW9eeDtAflM0YWN+SnBHdz5rQ3daJGYlVHc4PCM9SUdCIzNnLUNqbjhKKWVifVRIbEk/SC03ejJLSU05a31RN0BfaH4mKSRyKmJnWUJVUUx1KUM/X29AcycKICAgICc/QGhMT2c/P2lXY1VHK0Vua3dha3M0e0ZtUzg1LT0ofUZpdktPVHF0X1pVVE9FfVB+Nyo4NHVJLSlyWTRXfV49I2AkZWFhSzh8Rz1wcWYlZ0o4V2QqdSp2ZG80aFhuXmY2V3dfJwogICAgJ2wyb00mT08hKGlDaHVJIWZLSCticipKZT5hT150Xk9fRlF3el5BNTxqaVItMVc/Zj1ZdS1LbmpoNyVtdlpnaFFNWDVZKCMrSmdyajhkJVUtQ2JUYWUjPmxLWEF2I1NFOUhSbkInCiAgICAnTV5ja3JXbDgqWi1oTyl0UDR0QSZqUCVgODFQRHdzJFdYa2FvVW5qJUx3O0NMe2w/YD0lNWN6MmdMWEpzRntuWnE0VTdlZmtGY3xkb1E3Tlk8WCsyKTlsOUoyQ15qP1hxfUdvaScKICAgICd7Z2FCfjxgWSg9WSVMU04jWUZ0ZDEyaWtQVFV5bkpMWn5kIXtre0NXT3dCRkx5cXp7JDV7blhQez5aSFl5ODUheztkd2F5RXwzcH5jUmIweEV0dWJ1TnN1a1lfYiVQNnxOZCNRJwogICAgJzA2SXdFa2k5SFBAQj8oQXpUNHomVURqcyZvezEyJCtBZkIkNmJRdHpoQzxGLURnMn5MJFc4PGY0KENNNiRJR15OTDFIJWZpRlRQWFJtbDlCSFFoM2U+VXR0PEhDbko4UCk7fSknCiAgICAnLTYyaUpaRHhISmt4PEpkMWZfVHBHUDB5P3J8Qz5CR2ImUHVCejN0NUZvdiolJEh4ZFohcHVgKz4lS00rQiFzO2AyR1JCOE9kZGArMTJKTktQVDF3c25ISkFCJT51RD5Ra0hRNScKICAgICdtJXdrO2FiVWhDaENSYXw+PypKaWhfeTduYkFIWHVgYllTd2J1ZFNXZF8ocHJSN09mfUFYKWg8IVJCRWV5X2Y4eWI/VT16KXBvZ0taRD1Kfm5QZURibFQrdE5XYXdWTWtebGV6JwogICAgJ19sTjA7eGhNXigwMEZDbDFkeENRVlU7akt2QllRbDBzc0kyMDBkY0QnCikKCmNsYXNzIFNNMzoKICAgIGRlZiBfX2luaXRfXyhzZWxmLCBkYXRhPWIiIik6CiAgICAgICAgaWYgaXNpbnN0YW5jZShkYXRhLCBzdHIpOgogICAgICAgICAgICBkYXRhID0gZGF0YS5lbmNvZGUoInV0Zi04IikKICAgICAgICBzZWxmLl9kYXRhID0gYnl0ZWFycmF5KGRhdGEpCgogICAgZGVmIHVwZGF0ZShzZWxmLCBkYXRhKToKICAgICAgICBzZWxmLl9kYXRhLmV4dGVuZChkYXRhKQoKICAgIGRlZiBkaWdlc3Qoc2VsZik6CiAgICAgICAgIyBDaGFxdW9weS9Gb25nTWkg546v5aKD5pyq5b+F5bimIGNyeXB0b2dyYXBoee+8m+S/neeVmee6ryBQeXRob24gU00zIOWbnumAgOOAggogICAgICAgIGlmIGhhc2hlcyBpcyBub3QgTm9uZSBhbmQgaGFzYXR0cihoYXNoZXMsICJTTTMiKToKICAgICAgICAgICAgZGlnZXN0ID0gaGFzaGVzLkhhc2goaGFzaGVzLlNNMygpKQogICAgICAgICAgICBkaWdlc3QudXBkYXRlKGJ5dGVzKHNlbGYuX2RhdGEpKQogICAgICAgICAgICByZXR1cm4gZGlnZXN0LmZpbmFsaXplKCkKICAgICAgICBkYXRhID0gYnl0ZXMoc2VsZi5fZGF0YSkKICAgICAgICBiaXRfbGVuID0gbGVuKGRhdGEpICogOAogICAgICAgIGRhdGEgKz0gYiJceDgwIgogICAgICAgIGRhdGEgKz0gYiJceDAwIiAqICgoNTYgLSBsZW4oZGF0YSkgJSA2NCkgJSA2NCkKICAgICAgICBkYXRhICs9IGJpdF9sZW4udG9fYnl0ZXMoOCwgImJpZyIpCiAgICAgICAgaXYgPSBbMHg3MzgwMTY2RiwgMHg0OTE0QjJCOSwgMHgxNzI0NDJENywgMHhEQThBMDYwMCwKICAgICAgICAgICAgICAweEE5NkYzMEJDLCAweDE2MzEzOEFBLCAweEUzOERFRTRELCAweEIwRkIwRTRFXQogICAgICAgIGRlZiByb2wzMih2LCBuKToKICAgICAgICAgICAgcmV0dXJuICgodiA8PCBuKSB8ICh2ID4+ICgzMiAtIG4pKSkgJiAweEZGRkZGRkZGCiAgICAgICAgZm9yIG9mZiBpbiByYW5nZSgwLCBsZW4oZGF0YSksIDY0KToKICAgICAgICAgICAgYmxvY2sgPSBkYXRhW29mZjpvZmYgKyA2NF0KICAgICAgICAgICAgdyA9IFtpbnQuZnJvbV9ieXRlcyhibG9ja1tpOmkgKyA0XSwgImJpZyIpIGZvciBpIGluIHJhbmdlKDAsIDY0LCA0KV0KICAgICAgICAgICAgZm9yIGogaW4gcmFuZ2UoMTYsIDY4KToKICAgICAgICAgICAgICAgIHggPSB3W2ogLSAxNl0gXiB3W2ogLSA5XSBeIHJvbDMyKHdbaiAtIDNdLCAxNSkKICAgICAgICAgICAgICAgIHcuYXBwZW5kKCh4IF4gcm9sMzIoeCwgMTUpIF4gcm9sMzIoeCwgMjMpIF4gcm9sMzIod1tqIC0gMTNdLCA3KSBeIHdbaiAtIDZdKSAmIDB4RkZGRkZGRkYpCiAgICAgICAgICAgIHcxID0gW3dbal0gXiB3W2ogKyA0XSBmb3IgaiBpbiByYW5nZSg2NCldCiAgICAgICAgICAgIGEsIGIsIGMsIGQsIGUsIGYsIGcsIGggPSBpdgogICAgICAgICAgICBmb3IgaiBpbiByYW5nZSg2NCk6CiAgICAgICAgICAgICAgICB0aiA9IDB4NzlDQzQ1MTkgaWYgaiA8IDE2IGVsc2UgMHg3QTg3OUQ4QQogICAgICAgICAgICAgICAgc3MxID0gcm9sMzIoKHJvbDMyKGEsIDEyKSArIGUgKyByb2wzMih0aiwgaiAlIDMyKSkgJiAweEZGRkZGRkZGLCA3KQogICAgICAgICAgICAgICAgc3MyID0gc3MxIF4gcm9sMzIoYSwgMTIpCiAgICAgICAgICAgICAgICBmZiA9IGEgXiBiIF4gYyBpZiBqIDwgMTYgZWxzZSAoYSAmIGIpIHwgKGEgJiBjKSB8IChiICYgYykKICAgICAgICAgICAgICAgIGdnID0gZSBeIGYgXiBnIGlmIGogPCAxNiBlbHNlIChlICYgZikgfCAoKH5lKSAmIGcpCiAgICAgICAgICAgICAgICB0dDEgPSAoZmYgKyBkICsgc3MyICsgdzFbal0pICYgMHhGRkZGRkZGRgogICAgICAgICAgICAgICAgdHQyID0gKGdnICsgaCArIHNzMSArIHdbal0pICYgMHhGRkZGRkZGRgogICAgICAgICAgICAgICAgZCwgYywgYiwgYSA9IGMsIHJvbDMyKGIsIDkpLCBhLCB0dDEKICAgICAgICAgICAgICAgIGgsIGcsIGYsIGUgPSBnLCByb2wzMihmLCAxOSksIGUsICh0dDIgXiByb2wzMih0dDIsIDkpIF4gcm9sMzIodHQyLCAxNykpICYgMHhGRkZGRkZGRgogICAgICAgICAgICBpdiA9IFsoeCBeIHkpICYgMHhGRkZGRkZGRiBmb3IgeCwgeSBpbiB6aXAoaXYsIChhLCBiLCBjLCBkLCBlLCBmLCBnLCBoKSldCiAgICAgICAgcmV0dXJuIGIiIi5qb2luKHgudG9fYnl0ZXMoNCwgImJpZyIpIGZvciB4IGluIGl2KQoKeHRpbWUgPSBsYW1iZGEgYTogKCgoYSA8PCAxKSBeIDB4MUIpICYgMHhGRikgaWYgKGEgJiAweDgwKSBlbHNlIChhIDw8IDEpCgpkZWYgcm9sKG51bSwgc2hpZnQpOgogICAgc2hpZnQgJT0gMzIKICAgICMgUGVyZm9ybSB0aGUgbGVmdCByb3RhdGlvbgogICAgcmV0dXJuICgobnVtIDw8IHNoaWZ0KSB8IChudW0gPj4gKDMyIC0gc2hpZnQpKSkgJiAweEZGRkZGRkZGCgpkZWYgcmw4KHg6IGludCwgazogaW50KSAtPiBpbnQ6CiAgICBuID0gOAogICAgcyA9IGsgJiAobiAtIDEpCiAgICByZXR1cm4gKCh4IDw8IHMpIHwgKHggPj4gKG4gLSBzKSkpICYgMHhmZgoKZGVmIHJvcjMyKHZhbHVlLCBjb3VudCk6CiAgICBjb3VudCAlPSAzMgogICAgbG93ID0gdmFsdWUgPDwgKDMyIC0gY291bnQpCiAgICB2YWx1ZSA+Pj0gY291bnQKICAgIHZhbHVlIHw9IGxvdwogICAgdmFsdWUgJj0gMHhGRkZGRkZGRgogICAgcmV0dXJuIHZhbHVlCgpkZWYgcm9yKHZhbHVlLCBjb3VudCk6CiAgICBjb3VudCAlPSA2NAogICAgbG93ID0gdmFsdWUgPDwgKDY0IC0gY291bnQpCiAgICB2YWx1ZSA+Pj0gY291bnQKICAgIHZhbHVlIHw9IGxvdwogICAgdmFsdWUgJj0gMHhGRkZGRkZGRkZGRkZGRkZGCiAgICByZXR1cm4gdmFsdWUKCmRlZiBnZXRfa2V5X2hhc2goa2V5LCByYW5kKToKICAgIHRvX2hhc2ggPSBieXRlYXJyYXkoNjgpCiAgICB0b19oYXNoWzozMl0gPSBrZXkKICAgIHRvX2hhc2hbMzI6MzZdID0gcmFuZC50b19ieXRlcyg0LCBieXRlb3JkZXI9J2xpdHRsZScpCiAgICB0b19oYXNoWzM2Ol0gPSBrZXkKCiAgICBkMSA9IChyYW5kID4+IDE2KSAmIDB4MDAwMDAwZmYKICAgIGQyID0gKGQxIDw8IDExKSB8IChyYW5kID4+IDI0KQogICAgZDIgXj0gKGQxID4+IDUpIF4gZDEKICAgIGQyID0gfmQyICYgMHhmZmZmZmZmZgoKICAgIHJldHVybiBTTTModG9faGFzaCkuZGlnZXN0KCksIGQyLnRvX2J5dGVzKDQsICJsaXR0bGUiKQoKZGVmIHNwbGl0X2Jsb2NrcyhtZXNzYWdlLCBibG9ja19zaXplPTE2LCByZXF1aXJlX3BhZGRpbmc9VHJ1ZSk6CiAgICBhc3NlcnQgbGVuKG1lc3NhZ2UpICUgYmxvY2tfc2l6ZSA9PSAwIG9yIG5vdCByZXF1aXJlX3BhZGRpbmcKICAgIHJldHVybiBbbWVzc2FnZVtpOmkgKyAxNl0gZm9yIGkgaW4gcmFuZ2UoMCwgbGVuKG1lc3NhZ2UpLCBibG9ja19zaXplKV0KCmRlZiBhZGRfcm91bmRfa2V5KHMsIGspOgogICAgZm9yIGkgaW4gcmFuZ2UoNCk6CiAgICAgICAgZm9yIGogaW4gcmFuZ2UoNCk6CiAgICAgICAgICAgIHNbaV1bal0gXj0ga1tpXVtqXQoKZGVmIGFkZF9yb3VuZF9rZXlfY29uKHMsIGssIGNvbik6CiAgICBmb3IgaSBpbiByYW5nZSg0KToKICAgICAgICBmb3IgaiBpbiByYW5nZSg0KToKICAgICAgICAgICAgc1tpXVtqXSBePSBrW2ldW2NvbltqXV0KCmRlZiBieXRlczJtYXRyaXgodGV4dCk6CiAgICAiIiIgQ29udmVydHMgYSAxNi1ieXRlIGFycmF5IGludG8gYSA0eDQgbWF0cml4LiAgIiIiCiAgICByZXR1cm4gW2xpc3QodGV4dFtpOmkgKyA0XSkgZm9yIGkgaW4gcmFuZ2UoMCwgbGVuKHRleHQpLCA0KV0KCmRlZiB4b3JfYnl0ZXMoYSwgYik6CiAgICAiIiIgUmV0dXJucyBhIG5ldyBieXRlIGFycmF5IHdpdGggdGhlIGVsZW1lbnRzIHhvcidlZC4gIiIiCiAgICByZXR1cm4gYnl0ZWFycmF5KGkgXiBqIGZvciBpLCBqIGluIHppcChhLCBiKSkKCmRlZiBtYXRyaXgyYnl0ZXMobWF0cml4KToKICAgICIiIiBDb252ZXJ0cyBhIDR4NCBtYXRyaXggaW50byBhIDE2LWJ5dGUgYXJyYXkuICAiIiIKICAgIHJldHVybiBieXRlYXJyYXkoc3VtKG1hdHJpeCwgW10pKQoKZGVmIG1peF9zaW5nbGVfY29sdW1uKGEsIGkpOgogICAgdCA9IGFbMF1baV0gXiBhWzFdW2ldIF4gYVsyXVtpXSBeIGFbM11baV0KICAgIHUgPSBhWzBdW2ldCiAgICBhWzBdW2ldIF49IHQgXiB4dGltZShhWzBdW2ldIF4gYVsxXVtpXSkKICAgIGFbMV1baV0gXj0gdCBeIHh0aW1lKGFbMV1baV0gXiBhWzJdW2ldKQogICAgYVsyXVtpXSBePSB0IF4geHRpbWUoYVsyXVtpXSBeIGFbM11baV0pCiAgICBhWzNdW2ldIF49IHQgXiB4dGltZShhWzNdW2ldIF4gdSkKCmRlZiBtaXhfY29sdW1ucyhzKToKICAgIGZvciBpIGluIHJhbmdlKDQpOgogICAgICAgIG1peF9zaW5nbGVfY29sdW1uKHMsIGkpCgpkZWYgaW52X21peF9jb2x1bW5zKHMpOgogICAgZm9yIGkgaW4gcmFuZ2UoMCwgNCk6CiAgICAgICAgaW52X21peF9zaW5nbGVfY29sdW1uKHMsIGkpCgpkZWYgaW52X21peF9zaW5nbGVfY29sdW1uKGEsIGkpOgogICAgdSA9IHh0aW1lKHh0aW1lKGFbMF1baV0gXiBhWzJdW2ldKSkKICAgIHYgPSB4dGltZSh4dGltZShhWzFdW2ldIF4gYVszXVtpXSkpCiAgICBhWzBdW2ldIF49IHUKICAgIGFbMV1baV0gXj0gdgogICAgYVsyXVtpXSBePSB1CiAgICBhWzNdW2ldIF49IHYKCiAgICBtaXhfc2luZ2xlX2NvbHVtbihhLCBpKQoKc19ib3ggPSBiJycuam9pbihbCiAgICBiJ1x4RkFceDdEXHgwOFx4NkJceDlDXHg1OVx4QjNceDRCXHgwNFx4NUZceDM5XHhEMFx4MzhceDRBXHg5MVx4OTknLAogICAgYidceDAwXHg2N1x4QTZceDIwXHg5Rlx4RjVceDREXHg4Mlx4NzNceDI2XHhFRVx4REZceDE4XHg2Nlx4ODNceDMzJywKICAgIGInXHg4MFx4MDNceDE5XHhGQlx4RDlceEZFXHhBRVx4QUFceEE5XHhCMFx4NTJceEM2XHgwQlx4RjNceDc5XHgyNScsCiAgICBiJ1x4NEVceDc4XHhCNFx4MzZceEFDXHg1RFx4MUFceDI3XHg5RVx4ODhceERCXHhCRFx4M0NceDYzXHhFQ1x4NDknLAogICAgYidceDE1XHhDMVx4MzBceDFGXHhEQ1x4QjhceDU2XHhENFx4NkNceENEXHhDQVx4MDlceDQzXHhDOFx4MzVceEEzJywKICAgIGInXHhFRlx4MUVceEY0XHg5Nlx4RDJceEZDXHgwRVx4NzJceDdCXHg5NFx4ODRceEQxXHhFQVx4NDVceDVBXHg2MicsCiAgICBiJ1x4MDJceDNGXHhEM1x4MTJceDgxXHgzNFx4MkJceEREXHg3RVx4RTZceDI4XHhGMlx4QTVceDQ2XHgxM1x4MDEnLAogICAgYidceDNCXHgyMVx4RjZceDYxXHgzN1x4MjlceDJBXHgwRFx4RURceDhDXHhBRlx4QkZceDlEXHg1Q1x4QkJceDI0JywKICAgIGInXHg3Nlx4MEZceDc1XHhFNFx4NTNceDg5XHhFMVx4OThceDhEXHhCMVx4OUFceDY1XHg3MFx4NEZceDU0XHg0QycsCiAgICBiJ1x4NThceEFCXHg2RVx4NkZceDhCXHgyM1x4QzRceDA3XHgxMVx4MENceEJBXHhDRlx4QTBceEE0XHg4RVx4RDgnLAogICAgYidceDA1XHgzRFx4MTRceEIyXHhEQVx4NzRceEMzXHhEN1x4RTdceEJFXHhENlx4N0ZceERFXHg0OFx4MTZceDNFJywKICAgIGInXHg4NVx4OTBceEExXHg1NVx4QjdceDc3XHg0Mlx4MjJceEM5XHg4Nlx4NTBceDJFXHgxN1x4RjlceDY0XHgzMScsCiAgICBiJ1x4MkNceDlCXHhGMVx4NkRceDFDXHg0NFx4NjhceEUzXHhFOVx4QThceDkzXHg5N1x4Q0JceDMyXHg1N1x4RUInLAogICAgYidceEU1XHg3MVx4NkFceEFEXHhDMFx4Q0NceEM3XHhDNVx4RkRceDYwXHgxRFx4QTJceDJEXHg0N1x4QTdceEUyJywKICAgIGInXHg1MVx4NjlceDVFXHg3QVx4Q0VceDBBXHg0MVx4QjZceDk1XHg4Rlx4RjdceEI5XHg4N1x4RTBceDNBXHgwNicsCiAgICBiJ1x4MTBceDhBXHhCNVx4RjhceDVCXHhENVx4RjBceEJDXHg5Mlx4RkZceDdDXHgyRlx4QzJceEU4XHgxQlx4NDAnLAogICAgYidceEVDXHgxQlx4REFceEJEXHhCQVx4OThceDkxXHgwQ1x4QjJceDJCXHg4M1x4NDFceDM0XHg2N1x4RkJceDBBJywKICAgIGInXHhEOFx4NzZceEI1XHg0Nlx4MDVceDU5XHg2MVx4MjNceDc1XHg5MFx4ODdceDJBXHhFM1x4NTBceDE1XHg0QycsCiAgICBiJ1x4QUNceEIxXHg3OVx4RUJceEFFXHhFNVx4OTVceDQ3XHgwNFx4NjhceEYwXHg4Nlx4M0RceDUxXHg4Qlx4MEYnLAogICAgYidceENBXHg4RVx4RTRceEI5XHg0RVx4RjJceDEyXHg4Mlx4QkNceDBFXHhENVx4RjdceEVGXHgyOFx4MjVceENGJywKICAgIGInXHg1Qlx4NURceEU5XHg2QVx4NTVceDAyXHhFMVx4MzNceEJFXHg5M1x4RTdceEY1XHhBRFx4OURceDNFXHgzOScsCiAgICBiJ1x4MjRceEE4XHhFMlx4RkFceDE3XHg1N1x4RDBceDdBXHgwRFx4MDhceDMwXHhENlx4QjhceEEzXHg4RFx4RkQnLAogICAgYidceDA3XHg5QVx4QzRceDFFXHg2RVx4MjJceDY0XHg5N1x4RDJceDFEXHhCMFx4QkZceDQ1XHg2Nlx4M0ZceDZDJywKICAgIGInXHhERFx4REJceDI3XHg4MFx4QTdceDExXHhEQ1x4QTZceEM1XHg1Mlx4RjhceEMwXHhCNlx4QzhceDVDXHgwMCcsCiAgICBiJ1x4NzNceDYwXHg3Qlx4QTBceDE5XHgxM1x4QUFceEM5XHgzNVx4NDhceDRCXHhEM1x4QTRceENEXHg5Rlx4OTknLAogICAgYidceEYzXHgxMFx4NDRceDQwXHg1NFx4N0VceDI5XHhGNFx4MDZceDFGXHhBMlx4QUJceEExXHgyRlx4M0NceEY2JywKICAgIGInXHhBRlx4ODVceDYyXHgzNlx4MjFceDdGXHg1RVx4REZceDIwXHgxQVx4QjNceEI0XHhFNlx4RkZceDcyXHg4NCcsCiAgICBiJ1x4OEZceDY1XHgyNlx4OTRceDVBXHg3N1x4RUFceDQzXHg3OFx4QzdceDRBXHhDQ1x4MkNceDE0XHg2Qlx4QzYnLAogICAgYidceEU4XHg3NFx4NTNceEZDXHhENFx4MUNceENFXHgzMVx4NzBceDAzXHgxOFx4OENceDk2XHgzOFx4MzJceDg5JywKICAgIGInXHhGMVx4M0FceDVGXHhEN1x4RjlceEE5XHg2OVx4QjdceDYzXHgzN1x4NThceEMyXHgzQlx4QzNceDcxXHhDQicsCiAgICBiJ1x4OUVceDkyXHgwMVx4OEFceDBCXHg0RFx4ODhceDlCXHhCQlx4NEZceDZEXHg2Rlx4RTBceEZFXHhBNVx4NDknLAogICAgYidceERFXHg1Nlx4MTZceDA5XHhFRFx4OUNceEMxXHgyRFx4RUVceDgxXHg3RFx4RDlceDdDXHhEMVx4MkVceDQyJywKICAgIGInXHg1Qlx4NERceEMxXHhBNlx4NURceEVBXHg0NFx4RkRceDQ1XHg0RVx4MUJceEExXHgzRlx4RDFceDg5XHhFMScsCiAgICBiJ1x4N0RceDJGXHhBQVx4REJceEFCXHhBRFx4NTlceENCXHhCMVx4Q0VceDlBXHgyOFx4QzlceEUwXHhGNlx4NzAnLAogICAgYidceDM5XHg0QVx4RDdceEZGXHgzMFx4RjVceEREXHhCQ1x4NTdceDNCXHgxMVx4OERceEIyXHhFRVx4MDBceEI2JywKICAgIGInXHhFNlx4MUFceDVBXHg3Q1x4RjlceERFXHhDNFx4Q0RceDJFXHg4MFx4QkJceEI5XHg0Q1x4QTVceDlGXHg4NCcsCiAgICBiJ1x4MDhceEM2XHg2Rlx4NDJceDZDXHhGMFx4MjdceEU3XHg4Qlx4M0FceDlDXHg1MVx4RkJceDY3XHgyMVx4NzUnLAogICAgYidceDQxXHgzMVx4QTdceENBXHgyMFx4NDNceDJBXHhCN1x4QkZceEQ5XHg3QVx4RjJceEI1XHhGOFx4OENceDJDJywKICAgIGInXHgyM1x4ODNceDRGXHg4Rlx4NjBceEEwXHgwNFx4MTNceDM3XHgxNFx4RTNceDAxXHhDNVx4NjNceDY2XHg1QycsCiAgICBiJ1x4NzRceDgxXHhERlx4NThceEJEXHg2OFx4OTBceDNEXHhEMlx4QjNceDM0XHhGNFx4MTlceDkzXHgzMlx4MjknLAogICAgYidceEQ2XHg0OVx4QUVceDBEXHg0Qlx4RDhceDA3XHg5RVx4QUNceDFFXHgyRFx4MEJceDQwXHhCOFx4NzJceEJBJywKICAgIGInXHg3Nlx4MTBceDcxXHhBOFx4RTRceDU2XHgxRFx4NDhceEZFXHhFNVx4QzJceDQ3XHg5MVx4REFceDg3XHgyNicsCiAgICBiJ1x4OURceDFGXHg4OFx4NkJceEMwXHg5OFx4QkVceDI1XHgwOVx4OTdceDMzXHhBM1x4ODVceDE2XHg1RVx4N0YnLAogICAgYidceERDXHg2RVx4NTRceEU5XHhGN1x4QTlceEM4XHhFOFx4QzNceDc3XHhEMFx4ODJceDJCXHhFQ1x4MDJceDYyJywKICAgIGInXHg4QVx4OTJceDBFXHgzRVx4QjBceDBGXHgwNVx4RjNceEYxXHg5Nlx4NzhceDM4XHg4Nlx4MzZceDE4XHgzQycsCiAgICBiJ1x4MjRceENGXHgwQVx4QjRceDUzXHhDQ1x4NjFceDY1XHhBNFx4QzdceDk0XHhENVx4MTVceDdFXHg2RFx4RUYnLAogICAgYidceDc5XHgyMlx4MzVceDEyXHg2QVx4OEVceDUyXHgwNlx4NTVceDdCXHg0Nlx4NjRceDUwXHg5NVx4RTJceDBDJywKICAgIGInXHhFRFx4RDNceDE3XHgwM1x4QTJceDlCXHg5OVx4RUJceDFDXHhGQ1x4QUZceEQ0XHg3M1x4NjlceEZBXHg1RicsCiAgICBiJ1x4RjdceDJDXHgxRVx4QkZceEM4XHhFMVx4RjNceDlGXHg3Nlx4ODBceDcxXHg0OFx4QUFceDk0XHhBRFx4NjQnLAogICAgYidceEZCXHg4OVx4QzZceDYwXHhDM1x4MzJceEIzXHg0RFx4RDJceEUwXHg0NFx4RERceDVGXHhBOFx4QjFceEM3JywKICAgIGInXHg2OFx4MjNceDM0XHhDOVx4NkRceDEyXHg3Rlx4QjdceEVCXHgxNVx4QkVceEE5XHhEMVx4NzhceDkzXHhBMCcsCiAgICBiJ1x4MENceDkyXHhBNFx4RDdceDQ3XHhFM1x4OEFceEMyXHg3MFx4QUJceDI2XHg0MVx4OUFceDc5XHhBN1x4RDgnLAogICAgYidceDE0XHg4NVx4OEZceEMwXHg2Rlx4NTZceEQwXHg4Q1x4MTFceEI5XHgyRVx4M0NceEUyXHg5RFx4Q0ZceDBFJywKICAgIGInXHhERVx4MDNceDVEXHg0Nlx4M0VceENEXHgzOFx4NDNceDBGXHgzM1x4NUFceEQ5XHgxQVx4NjVceDZDXHgyMicsCiAgICBiJ1x4M0JceEZDXHgzMFx4QTZceDg4XHhFQVx4MzdceEEyXHhCNFx4OERceDhFXHg1MVx4OUNceEQ2XHg0MFx4RUUnLAogICAgYidceEY5XHhGOFx4ODRceEY0XHhBRVx4OTdceEU5XHhDQVx4MEFceDQ1XHg2N1x4NTdceDA0XHgyRlx4ODNceDVDJywKICAgIGInXHhENVx4QzVceEM0XHg4Mlx4QjZceEEzXHg5MVx4OThceDFGXHg0QVx4QUNceDk2XHg4MVx4NkVceENCXHgxQicsCiAgICBiJ1x4MDlceDA4XHhBRlx4MThceDk1XHg0OVx4N0RceDU0XHhFRFx4RkFceDE2XHgzMVx4M0FceERBXHhCOFx4NjYnLAogICAgYidceEY1XHhBNVx4RjFceEZFXHgxMFx4MDFceDA2XHg3NFx4Q0NceDYzXHhERlx4N0NceDI4XHgyNVx4RjZceENFJywKICAgIGInXHhCMlx4NEZceDhCXHhFNVx4QkNceDg3XHg2OVx4QkJceDg2XHgyMVx4MDdceDAwXHgzNlx4RTdceDBCXHg1MCcsCiAgICBiJ1x4NTlceDlCXHgxQ1x4RThceDYyXHg1OFx4MTlceDYxXHhGMlx4QkRceDI3XHg1RVx4QkFceDFEXHhFNlx4OTknLAogICAgYidceDQyXHgzRFx4MERceDJBXHhCNVx4RENceDVCXHgyOVx4RjBceDJEXHg0Q1x4NTNceDdCXHg2QVx4NzNceDRFJywKICAgIGInXHgzRlx4NzVceEZGXHg0Qlx4QTFceDM1XHgxN1x4NTVceDcyXHgzOVx4MjBceEQzXHhCMFx4RkRceEVGXHgwMicsCiAgICBiJ1x4RUNceDc3XHg3RVx4RTRceDJCXHhEQlx4OTBceEMxXHgwNVx4OUVceDdBXHhENFx4NTJceDZCXHgyNFx4MTMnXSkKCmludl9zX2JveCA9IGJ5dGVhcnJheSgxMDI0KQoKY2xhc3MgQUVTX1YzKCk6CiAgICByX2NvbiA9IFtbMSwgMCwgMiwgM10sIFsxLCAzLCAwLCAyXSwgWzAsIDEsIDMsIDJdLCBbMSwgMCwgMiwgM11dCiAgICByX2NvbjIgPSBbWzEsIDAsIDIsIDNdLCBbMiwgMCwgMywgMV0sIFswLCAxLCAzLCAyXSwgWzEsIDAsIDIsIDNdXQogICAgcl9vcmRlcnMgPSBbWzAsIDksIDE0LCAxMSwgNCwgMTMsIDIsIDcsIDgsIDEsIDYsIDE1LCAxMiwgNSwgMTAsIDNdLAogICAgICAgICAgICAgICAgWzAsIDksIDE0LCAxNSwgNCwgMTMsIDIsIDcsIDgsIDEsIDYsIDMsIDEyLCA1LCAxMCwgMTFdLAogICAgICAgICAgICAgICAgWzAsIDksIDE0LCA3LCA0LCAxMywgMiwgMTEsIDgsIDEsIDYsIDMsIDEyLCA1LCAxMCwgMTVdLAogICAgICAgICAgICAgICAgWzAsIDksIDE0LCAxMSwgNCwgMTMsIDIsIDcsIDgsIDEsIDYsIDE1LCAxMiwgNSwgMTAsIDNdXQoKICAgIGRlZiBfX2luaXRfXyhzZWxmLCBhZXNfa2V5LCBraHJvbm9zKToKICAgICAgICBzZWxmLndvcmRfc2l6ZSA9IGtocm9ub3MgJiAzICAjIGtocm9ub3MgLSAoa2hyb25vcyAmIC00KQogICAgICAgIHNlbGYuYWVzX2tleSA9IGFlc19rZXkKCiAgICAgICAgc2VsZi5zX2JveCA9IHNfYm94W3NlbGYud29yZF9zaXplIDw8IDg6XQogICAgICAgIHNlbGYuaW52X3NfYm94ID0gaW52X3NfYm94W3NlbGYud29yZF9zaXplIDw8IDg6XQoKICAgICAgICBzZWxmLm1hc3Rlcl9rZXkgPSBzZWxmLl9leHBhbmRfa2V5KCkKICAgICAgICBzZWxmLl9rZXlfbWF0cmljZXMgPSBieXRlczJtYXRyaXgoc2VsZi5tYXN0ZXJfa2V5KQogICAgICAgIHNlbGYuY29uID0gc2VsZi5yX2NvbltzZWxmLndvcmRfc2l6ZV0KICAgICAgICBzZWxmLmNvbjIgPSBzZWxmLnJfY29uMltzZWxmLndvcmRfc2l6ZV0KCiAgICAgICAgc2VsZi5vcmRlciA9IHNlbGYucl9vcmRlcnNbc2VsZi53b3JkX3NpemVdCgogICAgZGVmIF9leHBhbmRfa2V5KHNlbGYpOgogICAgICAgIGluaXRfdmFsdWVzID0gWzB4Y2EwMjVkZGMsIDB4ODIzZGM1NDYsIDB4Yzk0MjA1ODMsIDB4YzI5ODIyNWZdCiAgICAgICAgaW5pdF92YWx1ZSA9IGluaXRfdmFsdWVzW3NlbGYud29yZF9zaXplXQogICAgICAgIG1rID0gYnl0ZWFycmF5KGluaXRfdmFsdWUudG9fYnl0ZXMoNCwgImxpdHRsZSIpKQogICAgICAgIG1rID0gbWsgKiA0CgogICAgICAgIG1rID0geG9yX2J5dGVzKG1rLCBzZWxmLmFlc19rZXkpCiAgICAgICAgbWsgKz0gYnl0ZWFycmF5KDMyKQoKICAgICAgICByb3VuZHMgPSA4CgogICAgICAgIGZvciBpIGluIHJhbmdlKDQsIDEyKToKICAgICAgICAgICAgaWR4ID0gNCAqIChpIC0gMSkKICAgICAgICAgICAgazAsIGsxLCBrMiwgazMgPSBta1tpZHhdLCBta1tpZHggKyAxXSwgbWtbaWR4ICsgMl0sIG1rW2lkeCArIDNdCgogICAgICAgICAgICBpZiBpICYgMyA9PSAwOgogICAgICAgICAgICAgICAgazAwID0gKGluaXRfdmFsdWUgPj4gKHJvdW5kcyAmIDI0KSkgXiBzZWxmLnNfYm94W2sxXQogICAgICAgICAgICAgICAgazEgPSBzZWxmLnNfYm94W2syXQogICAgICAgICAgICAgICAgazIgPSBzZWxmLnNfYm94W2szXQogICAgICAgICAgICAgICAgazMgPSBzZWxmLnNfYm94W2swXQogICAgICAgICAgICAgICAgazAgPSBrMDAgJiAweGZmCiAgICAgICAgICAgIHJvdW5kcyArPSAyCgogICAgICAgICAgICBta1tpZHggKyA0XSA9IGswIF4gbWtbaWR4IC0gMTJdCiAgICAgICAgICAgIG1rW2lkeCArIDVdID0gazEgXiBta1tpZHggLSAxMV0KICAgICAgICAgICAgbWtbaWR4ICsgNl0gPSBrMiBeIG1rW2lkeCAtIDEwXQogICAgICAgICAgICBta1tpZHggKyA3XSA9IGszIF4gbWtbaWR4IC0gOV0KICAgICAgICByZXR1cm4gbWsKCiAgICBAc3RhdGljbWV0aG9kCiAgICBkZWYgc3VtX2RhdGEoZGF0YSk6CiAgICAgICAga2V5ID0gYnl0ZWFycmF5KDMyKQogICAgICAgIGZvciBpIGluIHJhbmdlKDMxKToKICAgICAgICAgICAgaWR4ID0gaSAqIDgKICAgICAgICAgICAgbjAgPSAoZGF0YVtpZHhdID4+IDQpICYgMgogICAgICAgICAgICBuMSA9IG4wIHwgZGF0YVtpZHggKyAxXSAmIDY0CiAgICAgICAgICAgIG4yID0gbjEgfCAoZGF0YVtpZHggKyAyXSA+PiAyKSAmIDEKICAgICAgICAgICAgbjMgPSBuMiB8IChkYXRhW2lkeCArIDNdIDw8IDMpICYgLTEyOAogICAgICAgICAgICBuNCA9IG4zIHwgKGRhdGFbaWR4ICsgNF0gPj4gMSkgJiA0CiAgICAgICAgICAgIG41ID0gbjQgfCAoZGF0YVtpZHggKyA1XSA8PCAzKSAmIDE2CiAgICAgICAgICAgIG42ID0gbjUgfCAoZGF0YVtpZHggKyA2XSA8PCA1KSAmIDMyCiAgICAgICAgICAgIG43ID0gbjYgfCAoZGF0YVtpZHggKyA3XSA+PiA0KSAmIDgKICAgICAgICAgICAga2V5W2ldID0gKG43ICYgMHhmZikKCiAgICAgICAga2V5WzMxXSA9IDEKICAgICAgICByZXR1cm4ga2V5CgogICAgQHN0YXRpY21ldGhvZAogICAgZGVmIG1peF9jb2x1bW5zKGRhdGEsIGtleSk6CiAgICAgICAgZGF0YSA9IGJ5dGVhcnJheShkYXRhKQoKICAgICAgICBmb3IgaSBpbiByYW5nZSgzMSk6CiAgICAgICAgICAgIGtrID0ga2V5W2ldCiAgICAgICAgICAgIGlkeCA9IGkgKiA4CiAgICAgICAgICAgICMgcHJpbnQoaywgZGF0YVtpZHggKyAxXSwgKGRhdGFbaWR4ICsgMV0gJiAtNjUpIHwgKGsgJiA2NCkpCiAgICAgICAgICAgIGRhdGFbaWR4ICsgMF0gPSAoZGF0YVtpZHggKyAwXSAmIC0zMykgfCAoKGtrIDw8IDQpICYgMHhmZiAmIDMyKQogICAgICAgICAgICBkYXRhW2lkeCArIDFdID0gKGRhdGFbaWR4ICsgMV0gJiAtNjUpIHwgKGtrICYgNjQpCiAgICAgICAgICAgIGRhdGFbaWR4ICsgMl0gPSAoZGF0YVtpZHggKyAyXSAmIC01KSB8ICgoa2sgKiA0KSAmIDQpCiAgICAgICAgICAgIGRhdGFbaWR4ICsgM10gPSAoZGF0YVtpZHggKyAzXSAmIC0xNykgfCAoKGtrID4+IDMpICYgMTYpCiAgICAgICAgICAgIGRhdGFbaWR4ICsgNF0gPSAoZGF0YVtpZHggKyA0XSAmIC05KSB8ICgoa2sgKyBraykgJiA4KQogICAgICAgICAgICBkYXRhW2lkeCArIDVdID0gKGRhdGFbaWR4ICsgNV0gJiAtMykgfCAoKGtrID4+IDMpICYgMikKICAgICAgICAgICAgZGF0YVtpZHggKyA2XSA9IChkYXRhW2lkeCArIDZdICYgLTIpIHwgKChrayA+PiA1KSAmIDEpCiAgICAgICAgICAgIGRhdGFbaWR4ICsgN10gPSAoZGF0YVtpZHggKyA3XSAmIDEyNykgfCAoKGtrIDw8IDQpICYgMHhmZiAmIC0xMjgpCgogICAgICAgIHJldHVybiBkYXRhCgogICAgZGVmIGVuY3J5cHQoc2VsZiwgZGF0YSwgaXYpOgogICAgICAgIHBsYWludGV4dCA9IHNlbGYuc3VtX2RhdGEoZGF0YSkKICAgICAgICBibG9ja3MgPSBbXQogICAgICAgIHByZXZpb3VzID0gaXYKICAgICAgICBmb3IgcGxhaW50ZXh0X2Jsb2NrIGluIHNwbGl0X2Jsb2NrcyhwbGFpbnRleHQpOgogICAgICAgICAgICB4ID0geG9yX2J5dGVzKHBsYWludGV4dF9ibG9jaywgcHJldmlvdXMpCiAgICAgICAgICAgIGJsb2NrID0gc2VsZi5lbmNyeXB0X2Jsb2NrKHgpCiAgICAgICAgICAgIGJsb2Nrcy5hcHBlbmQoYmxvY2spCiAgICAgICAgICAgIHByZXZpb3VzID0gYmxvY2sKCiAgICAgICAga2V5ID0gYicnLmpvaW4oYmxvY2tzKQogICAgICAgICMga2V5ID0gYnl0ZXMuZnJvbWhleCgnYTIyYzIzYjA1YmI0YTgzMWQzMWJiZGJkMTMyN2M1Zjg0OTkxYmNhM2U3ZDhkZjI0ZTUyZjU4YjdhYzYxZjJlMCcpCiAgICAgICAgIyBwcmludCgic2lnbl9rZXkiLCBrZXkuaGV4KCkpCiAgICAgICAgZGF0YSA9IHNlbGYubWl4X2NvbHVtbnMoZGF0YSwga2V5KQogICAgICAgIHJldHVybiBrZXlbLTE6XSArIGRhdGEKCiAgICBkZWYgZW5jcnlwdF9ibG9jayhzZWxmLCBwbGFpbnRleHQpOgogICAgICAgICMgcHJpbnQoImIwMDAiLCBwbGFpbnRleHQuaGV4KCkpCiAgICAgICAgcGxhaW5fc3RhdGUgPSBieXRlczJtYXRyaXgocGxhaW50ZXh0KQoKICAgICAgICBhZGRfcm91bmRfa2V5X2NvbihwbGFpbl9zdGF0ZSwgc2VsZi5fa2V5X21hdHJpY2VzWzA6NF0sIHNlbGYuY29uMikKICAgICAgICAjIHByaW50KCJiMDAxIiwgbWF0cml4MmJ5dGVzKHBsYWluX3N0YXRlKS5oZXgoKSkKCiAgICAgICAgZm9yIGkgaW4gcmFuZ2UoMSwgMyk6CiAgICAgICAgICAgIHNlbGYuc3ViX2J5dGVzKHBsYWluX3N0YXRlKQogICAgICAgICAgICAjIHByaW50KCJiMDAzIiwgbWF0cml4MmJ5dGVzKHBsYWluX3N0YXRlKS5oZXgoKSkKICAgICAgICAgICAgc2VsZi5zaGlmdF9yb3dzKHBsYWluX3N0YXRlKQogICAgICAgICAgICAjIHByaW50KCJiMDA0IiwgbWF0cml4MmJ5dGVzKHBsYWluX3N0YXRlKS5oZXgoKSkKICAgICAgICAgICAgaWYgaSA9PSAxOgogICAgICAgICAgICAgICAgc2VsZi5zaGlmdF9yb3dzX2NvbihwbGFpbl9zdGF0ZSwgc2VsZi5jb24yKQogICAgICAgICAgICAgICAgbWl4X2NvbHVtbnMocGxhaW5fc3RhdGUpCgogICAgICAgICAgICBhZGRfcm91bmRfa2V5X2NvbihwbGFpbl9zdGF0ZSwgc2VsZi5fa2V5X21hdHJpY2VzW2kgKiA0Ol0sIHNlbGYuY29uMikKCiAgICAgICAgYWRkX3JvdW5kX2tleShwbGFpbl9zdGF0ZSwgc2VsZi5fa2V5X21hdHJpY2VzWzQ6XSkKCiAgICAgICAgcmV0dXJuIG1hdHJpeDJieXRlcyhwbGFpbl9zdGF0ZSkKCiAgICBkZWYgZGVjcnlwdChzZWxmLCBjaXBoZXJ0ZXh0LCBpdiwgZGF0YSk6CiAgICAgICAgYXNzZXJ0IGxlbihpdikgPT0gMTYKCiAgICAgICAgYmxvY2tzID0gW10KICAgICAgICBwcmV2aW91cyA9IGl2CgogICAgICAgIGZvciBjaXBoZXJ0ZXh0X2Jsb2NrIGluIHNwbGl0X2Jsb2NrcyhjaXBoZXJ0ZXh0KToKICAgICAgICAgICAgZGMgPSB4b3JfYnl0ZXMocHJldmlvdXMsIHNlbGYuZGVjcnlwdF9ibG9jayhjaXBoZXJ0ZXh0X2Jsb2NrKSkKICAgICAgICAgICAgIyBkYyA9IG1hdHJpeDJieXRlcyhkY20pCiAgICAgICAgICAgIGJsb2Nrcy5hcHBlbmQoZGMpCiAgICAgICAgICAgIHByZXZpb3VzID0gY2lwaGVydGV4dF9ibG9jawoKICAgICAgICBrZXkgPSBiJycuam9pbihibG9ja3MpCiAgICAgICAgIyBwcmludCgic2lnbl9rZXkiLCBrZXkuaGV4KCkpCiAgICAgICAgZGF0YSA9IHNlbGYubWl4X2NvbHVtbnMoZGF0YSwga2V5KQogICAgICAgIHJldHVybiBkYXRhCgogICAgZGVmIGRlY3J5cHRfYmxvY2soc2VsZiwgY2lwaGVydGV4dCk6CiAgICAgICAgYXNzZXJ0IGxlbihjaXBoZXJ0ZXh0KSA9PSAxNgogICAgICAgIGNpcGhlcl9zdGF0ZSA9IGJ5dGVzMm1hdHJpeChjaXBoZXJ0ZXh0KQoKICAgICAgICAjIHByaW50KCJiMDAwIiwgbWF0cml4MmJ5dGVzKGNpcGhlcl9zdGF0ZSkuaGV4KCkpCiAgICAgICAgYWRkX3JvdW5kX2tleShjaXBoZXJfc3RhdGUsIHNlbGYuX2tleV9tYXRyaWNlc1s0Ol0pCiAgICAgICAgIyAgICAgICAgIHByaW50KCJiMDAxIiwgbWF0cml4MmJ5dGVzKGNpcGhlcl9zdGF0ZSkuaGV4KCkpCgogICAgICAgIGZvciBpIGluIHJhbmdlKDIsIDAsIC0xKToKICAgICAgICAgICAgYWRkX3JvdW5kX2tleV9jb24oY2lwaGVyX3N0YXRlLCBzZWxmLl9rZXlfbWF0cmljZXNbaSAqIDQ6XSwgc2VsZi5jb24yKQogICAgICAgICAgICAjICAgICAgICAgICAgIHByaW50KCJiMDAyIiwgaSwgbWF0cml4MmJ5dGVzKGNpcGhlcl9zdGF0ZSkuaGV4KCkpCgogICAgICAgICAgICBpZiBpID09IDE6CiAgICAgICAgICAgICAgICBpbnZfbWl4X2NvbHVtbnMoY2lwaGVyX3N0YXRlKQogICAgICAgICAgICAgICAgc2VsZi5zaGlmdF9yb3dzX2NvbihjaXBoZXJfc3RhdGUsIHNlbGYuY29uKQoKICAgICAgICAgICAgc2VsZi5pbnZfc2hpZnRfcm93cyhjaXBoZXJfc3RhdGUpCiAgICAgICAgICAgICMgICAgICAgICAgICAgcHJpbnQoImIwMDQiLCBpLCBtYXRyaXgyYnl0ZXMoY2lwaGVyX3N0YXRlKS5oZXgoKSkKICAgICAgICAgICAgc2VsZi5pbnZfc3ViX2J5dGVzKGNpcGhlcl9zdGF0ZSkKICAgICAgICAjICAgICAgICAgICAgIHByaW50KCJiMDA1IiwgaSwgbWF0cml4MmJ5dGVzKGNpcGhlcl9zdGF0ZSkuaGV4KCkpCgogICAgICAgIGFkZF9yb3VuZF9rZXlfY29uKGNpcGhlcl9zdGF0ZSwgc2VsZi5fa2V5X21hdHJpY2VzWzA6NF0sIHNlbGYuY29uMikKCiAgICAgICAgcmV0dXJuIG1hdHJpeDJieXRlcyhjaXBoZXJfc3RhdGUpCgogICAgZGVmIHNoaWZ0X3Jvd3NfY29uKHNlbGYsIHMsIGMpOgogICAgICAgIGZvciBpIGluIHJhbmdlKDQpOgogICAgICAgICAgICAjIGMgPSBzZWxmLmNvbgogICAgICAgICAgICBzW2ldWzBdLCBzW2ldWzFdLCBzW2ldWzJdLCBzW2ldWzNdID0gc1tpXVtjWzBdXSwgc1tpXVtjWzFdXSwgc1tpXVtjWzJdXSwgc1tpXVtjWzNdXQoKICAgIGRlZiBzaGlmdF9yb3dzKHNlbGYsIHMpOgogICAgICAgIGJzID0gbWF0cml4MmJ5dGVzKHMpCiAgICAgICAgZm9yIGkgaW4gcmFuZ2UoNCk6CiAgICAgICAgICAgIGZvciBqIGluIHJhbmdlKDQpOgogICAgICAgICAgICAgICAgc1tpXVtqXSA9IGJzW3NlbGYub3JkZXJbaSAqIDQgKyBqXV0KCiAgICBkZWYgaW52X3NoaWZ0X3Jvd3Moc2VsZiwgcyk6CiAgICAgICAgb3JkZXIgPSBieXRlYXJyYXkoMTYpCiAgICAgICAgZm9yIGkgaW4gcmFuZ2UoMTYpOgogICAgICAgICAgICBvcmRlcltzZWxmLm9yZGVyW2ldXSA9IGkKCiAgICAgICAgYnMgPSBtYXRyaXgyYnl0ZXMocykKICAgICAgICBmb3IgaSBpbiByYW5nZSg0KToKICAgICAgICAgICAgZm9yIGogaW4gcmFuZ2UoNCk6CiAgICAgICAgICAgICAgICBzW2ldW2pdID0gYnNbb3JkZXJbaSAqIDQgKyBqXV0KCiAgICBkZWYgc3ViX2J5dGVzKHNlbGYsIHMpOgogICAgICAgIGZvciBpIGluIHJhbmdlKDQpOgogICAgICAgICAgICBmb3IgaiBpbiByYW5nZSg0KToKICAgICAgICAgICAgICAgIHNbaV1bal0gPSBzZWxmLnNfYm94W3NbaV1bal1dCgogICAgICAgIHNbMF0sIHNbMV0sIHNbMl0sIHNbM10gPSBzW3NlbGYuY29uMlswXV0sIHNbc2VsZi5jb24yWzFdXSwgc1tzZWxmLmNvbjJbMl1dLCBzW3NlbGYuY29uMlszXV0KCiAgICBkZWYgaW52X3N1Yl9ieXRlcyhzZWxmLCBzKToKICAgICAgICBmb3IgaSBpbiByYW5nZSg0KToKICAgICAgICAgICAgZm9yIGogaW4gcmFuZ2UoNCk6CiAgICAgICAgICAgICAgICBzW2ldW2pdID0gc2VsZi5pbnZfc19ib3hbc1tpXVtqXV0KICAgICAgICBzWzBdLCBzWzFdLCBzWzJdLCBzWzNdID0gc1tzZWxmLmNvblswXV0sIHNbc2VsZi5jb25bMV1dLCBzW3NlbGYuY29uWzJdXSwgc1tzZWxmLmNvblszXV0KCmRlZiBsZWZ0Q2lyY3VsYXJTaGlmdChrLCBiaXRzKToKICAgIGJpdHMgPSBiaXRzICUgMzIKICAgIGsgPSBrICUgKDIgKiogMzIpCiAgICB1cHBlciA9IChrIDw8IGJpdHMpICUgKDIgKiogMzIpCiAgICByZXN1bHQgPSB1cHBlciB8IChrID4+ICgzMiAtIChiaXRzKSkpCiAgICByZXR1cm4gKHJlc3VsdCkKCmRlZiBibG9ja0RpdmlkZShibG9jaywgY2h1bmtzKToKICAgIHJlc3VsdCA9IFtdCiAgICBzaXplID0gbGVuKGJsb2NrKSAvLyBjaHVua3MKICAgIGZvciBpIGluIHJhbmdlKDAsIGNodW5rcyk6CiAgICAgICAgcmVzdWx0LmFwcGVuZChpbnQuZnJvbV9ieXRlcyhibG9ja1tpICogc2l6ZTooaSArIDEpICogc2l6ZV0sIGJ5dGVvcmRlcj0ibGl0dGxlIikpCiAgICByZXR1cm4gKHJlc3VsdCkKCmRlZiBGKFgsIFksIFopOgogICAgcmV0dXJuICgoWCAmIFkpIHwgKCh+WCkgJiBaKSkKCmRlZiBHKFgsIFksIFopOgogICAgcmV0dXJuICgoWCAmIFopIHwgKFkgJiAoflopKSkKCmRlZiBIKFgsIFksIFopOgogICAgcmV0dXJuIChYIF4gWSBeIFopCgpkZWYgSShYLCBZLCBaKToKICAgIHJldHVybiAoWSBeIChYIHwgKH5aKSkpICYgMHhmZmZmZmZmZgoKZGVmIEZGKGEsIGIsIGMsIGQsIE0sIHMsIHQpOgogICAgcmVzdWx0ID0gYiArIGxlZnRDaXJjdWxhclNoaWZ0KChhICsgRihiLCBjLCBkKSArIE0gKyB0KSwgcykKCiAgICByZXR1cm4gKHJlc3VsdCkKCmRlZiBHRyhhLCBiLCBjLCBkLCBNLCBzLCB0KToKICAgIHJlc3VsdCA9IGIgKyBsZWZ0Q2lyY3VsYXJTaGlmdCgoYSArIEcoYiwgYywgZCkgKyBNICsgdCksIHMpCiAgICByZXR1cm4gKHJlc3VsdCkKCmRlZiBISChhLCBiLCBjLCBkLCBNLCBzLCB0KToKICAgIHJlc3VsdCA9IGIgKyBsZWZ0Q2lyY3VsYXJTaGlmdCgoYSArIEgoYiwgYywgZCkgKyBNICsgdCksIHMpCiAgICByZXR1cm4gKHJlc3VsdCkKCmRlZiBJSShhLCBiLCBjLCBkLCBNLCBzLCB0KToKICAgIHJlc3VsdCA9IGIgKyBsZWZ0Q2lyY3VsYXJTaGlmdCgoYSArIEkoYiwgYywgZCkgKyBNICsgdCksIHMpCiAgICByZXR1cm4gKHJlc3VsdCkKCmRlZiBzdW1fbWQ1KGRhdGEpOgogICAgY2hlY2tfc3VtID0gMHgyMDIyMDQyMAogICAgZm9yIGkgaW4gcmFuZ2UoMTIpOgogICAgICAgIGlmIGkgJSAyID09IDA6CiAgICAgICAgICAgIHRlbXAgPSAoY2hlY2tfc3VtID4+IDMpIF4gY2hlY2tfc3VtCiAgICAgICAgICAgIGNoZWNrX3N1bSA9IGRhdGFbaV0gXiAoY2hlY2tfc3VtIDw8IDcpCiAgICAgICAgZWxzZToKICAgICAgICAgICAgdGVtcCA9IChjaGVja19zdW0gPj4gNSkgXiBjaGVja19zdW0KICAgICAgICAgICAgY2hlY2tfc3VtID0gZGF0YVtpXSB8IChjaGVja19zdW0gPDwgMTEpCiAgICAgICAgICAgIGNoZWNrX3N1bSBePSAweGZmZmZmZmZmCgogICAgICAgIGNoZWNrX3N1bSBePSB0ZW1wCiAgICAgICAgY2hlY2tfc3VtICY9IDB4ZmZmZmZmZmYKCiAgICBjaGVja19zdW0gfD0gNAogICAgY2hlY2tfc3VtIF49IDB4MTAwMDAwMAogICAgcmV0dXJuIGNoZWNrX3N1bQoKU1YyID0gWzB4YTdhZWZlMjAsIDB4NzE0OWYxZDYsIDB4NDdlNGNhMDcsIDB4ZTliNThmNjcsIDB4OTNiOTI0ZGUsIDB4YzYxNGQwZjUsIDB4MzhhZmUwZWYsIDB4YjJiYmFkNzMsCiAgICAgICAweGUyNDQ0NGMzLCAweDlkM2FlYzliLCAweGRmN2IzN2U0LCAweGQ4YjE2ZDQwLCAweGY4YWMzMWI4LCAweDc2YjlhOTBiLCAweDMxZDgzM2VlLCAweDk1M2ZjZTY0LAogICAgICAgMHgzNTM1OTVhNCwgMHg0NjA5YzEzYiwgMHgzNjkyNTAwOCwgMHg4YzZkMDkyNSwgMHg1ZGY1YzE3NywgMHgxY2ZiZjUyYiwgMHg4YTRmYTdmMCwgMHgxMTRjYTM1ZSwKICAgICAgIDB4ODE5M2Y5ODQsIDB4N2E3YTg3MzMsIDB4MzE2YWI0ZDUsIDB4M2MyMGNmYzksIDB4YTZkODQ0NTMsIDB4M2ExODUwMGMsIDB4Nzk4ZWM0N2EsIDB4OTdhNzZiMjgsCiAgICAgICAweDY2YzRmZjk2LCAweDUxNzE2NDQzLCAweGRkMmZjM2IsIDB4YjU2OTZkYTcsIDB4YmJlYjNhYzUsIDB4NWM1M2QyMDQsIDB4ZDMyNjA4Y2UsIDB4NzI3OWI5ZWMsCiAgICAgICAweGY0MTg4ZWNmLCAweGY3ZDc5M2RiLCAweDMzMmNjNDkxLCAweGFiNzZhZTE1LCAweDliZWJlNzI3LCAweDE4YTAxMzg0LCAweDViZTlmOGE3LCAweDVmOTBhNzU0LAogICAgICAgMHgzOWI2NjNjMCwgMHgzNjY3M2M4MywgMHg3YzkyZjUxNCwgMHg5ZDdkOTRkNywgMHhlMmU4ZDlhYSwgMHg1ZjdlOWVhOSwgMHg3YWJkNDU1MSwgMHg1NjllMDVkYSwKICAgICAgIDB4NDBhMjU2MzIsIDB4M2RmNWE5YTUsIDB4YmFiMzdkODAsIDB4NDU0Mjg2ZGMsIDB4M2Y1ZDRlNzgsIDB4M2Q3Yjc1ZCwgMHhiMWZlNGFmNywgMHhhNWFiMjZhM10KCmRlZiBtZDVzdW1fdjMobXNnLCBjb3VudF92Miwgb3JkZXJzLCBjb3VudF92MSwgbj0wKToKICAgIGNvdW50ID0gY291bnRfdjIgJiAweGZmCgogICAgc3YgPSBbMF0gKiA2NAogICAgZm9yIGkgaW4gcmFuZ2UoNjQpOgogICAgICAgIHN2W2ldID0gcm9yMzIoU1YyW2ldLCBjb3VudF92MSkKCiAgICBzdGFydCA9IFsKICAgICAgICByb3IzMigweDc5ZTBmMmZiLCBjb3VudCksCiAgICAgICAgcm9yMzIoMHhjOGI1MjU3MCwgY291bnQpLAogICAgICAgIHJvcjMyKDB4ZWJjMmY4Y2QsIGNvdW50KSwKICAgICAgICByb3IzMigweDdjMTA0ZDkzLCBjb3VudCkKICAgIF0KCiAgICBjb3VudCA9IChjb3VudF92MiArIDYpICYgMHhmZgogICAgZW5kID0gWwogICAgICAgIHJvcjMyKDB4MTliZTQ4NjYsIGNvdW50KSwKICAgICAgICByb3IzMigweGU4NTk4NmI0LCBjb3VudCksCiAgICAgICAgcm9yMzIoMHhlMTliMzI2ZSwgY291bnQpLAogICAgICAgIHJvcjMyKDB4NzFkMWQ3ZDQsIGNvdW50KQogICAgXQogICAgQSA9IHN0YXJ0WzBdICAjIDB4NzllMGYyZmIKICAgIEIgPSBzdGFydFsxXSAgIyAweGM4YjUyNTcwCiAgICBDID0gc3RhcnRbMl0gICMgMHhlYmMyZjhjZAogICAgRCA9IHN0YXJ0WzNdICAjIDB4N2MxMDRkOTMKCiAgICBhID0gQQogICAgYiA9IEIKICAgIGMgPSBDCiAgICBkID0gRAogICAgYmxvY2sgPSBtc2dbOjY0XQogICAgTSA9IGJsb2NrRGl2aWRlKGJsb2NrLCAxNikKCiAgICBvcmRlcjEgPSBvcmRlcnNbOjE2XQogICAgb3JkZXIyID0gb3JkZXJzWzE2OjMyXQogICAgb3JkZXIzID0gb3JkZXJzWzMyOjQ4XQogICAgb3JkZXI0ID0gb3JkZXJzWzQ4Ol0KICAgICMgUm91bmRzCiAgICBhID0gRkYoYSwgYiwgYywgZCwgTVtvcmRlcjFbMF1dLCA3LCBzdlswXSkKICAgIGQgPSBGRihkLCBhLCBiLCBjLCBNW29yZGVyMVsxXV0sIDEyLCBzdlsxXSkgICMgMHhiNmJjNmRkYgogICAgYyA9IEZGKGMsIGQsIGEsIGIsIE1bb3JkZXIxWzJdXSwgMTcsIHN2WzJdKSAgIyAweGY4MGIxNWQ0CiAgICBiID0gRkYoYiwgYywgZCwgYSwgTVtvcmRlcjFbM11dLCAyMiwgc3ZbM10pCiAgICBhID0gRkYoYSwgYiwgYywgZCwgTVtvcmRlcjFbNF1dLCA3LCBzdls0XSkKICAgIGQgPSBGRihkLCBhLCBiLCBjLCBNW29yZGVyMVs1XV0sIDEyLCBzdls1XSkKICAgIGMgPSBGRihjLCBkLCBhLCBiLCBNW29yZGVyMVs2XV0sIDE3LCBzdls2XSkKICAgIGIgPSBGRihiLCBjLCBkLCBhLCBNW29yZGVyMVs3XV0sIDIyLCBzdls3XSkKICAgIGEgPSBGRihhLCBiLCBjLCBkLCBNW29yZGVyMVs4XV0sIDcsIHN2WzhdKQogICAgZCA9IEZGKGQsIGEsIGIsIGMsIE1bb3JkZXIxWzldXSwgMTIsIHN2WzldKQogICAgYyA9IEZGKGMsIGQsIGEsIGIsIE1bb3JkZXIxWzEwXV0sIDE3LCBzdlsxMF0pCiAgICBiID0gRkYoYiwgYywgZCwgYSwgTVtvcmRlcjFbMTFdXSwgMjIsIHN2WzExXSkKICAgIGEgPSBGRihhLCBiLCBjLCBkLCBNW29yZGVyMVsxMl1dLCA3LCBzdlsxMl0pCiAgICBkID0gRkYoZCwgYSwgYiwgYywgTVtvcmRlcjFbMTNdXSwgMTIsIHN2WzEzXSkKICAgIGMgPSBGRihjLCBkLCBhLCBiLCBNW29yZGVyMVsxNF1dLCAxNywgc3ZbMTRdKQogICAgYiA9IEZGKGIsIGMsIGQsIGEsIE1bb3JkZXIxWzE1XV0sIDIyLCBzdlsxNV0pCgogICAgYSA9IEdHKGEsIGIsIGMsIGQsIE1bb3JkZXIyWzBdXSwgNSwgc3ZbMTZdKQogICAgZCA9IEdHKGQsIGEsIGIsIGMsIE1bb3JkZXIyWzFdXSwgOSwgc3ZbMTddKQogICAgYyA9IEdHKGMsIGQsIGEsIGIsIE1bb3JkZXIyWzJdXSwgMTQsIHN2WzE4XSkKICAgIGIgPSBHRyhiLCBjLCBkLCBhLCBNW29yZGVyMlszXV0sIDIwLCBzdlsxOV0pCiAgICBhID0gR0coYSwgYiwgYywgZCwgTVtvcmRlcjJbNF1dLCA1LCBzdlsyMF0pCiAgICBkID0gR0coZCwgYSwgYiwgYywgTVtvcmRlcjJbNV1dLCA5LCBzdlsyMV0pCiAgICBjID0gR0coYywgZCwgYSwgYiwgTVtvcmRlcjJbNl1dLCAxNCwgc3ZbMjJdKQogICAgYiA9IEdHKGIsIGMsIGQsIGEsIE1bb3JkZXIyWzddXSwgMjAsIHN2WzIzXSkKICAgIGEgPSBHRyhhLCBiLCBjLCBkLCBNW29yZGVyMls4XV0sIDUsIHN2WzI0XSkKICAgIGQgPSBHRyhkLCBhLCBiLCBjLCBNW29yZGVyMls5XV0sIDksIHN2WzI1XSkKICAgIGMgPSBHRyhjLCBkLCBhLCBiLCBNW29yZGVyMlsxMF1dLCAxNCwgc3ZbMjZdKQogICAgYiA9IEdHKGIsIGMsIGQsIGEsIE1bb3JkZXIyWzExXV0sIDIwLCBzdlsyN10pCiAgICBhID0gR0coYSwgYiwgYywgZCwgTVtvcmRlcjJbMTJdXSwgNSwgc3ZbMjhdKQogICAgZCA9IEdHKGQsIGEsIGIsIGMsIE1bb3JkZXIyWzEzXV0sIDksIHN2WzI5XSkKICAgIGMgPSBHRyhjLCBkLCBhLCBiLCBNW29yZGVyMlsxNF1dLCAxNCwgc3ZbMzBdKQogICAgYiA9IEdHKGIsIGMsIGQsIGEsIE1bb3JkZXIyWzE1XV0sIDIwLCBzdlszMV0pCgogICAgYSA9IEhIKGEsIGIsIGMsIGQsIE1bb3JkZXIzWzBdXSwgNCwgc3ZbMzJdKQogICAgZCA9IEhIKGQsIGEsIGIsIGMsIE1bb3JkZXIzWzFdXSwgMTEsIHN2WzMzXSkKICAgIGMgPSBISChjLCBkLCBhLCBiLCBNW29yZGVyM1syXV0sIDE2LCBzdlszNF0pCiAgICBiID0gSEgoYiwgYywgZCwgYSwgTVtvcmRlcjNbM11dLCAyMywgc3ZbMzVdKQogICAgYSA9IEhIKGEsIGIsIGMsIGQsIE1bb3JkZXIzWzRdXSwgNCwgc3ZbMzZdKQogICAgZCA9IEhIKGQsIGEsIGIsIGMsIE1bb3JkZXIzWzVdXSwgMTEsIHN2WzM3XSkKICAgIGMgPSBISChjLCBkLCBhLCBiLCBNW29yZGVyM1s2XV0sIDE2LCBzdlszOF0pCiAgICBiID0gSEgoYiwgYywgZCwgYSwgTVtvcmRlcjNbN11dLCAyMywgc3ZbMzldKQogICAgYSA9IEhIKGEsIGIsIGMsIGQsIE1bb3JkZXIzWzhdXSwgNCwgc3ZbNDBdKQogICAgZCA9IEhIKGQsIGEsIGIsIGMsIE1bb3JkZXIzWzldXSwgMTEsIHN2WzQxXSkKICAgIGMgPSBISChjLCBkLCBhLCBiLCBNW29yZGVyM1sxMF1dLCAxNiwgc3ZbNDJdKQogICAgYiA9IEhIKGIsIGMsIGQsIGEsIE1bb3JkZXIzWzExXV0sIDIzLCBzdls0M10pCiAgICBhID0gSEgoYSwgYiwgYywgZCwgTVtvcmRlcjNbMTJdXSwgNCwgc3ZbNDRdKQogICAgZCA9IEhIKGQsIGEsIGIsIGMsIE1bb3JkZXIzWzEzXV0sIDExLCBzdls0NV0pCiAgICBjID0gSEgoYywgZCwgYSwgYiwgTVtvcmRlcjNbMTRdXSwgMTYsIHN2WzQ2XSkKICAgIGIgPSBISChiLCBjLCBkLCBhLCBNW29yZGVyM1sxNV1dLCAyMywgc3ZbNDddKQoKICAgIGEgPSBJSShhLCBiLCBjLCBkLCBNW29yZGVyNFswXV0sIDYsIHN2WzQ4XSkKICAgIGQgPSBJSShkLCBhLCBiLCBjLCBNW29yZGVyNFsxXV0sIDEwLCBzdls0OV0pCiAgICBjID0gSUkoYywgZCwgYSwgYiwgTVtvcmRlcjRbMl1dLCAxNSwgc3ZbNTBdKQogICAgYiA9IElJKGIsIGMsIGQsIGEsIE1bb3JkZXI0WzNdXSwgMjEsIHN2WzUxXSkKICAgIGEgPSBJSShhLCBiLCBjLCBkLCBNW29yZGVyNFs0XV0sIDYsIHN2WzUyXSkKICAgIGQgPSBJSShkLCBhLCBiLCBjLCBNW29yZGVyNFs1XV0sIDEwLCBzdls1M10pCiAgICBjID0gSUkoYywgZCwgYSwgYiwgTVtvcmRlcjRbNl1dLCAxNSwgc3ZbNTRdKQogICAgYiA9IElJKGIsIGMsIGQsIGEsIE1bb3JkZXI0WzddXSwgMjEsIHN2WzU1XSkKICAgIGEgPSBJSShhLCBiLCBjLCBkLCBNW29yZGVyNFs4XV0sIDYsIHN2WzU2XSkKICAgIGQgPSBJSShkLCBhLCBiLCBjLCBNW29yZGVyNFs5XV0sIDEwLCBzdls1N10pCiAgICBjID0gSUkoYywgZCwgYSwgYiwgTVtvcmRlcjRbMTBdXSwgMTUsIHN2WzU4XSkKICAgIGIgPSBJSShiLCBjLCBkLCBhLCBNW29yZGVyNFsxMV1dLCAyMSwgc3ZbNTldKQogICAgYSA9IElJKGEsIGIsIGMsIGQsIE1bb3JkZXI0WzEyXV0sIDYsIHN2WzYwXSkKICAgIGQgPSBJSShkLCBhLCBiLCBjLCBNW29yZGVyNFsxM11dLCAxMCwgc3ZbNjFdKQogICAgYyA9IElJKGMsIGQsIGEsIGIsIE1bb3JkZXI0WzE0XV0sIDE1LCBzdls2Ml0pCiAgICBiID0gSUkoYiwgYywgZCwgYSwgTVtvcmRlcjRbMTVdXSwgMjEsIHN2WzYzXSkKCiAgICBBID0gKEEgKyBhKSAlICgyICoqIDMyKSBeIGVuZFswXQogICAgQiA9IChCICsgYikgJSAoMiAqKiAzMikgXiBlbmRbMV0KICAgIEMgPSAoQyArIGMpICUgKDIgKiogMzIpIF4gZW5kWzJdCiAgICBEID0gKEQgKyBkKSAlICgyICoqIDMyKSBeIGVuZFszXQoKICAgIHJlc3VsdCA9IGJ5dGVhcnJheSgKICAgICAgICBBLnRvX2J5dGVzKDQsICJsaXR0bGUiKSArIEIudG9fYnl0ZXMoNCwgImxpdHRsZSIpICsgQy50b19ieXRlcyg0LCAibGl0dGxlIikgKyBELnRvX2J5dGVzKDQsICJsaXR0bGUiKSkKCiAgICByZXN1bHQgKz0gc3VtX21kNShyZXN1bHQpLnRvX2J5dGVzKDQsICJsaXR0bGUiKQogICAgcmV0dXJuIHJlc3VsdAoKZGVmIGJ4b3IoYjEsIGIyKToKICAgIGIzID0gYnl0ZWFycmF5KGxlbihiMSkpCiAgICBmb3IgaSBpbiByYW5nZShsZW4oYjEpKToKICAgICAgICBiM1tpXSA9IGIxW2ldIF4gYjJbaV0KICAgIHJldHVybiBiMwoKZGVmIGdldF9pdihpdiwgZGF0YSk6CiAgICBmb3IgaSBpbiByYW5nZShsZW4oZGF0YSkpOgogICAgICAgIGlmIGkgJiAxID09IDA6CiAgICAgICAgICAgIGl2ID0gKGl2ID4+IDQpIF4gaXYgXiAoaXYgPDwgNikgXiBkYXRhW2ldCiAgICAgICAgZWxzZToKICAgICAgICAgICAgaXYgPSB+KChpdiA+PiA3KSBeIGl2IF4gKGRhdGFbaV0gfCBpdiA8PCAxMikpCiAgICAgICAgaXYgPSBpdiAmIDB4ZmZmZmZmZmYKICAgIHJldHVybiBpdgoKZGVmIGhhc2hfZjEzKHF1ZXJ5X3NtMywgYm9keV9tZDVfYnl0ZXMsIHRzX2J5dGVzLCBraHJvbm9zKToKICAgIGl2ID0gZ2V0X2l2KDB4MjAyMzA5MjgsIHF1ZXJ5X3NtMykKICAgIGl2ID0gZ2V0X2l2KGl2LCBib2R5X21kNV9ieXRlcykKICAgIGl2ID0gZ2V0X2l2KGl2LCB0c19ieXRlcykKCiAgICBpdl92MCA9ICgoaXYgJiAxNSkgKiAxNzEpID4+IDkKICAgIGJyYW5jaCA9IChpdiAmIDE1KSAtICgoaXZfdjAgKiAzKSAmIDB4ZmYpCiAgICBpZiBicmFuY2ggPT0gMDoKICAgICAgICByZXR1cm4gYnJhbmNoXzAoaXZfdjAsIGtocm9ub3MsIHF1ZXJ5X3NtMywgYm9keV9tZDVfYnl0ZXMsIHRzX2J5dGVzKQogICAgZWxpZiBicmFuY2ggPT0gMToKICAgICAgICByZXR1cm4gYnJhbmNoXzEoaXZfdjAsIGtocm9ub3MsIHF1ZXJ5X3NtMywgYm9keV9tZDVfYnl0ZXMsIHRzX2J5dGVzKQogICAgZWxpZiBicmFuY2ggPT0gMjoKICAgICAgICByZXR1cm4gYnJhbmNoXzIoaXYsIGtocm9ub3MsIHF1ZXJ5X3NtMywgYm9keV9tZDVfYnl0ZXMsIHRzX2J5dGVzKQogICAgZWxzZToKICAgICAgICByYWlzZSBFeGNlcHRpb24oIm5vIGJyYW5jaDogIiArIHN0cihicmFuY2gpKQoKZGVmIGJyYW5jaF8wKGl2X3YwLCBraHJvbm9zLCBxdWVyeV9zbTMsIGJvZHlfbWQ1X2J5dGVzLCB0c19ieXRlcyk6CiAgICB0dDAxID0gWzB4YzRhNzg1ODAsIDB4YjNjMGZkMzksIDB4YzU4YzU2ODYsIDB4YzlhYTNiYTcsIDB4ZjVhN2FkZjIsIDB4OTYzYzJlZDFdCiAgICBpdl92MSA9IHR0MDFbaXZfdjBdCgogICAgY291bnRfdjEgPSAoaXZfdjEgKyBraHJvbm9zICsgMSkgJiAweGZmCiAgICBjb3VudF92MiA9IChpdl92MSArIGtocm9ub3MpICYgMHhmZmZmZmZmZgoKICAgIHR0MDIgPSBbMHhlYmI2NGZhZiwgMHg3YWFkY2MyLCAweGNmMzE4N2JmLCAweGUwMTEzOGZmLCAweDZkMGJmY2ZmLCAweDVhMzBhM2JlLCAweGI0MWFkNjM4LCAweDM0MTgwZWI4LCAweGYyMzNlYjZmLAogICAgICAgICAgICAweGIxYTU4NGNjLCAweGNjYzMwZGM3LCAweDQ3ZDFkYjUxLCAweGQ1NTY1M2RlLCAweDcwYTg0ZmExLCAweDU3NDczYzEyLCAweGY3NmYwMjg4LCAweDJjMDc3ZjBhLCAweGRhMGRjYWQwLAogICAgICAgICAgICAweGZiYjg2ZjZjLCAweGZkYzRjZjAwLCAweDY4OGEwMjBkLCAweGU2NzZjNmE2LCAweDhjZDYzMzhiLCAweDFhM2M4ZDBlLCAweGNjZThiMDZiLCAweDZhZDBlZDBiLCAweGEwNTIyNzE3LAogICAgICAgICAgICAweGRjNzFhYzgzLCAweDIyODVkYjcxLCAweGQ1YjRkZGE2LCAweDczNmY4NjUwLCAweDY1NjAzMDZjLCAweDYxN2NlMmE2LCAweGU0MjM0MTdlLCAweGE0MGUxNDMsIDB4NTQ0ZTQwMzIsCiAgICAgICAgICAgIDB4ODhkZmZiMmEsIDB4NzE2YzFhZTAsIDB4NGM0NjdhODgsIDB4NWIyM2JiMywgMHhlMWQwYjg2NiwgMHhiYWEzZGNiOCwgMHhhZTMzNzRkMywgMHhjMzM4MWE1MCwgMHgxNzAyZjc1YiwKICAgICAgICAgICAgMHhmZTZkYTM2OCwgMHhmMGI0Y2Y0OCwgMHg0ZTBmZmJiOCwgMHg3MmFhZDEwZCwgMHgyNmM1M2EzZCwgMHhmMmJjZTBmNiwgMHhiNDU1NzU4MSwgMHg0YTI1N2ZkZCwgMHg4YzMxODJhMiwKICAgICAgICAgICAgMHhhYjBiM2I4NiwgMHgzZDVkZmIxNCwgMHg0ZjEwMzYzNCwgMHhkMzdiNTJkNywgMHg0NDRlZmYxNiwgMHhlYjBhMzNkMSwgMHg2Y2E4NmY2ZSwgMHgyODRiYTcsIDB4ODM4N2NmYSwKICAgICAgICAgICAgMHg1ZmIzNzU4Nl0KCiAgICB0dDAzID0gWzBdICogNjQKICAgIGZvciBpIGluIHJhbmdlKDAsIDY0KToKICAgICAgICB0dDAzW2ldID0gcm9yMzIodHQwMltpXSwgY291bnRfdjEpICYgMHhmZmZmZmZmZgoKICAgIG4wID0gKGNvdW50X3YyICsgMikgJiA3CgogICAgcGFkID0gYnl0ZWFycmF5KDQpCiAgICBzZWVkID0gYnl0ZXMoWzB4ZmEsIDB4NDUsIDB4NjEsIDB4ZDddKQogICAgZm9yIGkgaW4gcmFuZ2UoNCk6CiAgICAgICAgdiA9IGludC5mcm9tX2J5dGVzKGJ5dGVzKFtzZWVkW2ldLCBzZWVkW2ldXSksICdsaXR0bGUnKQogICAgICAgIHYgPSB2ID4+IG4wCiAgICAgICAgcGFkW2ldID0gdiAmIDB4ZmYKCiAgICBjb3VudF92MiA9IGNvdW50X3YyICYgMHhmZgogICAgaW5pdF92YWx1ZSA9IFsKICAgICAgICByb3IzMigweDdhYmE0ZmM4LCBjb3VudF92MiksIHJvcjMyKDB4NjcxNjY1MDcsIGNvdW50X3YyKSwKICAgICAgICByb3IzMigweDY0MDNmYTAwLCBjb3VudF92MiksIHJvcjMyKDB4MzQwZjUxMmYsIGNvdW50X3YyKSwKICAgICAgICByb3IzMig5ODQzMDQ5MTIsIGNvdW50X3YyKSwgcm9yMzIoMzAwNTA0Nzg2NiwgY291bnRfdjIpLAogICAgICAgIHJvcjMyKDI4NzQxMjUyOTMsIGNvdW50X3YyKSwgcm9yMzIoMjE1MjQxMzI2NCwgY291bnRfdjIpCiAgICBdCgogICAgZGF0YSA9IHF1ZXJ5X3NtMyArIGJvZHlfbWQ1X2J5dGVzICsgdHNfYnl0ZXMgKyBwYWQgKyBieXRlcy5mcm9taGV4KCcgMDAgMDAgMDAgMDAgMDAgMDAgMDEgYTAnKQogICAgZGkgPSBbMF0gKiAobGVuKGRhdGEpIC8vIDQpCiAgICBmb3IgaSBpbiByYW5nZShsZW4oZGF0YSkgLy8gNCk6CiAgICAgICAgZGlbaV0gPSBpbnQuZnJvbV9ieXRlcyhkYXRhW2kgKiA0OmkgKiA0ICsgNF0sICJiaWciKQoKICAgIGRpMCA9IGRpWzBdCiAgICBmb3IgaSBpbiByYW5nZSgxMTIpOgogICAgICAgIGRpMSwgZGkxNCA9IGRpW2kgKyAxXSwgZGlbaSArIDE0XQogICAgICAgIHJfZGkxID0gcm9sKGRpMSwgMTQpIF4gcm9sKGRpMSwgMjUpIF4gKGRpMSA+PiAzKQogICAgICAgIHJfZGkyID0gcm9sKGRpMTQsIDEzKSBeIHJvbChkaTE0LCAxNSkgXiAoZGkxNCA+PiAxMCkKICAgICAgICBkaTAgPSBkaTAgKyBkaVtpICsgOV0gKyByX2RpMSArIHJfZGkyCiAgICAgICAgZGkuYXBwZW5kKGRpMCAmIDB4ZmZmZmZmZmYpCiAgICAgICAgZGkwID0gZGkxCgogICAgaWYgaXZfdjAgPT0gNToKICAgICAgICB2X2ogPSBicmFuY2gwX3hvcihpbml0X3ZhbHVlLCBpdl92MSwgZGksIHR0MDMsIDEwMCwgMiwgMCwgMywgNSwgNCwgNiwgNywgMiwgMSwgNSkKICAgIGVsaWYgaXZfdjAgPT0gNDoKICAgICAgICB2X2ogPSBicmFuY2gwX3hvcihpbml0X3ZhbHVlLCBpdl92MSwgZGksIHR0MDMsIDk2LCAwLCA1LCA2LCA3LCAzLCAxLCAyLCA1LCA0LCA0KQogICAgZWxpZiBpdl92MCA9PSAzOgogICAgICAgIHZfaiA9IGJyYW5jaDBfeG9yKGluaXRfdmFsdWUsIGl2X3YxLCBkaSwgdHQwMywgOTksIDMsIDYsIDIsIDQsIDUsIDEsIDAsIDAsIDcsIDYpCiAgICBlbGlmIGl2X3YwID09IDI6CiAgICAgICAgdl9qID0gYnJhbmNoMF94b3IoaW5pdF92YWx1ZSwgaXZfdjEsIGRpLCB0dDAzLCA5NiwgNywgNiwgMiwgMSwgNCwgMCwgNSwgNCwgMywgNSkKICAgIGVsaWYgaXZfdjAgPT0gMToKICAgICAgICB2X2ogPSBicmFuY2gwX3hvcihpbml0X3ZhbHVlLCBpdl92MSwgZGksIHR0MDMsIDk2LCAwLCA2LCA3LCA1LCAzLCAyLCAxLCA1LCA0LCA0KQogICAgZWxpZiBpdl92MCA9PSAwOgogICAgICAgIHZfaiA9IGJyYW5jaDBfeG9yKGluaXRfdmFsdWUsIGl2X3YxLCBkaSwgdHQwMywgMTAxLCA1LCA3LCA2LCAzLCAyLCAxLCAwLCA1LCA0LCAzKQoKICAgIHJldCA9IGJ5dGVhcnJheSgzMikKICAgIGZvciBpIGluIHJhbmdlKDgpOgogICAgICAgIHJldFtpICogNDppICogNCArIDRdID0gKCh2X2pbaV0gKyBpbml0X3ZhbHVlW2ldKSAmIDB4ZmZmZmZmZmYpLnRvX2J5dGVzKDQsICdiaWcnKQoKICAgIHJldCA9IGJ4b3IocmV0WzoxNl0sIHJldFsxNjpdKQogICAgc3VtID0gc3VtX21kNShyZXQpCiAgICByZXQgKz0gc3VtLnRvX2J5dGVzKDQsICJsaXR0bGUiKQogICAgcmV0dXJuIHJldAoKZGVmIHN3YXBfdjAoc3JjLCBzcmNfeG9yLCB0dDIsIHRhYmxlX2YsIG9yZGVyMSwgdHlwPU5vbmUpOgogICAgZGEwID0gWzBdICogOAogICAgaGEwID0gc3JjX3hvcls6XQogICAgZm9yIGkgaW4gcmFuZ2UoOCk6CiAgICAgICAgZGEwW2ldID0gc3JjW29yZGVyMVtpXV0gXiBzcmNfeG9yW2ldCgogICAgZm9yIHJvdW5kIGluIHJhbmdlKDEwKToKICAgICAgICBycl8wID0gcjAwKGhhMFswXSwgaGEwWzFdLCBoYTBbMl0sIGhhMFszXSwgaGEwWzRdLCBoYTBbNV0sIGhhMFs2XSwgaGEwWzddLCAwLCB0YWJsZV9mKQogICAgICAgIHJyXzEgPSByMDAoaGEwWzFdLCBoYTBbMl0sIGhhMFszXSwgaGEwWzRdLCBoYTBbNV0sIGhhMFs2XSwgaGEwWzddLCBoYTBbMF0sIDAsIHRhYmxlX2YpCiAgICAgICAgcnJfMiA9IHIwMChoYTBbMl0sIGhhMFszXSwgaGEwWzRdLCBoYTBbNV0sIGhhMFs2XSwgaGEwWzddLCBoYTBbMF0sIGhhMFsxXSwgMCwgdGFibGVfZikKICAgICAgICBycl8zID0gcjAwKGhhMFszXSwgaGEwWzRdLCBoYTBbNV0sIGhhMFs2XSwgaGEwWzddLCBoYTBbMF0sIGhhMFsxXSwgaGEwWzJdLCAwLCB0YWJsZV9mKQogICAgICAgIHJyXzQgPSByMDAoaGEwWzRdLCBoYTBbNV0sIGhhMFs2XSwgaGEwWzddLCBoYTBbMF0sIGhhMFsxXSwgaGEwWzJdLCBoYTBbM10sIDAsIHRhYmxlX2YpCiAgICAgICAgcnJfNSA9IHIwMChoYTBbNV0sIGhhMFs2XSwgaGEwWzddLCBoYTBbMF0sIGhhMFsxXSwgaGEwWzJdLCBoYTBbM10sIGhhMFs0XSwgMCwgdGFibGVfZikKICAgICAgICBycl82ID0gcjAwKGhhMFs2XSwgaGEwWzddLCBoYTBbMF0sIGhhMFsxXSwgaGEwWzJdLCBoYTBbM10sIGhhMFs0XSwgaGEwWzVdLCAwLCB0YWJsZV9mKQogICAgICAgIHJyXzcgPSByMDAoaGEwWzddLCBoYTBbMF0sIGhhMFsxXSwgaGEwWzJdLCBoYTBbM10sIGhhMFs0XSwgaGEwWzVdLCBoYTBbNl0sIDAsIHRhYmxlX2YpCiAgICAgICAgcnJfNyA9IHJyXzcgXiB0dDJbcm91bmQgKyAxXQoKICAgICAgICBkMCwgZDEsIGQyLCBkMywgZDQsIGQ1LCBkNiwgZDcgPSBkYTBbMF0sIGRhMFsxXSwgZGEwWzJdLCBkYTBbM10sIGRhMFs0XSwgZGEwWzVdLCBkYTBbNl0sIGRhMFs3XQoKICAgICAgICBkYTBbMF0gPSByMDAoZDAsIGQxLCBkMiwgZDMsIGQ0LCBkNSwgZDYsIGQ3LCBycl8wLCB0YWJsZV9mKQogICAgICAgIGRhMFsxXSA9IHIwMChkMSwgZDIsIGQzLCBkNCwgZDUsIGQ2LCBkNywgZDAsIHJyXzEsIHRhYmxlX2YpICAjIDB4ZDBhNDg5YjM1YmE2NzhlOAogICAgICAgIGRhMFsyXSA9IHIwMChkMiwgZDMsIGQ0LCBkNSwgZDYsIGQ3LCBkMCwgZDEsIHJyXzIsIHRhYmxlX2YpICAjIDB4M2JlNWI3ZjljZmQ0NDY1NAogICAgICAgIGRhMFszXSA9IHIwMChkMywgZDQsIGQ1LCBkNiwgZDcsIGQwLCBkMSwgZDIsIHJyXzMsIHRhYmxlX2YpCiAgICAgICAgZGEwWzRdID0gcjAwKGQ0LCBkNSwgZDYsIGQ3LCBkMCwgZDEsIGQyLCBkMywgcnJfNCwgdGFibGVfZikKICAgICAgICBkYTBbNV0gPSByMDAoZDUsIGQ2LCBkNywgZDAsIGQxLCBkMiwgZDMsIGQ0LCBycl81LCB0YWJsZV9mKQogICAgICAgIGRhMFs2XSA9IHIwMChkNiwgZDcsIGQwLCBkMSwgZDIsIGQzLCBkNCwgZDUsIHJyXzYsIHRhYmxlX2YpCiAgICAgICAgZGEwWzddID0gcjAwKGQ3LCBkMCwgZDEsIGQyLCBkMywgZDQsIGQ1LCBkNiwgcnJfNywgdGFibGVfZikKCiAgICAgICAgaGEwWzBdLCBoYTBbMV0sIGhhMFsyXSwgaGEwWzNdLCBoYTBbNF0sIGhhMFs1XSwgaGEwWzZdLCBoYTBbN10gPSBycl8wLCBycl8xLCBycl8yLCBycl8zLCBycl80LCBycl81LCBycl82LCBycl83CgogICAgaWYgdHlwIGlzIE5vbmU6CiAgICAgICAgc3JjWzBdID0gZGEwWzBdIF4gc3JjX3hvclswXSBeIHNyY1swXQogICAgICAgIHNyY1sxXSA9IGRhMFs3XSBeIHNyY194b3JbMV0gXiBzcmNbMV0KICAgICAgICBzcmNbMl0gPSBkYTBbNl0gXiBzcmNfeG9yWzJdIF4gc3JjWzJdCiAgICAgICAgc3JjWzNdID0gZGEwWzVdIF4gc3JjX3hvclszXSBeIHNyY1szXQogICAgICAgIHNyY1s0XSA9IGRhMFs0XSBeIHNyY194b3JbNF0gXiBzcmNbNF0KICAgICAgICBzcmNbNV0gPSBkYTBbM10gXiBzcmNfeG9yWzVdIF4gc3JjWzVdCiAgICAgICAgc3JjWzZdID0gZGEwWzJdIF4gc3JjX3hvcls2XSBeIHNyY1s2XQogICAgICAgIHNyY1s3XSA9IGRhMFsxXSBeIHNyY194b3JbN10gXiBzcmNbN10KICAgIGVsc2U6CiAgICAgICAgc3JjWzBdID0gZGEwWzddIF4gdHlwWzFdCiAgICAgICAgc3JjWzFdID0gZGEwWzZdIF4gdHlwWzJdCiAgICAgICAgc3JjWzJdID0gZGEwWzVdIF4gdHlwWzNdCiAgICAgICAgc3JjWzNdID0gZGEwWzRdIF4gdHlwWzRdCiAgICAgICAgc3JjWzRdID0gZGEwWzNdIF4gdHlwWzVdCiAgICAgICAgc3JjWzVdID0gZGEwWzJdIF4gdHlwWzZdCiAgICAgICAgc3JjWzZdID0gZGEwWzFdIF4gdHlwWzddIF4gc3JjWzddCiAgICAgICAgc3JjWzddID0gZGEwWzBdIF4gdHlwWzBdCiAgICByZXR1cm4gc3JjCgpkZWYgYnJhbmNoXzEoaXZfdjAsIGtocm9ub3MsIHF1ZXJ5X3NtMywgYm9keV9tZDVfYnl0ZXMsIHRzX2J5dGVzKToKICAgIHR0MSA9IFsweDgwOGE5Yzc5LCAweGYwNzk4MDdlLCAweGJhZGY3OWM1LCAweGE3ODVkM2ZmLCAweDgyZDg0MzhjXQogICAgaXZfdjEgPSB0dDFbaXZfdjBdCgogICAgY192MSA9IChpdl92MSArIGtocm9ub3MpICYgMHhmZgogICAgY192MSA9IHJvcihraHJvbm9zLCBjX3YxKQoKICAgIG9yZGVycyA9IGJ5dGVzLmZyb21oZXgoJycnMDUgMDcgMDEgMDIgMDQgMDAgMDYgMDMgMDAgMDUgMDIgMDQgMDEgMDMgMDcgMDYKICAgIDA1IDA3IDAyIDA0IDAxIDA2IDAzIDAwIDAzIDAwIDAyIDA0IDA2IDA3IDAxIDA1CiAgICAwNCAwNSAwMCAwMyAwNiAwMiAwMSAwNyAwMCAwMCAwMCAwMCAwMCAwMCAwMCAwMCcnJykKCiAgICBvcmRlcjEgPSBvcmRlcnNbaXZfdjAgKiA4Oml2X3YwICogOCArIDhdCgogICAgaXZfdjEgPSAoaXZfdjEgKyBraHJvbm9zICsgMSkgJiA2MwogICAgdHQxID0gWzB4ODdhZWVhNWRhYjM3Y2Q2YiwgMHg3ZmY0OGJlY2I0ZjU0MDg3LCAweGIwNzI0YzA2NzA2YmJkNWQsIDB4MWZlNWRmYjExNDNlMzI4ZCwKICAgICAgICAgICAweDFhMjMzMWQwMGFmNGYxZjIsIDB4Y2FmZjcxMzFiYjFlNzFiYSwgMHgzMzM4NWUxMDQyNzUyMjE4LCAweGZmMDFlZDY1ZDRhNDQxZmIsCiAgICAgICAgICAgMHhhZGIxZWM4ODI4YzgwZTgsIDB4NjI0NzVkMTJmNGUwNmZlNywgMHhiZDBiMjM4ZGE0ZmU3Ml0KCiAgICB0dDIgPSBbMF0gKiAxMQogICAgZm9yIGkgaW4gcmFuZ2UoMCwgMTEpOgogICAgICAgIHR0MltpXSA9IHJvcih0dDFbaV0sIGl2X3YxKQoKICAgIHRvX3NpZ24gPSBieXRlYXJyYXkocXVlcnlfc20zICsgYm9keV9tZDVfYnl0ZXMgKyB0c19ieXRlcyArIGJ5dGVzKFsweDgwLCAwLCAwLCAwLCAwLCAwLCAwLCAwLCAwLCAwLCAwLCAwXSkpCgogICAgc3JjID0gWzBdICogKGxlbih0b19zaWduKSAvLyA4KQogICAgZm9yIGkgaW4gcmFuZ2UobGVuKHRvX3NpZ24pIC8vIDgpOgogICAgICAgIHNyY1tpXSA9IGludC5mcm9tX2J5dGVzKHRvX3NpZ25baSAqIDg6aSAqIDggKyA4XSwgJ2JpZycpCgogICAgc3JjX3hvciA9IFtjX3YxLCBjX3YxLCBjX3YxLCBjX3YxLCBjX3YxLCBjX3YxLCBjX3YxLCBjX3YxXQoKICAgIHRhYmxlX2YgPSBnZXRfYnJhbmNoXzFfdGFibGVfZihpdl92MCkKICAgIHN3YXAgPSBzd2FwX3YwKHNyYywgc3JjX3hvciwgdHQyLCB0YWJsZV9mLCBvcmRlcjEpCiAgICBkYXRhID0gWzBdICogOAogICAgZGF0YVs3XSA9IDQxNgoKICAgIHNyY194b3IgPSBbc3dhcFs0XSwgc3dhcFszXSwgc3dhcFsyXSwgc3dhcFsxXSwgc3dhcFswXSwgc3dhcFs3XSwgc3dhcFs2XSwgc3dhcFs1XV0KICAgIHN3YXAgPSBzd2FwX3YwKGRhdGEsIHNyY194b3IsIHR0MiwgdGFibGVfZiwgb3JkZXIxLCBzd2FwKQoKICAgIHJldCA9IGJ5dGVhcnJheSgzMikKICAgIG4gPSAwCiAgICBmb3IgaSBpbiByYW5nZSg3LCAtMSwgLTEpOgogICAgICAgIHBwID0gc3dhcFtpXS50b19ieXRlcyg4LCAibGl0dGxlIikKICAgICAgICByZXRbbiArIDBdLCByZXRbbiArIDFdLCByZXRbbiArIDJdLCByZXRbbiArIDNdID0gcHBbMV0sIHBwWzNdLCBwcFs1XSwgcHBbNl0KICAgICAgICBuICs9IDQKCiAgICBmb3IgaSBpbiByYW5nZSgxNik6CiAgICAgICAgcmV0W2ldIF49IHJldFtpICsgMTZdCiAgICByZXQgPSByZXRbOjE2XQogICAgc3VtID0gc3VtX21kNShyZXQpCiAgICByZXQgKz0gc3VtLnRvX2J5dGVzKDQsICJsaXR0bGUiKQogICAgcmV0dXJuIHJldAoKZGVmIHIwMChyMCwgcjEsIHIyLCByMywgcjQsIHI1LCByNiwgcjcsIHR0LCB0YWJsZV9mLCB2PTApOgogICAgeCA9IHRhYmxlX2YoOCAqIChyMCA+PiA1NikpCiAgICByMSA9IChyMSA+PiA0NSkgJiAyMDQwCgogICAgaWYgdHQgPiAwOgogICAgICAgIHggPSB4IF4gdHQKICAgIHggPSB4IF4gdGFibGVfZihyMSArIDIwNDgpCgogICAgcjIgPSAocjIgPj4gMzcpICYgMjA0MAogICAgeCA9IHggXiB0YWJsZV9mKHIyICsgNDA5NikKCiAgICByMyA9IChyMyA+PiAyOSkgJiAyMDQwCiAgICB4ID0geCBeIHRhYmxlX2YocjMgKyA2MTQ0KQoKICAgIHI0ID0gKHI0ID4+IDIxKSAmIDIwNDAKICAgIHggPSB4IF4gdGFibGVfZihyNCArIDgxOTIpCgogICAgcjUgPSAocjUgPj4gMTMpICYgMjA0MAogICAgeCA9IHggXiB0YWJsZV9mKHI1ICsgMTAyNDApCgogICAgcjYgPSAocjYgPj4gOCkgJiAyNTUKICAgIHggPSB4IF4gdGFibGVfZig4ICogcjYgKyAxMjI4OCkKCiAgICByNyA9IHI3ICYgMjU1CiAgICB4ID0geCBeIHRhYmxlX2YoOCAqIHI3ICsgMTQzMzYpCgogICAgcmV0dXJuIHgKCmJyYW5jaF8yX29yZGVycyA9IGJ5dGVzLmZyb21oZXgoJycnCiAgICAwZiAwNyAwNCAwMCAwOSAwOCAwMyAwYSAwNiAwYiAwNSAwZCAwZSAwMSAwYyAwMiAwZiAwNSAwOCAwYyAwMCAwOSAwMiAwMSAwMyAwNyAwZSAwNiAwYiAwYSAwZCAwNCAwNiAwNSAwMCAwNyAwYyAwMCAwYSAwNCAwOCAwZiAwMSAwYiAwZCAwOSAwMiAwZSAwNiAwYiAwMiAwNSAwNCAwMyAwOCAwMSAwMSAwNyAwYSAwMCAwZCAwYyAwOSAwZQogICAgMGQgMDcgMGUgMGYgMGIgMDIgMDggMDMgMGMgMDUgMDkgMDEgMDAgMDQgMDYgMGEgMGQgMDkgMDIgMDYgMGYgMGIgMGEgMDQgMDggMDcgMDAgMGMgMDUgMDMgMDEgMGUgMGMgMDkgMGYgMDcgMDYgMGYgMDMgMGUgMDIgMGQgMDQgMDUgMDEgMGIgMGEgMDAgMGMgMDUgMGEgMDkgMGUgMDggMDIgMDQgMDQgMDcgMDMgMGYgMDEgMDYgMGIgMDAKICAgIDBiIDBmIDA0IDA4IDAyIDBhIDA3IDAwIDA5IDBkIDA2IDAxIDBlIDAzIDA1IDBjIDBiIDA2IDBhIDA1IDA4IDAyIDBjIDAzIDA3IDBmIDBlIDA5IDBkIDAwIDAxIDA0IDA5IDA2IDA4IDBmIDA1IDA4IDAwIDA0IDBhIDBiIDAzIDBkIDAxIDAyIDBjIDBlIDA5IDBkIDBjIDA2IDA0IDA3IDBhIDAzIDAzIDBmIDAwIDA4IDAxIDA1IDAyIDBlCiAgICAwMSAwMCAwZCAwZiAwOSAwYSAwYiAwZSAwNCAwMiAwOCAwNyAwMyAwNiAwYyAwNSAwMSAwOCAwYSAwYyAwZiAwOSAwNSAwNiAwYiAwMCAwMyAwNCAwMiAwZSAwNyAwZCAwNCAwOCAwZiAwMCAwYyAwZiAwZSAwZCAwYSAwMSAwNiAwMiAwNyAwOSAwNSAwMyAwNCAwMiAwNSAwOCAwZCAwYiAwYSAwNiAwNiAwMCAwZSAwZiAwNyAwYyAwOSAwMwogICAgMGEgMDggMDQgMGYgMDAgMGIgMDEgMDYgMGQgMGMgMDcgMDkgMDMgMGUgMDUgMDIgMGEgMDcgMGIgMDUgMGYgMDAgMDIgMGUgMDEgMDggMDMgMGQgMGMgMDYgMDkgMDQgMGQgMDcgMGYgMDggMDUgMGYgMDYgMDQgMGIgMGEgMGUgMGMgMDkgMDAgMDIgMDMgMGQgMGMgMDIgMDcgMDQgMDEgMGIgMGUgMGUgMDggMDYgMGYgMDkgMDUgMDAgMDMKICAgICcnJykKCmRlZiBicmFuY2hfMihpdiwga2hyb25vcywgcXVlcnlfc20zLCBib2R5X21kNV9ieXRlcywgdHNfYnl0ZXMpOgogICAgbjAgPSAoaXYgJiAxNSAtIDIpICogODYKICAgIGl2X3YwID0gKG4wID4+IDE1ICYgMHhmZikgKyAobjAgPj4gOCAmIDB4ZmYpCgogICAgdDAwMSA9IFsweDg5ODBmMjliLCAweGViNTQ5YzdmLCAweGIwODcyNmRiLCAweGQ0MGNiNWU2LCAweGU4ZjU1OWU0XQoKICAgIG4xID0gdDAwMVtpdl92MF0KICAgIGNvdW50X3YxID0gKG4xICsga2hyb25vcyArIDEpICYgMHhmZgogICAgY291bnRfdjIgPSAobjEgKyBraHJvbm9zKSAmIDB4ZmZmZmZmZmYKCiAgICBuMCA9IChjb3VudF92MiArIDUpICYgNwoKICAgIHBhZCA9IGJ5dGVhcnJheSg4KQogICAgc2VlZCA9IGJ5dGVzKFsweDg0LCAweDk2LCAweDc3LCAweDlkLCAweGQ0LCAweDE1LCAweDBiLCAweGY4XSkKICAgIGZvciBpIGluIHJhbmdlKDgpOgogICAgICAgIHYgPSBpbnQuZnJvbV9ieXRlcyhieXRlcyhbc2VlZFtpXSwgc2VlZFtpXV0pLCAnbGl0dGxlJykKICAgICAgICB2ID0gdiA+PiBuMAogICAgICAgIHBhZFtpXSA9IHYgJiAweGZmCgogICAgZGF0YSA9IHF1ZXJ5X3NtMyArIGJvZHlfbWQ1X2J5dGVzICsgdHNfYnl0ZXMgKyBwYWQgKyBieXRlcy5mcm9taGV4KCdhMCAwMSAwMCAwMCcpCgogICAgaWR4ID0gaXZfdjAgPDwgNgogICAgcmV0ID0gbWQ1c3VtX3YzKGRhdGEsIGNvdW50X3YyLCBicmFuY2hfMl9vcmRlcnNbaWR4OmlkeCArIDY0XSwgY291bnRfdjEpCgogICAgcmV0dXJuIHJldAoKZGVmIGJyYW5jaDBfeG9yKGRhdGEsIGJhc2UsIGRpLCB0dDAzLCByb3VuZCwgeDEsIHgyLCB4MywgeDQsIHg1LCB4NiwgeDcsIHg4LCB4OSwgeDEwKToKICAgIGQgPSBkYXRhWzpdCgogICAgZm9yIGkgaW4gcmFuZ2Uocm91bmQpOgogICAgICAgIG9mZnNldCA9IGJhc2UgKyBpCiAgICAgICAgbjAgPSBkaVtvZmZzZXQgJiAxMjddCgogICAgICAgIG4xID0gKChkW3gzXSBeIGRbeDRdKSAmIGRbeDFdKSBeIGRbeDNdCgogICAgICAgIG4yID0gcm9sKGRbeDFdLCAyNikgXiByb2woZFt4MV0sIDIxKSBeIHJvbChkW3gxXSwgNykKICAgICAgICBvZmZzZXQgPSBvZmZzZXQgJiA2MwogICAgICAgIG4zID0gdHQwM1tvZmZzZXRdCgogICAgICAgIG40ID0gKG4wICsgbjEgKyBuMiArIG4zICsgZFt4NV0pICYgMHhmZmZmZmZmZgoKICAgICAgICBuNSA9IHJvbChkW3gyXSwgMzApIF4gcm9sKGRbeDJdLCAxOSkgXiByb2woZFt4Ml0sIDEwKQogICAgICAgIG42ID0gKGRbeDJdICYgZFt4Nl0pIHwgKChkW3gyXSB8IGRbeDZdKSAmIGRbeDddKQogICAgICAgIG43ID0gbjUgKyBuNgoKICAgICAgICBvID0gZFt4OV0KICAgICAgICBkWzBdLCBkWzFdLCBkWzJdLCBkWzNdLCBkWzRdLCBkWzVdLCBkWzZdLCBkWzddID0gZFs3XSwgZFswXSwgZFsxXSwgZFsyXSwgZFszXSwgZFs0XSwgZFs1XSwgZFs2XQogICAgICAgIGRbeDEwXSA9IChuNyArIG40KSAmIDB4ZmZmZmZmZmYKICAgICAgICBkW3g4XSA9IChvICsgbjQpICYgMHhmZmZmZmZmZgogICAgcmV0dXJuIGQKCmJyYW5jaF8xX3RhYmxlID0gTm9uZQoKZGVmIGdldF9icmFuY2hfMV90YWJsZV9mKGl2X3YwKToKICAgIGdsb2JhbCBicmFuY2hfMV90YWJsZQogICAgaWYgYnJhbmNoXzFfdGFibGUgaXMgTm9uZToKICAgICAgICBicmFuY2hfMV90YWJsZSA9IF9icmFuY2hfb25lX2J5dGVzKCkKCiAgICB0YWJsZSA9IGJyYW5jaF8xX3RhYmxlW2l2X3YwIDw8IDE0Ol0KICAgIGRlZiB0YWJsZV9mKHgpOgogICAgICAgIHJldHVybiBpbnQuZnJvbV9ieXRlcyh0YWJsZVt4OnggKyA4XSwgJ2xpdHRsZScpCiAgICByZXR1cm4gdGFibGVfZgoKZGVmIF92YXJpbnQodmFsdWU6IGludCkgLT4gYnl0ZXM6CiAgICB2YWx1ZSA9IGludCh2YWx1ZSkKICAgIGlmIHZhbHVlIDwgMDoKICAgICAgICB2YWx1ZSAmPSAoMSA8PCA2NCkgLSAxCiAgICByZXN1bHQgPSBieXRlYXJyYXkoKQogICAgd2hpbGUgdmFsdWUgPiAweDdGOgogICAgICAgIHJlc3VsdC5hcHBlbmQoKHZhbHVlICYgMHg3RikgfCAweDgwKQogICAgICAgIHZhbHVlID4+PSA3CiAgICByZXN1bHQuYXBwZW5kKHZhbHVlKQogICAgcmV0dXJuIGJ5dGVzKHJlc3VsdCkKCmRlZiBfc2ludCh2YWx1ZTogaW50LCBiaXRzOiBpbnQpIC0+IGludDoKICAgICMg5q2j5byPIHByb3RvYnVmIOe8lueggeinhOWIme+8muato+aVsOS4jeWFiOaIquaWreWIsOacieespuWPt+iMg+WbtO+8mwogICAgIyDov5nlr7kgTWVkdXNhLnJhbmQg562J5Y+v6IO95aSn5LqOIDIqKjMxIOeahCBzaW50MzIg5a2X5q615b6I6YeN6KaB44CCCiAgICB2YWx1ZSA9IGludCh2YWx1ZSkKICAgIHJldHVybiAodmFsdWUgPDwgMSkgaWYgdmFsdWUgPj0gMCBlbHNlICh2YWx1ZSA8PCAxKSBeICh+MCkKCmRlZiBfcHJvdG9fZmllbGQoZmllbGQ6IGludCwgdmFsdWU6IEFueSwga2luZDogc3RyKSAtPiBieXRlczoKICAgIGlmIHZhbHVlIGluIChOb25lLCAiIiwgYiIiLCAwLCAwLjAsIEZhbHNlKToKICAgICAgICByZXR1cm4gYiIiCiAgICBpZiBraW5kID09ICJzaW50MzIiOgogICAgICAgIHJldHVybiBfdmFyaW50KChmaWVsZCA8PCAzKSB8IDApICsgX3ZhcmludChfc2ludChpbnQodmFsdWUpLCAzMikpCiAgICBpZiBraW5kID09ICJzaW50NjQiOgogICAgICAgIHJldHVybiBfdmFyaW50KChmaWVsZCA8PCAzKSB8IDApICsgX3ZhcmludChfc2ludChpbnQodmFsdWUpLCA2NCkpCiAgICBpZiBraW5kID09ICJmbG9hdCI6CiAgICAgICAgcmV0dXJuIF92YXJpbnQoKGZpZWxkIDw8IDMpIHwgNSkgKyBzdHJ1Y3QucGFjaygiPGYiLCBmbG9hdCh2YWx1ZSkpCiAgICBpZiBraW5kID09ICJieXRlcyI6CiAgICAgICAgcmF3ID0gYnl0ZXModmFsdWUpCiAgICBlbGlmIGtpbmQgPT0gInN0cmluZyI6CiAgICAgICAgcmF3ID0gc3RyKHZhbHVlKS5lbmNvZGUoInV0Zi04IikKICAgIGVsaWYga2luZCA9PSAibWVzc2FnZSI6CiAgICAgICAgcmF3ID0gYnl0ZXModmFsdWUpCiAgICBlbHNlOgogICAgICAgIHJhaXNlIFZhbHVlRXJyb3IoZiJ1bmtub3duIHByb3RvYnVmIGZpZWxkIGtpbmQ6IHtraW5kfSIpCiAgICByZXR1cm4gX3ZhcmludCgoZmllbGQgPDwgMykgfCAyKSArIF92YXJpbnQobGVuKHJhdykpICsgcmF3CgpkZWYgX3Byb3RvKGZpZWxkczogbGlzdFt0dXBsZVtpbnQsIEFueSwgc3RyXV0pIC0+IGJ5dGVzOgogICAgcmV0dXJuIGIiIi5qb2luKF9wcm90b19maWVsZChmaWVsZCwgdmFsdWUsIGtpbmQpIGZvciBmaWVsZCwgdmFsdWUsIGtpbmQgaW4gZmllbGRzKQoKZGVmIF9lbmNvZGVfcmVxdWVzdCgpIC0+IGJ5dGVzOgogICAgcmV0dXJuIF9wcm90byhbCiAgICAgICAgKDEsIDExMSwgInNpbnQzMiIpLAogICAgICAgICgyLCAxMCwgInNpbnQzMiIpLAogICAgICAgICgzLCA2OTQzNjcsICJzaW50MzIiKSwKICAgICAgICAoNSwgNTg2OTUyMTk5LCAic2ludDMyIiksCiAgICBdKQoKZGVmIF9lbmNvZGVfZGV2aWNlKGRldmljZTogTWFwcGluZ1tzdHIsIEFueV0pIC0+IGJ5dGVzOgogICAgZmllbGRzID0gWwogICAgICAgICgxLCBkZXZpY2UuZ2V0KCJkMSIpLCAic2ludDMyIiksICgyLCBkZXZpY2UuZ2V0KCJjb2xsZWN0X3N0YXQiKSwgInNpbnQzMiIpLAogICAgICAgICgzLCBkZXZpY2UuZ2V0KCJhaWQiKSwgInN0cmluZyIpLCAoNCwgZGV2aWNlLmdldCgiZGV2aWNlX2lkIiksICJzdHJpbmciKSwKICAgICAgICAoNSwgZGV2aWNlLmdldCgic2VjX2RldmljZV90b2tlbiIpLCAic3RyaW5nIiksICg2LCBkZXZpY2UuZ2V0KCJhcHBfdmVyc2lvbiIpLCAic3RyaW5nIiksCiAgICAgICAgKDcsIGRldmljZS5nZXQoImJhdHRlcnkiKSwgInNpbnQzMiIpLCAoOCwgZGV2aWNlLmdldCgiYmF0dGVyeTIiKSwgInNpbnQzMiIpLAogICAgICAgICg5LCBkZXZpY2UuZ2V0KCJiYXR0ZXJ5X2hlYWx0aCIpLCAic2ludDMyIiksICgxMCwgZGV2aWNlLmdldCgiYmF0dGVyeV9jaGFuZ2VkIiksICJzaW50MzIiKSwKICAgICAgICAoMTEsIGRldmljZS5nZXQoIm5ldHdvcmsiKSwgInN0cmluZyIpLCAoMTIsIGRldmljZS5nZXQoInR6IiksICJzdHJpbmciKSwKICAgICAgICAoMTMsIGRldmljZS5nZXQoImxhbiIpLCAic3RyaW5nIiksICgxNCwgZGV2aWNlLmdldCgiY3B1IiksICJzaW50MzIiKSwKICAgICAgICAoMTUsIGRldmljZS5nZXQoInJlc29sdXRpb24iKSwgInN0cmluZyIpLCAoMTYsIGRldmljZS5nZXQoInNkY2FyZCIpLCAiZmxvYXQiKSwKICAgICAgICAoMTcsIGRldmljZS5nZXQoInNkY2FyZF91c2VkIiksICJmbG9hdCIpLCAoMTgsIGRldmljZS5nZXQoIm1lbW9yeSIpLCAiZmxvYXQiKSwKICAgICAgICAoMTksIGRldmljZS5nZXQoIm1lbW9yeTIiKSwgImZsb2F0IiksICgyMCwgZGV2aWNlLmdldCgiZGF0YSIpLCAiZmxvYXQiKSwKICAgICAgICAoMjEsIGRldmljZS5nZXQoImRhdGFfdXNlZCIpLCAiZmxvYXQiKSwgKDIyLCBkZXZpY2UuZ2V0KCJvc192ZXJzaW9uIiksICJzdHJpbmciKSwKICAgICAgICAoMjMsIGRldmljZS5nZXQoImJyaWdodG5lc3MiKSwgInNpbnQzMiIpLCAoMjQsIGRldmljZS5nZXQoInZvbHVtZSIpLCAic2ludDMyIiksCiAgICAgICAgKDI1LCBkZXZpY2UuZ2V0KCJ0cyIpLCAic2ludDY0IiksICgyNiwgZGV2aWNlLmdldCgidHMyIiksICJzaW50NjQiKSwKICAgICAgICAoMjcsIGRldmljZS5nZXQoInRzMyIpLCAic2ludDY0IiksICgyOCwgZGV2aWNlLmdldCgidHM0IiksICJzaW50NjQiKSwKICAgICAgICAoMjksIGRldmljZS5nZXQoInVzYiIpLCAic2ludDMyIiksICgzMCwgZGV2aWNlLmdldCgiaHdfdmVyc2lvbiIpLCAic3RyaW5nIiksCiAgICAgICAgKDMxLCBkZXZpY2UuZ2V0KCJicmFuZCIpLCAic3RyaW5nIiksICgzMiwgZGV2aWNlLmdldCgiYm9hcmQiKSwgInN0cmluZyIpLAogICAgICAgICgzMywgZGV2aWNlLmdldCgicHJvZHVjdF9uYW1lIiksICJzdHJpbmciKSwgKDM0LCBkZXZpY2UuZ2V0KCJwcm9kdWN0X2RldmljZSIpLCAic3RyaW5nIiksCiAgICAgICAgKDM1LCBkZXZpY2UuZ2V0KCJwcm9kdWN0X21hbnVmYWN0dXJlciIpLCAic3RyaW5nIiksICgzNiwgZGV2aWNlLmdldCgiaGFyZHdhcmUiKSwgInN0cmluZyIpLAogICAgICAgICgzOCwgZGV2aWNlLmdldCgidW5rbm93bjM4IiksICJzaW50MzIiKSwgKDQwLCBkZXZpY2UuZ2V0KCJ1bmtub3duNDAiKSwgInNpbnQzMiIpLAogICAgXQogICAgcmV0dXJuIF9wcm90byhmaWVsZHMpCgpkZWYgX2VuY29kZV9lbnYoZW52OiBNYXBwaW5nW3N0ciwgQW55XSkgLT4gYnl0ZXM6CiAgICBmaWVsZHMgPSBbCiAgICAgICAgKDEsIGVudi5nZXQoImxhdW5jaF90aW1lIiksICJzaW50MzIiKSwgKDIsIGVudi5nZXQoInVua25vd24yIiksICJzaW50MzIiKSwKICAgICAgICAoMywgZW52LmdldCgidW5rbm93bjMiKSwgInNpbnQzMiIpLCAoNSwgZW52LmdldCgidW5rbm93bjUiKSwgInNpbnQzMiIpLAogICAgICAgICg2LCBlbnYuZ2V0KCJ2ZXJzaW9uIiksICJzdHJpbmciKSwgKDcsIGVudi5nZXQoInBpZCIpLCAic2ludDMyIiksCiAgICAgICAgKDEyLCBfZW5jb2RlX2RldmljZShlbnYuZ2V0KCJkZXZpY2UiKSBvciB7fSksICJtZXNzYWdlIiksCiAgICAgICAgKDEzLCBfcHJvdG8oWwogICAgICAgICAgICAoMSwgKGVudi5nZXQoInJlcG9ydCIpIG9yIHt9KS5nZXQoInRpbWUiKSwgInNpbnQ2NCIpLAogICAgICAgICAgICAoMiwgKGVudi5nZXQoInJlcG9ydCIpIG9yIHt9KS5nZXQoInN0YXRlIiksICJzaW50MzIiKSwKICAgICAgICAgICAgKDQsIChlbnYuZ2V0KCJyZXBvcnQiKSBvciB7fSkuZ2V0KCJjb2RlIiksICJzaW50MzIiKSwKICAgICAgICAgICAgKDUsIChlbnYuZ2V0KCJyZXBvcnQiKSBvciB7fSkuZ2V0KCJ0aW1lcyIpLCAic2ludDMyIiksCiAgICAgICAgICAgICg2LCAoZW52LmdldCgicmVwb3J0Iikgb3Ige30pLmdldCgidW5rbm93bjYiKSwgInNpbnQzMiIpLAogICAgICAgIF0pLCAibWVzc2FnZSIpLAogICAgICAgICgxNCwgZW52LmdldCgiYXBwX3ZlcnNpb24iKSwgInN0cmluZyIpLAogICAgICAgICgxNSwgZW52LmdldCgidW5rbm93bjE1IiksICJzaW50MzIiKSwgKDE2LCBlbnYuZ2V0KCJ1bmtub3duMTYiKSwgInNpbnQzMiIpLAogICAgICAgICgxOCwgZW52LmdldCgidW5rbm93bjE4IiksICJzaW50MzIiKSwgKDE5LCBlbnYuZ2V0KCJ1bmtub3duMTkiKSwgInNpbnQzMiIpLAogICAgICAgICgyMCwgZW52LmdldCgidW5rbm93bjIwIiksICJzaW50MzIiKSwgKDIxLCBlbnYuZ2V0KCJ1bmtub3duMjEiKSwgInNpbnQzMiIpLAogICAgXQogICAgcmV0dXJuIF9wcm90byhmaWVsZHMpCgpkZWYgX2VuY29kZV9tZWR1c2EodmFsdWVzOiBNYXBwaW5nW3N0ciwgQW55XSkgLT4gYnl0ZXM6CiAgICByZXR1cm4gX3Byb3RvKFsKICAgICAgICAoMSwgdmFsdWVzLmdldCgibWFnaWMiKSwgImJ5dGVzIiksICgyLCB2YWx1ZXMuZ2V0KCJ2ZXJzaW9uIiksICJzaW50MzIiKSwKICAgICAgICAoMywgdmFsdWVzLmdldCgicmFuZCIpLCAic2ludDMyIiksICg0LCB2YWx1ZXMuZ2V0KCJtc19hcHBfaWQiKSwgInN0cmluZyIpLAogICAgICAgICg1LCB2YWx1ZXMuZ2V0KCJkZXZpY2VfaWQiKSwgInN0cmluZyIpLCAoNiwgdmFsdWVzLmdldCgibGljZW5zZV9pZCIpLCAic3RyaW5nIiksCiAgICAgICAgKDcsIHZhbHVlcy5nZXQoImFwcF92ZXJzaW9uIiksICJzdHJpbmciKSwgKDgsIHZhbHVlcy5nZXQoInNka192ZXJzaW9uX3N0ciIpLCAic3RyaW5nIiksCiAgICAgICAgKDksIHZhbHVlcy5nZXQoInNka192ZXJzaW9uIiksICJzaW50MzIiKSwgKDEwLCB2YWx1ZXMuZ2V0KCJ4Z19zZWVkX2J5dGVzIiksICJieXRlcyIpLAogICAgICAgICgxMiwgdmFsdWVzLmdldCgidGltZSIpLCAic2ludDMyIiksICgxMywgdmFsdWVzLmdldCgicXVlcnlfYm9keV90c19oYXNoIiksICJieXRlcyIpLAogICAgICAgICgxNCwgdmFsdWVzLmdldCgicXVlcnlfc20zIiksICJieXRlcyIpLCAoMTUsIF9lbmNvZGVfcmVxdWVzdCgpLCAibWVzc2FnZSIpLAogICAgICAgICgxNiwgdmFsdWVzLmdldCgic2VjX2RldmljZV90b2tlbiIpLCAic3RyaW5nIiksICgxNywgdmFsdWVzLmdldCgidGltZTIiKSwgInNpbnQzMiIpLAogICAgICAgICgxOCwgdmFsdWVzLmdldCgibGFudXNrX2hhc2giKSwgImJ5dGVzIiksICgxOSwgdmFsdWVzLmdldCgicXVlcnlfYm9keV9oYXNoX3NtMyIpLCAiYnl0ZXMiKSwKICAgICAgICAoMjAsIHZhbHVlcy5nZXQoInBza192ZXJzaW9uIiksICJzdHJpbmciKSwgKDIxLCB2YWx1ZXMuZ2V0KCJjYWxsX3R5cGUiKSwgInNpbnQzMiIpLAogICAgICAgICgyMywgX2VuY29kZV9lbnYodmFsdWVzLmdldCgiZW52Iikgb3Ige30pLCAibWVzc2FnZSIpLAogICAgICAgICgyNCwgdmFsdWVzLmdldCgidW5rbm93bjI0IiksICJzdHJpbmciKSwgKDI2LCB2YWx1ZXMuZ2V0KCJvcmlnaW5hbCIpLCAic3RyaW5nIiksCiAgICBdKQoKZGVmIF9qc29uX2JvZHlfbWQ1KGRhdGE6IEFueSwgZGF0YV90eXBlOiBzdHIgfCBOb25lID0gTm9uZSkgLT4gc3RyOgogICAgaWYgbm90IGRhdGE6CiAgICAgICAgcmV0dXJuICIiCiAgICBpZiBpc2luc3RhbmNlKGRhdGEsIHN0cik6CiAgICAgICAgcmF3ID0gZGF0YS5lbmNvZGUoInV0Zi04IikKICAgIGVsaWYgaXNpbnN0YW5jZShkYXRhLCBieXRlcyk6CiAgICAgICAgcmF3ID0gZGF0YQogICAgZWxpZiBkYXRhX3R5cGUgPT0gImFwcGxpY2F0aW9uL2pzb247IGNoYXJzZXQ9VVRGLTgiOgogICAgICAgIHJhdyA9IGpzb24uZHVtcHMoZGF0YSwgZW5zdXJlX2FzY2lpPUZhbHNlLCBzZXBhcmF0b3JzPSgiLCIsICI6IikpLmVuY29kZSgidXRmLTgiKQogICAgZWxzZToKICAgICAgICByYXcgPSB1cmxlbmNvZGUoZGF0YSkuZW5jb2RlKCJ1dGYtOCIpCiAgICByZXR1cm4gaGFzaGxpYi5tZDUocmF3KS5oZXhkaWdlc3QoKS51cHBlcigpCgpkZWYgX3VybF9lbmNvZGUodmFsdWU6IE1hcHBpbmdbc3RyLCBBbnldKSAtPiBzdHI6CiAgICByZXR1cm4gdXJsZW5jb2RlKHZhbHVlKS5yZXBsYWNlKCIrIiwgIiUyMCIpLnJlcGxhY2UoIiUyQSIsICIqIikKCmRlZiBfZ2V0X3BhcmFtc19lbmNyeXB0dXJsKHVybDogc3RyLCBwYXJhbXM6IE1hcHBpbmdbc3RyLCBBbnldLCBkZXZpY2VzOiBNYXBwaW5nW3N0ciwgQW55XSkgLT4gdHVwbGVbc3RyLCBkaWN0W3N0ciwgQW55XV06CiAgICByZXN1bHQgPSBkaWN0KHBhcmFtcykKICAgIGZvciBrZXksIHZhbHVlIGluIGRldmljZXMuaXRlbXMoKToKICAgICAgICBpZiBrZXkgaW4gcmVzdWx0OgogICAgICAgICAgICByZXN1bHRba2V5XSA9IHZhbHVlCiAgICAgICAgZWxpZiBrZXkgPT0gImRldmljZV9pZCIgYW5kICJkaWQiIGluIHJlc3VsdDoKICAgICAgICAgICAgcmVzdWx0WyJkaWQiXSA9IHZhbHVlCiAgICByZXN1bHRbInRzIl0gPSBpbnQodGltZS50aW1lKCkpCiAgICByZXN1bHRbIl9ydGlja2V0Il0gPSBpbnQodGltZS50aW1lKCkgKiAxMDAwKQogICAgcmV0dXJuIHVybC5zcGxpdCgiPyIsIDEpWzBdICsgIj8iICsgX3VybF9lbmNvZGUocmVzdWx0KSwgcmVzdWx0CgpkZWYgX3hnX3JjNChkYXRhOiBieXRlcywga2V5OiBieXRlcykgLT4gYnl0ZWFycmF5OgogICAgdGFibGUgPSBsaXN0KHJhbmdlKDI1NikpCiAgICBqID0gMAogICAgZm9yIGkgaW4gcmFuZ2UoMjU2KToKICAgICAgICBqID0gKGogKyB0YWJsZVtpXSArIGtleVtpICUgbGVuKGtleSldKSAlIDI1NgogICAgICAgIHRhYmxlW2ldID0gdGFibGVbal0KICAgIGkgPSBqID0gMAogICAgcmVzdWx0ID0gYnl0ZWFycmF5KGxlbihkYXRhKSkKICAgIGZvciBpbmRleCwgdmFsdWUgaW4gZW51bWVyYXRlKGRhdGEpOgogICAgICAgIGkgPSAoaSArIDEpICYgMHhGRgogICAgICAgIHggPSB0YWJsZVtpXQogICAgICAgIGogPSAoaiArIHgpICYgMHhGRgogICAgICAgIHkgPSB0YWJsZVtqXQogICAgICAgICMg5L+d5oyB5q2j5byP5Z+657q/55qEIFJDNCDlj5jkvZPvvJrov5nph4zlj6ropobnm5YgU1tpXe+8jOS4jeS6pOaNoiBTW2pd44CCCiAgICAgICAgdGFibGVbaV0gPSB5CiAgICAgICAgcmVzdWx0W2luZGV4XSA9IHZhbHVlIF4gdGFibGVbKHkgKyB5KSAmIDB4RkZdCiAgICByZXR1cm4gcmVzdWx0CgpkZWYgX3JldmVyc2VfYml0cyh2YWx1ZTogaW50KSAtPiBpbnQ6CiAgICByZXR1cm4gaW50KGYie3ZhbHVlOjA4Yn0iWzo6LTFdLCAyKQoKZGVmIF9lbmNyeXB0X2dvcmdvbihib2R5OiBBbnksIHF1ZXJ5OiBzdHIsIGtocm9ub3M6IGludCwgeGdfcmFuZDogaW50LCBkYXRhX3R5cGU6IHN0cikgLT4gc3RyOgogICAgYm9keV9tZDUgPSBfanNvbl9ib2R5X21kNShib2R5LCBkYXRhX3R5cGUpLmxvd2VyKCkgaWYgYm9keSBlbHNlICIiCiAgICBkYXRhID0gYnl0ZWFycmF5KGhhc2hsaWIubWQ1KHF1ZXJ5LmVuY29kZSgpKS5kaWdlc3QoKVs6NF0pCiAgICBkYXRhICs9IGJ5dGVzLmZyb21oZXgoYm9keV9tZDUpWzo0XSBpZiBib2R5X21kNSBlbHNlIGIiXDBcMFwwXDAiCiAgICBkYXRhICs9IGIiXDBcMFwwXDAiICsgKDY3NTAzMTA0KS50b19ieXRlcyg0LCAibGl0dGxlIikgKyBraHJvbm9zLnRvX2J5dGVzKDQsICJiaWciKQogICAga2V5ID0gYnl0ZXMoKDB4NEEsIDMyMCAmIDB4RkYsIDB4MTYsICh4Z19yYW5kID4+IDgpICYgMHhGRiwgMHg0NywgMHg2QywgMSwgeGdfcmFuZCAmIDB4RkYpKQogICAgcmVzdWx0ID0gX3hnX3JjNChkYXRhLCBrZXkpCiAgICBmb3IgaW5kZXgsIHZhbHVlIGluIGVudW1lcmF0ZShyZXN1bHQpOgogICAgICAgIHZhbHVlID0gKCh2YWx1ZSA+PiA0KSB8ICh2YWx1ZSA8PCA0KSkgJiAweEZGCiAgICAgICAgZm9sbG93aW5nID0gcmVzdWx0W2luZGV4ICsgMV0gaWYgaW5kZXggKyAxIDwgbGVuKHJlc3VsdCkgZWxzZSByZXN1bHRbMF0KICAgICAgICByZXN1bHRbaW5kZXhdID0gKH4oX3JldmVyc2VfYml0cyhmb2xsb3dpbmcgXiB2YWx1ZSkgXiAyMCkpICYgMHhGRgogICAgcmV0dXJuIChiIlx4ODRceDA0IiArIHhnX3JhbmQudG9fYnl0ZXMoMiwgImxpdHRsZSIpICsgKDMyMCkudG9fYnl0ZXMoMiwgImxpdHRsZSIpICsgcmVzdWx0KS5oZXgoKQoKZGVmIF9yb3I2NCh2YWx1ZTogaW50LCBjb3VudDogaW50KSAtPiBpbnQ6CiAgICBjb3VudCAlPSA2NAogICAgcmV0dXJuICgodmFsdWUgPj4gY291bnQpIHwgKHZhbHVlIDw8ICg2NCAtIGNvdW50KSkpICYgMHhGRkZGRkZGRkZGRkZGRkZGCgpkZWYgX2VuY3J5cHRfaGVsaW9zKGtocm9ub3M6IGludCwgcmFuZF92YWx1ZTogaW50ID0gMCkgLT4gc3RyOgogICAgdmFsdWUgPSByYW5kX3ZhbHVlIG9yIHJhbmRvbS5yYW5kaW50KDAsIDB4RkZGRkZGRkYpCiAgICBzZWVkID0gdmFsdWUudG9fYnl0ZXMoNCwgImxpdHRsZSIpICsgYiI4NjYyIgogICAgZGlnZXN0ID0gaGFzaGxpYi5tZDUoc2VlZCkuZGlnZXN0KCkKICAgIGtleXMgPSBiIiIuam9pbihmIntpdGVtOjAyeH0iLmVuY29kZSgpIGZvciBpdGVtIGluIGRpZ2VzdCkKICAgIHRhYmxlID0gW2ludC5mcm9tX2J5dGVzKGtleXNbOjhdLCAibGl0dGxlIildCiAgICB3b3JkcyA9IFtpbnQuZnJvbV9ieXRlcyhrZXlzW2k6aSArIDhdLCAibGl0dGxlIikgZm9yIGkgaW4gcmFuZ2UoMCwgMzIsIDgpXQogICAgZmlyc3QsIHNlY29uZCA9IHdvcmRzWzBdLCB3b3Jkc1sxXQogICAgd29yZHMgPSB3b3Jkc1syOl0KICAgIGZvciBpbmRleCBpbiByYW5nZSgweDIyKToKICAgICAgICB2YWx1ZTIgPSBfcm9yNjQoc2Vjb25kLCA4KQogICAgICAgIHZhbHVlMiA9ICh2YWx1ZTIgKyBmaXJzdCkgJiAweEZGRkZGRkZGRkZGRkZGRkYKICAgICAgICB2YWx1ZTIgPSAodmFsdWUyIF4gaW5kZXgpICYgMHhGRkZGRkZGRkZGRkZGRkZGCiAgICAgICAgd29yZHMuYXBwZW5kKHZhbHVlMikKICAgICAgICB2YWx1ZTIgXj0gX3JvcjY0KGZpcnN0LCA2MSkKICAgICAgICB2YWx1ZTIgJj0gMHhGRkZGRkZGRkZGRkZGRkZGCiAgICAgICAgdGFibGUuYXBwZW5kKHZhbHVlMikKICAgICAgICBmaXJzdCwgc2Vjb25kID0gdmFsdWUyLCB3b3Jkcy5wb3AoMCkKICAgIHJhdyA9IChmIntraHJvbm9zfS0xNTg4MDkzMjI4LTg2NjIiKS5lbmNvZGUoKQogICAgcGFkID0gMTYgLSBsZW4ocmF3KSAlIDE2CiAgICByYXcgKz0gYnl0ZXMoW3BhZF0pICogcGFkCiAgICBvdXRwdXQgPSBieXRlYXJyYXkoKQogICAgZm9yIG9mZnNldCBpbiByYW5nZSgwLCBsZW4ocmF3KSwgMTYpOgogICAgICAgIGxlZnQgPSBpbnQuZnJvbV9ieXRlcyhyYXdbb2Zmc2V0Om9mZnNldCArIDhdLCAibGl0dGxlIikKICAgICAgICByaWdodCA9IGludC5mcm9tX2J5dGVzKHJhd1tvZmZzZXQgKyA4Om9mZnNldCArIDE2XSwgImxpdHRsZSIpCiAgICAgICAgZm9yIGluZGV4IGluIHJhbmdlKDB4MjIpOgogICAgICAgICAgICByaWdodCA9ICh0YWJsZVtpbmRleF0gXiAobGVmdCArIF9yb3I2NChyaWdodCwgOCkpKSAmIDB4RkZGRkZGRkZGRkZGRkZGRgogICAgICAgICAgICBsZWZ0ID0gKHJpZ2h0IF4gX3JvcjY0KGxlZnQsIDYxKSkgJiAweEZGRkZGRkZGRkZGRkZGRkYKICAgICAgICBvdXRwdXQgKz0gbGVmdC50b19ieXRlcyg4LCAibGl0dGxlIikgKyByaWdodC50b19ieXRlcyg4LCAibGl0dGxlIikKICAgIHJldHVybiBiYXNlNjQuYjY0ZW5jb2RlKHZhbHVlLnRvX2J5dGVzKDQsICJsaXR0bGUiKSArIG91dHB1dCkuZGVjb2RlKCkKCmRlZiBfZ2VuX21lZHVzYV9wcm90byh1cmw6IHN0ciwgdXJsX3BhcmFtczogTWFwcGluZ1tzdHIsIEFueV0sIGRldmljZXM6IE1hcHBpbmdbc3RyLCBBbnldLCBkYXRhOiBBbnksIGtocm9ub3M6IGludCwgZGF0YV90eXBlOiBzdHIpIC0+IHR1cGxlW2J5dGVzLCBieXRlcywgYnl0ZXNdOgogICAgYm9keV9tZDUgPSBfanNvbl9ib2R5X21kNShkYXRhLCBkYXRhX3R5cGUpLmxvd2VyKCkgaWYgZGF0YSBlbHNlICIiCiAgICBib2R5X21kNV9ieXRlcyA9IGJ5dGVzLmZyb21oZXgoYm9keV9tZDUpIGlmIGJvZHlfbWQ1IGVsc2UgYnl0ZXMoMTYpCiAgICB0c19ieXRlcyA9IGtocm9ub3MudG9fYnl0ZXMoNCwgImxpdHRsZSIpCiAgICBxdWVyeSA9IHVybC5zcGxpdCgiPyIsIDEpWzFdIGlmICI/IiBpbiB1cmwgZWxzZSAiIgogICAgcXVlcnlfc20zID0gU00zKHF1ZXJ5KS5kaWdlc3QoKQogICAgcXVlcnlfYm9keV9oYXNoID0gU00zKHF1ZXJ5LmVuY29kZSgpICsgYm9keV9tZDVfYnl0ZXMgKyBiIm5vbmUiKS5kaWdlc3QoKQogICAgZGV2aWNlX2lkID0gc3RyKGRldmljZXMuZ2V0KCJkZXZpY2VfaWQiLCB1cmxfcGFyYW1zLmdldCgiZGV2aWNlX2lkIiwgdXJsX3BhcmFtcy5nZXQoImRpZCIsICIiKSkpKQogICAgdmVyc2lvbl9uYW1lID0gc3RyKGRldmljZXMuZ2V0KCJ2ZXJzaW9uX25hbWUiLCB1cmxfcGFyYW1zLmdldCgidmVyc2lvbl9uYW1lIiwgIjcuMS4zLjMyIikpKQogICAgZGV2aWNlX21vZGVsID0gc3RyKGRldmljZXMuZ2V0KCJkZXZpY2VfbW9kZWwiLCB1cmxfcGFyYW1zLmdldCgiZGV2aWNlX3R5cGUiLCAiIikpKQogICAgYnJhbmQgPSBzdHIoZGV2aWNlcy5nZXQoImRldmljZV9icmFuZCIsIHVybF9wYXJhbXMuZ2V0KCJkZXZpY2VfYnJhbmQiLCAiIikpKQogICAgc2VjX2RldmljZV90b2tlbiA9IHN0cihkZXZpY2VzLmdldCgic2VjX2RldmljZV90b2tlbiIpIG9yICIiKQogICAgZGV2aWNlX3NlY19kZXZpY2VfdG9rZW4gPSBzdHIoZGV2aWNlcy5nZXQoImRldmljZV9zZWNfZGV2aWNlX3Rva2VuIikgb3IgIiIpCiAgICBwcm90b19yYW5kID0gcmFuZG9tLnJhbmRpbnQoMCwgMHhGRkZGRkZGRikKICAgIGxhdW5jaF90aW1lID0gcmFuZG9tLnJhbmRpbnQoMTAwLCAxMjApCiAgICBwcm9jZXNzX2lkID0gcmFuZG9tLnJhbmRpbnQoMTAwMDEsIDEyMDAwKQogICAgIyDov5nkupvlrZfmrrXmmK/mraPlvI/nrb7lkI3lrp7njrDkuK3nmoTlm7rlrprnjq/looPph4fmoLflgLzvvIzkuI3mmK/nlKjmiLforr7lpIfmoIfor4bjgIIKICAgIHJlcG9ydF90cyA9IDE3MjgzODgwMTY2MzUKICAgIHJlcG9ydF90aW1lID0gaW50KHRpbWUudGltZSgpKQogICAgZGV2aWNlID0gewogICAgICAgICJkMSI6IDEsICJjb2xsZWN0X3N0YXQiOiAyLCAiYWlkIjogIjg2NjIiLCAiZGV2aWNlX2lkIjogZGV2aWNlX2lkLAogICAgICAgICJzZWNfZGV2aWNlX3Rva2VuIjogZGV2aWNlX3NlY19kZXZpY2VfdG9rZW4sCiAgICAgICAgImFwcF92ZXJzaW9uIjogIiFub3Blcm0hIiwgImJhdHRlcnkiOiAtODg4ODg4LCAiYmF0dGVyeTIiOiAtODg4ODg4LAogICAgICAgICJiYXR0ZXJ5X2hlYWx0aCI6IDMsICJiYXR0ZXJ5X2NoYW5nZWQiOiAtODg4ODg4LCAibmV0d29yayI6ICIhbm90c2V0ISIsCiAgICAgICAgInR6IjogIkFzaWEvU2hhbmdoYWksOCIsICJsYW4iOiAiemhfQ04iLCAiY3B1IjogNCwKICAgICAgICAic2RjYXJkIjogMjU1LjI0OTkzODk2NDg0Mzc1LCAic2RjYXJkX3VzZWQiOiAzNS41ODU5OTA5MDU3NjE3MiwKICAgICAgICAibWVtb3J5IjogMy40Njc0NDkxODgyMzI0MjIsICJtZW1vcnkyIjogMy40Njc0NDkxODgyMzI0MjIsCiAgICAgICAgImRhdGEiOiAyNTUuMTc1NDkxMzMzMDA3OCwgImRhdGFfdXNlZCI6IDQyLjE3NTQ0MTc0MTk0MzM2LAogICAgICAgICJvc192ZXJzaW9uIjogc3RyKGRldmljZXMuZ2V0KCJvc192ZXJzaW9uIiwgdXJsX3BhcmFtcy5nZXQoIm9zX3ZlcnNpb24iLCAiIikpKSwKICAgICAgICAiYnJpZ2h0bmVzcyI6IDQxLCAidm9sdW1lIjogMzYsICJ0cyI6IHJlcG9ydF90cywgInRzMiI6IHJlcG9ydF90cywKICAgICAgICAidHMzIjogcmVwb3J0X3RzLCAidHM0IjogcmVwb3J0X3RzICsgMiwgInVzYiI6IC0xLCAiaHdfdmVyc2lvbiI6IGRldmljZV9tb2RlbCwKICAgICAgICAiYnJhbmQiOiBicmFuZCwgImJvYXJkIjogZGV2aWNlX21vZGVsLCAicHJvZHVjdF9uYW1lIjogZGV2aWNlX21vZGVsLAogICAgICAgICJwcm9kdWN0X2RldmljZSI6IHN0cihkZXZpY2VzLmdldCgiZGV2aWNlX21hbnVmYWN0dXJlciIsIGJyYW5kKSksCiAgICAgICAgInByb2R1Y3RfbWFudWZhY3R1cmVyIjogYnJhbmQsICJoYXJkd2FyZSI6IGJyYW5kLCAidW5rbm93bjM4IjogMzEsCiAgICB9CiAgICBlbnYgPSB7CiAgICAgICAgImxhdW5jaF90aW1lIjogbGF1bmNoX3RpbWUsICJ1bmtub3duMiI6IDE0NjMzMTM5OSwKICAgICAgICAidW5rbm93bjMiOiAxNDYzMzEzOTYsICJ1bmtub3duNSI6IDcsICJ2ZXJzaW9uIjogInYwNC4wNi4wNC4wMy1idWdmaXgiLAogICAgICAgICJwaWQiOiBwcm9jZXNzX2lkLCAiZGV2aWNlIjogZGV2aWNlLAogICAgICAgICJyZXBvcnQiOiB7InRpbWUiOiByZXBvcnRfdGltZSwgInN0YXRlIjogLTIsICJjb2RlIjogMjAwLCAidGltZXMiOiAwLCAidW5rbm93bjYiOiAwfSwKICAgICAgICAiYXBwX3ZlcnNpb24iOiB2ZXJzaW9uX25hbWUsCiAgICB9CiAgICB2YWx1ZXMgPSB7CiAgICAgICAgIm1hZ2ljIjogYiJceGY3XHhlOF9ceGZhXHhkN1x4ZDdceGRjO1x4ZDYqXHhjOHBXXHhjZmFceDE4IiwKICAgICAgICAidmVyc2lvbiI6IDMsICJyYW5kIjogcHJvdG9fcmFuZCwgIm1zX2FwcF9pZCI6ICI4NjYyIiwKICAgICAgICAiZGV2aWNlX2lkIjogZGV2aWNlX2lkLCAibGljZW5zZV9pZCI6ICIxNTg4MDkzMjI4IiwgImFwcF92ZXJzaW9uIjogdmVyc2lvbl9uYW1lLAogICAgICAgICJzZGtfdmVyc2lvbl9zdHIiOiAidjA0LjA2LjA0LW1sLWFuZHJvaWQiLCAic2RrX3ZlcnNpb24iOiA2NzUwMzEwNCwKICAgICAgICAieGdfc2VlZF9ieXRlcyI6ICgzMjApLnRvX2J5dGVzKDgsICJsaXR0bGUiKSwgInRpbWUiOiBraHJvbm9zLAogICAgICAgICJxdWVyeV9ib2R5X3RzX2hhc2giOiBoYXNoX2YxMyhxdWVyeV9zbTMsIGJvZHlfbWQ1X2J5dGVzLCB0c19ieXRlcywga2hyb25vcyksCiAgICAgICAgInF1ZXJ5X3NtMyI6IHF1ZXJ5X3NtM1s6Nl0sICJzZWNfZGV2aWNlX3Rva2VuIjogc2VjX2RldmljZV90b2tlbiwgInRpbWUyIjoga2hyb25vcywKICAgICAgICAibGFudXNrX2hhc2giOiBiIiIsICJxdWVyeV9ib2R5X2hhc2hfc20zIjogcXVlcnlfYm9keV9oYXNoLCAicHNrX3ZlcnNpb24iOiAibm9uZSIsCiAgICAgICAgImNhbGxfdHlwZSI6IDMxMiwgImVudiI6IGVudiwKICAgICAgICAidW5rbm93bjI0IjogJ3siY21yIjoxNjc3NzIxNiwiY21yMiI6MTY3NzcyMTYsInVuX2giOjE4NzkxOTQwNDAsInZwbiI6MCwia2QiOjAsImZrZCI6MzY3MjUxODk3MiwicGQiOi0xODcyNTczMjQ3LCJkeW4iOiIiLCJkbyI6MCwidGsiOnRydWV9JywKICAgIH0KICAgIHJldHVybiBfZW5jb2RlX21lZHVzYSh2YWx1ZXMpLCBxdWVyeV9zbTMsIGhhc2hfZjEzKHF1ZXJ5X3NtMywgYm9keV9tZDVfYnl0ZXMsIHRzX2J5dGVzLCBraHJvbm9zKQoKZGVmIF94bXhvcl90d28oZGF0YTogYnl0ZXMsIGtleTogYnl0ZXMpIC0+IGJ5dGVhcnJheToKICAgIGVuY29kZWQgPSBieXRlYXJyYXkobGVuKGRhdGEpKQogICAgZm9yIGluZGV4LCB2YWx1ZSBpbiBlbnVtZXJhdGUoZGF0YSk6CiAgICAgICAgcG9zaXRpb24gPSAoaW5kZXggKiA0KSAmIDI4CiAgICAgICAgZDAsIGQxID0ga2V5W3Bvc2l0aW9uXSwga2V5W3Bvc2l0aW9uICsgMV0KICAgICAgICBkMiA9IChybDgodmFsdWUsIDQpICsgZDApIF4gZDEKICAgICAgICBkMiA9IHJsOCgofmQyKSAmIDB4RkYsIDMpCiAgICAgICAgZDIgPSAoKGQyICsgZDEpICYgMHhGRikgXiBkMAogICAgICAgIGVuY29kZWRbLWluZGV4IC0gMV0gPSAofmQyKSAmIDB4RkYKICAgIHJldHVybiBlbmNvZGVkCgpkZWYgX3hteG9yKGRhdGE6IGJ5dGVzLCBrZXk6IGJ5dGVzKSAtPiBieXRlYXJyYXk6CiAgICB2YWx1ZSA9IF94bXhvcl90d28oZGF0YSwga2V5KQogICAgbGFzdF9mbGFnID0gdmFsdWVbLTFdIF4gdmFsdWVbLTJdCiAgICBkYXRhMCA9IHZhbHVlWzBdCiAgICB2YWx1ZVswXSA9ICh+bGFzdF9mbGFnICsgdmFsdWVbMF0pICYgMHhGRgogICAgdmFsdWVbMV0gPSAoKHZhbHVlWzBdIF4gdmFsdWVbLTFdIF4gMjU0KSArIHZhbHVlWzFdKSAmIDB4RkYKICAgIHZhbHVlWzJdID0gKHZhbHVlWzJdICsgKChsYXN0X2ZsYWcgLSBkYXRhMCkgXiBybDgodmFsdWVbMV0sIDMpIF4gMikpICYgMHhGRgogICAgZm9yIGluZGV4IGluIHJhbmdlKGxlbih2YWx1ZSkgLSA0KToKICAgICAgICB0ZW1wID0gcmw4KHZhbHVlW2luZGV4ICsgMl0sIDMpIF4gdmFsdWVbaW5kZXggKyAxXSBeIChpbmRleCArIDMpCiAgICAgICAgdmFsdWVbaW5kZXggKyAzXSA9ICh+dGVtcCArIHZhbHVlW2luZGV4ICsgM10pICYgMHhGRgogICAgdmFsdWVbLTFdIF49IHZhbHVlWy0yXQogICAgdmFsdWVbMF0gPSAoKHZhbHVlWzBdIF4gdmFsdWVbMV0pICsgc3VtKHZhbHVlWzE6XSkpICYgMHhGRgogICAgcmV0dXJuIHZhbHVlCgpkZWYgX2dlbl9tZWR1c2EodXJsOiBzdHIsIHVybF9wYXJhbXM6IE1hcHBpbmdbc3RyLCBBbnldLCBkZXZpY2VzOiBNYXBwaW5nW3N0ciwgQW55XSwgZGF0YTogQW55LCBraHJvbm9zOiBpbnQsIGRhdGFfdHlwZTogc3RyKSAtPiBzdHI6CiAgICBjb25maWdfa2V5ID0gYiJceGYxWTN2dm5ceGE5XHg4ZDRceGYzXHgxYlx4MDV6XHg5ZFtceGU0IgogICAgY29uZmlnX2l2ID0gYiJceDFmXHhlMVx0XHhhNFx4MTJSXHg4M1x4ZjRceDE4XHhkZVx4OWVceDA1XHgxYVx4OTZceDllXHgxMiIKICAgIHNpZ25fa2V5ID0gYiJceDhlXHhiZFx4ZmE4XHgwNlx4ZWNceGM1XHhjZVx4ZTdceDk0I1x4ZTZceDAyXHg5ZVx4ZDglQFx4YmNcIlx4MThceGJiflx4YWVceGY3XHgxY1x4YjZceDkxXHhmN1x4YWFceDhhXHhhMlx4ZjUiCiAgICBwcm90bywgcXVlcnlfc20zLCBib2R5X3NtMyA9IF9nZW5fbWVkdXNhX3Byb3RvKHVybCwgdXJsX3BhcmFtcywgZGV2aWNlcywgZGF0YSwga2hyb25vcywgZGF0YV90eXBlKQogICAgaGFzaF9yYW5kID0gcmFuZG9tLnJhbmRpbnQoMCwgMHhGRkZGRkZGRikKICAgIHhtX3JhbmQgPSByYW5kb20ucmFuZGludCgwLCAweEZGRkZGRkZGKQogICAga2V5LCBzZWVkID0gZ2V0X2tleV9oYXNoKHNpZ25fa2V5LCBoYXNoX3JhbmQpCiAgICBtaXhlZCA9IF94bXhvcihwcm90bywga2V5KQogICAgbWl4ZWQgPSAoMzIwKS50b19ieXRlcyg4LCAibGl0dGxlIikgKyBtaXhlZAogICAgbWl4ZWQgPSBieXRlYXJyYXkobWl4ZWRbOjotMV0pCiAgICBmb3IgaW5kZXggaW4gcmFuZ2UobGVuKG1peGVkKSk6CiAgICAgICAgbWl4ZWRbaW5kZXhdIF49IHNlZWRbfmluZGV4ICYgM10KICAgIGhhc2hfYnl0ZXMgPSBoYXNoX3JhbmQudG9fYnl0ZXMoNCwgImxpdHRsZSIpCiAgICBjaGVja19iaXQgPSAoKHF1ZXJ5X3NtM1swXSAmIDYzKSA8PCAxNCkgfCAweDE4MDAwMDAxIHwgKChib2R5X3NtM1swXSAmIDYzKSA8PCA4KQogICAgbWl4ZWQgPSBiIlx4MzUiICsgeG1fcmFuZC50b19ieXRlcyg0LCAibGl0dGxlIikgKyBjaGVja19iaXQudG9fYnl0ZXMoNCwgImxpdHRsZSIpICsgbWl4ZWQgKyBoYXNoX2J5dGVzWzI6XQogICAgbWl4ZWQgPSBBRVNfVjMoY29uZmlnX2tleSwga2hyb25vcykuZW5jcnlwdChtaXhlZCwgY29uZmlnX2l2KQogICAgdmVyc2lvbiA9IGJ5dGVzLmZyb21oZXgoIjAzIDAwIDAwIDAwIGY3IGU4IDVmIGZhIGQ3IGQ3IGRjIDNiIGQ2IDJhIGM4IDcwIDU3IGNmIDYxIDE4IikKICAgIHZlcnNpb25fb3IgPSBiIiIuam9pbigoaW50LmZyb21fYnl0ZXModmVyc2lvbltpOmkgKyA0XSwgImxpdHRsZSIpIF4ga2hyb25vcykudG9fYnl0ZXMoNCwgImxpdHRsZSIpIGZvciBpIGluIHJhbmdlKDAsIDIwLCA0KSkKICAgIHJldHVybiBiYXNlNjQuYjY0ZW5jb2RlKHZlcnNpb25fb3IgKyBoYXNoX2J5dGVzWzoyXSArICgyNTYpLnRvX2J5dGVzKDIsICJsaXR0bGUiKSArIG1peGVkKS5kZWNvZGUoKQoKZGVmIF9jb3JlX3NpeGdvZCh1cmw6IHN0ciwgcGFyYW1zOiBNYXBwaW5nW3N0ciwgQW55XSwgZGV2aWNlczogTWFwcGluZ1tzdHIsIEFueV0sIGRhdGE6IEFueSwgaGVhZGVyOiBNYXBwaW5nW3N0ciwgQW55XSkgLT4gdHVwbGVbZGljdFtzdHIsIHN0cl0sIHN0cl06CiAgICBkYXRhX3R5cGUgPSBzdHIoaGVhZGVyLmdldCgiY29udGVudC10eXBlIiwgaGVhZGVyLmdldCgiQ29udGVudC1UeXBlIiwgIiIpKSkKICAgIHhnX3JhbmQgPSByYW5kb20ucmFuZGludCgwLCAweEZGRkYpCiAgICBlbmNyeXB0ZWRfdXJsLCB1cmxfcGFyYW1zID0gX2dldF9wYXJhbXNfZW5jcnlwdHVybCh1cmwsIHBhcmFtcywgZGV2aWNlcykKICAgIGtocm9ub3MgPSBpbnQodGltZS50aW1lKCkpCiAgICBlbmNvZGVkX3F1ZXJ5ID0gX3VybF9lbmNvZGUodXJsX3BhcmFtcykKICAgIHZhbHVlcyA9IHsKICAgICAgICAia2hyb25vcyI6IHN0cihraHJvbm9zKSwKICAgICAgICAibGFkb24iOiBiYXNlNjQuYjY0ZW5jb2RlKGtocm9ub3MudG9fYnl0ZXMoNCwgImJpZyIpKS5kZWNvZGUoKSwKICAgICAgICAiYXJndXMiOiBiYXNlNjQuYjY0ZW5jb2RlKGtocm9ub3MudG9fYnl0ZXMoNCwgImxpdHRsZSIpKS5kZWNvZGUoKSwKICAgICAgICAiZ29yZ29uIjogX2VuY3J5cHRfZ29yZ29uKGRhdGEsIGVuY29kZWRfcXVlcnksIGtocm9ub3MsIHhnX3JhbmQsIGRhdGFfdHlwZSksCiAgICAgICAgImhlbGlvcyI6IF9lbmNyeXB0X2hlbGlvcyhraHJvbm9zLCAwKSwKICAgICAgICAibWVkdXNhIjogX2dlbl9tZWR1c2EoZW5jcnlwdGVkX3VybCwgdXJsX3BhcmFtcywgZGV2aWNlcywgZGF0YSwga2hyb25vcywgZGF0YV90eXBlKSwKICAgIH0KICAgIHNpZ25zID0gewogICAgICAgICJ4LWxhZG9uIjogdmFsdWVzWyJsYWRvbiJdLCAieC1raHJvbm9zIjogdmFsdWVzWyJraHJvbm9zIl0sCiAgICAgICAgIngtYXJndXMiOiB2YWx1ZXNbImFyZ3VzIl0sICJ4LWdvcmdvbiI6IHZhbHVlc1siZ29yZ29uIl0sCiAgICAgICAgIngtaGVsaW9zIjogdmFsdWVzWyJoZWxpb3MiXSwgIngtbWVkdXNhIjogdmFsdWVzWyJtZWR1c2EiXSwKICAgIH0KICAgIGlmIGRhdGE6CiAgICAgICAgc2lnbnNbIngtc3Mtc3R1YiJdID0gX2pzb25fYm9keV9tZDUoZGF0YSwgZGF0YV90eXBlKQogICAgcmVzdWx0X2hlYWRlcnMgPSB7c3RyKGtleSkubG93ZXIoKTogc3RyKHZhbHVlKSBmb3Iga2V5LCB2YWx1ZSBpbiBoZWFkZXIuaXRlbXMoKX0KICAgIHJlc3VsdF9oZWFkZXJzLnVwZGF0ZShzaWducykKICAgIGlmIGRldmljZXMuZ2V0KCJ1YSIpOgogICAgICAgIHJlc3VsdF9oZWFkZXJzWyJ1c2VyLWFnZW50Il0gPSBzdHIoZGV2aWNlc1sidWEiXSkKICAgIHJlc3VsdF9oZWFkZXJzWyJ4LXR0LWR0Il0gPSBzdHIoZGV2aWNlcy5nZXQoInhfdHRfZHQiLCAiIikpCiAgICByZXR1cm4gcmVzdWx0X2hlYWRlcnMsIGVuY3J5cHRlZF91cmwKCiMgLS0tLS0tLS0tLS0tLS0tLSDorr7lpIfova7mjaIgLS0tLS0tLS0tLS0tLS0tLQojIOe6ouaenOeahOWPlua1geaOpeWPo+aMieiuvuWkh+mZkOa1ge+8muWQjOS4gOWPsOiuvuWkh+aIkOWKn+WPlui/h+S4gOasoea1geWQju+8jOWGjeWPlu+8iOWTquaAleaNoumbhuOAgeaNoua4heaZsOW6pu+8iQojIOi/lOWbnueahCB2aWRlb19saXN0IOWwseaYr+epuueahOOAguaJgOS7peavj+aSreS4gOmbhuW/hemhu+aNouS4gOWPsOW5suWHgOiuvuWkh++8jOWksei0peiHquWKqOaNouS4i+S4gOWPsOmHjeivleOAggpfREVWX1JPVF9MT0NLID0gdGhyZWFkaW5nLkxvY2soKQpfREVWX1JPVF9VU0VEOiBzZXQgPSBzZXQoKQoKCmRlZiBfcmFuZF9kZXZpY2UoKSAtPiB0dXBsZVtzdHIsIHN0cl06CiAgICByZXR1cm4gKHN0cihyYW5kb20ucmFuZGludCgxMCAqKiAxNywgMTAgKiogMTggLSAxKSksCiAgICAgICAgICAgIHN0cihyYW5kb20ucmFuZGludCgxMCAqKiAxNywgMTAgKiogMTggLSAxKSkpCgoKZGVmIF9uZXdfZGV2aWNlX3BhaXIoYXZvaWQ9KCkpIC0+IHR1cGxlW3N0ciwgc3RyXToKICAgICIiIueUn+aIkOS4gOWvueayoeeUqOi/h+eahCBkZXZpY2VfaWQvaW5zdGFsbF9pZOOAgiIiIgogICAgc2tpcCA9IHNldCgpCiAgICBmb3IgaXRlbSBpbiBhdm9pZDoKICAgICAgICBpdGVtID0gX3RleHQoaXRlbSkKICAgICAgICBpZiBpdGVtOgogICAgICAgICAgICBza2lwLmFkZChpdGVtKQogICAgd2l0aCBfREVWX1JPVF9MT0NLOgogICAgICAgIGZvciBfIGluIHJhbmdlKDIwMCk6CiAgICAgICAgICAgIGRpZCwgaWlkID0gX3JhbmRfZGV2aWNlKCkKICAgICAgICAgICAgaWYgZGlkIGluIF9ERVZfUk9UX1VTRUQgb3IgaWlkIGluIF9ERVZfUk9UX1VTRUQ6CiAgICAgICAgICAgICAgICBjb250aW51ZQogICAgICAgICAgICBpZiBkaWQgaW4gc2tpcCBvciBpaWQgaW4gc2tpcDoKICAgICAgICAgICAgICAgIGNvbnRpbnVlCiAgICAgICAgICAgIF9ERVZfUk9UX1VTRUQuYWRkKGRpZCkKICAgICAgICAgICAgX0RFVl9ST1RfVVNFRC5hZGQoaWlkKQogICAgICAgICAgICBpZiBsZW4oX0RFVl9ST1RfVVNFRCkgPiA4MDAwOgogICAgICAgICAgICAgICAgX0RFVl9ST1RfVVNFRC5jbGVhcigpCiAgICAgICAgICAgICAgICBfREVWX1JPVF9VU0VELmFkZChkaWQpCiAgICAgICAgICAgICAgICBfREVWX1JPVF9VU0VELmFkZChpaWQpCiAgICAgICAgICAgIHJldHVybiBkaWQsIGlpZAogICAgcmV0dXJuIF9yYW5kX2RldmljZSgpCgoKZGVmIF9kZXZpY2VfY2FuZGlkYXRlcyhwYXJhbTogTWFwcGluZ1tzdHIsIEFueV0gfCBOb25lLCBjb3VudDogaW50ID0gMykgLT4gbGlzdDoKICAgICIiIuWAmemAieiuvuWkh+WIl+ihqO+8muWFiOeUqOS8oOWFpeeahO+8iFVSTC/lo7PluKbnmoTvvInvvIzlho3ov73liqDoi6XlubLlhajmlrDorr7lpIfjgIIiIiIKICAgIHAgPSBwYXJhbSBvciB7fQogICAgZGlkID0gX3RleHQocC5nZXQoImRpZCIpIG9yIHAuZ2V0KCJkZXZpY2VfaWQiKSBvciBwLmdldCgiZGV2aWNlSWQiKSkKICAgIGlpZCA9IF90ZXh0KHAuZ2V0KCJpaWQiKSBvciBwLmdldCgiaW5zdGFsbF9pZCIpIG9yIHAuZ2V0KCJpbnN0YWxsSWQiKSkKICAgIG91dDogbGlzdCA9IFtdCiAgICBzZWVuOiBzZXQgPSBzZXQoKQogICAgaWYgZGlkIGFuZCBpaWQ6CiAgICAgICAgb3V0LmFwcGVuZCgoZGlkLCBpaWQpKQogICAgICAgIHNlZW4uYWRkKGRpZCkKICAgICAgICBzZWVuLmFkZChpaWQpCiAgICAgICAgd2l0aCBfREVWX1JPVF9MT0NLOgogICAgICAgICAgICBfREVWX1JPVF9VU0VELmFkZChkaWQpCiAgICAgICAgICAgIF9ERVZfUk9UX1VTRUQuYWRkKGlpZCkKICAgIGZvciBfIGluIHJhbmdlKG1heCgxLCBpbnQoY291bnQpKSk6CiAgICAgICAgcGFpciA9IF9uZXdfZGV2aWNlX3BhaXIoYXZvaWQ9c2VlbikKICAgICAgICBzZWVuLmFkZChwYWlyWzBdKQogICAgICAgIHNlZW4uYWRkKHBhaXJbMV0pCiAgICAgICAgb3V0LmFwcGVuZChwYWlyKQogICAgcmV0dXJuIG91dAoKCmRlZiBfZGV2aWNlX2NvbmZpZyhjb25maWc6IE1hcHBpbmdbc3RyLCBBbnldKSAtPiBkaWN0W3N0ciwgc3RyXToKICAgIGRldmljZV9pZCA9IF90ZXh0KGNvbmZpZy5nZXQoImRldmljZV9pZCIpKQogICAgaW5zdGFsbF9pZCA9IF90ZXh0KGNvbmZpZy5nZXQoImluc3RhbGxfaWQiKSkKICAgIGlmIG5vdCBkZXZpY2VfaWQgb3Igbm90IGluc3RhbGxfaWQ6CiAgICAgICAgcmFpc2UgSG9uZ2d1b1BsdWdpbkVycm9yKCLnvLrlsJHnuqLmnpwgZGV2aWNlX2lkL2luc3RhbGxfaWQg6YWN572uIikKICAgIHJldHVybiB7CiAgICAgICAgImRldmljZV9pZCI6IGRldmljZV9pZCwgImlpZCI6IGluc3RhbGxfaWQsICJpbnN0YWxsX2lkIjogaW5zdGFsbF9pZCwKICAgICAgICAiZGV2aWNlX2JyYW5kIjogIlJlZG1pIiwgImRldmljZV9tb2RlbCI6ICIyNTA1M1JUNDdDIiwgImRldmljZV90eXBlIjogIjI1MDUzUlQ0N0MiLAogICAgICAgICJkZXZpY2VfbWFudWZhY3R1cmVyIjogIlhpYW9taSIsICJvc192ZXJzaW9uIjogIjE2IiwgInZlcnNpb25fbmFtZSI6ICI3LjEuMy4zMiIsCiAgICAgICAgInhfdHRfZHQiOiBfdGV4dChjb25maWcuZ2V0KCJ4X3R0X2R0IikpLAogICAgICAgICJzZWNfZGV2aWNlX3Rva2VuIjogX3RleHQoY29uZmlnLmdldCgic2VjX2RldmljZV90b2tlbiIpKSwKICAgICAgICAiZGV2aWNlX3NlY19kZXZpY2VfdG9rZW4iOiBfdGV4dChjb25maWcuZ2V0KCJkZXZpY2Vfc2VjX2RldmljZV90b2tlbiIpKSwKICAgICAgICAidWEiOiBBUFBfVUEsCiAgICB9CgpkZWYgX3ZpZGVvX21vZGVsKHZpZGVvX2lkOiBzdHIsIGNvbmZpZzogTWFwcGluZ1tzdHIsIEFueV0pIC0+IGRpY3Rbc3RyLCBBbnldOgogICAgZGV2aWNlcyA9IF9kZXZpY2VfY29uZmlnKGNvbmZpZykKICAgIHBhcmFtcyA9IHsKICAgICAgICAiaWlkIjogZGV2aWNlc1siaW5zdGFsbF9pZCJdLAogICAgICAgICJkZXZpY2VfaWQiOiBkZXZpY2VzWyJkZXZpY2VfaWQiXSwKICAgICAgICAiYWMiOiAid2lmaSIsCiAgICAgICAgImNoYW5uZWwiOiAidXBkYXRlXzY0IiwKICAgICAgICAiYWlkIjogIjg2NjIiLAogICAgICAgICJhcHBfbmFtZSI6ICJub3ZlbHJlYWQiLAogICAgICAgICJ2ZXJzaW9uX2NvZGUiOiAiNzEzMzIiLAogICAgICAgICJ2ZXJzaW9uX25hbWUiOiAiNy4xLjMuMzIiLAogICAgICAgICJkZXZpY2VfcGxhdGZvcm0iOiAiYW5kcm9pZCIsCiAgICAgICAgIm9zIjogImFuZHJvaWQiLAogICAgICAgICJzc21peCI6ICJhIiwKICAgICAgICAiZGV2aWNlX3R5cGUiOiAiMjUwNTNSVDQ3QyIsCiAgICAgICAgImRldmljZV9icmFuZCI6ICJSZWRtaSIsCiAgICAgICAgImxhbmd1YWdlIjogInpoIiwKICAgICAgICAib3NfYXBpIjogIjM2IiwKICAgICAgICAib3NfdmVyc2lvbiI6ICIxNiIsCiAgICAgICAgIm1hbmlmZXN0X3ZlcnNpb25fY29kZSI6ICI3MTMzMiIsCiAgICAgICAgInJlc29sdXRpb24iOiAiMTI4MCoyNzcyIiwKICAgICAgICAiZHBpIjogIjUyMCIsCiAgICAgICAgInVwZGF0ZV92ZXJzaW9uX2NvZGUiOiAiNzEzMzIiLAogICAgICAgICJob3N0X2FiaSI6ICJhcm02NC12OGEiLAogICAgICAgICJkcmFnb25fZGV2aWNlX3R5cGUiOiAicGhvbmUiLAogICAgICAgICJwdl9wbGF5ZXIiOiAiNzEzMzIiLAogICAgICAgICJjb21wbGlhbmNlX3N0YXR1cyI6ICIwIiwKICAgICAgICAibmVlZF9wZXJzb25hbF9yZWNvbW1lbmQiOiAiMSIsCiAgICAgICAgInBsYXllcl9zb19sb2FkIjogIjEiLAogICAgICAgICJpc19hbmRyb2lkX3BhZF9zY3JlZW4iOiAiMCIsCiAgICB9CiAgICBwYXlsb2FkID0gewogICAgICAgICJiaXpfcGFyYW0iOiB7CiAgICAgICAgICAgICJkZXRhaWxfcGFnZV92ZXJzaW9uIjogMCwKICAgICAgICAgICAgImRldmljZV9sZXZlbCI6IDMsCiAgICAgICAgICAgICJkaXNhYmxlX2RpZ2dfc3RhdCI6IEZhbHNlLAogICAgICAgICAgICAibmVlZF9hbGxfdmlkZW9fZGVmaW5pdGlvbiI6IFRydWUsCiAgICAgICAgICAgICJuZWVkX21wNF9hbGlnbiI6IEZhbHNlLAogICAgICAgICAgICAidXNlX29zX3BsYXllciI6IEZhbHNlLAogICAgICAgICAgICAidXNlX3NlcnZlcl9kbnMiOiBGYWxzZSwKICAgICAgICAgICAgInZpZGVvX3BsYXRmb3JtIjogMTAyNCwKICAgICAgICB9LAogICAgICAgICJtaXhlZF92aWRlb19pZF9tYXAiOiB7IjEwMDQiOiBbdmlkZW9faWRdfSwKICAgIH0KICAgIHJlcXVlc3RfaGVhZGVycyA9IHsKICAgICAgICAiVXNlci1BZ2VudCI6IEFQUF9VQSwKICAgICAgICAiQWNjZXB0IjogImFwcGxpY2F0aW9uL2pzb247IGNoYXJzZXQ9dXRmLTgsYXBwbGljYXRpb24veC1wcm90b2J1ZiIsCiAgICAgICAgIkNvbnRlbnQtVHlwZSI6ICJhcHBsaWNhdGlvbi9qc29uOyBjaGFyc2V0PVVURi04IiwKICAgICAgICAieC14cy1mcm9tLXdlYiI6ICIwIiwKICAgICAgICAieC1zcy1yZXEtdGlja2V0Ijogc3RyKGludCh0aW1lLnRpbWUoKSAqIDEwMDApKSwKICAgICAgICAieC10dC1yZXF1ZXN0LXRhZyI6ICJ0PTA7bj0wIiwKICAgICAgICAic2RrLXZlcnNpb24iOiAiMiIsCiAgICAgICAgInBhc3Nwb3J0LXNkay12ZXJzaW9uIjogIjUwNTYxIiwKICAgICAgICAieC12Yy1iZHR1cmluZy1zZGstdmVyc2lvbiI6ICIzLjcuMi5jbiIsCiAgICB9CiAgICBpZiBkZXZpY2VzLmdldCgiY29va2llIik6CiAgICAgICAgcmVxdWVzdF9oZWFkZXJzWyJDb29raWUiXSA9IGRldmljZXNbImNvb2tpZSJdCiAgICBzaWduZWRfaGVhZGVycywgc2lnbmVkX3VybCA9IF9jb3JlX3NpeGdvZCgKICAgICAgICBWSURFT19VUkwsCiAgICAgICAgcGFyYW1zLAogICAgICAgIGRldmljZXMsCiAgICAgICAgcGF5bG9hZCwKICAgICAgICByZXF1ZXN0X2hlYWRlcnMsCiAgICApCiAgICBib2R5ID0ganNvbi5kdW1wcyhwYXlsb2FkLCBlbnN1cmVfYXNjaWk9RmFsc2UsIHNlcGFyYXRvcnM9KCIsIiwgIjoiKSkuZW5jb2RlKCJ1dGYtOCIpCiAgICByZXNwb25zZSA9IHJlcXVlc3RzLnBvc3QoCiAgICAgICAgc2lnbmVkX3VybCwKICAgICAgICBoZWFkZXJzPXNpZ25lZF9oZWFkZXJzLAogICAgICAgIGRhdGE9Ym9keSwKICAgICAgICB0aW1lb3V0PTMwLAogICAgKQogICAgcmVzcG9uc2VfZGF0YSA9IF9qc29uX3Jlc3BvbnNlKHJlc3BvbnNlKQogICAgZGF0YSA9IHJlc3BvbnNlX2RhdGEuZ2V0KCJkYXRhIikgb3Ige30KICAgIGlmIG5vdCBpc2luc3RhbmNlKGRhdGEsIE1hcHBpbmcpOgogICAgICAgIHJhaXNlIEhvbmdndW9QbHVnaW5FcnJvcigidmlkZW9fbW9kZWwg5pWw5o2u5Li656m6IikKICAgIGVudHJ5OiBBbnkgPSBkYXRhLmdldCh2aWRlb19pZCkKICAgIGlmIGVudHJ5IGlzIE5vbmU6CiAgICAgICAgZm9yIHZhbHVlIGluIGRhdGEudmFsdWVzKCk6CiAgICAgICAgICAgIGlmIGlzaW5zdGFuY2UodmFsdWUsIE1hcHBpbmcpOgogICAgICAgICAgICAgICAgZW50cnkgPSB2YWx1ZQogICAgICAgICAgICAgICAgYnJlYWsKICAgICAgICAgICAgaWYgaXNpbnN0YW5jZSh2YWx1ZSwgbGlzdCkgYW5kIHZhbHVlIGFuZCBpc2luc3RhbmNlKHZhbHVlWzBdLCBNYXBwaW5nKToKICAgICAgICAgICAgICAgIGVudHJ5ID0gdmFsdWVbMF0KICAgICAgICAgICAgICAgIGJyZWFrCiAgICBpZiBub3QgaXNpbnN0YW5jZShlbnRyeSwgTWFwcGluZyk6CiAgICAgICAgZW50cnkgPSBkYXRhCiAgICByYXdfbW9kZWwgPSBlbnRyeS5nZXQoInZpZGVvX21vZGVsIikgaWYgaXNpbnN0YW5jZShlbnRyeSwgTWFwcGluZykgZWxzZSBOb25lCiAgICBpZiByYXdfbW9kZWwgaXMgTm9uZToKICAgICAgICByYXdfbW9kZWwgPSBkYXRhLmdldCgidmlkZW9fbW9kZWwiKQogICAgaWYgaXNpbnN0YW5jZShyYXdfbW9kZWwsIHN0cik6CiAgICAgICAgdHJ5OgogICAgICAgICAgICByYXdfbW9kZWwgPSBqc29uLmxvYWRzKHJhd19tb2RlbCkKICAgICAgICBleGNlcHQgVmFsdWVFcnJvciBhcyBleGM6CiAgICAgICAgICAgIHJhaXNlIEhvbmdndW9QbHVnaW5FcnJvcigidmlkZW9fbW9kZWwgSlNPTiDml6DmlYgiKSBmcm9tIGV4YwogICAgaWYgbm90IGlzaW5zdGFuY2UocmF3X21vZGVsLCBNYXBwaW5nKToKICAgICAgICByYWlzZSBIb25nZ3VvUGx1Z2luRXJyb3IoInZpZGVvX21vZGVsIOS4uuepuiIpCiAgICByZXR1cm4gZGljdChyYXdfbW9kZWwpCgpkZWYgX3ZpZGVvX2xpc3RfZnJvbV9tb2RlbChtb2RlbDogTWFwcGluZ1tzdHIsIEFueV0pIC0+IEFueToKICAgIGZvciBrZXkgaW4gKCJ2aWRlb19saXN0IiwgImR5bmFtaWNfdmlkZW9fbGlzdCIpOgogICAgICAgIGlmIG1vZGVsLmdldChrZXkpIGlzIG5vdCBOb25lOgogICAgICAgICAgICByZXR1cm4gbW9kZWxba2V5XQogICAgZHluYW1pYyA9IG1vZGVsLmdldCgiZHluYW1pY192aWRlbyIpCiAgICBpZiBpc2luc3RhbmNlKGR5bmFtaWMsIE1hcHBpbmcpOgogICAgICAgIGZvciBrZXkgaW4gKCJkeW5hbWljX3ZpZGVvX2xpc3QiLCAidmlkZW9fbGlzdCIsICJsaXN0Iik6CiAgICAgICAgICAgIGlmIGR5bmFtaWMuZ2V0KGtleSkgaXMgbm90IE5vbmU6CiAgICAgICAgICAgICAgICByZXR1cm4gZHluYW1pY1trZXldCiAgICB2aWRlb19pbmZvID0gbW9kZWwuZ2V0KCJ2aWRlb19pbmZvIikKICAgIGlmIGlzaW5zdGFuY2UodmlkZW9faW5mbywgTWFwcGluZyk6CiAgICAgICAgZGF0YSA9IHZpZGVvX2luZm8uZ2V0KCJkYXRhIikKICAgICAgICBpZiBpc2luc3RhbmNlKGRhdGEsIE1hcHBpbmcpOgogICAgICAgICAgICByZXR1cm4gX3ZpZGVvX2xpc3RfZnJvbV9tb2RlbChkYXRhKQogICAgZGF0YSA9IG1vZGVsLmdldCgiZGF0YSIpCiAgICBpZiBpc2luc3RhbmNlKGRhdGEsIE1hcHBpbmcpOgogICAgICAgIHJldHVybiBfdmlkZW9fbGlzdF9mcm9tX21vZGVsKGRhdGEpCiAgICByZXR1cm4gTm9uZQoKCl9RVUFMSVRZX09SREVSID0gKCIyMTYwIiwgIjE0NDAiLCAiMTA4MCIsICI3MjAiLCAiNTc2IiwgIjU0MCIsICI0ODAiLCAiMzYwIikKCmRlZiBfaW50KHZhbHVlOiBBbnkpIC0+IGludDoKICAgIG1hdGNoID0gcmUuc2VhcmNoKHIiXGQrIiwgX3RleHQodmFsdWUpKQogICAgcmV0dXJuIGludChtYXRjaC5ncm91cCgpKSBpZiBtYXRjaCBlbHNlIDAKCmRlZiBfcXVhbGl0eSh2YWx1ZTogQW55KSAtPiBzdHI6CiAgICB0ZXh0ID0gX3RleHQodmFsdWUpLmxvd2VyKCkKICAgIG1hdGNoID0gcmUuc2VhcmNoKHIiKDIxNjB8MTQ0MHwxMDgwfDcyMHw1NzZ8NTQwfDQ4MHwzNjApIiwgdGV4dCkKICAgIHJldHVybiBtYXRjaC5ncm91cCgxKSBpZiBtYXRjaCBlbHNlICIxMDgwIgoKZGVmIF9zZWxlY3RfcXVhbGl0eSh2aWRlb19saXN0OiBBbnksIHdhbnRlZDogc3RyID0gIjEwODAiKSAtPiB0dXBsZVtzdHIsIGRpY3Rbc3RyLCBBbnldXToKICAgIGRlZiByb3dzX2Zyb20odmFsdWU6IEFueSwgaGludGVkX3F1YWxpdHk6IHN0ciA9ICIiKSAtPiBsaXN0W3R1cGxlW3N0ciwgZGljdFtzdHIsIEFueV1dXToKICAgICAgICBpZiBpc2luc3RhbmNlKHZhbHVlLCBsaXN0KToKICAgICAgICAgICAgcmVzdWx0OiBsaXN0W3R1cGxlW3N0ciwgZGljdFtzdHIsIEFueV1dXSA9IFtdCiAgICAgICAgICAgIGZvciBpdGVtIGluIHZhbHVlOgogICAgICAgICAgICAgICAgcmVzdWx0LmV4dGVuZChyb3dzX2Zyb20oaXRlbSwgaGludGVkX3F1YWxpdHkpKQogICAgICAgICAgICByZXR1cm4gcmVzdWx0CiAgICAgICAgaWYgbm90IGlzaW5zdGFuY2UodmFsdWUsIE1hcHBpbmcpOgogICAgICAgICAgICByZXR1cm4gW10KICAgICAgICBpZiBhbnkoCiAgICAgICAgICAgIGtleSBpbiB2YWx1ZQogICAgICAgICAgICBmb3Iga2V5IGluICgKICAgICAgICAgICAgICAgICJtYWluX3VybCIsCiAgICAgICAgICAgICAgICAiYmFja3VwX3VybCIsCiAgICAgICAgICAgICAgICAiYmFja3VwX3VybF8xIiwKICAgICAgICAgICAgICAgICJwbGF5X2FkZHIiLAogICAgICAgICAgICAgICAgInNwYWRlX2EiLAogICAgICAgICAgICAgICAgImVuY3J5cHRfaW5mbyIsCiAgICAgICAgICAgICkKICAgICAgICApOgogICAgICAgICAgICByZXR1cm4gWyhoaW50ZWRfcXVhbGl0eSwgZGljdCh2YWx1ZSkpXQogICAgICAgIHJlc3VsdCA9IFtdCiAgICAgICAgZm9yIGtleSwgaXRlbSBpbiB2YWx1ZS5pdGVtcygpOgogICAgICAgICAgICBpZiBrZXkgaW4geyJkeW5hbWljX3ZpZGVvIiwgInZpZGVvX2luZm8iLCAiZGF0YSJ9IGFuZCBpc2luc3RhbmNlKGl0ZW0sIE1hcHBpbmcpOgogICAgICAgICAgICAgICAgcmVzdWx0LmV4dGVuZChyb3dzX2Zyb20oaXRlbSwgaGludGVkX3F1YWxpdHkpKQogICAgICAgICAgICAgICAgY29udGludWUKICAgICAgICAgICAgaWYga2V5IGluIHsidmlkZW9fbGlzdCIsICJkeW5hbWljX3ZpZGVvX2xpc3QiLCAibGlzdCJ9OgogICAgICAgICAgICAgICAgcmVzdWx0LmV4dGVuZChyb3dzX2Zyb20oaXRlbSwgX3F1YWxpdHkoa2V5KSkpCiAgICAgICAgICAgICAgICBjb250aW51ZQogICAgICAgICAgICBpZiBpc2luc3RhbmNlKGl0ZW0sIChNYXBwaW5nLCBsaXN0KSk6CiAgICAgICAgICAgICAgICByZXN1bHQuZXh0ZW5kKHJvd3NfZnJvbShpdGVtLCBfcXVhbGl0eShrZXkpKSkKICAgICAgICByZXR1cm4gcmVzdWx0CgogICAgY2FuZGlkYXRlcyA9IHJvd3NfZnJvbSh2aWRlb19saXN0KQogICAgcm93czogZGljdFtzdHIsIGRpY3Rbc3RyLCBBbnldXSA9IHt9CiAgICBmb3IgaGludGVkX3F1YWxpdHksIGl0ZW0gaW4gY2FuZGlkYXRlczoKICAgICAgICBkZWZpbml0aW9uID0gX3F1YWxpdHkoCiAgICAgICAgICAgIGl0ZW0uZ2V0KCJkZWZpbml0aW9uIikKICAgICAgICAgICAgb3IgaXRlbS5nZXQoInZoZWlnaHQiKQogICAgICAgICAgICBvciAoaXRlbS5nZXQoInZpZGVvX21ldGEiKSBvciB7fSkuZ2V0KCJkZWZpbml0aW9uIikKICAgICAgICAgICAgb3IgaGludGVkX3F1YWxpdHkKICAgICAgICApCiAgICAgICAgcm93c1tkZWZpbml0aW9uXSA9IGl0ZW0KICAgIGlmIG5vdCByb3dzOgogICAgICAgIHJhaXNlIEhvbmdndW9QbHVnaW5FcnJvcigi5pKt5pS+5qih5Z6L5rKh5pyJ5riF5pmw5bqmIikKICAgIHJlcXVlc3RlZCA9IF9xdWFsaXR5KHdhbnRlZCkKICAgIG9yZGVyID0gW3JlcXVlc3RlZF0gKyBbaXRlbSBmb3IgaXRlbSBpbiBfUVVBTElUWV9PUkRFUiBpZiBpdGVtICE9IHJlcXVlc3RlZF0KICAgIGZvciBkZWZpbml0aW9uIGluIG9yZGVyOgogICAgICAgIGlmIGRlZmluaXRpb24gaW4gcm93czoKICAgICAgICAgICAgcmV0dXJuIGRlZmluaXRpb24sIHJvd3NbZGVmaW5pdGlvbl0KICAgIGRlZmluaXRpb24gPSBtYXgocm93cywga2V5PWxhbWJkYSBpdGVtOiBfaW50KGl0ZW0pKQogICAgcmV0dXJuIGRlZmluaXRpb24sIHJvd3NbZGVmaW5pdGlvbl0KCmRlZiBfZmFsbGJhY2tfYXBpX3ZhbHVlKHZhbHVlOiBBbnkpIC0+IHN0cjoKICAgIGlmIGlzaW5zdGFuY2UodmFsdWUsIE1hcHBpbmcpOgogICAgICAgIHJldHVybiBfZmlyc3QoCiAgICAgICAgICAgIHZhbHVlLmdldCgiZmFsbGJhY2tfYXBpIiksCiAgICAgICAgICAgIHZhbHVlLmdldCgidXJsIiksCiAgICAgICAgICAgIHZhbHVlLmdldCgiYXBpIiksCiAgICAgICAgICAgIHZhbHVlLmdldCgiZGF0YSIpLAogICAgICAgICkKICAgIGlmIGlzaW5zdGFuY2UodmFsdWUsIChsaXN0LCB0dXBsZSkpOgogICAgICAgIGZvciBpdGVtIGluIHZhbHVlOgogICAgICAgICAgICByZXN1bHQgPSBfZmFsbGJhY2tfYXBpX3ZhbHVlKGl0ZW0pCiAgICAgICAgICAgIGlmIHJlc3VsdDoKICAgICAgICAgICAgICAgIHJldHVybiByZXN1bHQKICAgICAgICByZXR1cm4gIiIKICAgIHRleHQgPSBfdGV4dCh2YWx1ZSkKICAgIGlmIHRleHQuc3RhcnRzd2l0aCgieyIpOgogICAgICAgIHRyeToKICAgICAgICAgICAgZGVjb2RlZCA9IGpzb24ubG9hZHModGV4dCkKICAgICAgICBleGNlcHQgVmFsdWVFcnJvcjoKICAgICAgICAgICAgZGVjb2RlZCA9IHt9CiAgICAgICAgaWYgZGVjb2RlZDoKICAgICAgICAgICAgcmV0dXJuIF9mYWxsYmFja19hcGlfdmFsdWUoZGVjb2RlZCkKICAgIHJldHVybiB0ZXh0IGlmIGxlbih0ZXh0KSA+IDEwIGVsc2UgIiIKCmRlZiBfZGVjcnlwdF9zcGFkZV91cmwodmFsdWU6IHN0ciwga2V5X3NlZWQ6IGJ5dGVzKSAtPiBzdHI6CiAgICByYXcgPSBfYjY0KHZhbHVlKQogICAgaWYgbGVuKHJhdykgPCAyMCBvciByYXdbMF0gIT0gMHhBOCBvciByYXdbMjo0XSAhPSBiIlx4MDFceDAwIjoKICAgICAgICByYWlzZSBIb25nZ3VvUGx1Z2luRXJyb3IoInNwYWRlIFVSTCDlpLTml6DmlYgiKQogICAgY2lwaGVyX2RhdGEgPSByYXdbNCA6IGxlbihyYXcpIC0gKGxlbihyYXcpIC0gNCkgJSAxNl0KICAgIGlmIG5vdCBjaXBoZXJfZGF0YToKICAgICAgICByYWlzZSBIb25nZ3VvUGx1Z2luRXJyb3IoInNwYWRlIFVSTCDlr4bmlofkuLrnqboiKQogICAgY29uc3RhbnRzID0gYnl0ZXMuZnJvbWhleCgKICAgICAgICAiNGRkNGMyZTZiODMxNjIwOTBlNTJiM2M3YTY3MzNiYTQiCiAgICAgICAgIjFjYjI0NjJiODI5YWI1OGExOTZiMzlkYjU3MTc3NTI0IgogICAgICAgICJmNDliYWY3ZjA4ZThkNjhkMjZhNzJlMzdjMWE5NWEyZiIKICAgICAgICAiMWYwNWE1MTg5MmFlZjI5NDk3MzJiNjJhMzhhYWRkNTgiCiAgICApCiAgICBmaXJzdCA9IGhhc2hsaWIuc2hhNTEyKGtleV9zZWVkKS5kaWdlc3QoKQogICAgc2Vjb25kID0gaGFzaGxpYi5zaGE1MTIoZmlyc3QgKyBjb25zdGFudHMpLmRpZ2VzdCgpCiAgICBwbGFpbnRleHQgPSBfYWVzX2NiY19kZWNyeXB0KHNlY29uZFs6MTZdLCBzZWNvbmRbMTY6MzJdLCBjaXBoZXJfZGF0YSkKICAgIGlmIHBsYWludGV4dDoKICAgICAgICBwYWRkaW5nID0gcGxhaW50ZXh0Wy0xXQogICAgICAgIGlmIDEgPD0gcGFkZGluZyA8PSAxNiBhbmQgcGFkZGluZyA8PSBsZW4ocGxhaW50ZXh0KToKICAgICAgICAgICAgcGxhaW50ZXh0ID0gcGxhaW50ZXh0WzotcGFkZGluZ10KICAgIHJldHVybiBwbGFpbnRleHQucnN0cmlwKGIiXDAiKS5kZWNvZGUoInV0Zi04IiwgZXJyb3JzPSJyZXBsYWNlIikKCmRlZiBfcGFyc2VfcmVmKHZhbHVlOiBzdHIsIHByZWZpeDogc3RyKSAtPiBzdHI6CiAgICBpZiBub3QgdmFsdWUuc3RhcnRzd2l0aChwcmVmaXgpOgogICAgICAgIHJhaXNlIEhvbmdndW9QbHVnaW5FcnJvcigi5pKt5pS+5byV55So5peg5pWIIikKICAgIHJhdyA9IHZhbHVlW2xlbihwcmVmaXgpIDpdCiAgICBpZiBub3QgcmF3IG9yIG5vdCBfVklERU9fSUQuZnVsbG1hdGNoKHJhdyk6CiAgICAgICAgcmFpc2UgSG9uZ2d1b1BsdWdpbkVycm9yKCLmkq3mlL7lvJXnlKjmoLzlvI/ml6DmlYgiKQogICAgcmV0dXJuIHJhdwoKZGVmIF9rZXlfc2VlZF9mcm9tX21vZGVsKG1vZGVsOiBNYXBwaW5nW3N0ciwgQW55XSkgLT4gYnl0ZXM6CiAgICB2YWx1ZSA9IF90ZXh0KG1vZGVsLmdldCgia2V5X3NlZWQiKSkKICAgIGlmIHZhbHVlOgogICAgICAgIHJldHVybiBfYjY0KHZhbHVlKQogICAgZm9yIGtleSBpbiAoImR5bmFtaWNfdmlkZW8iLCAidmlkZW9faW5mbyIsICJkYXRhIik6CiAgICAgICAgbmVzdGVkID0gbW9kZWwuZ2V0KGtleSkKICAgICAgICBpZiBpc2luc3RhbmNlKG5lc3RlZCwgTWFwcGluZyk6CiAgICAgICAgICAgIHJlc3VsdCA9IF9rZXlfc2VlZF9mcm9tX21vZGVsKG5lc3RlZCkKICAgICAgICAgICAgaWYgcmVzdWx0OgogICAgICAgICAgICAgICAgcmV0dXJuIHJlc3VsdAogICAgcmV0dXJuIGIiIgpkZWYgX3BhZ2UodXJsKToKICAgIGxhc3RfZXJyID0gTm9uZQogICAgZm9yIGF0dGVtcHQgaW4gcmFuZ2UoMyk6CiAgICAgICAgdHJ5OgogICAgICAgICAgICByID0gcmVxdWVzdHMuZ2V0KAogICAgICAgICAgICAgICAgdXJsLAogICAgICAgICAgICAgICAgaGVhZGVycz17CiAgICAgICAgICAgICAgICAgICAgIlVzZXItQWdlbnQiOiBVQSwKICAgICAgICAgICAgICAgICAgICAiQWNjZXB0LUxhbmd1YWdlIjogInpoLUNOLHpoO3E9MC45IiwKICAgICAgICAgICAgICAgICAgICAiQWNjZXB0IjogInRleHQvaHRtbCxhcHBsaWNhdGlvbi94aHRtbCt4bWw7cT0wLjksKi8qO3E9MC44IiwKICAgICAgICAgICAgICAgICAgICAiQ2FjaGUtQ29udHJvbCI6ICJuby1jYWNoZSIsCiAgICAgICAgICAgICAgICB9LAogICAgICAgICAgICAgICAgdGltZW91dD0zMCwKICAgICAgICAgICAgKQogICAgICAgICAgICByLnJhaXNlX2Zvcl9zdGF0dXMoKQogICAgICAgICAgICByLmVuY29kaW5nID0gci5lbmNvZGluZyBvciAidXRmLTgiCiAgICAgICAgICAgIGlmIG5vdCByLnRleHQgb3IgIl9ST1VURVJfREFUQSIgbm90IGluIHIudGV4dDoKICAgICAgICAgICAgICAgIHJhaXNlIFJ1bnRpbWVFcnJvcigiZW1wdHkgb3IgaW52YWxpZCBwYWdlIikKICAgICAgICAgICAgcmV0dXJuIHIudGV4dAogICAgICAgIGV4Y2VwdCBFeGNlcHRpb24gYXMgZXJyOgogICAgICAgICAgICBsYXN0X2VyciA9IGVycgogICAgICAgICAgICB0cnk6CiAgICAgICAgICAgICAgICB0aW1lLnNsZWVwKDAuNiAqIChhdHRlbXB0ICsgMSkpCiAgICAgICAgICAgIGV4Y2VwdCBFeGNlcHRpb246CiAgICAgICAgICAgICAgICBwYXNzCiAgICByYWlzZSBSdW50aW1lRXJyb3IoInBhZ2UgZmV0Y2ggZmFpbGVkOiAlcyIgJSBsYXN0X2VycikKCmRlZiBfZGF0YSh1cmwpOgogICAgaHRtbCA9IF9wYWdlKHVybCkKICAgIG0gPSByZS5zZWFyY2gociIoPzp3aW5kb3dcLik/X1JPVVRFUl9EQVRBXHMqPVxzKiIsIGh0bWwpCiAgICBpZiBub3QgbToKICAgICAgICByZXR1cm4ge30KICAgIHRyeToKICAgICAgICByZXR1cm4ganNvbi5KU09ORGVjb2RlcigpLnJhd19kZWNvZGUoaHRtbFttLmVuZCgpOl0pWzBdCiAgICBleGNlcHQgKFZhbHVlRXJyb3IsIFR5cGVFcnJvcik6CiAgICAgICAgcmV0dXJuIHt9CgpkZWYgX2l0ZW0oeCk6CiAgICB4ID0geCBvciB7fQogICAgdmQgPSB4LmdldCgidmlkZW9fZGF0YSIpIGlmIGlzaW5zdGFuY2UoeC5nZXQoInZpZGVvX2RhdGEiKSwgZGljdCkgZWxzZSB4CiAgICBzaWQgPSBzdHIoCiAgICAgICAgdmQuZ2V0KCJzZXJpZXNfaWQiKQogICAgICAgIG9yIHguZ2V0KCJzZXJpZXNfaWQiKQogICAgICAgIG9yIHguZ2V0KCJrZXl3b3JkIikKICAgICAgICBvciB2ZC5nZXQoImtleXdvcmQiKQogICAgICAgIG9yICIiCiAgICApCiAgICBuYW1lID0gc3RyKAogICAgICAgIHZkLmdldCgic2VyaWVzX3RpdGxlIikKICAgICAgICBvciB2ZC5nZXQoInNlcmllc19uYW1lIikKICAgICAgICBvciB4LmdldCgic2VyaWVzX25hbWUiKQogICAgICAgIG9yIHguZ2V0KCJuYW1lIikKICAgICAgICBvciAi5pyq5ZG95ZCNIgogICAgKQogICAgY291bnQgPSB2ZC5nZXQoImVwaXNvZGVfY250Iikgb3IgeC5nZXQoImVwaXNvZGVfY250Iikgb3IgMAogICAgcGljID0gc3RyKHZkLmdldCgic2VyaWVzX2NvdmVyIikgb3IgeC5nZXQoInNlcmllc19jb3ZlciIpIG9yICIiKQogICAgaW50cm8gPSBzdHIodmQuZ2V0KCJzZXJpZXNfaW50cm8iKSBvciB4LmdldCgic2VyaWVzX2ludHJvIikgb3IgIiIpCiAgICByZXR1cm4gewogICAgICAgICJ2b2RfaWQiOiBzaWQsCiAgICAgICAgInZvZF9uYW1lIjogbmFtZSwKICAgICAgICAidm9kX3BpYyI6IHBpYywKICAgICAgICAidm9kX3JlbWFya3MiOiAoIuWFqCVz6ZuGIiAlIGNvdW50KSBpZiBjb3VudCBlbHNlICIiLAogICAgICAgICJ2b2RfY29udGVudCI6IGludHJvLAogICAgfQoKZGVmIF9jYXRfaXRlbSh4KToKICAgIHJldHVybiBfaXRlbSh4KQoKZGVmIF9maWx0ZXJfZ3JvdXAoa2V5LCBuYW1lLCB2YWx1ZXMpOgogICAgcmV0dXJuIHsia2V5Ijoga2V5LCAibmFtZSI6IG5hbWUsICJ2YWx1ZSI6IFt7Im4iOiBuLCAidiI6IHZ9IGZvciBuLCB2IGluIHZhbHVlc119CgoKZGVmIF9zZWFyY2hfbG9hZGVyKGtleTogc3RyKSAtPiBkaWN0OgogICAgIiIi5ouJ5Y+W5pCc57Si6aG1IGxvYWRlckRhdGHvvIzlpLHotKXph43or5XjgIIiIiIKICAgIGxhc3QgPSB7fQogICAgZm9yIGF0dGVtcHQgaW4gcmFuZ2UoMyk6CiAgICAgICAgdHJ5OgogICAgICAgICAgICBkYXRhID0gX2RhdGEoU0lURSArICIvc2VhcmNoLyIgKyBxdW90ZShzdHIoa2V5KSwgc2FmZT0iIikpCiAgICAgICAgICAgIHBhZ2UgPSAoZGF0YS5nZXQoImxvYWRlckRhdGEiKSBvciB7fSkuZ2V0KCJzZWFyY2hfKGtleXdvcmQpL3BhZ2UiKSBvciB7fQogICAgICAgICAgICBpZiBwYWdlLmdldCgic2VhcmNoTGlzdCIpOgogICAgICAgICAgICAgICAgcmV0dXJuIHBhZ2UKICAgICAgICAgICAgbGFzdCA9IHBhZ2Ugb3IgbGFzdAogICAgICAgIGV4Y2VwdCBFeGNlcHRpb246CiAgICAgICAgICAgIHBhc3MKICAgICAgICB0cnk6CiAgICAgICAgICAgIHRpbWUuc2xlZXAoMC41ICogKGF0dGVtcHQgKyAxKSkKICAgICAgICBleGNlcHQgRXhjZXB0aW9uOgogICAgICAgICAgICBwYXNzCiAgICByZXR1cm4gbGFzdAoKCmRlZiBfc2VhcmNoX2J5X2tleXdvcmRzKGtleXdvcmRzLCBwYWdlOiBpbnQpIC0+IGRpY3Q6CiAgICAiIiLlpJrlhbPplK7or43ova7mjaLvvJrnrKwgTiDpobXnlKjnrKwgTiDkuKrlhbPplK7or43vvIjlvqrnjq/vvInvvIzpgb/lhY3mkJzntKLml6Dms5Xnv7vpobXjgIIiIiIKICAgIHBhZ2UgPSBtYXgoMSwgaW50KHBhZ2Ugb3IgMSkpCiAgICBrd3MgPSBbayBmb3IgayBpbiAoa2V5d29yZHMgb3IgW10pIGlmIGtdCiAgICBpZiBub3Qga3dzOgogICAgICAgIGt3cyA9IFsi55+t5YmnIl0KICAgIGtleSA9IGt3c1socGFnZSAtIDEpICUgbGVuKGt3cyldCiAgICBwID0gX3NlYXJjaF9sb2FkZXIoa2V5KQogICAgcm93cyA9IHAuZ2V0KCJzZWFyY2hMaXN0Iikgb3IgW10KICAgICMg5Y676YeN56m6IGlkCiAgICBvdXQgPSBbXQogICAgc2VlbiA9IHNldCgpCiAgICBmb3IgeCBpbiByb3dzOgogICAgICAgIGl0ID0gX2l0ZW0oeCkKICAgICAgICB2aWQgPSBzdHIoaXQuZ2V0KCJ2b2RfaWQiKSBvciAiIikKICAgICAgICBpZiBub3QgdmlkIG9yIHZpZCBpbiBzZWVuOgogICAgICAgICAgICBjb250aW51ZQogICAgICAgIHNlZW4uYWRkKHZpZCkKICAgICAgICBvdXQuYXBwZW5kKGl0KQogICAgIyDomZrmi5/pobXmlbDvvJrlhbPplK7or43mlbDvvJvoi6Xnq5nngrnmnIkgdG90YWxDb3VudCDkuZ/lj4LogIMKICAgIHRvdGFsID0gaW50KHAuZ2V0KCJ0b3RhbENvdW50Iikgb3IgMCkKICAgIHBhZ2Vjb3VudCA9IG1heChsZW4oa3dzKSwgKHRvdGFsICsgOSkgLy8gMTAgaWYgdG90YWwgZWxzZSBsZW4oa3dzKSkKICAgIHJldHVybiB7CiAgICAgICAgInBhZ2UiOiBwYWdlLAogICAgICAgICJwYWdlY291bnQiOiBtYXgoMSwgcGFnZWNvdW50KSwKICAgICAgICAibGltaXQiOiBsZW4ob3V0KSwKICAgICAgICAidG90YWwiOiB0b3RhbCBvciBsZW4ob3V0KSAqIHBhZ2Vjb3VudCwKICAgICAgICAibGlzdCI6IG91dCwKICAgIH0KCgpkZWYgX2NhdGVnb3J5X2xvYWRlcihwYWdlOiBpbnQsIHE6IGRpY3QpIC0+IGRpY3Q6CiAgICAiIiLliIbnsbvpobXluKbph43or5XvvJtwYWdlPTEg5YG25Y+R56m65YiX6KGo5pe25aSa6K+V5Yeg5qyh44CCIiIiCiAgICBwYWdlID0gbWF4KDEsIGludChwYWdlIG9yIDEpKQogICAgcSA9IGRpY3QocSBvciB7fSkKICAgIGlmIHBhZ2UgPiAxOgogICAgICAgIHFbInBhZ2UiXSA9IHN0cihwYWdlKQogICAgbGFzdCA9IHt9CiAgICBmb3IgYXR0ZW1wdCBpbiByYW5nZSgzKToKICAgICAgICB0cnk6CiAgICAgICAgICAgIGRhdGEgPSBfZGF0YShTSVRFICsgIi9jYXRlZ29yeT8iICsgdXJsZW5jb2RlKHEpKQogICAgICAgICAgICBwID0gKGRhdGEuZ2V0KCJsb2FkZXJEYXRhIikgb3Ige30pLmdldCgiY2F0ZWdvcnlfJCIpIG9yIChkYXRhLmdldCgibG9hZGVyRGF0YSIpIG9yIHt9KS5nZXQoImNhdGVnb3J5X3BhZ2UiKSBvciB7fQogICAgICAgICAgICByb3dzID0gcC5nZXQoInJlY29tbWVuZExpc3QiKSBvciBbXQogICAgICAgICAgICBpZiByb3dzIG9yIHBhZ2UgPiAxOgogICAgICAgICAgICAgICAgcmV0dXJuIHAKICAgICAgICAgICAgbGFzdCA9IHAgb3IgbGFzdAogICAgICAgIGV4Y2VwdCBFeGNlcHRpb246CiAgICAgICAgICAgIHBhc3MKICAgICAgICB0cnk6CiAgICAgICAgICAgIHRpbWUuc2xlZXAoMC41ICogKGF0dGVtcHQgKyAxKSkKICAgICAgICBleGNlcHQgRXhjZXB0aW9uOgogICAgICAgICAgICBwYXNzCiAgICByZXR1cm4gbGFzdAoKY2xhc3MgU3BpZGVyKF9CYXNlU3BpZGVyKToKICAgIGRlZiBfX2luaXRfXyhzZWxmKToKICAgICAgICBzZWxmLmRldmljZV9pZCA9IHN0cihyYW5kb20ucmFuZGludCgxMCoqMTcsIDEwKioxOCAtIDEpKQogICAgICAgIHNlbGYuaW5zdGFsbF9pZCA9IHN0cihyYW5kb20ucmFuZGludCgxMCoqMTcsIDEwKioxOCAtIDEpKQoKICAgIGRlZiBnZXROYW1lKHNlbGYpOgogICAgICAgIHJldHVybiAi57qi5p6c55+t5YmnIgoKICAgIGRlZiBpc1ZpZGVvRm9ybWF0KHNlbGYsIHVybCk6CiAgICAgICAgdSA9IHN0cih1cmwgb3IgIiIpLmxvd2VyKCkKICAgICAgICByZXR1cm4gKCIubXA0IiBpbiB1KSBvciAoInZpZGVvX21wNCIgaW4gdSkgb3IgKCJtM3U4IiBpbiB1KSBvciAoIm1pbWVfdHlwZT12aWRlbyIgaW4gdSkgb3IgKCJxem5vdmVsdm9kIiBpbiB1KQoKICAgIGRlZiBtYW51YWxWaWRlb0NoZWNrKHNlbGYpOgogICAgICAgIHJldHVybiBGYWxzZQoKICAgIGRlZiBnZXREZXBlbmRlbmNlKHNlbGYpOgogICAgICAgIHJldHVybiBbXQoKICAgIGRlZiBkb3dubG9hZChzZWxmLCBwYXRoLCB1cmwpOgogICAgICAgIHJldHVybiAiIgoKICAgIGRlZiBsaXZlQ29udGVudChzZWxmKToKICAgICAgICByZXR1cm4ge30KCiAgICBkZWYgaXNWUEFZYXJkKHNlbGYsIGZsYWcpOgogICAgICAgIHJldHVybiBGYWxzZQoKICAgIGRlZiBhY3Rpb24oc2VsZiwgYWN0aW9uKToKICAgICAgICByZXR1cm4gIiIKCiAgICBkZWYgaW5pdChzZWxmLCBleHRlbmQ9IiIpOgogICAgICAgICMg5q+P5qyh5rqQ5a6e5L6L5L2/55So6ZqP5py65ZCI5rOV6K6+5aSH5qCH6K+G77yb5LiN5L6d6LWW55So5oi356eB5pyJ6YWN572u44CCCiAgICAgICAgdHJ5OgogICAgICAgICAgICBfaGdfY2FjaGVfY2xlYW51cChGYWxzZSkKICAgICAgICBleGNlcHQgRXhjZXB0aW9uOgogICAgICAgICAgICBwYXNzCiAgICAgICAgcmV0dXJuIE5vbmUKCiAgICBkZWYgZGVzdHJveShzZWxmKToKICAgICAgICB0cnk6CiAgICAgICAgICAgIF9oZ19jYWNoZV9jbGVhbnVwKEZhbHNlKQogICAgICAgIGV4Y2VwdCBFeGNlcHRpb246CiAgICAgICAgICAgIHBhc3MKCiAgICBkZWYgaG9tZUNvbnRlbnQoc2VsZiwgZmlsdGVyKToKICAgICAgICBjbGFzc19saXN0ID0gWwogICAgICAgICAgICB7InR5cGVfaWQiOiAiYWxsIiwgInR5cGVfbmFtZSI6ICLnn63liacifSwKICAgICAgICAgICAgeyJ0eXBlX2lkIjogImFpX2NvbWljIiwgInR5cGVfbmFtZSI6ICJBSea8q+WJpyJ9LAogICAgICAgICAgICB7InR5cGVfaWQiOiAibGF0ZXN0IiwgInR5cGVfbmFtZSI6ICLmnIDmlrAifSwKICAgICAgICAgICAgeyJ0eXBlX2lkIjogImhvdCIsICJ0eXBlX25hbWUiOiAi5pyA54OtIn0sCiAgICAgICAgICAgIHsidHlwZV9pZCI6ICJtYWxlIiwgInR5cGVfbmFtZSI6ICLnlLfpopEifSwKICAgICAgICAgICAgeyJ0eXBlX2lkIjogImZlbWFsZSIsICJ0eXBlX25hbWUiOiAi5aWz6aKRIn0sCiAgICAgICAgXQogICAgICAgIGdyb3VwcyA9IFsKICAgICAgICAgICAgeyJrZXkiOiAidG9waWMiLCAibmFtZSI6ICLkuLvpopgiLCAidmFsdWUiOiBbCiAgICAgICAgICAgICAgICB7Im4iOiAi5YWo6YOoIiwgInYiOiAiIn0sIHsibiI6ICLnjrDoqIAiLCAidiI6ICJjYXRlXzEwMjEifSwgeyJuIjogIuWls+aAp+aIkOmVvyIsICJ2IjogImNhdGVfMTA0OCJ9LAogICAgICAgICAgICAgICAgeyJuIjogIuiEkea0niIsICJ2IjogImNhdGVfMjYyIn0sIHsibiI6ICLlpYflubsiLCAidiI6ICJjYXRlXzEwMjAifSwgeyJuIjogIueOhOW5uyIsICJ2IjogImNhdGVfMTAxOSJ9LAogICAgICAgICAgICAgICAgeyJuIjogIuWPpOiogCIsICJ2IjogImNhdGVfNDM5In0sIHsibiI6ICLmiJjnpZ4iLCAidiI6ICJjYXRlXzEwMzgifSwgeyJuIjogIuWuq+aWlyIsICJ2IjogImNhdGVfMjQ2In0sCiAgICAgICAgICAgICAgICB7Im4iOiAi5LuZ5L6gIiwgInYiOiAiY2F0ZV8xMDEzIn0sIHsibiI6ICLmnYPosIsiLCAidiI6ICJjYXRlXzEwNDcifSwgeyJuIjogIuenjeeUsCIsICJ2IjogImNhdGVfMTE4MCJ9LAogICAgICAgICAgICAgICAgeyJuIjogIuW5tOS7o+eIseaDhSIsICJ2IjogImNhdGVfMTAyMiJ9LCB7Im4iOiAi5oKs55aRIiwgInYiOiAiY2F0ZV8xNjUifSwgeyJuIjogIuWWnOWJpyIsICJ2IjogImNhdGVfMzAzIn0sCiAgICAgICAgICAgICAgICB7Im4iOiAi6Z2S5pilIiwgInYiOiAiY2F0ZV8yOTcifSwgeyJuIjogIuW/l+aAqiIsICJ2IjogImNhdGVfMTAyNyJ9LCB7Im4iOiAi5rCR5Zu954ix5oOFIiwgInYiOiAiY2F0ZV8xMDI1In0sCiAgICAgICAgICAgICAgICB7Im4iOiAi54G15byCIiwgInYiOiAiY2F0ZV83NTEifSwgeyJuIjogIuWutuWbveaDheaAgCIsICJ2IjogImNhdGVfMTIzNSJ9LCB7Im4iOiAi5rOV5b6LIiwgInYiOiAiY2F0ZV8xMTM2In0sCiAgICAgICAgICAgICAgICB7Im4iOiAi5YiR5L6mIiwgInYiOiAiY2F0ZV8xMTQ4In0sIHsibiI6ICLmipfmiJgiLCAidiI6ICJjYXRlXzUwNCJ9LCB7Im4iOiAi5q2m5L6gIiwgInYiOiAiY2F0ZV8xMTcyIn0sCiAgICAgICAgICAgICAgICB7Im4iOiAi5rCR5Zu95Lyg5aWHIiwgInYiOiAiY2F0ZV8xMjQwIn0sIHsibiI6ICLmsYLnlJ8iLCAidiI6ICJjYXRlXzExNjgifSwgeyJuIjogIuWKqOS9nCIsICJ2IjogImNhdGVfMzAyIn0sCiAgICAgICAgICAgICAgICB7Im4iOiAi56eR5bm7IiwgInYiOiAiY2F0ZV8xMDkyIn0sIHsibiI6ICLmgZDmgJYiLCAidiI6ICJjYXRlXzEyMTkifSwgeyJuIjogIuWVhuaImCIsICJ2IjogImNhdGVfMTIyNSJ9LAogICAgICAgICAgICBdfSwKICAgICAgICAgICAgeyJrZXkiOiAiYmFja2dyb3VuZCIsICJuYW1lIjogIuiDjOaZryIsICJ2YWx1ZSI6IFsKICAgICAgICAgICAgICAgIHsibiI6ICLlhajpg6giLCAidiI6ICIifSwgeyJuIjogIueOsOS7oyIsICJ2IjogImNhdGVfNzU3In0sIHsibiI6ICLpg73luIIiLCAidiI6ICJjYXRlXzEifSwKICAgICAgICAgICAgICAgIHsibiI6ICLlj6Tku6MiLCAidiI6ICJjYXRlXzc1OCJ9LCB7Im4iOiAi5Lmh5p2RIiwgInYiOiAiY2F0ZV8xMSJ9LCB7Im4iOiAi5bm05LujIiwgInYiOiAiY2F0ZV83OSJ9LAogICAgICAgICAgICAgICAgeyJuIjogIuaetuepuiIsICJ2IjogImNhdGVfNDUyIn0sIHsibiI6ICLogYzlnLoiLCAidiI6ICJjYXRlXzEyNyJ9LCB7Im4iOiAi5rCR5Zu9IiwgInYiOiAiY2F0ZV8zOTAifSwKICAgICAgICAgICAgICAgIHsibiI6ICLmoKHlm60iLCAidiI6ICJjYXRlXzQifSwgeyJuIjogIuWuq+W7tyIsICJ2IjogImNhdGVfMTE1MyJ9LCB7Im4iOiAi6I2S5bKbIiwgInYiOiAiY2F0ZV8xMTYyIn0sCiAgICAgICAgICAgIF19LAogICAgICAgICAgICB7ImtleSI6ICJzZXR0aW5nIiwgIm5hbWUiOiAi6K6+5a6aIiwgInZhbHVlIjogWwogICAgICAgICAgICAgICAgeyJuIjogIuWFqOmDqCIsICJ2IjogIiJ9LCB7Im4iOiAi5omT6IS46JmQ5rijIiwgInYiOiAiY2F0ZV8xMDUxIn0sIHsibiI6ICLlpKfnlLfkuLsiLCAidiI6ICJjYXRlXzEyMDcifSwKICAgICAgICAgICAgICAgIHsibiI6ICLlpKflpbPkuLsiLCAidiI6ICJjYXRlXzc2MCJ9LCB7Im4iOiAi6ams55SyIiwgInYiOiAiY2F0ZV8yNjYifSwgeyJuIjogIumHjeeUnyIsICJ2IjogImNhdGVfMzYifSwKICAgICAgICAgICAgICAgIHsibiI6ICLnqb/otooiLCAidiI6ICJjYXRlXzM3In0sIHsibiI6ICLns7vnu58iLCAidiI6ICJjYXRlXzE5In0sIHsibiI6ICLlhYjlqZrlkI7niLEiLCAidiI6ICJjYXRlXzI2NSJ9LAogICAgICAgICAgICAgICAgeyJuIjogIuWutumVv+mHjOefrSIsICJ2IjogImNhdGVfODYyIn0sIHsibiI6ICLlsI/kurrniakiLCAidiI6ICJjYXRlXzEwMTAifSwgeyJuIjogIuegtOmVnOmHjeWchiIsICJ2IjogImNhdGVfNDc1In0sCiAgICAgICAgICAgICAgICB7Im4iOiAi56We6LGqIiwgInYiOiAiY2F0ZV8yMCJ9LCB7Im4iOiAi6LGq6ZeoIiwgInYiOiAiY2F0ZV85MzYifSwgeyJuIjogIuW8uuiAheWbnuW9kiIsICJ2IjogImNhdGVfMTA0NSJ9LAogICAgICAgICAgICAgICAgeyJuIjogIuW8guiDvSIsICJ2IjogImNhdGVfNTk4In0sIHsibiI6ICLomZDmgYsiLCAidiI6ICJjYXRlXzEwMDgifSwgeyJuIjogIuS8oOaJv+iniemGkiIsICJ2IjogImNhdGVfMTAwNyJ9LAogICAgICAgICAgICAgICAgeyJuIjogIuWMu+eUnyIsICJ2IjogImNhdGVfNDg3In0sIHsibiI6ICLlvLrlvLrogZTlkIgiLCAidiI6ICJjYXRlXzEwNDkifSwgeyJuIjogIui1mOWpv+mAhuiirSIsICJ2IjogImNhdGVfMTA0NCJ9LAogICAgICAgICAgICAgICAgeyJuIjogIueUnOWuoCIsICJ2IjogImNhdGVfOTYifSwgeyJuIjogIuWoseS5kOWciCIsICJ2IjogImNhdGVfNDMifSwgeyJuIjogIuelnuWMuyIsICJ2IjogImNhdGVfMjYifSwKICAgICAgICAgICAgICAgIHsibiI6ICLpnZLmooXnq7npqawiLCAidiI6ICJjYXRlXzM4NyJ9LCB7Im4iOiAi5aeQ5byf5oGLIiwgInYiOiAiY2F0ZV83NjIifSwgeyJuIjogIueOhOWtpiIsICJ2IjogImNhdGVfOTI5In0sCiAgICAgICAgICAgICAgICB7Im4iOiAi6L+95aa754Gr6JGs5Zy6IiwgInYiOiAiY2F0ZV82MTYifSwgeyJuIjogIuS4mueVjOeyvuiLsSIsICJ2IjogImNhdGVfMTI5MyJ9LCB7Im4iOiAi5LiA6KeB6ZKf5oOFIiwgInYiOiAiY2F0ZV80NzcifSwKICAgICAgICAgICAgICAgIHsibiI6ICLnpo/lrp0iLCAidiI6ICJjYXRlXzEyOTEifSwgeyJuIjogIuaNnuWBj+mXqCIsICJ2IjogImNhdGVfMTI4NyJ9LCB7Im4iOiAi5Y+N5rS+5Li76KeSIiwgInYiOiAiY2F0ZV8xMDQyIn0sCiAgICAgICAgICAgICAgICB7Im4iOiAi6JCM5a6gIiwgInYiOiAiY2F0ZV80MjgifSwgeyJuIjogIuWPjOWQkeaVkei1jiIsICJ2IjogImNhdGVfMTIwMCJ9LCB7Im4iOiAi5pa56KiAIiwgInYiOiAiY2F0ZV8xMjU1In0sCiAgICAgICAgICAgICAgICB7Im4iOiAi55m95pyI5YWJIiwgInYiOiAiY2F0ZV82MTUifSwgeyJuIjogIueBtemtguS6kuaNoiIsICJ2IjogImNhdGVfODMxIn0sIHsibiI6ICLnl4XlqIciLCAidiI6ICJjYXRlXzM4MCJ9LAogICAgICAgICAgICAgICAgeyJuIjogIuaatOWvjCIsICJ2IjogImNhdGVfMTE5MSJ9LCB7Im4iOiAi6buR6YGTIiwgInYiOiAiY2F0ZV84MjYifSwgeyJuIjogIuS4p+WwuCIsICJ2IjogImNhdGVfNTgyIn0sCiAgICAgICAgICAgICAgICB7Im4iOiAi54m556eN5YW1IiwgInYiOiAiY2F0ZV8zNzUifSwKICAgICAgICAgICAgXX0sCiAgICAgICAgICAgIHsia2V5IjogInRpbWUiLCAibmFtZSI6ICLml7bpl7QiLCAidmFsdWUiOiBbCiAgICAgICAgICAgICAgICB7Im4iOiAi5YWo6YOoIiwgInYiOiAiIn0sIHsibiI6ICI35aSp5YaF5LiK5pawIiwgInYiOiAiMSJ9LCB7Im4iOiAiMTTlpKnlhoXkuIrmlrAiLCAidiI6ICIyIn0sCiAgICAgICAgICAgICAgICB7Im4iOiAiMzDlpKnlhoXkuIrmlrAiLCAidiI6ICIzIn0sIHsibiI6ICI5MOWkqeWGheS4iuaWsCIsICJ2IjogIjQifSwKICAgICAgICAgICAgXX0sCiAgICAgICAgXQogICAgICAgIGZpbHRlcl9kaWN0ID0ge2NbInR5cGVfaWQiXTogZ3JvdXBzIGZvciBjIGluIGNsYXNzX2xpc3R9CiAgICAgICAgaG9tZV9saXN0ID0gW10KICAgICAgICB0cnk6CiAgICAgICAgICAgIGRhdGEgPSBfZGF0YShTSVRFICsgIi8iKQogICAgICAgICAgICBwYWdlID0gKGRhdGEuZ2V0KCJsb2FkZXJEYXRhIikgb3Ige30pLmdldCgicGFnZSIpIG9yIHt9CiAgICAgICAgICAgIHNlZW4gPSBzZXQoKQogICAgICAgICAgICBmb3Igc2VjIGluIChwYWdlLmdldCgiaG9tZVNlY3Rpb25zIikgb3IgW10pOgogICAgICAgICAgICAgICAgZm9yIHYgaW4gKHNlYy5nZXQoInZpZGVvX2xpc3QiKSBvciBbXSk6CiAgICAgICAgICAgICAgICAgICAgaXQgPSBfaXRlbSh2KQogICAgICAgICAgICAgICAgICAgIHZpZCA9IHN0cihpdC5nZXQoInZvZF9pZCIpIG9yICIiKQogICAgICAgICAgICAgICAgICAgIGlmIHZpZCBhbmQgdmlkIG5vdCBpbiBzZWVuOgogICAgICAgICAgICAgICAgICAgICAgICBzZWVuLmFkZCh2aWQpCiAgICAgICAgICAgICAgICAgICAgICAgIGhvbWVfbGlzdC5hcHBlbmQoaXQpCiAgICAgICAgZXhjZXB0IEV4Y2VwdGlvbjoKICAgICAgICAgICAgaG9tZV9saXN0ID0gW10KICAgICAgICByZXR1cm4geyJjbGFzcyI6IGNsYXNzX2xpc3QsICJmaWx0ZXJzIjogZmlsdGVyX2RpY3QsICJsaXN0IjogaG9tZV9saXN0Wzo0MF19CiAgICBkZWYgaG9tZVZpZGVvQ29udGVudChzZWxmKToKICAgICAgICB0cnk6CiAgICAgICAgICAgIGRhdGEgPSBfZGF0YShTSVRFICsgIi8iKQogICAgICAgICAgICBwYWdlID0gKGRhdGEuZ2V0KCJsb2FkZXJEYXRhIikgb3Ige30pLmdldCgicGFnZSIpIG9yIHt9CiAgICAgICAgICAgIG91dCA9IFtdCiAgICAgICAgICAgIHNlZW4gPSBzZXQoKQogICAgICAgICAgICBmb3Igc2VjIGluIChwYWdlLmdldCgiaG9tZVNlY3Rpb25zIikgb3IgW10pOgogICAgICAgICAgICAgICAgZm9yIHYgaW4gKHNlYy5nZXQoInZpZGVvX2xpc3QiKSBvciBbXSk6CiAgICAgICAgICAgICAgICAgICAgaXQgPSBfaXRlbSh2KQogICAgICAgICAgICAgICAgICAgIHZpZCA9IHN0cihpdC5nZXQoInZvZF9pZCIpIG9yICIiKQogICAgICAgICAgICAgICAgICAgIGlmIHZpZCBhbmQgdmlkIG5vdCBpbiBzZWVuOgogICAgICAgICAgICAgICAgICAgICAgICBzZWVuLmFkZCh2aWQpCiAgICAgICAgICAgICAgICAgICAgICAgIG91dC5hcHBlbmQoaXQpCiAgICAgICAgICAgIHJldHVybiB7Imxpc3QiOiBvdXRbOjYwXX0KICAgICAgICBleGNlcHQgRXhjZXB0aW9uOgogICAgICAgICAgICByZXR1cm4geyJsaXN0IjogW119CgogICAgZGVmIF9xdWVyeShzZWxmLCBwZywgcT1Ob25lKToKICAgICAgICB0cnk6CiAgICAgICAgICAgIHBnID0gbWF4KDEsIGludChwZykpCiAgICAgICAgZXhjZXB0IChUeXBlRXJyb3IsIFZhbHVlRXJyb3IpOgogICAgICAgICAgICBwZyA9IDEKICAgICAgICBpZiBxIGlzIE5vbmU6CiAgICAgICAgICAgIHEgPSB7InRhYiI6ICIxIiwgInNvcnRfdHlwZSI6ICIxIn0KICAgICAgICByZXR1cm4gX2NhdGVnb3J5X2xvYWRlcihwZywgcSkKICAgIGRlZiBjYXRlZ29yeUNvbnRlbnQoc2VsZiwgdGlkLCBwZywgZmlsdGVyLCBleHRlbmQpOgogICAgICAgIHRyeToKICAgICAgICAgICAgcGFnZSA9IG1heCgxLCBpbnQocGcpKQogICAgICAgIGV4Y2VwdCAoVHlwZUVycm9yLCBWYWx1ZUVycm9yKToKICAgICAgICAgICAgcGFnZSA9IDEKICAgICAgICAjIOa8q+WJpyAvIEFJ5ryr5Ymn77ya5a6Y572R5pCc57Si5LiN5pSv5oyB55yf57+76aG177yM5aSa5YWz6ZSu6K+N6L2u5o2iCiAgICAgICAgaWYgdGlkIGluICgiY29taWMiLCAibWFuanUiLCAi5ryr5YmnIik6CiAgICAgICAgICAgIHRyeToKICAgICAgICAgICAgICAgIHAgPSBfY2F0ZWdvcnlfbG9hZGVyKHBhZ2UsIHsidGFiIjogIjIiLCAic29ydF90eXBlIjogIjEifSkKICAgICAgICAgICAgICAgIHJvd3MgPSBwLmdldCgicmVjb21tZW5kTGlzdCIpIG9yIFtdCiAgICAgICAgICAgICAgICBpZiByb3dzOgogICAgICAgICAgICAgICAgICAgIHBhZ2VfZGF0YSA9IHAuZ2V0KCJwYWdpbmF0aW9uIikgb3Ige30KICAgICAgICAgICAgICAgICAgICByZXR1cm4gewogICAgICAgICAgICAgICAgICAgICAgICAicGFnZSI6IHBhZ2UsCiAgICAgICAgICAgICAgICAgICAgICAgICJwYWdlY291bnQiOiBpbnQocGFnZV9kYXRhLmdldCgidG90YWxQYWdlcyIpIG9yIDEpLAogICAgICAgICAgICAgICAgICAgICAgICAibGltaXQiOiBsZW4ocm93cyksCiAgICAgICAgICAgICAgICAgICAgICAgICJ0b3RhbCI6IGludChwYWdlX2RhdGEuZ2V0KCJ0b3RhbCIpIG9yIGxlbihyb3dzKSksCiAgICAgICAgICAgICAgICAgICAgICAgICJsaXN0IjogW19jYXRfaXRlbSh4KSBmb3IgeCBpbiByb3dzXSwKICAgICAgICAgICAgICAgICAgICB9CiAgICAgICAgICAgIGV4Y2VwdCBFeGNlcHRpb246CiAgICAgICAgICAgICAgICBwYXNzCiAgICAgICAgICAgIHJldHVybiBfc2VhcmNoX2J5X2tleXdvcmRzKF9NQU5KVV9LRVlXT1JEUywgcGFnZSkKICAgICAgICBpZiB0aWQgaW4gKCJhaV9jb21pYyIsICJhaV9tYW5qdSIsICJBSea8q+WJpyIsICJhaea8q+WJpyIpOgogICAgICAgICAgICByZXR1cm4gX3NlYXJjaF9ieV9rZXl3b3JkcyhfQUlfTUFOSlVfS0VZV09SRFMsIHBhZ2UpCiAgICAgICAgcSA9IHsidGFiIjogIjEiLCAic29ydF90eXBlIjogIjEifQogICAgICAgIGlmIHRpZCA9PSAibGF0ZXN0IjoKICAgICAgICAgICAgcVsic29ydF90eXBlIl0gPSAiMiIKICAgICAgICBlbGlmIHRpZCA9PSAiaG90IjoKICAgICAgICAgICAgcVsic29ydF90eXBlIl0gPSAiMSIKICAgICAgICBlbGlmIHRpZCA9PSAibWFsZSI6CiAgICAgICAgICAgIHFbImdlbmRlciJdID0gIjEiCiAgICAgICAgZWxpZiB0aWQgPT0gImZlbWFsZSI6CiAgICAgICAgICAgIHFbImdlbmRlciJdID0gIjIiCiAgICAgICAgaWYgaXNpbnN0YW5jZShleHRlbmQsIHN0cikgYW5kIGV4dGVuZDoKICAgICAgICAgICAgdHJ5OgogICAgICAgICAgICAgICAgZXh0ZW5kID0ganNvbi5sb2FkcyhleHRlbmQpCiAgICAgICAgICAgIGV4Y2VwdCBFeGNlcHRpb246CiAgICAgICAgICAgICAgICBleHRlbmQgPSB7fQogICAgICAgIGlmIGlzaW5zdGFuY2UoZXh0ZW5kLCBkaWN0KToKICAgICAgICAgICAgZm9yIGssIHYgaW4gZXh0ZW5kLml0ZW1zKCk6CiAgICAgICAgICAgICAgICBpZiB2IGFuZCBzdHIodikgbm90IGluICgiIiwgImFsbCIsICIwIik6CiAgICAgICAgICAgICAgICAgICAgcVtrXSA9IHN0cih2KQogICAgICAgIHAgPSBfY2F0ZWdvcnlfbG9hZGVyKHBhZ2UsIHEpCiAgICAgICAgcm93cyA9IHAuZ2V0KCJyZWNvbW1lbmRMaXN0Iikgb3IgW10KICAgICAgICBwYWdlX2RhdGEgPSBwLmdldCgicGFnaW5hdGlvbiIpIG9yIHt9CiAgICAgICAgcmV0dXJuIHsKICAgICAgICAgICAgInBhZ2UiOiBwYWdlLAogICAgICAgICAgICAicGFnZWNvdW50IjogaW50KHBhZ2VfZGF0YS5nZXQoInRvdGFsUGFnZXMiKSBvciAxKSwKICAgICAgICAgICAgImxpbWl0IjogbGVuKHJvd3MpLAogICAgICAgICAgICAidG90YWwiOiBpbnQocGFnZV9kYXRhLmdldCgidG90YWwiKSBvciBsZW4ocm93cykpLAogICAgICAgICAgICAibGlzdCI6IFtfY2F0X2l0ZW0oeCkgZm9yIHggaW4gcm93c10sCiAgICAgICAgfQogICAgZGVmIHNlYXJjaENvbnRlbnQoc2VsZiwga2V5LCBxdWljaz1GYWxzZSwgcGc9IjEiKToKICAgICAgICB0cnk6CiAgICAgICAgICAgIHBhZ2UgPSBtYXgoMSwgaW50KHBnKSkKICAgICAgICBleGNlcHQgKFR5cGVFcnJvciwgVmFsdWVFcnJvcik6CiAgICAgICAgICAgIHBhZ2UgPSAxCiAgICAgICAga2V5ID0gc3RyKGtleSBvciAiIikuc3RyaXAoKSBvciAi55+t5YmnIgogICAgICAgICMgQUkv5ryr5Ymn55u45YWz5pCc57Si5Lmf6LWw5YWz6ZSu6K+N6L2u5o2i77yM5o+Q5Y2H57+76aG15L2T6aqMCiAgICAgICAgbG93ID0ga2V5Lmxvd2VyKCkKICAgICAgICBpZiBrZXkgaW4gKCJBSea8q+WJpyIsICJhaea8q+WJpyIpIG9yICJhaea8qyIgaW4gbG93OgogICAgICAgICAgICByZXR1cm4gX3NlYXJjaF9ieV9rZXl3b3JkcyhfQUlfTUFOSlVfS0VZV09SRFMsIHBhZ2UpCiAgICAgICAgaWYga2V5IGluICgi5ryr5YmnIiwgIuWKqOa8q+efreWJpyIpOgogICAgICAgICAgICByZXR1cm4gX3NlYXJjaF9ieV9rZXl3b3JkcyhfTUFOSlVfS0VZV09SRFMsIHBhZ2UpCgogICAgICAgIHAgPSBfc2VhcmNoX2xvYWRlcihrZXkpCiAgICAgICAgcm93cyA9IHAuZ2V0KCJzZWFyY2hMaXN0Iikgb3IgW10KICAgICAgICB0b3RhbCA9IGludChwLmdldCgidG90YWxDb3VudCIpIG9yIGxlbihyb3dzKSBvciAwKQogICAgICAgICMg5a6Y572R5pCc57Si5Z+65pys5Y+q5pyJ5LiA6aG15pyJ5pWI57uT5p6cCiAgICAgICAgcmV0dXJuIHsKICAgICAgICAgICAgInBhZ2UiOiBwYWdlLAogICAgICAgICAgICAicGFnZWNvdW50IjogMSBpZiBub3QgdG90YWwgZWxzZSBtYXgoMSwgbWluKDEwLCAodG90YWwgKyA5KSAvLyAxMCkpLAogICAgICAgICAgICAibGltaXQiOiBsZW4ocm93cyksCiAgICAgICAgICAgICJ0b3RhbCI6IHRvdGFsIG9yIGxlbihyb3dzKSwKICAgICAgICAgICAgImxpc3QiOiBbX2l0ZW0oeCkgZm9yIHggaW4gcm93c10sCiAgICAgICAgfQoKCiAgICBkZWYgZGV0YWlsQ29udGVudChzZWxmLCBpZHMpOgogICAgICAgIHNpZCA9IHN0cihpZHNbMF0gaWYgaXNpbnN0YW5jZShpZHMsIChsaXN0LCB0dXBsZSkpIGVsc2UgaWRzKQogICAgICAgIHNpZCA9IHNpZC5yZXBsYWNlKCJoZy1zZXJpZXMtdjE6IiwgIiIpCiAgICAgICAgcCA9ICgoX2RhdGEoU0lURSArICIvZGV0YWlsP3Nlcmllc19pZD0iICsgcXVvdGUoc2lkLCBzYWZlPSIiKSkuZ2V0KCJsb2FkZXJEYXRhIikgb3Ige30pLmdldCgiZGV0YWlsX3BhZ2UiKSBvciB7fSkKICAgICAgICBzID0gcC5nZXQoInNlcmllc0RldGFpbCIpIG9yIHt9CiAgICAgICAgdmlkcyA9IHMuZ2V0KCJ2aWRfbGlzdCIpIG9yIFtdCiAgICAgICAgYWN0b3JzID0gW3N0cih4LmdldCgibmlja25hbWUiKSkgZm9yIHggaW4gKHMuZ2V0KCJjZWxlYnJpdGllcyIpIG9yIFtdKSBpZiBpc2luc3RhbmNlKHgsIGRpY3QpIGFuZCB4LmdldCgibmlja25hbWUiKV0KICAgICAgICBwbGF5X2Zyb20gPSBbXQogICAgICAgIHBsYXlfdXJsID0gW10KICAgICAgICBmb3IgcSwgbGluZV9uYW1lIGluIF9IR19RVUFMSVRZX0xJTkVTOgogICAgICAgICAgICBlcHMgPSAiIyIuam9pbigKICAgICAgICAgICAgICAgICLnrKwlZOmbhiVzJXMlcyVzIiAlIChpICsgMSwgIiQiLCBFUElTT0RFX1BSRUZJWCwgcSArICI6Iiwgc3RyKHYpKQogICAgICAgICAgICAgICAgZm9yIGksIHYgaW4gZW51bWVyYXRlKHZpZHMpCiAgICAgICAgICAgICkKICAgICAgICAgICAgcGxheV9mcm9tLmFwcGVuZChsaW5lX25hbWUpCiAgICAgICAgICAgIHBsYXlfdXJsLmFwcGVuZChlcHMpCiAgICAgICAgcmV0dXJuIHsibGlzdCI6IFt7InZvZF9pZCI6IHNpZCwgInZvZF9uYW1lIjogc3RyKHMuZ2V0KCJzZXJpZXNfbmFtZSIpIG9yICIiKSwgInZvZF9waWMiOiBzdHIocy5nZXQoInNlcmllc19jb3ZlciIpIG9yICIiKSwgInZvZF95ZWFyIjogIiIsICJ2b2RfYXJlYSI6ICIiLCAidm9kX2RpcmVjdG9yIjogIiIsICJ2b2RfYWN0b3IiOiAiLCIuam9pbihhY3RvcnMpLCAidm9kX2NvbnRlbnQiOiBzdHIocy5nZXQoInNlcmllc19pbnRybyIpIG9yICIiKSwgInZvZF9yZW1hcmtzIjogc3RyKHMuZ2V0KCJlcGlzb2RlX3JpZ2h0X3RleHQiKSBvciAiIiksICJ2b2RfcGxheV9mcm9tIjogIiQkJCIuam9pbihwbGF5X2Zyb20pLCAidm9kX3BsYXlfdXJsIjogIiQkJCIuam9pbihwbGF5X3VybCl9XX0KICAgIGRlZiBwbGF5ZXJDb250ZW50KHNlbGYsIGZsYWcsIGlkLCB2aXBGbGFncz1Ob25lKToKICAgICAgICAjIOS7jue6v+i3r+WQje+8iGZsYWfvvIzlpoLigJznuqLmnpzotoXmuIUv57qi5p6c6auY5riF4oCd77yJ5LiO6ZuGIHRva2VuIOWPjOi3r+ino+aekOa4heaZsOW6puOAggogICAgICAgICMgdG9rZW4g5bey5pivICdoZy1lcGlzb2RlLXYxOjxxPjo8dmlkPifvvIxmbGFnIOeUqOS6juaXp+Wjs+WPquS8oOe6v+i3r+WQjeaXtuWFnOW6leOAggogICAgICAgIHRva2VuX3EsIHZpZCA9IF9zcGxpdF9lcGlzb2RlX3Rva2VuKGlkKQogICAgICAgIGxpbmVfcSA9ICIxMDgwIgogICAgICAgIGZvciBuYW1lX2tleSwgY2FuZGlkYXRlX3EgaW4gX1FVQUxJVFlfTElORV9OQU1FX1RPX1EuaXRlbXMoKToKICAgICAgICAgICAgaWYgbmFtZV9rZXkgaW4gc3RyKGZsYWcgb3IgIiIpOgogICAgICAgICAgICAgICAgbGluZV9xID0gY2FuZGlkYXRlX3EKICAgICAgICAgICAgICAgIGJyZWFrCiAgICAgICAgcSA9IGxpbmVfcSBpZiB0b2tlbl9xID09ICIxMDgwIiBhbmQgc3RyKGZsYWcpIGVsc2UgdG9rZW5fcQogICAgICAgIHEgPSBxIGlmIHEgaW4gX1FVQUxJVFlfTElORV9OQU1FX1RPX1EgZWxzZSAiMTA4MCIKICAgICAgICBpZiBub3Qgc3RyKHZpZCkuaXNkaWdpdCgpOgogICAgICAgICAgICByZXR1cm4gewogICAgICAgICAgICAgICAgInBhcnNlIjogMSwKICAgICAgICAgICAgICAgICJqeCI6IDAsCiAgICAgICAgICAgICAgICAicGxheVVybCI6ICIiLAogICAgICAgICAgICAgICAgInVybCI6IFNJVEUgKyAiLyIsCiAgICAgICAgICAgICAgICAiaGVhZGVyIjogeyJVc2VyLUFnZW50IjogVUF9LAogICAgICAgICAgICB9CiAgICAgICAgIyDnuqLmnpzmjInorr7lpIfpmZDmtYHvvJrmr4/mrKHor7fmsYLmkq3mlL7pg73nu5nkuIDlr7nlhajmlrDorr7lpIfmoIfor4bvvIwKICAgICAgICAjIOS/neivgeesrCAyIOmbhuOAgeesrCA1IOmbhuWQhOiHqumDveaYr+ayoeiiq+mZkOa1gei/h+eahOW5suWHgOiuvuWkh+OAggogICAgICAgIHRyeToKICAgICAgICAgICAgX2ZyZXNoX2RpZCwgX2ZyZXNoX2lpZCA9IF9uZXdfZGV2aWNlX3BhaXIoCiAgICAgICAgICAgICAgICBhdm9pZD0oc2VsZi5kZXZpY2VfaWQsIHNlbGYuaW5zdGFsbF9pZCkpCiAgICAgICAgICAgIHNlbGYuZGV2aWNlX2lkLCBzZWxmLmluc3RhbGxfaWQgPSBfZnJlc2hfZGlkLCBfZnJlc2hfaWlkCiAgICAgICAgZXhjZXB0IEV4Y2VwdGlvbjoKICAgICAgICAgICAgcGFzcwogICAgICAgICMgT0vlvbHop4YgLyDlpJrmlbDlo7PvvJrlv4XpobvotbAgZ2V0UHJveHlVcmzvvIjpgJrluLjlt7LluKYgZG89cHnvvInvvIzkuI3opoHopobnm5YgZG8KICAgICAgICBwcm94eSA9ICIiCiAgICAgICAgdHJ5OgogICAgICAgICAgICBpZiBoYXNhdHRyKHNlbGYsICJnZXRQcm94eVVybCIpOgogICAgICAgICAgICAgICAgcHJveHkgPSAoc2VsZi5nZXRQcm94eVVybCgpIG9yICIiKS5zdHJpcCgpCiAgICAgICAgZXhjZXB0IEV4Y2VwdGlvbjoKICAgICAgICAgICAgcHJveHkgPSAiIgogICAgICAgIGlmIHByb3h5OgogICAgICAgICAgICBzZXAgPSAiJiIgaWYgIj8iIGluIHByb3h5IGVsc2UgIj8iCiAgICAgICAgICAgICMg5L+d55WZ5aOz6Ieq5bim55qEIGRvPXB577yM5Y+q6L+95Yqg5Lia5Yqh5Y+C5pWw5LiO5riF5pmw5bqm57q/6LevCiAgICAgICAgICAgIHVybCA9IHByb3h5ICsgc2VwICsgdXJsZW5jb2RlKAogICAgICAgICAgICAgICAgewogICAgICAgICAgICAgICAgICAgICJ2aWQiOiB2aWQsCiAgICAgICAgICAgICAgICAgICAgInEiOiBxLAogICAgICAgICAgICAgICAgICAgICJoZyI6ICJjZW5jIiwKICAgICAgICAgICAgICAgICAgICAiZGlkIjogc2VsZi5kZXZpY2VfaWQgb3IgIiIsCiAgICAgICAgICAgICAgICAgICAgImlpZCI6IHNlbGYuaW5zdGFsbF9pZCBvciAiIiwKICAgICAgICAgICAgICAgIH0KICAgICAgICAgICAgKQogICAgICAgICAgICByZXR1cm4gewogICAgICAgICAgICAgICAgInBhcnNlIjogMCwKICAgICAgICAgICAgICAgICJqeCI6IDAsCiAgICAgICAgICAgICAgICAicGxheVVybCI6ICIiLAogICAgICAgICAgICAgICAgInVybCI6IHVybCwKICAgICAgICAgICAgICAgICJoZWFkZXIiOiB7CiAgICAgICAgICAgICAgICAgICAgIlVzZXItQWdlbnQiOiBNRURJQV9VQSwKICAgICAgICAgICAgICAgICAgICAiUmVmZXJlciI6ICJodHRwczovL25vdmVsLnNuc3Nkay5jb20vIiwKICAgICAgICAgICAgICAgIH0sCiAgICAgICAgICAgIH0KICAgICAgICAjIOWkh+eUqO+8muacrOacuiBSYW5nZSDmtYHvvIhGb25nTWkg5pu05Y+L5aW977yJCiAgICAgICAgdHJ5OgogICAgICAgICAgICBwb3J0ID0gX3N0YXJ0X3N0cmVhbV9zZXJ2ZXIoKQogICAgICAgIGV4Y2VwdCBFeGNlcHRpb246CiAgICAgICAgICAgIHBvcnQgPSAwCiAgICAgICAgaWYgcG9ydDoKICAgICAgICAgICAgcXVlcnkgPSB1cmxlbmNvZGUoCiAgICAgICAgICAgICAgICB7CiAgICAgICAgICAgICAgICAgICAgInZpZCI6IHZpZCwKICAgICAgICAgICAgICAgICAgICAicSI6IHEsCiAgICAgICAgICAgICAgICAgICAgImRpZCI6IHNlbGYuZGV2aWNlX2lkIG9yICIiLAogICAgICAgICAgICAgICAgICAgICJpaWQiOiBzZWxmLmluc3RhbGxfaWQgb3IgIiIsCiAgICAgICAgICAgICAgICB9CiAgICAgICAgICAgICkKICAgICAgICAgICAgcmV0dXJuIHsKICAgICAgICAgICAgICAgICJwYXJzZSI6IDAsCiAgICAgICAgICAgICAgICAiangiOiAwLAogICAgICAgICAgICAgICAgInBsYXlVcmwiOiAiIiwKICAgICAgICAgICAgICAgICJ1cmwiOiAiaHR0cDovLzEyNy4wLjAuMTolZC9oZy5tcDQ/JXMiICUgKHBvcnQsIHF1ZXJ5KSwKICAgICAgICAgICAgICAgICJoZWFkZXIiOiB7IlVzZXItQWdlbnQiOiBVQX0sCiAgICAgICAgICAgIH0KICAgICAgICByZXR1cm4gewogICAgICAgICAgICAicGFyc2UiOiAxLAogICAgICAgICAgICAiangiOiAwLAogICAgICAgICAgICAicGxheVVybCI6ICIiLAogICAgICAgICAgICAidXJsIjogU0lURSArICIvIiwKICAgICAgICAgICAgImhlYWRlciI6IHsiVXNlci1BZ2VudCI6IFVBfSwKICAgICAgICB9CgoKICAgIGRlZiBwcm94eShzZWxmLCBwYXJhbSk6CiAgICAgICAgIiIi6YOo5YiG5aOz6LCD55SoIHByb3h5IOiAjOS4jeaYryBsb2NhbFByb3h544CCIiIiCiAgICAgICAgcmV0dXJuIHNlbGYubG9jYWxQcm94eShwYXJhbSkKCiAgICBkZWYgbG9jYWxQcm94eShzZWxmLCBwYXJhbSk6CiAgICAgICAgIiIi5aOz5pys5Zyw5Luj55CG77ya5LyY5YWI6K+757yT5a2Y77yb5peg5Y6f55SfIEFFUyDml7bpgb/lhY3kuIDkuIrmnaXlsLHop6MgMTA4MCDmlbTpm4blr7zoh7TotoXml7blpLHotKXjgIIiIiIKICAgICAgICBpbXBvcnQgdHJhY2ViYWNrCiAgICAgICAgcGFyYW0gPSBwYXJhbSBvciB7fQogICAgICAgIHZpZCA9IHN0cigKICAgICAgICAgICAgcGFyYW0uZ2V0KCJ2aWQiKQogICAgICAgICAgICBvciBwYXJhbS5nZXQoImlkIikKICAgICAgICAgICAgb3IgcGFyYW0uZ2V0KCJtZWRpYUlkIikKICAgICAgICAgICAgb3IgIiIKICAgICAgICApLnN0cmlwKCkKICAgICAgICBpZiBub3QgdmlkIG9yIG5vdCBzdHIodmlkKS5pc2RpZ2l0KCk6CiAgICAgICAgICAgIGZvciBfa2V5LCB2YWx1ZSBpbiBwYXJhbS5pdGVtcygpOgogICAgICAgICAgICAgICAgdGV4dCA9IHN0cih2YWx1ZSBvciAiIikuc3RyaXAoKQogICAgICAgICAgICAgICAgaWYgdGV4dC5pc2RpZ2l0KCkgYW5kIGxlbih0ZXh0KSA+PSAxMDoKICAgICAgICAgICAgICAgICAgICB2aWQgPSB0ZXh0CiAgICAgICAgICAgICAgICAgICAgYnJlYWsKICAgICAgICBpZiBub3QgdmlkOgogICAgICAgICAgICByZXR1cm4gWzQwMCwgInRleHQvcGxhaW47IGNoYXJzZXQ9dXRmLTgiLCBiIm1pc3NpbmcgdmlkIl0KCiAgICAgICAgdHJ5OgogICAgICAgICAgICBjZmcgPSB7CiAgICAgICAgICAgICAgICAiZGV2aWNlX2lkIjogc3RyKHBhcmFtLmdldCgiZGlkIikgb3Igc2VsZi5kZXZpY2VfaWQgb3IgIiIpLAogICAgICAgICAgICAgICAgImluc3RhbGxfaWQiOiBzdHIocGFyYW0uZ2V0KCJpaWQiKSBvciBzZWxmLmluc3RhbGxfaWQgb3IgIiIpLAogICAgICAgICAgICB9CiAgICAgICAgICAgIHVzZXJfcSA9IHN0cihwYXJhbS5nZXQoInEiKSBvciBwYXJhbS5nZXQoInF1YWxpdHkiKSBvciAiIikuc3RyaXAoKQogICAgICAgICAgICAjIOacieWOn+eUnyBBRVPvvJrkvJjlhYggMTA4MO+8m+e6ryBQeXRob24gQUVTIOW+iOaFou+8muWFiCA3MjAg5L+d6K+B6IO95pKt77yM5YaN5bCd6K+V5pu06auYCiAgICAgICAgICAgIGlmIHVzZXJfcToKICAgICAgICAgICAgICAgIG9yZGVyID0gW3VzZXJfcSwgIjEwODAiLCAiNzIwIiwgIjQ4MCIsICIzNjAiXQogICAgICAgICAgICBlbGlmIF9hZXNfaXNfZmFzdCgpOgogICAgICAgICAgICAgICAgb3JkZXIgPSBbIjEwODAiLCAiNzIwIiwgIjQ4MCIsICIzNjAiXQogICAgICAgICAgICBlbHNlOgogICAgICAgICAgICAgICAgb3JkZXIgPSBbIjcyMCIsICI0ODAiLCAiMTA4MCIsICIzNjAiXQogICAgICAgICAgICAjIGRlZHVwZQogICAgICAgICAgICBzZWVuX3EgPSBzZXQoKQogICAgICAgICAgICBxdWFscyA9IFtdCiAgICAgICAgICAgIGZvciBxIGluIG9yZGVyOgogICAgICAgICAgICAgICAgaWYgcSBhbmQgcSBub3QgaW4gc2Vlbl9xOgogICAgICAgICAgICAgICAgICAgIHNlZW5fcS5hZGQocSkKICAgICAgICAgICAgICAgICAgICBxdWFscy5hcHBlbmQocSkKCiAgICAgICAgICAgICMg57yT5a2Y5ZG95Lit55u05o6l6L+U5Zue44CC55So5oi35oyH5a6a57q/6Lev5riF5pmw5bqmKHVzZXJfcSnml7bvvIzlj6rorqTor6XmuIXmmbDluqbnvJPlrZjvvIwKICAgICAgICAgICAgIyDkuI3og73lm57pgIDlkb3kuK3lhbblroPmuIXmmbDluqbnvJPlrZjvvIjlkKbliJnor7fmsYI0ODDkvJrmi7/liLAzNjDlhoXlrrnvvInjgIIKICAgICAgICAgICAgaWYgdXNlcl9xOgogICAgICAgICAgICAgICAgcHJpbWFyeSA9IFt1c2VyX3FdCiAgICAgICAgICAgIGVsc2U6CiAgICAgICAgICAgICAgICBwcmltYXJ5ID0gcXVhbHMKICAgICAgICAgICAgZm9yIHEgaW4gcHJpbWFyeToKICAgICAgICAgICAgICAgIGNhY2hlZCA9IF9oZ19jYWNoZV9nZXQodmlkLCBxKQogICAgICAgICAgICAgICAgaWYgY2FjaGVkOgogICAgICAgICAgICAgICAgICAgIHJldHVybiBbMjAwLCAidmlkZW8vbXA0IiwgY2FjaGVkXQoKICAgICAgICAgICAgbGFzdF9lcnIgPSBOb25lCiAgICAgICAgICAgICMg6K6+5aSH6L2u5o2i77ya5LiA5Y+w6K6+5aSH5Y+q5pS+5LiA5qyh5Y+W5rWB77yM5aSx6LSl5bCx5o2i5LiL5LiA5Y+w5bmy5YeA6K6+5aSH6YeN6K+VCiAgICAgICAgICAgIGZvciBkZXZfaWR4LCAoZGV2X2RpZCwgZGV2X2lpZCkgaW4gZW51bWVyYXRlKAogICAgICAgICAgICAgICAgICAgIF9kZXZpY2VfY2FuZGlkYXRlcyhwYXJhbSwgMykpOgogICAgICAgICAgICAgICAgZGV2X2NmZyA9IHsiZGV2aWNlX2lkIjogZGV2X2RpZCwgImluc3RhbGxfaWQiOiBkZXZfaWlkfQogICAgICAgICAgICAgICAgdHJ5OgogICAgICAgICAgICAgICAgICAgIG1vZGVsID0gX3ZpZGVvX21vZGVsKHZpZCwgZGV2X2NmZykKICAgICAgICAgICAgICAgIGV4Y2VwdCBFeGNlcHRpb24gYXMgbW9kZWxfZXJyOgogICAgICAgICAgICAgICAgICAgIGxhc3RfZXJyID0gKCJ2aWRlb19tb2RlbCBmYWlsZWQgZGV2IyVkICVzIgogICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICUgKGRldl9pZHggKyAxLCBtb2RlbF9lcnIpKQogICAgICAgICAgICAgICAgICAgIGNvbnRpbnVlCiAgICAgICAgICAgICAgICByb3dzID0gX3ZpZGVvX2xpc3RfZnJvbV9tb2RlbChtb2RlbCkKICAgICAgICAgICAgICAgIGlmIG5vdCByb3dzOgogICAgICAgICAgICAgICAgICAgIGxhc3RfZXJyID0gImVtcHR5IHZpZGVvIGxpc3QgZGV2IyVkIiAlIChkZXZfaWR4ICsgMSkKICAgICAgICAgICAgICAgICAgICBjb250aW51ZQoKICAgICAgICAgICAgICAgIGZvciB3YW50ZWQgaW4gcXVhbHM6CiAgICAgICAgICAgICAgICAgICAgdHJ5OgogICAgICAgICAgICAgICAgICAgICAgICBjYWNoZWQgPSBfaGdfY2FjaGVfZ2V0KHZpZCwgd2FudGVkKQogICAgICAgICAgICAgICAgICAgICAgICBpZiBjYWNoZWQ6CiAgICAgICAgICAgICAgICAgICAgICAgICAgICByZXR1cm4gWzIwMCwgInZpZGVvL21wNCIsIGNhY2hlZF0KCiAgICAgICAgICAgICAgICAgICAgICAgIF8sIGl0ZW0gPSBfc2VsZWN0X3F1YWxpdHkocm93cywgd2FudGVkKQogICAgICAgICAgICAgICAgICAgICAgICB1cmwgPSBfbWVkaWFfdXJsKGl0ZW0pCiAgICAgICAgICAgICAgICAgICAgICAgIHNwYWRlID0gX3NwYWRlX3ZhbHVlKGl0ZW0pCiAgICAgICAgICAgICAgICAgICAgICAgIGlmIG5vdCB1cmwgb3Igbm90IHNwYWRlOgogICAgICAgICAgICAgICAgICAgICAgICAgICAgbGFzdF9lcnIgPSAibWlzc2luZyB1cmwvc3BhZGUgcT0lcyIgJSB3YW50ZWQKICAgICAgICAgICAgICAgICAgICAgICAgICAgIGNvbnRpbnVlCiAgICAgICAgICAgICAgICAgICAgICAgIHRyeToKICAgICAgICAgICAgICAgICAgICAgICAgICAgIGtleV9zZWVkID0gX2tleV9zZWVkX2Zyb21fbW9kZWwobW9kZWwpCiAgICAgICAgICAgICAgICAgICAgICAgICAgICBpZiBrZXlfc2VlZDoKICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICB1cmwgPSBfZGVjcnlwdF9zcGFkZV91cmwodXJsLCBrZXlfc2VlZCkKICAgICAgICAgICAgICAgICAgICAgICAgZXhjZXB0IEV4Y2VwdGlvbjoKICAgICAgICAgICAgICAgICAgICAgICAgICAgIHBhc3MKCiAgICAgICAgICAgICAgICAgICAgICAgIGRsX3RpbWVvdXQgPSAxNTAgaWYgX2Flc19pc19mYXN0KCkgZWxzZSA5MAogICAgICAgICAgICAgICAgICAgICAgICBtZWRpYV9oZWFkZXJzID0gewogICAgICAgICAgICAgICAgICAgICAgICAgICAgIlVzZXItQWdlbnQiOiBNRURJQV9VQSwKICAgICAgICAgICAgICAgICAgICAgICAgICAgICJSZWZlcmVyIjogImh0dHBzOi8vbm92ZWwuc25zc2RrLmNvbS8iLAogICAgICAgICAgICAgICAgICAgICAgICB9CiAgICAgICAgICAgICAgICAgICAgICAgIHRyeToKICAgICAgICAgICAgICAgICAgICAgICAgICAgIGJvZHkgPSBfbXVsdGlfZG93bmxvYWQoCiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgdXJsLAogICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIGhlYWRlcnM9bWVkaWFfaGVhZGVycywKICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICB0aW1lb3V0PWRsX3RpbWVvdXQsCiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgd29ya2Vycz00IGlmIF9hZXNfaXNfZmFzdCgpIGVsc2UgMywKICAgICAgICAgICAgICAgICAgICAgICAgICAgICkKICAgICAgICAgICAgICAgICAgICAgICAgZXhjZXB0IEV4Y2VwdGlvbiBhcyBkbF9lcnI6CiAgICAgICAgICAgICAgICAgICAgICAgICAgICBsYXN0X2VyciA9ICgiZG93bmxvYWQgZmFpbGVkIHE9JXMgZXJyPSVzIgogICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgJSAod2FudGVkLCBkbF9lcnIpKQogICAgICAgICAgICAgICAgICAgICAgICAgICAgY29udGludWUKICAgICAgICAgICAgICAgICAgICAgICAgaWYgbm90IGJvZHk6CiAgICAgICAgICAgICAgICAgICAgICAgICAgICBsYXN0X2VyciA9ICJlbXB0eSBib2R5IHE9JXMiICUgd2FudGVkCiAgICAgICAgICAgICAgICAgICAgICAgICAgICBjb250aW51ZQoKICAgICAgICAgICAgICAgICAgICAgICAgaWYgKChub3QgX2Flc19pc19mYXN0KCkpIGFuZCB3YW50ZWQgaW4gKCIxMDgwIiwgIjRrIikKICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBhbmQgbGVuKGJvZHkpID4gNDUgKiAxMDI0ICogMTAyNCk6CiAgICAgICAgICAgICAgICAgICAgICAgICAgICBsYXN0X2VyciA9ICgic2tpcCBsYXJnZSAlcyB3aXRob3V0IG5hdGl2ZSBBRVMgc2l6ZT0lcyIKICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICUgKHdhbnRlZCwgbGVuKGJvZHkpKSkKICAgICAgICAgICAgICAgICAgICAgICAgICAgIGNvbnRpbnVlCgogICAgICAgICAgICAgICAgICAgICAgICBwbGFpbiA9IGRlY3J5cHRfbXA0X2NlbmMoYm9keSwKICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIGRlcml2ZV9jb250ZW50X2tleShzcGFkZSkpCiAgICAgICAgICAgICAgICAgICAgICAgIGlmIGxlbihwbGFpbikgPCA2NCBvciAoYiJmdHlwIiBub3QgaW4gcGxhaW5bOjY0XQogICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIGFuZCBiIm1vb3YiIG5vdCBpbiBwbGFpbls6NDA5Nl0pOgogICAgICAgICAgICAgICAgICAgICAgICAgICAgbGFzdF9lcnIgPSAiYmFkIG1wNCBhZnRlciBkZWNyeXB0IHE9JXMiICUgd2FudGVkCiAgICAgICAgICAgICAgICAgICAgICAgICAgICBjb250aW51ZQogICAgICAgICAgICAgICAgICAgICAgICB0cnk6CiAgICAgICAgICAgICAgICAgICAgICAgICAgICBfaGdfY2FjaGVfcHV0KHZpZCwgd2FudGVkLCBwbGFpbikKICAgICAgICAgICAgICAgICAgICAgICAgZXhjZXB0IEV4Y2VwdGlvbjoKICAgICAgICAgICAgICAgICAgICAgICAgICAgIHBhc3MKICAgICAgICAgICAgICAgICAgICAgICAgcmV0dXJuIFsyMDAsICJ2aWRlby9tcDQiLCBwbGFpbl0KICAgICAgICAgICAgICAgICAgICBleGNlcHQgRXhjZXB0aW9uIGFzIG9uZV9lcnI6CiAgICAgICAgICAgICAgICAgICAgICAgIGxhc3RfZXJyID0gKCIlcyBxPSVzIGRldiMlZCIKICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgJSAob25lX2Vyciwgd2FudGVkLCBkZXZfaWR4ICsgMSkpCiAgICAgICAgICAgICAgICAgICAgICAgIGNvbnRpbnVlCgogICAgICAgICAgICBtc2cgPSAiaGcgbG9jYWxQcm94eSBmYWlsZWQ6ICVzIiAlIGxhc3RfZXJyCiAgICAgICAgICAgIHJldHVybiBbNTAwLCAidGV4dC9wbGFpbjsgY2hhcnNldD11dGYtOCIsIG1zZy5lbmNvZGUoInV0Zi04IildCiAgICAgICAgZXhjZXB0IEV4Y2VwdGlvbiBhcyBleGM6CiAgICAgICAgICAgIG1zZyA9ICJoZyBsb2NhbFByb3h5IGZhaWxlZDogJXNcbiVzIiAlIChleGMsIHRyYWNlYmFjay5mb3JtYXRfZXhjKCkpCiAgICAgICAgICAgIHJldHVybiBbNTAwLCAidGV4dC9wbGFpbjsgY2hhcnNldD11dGYtOCIsIG1zZy5lbmNvZGUoInV0Zi04IildCgo=").decode("utf-8")
    _hg_ns = {"__name__": "_hg_shu0"}
    exec(compile(_hg_raw, "___3_shu0.py", "exec"), _hg_ns)
    _hgmod = _tmod.SimpleNamespace(**{k: v for k, v in _hg_ns.items()
                                      if not k.startswith("__")})
    _hgmod.Spider = _hg_ns["Spider"]
    _HG_IMPORT_ERR = ""
except Exception as _e1:
    _hgmod = None
    _HG_IMPORT_ERR = "%s: %s" % (type(_e1).__name__, str(_e1)[:120])


@_register
class _Hongguo(_Src):
    id = "hongguo"
    name = "红果"

    def __init__(self):
        super().__init__()
        self._hg = None
        self._dyn_cats = None
        self._dyn_filters = None

    def _get_hg(self):
        if _hgmod is None:
            raise _SrcErr(
                "红果源未加载：请把 ___3_shu0.py 与 zhenguojian.py 放在同一目录。"
                "%s" % _HG_IMPORT_ERR)
        if self._hg is None:
            self._hg = _hgmod.Spider()
        return self._hg

    def categories(self):
        if self._dyn_cats is not None:
            return self._dyn_cats
        hg = self._get_hg()
        j = hg.homeContent(False) or {}
        cats = []
        for c in j.get("class") or []:
            tid, nm = _s(c.get("type_id")), _s(c.get("type_name"))
            if tid and nm:
                cats.append((tid, nm))
        if cats:
            self._dyn_cats = cats
            return cats
        return [("all", "短剧")]

    def extra_filters(self):
        """红果自带的二级筛选组（主题/背景/设定/时间），list 格式。"""
        if self._dyn_filters is not None:
            return self._dyn_filters
        try:
            hg = self._get_hg()
            f = hg.homeContent(False).get("filters") or {}
            for _tid0, groups in f.items():
                if isinstance(groups, list) and groups:
                    self._dyn_filters = [g for g in groups
                                         if isinstance(g, dict)]
                    return self._dyn_filters
        except Exception:
            pass
        return []

    def _adapt_list(self, j):
        items = []
        for v in (j.get("list") or []) if isinstance(j, dict) else []:
            sid = _s(v.get("vod_id"))
            if not sid:
                continue
            items.append(_vod_item(self.id, sid, v.get("vod_name"),
                                   v.get("vod_pic"), v.get("vod_remarks"),
                                   v.get("vod_content")))
        pg = j.get("page", 1) if isinstance(j, dict) else 1
        try:
            pg = max(1, int(pg))
        except Exception:
            pg = 1
        pcount = j.get("pagecount", 1) if isinstance(j, dict) else 1
        try:
            pcount = max(1, int(pcount))
        except Exception:
            pcount = 1
        return items, pg < pcount

    def cat(self, catid, pg):
        return self.cat_ex(catid, pg, {})

    def cat_ex(self, catid, pg, ext):
        """带红果二级筛选透传的分类（ext 含 topic/background/setting/time）。"""
        hg = self._get_hg()
        tid = _s(catid) or "all"
        hg_ext = {}
        if isinstance(ext, dict):
            for k, v in ext.items():
                if _s(k) == "cat":
                    continue
                v = _s(v)
                if v and v not in ("", "all", "0"):
                    hg_ext[_s(k)] = v
        j = hg.categoryContent(tid, pg, False, hg_ext)
        return self._adapt_list(j)

    def detail(self, sid):
        hg = self._get_hg()
        j = hg.detailContent([_s(sid)])
        lst = j.get("list") or [] if isinstance(j, dict) else []
        if not lst:
            raise _SrcErr("红果未返回详情")
        v = lst[0]
        # 多清晰度线路（$$$ 分隔），取第一条（超清），proxy 会自动降级
        urls = _s(v.get("vod_play_url")).split("$$$")
        eps = urls[0] if urls else ""
        chapters = []
        for part in eps.split("#"):
            if "$" not in part:
                continue
            t, token = part.split("$", 1)
            token = token.strip()
            if token:
                chapters.append((token, t.strip() or "正片"))
        return _vod_detail(self, sid, _s(v.get("vod_name")),
                           _s(v.get("vod_pic")), _s(v.get("vod_remarks")),
                           _s(v.get("vod_content")), chapters=chapters)

    def play(self, sid, ep):
        hg = self._get_hg()
        try:
            main = _MAIN_SPIDER
            if main is not None and hasattr(main, "getProxyUrl"):
                hg.getProxyUrl = main.getProxyUrl
        except Exception:
            pass
        r = hg.playerContent("红果超清", _s(ep))
        if not isinstance(r, dict):
            raise _SrcErr("红果未返回播放地址")
        url = _s(r.get("url"))
        if not url:
            raise _SrcErr("红果未返回播放地址")
        header = r.get("header")
        if not isinstance(header, dict):
            header = {}
        return url, header

    def search(self, key, pg):
        hg = self._get_hg()
        j = hg.searchContent(key, False, str(pg))
        return self._adapt_list(j)


# ============================================================
# 饭果（西饭）— 纯 JSON API，无签名
# ============================================================
@_register
class _Fanguo(_Src):
    id = "fanguo"
    name = "饭果"
    cats = [("都市", "都市"), ("甜宠", "甜宠"), ("逆袭", "逆袭"), ("战神", "战神"),
            ("古装", "古装"), ("穿越", "穿越"), ("萌宝", "萌宝")]
    BASE = "https://xifan-api-cn.youlishipin.com"

    def _list(self, keyword, pg):
        if pg > 1:
            return [], False
        url = (self.BASE + "/xifan/search/getSearchList?reqType=search&offset=0"
               "&keyword=%s&quickEngineVersion=-1&scene=" % _q(keyword or "都市"))
        j = self.sess.get_json(url, headers={"Referer": self.BASE + "/"})
        items = []
        try:
            elements = j["result"]["elements"]
        except Exception:
            elements = []
        for el in elements:
            for c in (el.get("contents") or []):
                vo = c.get("duanjuVo") or {}
                vid = _pick(vo, "duanjuId", "duanju_id", "id")
                if not vid:
                    continue
                source = _pick(vo, "source")
                sid = "%s#%s" % (vid, source)
                items.append(_vod_item(
                    self.id, sid,
                    _pick(vo, "title", "name"),
                    _pick(vo, "coverImageUrl", "cover_image_url", "cover"),
                    ("全%s集" % _pick_int(vo, "total", "totalEpisodeNum"))
                    if _pick_int(vo, "total", "totalEpisodeNum") else ""))
        return items, False

    def cat(self, catid, pg):
        return self._list(catid or "都市", pg)

    def home(self, pg):
        return self._list("都市", pg)

    def search(self, key, pg):
        items, _ = self._list(key, 1)
        return items, False

    def detail(self, sid):
        vid, _, source = sid.partition("#")
        url = (self.BASE + "/xifan/drama/getDuanjuInfo?duanjuId=%s&source=%s"
               % (_q(vid), _q(source)))
        j = self.sess.get_json(url, headers={"Referer": self.BASE + "/"})
        result = j.get("result") or {}
        eps = result.get("episodeList") or []
        chapters = []
        for i, e in enumerate(eps):
            url_ = _pick(e, "playUrl", "play_url", "videoUrl")
            if not url_:
                continue
            no = _pick_int(e, "index", "episode", "sort") or (i + 1)
            chapters.append((url_, "第%d集" % no))
        chapters.sort(key=lambda x: _ep_no(x[1]))
        info = result.get("duanjuInfo") or result
        return _vod_detail(
            self, sid, _pick(info, "title", "name", "duanjuName"),
            _pick(info, "coverImageUrl", "cover_image_url", "cover"),
            ("全%d集" % len(chapters)) if chapters else "",
            _pick(info, "desc", "description", "introduction"),
            chapters=chapters)

    def play(self, sid, ep):
        # ep 本身就是直链 playUrl（302 跳到签名 MP4，播放器跟随跳转）
        if not _s(ep).startswith("http"):
            raise _SrcErr("饭果分集地址无效")
        return _s(ep), {"Referer": self.BASE + "/"}


# ============================================================
# 星果（星星接口）— 纯 JSON API，无签名（注意是 http）
# ============================================================
@_register
class _Xingguo(_Src):
    id = "xingguo"
    name = "星果"
    cats = [("1287", "推荐一"), ("1288", "推荐二"), ("1289", "推荐三"),
            ("1290", "推荐四"), ("1291", "推荐五")]
    BASE = "http://read.api.duodutek.com"
    FIXED = {
        "productId": "2a8c14d1-72e7-498b-af23-381028eb47c0",
        "vestId": "2be070e0-c824-4d0e-a67a-8f688890cadb",
        "channel": "oppo19",
        "osType": "android",
        "version": "20",
        "token": "202509271001001446030204698626",
    }

    def _api(self, path, params):
        q = dict(self.FIXED)
        q.update(params)
        url = self.BASE + path + "?" + urllib.parse.urlencode(q)
        return self.sess.get_json(url)

    def _node(self, n):
        bid = _pick(n, "id", "bookId")
        if not bid:
            return None
        intro = _pick(n, "introduction", "desc", "description")
        sid = "%s@%s" % (bid, intro)
        heat = _pick_int(n, "heat")
        remark = (("%s万播放" % (heat / 10000)) if heat >= 10000
                  else ("%d播放" % heat)) if heat else ""
        total = _pick_int(n, "chapterCount", "total")
        if total and not remark:
            remark = "全%d集" % total
        return _vod_item(
            self.id, sid, _pick(n, "name", "title"),
            _pick(n, "icon", "cover"), remark, intro)

    def cat(self, catid, pg):
        j = self._api("/novel-api/app/pageModel/getResourceById",
                      {"resourceId": catid or "1287",
                       "pageNum": str(pg), "pageSize": "10"})
        data = j.get("data") or {}
        items = []
        for n in data.get("datalist") or []:
            v = self._node(n)
            if v:
                items.append(v)
        return items, len(items) >= 10

    def home(self, pg):
        return self.cat("1287", pg)

    def search(self, key, pg):
        j = self._api("/novel-api/basedata/book/searchBook",
                      {"key": key, "pageNum": "1", "pageSize": "20"})
        data = j.get("data") or {}
        items = []
        for n in data.get("datalist") or []:
            v = self._node(n)
            if v:
                items.append(v)
        return items, False

    def _find_urls(self, node, out):
        if isinstance(node, dict):
            for k in ("shortPlayUrl", "playUrl", "url"):
                u = node.get(k)
                if isinstance(u, str) and u.startswith("http"):
                    out.append(u)
            for k in ("shortPlayList", "chapterShortPlayVoList", "list",
                      "children"):
                v = node.get(k)
                if isinstance(v, list):
                    for x in v:
                        self._find_urls(x, out)
        elif isinstance(node, list):
            for x in node:
                self._find_urls(x, out)

    def detail(self, sid):
        bid = sid.split("@")[0]
        j = self._api("/novel-api/basedata/book/getChapterList",
                      {"bookId": bid})
        data = j.get("data")
        eps = data if isinstance(data, list) else []
        chapters = []
        title, pic, intro = "", "", ""
        for i, e in enumerate(eps):
            if not isinstance(e, dict):
                continue
            if i == 0:
                title = _pick(e, "bookName", "name", "title")
                pic = _pick(e, "icon", "cover")
                intro = _pick(e, "introduction", "desc")
            urls = []
            self._find_urls(e, urls)
            if not urls:
                continue
            no = _pick_int(e, "chapterNum", "sort", "index") or (i + 1)
            et = _pick(e, "chapterName", "name", "title") or ("第%d集" % no)
            chapters.append((urls[0], et))
        if not title:
            title = bid
        return _vod_detail(self, sid, title, pic,
                           ("全%d集" % len(chapters)) if chapters else "",
                           intro, chapters=chapters)

    def play(self, sid, ep):
        if not _s(ep).startswith("http"):
            raise _SrcErr("星果分集地址无效")
        return _s(ep), {}


# ============================================================
# 观果（围观）— 纯 JSON API；详情接口已挂（源码级确认）
# ============================================================
@_register
class _Guanguo(_Src):
    id = "guanguo"
    name = "观果"
    cats = [("", "全部")]
    BASE = "https://api.drama.9ddm.com"

    def _pub_query(self):
        ts = str(int(time.time() * 1000))[-10:]
        return {
            "version_code": "1500", "version_name": "1.5.0",
            "device_name": "Pixel 8 Pro", "device_type": "phone",
            "is_first_day": "true", "is_first_24h": "true",
            "app_launch_way": "icon",
            "default_homepage": "homepage_interaction",
            "device_owning_firm": "Google", "font_scale": "default",
            "os_type": "1", "clientInfo": _md5(ts),
        }

    def _search_api(self, subject, word, pg):
        url = (self.BASE + "/drama/home/search?"
               + urllib.parse.urlencode(self._pub_query()))
        body = {"audience": "全部", "order": "最新", "page": pg,
                "pageSize": 30, "searchWord": word, "subject": subject}
        j = self.sess.post_json(
            url, body,
            headers={"User-Agent": "okhttp/5.1.0",
                     "Referer": self.BASE + "/"})
        items = []
        data = j.get("data")
        rows = data if isinstance(data, list) else []
        for n in rows:
            if not isinstance(n, dict):
                continue
            vid = _pick(n, "oneId", "one_id", "id")
            if not vid:
                continue
            total = _pick_int(n, "episodeCount", "totalEpisodeCount")
            items.append(_vod_item(
                self.id, vid, _pick(n, "title", "name"),
                _pick(n, "horzPoster", "vertPoster", "cover"),
                ("全%d集" % total) if total else "",
                _pick(n, "intro", "description", "desc")))
        return items, len(items) >= 30

    def cat(self, catid, pg):
        return self._search_api(_s(catid), "", pg)

    def search(self, key, pg):
        return self._search_api("", key, 1)

    def detail(self, sid):
        raise _SrcErr("观果接口已改版（站点侧），暂时取不到分集，请先用其它源")

    def play(self, sid, ep):
        raise _SrcErr("观果接口已改版（站点侧），暂时无法播放，请先用其它源")


# ============================================================
# 黄果AI — JSON 目录 + HTML 详情/播放，无登录，镜像轮换
# ============================================================
@_register
class _HuangguoAI(_Src):
    id = "hgai"
    name = "黄果AI"
    cats = [("ai-duanju", "AI短剧"), ("ai-manju", "AI漫剧"),
            ("ai-huanlian", "AI换脸"), ("ai-mogai", "AI魔改")]
    MAIN = "https://huangguoai.com"
    MIRRORS = ["https://ttvoij.ediayikma.cc", "https://thu.ediayikma.cc",
               "https://pku.ediayikma.cc", "https://fdu.ediayikma.cc",
               "https://thu.agdkczeyx.cc"]

    def _gen_mirrors(self, seed, n=8):
        out = []
        for i in range(n * 2):
            if len(out) >= n:
                break
            hx = hashlib.sha256(("%s:%d" % (seed, i)).encode()).hexdigest()
            pre = hx[:6].lstrip("0123456789")
            if len(pre) < 4:
                pre = hx[6:12].lstrip("0123456789")
            pre = (pre + "xxxxxx")[:6]
            if len(pre) >= 4:
                out.append("https://%s.ediayikma.cc" % pre)
        return out

    def _bases(self, path=""):
        bases = [self.MAIN] + self.MIRRORS
        bases += self._gen_mirrors(self.MAIN + path)
        seen = []
        for b in bases:
            if b not in seen:
                seen.append(b)
        return seen

    def _headers(self, base):
        return {"User-Agent": IPHONE_UA, "Referer": base + "/",
                "Accept-Language": "zh-CN,zh;q=0.9"}

    def _try_bases(self, path, timeout=12):
        last = None
        for base in self._bases(path):
            try:
                r = self.sess.fetch(base + path,
                                    headers=self._headers(base),
                                    timeout=timeout)
                if r.status == 200 and r.body:
                    return base, r
            except Exception as e:
                last = e
        raise _SrcErr("黄果AI线路暂不可用：%s" % last)

    def _walk_items(self, node, out):
        if isinstance(node, dict):
            vid = _pick(node, "id", "videoId", "video_id", "vid", "slug")
            title = _pick(node, "title", "name", "videoTitle", "video_title",
                          "videoName", "video_name")
            if vid and title:
                out.append(node)
                return
            for v in node.values():
                self._walk_items(v, out)
        elif isinstance(node, list):
            for v in node:
                self._walk_items(v, out)

    def _node(self, base, n):
        vid = _pick(n, "id", "videoId", "video_id", "vid", "slug")
        if not vid:
            m = re.search(r"/detail/([^\s\"'/?#]+)",
                          json.dumps(n, ensure_ascii=False))
            if m:
                vid = m.group(1)
        vid = _s(vid).strip().strip("/?#")
        if not vid or "/" in vid:
            vid = vid.split("/")[-1]
        if not vid:
            return None
        title = _pick(n, "title", "name", "videoTitle", "video_title",
                      "videoName", "video_name")
        if not title:
            return None
        pic = _pick(n, "cover", "coverUrl", "cover_url", "coverImage",
                    "cover_image", "image", "imageUrl", "thumbnail",
                    "poster", "posterUrl")
        total = _pick_int(n, "episode_count", "episodeCount", "total_episodes",
                          "totalEpisodes", "totalEpisode", "total_episode",
                          "episodes", "total")
        remark = _pick(n, "vod_remarks", "remark", "remarks")
        if not remark and total:
            fin = _pick(n, "is_finished")
            remark = ("全%d集" % total) if str(fin) in ("1", "true") else \
                ("更新至%d集" % total)
        score = _pick(n, "score", "rating")
        if score and "分" not in score:
            score += "分"
        return _vod_item(self.id, vid, title, _abs(base, pic), remark,
                         _pick(n, "desc", "description", "intro", "summary"))

    def cat(self, catid, pg):
        path = ("/api/videos/category/%s?sort=hot&page=%d&size=24"
                % (_q(catid or "ai-duanju"), pg))
        base, r = self._try_bases(path)
        try:
            j = json.loads(r.text())
        except Exception:
            raise _SrcErr("黄果AI目录解析失败")
        nodes = []
        self._walk_items(j, nodes)
        items, seen = [], set()
        for n in nodes:
            v = self._node(base, n)
            if v and v["vod_id"] not in seen:
                seen.add(v["vod_id"])
                items.append(v)
        return items, len(nodes) >= 24

    def home(self, pg):
        return self.cat("ai-duanju", pg)

    def _detail_page(self, sid):
        path = "/detail/%s/" % _q(sid.strip().strip("/"))
        return self._try_bases(path)

    def detail(self, sid):
        base, r = self._detail_page(sid)
        html = r.text()
        title = ""
        m = re.search(r"(?is)<title[^>]*>(.*?)</title>", html)
        if m:
            title = _strip_tags(m.group(1)).split("_")[0].split("-")[0].strip()
        desc = ""
        m = re.search(r'''(?is)<meta[^>]+(?:name|property)=["'](?:description|og:description)["'][^>]+content=["'](.*?)["']''', html)
        if m:
            desc = m.group(1)
        pic = ""
        m = re.search(r'''(?is)<meta[^>]+property=["']og:image["'][^>]+content=["'](.*?)["']''', html)
        if m:
            pic = _abs(base, m.group(1))
        anchors = re.findall(
            r'''(?is)<a\b[^>]*href=["']([^"']*/video/[^"']+)["'][^>]*>(.*?)</a>''',
            html)
        chapters = []
        seen = set()
        for href, inner in anchors:
            href = _abs(base, href.strip())
            if href in seen:
                continue
            seen.add(href)
            tm = re.search(r'''(?is)\b(?:title|aria-label)=["'](.*?)["']''', inner)
            t = _strip_tags(tm.group(1) if tm else inner)
            no = _ep_no(t, len(chapters) + 1)
            chapters.append((href, t or ("第%d集" % no)))
        chapters.sort(key=lambda x: _ep_no(x[1]))
        if not chapters:
            # 单视频页：直接提播放地址作为第 1 集
            media = self._extract_media(base, html, r.url)
            if media:
                chapters = [(media, "正片")]
        if not chapters:
            raise _SrcErr("黄果AI未找到分集")
        return _vod_detail(self, sid, title or sid, pic,
                           ("全%d集" % len(chapters)), desc,
                           chapters=chapters)

    def _extract_media(self, base, html, page_url):
        # 1) videoInitialData
        m = re.search(r'''(?is)<script[^>]+id=["']videoInitialData["'][^>]*>(.*?)</script>''', html)
        if m:
            try:
                import html as _html
                j = json.loads(_html.unescape(m.group(1)))
            except Exception:
                j = None
            if isinstance(j, dict):
                for k in ("videoSrc", "videoUrl", "playUrl"):
                    u = _pick(j, k)
                    if self._ok_media(u):
                        return self._norm_media(base, page_url, u)
                eps = j.get("epPlaySrcs")
                if isinstance(eps, dict) and eps:
                    key = _pick(j, "ep", "episode")
                    if not key:
                        pm = re.search(r"/ep-(\d+)", page_url)
                        if pm:
                            key = pm.group(1)
                    if key in eps and self._ok_media(eps[key]):
                        return self._norm_media(base, page_url, eps[key])
                    def _ek(k):
                        mm = re.search(r"(\d+)", _s(k))
                        return int(mm.group(1)) if mm else 0
                    for k in sorted(eps, key=_ek):
                        if self._ok_media(eps[k]):
                            return self._norm_media(base, page_url, eps[k])
        # 2) data-play-src
        m = re.search(r'''data-play-src=["']([^"']+)["']''', html)
        if m and self._ok_media(m.group(1)):
            return self._norm_media(base, page_url, m.group(1))
        # 3) 通用正则
        for m in re.finditer(
                r'''["']?(?:videoSrc|videoUrl|playUrl|src|url)["']?\s*[:=]\s*["']([^"']+\.(?:m3u8|mp4)[^"']*)["']''',
                html):
            return self._norm_media(base, page_url, m.group(1))
        return ""

    @staticmethod
    def _ok_media(u):
        u = _s(u)
        return bool(u) and (".m3u8" in u or ".mp4" in u)

    @staticmethod
    def _norm_media(base, page_url, u):
        import html as _html
        u = _html.unescape(_s(u)).replace("\\/", "/").strip()
        if u.startswith("//"):
            u = "https:" + u
        elif u.startswith("http://"):
            u = "https://" + u[7:]
        elif not u.startswith("https://"):
            u = _abs(page_url or base, u)
        return u

    def play(self, sid, ep):
        ep = _s(ep)
        if self._ok_media(ep):
            return ep, {"Referer": self.MAIN + "/",
                        "User-Agent": IPHONE_UA}
        # ep 是分集页面地址
        base = self.MAIN
        r = self.sess.fetch(ep, headers=self._headers(base), timeout=15)
        media = self._extract_media(base, r.text(), r.url)
        if not media:
            raise _SrcErr("黄果AI未找到播放地址")
        return media, {"Referer": ep, "User-Agent": IPHONE_UA}

    def search(self, key, pg):
        # 无服务端搜索：拉前两页按标题过滤
        items = []
        for p in (1, 2):
            try:
                rows, _ = self.cat("ai-duanju", p)
            except Exception:
                break
            for v in rows:
                if key in v["vod_name"]:
                    items.append(v)
            if len(items) >= 30:
                break
        return items[:30], False


# ============================================================
# 黄果视频 — HTML 解析，无登录
# ============================================================
@_register
class _HuangguoVideo(_Src):
    id = "hgv"
    name = "黄果视频"
    cats = [("", "全部")]
    BASE = "https://huangguo.video"

    def _headers(self):
        return {"User-Agent": IPHONE_UA, "Referer": self.BASE + "/",
                "Accept-Language": "zh-CN,zh;q=0.9"}

    def _cards(self, html):
        blocks = re.findall(
            r'''(?is)<article\b[^>]*class=["'][^"']*\bvideo-card\b[^"']*["'][^>]*>.*?</article>''',
            html)
        if not blocks:
            blocks = re.findall(r"(?is)<article\b[^>]*video-card.*?</article>",
                                html)
        items = []
        for b in blocks:
            m = re.search(
                r'''(?is)<a\b[^>]*href=["']([^"']*/(?:series|video)/([^"'/?#]+)[^"']*)["'][^>]*>''',
                b)
            if not m:
                continue
            sid = m.group(1).strip().strip("/")
            if sid.startswith("http"):
                sid = urllib.parse.urlparse(sid).path.strip("/")
            title = ""
            tm = re.search(r'''(?is)(?:title|alt|aria-label)=["']([^"']+)["']''', b)
            if tm:
                title = tm.group(1).strip()
            if not title:
                title = _strip_tags(b)[:60]
            pic = ""
            im = re.search(r'''(?is)<img\b[^>]*?(?:data-src|data-original|src)=["']([^"']+)["']''', b)
            if im:
                pic = _abs(self.BASE, im.group(1))
            desc = ""
            dm = re.search(r'''(?is)(?:data-description|description)=["']([^"']+)["']''', b)
            if dm:
                desc = dm.group(1)
            remark = ""
            rm = re.search(r'''(?is)class=["'][^"']*(?:bg-black/55|text-gold-dim)[^"']*["'][^>]*>(.*?)<''', b)
            if rm:
                remark = _strip_tags(rm.group(1))
            items.append(_vod_item(self.id, sid, title, pic, remark, desc))
        return items

    def cat(self, catid, pg):
        url = self.BASE + "/videos?page=%d" % pg
        if catid:
            url += "&category=" + _q(catid)
        html = self.sess.get_text(url, headers=self._headers())
        if _cf_blocked(html):
            raise _SrcErr("%s被 Cloudflare 拦截，换网络或稍后重试" % self.name)
        items = self._cards(html)
        return items, len(items) >= 20

    def detail(self, sid):
        if not sid.startswith(("series/", "video/")):
            sid = "series/" + sid
        url = self.BASE + "/" + sid
        html = self.sess.get_text(url, headers=self._headers())
        if _cf_blocked(html):
            raise _SrcErr("%s被 Cloudflare 拦截，换网络或稍后重试" % self.name)
        title = ""
        m = re.search(r"(?is)<title[^>]*>(.*?)</title>", html)
        if m:
            title = _strip_tags(m.group(1)).split("_")[0].split("-")[0].strip()
        pic = ""
        m = re.search(r'''(?is)<meta[^>]+property=["']og:image["'][^>]+content=["'](.*?)["']''', html)
        if m:
            pic = _abs(self.BASE, m.group(1))
        chapters = []
        if sid.startswith("series/"):
            # 新版站点结构：选集格子 series-ep-chip（href=/video/<slug>）
            box = html
            bm = re.search(r"(?is)data-episode-list(.*)", html)
            if bm:
                box = bm.group(1)[:200000]
            seen = set()
            for mm in re.finditer(
                    r'''(?is)<a\b[^>]*href=["']([^"']*/video/[^"'?#]+)["'][^>]*>(.*?)</a>''',
                    box):
                href = mm.group(1).strip()
                if href in seen:
                    continue
                seen.add(href)
                t = ""
                tm = re.search(r'''(?is)\btitle=["']([^"']+)["']''', mm.group(0))
                if tm:
                    t = tm.group(1).split("·")[0].strip()
                if not t:
                    t = _strip_tags(mm.group(2)).strip()
                chapters.append((_abs(self.BASE, href),
                                 t or ("第%d集" % (len(chapters) + 1))))
            # 兜底：老版 video-card
            if not chapters:
                blocks = re.findall(
                    r'''(?is)<article\b[^>]*class=["'][^"']*\bvideo-card\b[^"']*["'][^>]*>.*?</article>''',
                    html)
                for b in blocks:
                    m = re.search(r'''(?is)<a\b[^>]*href=["']([^"']*video/[^"']*)["']''', b)
                    if not m:
                        continue
                    hm = re.search(r'''data-hls=["']([^"']+)["']''', b)
                    media = _abs(self.BASE, hm.group(1)) if hm else ""
                    tm = re.search(r'''(?is)(?:title|alt|aria-label)=["']([^"']+)["']''', b)
                    t = tm.group(1).strip() if tm else _strip_tags(b)[:40]
                    chapters.append((media or _abs(self.BASE, m.group(1)),
                                     t or ("第%d集" % (len(chapters) + 1))))
        else:
            m = re.search(r'''data-hls=["']([^"']+)["']''', html)
            if m:
                chapters = [(_abs(self.BASE, m.group(1)), "正片")]
            if not chapters:
                m = re.search(r'''(?is)<video\b[^>]*>.*?src=["']([^"']+\.(?:m3u8|mp4)[^"']*)["']''',
                              html)
                if m:
                    chapters = [(_abs(self.BASE, m.group(1)), "正片")]
        if not chapters:
            raise _SrcErr("黄果视频未找到分集")
        chapters.sort(key=lambda x: _ep_no(x[1]))
        return _vod_detail(self, sid, title or sid, pic,
                           ("全%d集" % len(chapters)), "",
                           chapters=chapters)

    def play(self, sid, ep):
        url = _s(ep)
        if not url.startswith("http"):
            raise _SrcErr("黄果视频分集地址无效")
        # 直链
        if re.search(r"\.(?:m3u8|mp4)(?:\?|$)", url, re.I):
            return url, {"Referer": self.BASE + "/"}
        # 分集页：抓页面里的 m3u8
        html = self.sess.get_text(url, headers=self._headers())
        if _cf_blocked(html):
            raise _SrcErr("%s被 Cloudflare 拦截，换网络或稍后重试" % self.name)
        m = re.search(r'''["']([^"']*\.m3u8[^"']*)["']''', html)
        if not m:
            m = re.search(r'''https?://[^"'\s<>\\]+\.m3u8[^"'\s<>\\]*''', html)
        if not m:
            raise _SrcErr("黄果视频未找到播放地址")
        media = _abs(self.BASE, m.group(1))
        return media, {"Referer": url, "User-Agent": self._headers()["User-Agent"]}

    def search(self, key, pg):
        items = []
        for p in (1, 2):
            try:
                rows, _ = self.cat("", p)
            except Exception:
                break
            for v in rows:
                if key in v["vod_name"]:
                    items.append(v)
            if len(items) >= 30:
                break
        return items[:30], False


# ============================================================
# 河果（河马剧场）— Next.js __NEXT_DATA__ 解析
# ============================================================
@_register
class _Heguo(_Src):
    id = "heguo"
    name = "河果"
    cats = [("462", "甜宠"), ("1102", "古装仙侠"), ("1145", "现代言情"),
            ("1170", "青春"), ("585", "豪门恩怨"), ("417-464", "逆袭"),
            ("439-465", "重生"), ("1159", "系统"), ("1147", "总裁"),
            ("943", "职场商战")]
    BASE = "https://www.kuaikaw.cn"

    def _next_data(self, html):
        m = re.search(
            r'''(?is)<script[^>]+id=["']__NEXT_DATA__[^>]*>(.*?)</script>''',
            html)
        if not m:
            return {}
        try:
            j = json.loads(m.group(1))
            return j.get("props", {}).get("pageProps", {}) or {}
        except Exception:
            return {}

    def _node(self, n):
        bid = _pick(n, "bookId", "book_id", "id")
        if not bid:
            return None
        total = _pick_int(n, "totalChapterNum")
        return _vod_item(
            self.id, bid, _pick(n, "bookName", "title", "name"),
            _pick(n, "coverWap", "cover", "coverUrl"),
            ("全%d集" % total) if total else "",
            _pick(n, "introduction", "intro", "description"))

    def _parse_list_page(self, props):
        items, seen = [], set()
        buckets = []
        for k in ("bookList", "bannerList", "recommendList"):
            v = props.get(k)
            if isinstance(v, list):
                buckets += v
        for col in props.get("seoColumnVos") or []:
            if isinstance(col, dict):
                buckets += col.get("bookInfos") or []
        for n in buckets:
            if not isinstance(n, dict):
                continue
            v = self._node(n)
            if v and v["vod_id"] not in seen:
                seen.add(v["vod_id"])
                items.append(v)
        return items

    def cat(self, catid, pg):
        if pg == 1 and not catid:
            url = self.BASE + "/"
        else:
            url = "%s/browse/%s/%d" % (self.BASE, _q(catid or "462"), pg)
        html = self.sess.get_text(url, headers={"Referer": self.BASE + "/"})
        props = self._next_data(html)
        items = self._parse_list_page(props)
        pages = _pick_int(props, "pages", "page")
        more = (pg < pages) if pages else len(items) >= 20
        return items, more

    def home(self, pg):
        return self.cat("", pg)

    def detail(self, sid):
        url = "%s/drama/%s" % (self.BASE, _q(sid))
        html = self.sess.get_text(url, headers={"Referer": self.BASE + "/"})
        props = self._next_data(html)
        info = props.get("bookInfoVo") or {}
        v = self._node(info) or _vod_item(self.id, sid, sid)
        chapters = []
        for i, c in enumerate(props.get("chapterList") or []):
            if not isinstance(c, dict):
                continue
            cid = _pick(c, "chapterId", "chapter_id", "id")
            if not cid:
                continue
            no = _pick_int(c, "chapterNum", "sort", "index") or (i + 1)
            t = _pick(c, "chapterName", "title") or ("第%d集" % no)
            chapters.append((cid, t))
        chapters.sort(key=lambda x: _ep_no(x[1]))
        v.update({
            "vod_content": _pick(info, "introduction", "intro", "description"),
            "vod_remarks": ("全%d集" % len(chapters)) if chapters else "",
            "vod_play_from": self.name,
            "vod_play_url": "#".join(
                "%s$%s" % (t, _pid(self.id, sid, k)) for k, t in chapters),
        })
        return v

    def play(self, sid, ep):
        url = "%s/episode/%s/%s" % (self.BASE, _q(sid), _q(ep))
        html = self.sess.get_text(url, headers={"Referer": self.BASE + "/"})
        props = self._next_data(html)
        ci = props.get("chapterInfo") or {}
        vv = ci.get("chapterVideoVo") or {}
        media = _pick(vv, "mp4", "mp4720p", "vodMp4Url")
        if not media:
            m = re.search(r"""https?://[^"'\\\s<>]+\.(?:mp4|m3u8)[^"'\\\s<>]*""",
                          html)
            if m:
                media = m.group(0)
        if not media:
            raise _SrcErr("河果未找到播放地址")
        return _abs(self.BASE, media), {"Referer": url}

    def search(self, key, pg):
        url = self.BASE + "/seo/video/6007"
        j = self.sess.post_json(
            url, {"sourceType": 1, "keyword": key, "index": 1},
            headers={"Referer": self.BASE + "/",
                     "pname": "www.kuaikaw.cn"})
        data = j.get("data") or {}
        items = []
        for n in data.get("bookList") or []:
            v = self._node(n)
            if v:
                items.append(v)
        return items, False


# ============================================================
# MacCMS 网页类通用（花果/网果/发果/伍果；皮果被 Cloudflare 拦截）
# ============================================================

def _cf_blocked(html):
    """Cloudflare 'Just a moment' 拦截页检测"""
    if not html:
        return False
    low = html[:3000].lower()
    return ("just a moment" in low and "cloudflare" in low) or \
        "cf-challenge" in low or "cf_chl_" in low


class _MacCMS(_Src):
    BASE = ""
    UA = PC_UA

    def _headers(self, referer=None):
        return {"User-Agent": self.UA, "Referer": referer or self.BASE + "/"}

    # -- 各站覆盖 --
    def cat_url(self, catid, pg):
        raise NotImplementedError

    def detail_urls(self, sid):
        raise NotImplementedError

    def search_url(self, key, pg):
        raise NotImplementedError

    # -- 通用卡片解析（排除 /vod/type/、/vod/search/ 分类链接） --
    _DETAIL_HREF = re.compile(
        r'''(?is)<a\b[^>]*href=["']([^"']*(?:/detail/|/zywview/|/zywdetail/|/voddetail/|/xzyxvd/|/dramaDetail/|/movie/|/p/66/d/|/vod/(?!type/|search/|play/))[^"']*)["'][^>]*>(.*?)</a>''')

    def _cards(self, html, page_url):
        items, seen = [], set()
        for m in self._DETAIL_HREF.finditer(html):
            href, inner = m.group(1).strip(), m.group(2)
            if re.search(r"(?i)(app|下载|down)", _strip_tags(inner)[:20]):
                continue
            url = _abs(page_url, href)
            sid = self._sid_from_url(url)
            if not sid or sid in seen:
                continue
            # 封面：先看 <a> 标签自身（如 data-original 在锚标签上），再往前找最近的 img
            pic = ""
            start = max(0, m.start() - 3000)
            seg = html[start:m.start()]
            am0 = re.search(
                r'''(?is)\b(?:data-original|data-src|src)=["']([^"']+)["']''',
                m.group(0))
            if am0:
                pic = _abs(page_url, am0.group(1))
            if not pic:
                imgs = re.findall(
                    r'''(?is)<img\b[^>]*?(?:data-original|data-src|src)=["']([^"']+)["']''',
                    seg)
                if imgs:
                    pic = _abs(page_url, imgs[-1])
            title = ""
            tm = re.search(r'''(?is)\btitle=["']([^"']+)["']''', m.group(0))
            if tm:
                title = tm.group(1).strip()
            if not title:
                am = re.search(r'''(?is)\balt=["']([^"']+)["']''', seg[-800:])
                if am:
                    title = am.group(1).strip()
            if not title:
                title = _strip_tags(inner).strip()[:60]
            if not title:
                continue
            remark = ""
            rm = re.search(
                r'''(?is)(?:pic-text|module-item-note|imagelastChapter)[^>]*>([^<]{1,40})<''',
                seg[-1200:])
            if rm:
                remark = _strip_tags(rm.group(1))
            seen.add(sid)
            items.append(_vod_item(self.id, sid, title, pic, remark))
        return items

    def _sid_from_url(self, url):
        try:
            path = urllib.parse.urlparse(url).path
        except Exception:
            return ""
        m = re.search(r"/(\d+)\.html?$", path)
        if m:
            return m.group(1)
        m = re.search(r"/(\d+)/?$", path)
        if m:
            return m.group(1)
        m = re.search(r"/movie/([^/?#]+)", path)
        if m:
            return m.group(1)
        m = re.search(r"[?&](?:id|vid)=(\d+)", url)
        if m:
            return m.group(1)
        return ""

    # -- 通用分集解析 --
    _EP_HREF = re.compile(
        r'''(?is)<a\b[^>]*href=["']([^"']*(?:/play/|/vodplay/|/zyxplay/|/zywplay/|/xzyxplay/|/drama-play|episode_id=)[^"']*)["'][^>]*>(.*?)</a>''')

    def _episodes(self, html, page_url):
        eps, seen = [], set()
        for m in self._EP_HREF.finditer(html):
            href = _abs(page_url, m.group(1).strip())
            t = _strip_tags(m.group(2)).strip()[:40]
            if re.search(r"(?i)(app|下载|down)", t):
                continue
            if href in seen:
                continue
            seen.add(href)
            eps.append((href, t or ("第%d集" % (len(eps) + 1))))
        eps.sort(key=lambda x: _ep_no(x[1]))
        return eps

    # -- 通用播放提取 --
    def _extract_play(self, html, page_url):
        m = re.search(r"""player_aaaa\s*=\s*(\{.*?\})\s*</script>""",
                      html, re.S)
        if m:
            try:
                j = json.loads(m.group(1))
                u = _pick(j, "url")
                if u:
                    return self._norm_play(u, page_url)
            except Exception:
                pass
        m = re.search(r'''\$\.url\s*=\s*"([^"]+)"''', html)
        if m:
            return self._norm_play(m.group(1), page_url)
        m = re.search(r'''"url"\s*:\s*"([^"]+\.(?:m3u8|mp4)[^"]*)"''', html)
        if m:
            return self._norm_play(m.group(1), page_url)
        m = re.search(r"""https?://[^"'\\\s<>]+\.(?:m3u8|mp4)[^"'\\\s<>]*""",
                      html)
        if m:
            return self._norm_play(m.group(0), page_url)
        return ""

    def _norm_play(self, u, page_url):
        import html as _html
        u = _html.unescape(_s(u)).replace("\\/", "/").strip()
        # \uXXXX 转义
        try:
            u = u.encode("utf-8").decode("unicode_escape")
        except Exception:
            pass
        # 去掉 JS 拼接时带上的尾部标点（如 "...,https://x.m3u8,"）
        u = u.rstrip(" \t\r\n,;\"'")
        if not u.startswith("http"):
            u = _abs(page_url, u)
        # /p./ 或 /c1./ 伪装：取倒数第二段解码拼 index.m3u8
        if re.search(r"/[pc]1?\./", u):
            parts = [p for p in urllib.parse.urlparse(u).path.split("/")
                     if p]
            if len(parts) >= 2:
                try:
                    seg = base64.b64decode(parts[-2] + "==").decode("utf-8",
                                                                   "ignore")
                except Exception:
                    seg = ""
                if seg:
                    u = u.rsplit("/", 1)[0] + "/" + seg.strip("/") \
                        + "/index.m3u8"
        return u

    # -- 标准流程 --
    def cat(self, catid, pg):
        url = self.cat_url(_s(catid), pg)
        try:
            html = self.sess.get_text(url, headers=self._headers())
        except Exception as e:
            raise _SrcErr("%s列表打不开：%s" % (self.name, _err_text(e)))
        if _cf_blocked(html):
            raise _SrcErr("%s被 Cloudflare 拦截，换网络或稍后重试" % self.name)
        items = self._cards(html, url)
        return items, len(items) >= 10

    def home(self, pg):
        return self.cat("", pg)

    def detail(self, sid):
        last = None
        for url in self.detail_urls(sid):
            try:
                html = self.sess.get_text(url,
                                          headers=self._headers())
            except Exception as e:
                last = e
                continue
            title = ""
            m = re.search(r"(?is)<title[^>]*>(.*?)</title>", html)
            if m:
                title = _strip_tags(m.group(1)).split("_")[0].split("-")[0].strip()
            pic = ""
            m = re.search(
                r'''(?is)<img\b[^>]*?(?:data-original|data-src|src)=["']([^"']+)["'][^>]*class=["'][^"']*(?:poster|cover|vod-pic)''',
                html)
            if not m:
                m = re.search(
                    r'''(?is)<img\b[^>]*?(?:data-original|data-src|src)=["']([^"']+)["']''',
                    html)
            if m:
                pic = _abs(url, m.group(1))
            desc = ""
            m = re.search(
                r'''(?is)(?:vod-content|content|desc|detail-content)[^>]*>(.*?)</(?:div|p)>''',
                html)
            if m:
                desc = _strip_tags(m.group(1))[:2000]
            eps = self._episodes(html, url)
            if not title and not eps:
                last = _SrcErr("页面无内容")
                continue
            # 详情页分集不全时，跟进第一集播放页补全（如伍果详情页只有"立即播放"）
            if len(eps) <= 1:
                for href, _t in eps:
                    if ("/play/" in href or "/vodplay/" in href
                            or "zyxplay" in href or "zywplay" in href
                            or "xzyxplay" in href):
                        try:
                            ph = self.sess.get_text(
                                href, headers=self._headers(url), timeout=12)
                            peps = self._episodes(ph, href)
                            if len(peps) > len(eps):
                                eps = peps
                        except Exception:
                            pass
                        break
            chapters = [(href, t) for href, t in eps]
            return _vod_detail(self, sid, title or sid, pic,
                               ("全%d集" % len(chapters)) if chapters else "",
                               desc, chapters=chapters)
        raise _SrcErr("详情页打不开：%s" % _err_text(last))

    def play(self, sid, ep):
        try:
            html = self.sess.get_text(_s(ep), headers=self._headers())
        except Exception as e:
            raise _SrcErr("%s播放页打不开：%s" % (self.name, _err_text(e)))
        media = self._extract_play(html, _s(ep))
        if not media or not media.startswith("http"):
            raise _SrcErr("%s未找到播放地址" % self.name)
        return media, {"Referer": _s(ep), "User-Agent": self.UA}

    def search(self, key, pg):
        url = self.search_url(key, pg)
        html = self.sess.get_text(url, headers=self._headers())
        return self._cards(html, url), False


@_register
class _Huaguo(_MacCMS):
    id = "huaguo"
    name = "花果"
    cats = [("27", "短剧")]
    BASE = "https://www.zywest263.com"

    def cat_url(self, catid, pg):
        if pg == 1 and not catid:
            return self.BASE + "/"
        return ("%s/search.html?page=%d&searchtype=5&tid=%s&year="
                % (self.BASE, pg, _q(catid or "27")))

    def detail_urls(self, sid):
        return ["%s/zywview/%s.html" % (self.BASE, sid),
                "%s/zywdetail/%s.html" % (self.BASE, sid),
                "%s/detail/%s.html" % (self.BASE, sid)]

    def search_url(self, key, pg):
        return "%s/search.html?searchword=%s" % (self.BASE, _q(key))


@_register
class _Wangguo(_MacCMS):
    id = "wangguo"
    name = "网果"
    cats = [("", "全部")]
    BASE = "https://www.duanju2.com"

    def cat_url(self, catid, pg):
        if not catid:
            return self.BASE + "/show/duanju-----------.html"
        c = _s(catid)
        if c.endswith("---.html"):
            c = c[:-len("---.html")]
        return "%s/%s%d---.html" % (self.BASE, c, pg)

    def detail_urls(self, sid):
        return ["%s/vod/%s.html" % (self.BASE, sid),
                "%s/index.php/vod/detail/id/%s.html" % (self.BASE, sid),
                "%s/detail/%s.html" % (self.BASE, sid)]

    def search_url(self, key, pg):
        return "%s/search/%s----------1---.html" % (self.BASE, _q(key))


@_register
class _Faguo(_MacCMS):
    id = "faguo"
    name = "发果"
    cats = [("", "全部")]
    BASE = "https://www.xzyx168.com"

    def cat_url(self, catid, pg):
        if not catid:
            return "%s/xzyxvt/%szmn.html" % (self.BASE, pg)
        c = _s(catid)
        if "zmn" not in c:
            raise _SrcErr("发果分类无效")
        c = c.replace("zmn", "")
        return "%s/%s%dzmn.html" % (self.BASE, c, pg)

    def detail_urls(self, sid):
        return ["%s/xzyxvd/%s.html" % (self.BASE, sid),
                "%s/detail/%s.html" % (self.BASE, sid),
                "%s/voddetail/%s.html" % (self.BASE, sid)]

    def search_url(self, key, pg):
        return "%s/xzyxvc/%s-wdyswzqun1num.html" % (self.BASE, _q(key))


@_register
class _Wuguo(_MacCMS):
    id = "wuguo"
    name = "伍果"
    cats = [("", "全部")]
    BASE = "https://www.duanju55.com"

    def cat_url(self, catid, pg):
        if not catid:
            return self.BASE + "/"
        c = _s(catid)
        if c.endswith(".html"):
            c = c[:-5]
        return "%s%s/page/%d.html" % (self.BASE, c, pg)

    def detail_urls(self, sid):
        return ["%s/index.php/vod/detail/id/%s.html" % (self.BASE, sid),
                "%s/dramaDetail/%s.html" % (self.BASE, sid),
                "%s/detail/%s.html" % (self.BASE, sid)]

    def search_url(self, key, pg):
        return ("%s/index.php/vod/search/page/1/wd/%s.html"
                % (self.BASE, _q(key)))


# ============================================================
# 芽果（星芽接口）— 先 POST 登录拿 token
# ============================================================
@_register
class _Yaguo(_Src):
    id = "yaguo"
    name = "芽果"
    cats = [("1", "剧场"), ("9", "榜单")]
    BASE = "https://app.whjzjx.cn"
    LOGIN = "https://u.shytkjgs.com/user/v1/account/login"
    DEVICE = "24250683a3bdb3f118dff25ba4b1cba1a"

    def __init__(self):
        super().__init__()
        self._token = ""
        self._token_at = 0
        self._dyn_cats = None

    def _auth_headers(self):
        return {"authorization": self._token, "platform": "1",
                "version_name": "3.8.3.1"}

    def _token_get(self):
        if self._token and time.time() - self._token_at < 6 * 3600:
            return self._token
        j = self.sess.post_json(
            self.LOGIN, {"device": self.DEVICE},
            headers={"platform": "1"}, timeout=15)
        data = j.get("data") if isinstance(j.get("data"), dict) else {}
        token = _pick(data, "token") or _pick(j, "token")
        if not token:
            raise _SrcErr("芽果登录未返回 token")
        self._token, self._token_at = token, time.time()
        return token

    def categories(self):
        if self._dyn_cats is not None:
            return self._dyn_cats
        try:
            self._token_get()
            j = self.sess.get_json(self.BASE + "/cloud/v2/theater/classes",
                                   headers=self._auth_headers(), timeout=8)
            cats = []
            for g in j.get("data") or []:
                for c in (g.get("alg_class") or []):
                    cid = _pick(c, "id")
                    cn = _pick(c, "class_name", "name")
                    if cid and cn:
                        cats.append((cid, cn))
            if cats:
                self._dyn_cats = cats[:24]
                return self._dyn_cats
        except Exception:
            pass
        return self.cats

    def _node(self, n):
        node = n.get("theater") if isinstance(n.get("theater"), dict) else n
        vid = _pick(node, "id", "theater_id", "theater_parent_id")
        if not vid:
            return None
        total = _pick_int(node, "total", "total_num", "current_num")
        return _vod_item(
            self.id, vid, _pick(node, "title", "name"),
            _pick(node, "cover_url", "son_cover_url", "cover"),
            ("全%d集" % total) if total else "",
            _pick(node, "descrip", "introduction", "desc"))

    def cat(self, catid, pg):
        self._token_get()
        catid = catid or "1"
        if catid == "9":
            j = self.sess.get_json(
                self.BASE + "/cloud/v1/first_level_ranking/detail?id=1",
                headers=self._auth_headers())
            rows = (j.get("data") or {}).get("list") or []
            items = [v for v in (self._node(n) for n in rows) if v]
            return items, False
        url = (self.BASE + "/cloud/v2/theater/home_page?" +
               urllib.parse.urlencode(
                   {"theater_class_id": catid, "type": "1", "class2_ids": "0",
                    "page_num": str(pg), "page_size": "24"}))
        j = self.sess.get_json(url, headers=self._auth_headers())
        data = j.get("data") or {}
        rows = data.get("list") or []
        items = [v for v in (self._node(n) for n in rows) if v]
        total = _pick_int(data, "total")
        is_end = data.get("is_end")
        more = (not is_end) if is_end is not None else (
            len(rows) >= 24 if not total else pg * 24 < total)
        return items, more

    def home(self, pg):
        return self.cat("1", pg)

    def detail(self, sid):
        self._token_get()
        url = (self.BASE + "/v2/theater_parent/detail?" +
               urllib.parse.urlencode({"theater_parent_id": sid}))
        j = self.sess.get_json(url, headers=self._auth_headers())
        data = j.get("data") or {}
        eps = data.get("theaters") or []
        chapters = []
        title = _pick(data, "title", "theater_title", "name")
        pic = _pick(data, "cover_url", "cover")
        intro = _pick(data, "descrip", "introduction", "desc", "intro")
        for i, e in enumerate(eps):
            u = _pick(e, "son_video_url", "video_url")
            if not u:
                continue
            if not title:
                title = _pick(e, "theater_title", "title", "name")
            if not pic:
                pic = _pick(e, "cover_url", "son_cover_url", "cover")
            if not intro:
                intro = _pick(e, "descrip", "introduction", "desc")
            no = _pick_int(e, "num", "sort") or (i + 1)
            t = _pick(e, "son_title", "title") or ("第%d集" % no)
            chapters.append((u, t))
        chapters.sort(key=lambda x: _ep_no(x[1]))
        return _vod_detail(self, sid, title or sid, pic,
                           ("全%d集" % len(chapters)) if chapters else "",
                           intro, chapters=chapters)

    def play(self, sid, ep):
        if not _s(ep).startswith("http"):
            raise _SrcErr("芽果分集地址无效")
        return _s(ep), {"Referer": self.BASE + "/"}

    def search(self, key, pg):
        self._token_get()
        j = self.sess.post_json(self.BASE + "/v3/search", {"text": key},
                                headers=self._auth_headers())
        data = j.get("data") or {}
        rows = data.get("list") or []
        if not rows:
            th = data.get("theater") or {}
            rows = th.get("search_data") or []
        items = [v for v in (self._node(n) for n in rows) if v]
        return items, False


# ============================================================
# 剧果 — 访客鉴权 + CloudFront Cookie 播放
# ============================================================
@_register
class _Huangju(_Src):
    id = "huangju"
    name = "剧果"
    cats = [("", "全部")]
    BASE = "https://api.huangju.net"
    WEB = "https://huangju.net"

    def __init__(self):
        super().__init__()
        self._token = ""
        self._token_at = 0
        self._dyn_cats = None

    def _auth(self):
        if self._token and time.time() - self._token_at < 3600:
            return self._token
        j = self.sess.post_json(
            self.BASE + "/auth/guest",
            {"deviceId": str(uuid.uuid4())}, timeout=15)
        token = _pick(j, "token") or _pick(j.get("data") or {}, "token")
        if not token:
            raise _SrcErr("剧果访客鉴权失败")
        self._token, self._token_at = token, time.time()
        return token

    def _h(self):
        return {"Authorization": "Bearer " + self._auth(),
                "Referer": self.WEB + "/"}

    def _get(self, path, params=None):
        url = self.BASE + path
        if params:
            url += "?" + urllib.parse.urlencode(params)
        try:
            return self.sess.get_json(url, headers=self._h())
        except Exception as e:
            if "401" in str(e) or "403" in str(e):
                self._token = ""
                return self.sess.get_json(url, headers=self._h())
            raise

    def categories(self):
        if self._dyn_cats is not None:
            return self._dyn_cats
        try:
            j = self._get("/categories")
            rows = j if isinstance(j, list) else (
                j.get("data") if isinstance(j.get("data"), list)
                else j.get("categories") or [])
            cats = []
            for c in rows if isinstance(rows, list) else []:
                cid = _pick(c, "slug", "id")
                cn = _pick(c, "name", "title")
                if cid and cn:
                    cats.append((cid, cn))
            if cats:
                self._dyn_cats = [("", "全部")] + cats[:20]
                return self._dyn_cats
        except Exception:
            pass
        return self.cats

    def _node(self, n):
        vid = _pick(n, "slug", "slug_id", "drama_id", "id")
        if not vid:
            return None
        total = _pick_int(n, "episode_count", "total_episodes", "total",
                          "episodeCount")
        return _vod_item(
            self.id, vid, _pick(n, "title", "name"),
            _pick(n, "cover", "cover_url", "coverUrl", "poster"),
            ("全%d集" % total) if total else "",
            _pick(n, "desc", "description", "intro"))

    def _dramas(self, params, pg):
        params = dict(params or {})
        params["page"] = str(pg)
        j = self._get("/dramas", params)
        # 真实结构：{"total","page","pageSize","items":[]}；兼容 {"data":{...}}
        data = j.get("data") if isinstance(j.get("data"), dict) else j
        rows = []
        if isinstance(data, dict):
            rows = data.get("items") or data.get("dramas") or \
                data.get("list") or []
        elif isinstance(data, list):
            rows = data
        items = [v for v in (self._node(n) for n in rows
                             if isinstance(n, dict)) if v]
        total = _pick_int(data, "total") if isinstance(data, dict) else 0
        psize = _pick_int(data, "pageSize", "page_size") or 20
        more = (pg * psize < total) if total else len(items) >= psize
        return items, more

    def cat(self, catid, pg):
        if catid:
            return self._dramas({"category": catid}, pg)
        return self._dramas({"sort": "new"}, pg)

    def home(self, pg):
        return self._dramas({"sort": "new"}, pg)

    def search(self, key, pg):
        return self._dramas({"q": key}, 1)

    def detail(self, sid):
        j = self._get("/dramas/" + _q(sid))
        data = j.get("data") or j
        v = self._node(data) or _vod_item(self.id, sid, sid)
        v["vod_content"] = _pick(data, "desc", "description", "intro")
        chapters = []
        for e in data.get("episodes") or []:
            if not isinstance(e, dict):
                continue
            if e.get("playable") is False:
                continue
            eid = _pick(e, "id")
            if not eid:
                continue
            no = _pick_int(e, "epNo", "ep_no", "sort", "index") \
                or (len(chapters) + 1)
            t = _pick(e, "title", "name") or ("第%d集" % no)
            chapters.append((eid, t))
        chapters.sort(key=lambda x: _ep_no(x[1]))
        v.update({
            "vod_remarks": ("全%d集" % len(chapters)) if chapters else "",
            "vod_play_from": self.name,
            "vod_play_url": "#".join(
                "%s$%s" % (t, _pid(self.id, sid, k)) for k, t in chapters),
        })
        return v

    def play(self, sid, ep):
        r = self.sess.fetch(self.BASE + "/play/" + _q(ep),
                            headers=self._h(), timeout=15)
        try:
            j = json.loads(r.text())
        except Exception:
            raise _SrcErr("剧果播放接口返回无效")
        # 真实结构是裸 JSON：{"episodeId","dramaId","epNo","url",...}；兼容 data 包裹
        data = j.get("data") if isinstance(j.get("data"), dict) else j
        media = _pick(data, "url", "play_url", "video_url", "src")
        if not media:
            # 也可能是纯文本 URL
            t = r.text().strip()
            if t.startswith("http"):
                media = t.split()[0]
        if not media:
            raise _SrcErr("剧果未返回播放地址")
        ck = self.sess.cookies
        trio = "; ".join("%s=%s" % (k, ck[k]) for k in
                         ("CloudFront-Policy", "CloudFront-Signature",
                          "CloudFront-Key-Pair-Id") if k in ck)
        header = {"Referer": self.WEB + "/"}
        if trio:
            header["Cookie"] = trio
        return media, header


# ============================================================
# 猫果（七猫签名）— qm-params + MD5，参数顺序必须与原版一致
# ============================================================
@_register
class _Maoguo(_Src):
    id = "maoguo"
    name = "猫果"
    cats = [("0", "推荐")]
    STORE = "https://api-store.qmplaylet.com"
    READ = "https://api-read.qmplaylet.com"
    KEY = "d3dGiJc651gSQ8w1"
    TRACK_ID = "ec1280db127955061754851657967"
    # 与 Go 源码 duanjuMaoguoCharMap 逐字一致（'=' 不在表中，保持原样）
    CHARMAP = {
        '+': 'P', '/': 'X', '0': 'M', '1': 'U', '2': 'l', '3': 'E',
        '4': 'r', '5': 'Y', '6': 'W', '7': 'b', '8': 'd', '9': 'J',
        'A': '9', 'B': 's', 'C': 'a', 'D': 'I', 'E': '0', 'F': 'o',
        'G': 'y', 'H': '_', 'I': 'H', 'J': 'G', 'K': 'i', 'L': 't',
        'M': 'g', 'N': 'N', 'O': 'A', 'P': '8', 'Q': 'F', 'R': 'k',
        'S': '3', 'T': 'h', 'U': 'f', 'V': 'R', 'W': 'q', 'X': 'C',
        'Y': '4', 'Z': 'p', 'a': 'm', 'b': 'B', 'c': 'O', 'd': 'u',
        'e': 'c', 'f': '6', 'g': 'K', 'h': 'x', 'i': '5', 'j': 'T',
        'k': '-', 'l': '2', 'm': 'z', 'n': 'S', 'o': 'Z', 'p': '1',
        'q': 'V', 'r': 'v', 's': 'j', 't': 'Q', 'u': '7', 'v': 'D',
        'w': 'w', 'x': 'n', 'y': 'L', 'z': 'e',
    }

    def __init__(self):
        super().__init__()
        self._dyn_cats = None

    def _headers(self):
        payload = {
            "static_score": "0.8",
            "uuid": "00000000-7fc7-08dc-0000-000000000000",
            "device-id": "20250220125449b9b8cac84c2dd3d035c9052a2572f7dd0122edde3cc42a70",
            "mac": "",
            "sourceuid": "aa7de295aad621a6",
            "refresh-type": "0",
            "model": "22021211RC",
            "wlb-imei": "",
            "client-id": "aa7de295aad621a6",
            "brand": "Redmi",
            "oaid": "",
            "oaid-no-cache": "",
            "sys-ver": "12",
            "trusted-id": "",
            "phone-level": "H",
            "imei": "",
            "wlb-uid": "aa7de295aad621a6",
            "session-id": str(int(time.time() * 1000)),
        }
        b64 = base64.b64encode(
            json.dumps(payload, separators=(",", ":")).encode()).decode()
        qm = "".join(self.CHARMAP.get(c, c) for c in b64)
        sign = _md5("AUTHORIZATION=" + "app-version=10001" +
                    "application-id=com.duoduo.read" + "channel=unknown" +
                    "is-white=" + "net-env=5" + "platform=android" +
                    "qm-params=" + qm + "reg=" + self.KEY)
        return {
            "net-env": "5", "reg": "", "channel": "unknown", "is-white": "",
            "platform": "android", "application-id": "com.duoduo.read",
            "authorization": "", "app-version": "10001",
            "User-Agent": "webviewversion/0",
            "qm-params": qm, "sign": sign,
            "Accept": "application/json",
            "X-Requested-With": "com.duoduo.read",
        }

    def _get(self, base, path, sign_str):
        url = base + path + ("&" if "?" in path else "?") + "sign=" + sign_str
        return self.sess.get_json(url, headers=self._headers(), timeout=12)

    def categories(self):
        if self._dyn_cats is not None:
            return self._dyn_cats
        try:
            j = self._get(self.STORE, "/api/v1/playlet/tag/list?operation=1",
                          _md5("operation=1" + self.KEY))
            cats = []
            for c in (j.get("data") or {}).get("list") or []:
                cid = _pick(c, "tag_id", "id")
                cn = _pick(c, "tag_name", "name", "title")
                if cid and cn:
                    cats.append((cid, cn))
            if cats:
                self._dyn_cats = cats[:24]
                return self._dyn_cats
        except Exception:
            pass
        return self.cats

    def _node(self, n):
        vid = _pick(n, "playlet_id", "playletId", "id")
        if not vid:
            return None
        total = _pick_int(n, "total_episode_num", "totalEpisodeNum", "total")
        tags = n.get("tags") or n.get("tag_list") or []
        cat = ",".join(_s(t) for t in tags if _s(t))[:60]
        v = _vod_item(
            self.id, vid, _pick(n, "title", "playlet_name", "name"),
            _pick(n, "image_link", "imageLink", "cover", "cover_url"),
            ("全%d集" % total) if total else "",
            _pick(n, "intro", "description", "desc"))
        if cat:
            v["vod_remarks"] = (v["vod_remarks"] + " " + cat).strip()
        return v

    def cat(self, catid, pg):
        catid = _s(catid) or "0"
        if not catid.isdigit():
            catid = "0"
        if pg > 1:
            sign = _md5("next_id=%doperation=1playlet_privacy=1tag_id=%s%s"
                        % (pg, catid, self.KEY))
            path = ("/api/v1/playlet/index?tag_id=%s&playlet_privacy=1"
                    "&operation=1&next_id=%d" % (catid, pg))
        else:
            sign = _md5("operation=1playlet_privacy=1tag_id=%s%s"
                        % (catid, self.KEY))
            path = ("/api/v1/playlet/index?tag_id=%s&playlet_privacy=1"
                    "&operation=1" % catid)
        j = self._get(self.STORE, path, sign)
        rows = (j.get("data") or {}).get("list") or []
        items = [v for v in (self._node(n) for n in rows) if v]
        more = len(items) > 0 if pg > 1 else False
        return items, more

    def home(self, pg):
        return self.cat("0", pg)

    def detail(self, sid):
        sign = _md5("playlet_id=" + sid + self.KEY)
        j = self._get(self.READ, "/player/api/v1/playlet/info?playlet_id="
                      + _q(sid), sign)
        data = j.get("data") or {}
        v = self._node(data) or _vod_item(self.id, sid, sid)
        v["vod_content"] = _pick(data, "intro", "description", "desc")
        chapters = []
        for i, e in enumerate(data.get("play_list") or []):
            u = _pick(e, "video_url", "videoUrl", "url")
            if not u:
                continue
            no = _pick_int(e, "sort", "episode", "index") or (i + 1)
            t = _pick(e, "title", "name") or ("第%d集" % no)
            chapters.append((u, t))
        chapters.sort(key=lambda x: _ep_no(x[1]))
        v.update({
            "vod_remarks": ("全%d集" % len(chapters)) if chapters else "",
            "vod_play_from": self.name,
            "vod_play_url": "#".join(
                "%s$%s" % (t, _pid(self.id, sid, k)) for k, t in chapters),
        })
        return v

    def play(self, sid, ep):
        if not _s(ep).startswith("http"):
            raise _SrcErr("猫果分集地址无效")
        return _s(ep), {}

    def search(self, key, pg):
        # 顺序敏感：extend,page,read_preference,track_id,wd
        sign = _md5("extend=page=1read_preference=0track_id=%swd=%s%s"
                    % (self.TRACK_ID, key, self.KEY))
        path = ("/api/v1/playlet/search?extend=&page=1&wd=%s"
                "&read_preference=0&track_id=%s" % (_q(key), self.TRACK_ID))
        j = self._get(self.STORE, path, sign)
        data = j.get("data") or {}
        rows = data.get("list") or []
        items = [v for v in (self._node(n) for n in rows) if v]
        return items, False


# ============================================================
# 黄豆 — 自定义加密传输（HMAC-SHA256 派生 AES-256-CBC 密钥）
# ============================================================
@_register
class _Huangdou(_Src):
    id = "huangdou"
    name = "黄豆"
    cats = [("", "全部")]
    HOSTS = ["https://tideember.cc", "https://xqjurgek.top"]
    PLATFORM_KEY = "7961beb44246e3012ce228d6b5ced05a"
    VERSION = "2.0.0"

    def __init__(self):
        super().__init__()
        self._host = self.HOSTS[0]
        self._device_id = binascii.hexlify(os.urandom(16)).decode()
        self._session_id = binascii.hexlify(os.urandom(16)).decode()

    @staticmethod
    def _uuid_like():
        h = binascii.hexlify(os.urandom(16)).decode()
        return "%s-%s-%s-%s-%s" % (h[:8], h[8:12], h[12:16], h[16:20], h[20:])

    def _key(self, rid):
        msg = binascii.unhexlify(rid.replace("-", ""))
        return hmac.new(self.PLATFORM_KEY.encode(), msg,
                        hashlib.sha256).digest()

    def _call(self, path, data):
        path = "/" + path.lstrip("/")
        rid = self._uuid_like()
        key = self._key(rid)
        iv = os.urandom(16)
        plain = json.dumps({"token": "", "deviceId": self._device_id,
                            "data": data},
                           ensure_ascii=False).encode("utf-8")
        gz = gzip.compress(plain)
        body = iv + _aes_cbc_encrypt(gz, key, iv)
        ts = str(int(time.time()))
        sign_raw = "Dart|%s|%s|%s|%s" % (self._session_id, rid, ts, path)
        sign = hashlib.sha256(sign_raw.encode()).hexdigest() + "-" + ts
        headers = {
            "User-Agent": ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
                           "AppleWebKit/537.36 (KHTML, like Gecko) "
                           "Chrome/120 Safari/537.36"),
            "Accept": "*/*",
            "Content-Type": "application/octet-stream",
            "version": self.VERSION,
            "deviceType": "web",
            "requestId": rid,
            "sessionId": self._session_id,
            "time": ts,
            "sign": sign,
        }
        last = None
        for host in [self._host] + [h for h in self.HOSTS
                                    if h != self._host]:
            headers["Origin"] = host
            headers["Referer"] = host + "/home"
            try:
                r = self.sess.fetch(host + "/api" + path, method="POST",
                                    headers=headers, data=body, timeout=20)
            except Exception as e:
                last = e
                continue
            if r.status < 200 or r.status >= 300:
                last = _SrcErr("黄豆 HTTP %d" % r.status)
                continue
            self._host = host
            return self._decode(r.body, key)
        raise _SrcErr("黄豆接口不可用：%s" % last)

    def _decode(self, blob, key):
        blob = bytes(blob).strip()
        if blob.startswith((b"{", b"[")):
            try:
                decoded = json.loads(blob.decode("utf-8", "ignore"))
            except Exception:
                raise _SrcErr("黄豆响应 JSON 无效")
        else:
            if len(blob) < 32:
                raise _SrcErr("黄豆响应过短")
            iv, ct = blob[:16], blob[16:]
            try:
                plain = _aes_cbc_decrypt(ct, key, iv)
            except Exception as e:
                raise _SrcErr("黄豆响应解密失败：%s" % e)
            if plain[:2] == b"\x1f\x8b":
                try:
                    plain = gzip.decompress(plain)
                except Exception:
                    raise _SrcErr("黄豆响应解压失败")
            try:
                decoded = json.loads(plain.decode("utf-8", "ignore"))
            except Exception:
                raise _SrcErr("黄豆响应 JSON 无效")
        if isinstance(decoded, dict):
            status = _pick(decoded, "status")
            if status and status != "y":
                code = _pick(decoded, "errorCode", "error_code", "code")
                msg = _pick(decoded, "msg", "message", "error") or status
                if code in ("813004", "813005", "813006", "813103") or \
                        "preview" in code:
                    raise _SrcErr("黄豆：该内容需 VIP/试看限制")
                raise _SrcErr("黄豆接口拒绝：%s" % msg)
        return decoded

    def _rows(self, decoded):
        if isinstance(decoded, list):
            return decoded
        if isinstance(decoded, dict):
            data = decoded.get("data")
            if isinstance(data, list):
                return data
            if isinstance(data, dict):
                for k in ("list", "items", "data"):
                    v = data.get(k)
                    if isinstance(v, list):
                        return v
            for k in ("list", "items", "data"):
                v = decoded.get(k)
                if isinstance(v, list):
                    return v
        return []

    def _node(self, n):
        vid = _pick(n, "id", "drama_id")
        if vid.startswith("rp_"):
            vid = vid[3:]
        if not vid:
            return None
        total = _pick_int(n, "episode_count")
        remark = _pick(n, "update_label", "corner")
        if not remark and total:
            remark = "全%d集" % total
        return _vod_item(
            self.id, vid, _pick(n, "name", "title", "t"),
            _pick(n, "img_y", "img_x", "img", "cover", "pic"),
            remark, _pick(n, "description", "summary"))

    def cat(self, catid, pg):
        j = self._call("/drama/list", {"page": str(pg), "page_size": "30"})
        rows = self._rows(j)
        items = [v for v in (self._node(n) for n in rows) if v]
        return items, len(items) >= 30

    def search(self, key, pg):
        j = self._call("/drama/list", {"keywords": key, "page": "1",
                                       "page_size": "50"})
        rows = self._rows(j)
        items = [v for v in (self._node(n) for n in rows) if v]
        return items, False

    def detail(self, sid):
        j = self._call("/drama/detail", {"id": sid})
        data = j.get("data") if isinstance(j, dict) else None
        node = data if isinstance(data, dict) else (j if isinstance(j, dict)
                                                   else {})
        rid = _pick(node, "id", "drama_id")
        if rid.startswith("rp_"):
            rid = rid[3:]
        if rid and rid != sid:
            raise _SrcErr("黄豆详情与请求剧集不符")
        v = self._node(node) or _vod_item(self.id, sid, sid)
        v["vod_content"] = _pick(node, "description", "summary")
        chapters = []
        for i, e in enumerate(node.get("episodes") or []):
            no = _pick_int(e, "seq", "episode", "ep") or (i + 1)
            t = _pick(e, "name", "title") or ("第%d集" % no)
            chapters.append((str(no), t))
        if not chapters:
            total = _pick_int(node, "episode_count", "free_episodes")
            chapters = [(str(i + 1), "第%d集" % (i + 1))
                        for i in range(min(total, 3000))]
        v.update({
            "vod_remarks": ("全%d集" % len(chapters)) if chapters else "",
            "vod_play_from": self.name,
            "vod_play_url": "#".join(
                "%s$%s" % (t, _pid(self.id, sid, k)) for k, t in chapters),
        })
        return v

    def _is_preview(self, data, media):
        for k in ("is_preview", "isPreview"):
            if str(data.get(k)).lower() in ("true", "1", "y"):
                return True
        for k in ("preview_m3u8", "preview_url"):
            pv = _pick(data, k)
            if pv and (not media or pv.strip() == media.strip()):
                return True
        if media:
            p = urllib.parse.urlparse(media).path.lower()
            if p.endswith("/preview.mp4") or p.endswith("/preview.m3u8") \
                    or p == "preview.mp4" or p == "preview.m3u8":
                return True
        return False

    def play(self, sid, ep):
        j = self._call("/drama/play", {"id": sid, "seq": str(ep)})
        data = j.get("data") if isinstance(j, dict) else {}
        if not isinstance(data, dict):
            data = {}
        media = _pick(data, "m3u8", "url", "play_url", "playUrl")
        if self._is_preview(data, media):
            raise _SrcErr("黄豆：该分集为 VIP 试看，不提供试看地址")
        if media:
            if not media.startswith("http"):
                media = self._host + "/" + media.lstrip("/")
            return media, {"Referer": self._host + "/home",
                           "User-Agent": PC_UA}
        # 降级直链
        url = ("%s/api/drama/hls/%s/%s/play.m3u8?line=free"
               % (self._host, _q(sid), _q(str(ep))))
        try:
            r = self.sess.fetch(url,
                                headers={"Referer": self._host + "/home"},
                                timeout=12)
            if r.body.startswith(b"#EXTM3U"):
                return url, {"Referer": self._host + "/home"}
        except Exception:
            pass
        raise _SrcErr("黄豆未返回该集播放地址")


# ============================================================
# 野果 — 配置动态发现（__NUXT_DATA__ + _nuxt/*.js），AES-CBC + 响应签名
# 配置/解码失败只重新发现并重试一次。
# ============================================================
@_register
class _Yeguo(_Src):
    id = "yeguo"
    name = "野果"
    cats = [("", "全部")]
    SITES = ["https://analyze.buxefaex.cc", "https://ygdj7.com/"]
    _PUB_FIELD = re.compile(
        r"""\b(version|mode|padding|key|iv|sign_key)\s*:\s*(?:[a-zA-Z_$][a-zA-Z0-9_$]*\(\s*)?["'`]([^"'`\\\r\n]{1,512})["'`]""")
    _IMPORT = re.compile(
        r"""(?s)import\s*\{([^{};]+)\}\s*from\s*["'`]([^"'`]+)["'`]""")

    def __init__(self):
        super().__init__()
        self._access = None
        self._lock = threading.Lock()
        self._dyn_cats = None

    # -- 发现 --
    @staticmethod
    def _pub_bytes(value):
        if "_" not in value:
            return value.encode("utf-8")
        out = bytearray()
        for part in value.split("_"):
            try:
                n = int(part)
            except Exception:
                return None
            if n < 0 or n > 255:
                return None
            out.append(n)
        return bytes(out)

    def _parse_pub_config(self, script):
        fields = {}
        for m in self._PUB_FIELD.finditer(script[:2000000]):
            fields[m.group(1)] = m.group(2)
            if len(fields) > 32:
                break
        if fields.get("version") != "v0" or fields.get("mode") != "CBC" \
                or fields.get("padding") != "Pkcs7":
            return None
        key = self._pub_bytes(fields.get("key", ""))
        iv = self._pub_bytes(fields.get("iv", ""))
        sk = self._pub_bytes(fields.get("sign_key", ""))
        if key is None or iv is None or sk is None:
            return None
        if len(key) not in (16, 24, 32) or len(iv) != 16 \
                or not (1 <= len(sk) <= 128):
            return None
        return key, iv, sk

    def _api_base(self, html):
        m = re.search(
            r'''(?is)<script[^>]*id=["']__NUXT_DATA__["'][^>]*>(.*?)</script>''',
            html)
        if not m:
            return ""
        try:
            table = json.loads(m.group(1))
        except Exception:
            return ""
        if not isinstance(table, list) or len(table) > 100000:
            return ""
        for item in table:
            if isinstance(item, dict) and "apiBaseURL" in item:
                ref = item["apiBaseURL"]
                if isinstance(ref, int) and 0 <= ref < len(table):
                    base = table[ref]
                    if isinstance(base, str) and base:
                        return base.rstrip("/")
        return ""

    def _script_url(self, page_url, ref):
        try:
            page = urllib.parse.urlparse(page_url)
            u = urllib.parse.urljoin(page_url, ref)
            p = urllib.parse.urlparse(u)
        except Exception:
            return ""
        if p.netloc != page.netloc:
            return ""
        if not p.path.startswith("/_nuxt/") or \
                not p.path.endswith(".js"):
            return ""
        return u.split("#")[0]

    def _discover_at(self, site):
        r = self.sess.fetch(site + "/", headers={"Referer": site + "/"},
                            timeout=15)
        html = r.text()
        page_url = r.url or (site + "/")
        api_base = self._api_base(html)
        if not api_base:
            raise _SrcErr("野果页面未提供有效的接口入口")
        entry = ""
        for m in re.finditer(
                r'''(?is)<script[^>]*type=["']module["'][^>]*src=["']([^"']+)["']''',
                html):
            entry = self._script_url(page_url, m.group(1))
            if entry:
                break
        if not entry:
            raise _SrcErr("野果页面未提供接口配置脚本")
        entry_body = self.sess.fetch(entry, headers={"Referer": page_url},
                                     timeout=15).text()
        imports = self._IMPORT.findall(entry_body)
        # 无逗号的 import 优先
        imports.sort(key=lambda x: ("," in x[0]))
        seen = set()
        for _names, ref in imports:
            if len(ref) > 2400:
                continue
            url = self._script_url(entry, ref)
            if not url or url in seen or len(seen) >= 20:
                continue
            seen.add(url)
            try:
                body = self.sess.fetch(url, headers={"Referer": page_url},
                                       timeout=15).text()
            except Exception:
                continue
            cfg = self._parse_pub_config(body)
            if cfg:
                key, iv, sk = cfg
                ident = binascii.hexlify(os.urandom(16)).decode()
                return {"base": api_base, "site": site, "key": key,
                        "iv": iv, "sign_key": sk, "ident": ident}
        raise _SrcErr("野果接口配置已变化，暂时无法解码")

    def _discover(self):
        with self._lock:
            if self._access:
                return self._access
            last = None
            for site in self.SITES:
                try:
                    acc = self._discover_at(site)
                    self._access = acc
                    return acc
                except Exception as e:
                    last = e
            raise _SrcErr("野果线路暂不可用：%s" % last)

    def _drop_access(self):
        with self._lock:
            self._access = None

    # -- 签名/解码 --
    @staticmethod
    def _sign(envelope, sign_key):
        pieces = []
        for name in sorted(envelope.keys()):
            if name in ("sign", "_ver"):
                continue
            v = envelope[name]
            if v is None:
                continue
            if isinstance(v, bool):
                f = "true" if v else "false"
            elif isinstance(v, (int, float)):
                f = str(v)
            elif isinstance(v, str):
                f = v
            else:
                raise _SrcErr("野果响应签名格式无效")
            if name == "data":
                f = f.replace(" ", "+")
            pieces.append(name + "=" + f)
        d1 = hashlib.sha256(
            ("&".join(pieces)).encode("utf-8") + sign_key).hexdigest()
        return hashlib.md5(d1.encode("utf-8")).hexdigest()

    def _decode(self, body, acc):
        try:
            env = json.loads(body.decode("utf-8", "ignore"))
        except Exception:
            raise _SrcErr("野果响应 JSON 无效")
        if not isinstance(env, dict):
            raise _SrcErr("野果响应格式无效")
        sig = _s(env.get("sign"))
        if sig:
            try:
                exp = self._sign(env, acc["sign_key"])
            except _SrcErr:
                raise
            except Exception:
                raise _SrcErr("野果响应验签失败")
            if exp != sig.lower():
                raise _SrcErr("野果响应验签失败")
        data = env.get("data")
        if isinstance(data, str):
            b64 = data.replace(" ", "+").strip()
            try:
                ct = base64.b64decode(b64)
            except Exception:
                raise _SrcErr("野果数据 Base64 无效")
            if not ct or len(ct) % 16:
                raise _SrcErr("野果数据长度无效")
            try:
                plain = _aes_cbc_decrypt(ct, acc["key"], acc["iv"])
            except Exception:
                raise _SrcErr("野果数据解密失败")
            try:
                payload = json.loads(plain.decode("utf-8", "ignore"))
            except Exception:
                raise _SrcErr("野果数据 JSON 无效")
        else:
            payload = env
        if not isinstance(payload, dict):
            raise _SrcErr("野果返回的数据格式无效")
        if _s(payload.get("status")) == "-1":
            raise _SrcErr("野果当前内容需要站源授权")
        if _s(payload.get("status")) != "1":
            raise _SrcErr("野果请求未完成：%s"
                          % (_s(payload.get("msg"))[:90] or "请稍后重试"))
        data = payload.get("data")
        if not isinstance(data, dict):
            raise _SrcErr("野果返回的数据格式无效")
        return data

    def _call(self, route, params):
        last = None
        for attempt in range(2):
            acc = self._discover()
            values = {"bundleId": "com.pwa.mater", "version": "1.3.2",
                      "oauth_type": "web", "language": "zh", "via": "pwa",
                      "oauth_id": acc["ident"], "trace_id": acc["ident"],
                      "token": ""}
            values.update(params or {})
            method = "GET" if route == "/api/home/contentOptions" else "POST"
            url = acc["base"] + route
            headers = {"User-Agent": PC_UA,
                       "Accept": "application/json, text/plain, */*",
                       "Origin": acc["site"], "Referer": acc["site"] + "/"}
            try:
                if method == "GET":
                    url += "?" + urllib.parse.urlencode(values)
                    r = self.sess.fetch(url, headers=headers, timeout=20)
                else:
                    headers["Content-Type"] = \
                        "application/x-www-form-urlencoded"
                    r = self.sess.fetch(
                        url, method="POST", headers=headers,
                        data=urllib.parse.urlencode(values).encode(),
                        timeout=20)
                if r.status < 200 or r.status >= 300:
                    raise _SrcErr("野果 HTTP %d" % r.status)
                return self._decode(r.body, acc)
            except _SrcErr as e:
                last = e
                msg = str(e)
                if "验签失败" in msg or "解密失败" in msg:
                    self._drop_access()
                    continue
                raise
            except Exception as e:
                last = e
                raise _SrcErr("野果请求失败：%s" % e)
        raise _SrcErr("野果解码失败：%s" % last)

    # -- 业务 --
    def _node(self, n, site):
        vid = _pick(n, "video_id", "id")
        if not vid or not vid.isdigit():
            return None
        title = _pick(n, "title")
        if not title:
            return None
        total = _pick_int(n, "episode_count", "total_episode", "total")
        return _vod_item(
            self.id, vid, title,
            _abs(site + "/", _pick(n, "cover", "cover_url", "image")),
            ("全%d集" % total) if total else "",
            _pick(n, "desc", "description", "intro"))

    def categories(self):
        if self._dyn_cats is not None:
            return self._dyn_cats
        try:
            data = self._call("/api/home/contentOptions", None)
            vf = data.get("video_filter")
            if isinstance(vf, dict):
                cats, seen = [], set()
                for field, f in vf.items():
                    if not isinstance(f, dict):
                        continue
                    for o in f.get("list") or []:
                        if not isinstance(o, dict):
                            continue
                        val, nm = _pick(o, "value"), _pick(o, "name")
                        if not val or val == "0" or not nm or \
                                len(nm) > 48:
                            continue
                        cid = "%s:%s" % (field, val)
                        if cid in seen:
                            continue
                        seen.add(cid)
                        cats.append((cid, nm))
                if cats:
                    self._dyn_cats = cats[:30]
                    return self._dyn_cats
        except Exception:
            pass
        return self.cats

    def cat(self, catid, pg):
        params = {"page": str(pg), "limit": "20"}
        if catid and ":" in catid:
            f, v = catid.split(":", 1)
            params[f] = v
        data = self._call("/api/theater/exploreList", params)
        rows = data.get("list") or []
        site = (self._access or {}).get("site", self.SITES[0])
        items = [v for v in (self._node(n, site) for n in rows
                             if isinstance(n, dict)) if v]
        total = _pick_int(data, "total", "total_count", "totalCount")
        limit = _pick_int(data, "limit", "page_size", "pageSize",
                          "per_page", "perPage") or 20
        more = (pg < (total + limit - 1) // limit) if total \
            else len(items) >= limit
        hm = data.get("has_more")
        if hm is not None:
            more = str(hm).lower() in ("1", "true", "y")
        return items, more

    def home(self, pg):
        return self.cat("", pg)

    def search(self, key, pg):
        data = self._call("/api/search/result",
                          {"keyword": key, "tab": "video",
                           "page": str(pg), "limit": "20"})
        rows = data.get("list") or []
        site = (self._access or {}).get("site", self.SITES[0])
        items = [v for v in (self._node(n, site) for n in rows
                             if isinstance(n, dict)) if v]
        return items, False

    def detail(self, sid):
        if not sid.isdigit():
            raise _SrcErr("野果剧集 ID 无效")
        row = self._call("/api/playlet/detail",
                         {"video_id": sid, "id": sid, "episode_id": "0",
                          "related_limit": "0"})
        site = (self._access or {}).get("site", self.SITES[0])
        if _pick(row, "video_id", "id") != sid:
            raise _SrcErr("野果详情与请求剧集不符")
        v = self._node(row, site) or _vod_item(self.id, sid, sid)
        v["vod_content"] = _pick(row, "desc", "description", "intro")
        chapters = []
        seen_ids, seen_no = set(), set()
        for e in row.get("episodes") or []:
            if not isinstance(e, dict):
                continue
            if str(e.get("is_adv")).lower() in ("1", "true", "y"):
                continue
            eid = _pick(e, "id")
            try:
                no = int(_s(e.get("sort")))
            except Exception:
                no = 0
            if not eid or not eid.isdigit() or no < 1 or \
                    eid in seen_ids or no in seen_no:
                continue
            seen_ids.add(eid)
            seen_no.add(no)
            t = _pick(e, "title") or ("第%d集" % no)
            chapters.append((eid, t, no))
        chapters.sort(key=lambda x: x[2])
        v.update({
            "vod_remarks": ("全%d集" % len(chapters)) if chapters else "",
            "vod_play_from": self.name,
            "vod_play_url": "#".join(
                "%s$%s" % (t, _pid(self.id, sid, k))
                for k, t, _n in chapters),
        })
        return v

    def play(self, sid, ep):
        if not _s(ep).isdigit():
            raise _SrcErr("野果分集 ID 无效")
        row = self._call("/api/playlet/play",
                         {"playlet_id": sid, "video_id": sid,
                          "episode_id": _s(ep)})
        if _pick(row, "playlet_id") != sid or _pick(row, "id") != _s(ep):
            raise _SrcErr("野果返回的播放地址与请求分集不符")
        if str(row.get("is_adv")).lower() in ("1", "true", "y"):
            raise _SrcErr("野果未返回该集正片")
        media = _pick(row, "video_url", "video_url_h265")
        if not media:
            raise _SrcErr("野果未返回播放地址")
        site = (self._access or {}).get("site", self.SITES[0])
        return _abs(site + "/", media), {"Referer": site + "/"}


# ============================================================
# 黄果旧版 — AES 加密 JSON API + 访客 token 会话
# ============================================================
@_register
class _Hgcf(_Src):
    id = "hgcf"
    name = "黄果旧版"
    cats = [("", "推荐")]
    API_DEFAULT = "https://dr6skssi3nxbk.cloudfront.net"
    FRONTEND = "https://d2pypzndaqisk.cloudfront.net"
    CDN_DEFAULT = "https://sjljsla.lkkwip.cn"
    X_UA = ("BuildID=com.abc.Butterfly;SysType=ios;DevID=00000000000000000000000000000;"
            "Ver=1.0.0;DevType=iPhone;DeviceBrand=APPLE;DeviceModel=iPhone;"
            "SystemName=iOS;SystemVersion=18.7;Terminal=1;IsH5=1;"
            "Sid=00000000000000000000000000000000")

    def __init__(self):
        super().__init__()
        self._api = ""
        self._proto = None       # (interfaceKey, paramKey, paramIV)
        self._proto_at = 0
        self._device_id = ""
        self._token = ""
        self._lock = threading.Lock()
        self._dyn_cats = None
        self._fallback_tab = ""

    # -- 会话 --
    def _frontend_script(self):
        html = self.sess.get_text(self.FRONTEND + "/",
                                  headers={"User-Agent": IPHONE_UA},
                                  timeout=15)
        m = re.search(r'''(?is)<script[^>]+src=["']([^"']*main-[^"']*\.js)["']''',
                      html)
        if not m:
            raise _SrcErr("黄果旧版前端脚本未找到")
        js_url = _abs(self.FRONTEND + "/", m.group(1))
        return self.sess.get_text(js_url, headers={"User-Agent": IPHONE_UA},
                                  timeout=15)

    def _discover_api(self):
        try:
            js = self._frontend_script()
        except Exception:
            return self.API_DEFAULT
        for host in re.findall(r"https://[a-z0-9]+\.cloudfront\.net", js):
            try:
                j = self.sess.get_json(host + "/api/app/ping/check",
                                       headers={"User-Agent": IPHONE_UA},
                                       timeout=8)
                if j.get("code") == 200:
                    return host
            except Exception:
                continue
        return self.API_DEFAULT

    def _protocol(self):
        with self._lock:
            if self._proto and time.time() - self._proto_at < 24 * 3600:
                return self._proto
            js = self._frontend_script()
            def val(name):
                m = re.search(r"""["']%s["']\s*[:,]\s*["']([^"'\\\r\n]+)["']"""
                              % name, js)
                return m.group(1) if m else ""
            ik, pk, piv = val("interfaceKey"), val("parameterKey"), \
                val("parameterIv")
            if not (0 < len(ik) <= 512 and len(pk) == 16 and len(piv) == 16):
                raise _SrcErr("黄果旧版接口协议已变化")
            self._proto = (ik, pk, piv)
            self._proto_at = time.time()
            return self._proto

    def _login(self):
        ik, pk, piv = self._protocol()
        payload = self._raw_request(
            "POST", "/api/app/mine/login/h5",
            {"devID": self._device_id, "sysType": "ios",
             "isAppStore": False},
            ik, pk, piv, "")
        token = _pick(payload, "token")
        if not token:
            raise _SrcErr("黄果旧版访客登录未返回令牌")
        with self._lock:
            self._token = token

    def _x_user_agent(self):
        did = self._device_id or "00000000000000000000000000000"
        return self.X_UA.replace("DevID=00000000000000000000000000000",
                                 "DevID=" + did, 1)

    def _decrypt_response(self, data_str, interface_key):
        o = base64.b64decode(data_str.strip())
        if len(o) < 12:
            raise _SrcErr("黄果旧版加密响应过短")
        i = o[:12]
        r = interface_key.encode() + i
        l = len(r) >> 1
        s = _sha256(r)[8:24]
        c = s + r[:l]
        a = r[l:] + s
        d = _sha256(c)
        f = _sha256(a)
        m = d[:8] + f[8:24] + d[24:]
        p = f[:4] + d[12:20] + f[28:]
        g = o[12:]
        if len(g) % 16:
            raise _SrcErr("黄果旧版密文未对齐")
        return _pkcs7_unpad(_aes_crypt_fast(g, m, p, False, True), )

    def _raw_request(self, method, path, params, ik, pk, piv, token):
        enc = None
        if params is not None:
            plain = json.dumps(params, ensure_ascii=False).encode("utf-8")
            enc = base64.b64encode(
                _aes_cbc_encrypt(plain, pk.encode(), piv.encode())).decode()
        url = self._api + path
        headers = {
            "Accept": "application/json",
            "temp": "test",
            "X-User-Agent": self._x_user_agent(),
            "Origin": self.FRONTEND,
            "Referer": self.FRONTEND + "/",
            "User-Agent": IPHONE_UA,
        }
        if token:
            headers["Authorization"] = token
        if method == "GET":
            if enc:
                sep = "&" if "?" in url else "?"
                url += sep + "data=" + _q(enc)
            r = self.sess.fetch(url, headers=headers, timeout=15)
        else:
            headers["Content-Type"] = "application/json"
            body = json.dumps({"data": enc},
                              ensure_ascii=False).encode("utf-8")
            r = self.sess.fetch(url, method="POST", headers=headers,
                                data=body, timeout=15)
        if r.status < 200 or r.status >= 300:
            raise _SrcErr("黄果旧版 HTTP %d" % r.status)
        try:
            env = json.loads(r.text())
        except Exception:
            raise _SrcErr("黄果旧版响应 JSON 无效")
        code = _s(env.get("code")).strip('"')
        if code not in ("", "null", "200", "0"):
            msg = _s(env.get("msg"))[:120] or "接口错误"
            err = _SrcErr("黄果旧版 API %s: %s" % (code, msg))
            err.code = code
            raise err
        data = env.get("data")
        h = env.get("hash")
        hash_on = bool(h) if isinstance(h, bool) else _s(h).lower() not in (
            "", "0", "false", "null")
        if hash_on and data:
            if not isinstance(data, str):
                raise _SrcErr("黄果旧版加密数据格式无效")
            try:
                plain = self._decrypt_response(data, ik)
            except _SrcErr:
                raise
            except Exception as e:
                raise _SrcErr("黄果旧版响应解密失败：%s" % e)
            return json.loads(plain.decode("utf-8", "ignore"))
        return data

    def _api_call(self, method, path, params=None, retry=True):
        # 确保会话
        with self._lock:
            if not self._api:
                self._api = self._discover_api()
            if not self._device_id:
                self._device_id = ("%08X%d" % (
                    random.getrandbits(32), int(time.time() * 1000)))
            api, token = self._api, self._token
        ik, pk, piv = self._protocol()
        if not token:
            self._login()
            with self._lock:
                token = self._token
        try:
            return self._raw_request(method, path, params, ik, pk, piv,
                                     token)
        except _SrcErr as e:
            if retry and getattr(e, "code", "") == "5005":
                with self._lock:
                    self._token = ""
                self._login()
                with self._lock:
                    token = self._token
                return self._raw_request(method, path, params, ik, pk, piv,
                                         token)
            raise

    # -- 业务 --
    def _fix_cover(self, pic):
        pic = _s(pic)
        if not pic or pic.startswith("http"):
            return pic
        if pic.startswith("upload/") or pic.startswith("upload_01/"):
            return "https://pic.zdmhyg.cn/" + pic
        return "https://zzzznnn.lkkwip.cn/" + pic.lstrip("/")

    def categories(self):
        if self._dyn_cats is not None:
            return self._dyn_cats
        try:
            tabs = self._api_call("GET", "/api/app/playlet-tab/all", None)
            rows = tabs.get("list") if isinstance(tabs, dict) else tabs
            cats = []
            for t in rows if isinstance(rows, list) else []:
                cid = _pick(t, "id")
                cn = _pick(t, "name")
                if cid and cn:
                    cats.append((cid, cn))
            if cats:
                self._dyn_cats = cats[:24]
                return self._dyn_cats
        except Exception:
            pass
        return self.cats

    def _node(self, n):
        vid = _pick(n, "id", "playlet_id", "videoId")
        if not vid:
            return None
        total = _pick_int(n, "totalEpisode", "total_episode", "episodeCount",
                          "episode_count", "chapterCount", "chapter_count",
                          "total", "episodes")
        return _vod_item(
            self.id, vid, _pick(n, "title", "name"),
            self._fix_cover(_pick(n, "cover", "coverUrl", "cover_url",
                                 "image", "imageUrl", "image_url", "img",
                                 "pic", "picture", "poster", "thumb",
                                 "thumbnail")),
            ("全%d集" % total) if total else "",
            _pick(n, "desc", "description", "intro", "summary"))

    def _probe_tab(self):
        """分类接口没返回时的兜底：试几个常见 tab，哪个出数据用哪个。"""
        if self._fallback_tab:
            return self._fallback_tab
        for cand in ("1", "2", "0", "hot", "new", "all"):
            try:
                data = self._api_call(
                    "GET", "/api/app/playlet/home/tab/" + _q(cand),
                    {"pageNumber": "1", "pageSize": "20", "tabSortType": "1"})
                rows = (data.get("list") if isinstance(data, dict)
                        else data) or []
                if rows:
                    self._fallback_tab = cand
                    return cand
            except Exception:
                continue
        return ""

    def cat(self, catid, pg):
        cats = self.categories()
        tab = catid or (cats[0][0] if cats else "")
        if not tab:
            tab = self._probe_tab()
        if not tab:
            raise _SrcErr("黄果旧版分类接口暂时没返回，稍后再试")
        data = self._api_call(
            "GET", "/api/app/playlet/home/tab/" + _q(tab),
            {"pageNumber": str(pg), "pageSize": "20", "tabSortType": "1"})
        rows = (data.get("list") if isinstance(data, dict) else data) or []
        items = [v for v in (self._node(n) for n in rows
                             if isinstance(n, dict)) if v]
        return items, len(items) >= 20

    def home(self, pg):
        return self.cat("", pg)

    def detail(self, sid):
        try:
            data = self._api_call("GET",
                                  "/api/app/playlet/detail/" + _q(sid), None)
        except Exception as e:
            raise _SrcErr("黄果旧版详情失败：%s" % e)
        if not isinstance(data, dict):
            raise _SrcErr("黄果旧版详情格式无效")
        v = self._node(data) or _vod_item(self.id, sid, sid)
        v["vod_content"] = _pick(data, "desc", "description", "intro")
        chapters = data.get("chapters")
        if not chapters:
            try:
                chapters = self._api_call(
                    "GET", "/api/app/playlet-chapter/list/" + _q(sid), None)
            except Exception:
                chapters = []
        if isinstance(chapters, dict):
            chapters = chapters.get("list") or []
        eps = []
        for i, c in enumerate(chapters or []):
            if not isinstance(c, dict):
                continue
            vu = _pick(c, "videoUrl", "video_url", "playUrl", "url")
            if not vu:
                continue
            t = _pick(c, "title", "name") or ("第%d集" % (i + 1))
            eps.append((vu, t))
        v.update({
            "vod_remarks": ("全%d集" % len(eps)) if eps else "",
            "vod_play_from": self.name,
            "vod_play_url": "#".join(
                "%s$%s" % (t, _pid(self.id, sid, k)) for k, t in eps),
        })
        return v

    def play(self, sid, ep):
        ep = _s(ep)
        with self._lock:
            api, token = self._api, self._token
        if ep.startswith("http"):
            media = ep
        else:
            media = ("%s/api/app/vid/h5/m3u8/%s?%s"
                     % (api, _q(ep.strip("/")),
                        urllib.parse.urlencode(
                            {"token": token, "c": self.CDN_DEFAULT})))
        return media, {"Referer": self.FRONTEND + "/",
                       "User-Agent": IPHONE_UA}

    def search(self, key, pg):
        # 无服务端搜索：拉首页按标题过滤
        items = []
        try:
            rows, _ = self.cat("", 1)
        except Exception:
            rows = []
        for v in rows:
            if key in v["vod_name"]:
                items.append(v)
        return items[:30], False

# Spider 主类（FongMi 5.6.4 / Chaquopy 合约：全部返回 dict）
# ============================================================
from concurrent.futures import ThreadPoolExecutor

_MAIN_SPIDER = None


class Spider(BaseSpider):

    def getName(self):
        return "真果鉴·全站源"

    def init(self, extend=""):
        self.extend = _s(extend)
        global _MAIN_SPIDER
        _MAIN_SPIDER = self
        return {}

    def destroy(self):
        return {}

    # ---------- 本地代理（红果 CENC 解密通道） ----------
    def localProxy(self, param):
        try:
            src = _find_src("hongguo")
            if src is not None and _hgmod is not None:
                hg = src._get_hg()
                if hasattr(hg, "localProxy"):
                    return hg.localProxy(param or {})
        except Exception as e:
            return [500, "text/plain; charset=utf-8",
                    ("proxy error: %s" % e).encode("utf-8")]
        return [404, "text/plain; charset=utf-8", b"no proxy"]

    def proxy(self, param):
        return self.localProxy(param)

    def isVideoFormat(self, url):
        u = _s(url).lower()
        return (".m3u8" in u or ".mp4" in u or ".flv" in u or ".ts" in u
                or ".mkv" in u)

    def manualVideoCheck(self):
        return False

    # ---------- 首页 ----------
    def _source_cats(self, src):
        try:
            if hasattr(src, "categories"):
                cats = src.categories()
                if cats:
                    return cats[:24]
        except Exception:
            pass
        return src.cats or [("", "推荐")]

    def homeContent(self, filter=False):
        # 两级分类（照 ___3_shu0.py 的写法）：
        #   大分类=站源名（顶部 tab）；子分类=各源自己的分类，走 filters 二级筛选栏。
        #   filters 必须是 list 格式：{tid: [{"key","name","value":[{"n","v"}]}]}，
        #   dict 格式 FongMi 不认。
        cats_map = {}
        with ThreadPoolExecutor(max_workers=8) as ex:
            futs = {ex.submit(self._source_cats, src): src
                    for src in _SOURCES}
            for fut in futs:
                try:
                    cats_map[futs[fut].id] = fut.result(timeout=20)
                except Exception:
                    cats_map[futs[fut].id] = futs[fut].cats or [("", "推荐")]
        classes, filters = [], {}
        for src in _SOURCES:
            tid = _tid(src.id, "")
            classes.append({"type_id": tid, "type_name": src.name})
            subs = cats_map.get(src.id) or src.cats or [("", "推荐")]
            opts, seen_n = [], set()
            for cid, cname in subs[:30]:
                if not cname or cname in seen_n:
                    continue
                seen_n.add(cname)
                opts.append({"n": cname, "v": cid})
            groups = []
            if opts:
                groups.append({"key": "cat", "name": "分类", "value": opts})
            # 部分源（如红果）自带更多筛选组，追加
            if hasattr(src, "extra_filters"):
                try:
                    for g in src.extra_filters() or []:
                        if isinstance(g, dict) and g.get("value"):
                            groups.append(g)
                except Exception:
                    pass
            if groups:
                filters[tid] = groups
        vods = []
        try:
            items, _ = _SOURCES[0].home(1)
            vods = items[:24]
        except Exception:
            pass
        return {"class": classes, "list": vods, "filters": filters}

    def homeVideoContent(self):
        try:
            items, _ = _SOURCES[0].home(1)
            return {"list": items[:24]}
        except Exception:
            return {"list": []}

    # ---------- 分类 ----------
    def categoryContent(self, tid, pg="1", filter=False, extend=None):
        src_id, _ = _split_tid(tid)
        src = _find_src(src_id)
        if not src:
            return {"list": [], "page": 1, "pagecount": 1, "limit": 20,
                    "total": 0}
        try:
            pg = max(1, int(pg))
        except Exception:
            pg = 1
        # 子分类来自 filters 二级筛选：extend = {"cat": <cid>}（照 ___3_shu0.py）
        cat = ""
        ext = extend
        if isinstance(ext, str) and ext:
            try:
                ext = json.loads(ext)
            except Exception:
                ext = {}
        if isinstance(ext, dict):
            cat = _s(ext.get("cat", ""))
        if cat:
            # 兼容 FongMi 传显示名而不是 id 的情况
            try:
                cats = self._source_cats(src)
                if cat not in set(c[0] for c in cats):
                    by_name = dict((c[1], c[0]) for c in cats)
                    cat = by_name.get(cat, "")
            except Exception:
                pass
        if not cat:
            try:
                cats = self._source_cats(src)
                cat = cats[0][0] if cats else ""
            except Exception:
                cat = ""
        # 部分源（如红果）需要完整 extend 透传二级筛选
        ext_dict = ext if isinstance(ext, dict) else {}
        try:
            if hasattr(src, "cat_ex"):
                items, more = src.cat_ex(cat, pg, ext_dict)
            else:
                items, more = src.cat(cat, pg)
            if items:
                src.last_err = ""
        except Exception as e:
            src.last_err = _err_text(e)
            items, more = [], False
        if not items and not more:
            # 空列表别给白板：插一张说明卡，点进去能看原因
            note = src.last_err or "该分类当前没有数据"
            items = [_vod_item(src.id, "@@err@@",
                               "⚠ %s：%s" % (src.name, note))]
            more = False
        return {"list": items or [], "page": pg,
                "pagecount": 9999 if more else pg,
                "limit": 20, "total": 999999 if more else len(items or [])}

    # ---------- 详情 ----------
    def detailContent(self, ids):
        did = ids[0] if ids else ""
        src_id, sid = _split_did(did)
        src = _find_src(src_id)
        if not src:
            return {"list": []}
        if sid == "@@err@@":
            vod = _vod_detail(src, sid, "%s 暂时不可用" % src.name, "", "",
                              src.last_err or "该源当前没有返回数据",
                              chapters=())
            vod["vod_id"] = did
            return {"list": [vod]}
        try:
            vod = src.detail(sid)
        except _SrcErr as e:
            vod = _vod_detail(src, sid, "加载失败", "",
                              "", "原因：%s" % e, chapters=())
            vod["vod_id"] = did
        except Exception as e:
            vod = _vod_detail(src, sid, "加载失败", "",
                              "", "原因：%s" % type(e).__name__,
                              chapters=())
            vod["vod_id"] = did
        return {"list": [vod]}

    # ---------- 搜索（多源并行） ----------
    def _search_one(self, src, key):
        try:
            items, _ = src.search(key, 1)
            return items or []
        except Exception:
            return []

    def searchContent(self, key, quick=False, pg="1"):
        key = _s(key).strip()
        if not key:
            return {"list": []}
        try:
            pg = int(pg)
        except Exception:
            pg = 1
        if pg > 1:
            return {"list": []}
        out = []
        with ThreadPoolExecutor(max_workers=8) as ex:
            futs = {ex.submit(self._search_one, src, key): src
                    for src in _SOURCES}
            for fut in futs:
                try:
                    items = fut.result(timeout=30)
                except Exception:
                    continue
                src = futs[fut]
                for v in (items or [])[:12]:
                    # 搜索结果名前缀站源，便于区分
                    if not v["vod_name"].startswith(src.name):
                        v["vod_name"] = "[%s] %s" % (src.name,
                                                     v["vod_name"])
                    out.append(v)
                if len(out) >= 160:
                    break
        return {"list": out}

    # ---------- 播放 ----------
    def playerContent(self, flag, id, vipFlags=None):
        src_id, sid, ep = _split_pid(id)
        src = _find_src(src_id)
        if not src:
            return {"parse": 0, "playUrl": "", "url": "", "header": {}}
        try:
            url, header = src.play(sid, ep)
        except _SrcErr:
            return {"parse": 0, "playUrl": "", "url": "", "header": {}}
        except Exception:
            return {"parse": 0, "playUrl": "", "url": "", "header": {}}
        return {"parse": 0, "playUrl": "", "url": _s(url),
                "header": dict(header or {})}
