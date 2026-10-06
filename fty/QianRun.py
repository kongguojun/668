# -*- coding: utf-8 -*-
# 哔嘀视频(com.qianrun.musicmain) OK影视 py源  —  纯Python零依赖(自带握手, 无App/无Frida)
import json, os, time, base64, hmac, hashlib, sys, ssl, gzip, urllib.request

sys.path.append(os.path.dirname(os.path.abspath(__file__)))
try:
    from base.spider import Spider as BaseSpider
except ImportError:
    class BaseSpider:
        def __init__(self, query_params=None, t4_api=None):
            self.query_params = query_params or {}; self.t4_api = t4_api or ''; self.extend = ''
        def fetch(self, url, params=None, headers=None, cookies=None, timeout=10, **kw):
            import requests; return requests.get(url, params=params, headers=headers, cookies=cookies, timeout=timeout, verify=False)

# AES-GCM(优先 cryptography, 退 pycryptodome)
try:
    from cryptography.hazmat.primitives.ciphers.aead import AESGCM as _AESGCM
    def _enc(k, iv, pt): return _AESGCM(k).encrypt(iv, pt, None)
    def _dec(k, iv, ct): return _AESGCM(k).decrypt(iv, ct, None)
except ImportError:
    from Crypto.Cipher import AES as _AES
    def _enc(k, iv, pt):
        c = _AES.new(k, _AES.MODE_GCM, nonce=iv); ct, tag = c.encrypt_and_digest(pt); return ct + tag
    def _dec(k, iv, ct):
        c = _AES.new(k, _AES.MODE_GCM, nonce=iv); return c.decrypt_and_verify(ct[:-16], ct[-16:])

# RSA-OAEP(SHA256)
try:
    from cryptography.hazmat.primitives.asymmetric import padding
    from cryptography.hazmat.primitives import hashes as _h, serialization
    def _rsa(pubpem, data):
        pub = serialization.load_pem_public_key(pubpem.encode())
        return pub.encrypt(data, padding.OAEP(mgf=padding.MGF1(_h.SHA256()), algorithm=_h.SHA256(), label=None))
except ImportError:
    from Crypto.PublicKey import RSA as _RSA
    from Crypto.Cipher import PKCS1_OAEP as _OAEP
    from Crypto.Hash import SHA256 as _S256
    def _rsa(pubpem, data):
        return _OAEP.new(_RSA.import_key(pubpem), hashAlgo=_S256).encrypt(data)

PUBKEY = """-----BEGIN PUBLIC KEY-----
MIIBIjANBgkqhkiG9w0BAQEFAAOCAQ8AMIIBCgKCAQEA0/dbYRC/YXeptinMqQQt
CqjX5iSbQuRy5/waLLujq5R45oKHvUdU8t7Jh2npzdsgpAKcgAul/3NaTU+t/+Fp
zbDwhX94Zm3WZVx7oPDDLhRF7ay0zZWnjepTWo4/LvuuJ8IdpKgd6G/s61k6GVU8
GPGxgLnWIzLDePrhQ0eisR7SuupB1nkS4IWHMdzvqYeL77s0hKYqAwfpGf+rlC8N
hZtUSopCfnluvPooEs3FY8tmsM0DK7BOeR1UKksPNRfof5wZiaM4pvZAfs+Jfshl
0Aq1IUisKNMyh2+UxstjkZyfXcybVLEVfhVl2sx/cXdlUj6vhiMpXtQt4sQzSrpj
GwIDAQAB
-----END PUBLIC KEY-----"""
# challenge_response 用的嵌入密钥
KEY_EMB = bytes.fromhex('30623762363666373831303564663236343739313332383465386336613735333435633831396136656236353239656533613539313532323165613762633866')


class Spider(BaseSpider):
    HOST = "https://nox.app999.bidiys.com"
    UA = ("Mozilla/5.0 (iPhone; CPU iPhone OS 17_4 like Mac OS X) AppleWebKit/605.1.15 "
          "(KHTML, like Gecko) BD/2.0 Mobile/15E148 Safari/604.1")
    SIG = "FF:9B:A6:C4:F2:78:4F:71:55:D9:87:75:F0:AE:D3:0D:B2:38:11:59:64:18:8B:FE:6F:DC:D2:2C:21:31:31:C6"
    DEV = "f081e67bd8aecc69"
    DISCLAIMER = ("【免责声明】本资源由「小老虎」免费分享整理，仅供个人学习、交流与测试使用，"
                  "请于体验后 24 小时内删除；所有影视内容版权均归原版权方所有，"
                  "严禁用于任何商业用途，如有侵权请告知删除。\n\n")

    def init(self, extend=""):
        self.extend = extend or ""; self.timeout = 20
        self.aes = None; self.hmk = None; self.exp = 0
        return {"status": 0}

    def getName(self):
        return "🅿️哔嘀视频"

    def _b64(self, b): return base64.b64encode(b).decode()

    def _h0(self):
        return {"user-agent": self.UA, "content-type": "application/json",
                "x-device-id": self.DEV, "x-app-signature": self.SIG,
                "x-app-package": "com.qianrun.musicmain",
                "x-app-version-code": "2005", "x-app-version-name": "2.0.5"}

    def _http(self, path, data=None, hdr=None):
        h = self._h0()
        if hdr: h.update(hdr)
        req = urllib.request.Request(self.HOST + path, data=data, headers=h, method="POST" if data is not None else "GET")
        r = urllib.request.urlopen(req, timeout=self.timeout, context=ssl._create_unverified_context())
        raw = r.read()
        if r.headers.get("Content-Encoding") == "gzip":
            raw = gzip.decompress(raw)
        return json.loads(raw)

    def _handshake(self):
        ch = self._http("/api/captcha/rotate/init")["data"]["id"]
        H = os.urandom(32); tk = os.urandom(32)
        cr = hmac.new(KEY_EMB, (ch + "|" + self.DEV).encode(), hashlib.sha256).hexdigest()
        M = json.dumps({"temp_key": self._b64(tk), "device_id": self.DEV,
                        "challenge": ch, "challenge_response": cr},
                       separators=(",", ":")).encode()
        iv = os.urandom(12)
        gcm = self._b64(iv + _enc(H, iv, M))
        rsa = self._b64(_rsa(PUBKEY, H))
        resp = self._http("/api/sync/preferences",
                          json.dumps({"data": rsa + "|" + gcm}, separators=(",", ":")).encode())
        blob = base64.b64decode(resp["data"])
        sess = json.loads(_dec(tk, blob[:12], blob[12:]).decode("utf-8", "ignore"))
        self.aes = base64.b64decode(sess["aes_key"])
        self.hmk = base64.b64decode(sess["hmac_key"])
        self.exp = int(sess.get("expires_at") or 0)

    def _rpc(self, method, path, query="", body=""):
        if not self.aes or time.time() > self.exp - 30:
            self._handshake()
        ts = str(int(time.time() * 1000)); trace = self._b64(os.urandom(16))
        env = json.dumps({"method": method, "path": path, "query": query,
                          "headers": {"X-App-Package": "com.qianrun.musicmain", "X-App-Signature": self.SIG,
                                      "X-App-Version-Code": "2005", "X-App-Version-Name": "2.0.5"},
                          "body": body}, separators=(",", ":"), ensure_ascii=False).encode()
        iv = os.urandom(12)
        bundle = self._b64(iv + _enc(self.aes, iv, env))
        token = hmac.new(self.hmk, (bundle + ts + trace).encode(), hashlib.sha256).hexdigest()
        hdr = {"x-req-ts": ts, "x-req-id": self.DEV, "x-req-trace": trace, "x-req-token": token}
        body_bytes = json.dumps({"bundle": bundle}, separators=(",", ":")).encode()
        last = None
        for attempt in range(2):
            try:
                resp = self._http("/api/sync/push", body_bytes, hdr)
                b = base64.b64decode(resp["bundle"])
                return json.loads(_dec(self.aes, b[:12], b[12:]).decode("utf-8", "ignore"))
            except urllib.error.HTTPError as ex:
                last = ex
                if ex.code == 429:
                    time.sleep(3)
                    continue
                break
            except Exception as ex:
                last = ex
                break
        # 失败: 会话可能过期, 重新握手后重试一次
        self.aes = None
        self._handshake()
        ts = str(int(time.time() * 1000)); trace = self._b64(os.urandom(16))
        bundle = self._b64(iv + _enc(self.aes, iv, env))
        token = hmac.new(self.hmk, (bundle + ts + trace).encode(), hashlib.sha256).hexdigest()
        hdr = {"x-req-ts": ts, "x-req-id": self.DEV, "x-req-trace": trace, "x-req-token": token}
        resp = self._http("/api/sync/push", json.dumps({"bundle": bundle}, separators=(",", ":")).encode(), hdr)
        b = base64.b64decode(resp["bundle"])
        return json.loads(_dec(self.aes, b[:12], b[12:]).decode("utf-8", "ignore"))

    # ---- OK影视 接口 ----
    def homeContent(self, filter):
        classes = []; filters = {}
        try:
            d = self._rpc("GET", "/api/categories").get("data") or []
            for c in d:
                tid = str(c.get("type_id")); classes.append({"type_id": tid, "type_name": c.get("type_name")})
                fl = c.get("filters") or {}; g = []
                if fl.get("classes"): g.append({"key": "class", "name": "类型", "value": [{"n": x, "v": x} for x in fl["classes"]]})
                if fl.get("areas"): g.append({"key": "area", "name": "地区", "value": [{"n": x, "v": x} for x in fl["areas"]]})
                if fl.get("years"): g.append({"key": "year", "name": "年份", "value": [{"n": x, "v": x} for x in fl["years"]]})
                if g: filters[tid] = g
        except Exception: pass
        return {"class": classes, "filters": filters}

    def homeVideoContent(self):
        try: return {"list": self._cards("/api/category?type=1&page=1&limit=20")}
        except Exception: return {"list": []}

    def _cards(self, path):
        out = []
        try:
            d = self._rpc("GET", path)
            for v in (d.get("data") or {}).get("list", []):
                out.append({"vod_id": str(v.get("vod_id")), "vod_name": v.get("vod_name"),
                            "vod_pic": v.get("image_url") or v.get("vod_pic") or "",
                            "vod_remarks": v.get("vod_remarks") or ""})
        except Exception: pass
        return out

    def categoryContent(self, tid, pg, filter, extend):
        pg = max(1, int(pg or 1))
        lst = self._cards("/api/category?type=%s&page=%d&limit=36" % (tid, pg))
        return {"list": lst, "page": pg, "pagecount": pg + 1 if len(lst) >= 36 else pg, "limit": 36, "total": 999999}

    def searchContent(self, key, quick, pg=1):
        return {"list": []}   # 搜索需图形验证码

    def detailContent(self, ids):
        vid = ids[0] if isinstance(ids, list) else ids
        d = self._rpc("GET", "/api/videos/%s" % vid).get("data") or {}
        pf = []; pu = []
        srcs = d.get("play_sources", []) or []
        for src in srcs:
            if int(src.get("is_disabled") or 0) == 1:
                continue
            code = src.get("source_code")
            sh = src.get("headers") or {}
            try: shj = json.dumps(sh, separators=(",", ":"))
            except Exception: shj = "{}"
            nm = []
            for e in src.get("episodes", []):
                real = e.get("url", "")
                u = "%s\t%s\t%s\t%s" % (code, vid, real, shj)
                nm.append("%s$%s" % (str(e.get("name", "")).replace("$", "_"), u))
            if nm:
                pf.append(src.get("source_name") or code); pu.append("#".join(nm))
        vod = {"vod_id": vid, "vod_name": d.get("vod_name"), "vod_pic": d.get("vod_pic"),
               "type_name": d.get("type_name"), "vod_year": d.get("vod_year"), "vod_area": d.get("vod_area"),
               "vod_remarks": d.get("vod_remarks"), "vod_score": d.get("score"),
               "vod_director": d.get("vod_director"), "vod_actor": d.get("vod_actor"),
               "vod_content": self.DISCLAIMER + (d.get("vod_blurb") or "").strip(),
               "vod_play_from": "$$$".join(pf), "vod_play_url": "$$$".join(pu)}
        return {"list": [vod]}

    def playerContent(self, flag, vid, vip_flags):
        parts = (vid or "").split("\t")
        if len(parts) >= 4:
            code, v_id, real, shj = parts[0], parts[1], parts[2], "\t".join(parts[3:])
        else:
            code, v_id, real, shj = flag, "", (vid or ""), "{}"
        try: hdr = json.loads(shj) if shj else {}
        except Exception: hdr = {}
        if not hdr: hdr = {"User-Agent": self.UA}
        try:
            body = json.dumps({"id": int(v_id) if str(v_id).isdigit() else v_id, "source_code": code, "url": real})
            d = self._rpc("POST", "/api/videos/parse-url", "", body).get("data") or {}
            ph = d.get("headers")
            if ph: hdr = ph
            return {"parse": 0, "jx": 0, "url": (d.get("parsed_url") or "").strip(), "header": json.dumps(hdr, ensure_ascii=False)}
        except Exception:
            return {"parse": 0, "jx": 0, "url": "", "header": json.dumps(hdr, ensure_ascii=False)}

    def isVideoFormat(self, url): return ".m3u8" in (url or "") or ".mp4" in (url or "")
    def manualVideoCheck(self): return False
    def localProxy(self, param): return None
