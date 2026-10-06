# -*- coding: utf-8 -*-
"""
可可影视(OK影视系) py源  —  com.kkdyD12997260706.t181523 v3.5.0
全程实测逆向(抓包 + Frida Hook + so反汇编)，无一下是猜的。

接口宿主
  vcache.ybsdkl.cn   列表/详情/配置(响应体 AES-256-CBC 加密)
  vlogic.ybsdkl.cn   搜索/埋点(同上)
  vres.mppcdrr.cn    图片CDN

签名(实锤，两样本逐字节验证通过)
  sign = HMAC_SHA1(KEY, "get|{path}|{query按键名升序,未编码}|{ts}|{DEVICE}|")
  KEY  = ksggsr4tp6difdo1c3im8fqd3g        (26B, libutil.so .rodata 碎片)
  DEVICE = appId=kkdy&deviceCreatedAt=..&deviceId=..&st=2&userId=..
  ts   在 header 与待签串里一致(毫秒)
  注意: 只有路径(不含host)、query按“键”升序、未 URL 编码

响应解密(实锤)
  AES-256-CBC, KEY=ayt5wy5afwmwrpb19k9s3psx3dymyd0n, IV=b3t069ijy7pirw0j
  明文 = JSON, PKCS7 去填充(server 头 encrypted:1 时必解)

关键接口(实测)
  GET /v6/vod/home.capi?os=android&appId=kkdy&userLevel=2            首页
  GET /v5/config/appInit.capi?...                                     分类/筛选字典
  GET /vod/channel/list.capi?channelId=1&next=page=2&category=..&..    分类列表
  GET /vod/rankingVods.capi?...                                       榜单
  GET /v2/vod/detail.capi?vodId=..&os=android&appId=kkdy&userLevel=2  详情(含playSources)
  GET /v2/vod/episodes.capi?vodId=..&siteId=..&episodeVodId=..        剧集(含 m3u8 直链)
  GET /vod/search/query?channelId=0&k=仙逆&next=&os=android&appId=kkdy&userChannel=c900&userLevel=2

时效说明
  · vcache 侧请求无任何会话级/时效字段(只要 UA+appId+ts+sign); vlogic(搜索)更挑且会限流
  · 仅详情/剧集里的 m3u8 直链带 sign+timestamp 短时效, 播放时重取(见 playerContent)
依赖: 优先用客户端自带 pycryptodome(Chaquopy 已内置, C 实现快~1000x); 无则纯 Python 兜底
"""
import json
import re
import sys
import os
import time
import hmac
import hashlib
from urllib.parse import quote

sys.path.append(os.path.dirname(os.path.abspath(__file__)))

try:
    from base.spider import Spider as BaseSpider
except ImportError:
    class BaseSpider:
        def __init__(self, query_params=None, t4_api=None):
            self.query_params = query_params or {}
            self.t4_api = t4_api or ''
            self.extend = ''

        def fetch(self, url, params=None, headers=None, cookies=None, timeout=10, **kw):
            import requests
            return requests.get(url, params=params, headers=headers,
                                cookies=cookies, timeout=timeout, verify=False)


# ================= 纯 Python AES-256-CBC (零依赖) =================
def _gmul(a, b):
    p = 0
    for _ in range(8):
        if b & 1:
            p ^= a
        hi = a & 0x80
        a = (a << 1) & 0xff
        if hi:
            a ^= 0x1b
        b >>= 1
    return p


def _ginv(a):
    if a == 0:
        return 0
    for i in range(256):
        if _gmul(a, i) == 1:
            return i
    return 0


def _rotl(x, n):
    return ((x << n) | (x >> (8 - n))) & 0xff


_SBOX = [0] * 256
for _i in range(256):
    _b = _ginv(_i)
    _SBOX[_i] = _b ^ _rotl(_b, 1) ^ _rotl(_b, 2) ^ _rotl(_b, 3) ^ _rotl(_b, 4) ^ 0x63
_ISBOX = [0] * 256
for _i, _v in enumerate(_SBOX):
    _ISBOX[_v] = _i


def _expand(key):
    nk = len(key) // 4
    nr = nk + 6
    w = [list(key[4 * i:4 * i + 4]) for i in range(nk)]
    rc = 1
    for i in range(nk, 4 * (nr + 1)):
        t = w[i - 1][:]
        if i % nk == 0:
            t = t[1:] + t[:1]
            t = [_SBOX[x] for x in t]
            t[0] ^= rc
            rc = _gmul(rc, 2)
        elif nk > 6 and i % nk == 4:
            t = [_SBOX[x] for x in t]
        w.append([w[i - nk][j] ^ t[j] for j in range(4)])
    return w, nr


def _dec_block(blk, key):
    w, nr = _expand(key)
    s = list(blk)
    for c in range(4):
        for r in range(4):
            s[4 * c + r] ^= w[4 * nr + c][r]
    for rnd in range(nr - 1, 0, -1):
        for r in range(1, 4):                        # InvShiftRows
            row = [s[4 * c + r] for c in range(4)]
            row = row[-r:] + row[:-r]
            for c in range(4):
                s[4 * c + r] = row[c]
        s[:] = [_ISBOX[x] for x in s]                # InvSubBytes
        for c in range(4):                           # AddRoundKey
            for r in range(4):
                s[4 * c + r] ^= w[4 * rnd + c][r]
        for c in range(4):                           # InvMixColumns
            a = [s[4 * c + i] for i in range(4)]
            s[4 * c + 0] = _gmul(a[0], 14) ^ _gmul(a[1], 11) ^ _gmul(a[2], 13) ^ _gmul(a[3], 9)
            s[4 * c + 1] = _gmul(a[0], 9) ^ _gmul(a[1], 14) ^ _gmul(a[2], 11) ^ _gmul(a[3], 13)
            s[4 * c + 2] = _gmul(a[0], 13) ^ _gmul(a[1], 9) ^ _gmul(a[2], 14) ^ _gmul(a[3], 11)
            s[4 * c + 3] = _gmul(a[0], 11) ^ _gmul(a[1], 13) ^ _gmul(a[2], 9) ^ _gmul(a[3], 14)
    for r in range(1, 4):                            # 末轮
        row = [s[4 * c + r] for c in range(4)]
        row = row[-r:] + row[:-r]
        for c in range(4):
            s[4 * c + r] = row[c]
    s[:] = [_ISBOX[x] for x in s]
    for c in range(4):
        for r in range(4):
            s[4 * c + r] ^= w[c][r]
    return bytes(s)


def _aes_cbc_decrypt_py(data, key, iv):
    out = bytearray()
    prev = iv
    for i in range(0, len(data) - len(data) % 16, 16):
        blk = data[i:i + 16]
        d = _dec_block(blk, key)
        out += bytes(x ^ y for x, y in zip(d, prev))
        prev = blk
    return bytes(out)


def _aes_cbc_decrypt(data, key, iv):
    """AES-256-CBC 解密: 优先 C 实现(pycryptodome/cryptography), 纯 Python 兜底。"""
    n = len(data) - len(data) % 16
    data = data[:n]
    if not data:
        return b""
    # 1) pycryptodome (客户端自带, C 实现, 快约千倍)
    try:
        from Crypto.Cipher import AES as _AES
        return _AES.new(key, _AES.MODE_CBC, iv).decrypt(data)
    except Exception:
        pass
    # 1b) Cryptodome 变体
    try:
        from Cryptodome.Cipher import AES as _AES2
        return _AES2.new(key, _AES2.MODE_CBC, iv).decrypt(data)
    except Exception:
        pass
    # 2) cryptography (部分客户端有)
    try:
        from cryptography.hazmat.primitives.ciphers import Cipher, algorithms, modes
        d = Cipher(algorithms.AES(key), modes.CBC(iv)).decryptor()
        return d.update(data) + d.finalize()
    except Exception:
        pass
    # 3) 纯 Python 兜底
    return _aes_cbc_decrypt_py(data, key, iv)
# ================================================================


class Spider(BaseSpider):
    HOST_VCACHE = "https://vcache.ybsdkl.cn"
    HOST_VLOGIC = "https://vlogic.ybsdkl.cn"
    IMG_HOST = "https://vres.mppcdrr.cn"

    UA = "com.kkdyD12997260706.t181523/3.5.0 Dalvik/2.1.0 (Linux; U; Android 13; 25098PN5AC Build/CP2A.260605.016)"
    UA_MEDIA = "okhttp/4.12.0"

    # 逆向所得常量(见文件头)。
    # 实测: 接口只校验 UA + appId + ts + sign 四项;
    # 其余 header(X-Token / deviceInfo / package / userId / st / apiVer / X-DEVICE)
    # 均非必需(实测删掉、甚至喂假 X-Token 仍返回 200)。
    # 故这里只发最小必需集, 不含任何会话级/时效性字段。
    SIGN_KEY = b"ksggsr4tp6difdo1c3im8fqd3g"
    AES_KEY = b"ayt5wy5afwmwrpb19k9s3psx3dymyd0n"
    AES_IV = b"b3t069ijy7pirw0j"
    DEVICE = "appId=kkdy&deviceCreatedAt=1791100645895&deviceId=346214515d5c88f1&st=2&userId=55957380"
    # X-Token: vcache 侧非必需; vlogic(搜索)实测需带(缺则搜索/埋点返回空). 过期需重抓.
    TOKEN = ("NTU5NTczODB8MTc5MTA5MDkzM3w3MGEwODc5Yzc0MjA0NTAyMjE5ODI1NjM5ZWI4YWM4NTJmMGMx"
             "ODMxYzI4ODE4MmU3Mzg0OTIyMTI4Y2QxZmY4")
    DEVICE_INFO = ("eyJicmFuZCI6IlhpYW9taSIsIm1vZGVsIjoiMjUwOThQTjVBQyIsInR5cGUiOiJwaG9uZSIs"
                   "InJlc29sdXRpb25YIjoiMTIyMCIsInJlc29sdXRpb25ZIjoiMjQ0MSIsIm9yaWVudGF0aW9uIjoiMSIs"
                   "Im9zTmFtZSI6ImFuZHJvaWQiLCJvc1ZlcnNpb24iOiIxMyIsIm9zTGV2ZWwiOiIzMyIsImFiaSI6ImFy"
                   "bTY0LXY4YSIsImFuZHJvaWRJZCI6IjM0NjIxNDUxNWQ1Yzg4ZjEiLCJ1dWlkIjoiOTVkNzhkZTItNjc5"
                   "My00NzU1LWJmMWItZmU1NmQyOGM2MGU4IiwiZ2FpZCI6IiJ9")

    # ★强制：每个脚本都要带，拼在 vod_content 最前面
    DISCLAIMER = ("【免责声明】本资源由「网友」免费分享整理，仅供个人学习、交流与测试使用，"
                  "请于体验后 24 小时内删除；所有影视内容版权均归原版权方所有，"
                  "严禁用于任何商业用途，如有侵权请告知删除。\n\n")

    # 分类顶层(来自 /v5/config/appInit.capi 的 vodTabs)
    CHANNELS = [
        ("6", "短剧"), ("1", "电影"), ("2001", "院线上新"), ("2", "剧集"),
        ("2002", "韩剧"), ("3", "动漫"), ("4", "综艺纪录"), ("1000", "Netflix"),
    ]

    def init(self, extend=""):
        self.extend = extend or ""
        self.timeout = 15
        self._cache = {}
        self._appinit = None
        return {"status": 0}

    def getName(self):
        return "🅿️可可影视"

    # ---------- 基础 ----------
    def _headers(self, logic=False):
        # vcache 实测只需 UA+appId+ts+sign; 但 vlogic(搜索)更挑且会被限流,
        # 为兼容两 host 统一发完整 App 头(X-Token 保留: vlogic 可能需要, 过期需重抓).
        h = {
            "User-Agent": self.UA,
            "appId": "kkdy",
            "os": "android",
            "appVersion": "3.5.0",
            "package": "com.kkdyD12997260706.t181523",
            "deviceId": "346214515d5c88f1",
            "deviceCreatedAt": "1791100645895",
            "userId": "55957380",
            "channelId": "c900",
            "X-Token": self.TOKEN,
            "apiVer": "v2",
            "st": "2",
            "deviceInfo": self.DEVICE_INFO,
            "Accept": "*/*",
            "Accept-Language": "zh-CN,zh;q=0.9",
        }
        if logic:
            h["X-DEVICE"] = "1"
        else:
            h["x-d-video"] = "1"
        return h

    def _sign(self, path, params):
        ts = str(int(time.time() * 1000))
        qs = "&".join("%s=%s" % (k, params[k]) for k in sorted(params))
        plain = "get|%s|%s|%s|%s|" % (path, qs, ts, self.DEVICE)
        sig = hmac.new(self.SIGN_KEY, plain.encode("utf-8"), hashlib.sha1).hexdigest()
        return ts, sig

    def _decrypt(self, raw):
        if not raw:
            return ""
        if raw[:1] in (b"{", b"["):
            return raw.decode("utf-8", "ignore")
        body = raw[:len(raw) - len(raw) % 16]
        p = _aes_cbc_decrypt(body, self.AES_KEY, self.AES_IV)
        if p and 1 <= p[-1] <= 16:
            p = p[:-p[-1]]
        return p.decode("utf-8", "ignore")

    def _api(self, path, params, host=None):
        host = host or self.HOST_VCACHE
        url = host + path
        ck = url + "?" + "&".join("%s=%s" % (k, params[k]) for k in sorted(params))
        if ck in self._cache:
            return self._cache[ck]
        ts, sig = self._sign(path, params)
        h = self._headers(host == self.HOST_VLOGIC)
        h["ts"] = ts
        h["sign"] = sig
        text = ""
        for i in range(2):
            try:
                rsp = self.fetch(url, params=params, headers=h, timeout=self.timeout)
                text = self._decrypt(rsp.content if hasattr(rsp, "content") else rsp.text.encode())
                if text and '"code"' in text:
                    break
            except Exception:
                text = ""
            time.sleep(0.8)
        if len(self._cache) > 24:
            self._cache.clear()
        self._cache[ck] = text
        return text

    def _json(self, path, params, host=None):
        try:
            return json.loads(self._api(path, params, host) or "{}")
        except Exception:
            return {}

    def _img(self, item):
        grp = item.get("imageGroup") or "vod1"
        path = item.get("imagePath") or ""
        if not path:
            return ""
        if path.startswith("http"):
            return path
        return "%s/%s%s" % (self.IMG_HOST, grp, path)

    def _clean(self, s):
        return re.sub(r"<[^>]+>", "", s or "").strip()

    def _card(self, it):
        return {
            "vod_id": str(it.get("id", "")).lstrip("/"),
            "vod_name": self._clean(it.get("title")),
            "vod_pic": self._img(it),
            "vod_remarks": self._clean(it.get("bottomLabel") or it.get("topRightLabel") or ""),
        }

    # ---------- 首页 ----------
    def _filters(self):
        ai = self._appinit
        if ai is None:
            ai = self._json("/v5/config/appInit.capi",
                            {"os": "android", "appId": "kkdy", "userLevel": "2"})
            self._appinit = ai
        qmap = {}
        for blk in (ai.get("channelListQuery") or []):
            cid = str(blk.get("channelId"))
            groups = []
            for g in (blk.get("items") or []):
                vals = [{"n": "全部", "v": ""}]
                vals += [{"n": d.get("name", ""), "v": d.get("id", "")}
                         for d in (g.get("data") or []) if d.get("id")]
                groups.append({
                    "key": g.get("query", ""),
                    "name": {"sort": "排序", "category": "类型", "area": "地区",
                             "year": "年份", "language": "语言"}.get(g.get("query", ""), g.get("query", "")),
                    "value": vals,
                })
            qmap[cid] = groups
        return qmap

    def homeContent(self, filter):
        classes = [{"type_id": cid, "type_name": name} for cid, name in self.CHANNELS]
        filters = {}
        if filter:
            # filters 懒加载: 仅在需要时拉一次 appInit(结果缓存), 不拖慢首屏
            qmap = self._filters()
            for cid, _ in self.CHANNELS:
                if qmap.get(cid):
                    filters[cid] = qmap[cid]
        return {"class": classes, "filters": filters}

    def homeVideoContent(self):
        j = self._json("/v6/vod/home.capi", {"os": "android", "appId": "kkdy", "userLevel": "2"})
        out = []
        seen = set()
        for blk in (j.get("data", {}).get("blocks") or []):
            for it in (blk.get("data") or []):
                if not isinstance(it, dict) or "id" not in it:
                    continue
                # 只保留真 vod（排除文章 article/detail、导航 browser）
                if "vod/detail" not in (it.get("url") or ""):
                    continue
                c = self._card(it)
                if c["vod_id"] and c["vod_id"] not in seen:
                    seen.add(c["vod_id"])
                    out.append(c)
        return {"list": out}

    # ---------- 分类 ----------
    def categoryContent(self, tid, pg, filter, extend):
        pg = max(1, int(pg or 1))
        fl = json.loads(extend) if isinstance(extend, str) and extend.strip() else (extend or {})
        params = {"channelId": str(tid), "os": "android", "appId": "kkdy", "userLevel": "2"}
        # extend 里的 key 直接用接口的 query 名: sort/category/area/year/language
        for k in ("sort", "category", "area", "year", "language"):
            v = str(fl.get(k, "") or "").strip()
            if v and v != "全部":
                params[k] = v
        if "sort" not in params:
            params["sort"] = "3"          # 实测默认最热
        if pg > 1:
            params["next"] = "page=%d" % pg
        j = self._json("/vod/channel/list.capi", params)
        lst = [self._card(it) for it in (j.get("data", {}).get("items") or []) if it.get("id")]
        nxt = j.get("data", {}).get("next") or ""
        return {"list": lst, "page": pg,
                "pagecount": pg + 1 if nxt else pg,
                "limit": len(lst) or 21, "total": 999999}

    # ---------- 搜索 ----------
    def searchContent(self, key, quick, pg=1):
        pg = max(1, int(pg or 1))
        params = {"channelId": "0", "k": key, "next": "" if pg <= 1 else "page=%d" % pg,
                  "os": "android", "appId": "kkdy", "userChannel": "c900", "userLevel": "2"}
        j = self._json("/vod/search/query", params, host=self.HOST_VLOGIC)
        lst = [self._card(it) for it in (j.get("data", {}).get("items") or []) if it.get("id")]
        return {"list": lst, "page": pg}

    # ---------- 详情 ----------
    def _detail(self, vid):
        return self._json("/v2/vod/detail.capi",
                          {"vodId": str(vid), "os": "android", "appId": "kkdy", "userLevel": "2"})

    def _episodes(self, vid, site_id, ep_vod_id):
        return self._json("/v2/vod/episodes.capi",
                          {"vodId": str(vid), "siteId": site_id, "episodeVodId": str(ep_vod_id),
                           "os": "android", "appId": "kkdy", "userLevel": "2"})

    def detailContent(self, ids):
        vid = ids[0] if isinstance(ids, (list, tuple)) else str(ids).split(",")[0]
        vid = str(vid).split("|")[0].lstrip("/")
        j = self._detail(vid)
        d = j.get("data") or {}
        if not d:
            return {"list": []}

        content = (d.get("summary") or "").strip()
        if self.DISCLAIMER:
            content = self.DISCLAIMER + content

        def _names(arr):
            return " / ".join([x.get("name", "") for x in (arr or []) if isinstance(x, dict)])

        froms, urls = [], []
        # 选中线路内联了剧集(list)，可作为其它线路的集名模板
        tpl = None
        for src in (d.get("playSources") or []):
            if src.get("list"):
                t = (src["list"][0].get("title") or "")
                if "第" in t:
                    tpl = t
                break

        def _gen_title(i):
            if tpl:
                return re.sub(r"\d+", str(i), tpl, count=1)
            return "第%d集" % i

        for src in (d.get("playSources") or []):
            site_id = src.get("siteId") or ""
            ep_vod_id = src.get("episodeVodId", "")
            eps = src.get("list") or []
            total = int(src.get("total") or 0)
            parts = []
            if eps:
                for ep in eps:
                    name = (ep.get("title") or "").replace("$", "_")
                    v = "%s|%s|%s|%s" % (vid, site_id, ep_vod_id, ep.get("index", ""))
                    parts.append("%s$%s" % (name, v))
            elif total > 0:
                # 【省请求】详情不逐线路抓剧集，按 total 生成；播放时再取该线路
                for i in range(1, total + 1):
                    v = "%s|%s|%s|%s" % (vid, site_id, ep_vod_id, i)
                    parts.append("%s$%s" % (_gen_title(i), v))
            if parts:
                froms.append(re.sub(r"\$+", "_", src.get("name") or site_id))
                urls.append("#".join(parts))

        vod = {
            "vod_id": vid,
            "vod_name": d.get("title", ""),
            "vod_pic": self._img(d),
            "type_name": d.get("channelName", ""),
            "vod_year": (d.get("year") or {}).get("name", "") if isinstance(d.get("year"), dict) else "",
            "vod_area": _names(d.get("area")),
            "vod_remarks": d.get("bottomLabel", ""),
            "vod_score": str(d.get("score", "") or ""),
            "vod_director": _names(d.get("directors")),
            "vod_actor": _names(d.get("actors")),
            "vod_content": content,
            "vod_play_from": "$$$".join(froms),
            "vod_play_url": "$$$".join(urls),
        }
        return {"list": [vod]}

    # ---------- 播放 ----------
    def playerContent(self, flag, vid, vip_flags):
        raw = str(vid).split("$")[-1]
        parts = raw.split("|")
        url = ""
        if len(parts) >= 4:
            v_id, site_id, ep_vod_id, index = parts[0], parts[1], parts[2], parts[3]
            data = self._episodes(v_id, site_id, ep_vod_id).get("data") or []
            for ep in data:
                if str(ep.get("index")) == str(index):
                    pus = ep.get("playUrls") or []
                    if pus:
                        url = (pus[0].get("url") or "").strip()
                    break
            if not url and data:
                pus = data[0].get("playUrls") or []
                if pus:
                    url = (pus[0].get("url") or "").strip()
        return {"parse": 0, "jx": 0, "url": url,
                "header": json.dumps({"User-Agent": self.UA_MEDIA}, ensure_ascii=False)}

    def isVideoFormat(self, url):
        return bool(url and re.search(r"\.(m3u8|mp4|ts)(\?|$)", url))

    def manualVideoCheck(self):
        return False

    def localProxy(self, param):
        return None