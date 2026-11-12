# -*- coding: utf-8 -*-
"""
KTV 点歌台 —— OK影视 / 影视仓 / TVBox 通用 KTV 爬虫
音源 (2026-11 实测可用):
  1. MV视频     网易云官方 MV (type=1004 搜索 + enhance/play/mv/url 取 mp4, 1080→720→480降级)
  2. 酷狗伴奏   酷狗 (搜"歌名 伴奏", trackercdn 取 320k 直链 + LRC歌词)
  3. 网易云伴奏 iqwq 聚合 (搜"歌名 伴奏", 播放时 GDStudio 兜底解 VIP 直链)
单源失效(版权限制/VIP)会自动跨源找同名歌曲兜底。

【OK影视 用法】
1. 把本文件放进本地包的 py/ 目录, 命名 KTV伴奏.py
2. 在该包的 py.json (或 api.json) 里加一条:
   {"key":"py_KTV伴奏","name":"🎤KTV点歌台🎤","type":3,
    "api":"py_KTV伴奏","searchable":1,"changeable":0}
   (若你的版本 api 前缀用 csp_, 改成 "csp_KTV伴奏")
3. 重新加载本地包入口 (file://包名/api.json) 即可看到 KTV点歌台

【玩法】
  🎬MV视频   → 原唱 MV, 有画面有字幕, 跟着唱
  🎹酷狗伴奏 → 纯伴奏 320k, 无人声, 真 KTV 体验 (带歌词)
  🎼网易伴奏 → 纯伴奏备用源
  搜索框直接输 歌名/歌手 即可点歌
"""
import re
import json
import time
import base64
import hashlib
import urllib.parse

try:
    import requests as _requests
    _HAS_REQUESTS = True
except Exception:
    _requests = None
    _HAS_REQUESTS = False

try:
    from base.spider import Spider as _BaseSpider
except Exception:
    class _BaseSpider:
        pass


def _log(*args):
    try:
        print("KTV点歌台", *args)
    except Exception:
        pass


def _b64encode(s):
    try:
        return base64.b64encode(str(s).encode("utf-8")).decode("ascii")
    except Exception:
        return ""


def _b64decode(s):
    try:
        return base64.b64decode(str(s)).decode("utf-8")
    except Exception:
        return ""


# ============ 站点常量 ============
NE163 = "https://music.163.com"          # 网易云官方 (MV)
IQWQ = "https://music.iqwq.cn"           # iqwq 聚合 (网易云伴奏)
KG_SEARCH = "http://mobilecdn.kugou.com/api/v3/search/song"   # 酷狗搜索
KG_TRACKER = "http://trackercdn.kugou.com/i/v2/"             # 酷狗取直链
KG_LYR_SEARCH = "http://krcs.kugou.com/search"               # 酷狗歌词搜索
KG_LYR_DL = "http://lyrics.kugou.com/download"               # 酷狗歌词下载
GD_API = "https://music-api.gdstudio.xyz/api.php"            # GDStudio 兜底
METING = "https://api.qijieya.cn/meting/"                     # meting 解析 (快速)
METING_BAK = "https://api.injahow.cn/meting/"                 # meting 备站
BILI = "https://www.bilibili.com"                             # B站 (KTV伴奏MV)
BILI_API = "https://api.bilibili.com"                         # B站接口

UA = ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
      "AppleWebKit/537.36 (KHTML, like Gecko) "
      "Chrome/150.0.0.0 Safari/537.36")

DEFAULT_HEADERS = {
    "User-Agent": UA,
    "Accept": "application/json, text/plain, */*",
    "Accept-Language": "zh-CN,zh;q=0.9",
}

# 分类: 数字ID -> (音源标识, 显示名称)
_CATEGORY = {
    "1": ("bili",  "🎤B站伴奏"),
    "2": ("mv163", "🎬MV视频"),
    "3": ("kgbz",  "🎹酷狗伴奏"),
    "4": ("wybz",  "🎼网易伴奏"),
}

# 各音源的浏览关键词 (分类页轮换使用)
_PLATFORM_KEYWORDS = {
    "bili": [
        "后来", "晴天", "朋友", "红豆", "海阔天空", "女人花",
        "一剪梅", "上海滩", "吻别", "千千阙歌", "月亮代表我的心", "相思风雨中",
    ],
    "mv163": [
        "热门MV", "经典MV", "流行MV", "粤语MV", "民谣MV",
        "摇滚MV", "抖音热歌", "怀旧金曲", "英文MV", "古风MV",
        "情歌MV", "青春MV",
    ],
    "kgbz": [
        "热门 伴奏", "经典 伴奏", "流行 伴奏", "粤语 伴奏", "民谣 伴奏",
        "抖音 伴奏", "老歌 伴奏", "伤感 伴奏", "古风 伴奏", "英文 伴奏",
        "情歌 伴奏", "摇滚 伴奏",
    ],
    "wybz": [
        "热门 伴奏", "经典 伴奏", "流行 伴奏", "粤语 伴奏", "民谣 伴奏",
        "抖音 伴奏", "老歌 伴奏", "伤感 伴奏", "古风 伴奏", "英文 伴奏",
        "情歌 伴奏", "摇滚 伴奏",
    ],
}

_PLATFORM_FILTERS = {
    p: [{"n": k.replace(" 伴奏", "").replace("MV", ""), "v": k} for k in kws]
    for p, kws in _PLATFORM_KEYWORDS.items()
}

# 筛选器标题 (B站按歌名浏览, 其他按风格)
_FILTER_NAMES = {"bili": "热门歌名", "mv163": "风格", "kgbz": "风格", "wybz": "风格"}

_MEDIA_RE = re.compile(r'\.(mp3|m4a|aac|ogg|wav|flac|mp4|m3u8)(\?|$)', re.I)


def _fix_pic(pic):
    if not pic:
        return ""
    pic = re.sub(r"^(https?:)//+", r"\1//", str(pic))
    # 酷狗图片占位符
    pic = pic.replace("{size}", "400").replace("{Size}", "400")
    return pic


def _norm(title="", author="", pic="", url="", lrc="", song_type="",
          song_id="", src="", extra=None):
    d = {
        "title": title or "未知",
        "author": author or "",
        "pic": _fix_pic(pic),
        "url": url or "",
        "lrc": lrc or "",
        "type": song_type,
        "id": str(song_id) if song_id else "",
        "src": src,
    }
    if extra:
        d.update(extra)
    return d


class Spider(_BaseSpider):
    """KTV 点歌台 —— 网易云MV + 酷狗伴奏 + 网易云伴奏"""

    name = "KTV点歌台"

    def init(self, extend=""):
        _log("init ->", extend)
        self.host = NE163
        self.header = dict(DEFAULT_HEADERS)
        self.timeout = 15
        if _HAS_REQUESTS:
            self.session = _requests.Session()
            self.session.headers.update(self.header)

    def getName(self):
        return self.name

    def destroy(self):
        pass

    def isVideoFormat(self, url):
        if not url:
            return False
        return bool(_MEDIA_RE.search(url))

    def manualVideoCheck(self):
        return False

    def localProxy(self, param):
        return None

    # ================= 基础请求 =================
    def _get_json(self, url, params=None, hdrs=None, timeout=None):
        try:
            hdrs = hdrs or dict(self.header)
            timeout = timeout or self.timeout
            if _HAS_REQUESTS:
                sess = getattr(self, "session", None) or _requests
                r = sess.get(url, params=params, headers=hdrs,
                             timeout=timeout, verify=False)
                return r.json()
            import urllib.request
            full = url + ("?" + urllib.parse.urlencode(params) if params else "")
            req = urllib.request.Request(full, headers=hdrs)
            with urllib.request.urlopen(req, timeout=timeout) as resp:
                return json.loads(resp.read().decode("utf-8", errors="replace"))
        except Exception as exc:
            _log("get err", str(exc)[:80])
            return None

    def _post_text(self, url, data, hdrs=None, timeout=None):
        try:
            hdrs = hdrs or dict(self.header)
            timeout = timeout or self.timeout
            if _HAS_REQUESTS:
                sess = getattr(self, "session", None) or _requests
                r = sess.post(url, data=data, headers=hdrs,
                              timeout=timeout, verify=False)
                r.encoding = "utf-8"
                return r.text
            import urllib.request
            body = urllib.parse.urlencode(data).encode("utf-8")
            req = urllib.request.Request(url, data=body, headers=hdrs)
            with urllib.request.urlopen(req, timeout=timeout) as resp:
                return resp.read().decode("utf-8", errors="replace")
        except Exception as exc:
            _log("post err", str(exc)[:80])
            return ""

    # ================= 源0: B站 KTV伴奏MV (1080P) =================
    def _bili_warm(self):
        """首次访问带上 buvid3 cookie (B站搜索需要)"""
        if getattr(self, "_bili_ok", False):
            return
        try:
            sess = getattr(self, "session", None)
            if sess is not None:
                sess.get(BILI, headers={"User-Agent": UA},
                         timeout=8, verify=False)
        except Exception:
            pass
        self._bili_ok = True

    def _search_bili(self, keyword, page):
        """B站搜索 KTV伴奏/带字幕伴奏视频"""
        try:
            kw = str(keyword)
            if "伴奏" not in kw and "ktv" not in kw.lower():
                kw = kw + " 伴奏"
            self._bili_warm()
            j = self._get_json(BILI_API + "/x/web-interface/search/type", {
                "search_type": "video", "keyword": kw, "page": str(page),
            }, hdrs={"User-Agent": UA, "Referer": BILI + "/"})
            if not isinstance(j, dict) or j.get("code") != 0:
                return []
            res = ((j.get("data") or {}).get("result")) or []
            out = []
            for v in res:
                bvid = v.get("bvid") or ""
                if not bvid:
                    continue
                title = re.sub(r"<[^>]+>", "", str(v.get("title") or ""))
                for a, b in (("&quot;", '"'), ("&amp;", "&"),
                             ("&lt;", "<"), ("&gt;", ">")):
                    title = title.replace(a, b)
                pic = str(v.get("pic") or "")
                if pic.startswith("//"):
                    pic = "https:" + pic
                secs = 0
                try:
                    nums = [int(x) for x in str(v.get("duration") or "").split(":") if x != ""]
                    for n in nums:
                        secs = secs * 60 + n
                except Exception:
                    secs = 0
                out.append(_norm(
                    title=title,
                    author=v.get("author") or "",
                    pic=pic,
                    song_type="bili",
                    song_id=bvid,
                    src="bili",
                    extra={"dur": secs, "play": v.get("play")},
                ))
            return out
        except Exception as exc:
            _log("bili search err", exc)
            return []

    def _bili_url(self, bvid):
        """B站播放直链 (1080P → 720P → 480P 逐级降级)"""
        if not bvid:
            return ""
        self._bili_warm()
        hdrs = {"User-Agent": UA, "Referer": BILI + "/"}
        try:
            pl = self._get_json(BILI_API + "/x/player/pagelist",
                                {"bvid": bvid}, hdrs=hdrs)
            pages = (pl or {}).get("data") or []
            if not pages:
                return ""
            cid = pages[0].get("cid")
            if not cid:
                return ""
            for qn in ("80", "64", "32"):
                j = self._get_json(BILI_API + "/x/player/playurl", {
                    "bvid": bvid, "cid": str(cid), "fnval": "16",
                    "qn": qn, "platform": "html5",
                }, hdrs=hdrs)
                durl = ((j or {}).get("data") or {}).get("durl") or []
                if durl:
                    u = durl[0].get("url") or ""
                    if u:
                        return u
        except Exception as exc:
            _log("bili play err", exc)
        return ""

    # ================= 源1: 网易云 MV 视频 =================
    def _search_mv163(self, keyword, page):
        """网易云 MV 搜索 (type=1004)"""
        try:
            offset = (int(page) - 1) * 20
            j = self._get_json(NE163 + "/api/search/get", {
                "s": str(keyword), "type": "1004",
                "limit": "20", "offset": str(offset),
            }, hdrs={"User-Agent": UA, "Referer": NE163})
            if not j:
                return []
            mvs = ((j.get("result") or {}).get("mvs")) or []
            out = []
            for m in mvs:
                artists = "/".join(a.get("name", "") for a in (m.get("artists") or []) if a.get("name"))
                dur = m.get("duration") or 0
                out.append(_norm(
                    title=m.get("name", ""),
                    author=artists,
                    pic=m.get("cover", ""),
                    song_type="mv163",
                    song_id=m.get("id"),
                    src="mv163",
                    extra={"dur": int(dur / 1000) if dur else 0},
                ))
            return out
        except Exception as exc:
            _log("mv search err", exc)
            return []

    def _mv163_url(self, mv_id):
        """网易云 MV 播放直链 (1080 → 720 → 480 逐级降级)"""
        for r in ("1080", "720", "480"):
            j = self._get_json(NE163 + "/api/song/enhance/play/mv/url",
                               {"id": str(mv_id), "r": r},
                               hdrs={"User-Agent": UA, "Referer": NE163})
            if isinstance(j, dict):
                url = ((j.get("data") or {}).get("url")) or ""
                if url:
                    return url
        return ""

    # ================= 源2: 酷狗伴奏 (320k音频) =================
    def _search_kgbz(self, keyword, page):
        """酷狗搜索伴奏歌曲"""
        try:
            kw = str(keyword)
            if "伴奏" not in kw and "伴唱" not in kw and "纯音乐" not in kw:
                kw = kw + " 伴奏"
            j = self._get_json(KG_SEARCH, {
                "keyword": kw, "page": str(page), "pagesize": "20",
                "showtype": "1", "format": "json",
            })
            if not j:
                return []
            info = ((j.get("data") or {}).get("info")) or []
            out = []
            for s in info:
                h = s.get("hash") or ""
                if not h:
                    continue
                out.append(_norm(
                    title=s.get("songname", ""),
                    author=s.get("singername", ""),
                    pic=s.get("imgurl", ""),
                    song_type="kgbz",
                    song_id=h,
                    src="kgbz",
                    extra={
                        "h320": s.get("320hash") or "",
                        "album": s.get("album_id") or "",
                        "dur": int(s.get("duration") or 0),
                    },
                ))
            return out
        except Exception as exc:
            _log("kgbz search err", exc)
            return []

    def _kg_url(self, song):
        """酷狗取 mp3 直链: 320k 优先, 失败降 128k"""
        h = song.get("id", "")
        h320 = song.get("h320", "")
        album = song.get("album", "")
        tries = []
        if h320:
            tries.append((h320, "320"))
        tries.append((h, "128"))
        for hash_, br in tries:
            key = hashlib.md5((hash_ + "kgcloudv2").encode("utf-8")).hexdigest()
            params = {
                "key": key, "hash": hash_, "br": br,
                "appid": "1005", "pid": "2", "cmd": "25",
                "behavior": "play", "album_id": album,
            }
            j = self._get_json(KG_TRACKER, params)
            if isinstance(j, dict) and j.get("status") == 1:
                urls = j.get("url") or []
                if isinstance(urls, str):
                    urls = [urls]
                if urls:
                    return urls[0]
        return ""

    def _kg_lyric(self, hash_, duration):
        """酷狗歌词 (LRC)"""
        try:
            j = self._get_json(KG_LYR_SEARCH, {
                "ver": "1", "man": "yes", "client": "mobi",
                "keyword": "", "duration": str(int(duration or 0) * 1000),
                "hash": hash_,
            })
            cands = (j or {}).get("candidates") or []
            if not cands:
                return ""
            c = cands[0]
            j2 = self._get_json(KG_LYR_DL, {
                "ver": "1", "client": "pc", "id": c.get("id", ""),
                "accesskey": c.get("accesskey", ""), "fmt": "lrc", "charset": "utf8",
            })
            content = (j2 or {}).get("content") or ""
            if content:
                return base64.b64decode(content).decode("utf-8", errors="replace")
        except Exception as exc:
            _log("kg lyric err", exc)
        return ""

    # ================= 源3: 网易云伴奏 (iqwq) =================
    def _search_wybz(self, keyword, page):
        """iqwq 聚合搜网易云伴奏 (返回外链, 播放时再解析)"""
        try:
            kw = str(keyword)
            if "伴奏" not in kw and "伴唱" not in kw:
                kw = kw + " 伴奏"
            text = self._post_text(IQWQ, {
                "input": kw, "filter": "name", "type": "netease", "page": str(page),
            }, hdrs={"User-Agent": UA, "Referer": IQWQ,
                     "X-Requested-With": "XMLHttpRequest"})
            if not text:
                return []
            raw = (json.loads(text).get("data")) or []
            out = []
            for s in raw:
                url = s.get("url", "") or ""
                if not url:
                    continue
                sid = ""
                m = re.search(r'[?&]id=(\d+)', url)
                if m:
                    sid = m.group(1)
                lrc = s.get("lrc", "")
                if isinstance(lrc, list):
                    lrc = "\n".join(str(x) for x in lrc)
                out.append(_norm(
                    title=s.get("title", ""),
                    author=s.get("author", ""),
                    pic=s.get("pic", ""),
                    url=url,
                    lrc=lrc,
                    song_type="wybz",
                    song_id=sid,
                    src="wybz",
                ))
            return out
        except Exception as exc:
            _log("wybz search err", exc)
            return []

    def _gd_url(self, song_id, br="320"):
        """GDStudio 兜底解析网易云直链 (VIP歌外链会404)"""
        for b in (br, "128"):
            j = self._get_json(GD_API, {
                "types": "url", "source": "netease",
                "id": str(song_id), "br": b,
            }, timeout=8)
            if isinstance(j, dict) and j.get("url"):
                return j["url"]
        return ""

    def _lyric_163(self, song_id):
        try:
            j = self._get_json(NE163 + "/api/song/lyric",
                               {"id": str(song_id), "lv": "1", "kv": "1"},
                               hdrs={"User-Agent": UA, "Referer": NE163})
            return ((j or {}).get("lrc") or {}).get("lyric") or ""
        except Exception:
            return ""

    # ================= 统一分发 =================
    def _search_platform(self, keyword, platform, page=1):
        if platform == "bili":
            return self._search_bili(keyword, page)
        if platform == "mv163":
            return self._search_mv163(keyword, page)
        if platform == "kgbz":
            return self._search_kgbz(keyword, page)
        if platform == "wybz":
            return self._search_wybz(keyword, page)
        return []

    def _probe_audio(self, url, timeout=8):
        """跟随重定向, 拿到音频则返回最终URL (否则空)"""
        try:
            if _HAS_REQUESTS:
                r = _requests.get(url, headers={"User-Agent": UA}, timeout=timeout,
                                  verify=False, allow_redirects=True, stream=True)
                ct = (r.headers.get("Content-Type") or "").lower()
                final = r.url or ""
                code = r.status_code
                r.close()
                if code == 200 and ("audio" in ct or "octet-stream" in ct):
                    return final
                return ""
            import urllib.request
            req = urllib.request.Request(url, headers={"User-Agent": UA})
            with urllib.request.urlopen(req, timeout=timeout) as resp:
                ct = (resp.headers.get("Content-Type") or "").lower()
                if "audio" in ct or "octet-stream" in ct:
                    return resp.geturl()
            return ""
        except Exception:
            return ""

    def _meting_url(self, server, sid):
        """meting 解析直链 (比 GDStudio 快, 支持VIP歌)"""
        if not sid:
            return ""
        for base in (METING, METING_BAK):
            u = "%s?server=%s&type=url&id=%s" % (
                base, server, urllib.parse.quote(str(sid)))
            final = self._probe_audio(u, timeout=8)
            if final:
                return final
        return ""

    def _outer_ok(self, url, timeout=5):
        """快速探测网易外链是否真能拿到音频 (VIP歌会跳到HTML提示页)"""
        try:
            if _HAS_REQUESTS:
                r = _requests.head(url, headers={"User-Agent": UA, "Referer": NE163},
                                   timeout=timeout, verify=False, allow_redirects=True)
                ct = (r.headers.get("Content-Type") or "").lower()
                return r.status_code == 200 and "audio" in ct
            import urllib.request
            req = urllib.request.Request(
                url, headers={"User-Agent": UA, "Referer": NE163}, method="HEAD")
            with urllib.request.urlopen(req, timeout=timeout) as resp:
                return "audio" in (resp.headers.get("Content-Type") or "").lower()
        except Exception:
            return False

    def _resolve_url(self, song):
        """播放时解析直链 (单源失败自动跨源兜底)"""
        src = song.get("src", "")
        url = song.get("url", "")
        if src == "bili":
            if url:
                return url
            url = self._bili_url(song.get("id", ""))
            if url:
                song["url"] = url
                return url
            return self._fallback_url(song, ["kgbz", "wybz", "mv163"])
        if src == "mv163":
            if url:
                return url
            url = self._mv163_url(song.get("id", ""))
            if url:
                song["url"] = url
                return url
            # MV不可用 → 兜底找同名伴奏
            return self._fallback_url(song, ["kgbz", "wybz"])
        if src == "kgbz":
            if url:
                return url
            url = self._kg_url(song)
            if url:
                song["url"] = url
                return url
            return self._fallback_url(song, ["wybz", "mv163"])
        # wybz: meting 快速解析 -> 外链探测 -> GDStudio -> 跨源兜底
        if song.get("id"):
            fresh = self._meting_url("netease", song["id"])
            if fresh:
                song["url"] = fresh
                return fresh
        if url and self._outer_ok(url):
            return url
        if song.get("id"):
            fresh = self._gd_url(song["id"])
            if fresh:
                song["url"] = fresh
                return fresh
        if url:
            return url
        return self._fallback_url(song, ["kgbz", "mv163"])

    def _fallback_url(self, song, platforms):
        """跨源兜底: 用歌曲名去其他音源找可用直链"""
        title = re.sub(r'[（(【\[]?(伴奏|伴唱|和声伴奏版|纯伴奏|KTV版)[）)】\]]?', '',
                       song.get("title", ""), flags=re.I).strip()
        if not title:
            return ""
        for p in platforms:
            try:
                for cand in self._search_platform(title, p, 1)[:3]:
                    if p == "bili":
                        u = self._bili_url(cand.get("id", ""))
                    elif p == "mv163":
                        u = self._mv163_url(cand.get("id", ""))
                    elif p == "kgbz":
                        u = self._kg_url(cand)
                    else:
                        u = (self._meting_url("netease", cand.get("id", ""))
                             or self._gd_url(cand.get("id", "")))
                        if not u and cand.get("url") and self._outer_ok(cand.get("url")):
                            u = cand.get("url", "")
                    if u:
                        _log("跨源兜底 %s -> %s" % (song.get("title", "")[:16], p))
                        # 同步歌词来源, 便于 lyric 接口使用
                        song["lrc"] = song.get("lrc") or cand.get("lrc", "")
                        return u
            except Exception:
                continue
        return ""

    def _resolve_lyric(self, song):
        if song.get("lrc"):
            return song["lrc"]
        src = song.get("src", "")
        if src == "kgbz":
            song["lrc"] = self._kg_lyric(song.get("id", ""), song.get("dur", 0))
        elif src == "wybz" and song.get("id"):
            song["lrc"] = self._lyric_163(song["id"])
        return song.get("lrc", "")

    def _play_header(self, src, url):
        """按实际直链来源给请求头 (跨源兜底后仍匹配)"""
        h = {"User-Agent": UA}
        u = url or ""
        if "bilivideo" in u or "bilibili" in u:
            h["Referer"] = BILI + "/"
        elif "126.net" in u or "163.com" in u:
            h["Referer"] = NE163
        elif "kugou" in u:
            h["Referer"] = "http://www.kugou.com/"
        elif "iqwq" in u:
            h["Referer"] = IQWQ
        else:
            h["Referer"] = {"mv163": NE163, "wybz": IQWQ, "bili": BILI + "/",
                            "kgbz": "http://www.kugou.com/"}.get(src, IQWQ)
        return h

    def _song_to_vod(self, song):
        title = song.get("title", "") or "未知"
        author = song.get("author", "") or ""
        pic = song.get("pic", "") or ""
        tag = {"bili": "MV", "mv163": "MV", "kgbz": "伴奏", "wybz": "伴奏"}.get(song.get("src"), "")
        remark = ("%s · %s" % (author, tag)) if author else tag
        return {
            "vod_id": _b64encode(json.dumps(song, ensure_ascii=False)),
            "vod_name": title,
            "vod_pic": pic,
            "vod_remarks": remark,
        }

    # ================= 首页 =================
    def _recommend(self, limit=20):
        all_songs = []
        seen = set()

        def _add(songs):
            for s in songs:
                sig = "%s_%s" % (s.get("title", ""), s.get("author", ""))
                if sig and sig not in seen:
                    seen.add(sig)
                    all_songs.append(s)

        _add(self._search_bili("海阔天空", 1))
        _add(self._search_mv163("热门MV", 1))
        if len(all_songs) < limit // 2:
            _add(self._search_mv163("经典MV", 1))
        _add(self._search_kgbz("热门", 1))
        return all_songs[:limit]

    def homeContent(self, filter=False):
        try:
            classes = [
                {"type_id": "1", "type_pid": "0", "type_name": "🎤B站伴奏"},
                {"type_id": "2", "type_pid": "0", "type_name": "🎬MV视频"},
                {"type_id": "3", "type_pid": "0", "type_name": "🎹酷狗伴奏"},
                {"type_id": "4", "type_pid": "0", "type_name": "🎼网易伴奏"},
            ]
            filters = {}
            for tid, (platform, _) in _CATEGORY.items():
                values = _PLATFORM_FILTERS.get(platform, [])
                if values:
                    filters[tid] = [{
                        "key": "kw",
                        "name": _FILTER_NAMES.get(platform, "风格"),
                        "value": values,
                    }]
            result = {"class": classes, "list": []}
            if filter:
                result["filters"] = filters
            result["list"] = [self._song_to_vod(s) for s in self._recommend(20)]
            return result
        except Exception as exc:
            _log("homeContent err", exc)
            return {"class": [], "list": []}

    def homeVideoContent(self):
        try:
            return {"list": [self._song_to_vod(s) for s in self._recommend(12)]}
        except Exception:
            return {"list": []}

    # ================= 分类 =================
    def categoryContent(self, tid, pg, filter=False, extend=None):
        extend = extend or {}
        try:
            page = int(pg) if pg else 1
        except Exception:
            page = 1

        platform = "mv163"
        if str(tid) in _CATEGORY:
            platform, _ = _CATEGORY[str(tid)]
        keyword = extend.get("kw", "") if extend else ""
        keywords = _PLATFORM_KEYWORDS.get(platform, ["热门"])

        result = {"list": [], "page": page, "pagecount": 999,
                  "limit": 20, "total": 9999}

        try:
            all_songs = []
            seen = set()

            def _add(songs):
                for s in songs:
                    sig = "%s_%s" % (s.get("title", ""), s.get("author", ""))
                    if sig and sig not in seen:
                        seen.add(sig)
                        all_songs.append(s)

            if keyword:
                _add(self._search_platform(keyword, platform, page))
            else:
                # 无关键词: 按页轮换浏览词, 每页1个词翻页更深
                idx = (page - 1) % len(keywords)
                kw = keywords[idx]
                _add(self._search_platform(kw, platform, ((page - 1) // len(keywords)) + 1))
                if len(all_songs) < 10:
                    _add(self._search_platform(keywords[(idx + 1) % len(keywords)], platform, 1))

            if all_songs:
                result["list"] = [self._song_to_vod(s) for s in all_songs]
                result["limit"] = len(all_songs)
        except Exception as exc:
            _log("categoryContent err", exc)
        return result

    # ================= 详情 =================
    def detailContent(self, ids):
        if not ids:
            return {"list": []}
        try:
            vid = str(ids)
            if isinstance(ids, (list, tuple)):
                vid = str(ids[0])
            vid = vid.split("$")[-1].strip()

            song_json = _b64decode(vid)
            if not song_json:
                return {"list": []}
            song = json.loads(song_json)

            title = song.get("title", "") or "未知"
            author = song.get("author", "") or ""
            pic = song.get("pic", "") or ""
            src = song.get("src", "")
            src_name = {"bili": "B站伴奏MV", "mv163": "网易云MV",
                        "kgbz": "酷狗伴奏", "wybz": "网易云伴奏"}.get(src, "KTV")
            kind = "MV视频" if src in ("bili", "mv163") else "伴奏音频"

            # 预解析直链 + 歌词
            self._resolve_url(song)
            self._resolve_lyric(song)
            new_vid = _b64encode(json.dumps(song, ensure_ascii=False))

            dur = song.get("dur", 0)
            dur_txt = "%d:%02d" % (dur // 60, dur % 60) if dur else ""

            content_lines = ["歌手: %s" % author if author else "", "音源: %s" % src_name,
                             "类型: %s" % kind]
            if dur_txt:
                content_lines.append("时长: %s" % dur_txt)

            return {"list": [{
                "vod_id": new_vid,
                "vod_name": title,
                "vod_pic": pic,
                "vod_remarks": ("%s · %s" % (author, kind)) if author else kind,
                "vod_year": "",
                "vod_area": src_name,
                "vod_content": "\n".join([x for x in content_lines if x]),
                "vod_play_from": "KTV点歌",
                "vod_play_url": "%s$%s" % (title, new_vid),
            }]}
        except Exception as exc:
            _log("detailContent err", exc)
            return {"list": []}

    # ================= 播放 =================
    def playerContent(self, flag, id, vipFlags):
        try:
            vid = str(id).split("$")[-1].strip()
            song_json = _b64decode(vid)
            if song_json:
                song = json.loads(song_json)
                url = self._resolve_url(song)
                if url:
                    _log("播放:", song.get("title", "")[:20], url[:70])
                    return {
                        "parse": 0,
                        "url": url,
                        "header": self._play_header(song.get("src", ""), url),
                        "playUrl": "",
                    }
                _log("无直链:", song.get("title", ""))
        except Exception as exc:
            _log("playerContent err", exc)
        return {"parse": 0, "url": "", "header": {}, "playUrl": ""}

    # ================= 搜索 =================
    def searchContent(self, key, quick, pg="1"):
        if not key:
            return {"list": []}
        try:
            page = int(pg) if pg else 1
            vod_list = []
            seen = set()
            # 优先级: MV视频 → 酷狗伴奏 → 网易伴奏
            for platform in ["bili", "mv163", "kgbz", "wybz"]:
                for song in self._search_platform(key, platform, page):
                    sig = "%s_%s_%s" % (song.get("title", ""), song.get("author", ""), song.get("src", ""))
                    if sig and sig not in seen:
                        seen.add(sig)
                        vod_list.append(self._song_to_vod(song))
                if len(vod_list) >= 30:
                    break
            return {"list": vod_list}
        except Exception as exc:
            _log("searchContent err", exc)
            return {"list": []}

    # ================= 音乐接口兼容 (MusicTvBoxMobile/MusicFree) =================
    def search(self, query, page, type=""):
        data = []
        try:
            pg = int(page) if page else 1
            platform = "bili"
            if isinstance(type, str) and type in [p[0] for p in _CATEGORY.values()]:
                platform = type
            for song in self._search_platform(query, platform, pg):
                data.append({
                    "id": _b64encode(json.dumps(song, ensure_ascii=False)),
                    "title": song.get("title", ""),
                    "artist": song.get("author", ""),
                    "artwork": song.get("pic", ""),
                    "album": song.get("type", ""),
                    "ext": "",
                })
        except Exception:
            pass
        return {"isEnd": True, "data": data}

    def getMediaSource(self, id, ext, quality):
        result = {"url": ""}
        try:
            song_json = _b64decode(str(id))
            if song_json:
                song = json.loads(song_json)
                url = self._resolve_url(song)
                if url:
                    result["url"] = url
                    result["headers"] = self._play_header(song.get("src", ""), url)
        except Exception:
            pass
        return result

    def getLyric(self, id, ext):
        result = {"lyric": ""}
        try:
            song_json = _b64decode(str(id))
            if song_json:
                song = json.loads(song_json)
                result["lyric"] = self._resolve_lyric(song)
        except Exception:
            pass
        return result


if __name__ == "__main__":
    spider = Spider()
    spider.init()

    print("=" * 62)
    print("  %s — 自测" % spider.getName())
    print("=" * 62)

    home = spider.homeContent(True)
    print("\n[首页] 分类=%d 推荐=%d" % (len(home["class"]), len(home["list"])))
    for c in home["class"]:
        print("   ", c["type_id"], c["type_name"])
    for item in home["list"][:4]:
        print("    [%s] %s" % (item["vod_remarks"][:24], item["vod_name"][:28]))

    print("\n[分类+详情+播放]")
    for tid, (plat, name) in _CATEGORY.items():
        cat = spider.categoryContent(tid, 1, True, {})
        print("  %s: %d 首" % (name, len(cat["list"])))
        if not cat["list"]:
            continue
        for item in cat["list"][:2]:
            detail = spider.detailContent([item["vod_id"]])
            if not detail["list"]:
                print("    详情失败"); continue
            vod = detail["list"][0]
            pu = vod.get("vod_play_url", "")
            pid = pu.split("$")[-1] if "$" in pu else pu
            player = spider.playerContent("KTV点歌", pid, None)
            print("    %-22s -> %s" % (vod["vod_name"][:22], player.get("url", "")[:62]))

    print("\n[搜索 孤勇者]")
    s = spider.searchContent("孤勇者", False, "1")
    print("  共 %d 条" % len(s["list"]))
    for item in s["list"][:6]:
        print("    [%s] %s" % (item["vod_remarks"][:24], item["vod_name"][:28]))

    print("\n[歌词测试 - 酷狗伴奏]")
    kg = spider._search_kgbz("晴天", 1)
    if kg:
        ly = spider._resolve_lyric(kg[0])
        print("  %s | 歌词 %d 字" % (kg[0]["title"][:20], len(ly)))

    print("\n" + "=" * 62)
