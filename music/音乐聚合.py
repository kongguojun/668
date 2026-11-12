# -*- coding: utf-8 -*-
"""
音乐聚合 (多源版) —— TVBox / 影视仓 / MusicTvBoxMobile 通用音乐爬虫

音源 (2026-11 实测):
  1. 网易云     meting 搜索 + meting 解析直链 (VIP歌也能播)
  2. QQ音乐     meting(tencent) 搜索 + 直链 (免费歌可用)
  3. 酷狗音乐   meting(kugou) 搜索 + trackercdn 取 mp3 直链
  4. 咪咕音乐   meting(migu) 搜索 + 直链
  5. 百度音乐   iqwq 聚合 (直链即用, 通用词效果好)

解析链: meting 主站 -> meting 备站(injahow) -> iqwq外链 -> 官方接口 -> 跨源同名兜底
"""

import re
import json
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
        print("音乐聚合", *args)
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


# ============ 接口地址 ============
SITE = "https://music.iqwq.cn"                       # iqwq 聚合API (网易/百度备用搜索)
METING = "https://api.qijieya.cn/meting/"            # meting 主站
METING_BAK = "https://api.injahow.cn/meting/"        # meting 备站
NE163 = "https://music.163.com"                      # 网易云官方
KG_CDN = "http://trackercdn.kugou.com/i/v2/"         # 酷狗直链接口
MISSEVAN = "https://www.missevan.com"                # 猫耳FM (广播剧/有声)

UA = ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
      "AppleWebKit/537.36 (KHTML, like Gecko) "
      "Chrome/150.0.0.0 Safari/537.36")

DEFAULT_HEADERS = {
    "User-Agent": UA,
    "X-Requested-With": "XMLHttpRequest",
    "Accept": "application/json, text/plain, */*",
    "Accept-Language": "zh-CN,zh;q=0.9",
}

# 分类: 数字ID -> (平台标识, 显示名称)
_CATEGORY = {
    "1": ("netease", "网易云"),
    "2": ("tencent", "QQ音乐"),
    "3": ("kugou", "酷狗音乐"),
    "4": ("migu", "咪咕音乐"),
    "5": ("baidu", "百度音乐"),
    "6": ("playlist", "🔥歌单榜单"),
    "7": ("missevan", "🎧广播剧"),
}

# 音质档位 (meting 的 br 参数, 999 = 无损FLAC)
_QUALITY = [
    {"n": "标准", "v": ""},
    {"n": "320K", "v": "320"},
    {"n": "无损", "v": "999"},
]

# 猫耳FM 分类浏览关键词
_MS_KEYWORDS = [
    "广播剧", "古风", "悬疑", "言情", "有声书", "全一期",
    "搞笑", "恐怖", "热血", "治愈",
]

# 歌单/榜单: id 为固定歌单ID(空则按关键词动态搜索), name, kw
_PLAYLISTS = [
    {"id": "3778678",  "name": "🔥 热歌榜",     "kw": ""},
    {"id": "3779629",  "name": "🆕 新歌榜",     "kw": ""},
    {"id": "19723756", "name": "📈 飙升榜",     "kw": ""},
    {"id": "2884035",  "name": "🌱 原创榜",     "kw": ""},
    {"id": "",         "name": "🎧 抖音热歌",   "kw": "抖音热歌"},
    {"id": "",         "name": "🎤 粤语经典",   "kw": "粤语经典老歌"},
    {"id": "",         "name": "🏮 国风古风",   "kw": "古风"},
    {"id": "",         "name": "🎸 民谣",       "kw": "民谣"},
    {"id": "",         "name": "🎹 纯音乐",     "kw": "纯音乐"},
    {"id": "",         "name": "💽 DJ舞曲",     "kw": "DJ舞曲"},
    {"id": "",         "name": "👶 儿歌",       "kw": "儿歌"},
    {"id": "",         "name": "📼 怀旧金曲",   "kw": "怀旧经典老歌"},
    {"id": "",         "name": "🎬 影视原声",   "kw": "影视原声"},
    {"id": "",         "name": "🎤 KTV必点",    "kw": "KTV必点"},
    {"id": "",         "name": "💔 伤感",       "kw": "伤感情歌"},
    {"id": "",         "name": "🏃 运动燃曲",   "kw": "运动健身燃曲"},
]

# meting 的平台标识 (百度走 iqwq, 不在其中)
_METING_SERVERS = ("netease", "tencent", "kugou", "migu")

# 各平台通用热词 (分类页轮换用)
_HOT_WORDS = [
    "流行", "经典", "华语", "民谣", "治愈",
    "怀旧", "粤语", "古风", "伤感", "轻音乐",
    "摇滚", "电子", "说唱", "爵士", "纯音乐",
]

_PLATFORM_FILTERS = {
    p: [{"n": k, "v": k} for k in _HOT_WORDS]
    for p in list(_METING_SERVERS) + ["baidu"]
}

_AUDIO_RE = re.compile(r'\.(mp3|m4a|aac|ogg|wav|flac)(\?|$)', re.I)
_LRC_TIME_RE = re.compile(r'\[\d{1,2}:\d{1,2}[.:]\d{1,3}\]')


def _fix_pic(pic):
    """修复图片URL (如 https:////xxx -> https://xxx)"""
    if not pic:
        return ""
    return re.sub(r"^(https?:)//+", r"\1//", str(pic))


def _norm_song(title="", author="", pic="", url="", lrc="", song_type="",
               song_id="", src="", srv="", lrc_url="", dur=0):
    """归一化的歌曲信息"""
    if isinstance(lrc, list):
        lrc = "\n".join(str(x) for x in lrc)
    return {
        "title": title or "未知",
        "author": author or "",
        "pic": _fix_pic(pic),
        "url": url or "",
        "lrc": lrc or "",
        "lrc_url": lrc_url or "",
        "type": song_type,
        "id": str(song_id) if song_id else "",
        "src": src,       # mt / iqwq / kg / 163
        "srv": srv,       # meting 平台名
        "dur": dur or 0,
    }


class Spider(_BaseSpider):
    """多源音乐聚合 —— 网易云 / QQ音乐 / 酷狗 / 咪咕 / 百度"""

    name = "音乐聚合"

    def init(self, extend=""):
        _log("init ->", extend)
        self.host = SITE
        self.header = dict(DEFAULT_HEADERS)
        self.timeout = 12
        self._pl_cache = {}       # 关键词 -> 歌单ID
        self._pl_data = {}        # 歌单ID -> 歌曲列表
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
        return bool(_AUDIO_RE.search(url))

    def manualVideoCheck(self):
        return False

    def localProxy(self, param):
        return None

    # ============ 网络请求 ============
    def _http_post(self, url, data, hdrs=None):
        """POST 请求, 返回文本"""
        try:
            hdrs = hdrs or dict(self.header)
            if _HAS_REQUESTS:
                sess = getattr(self, "session", None) or _requests
                r = sess.post(url, data=data, headers=hdrs,
                              timeout=self.timeout, verify=False)
                r.encoding = "utf-8"
                return r.text
            import urllib.request
            post_data = urllib.parse.urlencode(data).encode("utf-8")
            req = urllib.request.Request(url, data=post_data, headers=hdrs)
            with urllib.request.urlopen(req, timeout=self.timeout) as resp:
                return resp.read().decode("utf-8", errors="replace")
        except Exception as exc:
            _log("post err", exc)
            return ""

    def _http_get_json(self, url, params, hdrs=None, timeout=None):
        """GET 请求, 返回 JSON 或 None"""
        try:
            hdrs = hdrs or {"User-Agent": UA, "Accept": "application/json"}
            timeout = timeout or self.timeout
            if _HAS_REQUESTS:
                sess = getattr(self, "session", None) or _requests
                r = sess.get(url, params=params, headers=hdrs,
                             timeout=timeout, verify=False)
                return r.json()
            import urllib.request
            full = url + "?" + urllib.parse.urlencode(params)
            req = urllib.request.Request(full, headers=hdrs)
            with urllib.request.urlopen(req, timeout=timeout) as resp:
                return json.loads(resp.read().decode("utf-8", errors="replace"))
        except Exception as exc:
            _log("get err", exc)
            return None

    def _http_get_text(self, url, hdrs=None, timeout=None):
        """GET 请求, 返回文本"""
        try:
            hdrs = hdrs or {"User-Agent": UA}
            timeout = timeout or self.timeout
            if _HAS_REQUESTS:
                sess = getattr(self, "session", None) or _requests
                r = sess.get(url, headers=hdrs, timeout=timeout, verify=False)
                r.encoding = "utf-8"
                return r.text
            import urllib.request
            req = urllib.request.Request(url, headers=hdrs)
            with urllib.request.urlopen(req, timeout=timeout) as resp:
                return resp.read().decode("utf-8", errors="replace")
        except Exception as exc:
            _log("get text err", exc)
            return ""

    def _probe_audio(self, url, timeout=8):
        """跟随重定向, 若最终拿到音频则返回最终URL, 否则返回空"""
        try:
            if _HAS_REQUESTS:
                sess = getattr(self, "session", None) or _requests
                r = sess.get(url, headers={"User-Agent": UA}, timeout=timeout,
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

    def _too_short(self, url, timeout=4):
        """试听片段检测: 小于 1.2MB 基本是 30 秒试听, 需要换源"""
        try:
            if not url or not _HAS_REQUESTS:
                return False
            sess = getattr(self, "session", None) or _requests
            r = sess.head(url, headers={"User-Agent": UA}, timeout=timeout,
                          verify=False, allow_redirects=True)
            cl = r.headers.get("Content-Length")
            ct = (r.headers.get("Content-Type") or "").lower()
            r.close()
            if not cl or ("audio" not in ct and "octet" not in ct):
                return False
            try:
                return int(cl) < 1200000
            except Exception:
                return False
        except Exception:
            return False

    def _outer_ok(self, url, timeout=5):
        """快速探测网易外链是否真能拿到音频 (VIP歌会跳到HTML提示页)"""
        try:
            if _HAS_REQUESTS:
                sess = getattr(self, "session", None) or _requests
                r = sess.head(url, headers={"User-Agent": UA, "Referer": NE163},
                              timeout=timeout, verify=False, allow_redirects=True)
                ct = (r.headers.get("Content-Type") or "").lower()
                return r.status_code == 200 and "audio" in ct
            return bool(self._probe_audio(url, timeout))
        except Exception:
            return False

    # ============ 源 A: meting 聚合 (网易/QQ/酷狗/咪咕) ============
    def _meting_search(self, server, keyword, page=1, limit=30):
        """meting 搜索: 返回带 url/pic/lrc 代理地址的歌曲"""
        try:
            j = self._http_get_json(METING, {
                "type": "search",
                "id": str(keyword),
                "server": server,
                "page": str(page),
                "limit": str(limit),
            }, timeout=10)
            if not isinstance(j, list):
                return []
            out = []
            for s in j:
                name = (s.get("name") or "").strip()
                if not name:
                    continue
                artist = s.get("artist") or ""
                if isinstance(artist, list):
                    artist = "/".join(str(a) for a in artist)
                url = s.get("url") or ""
                sid = ""
                m = re.search(r'[?&]id=([^&]+)', url)
                if m:
                    sid = m.group(1)
                out.append(_norm_song(
                    title=name,
                    author=str(artist),
                    pic=s.get("pic") or "",
                    url=url,
                    lrc_url=s.get("lrc") or "",
                    song_type=server,
                    song_id=sid,
                    src="mt",
                    srv=server,
                    dur=s.get("duration") or 0,
                ))
            return out
        except Exception as exc:
            _log("meting search err", exc)
            return []

    def _meting_url(self, server, sid, br=""):
        """meting 解析: 返回最终 CDN 直链 (302 跟随 + 音频类型校验)
        br: "" 标准 / "320" / "999" 无损, 高码率拿不到时自动降级
        """
        if not sid:
            return ""
        grades = [br] if br else []
        for g in ("320", ""):
            if g not in grades:
                grades.append(g)
        for base in (METING, METING_BAK):
            for g in grades:
                u = "%s?server=%s&type=url&id=%s" % (
                    base, server, urllib.parse.quote(str(sid)))
                if g:
                    u += "&br=%s" % g
                final = self._probe_audio(u, timeout=8)
                if final:
                    return final
        return ""

    def _meting_lyric(self, lrc_url):
        """meting 歌词代理 -> LRC 文本"""
        if not lrc_url:
            return ""
        txt = self._http_get_text(lrc_url, timeout=8)
        if txt and _LRC_TIME_RE.search(txt):
            return txt.strip()
        return ""

    # ============ 源 E: 猫耳FM 广播剧 / 有声 ============
    def _ms_headers(self):
        return {"User-Agent": UA, "Referer": MISSEVAN + "/"}

    def _ms_search(self, keyword, page=1):
        """猫耳FM 剧集搜索 -> 剧(多集)列表"""
        try:
            j = self._http_get_json(MISSEVAN + "/dramaapi/search", {
                "s": str(keyword), "page": str(page),
            }, hdrs=self._ms_headers(), timeout=10)
            if not isinstance(j, dict):
                return []
            datas = ((j.get("info") or {}).get("Datas")) or []
            out = []
            for d in datas:
                if not d.get("id"):
                    continue
                eps = [{"id": e.get("sound_id"), "name": e.get("name") or ""}
                       for e in (d.get("episodes") or []) if e.get("sound_id")]
                tname = d.get("type_name") or "广播剧"
                remark = tname
                song = _norm_song(
                    title=d.get("name", ""),
                    author=remark,
                    pic=d.get("cover", ""),
                    song_type="广播剧",
                    song_id=d.get("id"),
                    src="ms",
                )
                song["intro"] = str(d.get("abstract") or "").strip()
                song["eps"] = eps
                out.append(song)
            return out
        except Exception as exc:
            _log("missevan search err", exc)
            return []

    def _ms_episodes(self, did):
        """猫耳剧集详情: 只保留免费集 (付费集取不到音频)"""
        try:
            j = self._http_get_json(MISSEVAN + "/dramaapi/getdrama",
                                    {"drama_id": str(did)},
                                    hdrs=self._ms_headers(), timeout=10)
            info = (j or {}).get("info") or {}
            drama = info.get("drama") or {}
            eps = (info.get("episodes") or {}).get("episode") or []
            out = []
            for e in eps:
                if e.get("need_pay"):
                    continue
                sid = e.get("sound_id")
                if not sid:
                    continue
                out.append({
                    "id": sid,
                    "name": e.get("name") or ("第%d集" % (len(out) + 1)),
                    "dur": int((e.get("duration") or 0) / 1000),
                })
            return drama, out
        except Exception as exc:
            _log("missevan drama err", exc)
            return {}, []

    def _ms_sound_url(self, sid):
        """猫耳音频直链 (HLS m3u8, 播放器原生支持)"""
        try:
            j = self._http_get_json(MISSEVAN + "/sound/getsound",
                                    {"soundid": str(sid)},
                                    hdrs=self._ms_headers(), timeout=10)
            snd = ((j or {}).get("info") or {}).get("sound") or {}
            return snd.get("soundurl_128") or snd.get("soundurl") or ""
        except Exception as exc:
            _log("missevan sound err", exc)
            return ""

    # ============ 源 F: 歌单/榜单 (meting playlist) ============
    def _playlist_search_id(self, keyword):
        """按关键词搜网易歌单, 取播放量最高的一个, 结果缓存"""
        if not keyword:
            return ""
        if keyword in self._pl_cache:
            return self._pl_cache[keyword]
        pid = ""
        try:
            hdrs = {
                "User-Agent": UA,
                "Referer": NE163,
                "Content-Type": "application/x-www-form-urlencoded",
            }
            text = self._http_post(NE163 + "/api/search/get/web", {
                "s": str(keyword), "type": "1000", "limit": "10", "offset": "0",
            }, hdrs)
            if text:
                pls = ((json.loads(text).get("result") or {}).get("playlists")) or []
                if pls:
                    pls.sort(key=lambda x: x.get("playCount") or 0, reverse=True)
                    pid = str(pls[0].get("id") or "")
        except Exception as exc:
            _log("playlist search err", exc)
        self._pl_cache[keyword] = pid
        return pid

    def _meting_playlist(self, pid, server="netease"):
        """拉取歌单全部歌曲 (meting, 一次最多 200 首)"""
        if not pid:
            return []
        cache_key = "%s_%s" % (server, pid)
        if cache_key in self._pl_data:
            return self._pl_data[cache_key]
        try:
            j = self._http_get_json(METING, {
                "type": "playlist", "id": str(pid), "server": server,
            }, timeout=15)
            if not isinstance(j, list):
                return []
            out = []
            for s in j:
                name = (s.get("name") or "").strip()
                if not name:
                    continue
                artist = s.get("artist") or ""
                if isinstance(artist, list):
                    artist = "/".join(str(a) for a in artist)
                url = s.get("url") or ""
                sid = ""
                m = re.search(r'[?&]id=([^&]+)', url)
                if m:
                    sid = m.group(1)
                out.append(_norm_song(
                    title=name, author=str(artist),
                    pic=s.get("pic") or "", url=url,
                    lrc_url=s.get("lrc") or "",
                    song_type=server, song_id=sid, src="mt", srv=server,
                ))
            self._pl_data[cache_key] = out
            return out
        except Exception as exc:
            _log("playlist err", exc)
            return []

    def _get_playlist_songs(self, idx):
        """按索引取预置歌单, 返回 (名称, 歌曲列表)"""
        try:
            i = int(idx) if str(idx).strip() else 0
        except Exception:
            i = 0
        if i < 0 or i >= len(_PLAYLISTS):
            i = 0
        item = _PLAYLISTS[i]
        pid = item.get("id") or self._playlist_search_id(item.get("kw", ""))
        songs = self._meting_playlist(pid)
        return item.get("name", ""), songs

    # ============ 源 B: 酷狗直链 (trackercdn) ============
    def _kg_url(self, song_hash, br="320"):
        """酷狗 hash -> mp3 直链 (320k 失败降 128k, status!=1 表示版权受限)"""
        if not song_hash:
            return ""
        for b in (br, "128"):
            key = hashlib.md5((song_hash + "kgcloudv2").encode()).hexdigest()
            j = self._http_get_json(KG_CDN, {
                "key": key, "hash": song_hash, "br": b,
                "appid": "1005", "pid": "2", "cmd": "25", "behavior": "play",
            }, timeout=8)
            if isinstance(j, dict) and j.get("status") == 1:
                u = j.get("url") or []
                if isinstance(u, list) and u:
                    return u[0]
                if isinstance(u, str) and u:
                    return u
        return ""

    # ============ 源 C: iqwq 聚合 (百度 / 网易备用) ============
    def _search_iqwq(self, keyword, platform, page):
        """iqwq 聚合API搜索, 只返回有有效音频URL的歌曲"""
        try:
            data = {
                "input": str(keyword),
                "filter": "name",
                "type": platform,
                "page": str(page),
            }
            text = self._http_post(SITE, data)
            if not text:
                return []
            result = json.loads(text)
            raw = result.get("data", []) or []

            valid = []
            for s in raw:
                url = s.get("url", "") or ""
                if not url or not _AUDIO_RE.search(url):
                    continue
                song_id = ""
                if platform == "netease":
                    m = re.search(r'[?&]id=(\d+)', url)
                    if m:
                        song_id = m.group(1)
                valid.append(_norm_song(
                    title=s.get("title", ""),
                    author=s.get("author", ""),
                    pic=s.get("pic", ""),
                    url=url,
                    lrc=s.get("lrc", ""),
                    song_type=platform,
                    song_id=song_id,
                    src="iqwq",
                ))
            return valid
        except Exception as exc:
            _log("search iqwq err", exc)
            return []

    # ============ 源 D: 网易云官方 (直链兜底) ============
    def _search_163(self, keyword, page):
        """网易云官方搜索, 只留免费歌 (fee=0/8) 用外链播放"""
        try:
            hdrs = {
                "User-Agent": UA,
                "Referer": NE163,
                "Content-Type": "application/x-www-form-urlencoded",
            }
            data = {
                "s": str(keyword),
                "type": "1",
                "offset": str((int(page) - 1) * 30),
                "limit": "30",
            }
            text = self._http_post(NE163 + "/api/search/get/web", data, hdrs)
            if not text:
                return []
            result = json.loads(text)
            songs = ((result.get("result") or {}).get("songs")) or []

            out = []
            for s in songs:
                if s.get("fee") not in (0, 8):
                    continue
                artists = "/".join(a.get("name", "") for a in s.get("artists", []) if a.get("name"))
                pic = ""
                album = s.get("album") or {}
                if album.get("picUrl"):
                    pic = album["picUrl"]
                out.append(_norm_song(
                    title=s.get("name", ""),
                    author=artists,
                    pic=pic,
                    url=NE163 + "/song/media/outer/url?id=%s.mp3" % s.get("id"),
                    song_type="wy163",
                    song_id=s.get("id"),
                    src="163",
                    dur=int((s.get("duration") or 0) / 1000),
                ))
            return out
        except Exception as exc:
            _log("search 163 err", exc)
            return []

    def _lyric_163(self, song_id):
        try:
            j = self._http_get_json(NE163 + "/api/song/lyric",
                                    {"id": str(song_id), "lv": "1", "kv": "1"},
                                    hdrs={"User-Agent": UA, "Referer": NE163},
                                    timeout=8)
            return ((j or {}).get("lrc") or {}).get("lyric") or ""
        except Exception:
            return ""

    # ============ 播放解析 ============
    def _resolve_url(self, song):
        """播放时获取直链, 逐级兜底"""
        src = song.get("src", "")
        srv = song.get("srv", "")
        sid = song.get("id", "")
        url = song.get("url", "")
        br = song.get("br", "") or ""

        # meting 源: 解析成真实 CDN 直链 (酷狗优先走官方 trackercdn)
        if src == "mt":
            if srv == "kugou" and br != "999":
                u = self._kg_url(sid)
                if u and not self._too_short(u):
                    return u
            u = self._meting_url(srv, sid, br)
            if u and not self._too_short(u):
                return u
            # 试听/残缺 → 换其他平台找完整版
            others = [x for x in ("netease", "tencent", "migu", "kugou") if x != srv]
            fb = self._fallback_url(song, others)
            if fb:
                return fb
            if u:
                return u      # 只有试听也比放不出来强
            # 代理直连兜底 (部分歌只在代理端可播)
            if url and self._probe_audio(url, timeout=6):
                return url
            return ""

        # iqwq 百度: 本身就是 CDN 直链
        if src == "iqwq" and song.get("type") == "baidu":
            return url

        # iqwq 网易: meting 解析优先(VIP可播) -> 外链 -> 官方 -> 跨源
        if src == "iqwq" and song.get("type") == "netease":
            if sid:
                u = self._meting_url("netease", sid, br)
                if u and not self._too_short(u):
                    return u
            if url and self._outer_ok(url):
                return url
            return self._fallback_url(song, ["tencent", "migu", "kugou"])

        # 网易官方外链
        if src == "163":
            if url and self._outer_ok(url):
                return url
            if sid:
                u = self._meting_url("netease", sid)
                if u:
                    return u
            return self._fallback_url(song, ["tencent", "migu"])

        if url:
            return url
        return ""

    def _fallback_url(self, song, servers):
        """跨源兜底: 用歌名+歌手去其他平台找同名歌"""
        title = song.get("title", "")
        author = song.get("author", "").split("/")[0]
        if not title:
            return ""
        for srv in servers:
            for kw in (("%s %s" % (title, author)).strip(), title):
                try:
                    for cand in self._meting_search(srv, kw, 1, 5):
                        if cand.get("title") != title:
                            continue
                        if srv == "kugou":
                            u = self._kg_url(cand.get("id"))
                        else:
                            u = self._meting_url(srv, cand.get("id"))
                        if u:
                            _log("跨源兜底 %s -> %s" % (title[:16], srv))
                            if not song.get("lrc_url"):
                                song["lrc_url"] = cand.get("lrc_url", "")
                            return u
                except Exception:
                    continue
        return ""

    def _probe_quick(self, song):
        """详情页用的轻量探测: 只解析一次, 不做跨源兜底(留给播放时)"""
        src = song.get("src", "")
        srv = song.get("srv", "")
        sid = song.get("id", "")
        url = song.get("url", "")
        if src == "mt":
            if srv == "kugou":
                return self._kg_url(sid) or self._meting_url(srv, sid, song.get("br", ""))
            return self._meting_url(srv, sid, song.get("br", ""))
        if src in ("iqwq", "163"):
            return url
        return url

    def _resolve_lyric(self, song):
        """歌词: 已有 -> meting代理 -> 网易官方"""
        if song.get("lrc"):
            return song["lrc"]
        txt = self._meting_lyric(song.get("lrc_url", ""))
        if txt:
            song["lrc"] = txt
            return txt
        if song.get("id") and song.get("type") in ("netease", "wy163"):
            txt = self._lyric_163(song["id"])
            if txt:
                song["lrc"] = txt
        return song.get("lrc", "")

    def _play_header(self, song, url):
        """按源返回合适的请求头"""
        header = {"User-Agent": UA}
        srv = song.get("srv", "")
        src = song.get("src", "")
        if srv == "tencent":
            header["Referer"] = "https://y.qq.com/"
        elif srv == "kugou":
            header["Referer"] = "http://www.kugou.com/"
        elif srv in ("netease", "migu") or src in ("163", "iqwq"):
            header["Referer"] = NE163 + "/"
        elif "kugou" in (url or ""):
            header["Referer"] = "http://www.kugou.com/"
        elif "qq.com" in (url or ""):
            header["Referer"] = "https://y.qq.com/"
        else:
            header["Referer"] = SITE
        return header

    # ============ 统一搜索入口 ============
    def _search_platform(self, keyword, platform, page=1):
        if platform in _METING_SERVERS:
            songs = self._meting_search(platform, keyword, page)
            # 网易/酷狗结果偏少时用 iqwq 补 (百度/iQWQ 源只补百度)
            if len(songs) < 5 and platform == "netease":
                songs += self._search_iqwq(keyword, "netease", page)
            return songs
        if platform == "baidu":
            songs = self._search_iqwq(keyword, "baidu", page)
            if len(songs) < 5:
                songs += self._search_163(keyword, page)
            return songs
        return []

    def _song_to_vod(self, song):
        title = song.get("title", "") or "未知"
        author = song.get("author", "") or ""
        pic = song.get("pic", "") or ""
        song_info = json.dumps(song, ensure_ascii=False)
        return {
            "vod_id": _b64encode(song_info),
            "vod_name": title,
            "vod_pic": pic,
            "vod_remarks": author,
        }

    def _recommend(self, limit=20):
        """首页推荐: 热歌榜前段 + 各平台热门, 去重"""
        all_songs = []
        seen = set()

        def _add(songs):
            for s in songs:
                sig = "%s_%s" % (s.get("title", ""), s.get("author", ""))
                if sig and sig not in seen:
                    seen.add(sig)
                    all_songs.append(s)

        # 热歌榜质量最高, 优先取
        _add(self._meting_playlist("3778678")[:12])
        if len(all_songs) < limit:
            _add(self._meting_search("tencent", "热歌", 1, 6))
        if len(all_songs) < limit:
            _add(self._meting_search("netease", "流行", 1, 8))
        return all_songs[:limit]

    # ============ 首页 ============
    def homeContent(self, filter=False):
        try:
            classes = [
                {"type_id": tid, "type_pid": "0", "type_name": name}
                for tid, (_, name) in sorted(_CATEGORY.items())
            ]
            filters = {}
            if filter:
                for tid, (platform, _) in _CATEGORY.items():
                    if platform == "playlist":
                        filters[tid] = [{
                            "key": "pl",
                            "name": "歌单",
                            "value": [
                                {"n": item["name"], "v": str(i)}
                                for i, item in enumerate(_PLAYLISTS)
                            ],
                        }, {
                            "key": "br", "name": "音质", "value": _QUALITY,
                        }]
                        continue
                    if platform == "missevan":
                        filters[tid] = [{
                            "key": "kw", "name": "类型",
                            "value": [{"n": k, "v": k} for k in _MS_KEYWORDS],
                        }]
                        continue
                    values = _PLATFORM_FILTERS.get(platform, [])
                    if values:
                        filters[tid] = [{
                            "key": "kw",
                            "name": "关键词",
                            "value": values,
                        }, {
                            "key": "br", "name": "音质", "value": _QUALITY,
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
            return {"list": [self._song_to_vod(s) for s in self._recommend(10)]}
        except Exception:
            return {"list": []}

    # ============ 分类 ============
    def categoryContent(self, tid, pg, filter=False, extend=None):
        extend = extend or {}
        try:
            page = int(pg) if pg else 1
        except Exception:
            page = 1

        platform = "netease"
        if str(tid) in _CATEGORY:
            platform, _ = _CATEGORY[str(tid)]
        keyword = extend.get("kw", "") if extend else ""
        quality = (extend.get("br", "") or "").strip() if extend else ""

        result = {
            "list": [],
            "page": page,
            "pagecount": 20,
            "limit": 20,
            "total": 400,
        }

        # ---- 广播剧: 猫耳FM 剧集 (多集连续剧形式) ----
        if platform == "missevan":
            try:
                if keyword:
                    shows = self._ms_search(keyword, page)
                else:
                    idx = (page - 1) % len(_MS_KEYWORDS)
                    shows = self._ms_search(_MS_KEYWORDS[idx],
                                            ((page - 1) // len(_MS_KEYWORDS)) + 1)
                    if len(shows) < 10:
                        shows += self._ms_search(
                            _MS_KEYWORDS[(idx + 1) % len(_MS_KEYWORDS)], 1)
                result["list"] = [self._song_to_vod(s) for s in shows]
                result["limit"] = len(shows)
                result["total"] = 5000
                result["pagecount"] = 99
                _log("广播剧 %s 第 %d 页 %d 部" % (keyword or "默认", page, len(shows)))
                return result
            except Exception as exc:
                _log("missevan category err", exc)
                return result

        # ---- 歌单/榜单: 固定歌单或按关键词动态搜到的歌单, 每页 50 首 ----
        if platform == "playlist":
            try:
                pl_idx = extend.get("pl", "0") if extend else "0"
                name, songs = self._get_playlist_songs(pl_idx)
                size = 50
                chunk = songs[(page - 1) * size: page * size]
                for s in chunk:
                    s["br"] = quality
                result["list"] = [self._song_to_vod(s) for s in chunk]
                result["limit"] = len(chunk)
                result["total"] = len(songs)
                result["pagecount"] = max(1, (len(songs) + size - 1) // size)
                _log("歌单 %s 共 %d 首, 第 %d 页 %d 首" % (name, len(songs), page, len(chunk)))
                return result
            except Exception as exc:
                _log("playlist category err", exc)
                return result

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
                if len(all_songs) < 8:
                    _add(self._search_platform(keyword, platform, page + 1))
            else:
                # 每页轮换 2 个热词, 关键词用完则循环
                per_page = 2
                start = ((page - 1) * per_page) % len(_HOT_WORDS)
                kw_list = []
                for i in range(per_page):
                    kw_list.append(_HOT_WORDS[(start + i) % len(_HOT_WORDS)])
                for kw in kw_list:
                    _add(self._search_platform(kw, platform, 1))

            # 结果太少时再补几个热词
            if len(all_songs) < 8:
                for kw in _HOT_WORDS:
                    if kw == keyword:
                        continue
                    _add(self._search_platform(kw, platform, 1))
                    if len(all_songs) >= 15:
                        break

            if all_songs:
                if quality:
                    for s in all_songs:
                        s["br"] = quality
                result["list"] = [self._song_to_vod(s) for s in all_songs]
                result["limit"] = len(all_songs)
                result["total"] = max(400, len(all_songs) * 10)
        except Exception as exc:
            _log("categoryContent err", exc)

        return result

    # ============ 详情 ============
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
            if song.get("src") == "ms":
                return self._ms_detail(song)
            title = song.get("title", "") or "未知"
            author = song.get("author", "") or ""
            pic = song.get("pic", "") or ""
            song_type = song.get("type", "") or "音乐"
            # 轻量探测 (只验证一次, 跨源兜底留给播放时, 避免详情页卡顿)
            play_url = self._probe_quick(dict(song))
            self._resolve_lyric(song)

            song_info = json.dumps(song, ensure_ascii=False)
            new_vid = _b64encode(song_info)
            play_url_field = "%s$%s" % (title, new_vid)

            src_name = {
                "netease": "网易云", "tencent": "QQ音乐",
                "kugou": "酷狗音乐", "migu": "咪咕音乐",
                "baidu": "百度音乐", "wy163": "网易云官方",
            }.get(song_type, song_type)

            vod = {
                "vod_id": new_vid,
                "vod_name": title,
                "vod_pic": pic,
                "vod_remarks": author,
                "vod_year": "",
                "vod_area": src_name,
                "vod_content": ("歌手: %s\n平台: %s\n状态: %s" % (
                    author, src_name,
                    "可播放" if play_url else "直链解析失败，播放时会重试")),
                "vod_play_from": "音乐播放",
                "vod_play_url": play_url_field,
            }
            return {"list": [vod]}
        except Exception as exc:
            _log("detailContent err", exc)
            return {"list": []}

    def _ms_detail(self, song):
        """广播剧详情: 免费集拼成连续剧播放列表"""
        did = song.get("id", "")
        drama, eps = self._ms_episodes(did)
        if not eps:
            eps = [e for e in (song.get("eps") or []) if e.get("id")]
        if not eps:
            return {"list": []}
        title = song.get("title", "") or "未知"
        pic = song.get("pic") or drama.get("cover") or ""
        intro = str(drama.get("intro") or song.get("intro") or "").strip()
        parts = []
        for i, e in enumerate(eps):
            name = (e.get("name") or ("第%d集" % (i + 1)))
            name = name.replace("$", " ").replace("#", " ")
            vid = _b64encode(json.dumps({
                "src": "ms_ep", "sid": e.get("id"), "title": name,
                "pic": pic, "dur": e.get("dur", 0),
            }, ensure_ascii=False))
            parts.append("%s$%s" % (name, vid))
        _log("广播剧 %s 免费集 %d" % (title[:16], len(eps)))
        return {"list": [{
            "vod_id": _b64encode(json.dumps(song, ensure_ascii=False)),
            "vod_name": title,
            "vod_pic": pic,
            "vod_remarks": "%s · %d集免费" % (
                (song.get("author") or "广播剧").split(" · ")[0], len(eps)),
            "vod_year": "",
            "vod_area": "猫耳FM",
            "vod_content": (intro[:300] if intro else "猫耳FM 广播剧")
                           + "\n共 %d 个免费集(付费集不显示)" % len(eps),
            "vod_play_from": "猫耳FM",
            "vod_play_url": "#".join(parts),
        }]}

    # ============ 播放 ============
    def playerContent(self, flag, id, vipFlags):
        _log("playerContent ->", str(id)[:50] if id else "")
        try:
            vid = str(id).split("$")[-1].strip()
            song_json = _b64decode(vid)
            if song_json:
                song = json.loads(song_json)
                if song.get("src") == "ms_ep":
                    url = self._ms_sound_url(song.get("sid", ""))
                    if url:
                        return {
                            "parse": 0,
                            "url": url,
                            "header": {"User-Agent": UA, "Referer": MISSEVAN + "/"},
                            "playUrl": "",
                        }
                    return {"parse": 0, "url": "", "header": {}, "playUrl": ""}
                url = self._resolve_url(song)
                if url:
                    _log("播放地址:", url[:80])
                    return {
                        "parse": 0,
                        "url": url,
                        "header": self._play_header(song, url),
                        "playUrl": "",
                    }
        except Exception as exc:
            _log("playerContent err", exc)
        return {"parse": 0, "url": "", "header": {}, "playUrl": ""}

    # ============ 搜索 ============
    def searchContent(self, key, quick, pg="1"):
        """搜索: 遍历所有音源合并结果, 去重"""
        if not key:
            return {"list": []}
        try:
            page = int(pg) if pg else 1
            vod_list = []
            seen = set()
            order = ["netease", "tencent", "kugou", "migu", "baidu"]
            for platform in order:
                songs = self._search_platform(key, platform, page)
                for song in songs:
                    sig = "%s_%s" % (song.get("title", ""), song.get("author", ""))
                    if sig and sig not in seen:
                        seen.add(sig)
                        vod_list.append(self._song_to_vod(song))
                if len(vod_list) >= 30:
                    break
            return {"list": vod_list}
        except Exception as exc:
            _log("searchContent err", exc)
            return {"list": []}
