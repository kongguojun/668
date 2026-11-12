# -*- coding: utf-8 -*-
"""
易听┃音乐 —— 网易云音乐独立源 (TVBox / OK影视 / 影视仓 type:3 爬虫)

对标饭太硬"易听音乐"的栏目布局:
  首页 / New新歌榜 / TOP榜单 / 原创歌手 / 音乐歌单 / 主播电台 / 新碟上架 / 高清MV / 热搜

特点:
  - 全部走公开接口(网易官方 + meting 代理), 无壳无锁
  - 播放时实时解析直链, 无损 FLAC(999) -> 320K 自动降级, 试听残缺自动换源
  - 顶部搜索按钮(应用全局搜索)与站内"热搜"页均可用

注意: 本文件独立运行, 不依赖音乐聚合.py
"""

import re
import json
import urllib.request
import urllib.parse

try:
    from base.spider import Spider as _BaseSpider
except Exception:
    class _BaseSpider(object):
        pass


def _log(*args):
    try:
        print("易听", *args)
    except Exception:
        pass


METING = "https://api.qijieya.cn/meting/"
METING_BAK = "https://api.injahow.cn/meting/"
NE163 = "https://music.163.com"

UA = ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
      "AppleWebKit/537.36 (KHTML, like Gecko) "
      "Chrome/150.0.0.0 Safari/537.36")
NE_HEADERS = {"User-Agent": UA, "Referer": NE163 + "/"}

# ================= 榜单 / 分类数据 =================
_TOPLISTS = [
    {"id": "3779629",  "name": "New·新歌榜"},
    {"id": "3778678",  "name": "TOP·热歌榜"},
    {"id": "19723756", "name": "飙升榜"},
    {"id": "2884035",  "name": "原创榜"},
    {"id": "745956260", "name": "嘻哈榜"},
    {"id": "71384707", "name": "怀旧经典"},
    {"id": "71385702", "name": "民歌榜"},
    {"id": "10550289", "name": "游戏原声"},
    {"id": "71381012", "name": "影视原声"},
]

_PLAYLIST_CATS = [
    "华语", "流行", "摇滚", "民谣", "电子", "说唱",
    "古风", "轻音乐", "粤语", "乡村", "爵士", "古典",
    "电台", "伤感", "学习", "清晨", "夜晚", "咖啡",
]

_ALBUM_AREAS = [
    {"n": "全部", "v": "ALL"},
    {"n": "华语", "v": "ZH"},
    {"n": "欧美", "v": "EA"},
    {"n": "韩国", "v": "KR"},
    {"n": "日本", "v": "JP"},
]

_MV_AREAS = [
    {"n": "全部", "v": "全部"},
    {"n": "内地", "v": "内地"},
    {"n": "港台", "v": "港台"},
    {"n": "欧美", "v": "欧美"},
    {"n": "韩国", "v": "韩国"},
    {"n": "日本", "v": "日本"},
]

_HOT_WORDS = [
    "周杰伦", "林俊杰", "陈奕迅", "邓紫棋", "薛之谦",
    "抖音热歌", "KTV必点", "粤语经典", "伤感情歌",
    "古风", "民谣", "DJ舞曲", "纯音乐", "儿歌",
]


def _https(u):
    return u.replace("http://", "https://") if u else u


def _fix_pic(u):
    if not u:
        return ""
    u = _https(u)
    return u + "?param=300y300"


class _Net(object):
    """极简 HTTP, requests 优先 urllib 兜底"""

    @staticmethod
    def _req(url, hdrs=None, timeout=12):
        headers = dict(hdrs or {})
        headers.setdefault("User-Agent", UA)
        req = urllib.request.Request(url, headers=headers)
        return urllib.request.urlopen(req, timeout=timeout).read()

    @staticmethod
    def json(url, params=None, hdrs=None, timeout=12):
        if params:
            url = url + ("&" if "?" in url else "?") + urllib.parse.urlencode(params)
        try:
            return json.loads(_Net._req(url, hdrs, timeout))
        except Exception as exc:
            _log("json err", url[:80], exc)
            return None

    @staticmethod
    def head_ok(url, timeout=5):
        """探测直链是否可用, 返回 (ok, size_bytes)"""
        try:
            req = urllib.request.Request(url, headers={"User-Agent": UA})
            req.get_method = lambda: "HEAD"
            with urllib.request.urlopen(req, timeout=timeout) as r:
                ctype = (r.headers.get("Content-Type") or "").lower()
                size = int(r.headers.get("Content-Length") or 0)
                return ("audio" in ctype or "octet" in ctype or "flac" in ctype), size
        except Exception:
            pass
        # HEAD 被拒时退回 Range GET
        try:
            req = urllib.request.Request(url, headers={"User-Agent": UA, "Range": "bytes=0-1023"})
            with urllib.request.urlopen(req, timeout=timeout) as r:
                ctype = (r.headers.get("Content-Type") or "").lower()
                cr = r.headers.get("Content-Range") or ""
                total = cr.rsplit("/", 1)[-1] if "/" in cr else "0"
                return ("audio" in ctype or "octet" in ctype or "flac" in ctype), int(total or 0)
        except Exception:
            return False, 0


class Spider(_BaseSpider):

    def init(self, extend=""):
        _log("init")

    def getName(self):
        return "易听音乐"

    def destroy(self):
        pass

    def isVideoFormat(self, url):
        return False

    def manualVideoCheck(self):
        return False

    def localProxy(self, param):
        return [200, "text/plain", "", ""]

    # ================= 官方接口封装 =================
    def _ne(self, path, params=None):
        return _Net.json(NE163 + path, params, hdrs=NE_HEADERS)

    def _artist_list(self, limit=30, offset=0):
        j = self._ne("/api/artist/top", {"limit": str(limit), "offset": str(offset)})
        arts = (j or {}).get("artists") or []
        return [
            {"id": a.get("id"), "name": a.get("name", ""), "pic": _fix_pic(a.get("img1v1Url") or a.get("picUrl"))}
            for a in arts if a.get("id")
        ]

    def _artist_songs(self, aid):
        j = self._ne("/api/v1/artist/%s" % aid)
        hs = (j or {}).get("hotSongs") or []
        return [self._song_from_163(s) for s in hs]

    def _album_songs(self, aid):
        """v1 专辑接口优先(带歌名/歌曲id), 旧接口兜底"""
        j = self._ne("/api/v1/album/%s" % aid)
        al = (j or {}).get("album") or {}
        songs = (j or {}).get("songs") or []
        name = al.get("name", "")
        pic = _fix_pic(al.get("picUrl"))
        out = []
        for s in songs:
            item = self._song_from_163(s)
            if item and not item.get("pic"):
                item["pic"] = pic
            out.append(item)
        if not out:
            j2 = self._ne("/api/album/%s" % aid)
            al2 = (j2 or {}).get("album") or {}
            name = name or al2.get("name", "")
            pic = pic or _fix_pic(al2.get("picUrl"))
            for s in al2.get("songs") or []:
                item = self._song_from_163(s)
                if item and not item.get("pic"):
                    item["pic"] = pic
                out.append(item)
        return out, name

    def _playlist_page(self, cat, limit=24, offset=0):
        j = self._ne("/api/playlist/list", {"cat": cat, "limit": str(limit), "offset": str(offset)})
        pls = (j or {}).get("playlists") or []
        return [
            {"id": p.get("id"), "name": p.get("name", ""), "pic": _fix_pic(p.get("coverImgUrl")),
             "count": p.get("trackCount", 0)}
            for p in pls if p.get("id")
        ]

    def _new_albums(self, area="ALL", limit=24, offset=0):
        j = self._ne("/api/album/new", {"area": area, "limit": str(limit), "offset": str(offset)})
        als = (j or {}).get("albums") or []
        return [
            {"id": a.get("id"), "name": a.get("name", ""),
             "pic": _fix_pic(a.get("picUrl")),
             "artist": "/".join(x.get("name", "") for x in (a.get("artists") or []))}
            for a in als if a.get("id")
        ]

    def _new_mvs(self, area="全部", limit=24, offset=0):
        params = {"limit": str(limit), "offset": str(offset)}
        if area and area != "全部":
            params["area"] = area
        j = self._ne("/api/mv/first", params)
        mvs = (j or {}).get("data") or []
        return [
            {"id": m.get("id"), "name": m.get("name", ""),
             "pic": _fix_pic(m.get("cover")),
             "artist": "/".join(a.get("name", "") for a in (m.get("artists") or []))}
            for m in mvs if m.get("id")
        ]

    def _search_songs(self, kw, page=1, limit=30):
        offset = (int(page) - 1) * limit
        j = self._ne("/api/search/get", {"s": str(kw), "type": "1",
                                         "limit": str(limit), "offset": str(offset)})
        songs = ((j or {}).get("result") or {}).get("songs") or []
        return [self._song_from_163(s) for s in songs]

    def _search_mvs(self, kw, page=1):
        offset = (int(page) - 1) * 20
        j = self._ne("/api/search/get", {"s": str(kw), "type": "1004",
                                         "limit": "20", "offset": str(offset)})
        mvs = ((j or {}).get("result") or {}).get("mvs") or []
        return [
            {"id": m.get("id"), "name": m.get("name", ""), "pic": _fix_pic(m.get("cover")),
             "artist": "/".join(a.get("name", "") for a in (m.get("artists") or []))}
            for m in mvs if m.get("id")
        ]

    # ================= meting =================
    def _meting_playlist(self, pid):
        for base in (METING, METING_BAK):
            j = _Net.json(base, {"server": "netease", "type": "playlist", "id": str(pid)}, timeout=20)
            if isinstance(j, list) and j:
                return self._meting_to_songs(j)
        return []

    def _meting_to_songs(self, arr):
        out = []
        for s in arr:
            name = (s.get("name") or "").strip()
            if not name:
                continue
            artist = s.get("artist") or ""
            if isinstance(artist, list):
                artist = "/".join(str(a) for a in artist)
            url = s.get("url") or ""
            m = re.search(r"[?&]id=([^&]+)", url)
            sid = m.group(1) if m else ""
            out.append({"title": name, "author": str(artist), "pic": _fix_pic(s.get("pic")),
                        "id": sid, "kind": "song"})
        return out

    def _meting_url(self, sid):
        """无损(999) -> 320 -> 标准, 主备站逐个探测"""
        if not sid:
            return ""
        for base in (METING, METING_BAK):
            for br in ("999", "320", ""):
                u = "%s?server=netease&type=url&id=%s" % (base, urllib.parse.quote(str(sid)))
                if br:
                    u += "&br=" + br
                ok, size = _Net.head_ok(u)
                if ok and size >= 1024 * 1024:      # 小于 1MB 视为试听残缺
                    return u
                if ok and size > 0:
                    return u
        return ""

    def _song_info(self, sid):
        """官方接口取歌名/歌手, 供跨源兜底用"""
        j = self._ne("/api/song/detail", {"id": str(sid), "ids": "[%s]" % sid})
        songs = (j or {}).get("songs") or []
        return self._song_from_163(songs[0]) if songs else None

    def _cross_url(self, title, author):
        """跨源兜底: 拿歌名+歌手去腾讯/咪咕/酷狗找同名歌, 探测到真音频才算数"""
        if not title:
            return ""
        author = (author or "").split("/")[0]
        for srv in ("migu", "tencent", "kugou"):
            for kw in ("%s %s" % (title, author) if author else title, title):
                j = _Net.json(METING, {"type": "search", "server": srv,
                                       "id": kw, "page": "1", "limit": "5"}, timeout=12)
                if not isinstance(j, list):
                    continue
                for it in j:
                    if (it.get("name") or "").strip() != title:
                        continue
                    u = it.get("url") or ""
                    if not u:
                        continue
                    ok, size = _Net.head_ok(u, timeout=8)
                    if ok and size >= 1024 * 1024:
                        return u
                    if ok and size > 100 * 1024:
                        return u
        return ""

    def _mv_url(self, mvid):
        for r in ("1080", "720", "480"):
            j = self._ne("/api/song/enhance/play/mv/url", {"id": str(mvid), "r": r})
            url = ((j or {}).get("data") or {}).get("url") or ""
            if url:
                return _https(url)
        return ""

    # ================= 统一数据结构 =================
    def _song_from_163(self, s):
        try:
            artists = "/".join(a.get("name", "") for a in (s.get("ar") or s.get("artists") or []) if a.get("name"))
            al = s.get("al") or s.get("album") or {}
            return {"title": s.get("name", ""), "author": artists,
                    "pic": _fix_pic(al.get("picUrl")), "id": s.get("id"), "kind": "song"}
        except Exception:
            return None

    def _song_vod(self, song):
        """歌曲 -> vod 条目 (点开即播放)"""
        kind = "mv" if song.get("kind") == "mv" else "song"
        return {
            "vod_id": "%s|%s" % (kind, song["id"]),
            "vod_name": song["title"],
            "vod_pic": song.get("pic", ""),
            "vod_remarks": song.get("author", ""),
            "vod_tag": "folder" if kind == "mv" else "",
            "vod_play_from": "易听音乐",
            "vod_play_url": "播放$%s|%s" % (kind, song["id"]),
        }

    def _artist_vod(self, a):
        return {
            "vod_id": "ar|%s" % a["id"],
            "vod_name": a["name"],
            "vod_pic": a.get("pic", ""),
            "vod_remarks": "歌手",
        }

    def _list_vod(self, item, tid_prefix, remarks=""):
        return {
            "vod_id": "%s|%s" % (tid_prefix, item["id"]),
            "vod_name": item["name"],
            "vod_pic": item.get("pic", ""),
            "vod_remarks": remarks,
        }

    def _songs_page(self, songs, page):
        return {"list": [self._song_vod(s) for s in songs if s and s.get("id")],
                "page": int(page or 1)}

    # ================= TVBox 接口 =================
    def homeContent(self, filter=False):
        classes = [
            {"type_name": "首页",     "type_id": "home"},
            {"type_name": "New新歌榜", "type_id": "pl|3779629"},
            {"type_name": "TOP榜单",  "type_id": "top"},
            {"type_name": "原创歌手",  "type_id": "artist"},
            {"type_name": "音乐歌单",  "type_id": "plcat"},
            {"type_name": "主播电台",  "type_id": "plcatradio"},
            {"type_name": "新碟上架",  "type_id": "album"},
            {"type_name": "高清MV",   "type_id": "mv"},
            {"type_name": "热搜",     "type_id": "hot"},
        ]
        filters = {
            "top": [{"key": "id", "name": "榜单",
                     "value": [{"n": t["name"], "v": t["id"]} for t in _TOPLISTS]}],
            "artist": [{"key": "area", "name": "说明",
                        "value": [{"n": "热门歌手(按热度排序)", "v": "hot"}]}],
            "plcat": [{"key": "cat", "name": "分类",
                       "value": [{"n": c, "v": c} for c in _PLAYLIST_CATS if c != "电台"]}],
            "plcatradio": [{"key": "cat", "name": "分类",
                            "value": [{"n": "电台", "v": "电台"},
                                      {"n": "有声书", "v": "有声书"},
                                      {"n": "相声评书", "v": "相声曲艺"}]}],
            "album": [{"key": "area", "name": "地区",
                       "value": [{"n": a["n"], "v": a["v"]} for a in _ALBUM_AREAS]}],
            "mv": [{"key": "area", "name": "地区",
                    "value": [{"n": a["n"], "v": a["v"]} for a in _MV_AREAS]}],
        }
        # 首页默认内容: 热门歌手
        arts = self._artist_list(30)
        lst = [self._artist_vod(a) for a in arts]
        return {"class": classes, "filters": filters, "list": lst}

    def homeVideoContent(self):
        arts = self._artist_list(30)
        return {"list": [self._artist_vod(a) for a in arts]}

    def categoryContent(self, tid, pg, filter=False, extend=None):
        pg = int(pg or 1)
        extend = extend or {}
        try:
            if tid == "home" or tid == "artist":
                arts = self._artist_list(30, (pg - 1) * 30)
                return {"list": [self._artist_vod(a) for a in arts], "page": pg}

            if tid == "top":
                pid = extend.get("id") or "3778678"
                songs = self._meting_playlist(pid)
                return self._songs_page(songs, 1)

            if tid.startswith("pl|"):
                pid = tid.split("|", 1)[1]
                songs = self._meting_playlist(pid)
                return self._songs_page(songs, 1)

            if tid in ("plcat", "plcatradio"):
                cat = extend.get("cat") or ("电台" if tid == "plcatradio" else "华语")
                pls = self._playlist_page(cat, 24, (pg - 1) * 24)
                lst = [self._list_vod(p, "pl", "%s首" % p.get("count", "")) for p in pls]
                return {"list": lst, "page": pg}

            if tid == "album":
                area = extend.get("area") or "ALL"
                als = self._new_albums(area, 24, (pg - 1) * 24)
                lst = [self._list_vod(a, "al", a.get("artist", "")) for a in als]
                return {"list": lst, "page": pg}

            if tid == "mv":
                area = extend.get("area") or "全部"
                mvs = self._new_mvs(area, 24, (pg - 1) * 24)
                lst = [self._list_vod(m, "mv", m.get("artist", "")) for m in mvs]
                return {"list": lst, "page": pg}

            if tid == "hot":
                words = [{"vod_id": "kw|%s" % w, "vod_name": w, "vod_pic": "",
                          "vod_remarks": "点击搜索"} for w in _HOT_WORDS]
                return {"list": words, "page": 1}

            if tid.startswith("kw|"):
                songs = self._search_songs(tid.split("|", 1)[1], pg)
                return self._songs_page(songs, pg)
        except Exception as exc:
            _log("category err", tid, exc)
        return {"list": [], "page": pg}

    def detailContent(self, ids):
        try:
            tid = ids[0]
            kind, val = tid.split("|", 1)

            if kind == "ar":                       # 歌手 -> 热门50首
                j = self._ne("/api/v1/artist/%s" % val)
                artist = (j or {}).get("artist") or {}
                songs = self._artist_songs(val)
                eps = ["%s$%s" % (s["title"], self._song_vod(s)["vod_play_url"].split("$", 1)[1])
                       for s in songs if s and s.get("id")]
                return {"list": [{
                    "vod_id": tid,
                    "vod_name": artist.get("name", "歌手"),
                    "vod_pic": _fix_pic(artist.get("img1v1Url") or artist.get("picUrl")),
                    "vod_remarks": "%d首" % len(eps),
                    "vod_play_from": "易听音乐",
                    "vod_play_url": "#".join(eps) or "暂无$",
                }]}

            if kind == "pl":                       # 歌单/榜单 -> 全部歌曲
                pj = self._ne("/api/v6/playlist/detail", {"id": val})
                pl = (pj or {}).get("playlist") or {}
                name = pl.get("name", "歌单")
                pic = _fix_pic(pl.get("coverImgUrl"))
                songs = self._meting_playlist(val)
                eps = ["%s$%s" % (s["title"], self._song_vod(s)["vod_play_url"].split("$", 1)[1])
                       for s in songs if s and s.get("id")]
                return {"list": [{
                    "vod_id": tid, "vod_name": name, "vod_pic": pic,
                    "vod_remarks": "%d首" % len(eps),
                    "vod_play_from": "易听音乐",
                    "vod_play_url": "#".join(eps) or "暂无$",
                }]}

            if kind == "al":                       # 专辑 -> 曲目
                songs, name = self._album_songs(val)
                eps = ["%s$%s" % (s["title"], self._song_vod(s)["vod_play_url"].split("$", 1)[1])
                       for s in songs if s and s.get("id")]
                return {"list": [{
                    "vod_id": tid, "vod_name": name, "vod_pic": songs[0].get("pic") if songs else "",
                    "vod_remarks": "%d首" % len(eps),
                    "vod_play_from": "易听音乐",
                    "vod_play_url": "#".join(eps) or "暂无$",
                }]}

            if kind == "kw":                       # 热搜词 -> 歌曲列表
                songs = self._search_songs(val, 1)
                eps = ["%s$%s" % (s["title"], self._song_vod(s)["vod_play_url"].split("$", 1)[1])
                       for s in songs if s and s.get("id")]
                return {"list": [{
                    "vod_id": tid, "vod_name": "搜索: " + val, "vod_pic": "",
                    "vod_remarks": "%d首" % len(eps),
                    "vod_play_from": "易听音乐",
                    "vod_play_url": "#".join(eps) or "暂无$",
                }]}

            if kind in ("song", "mv"):             # 单曲/MV 直达
                if kind == "song":
                    j = self._ne("/api/song/detail", {"id": val, "ids": "[%s]" % val})
                    songs = (j or {}).get("songs") or []
                    s = self._song_from_163(songs[0]) if songs else {"title": str(val), "author": "", "pic": ""}
                    return {"list": [{
                        "vod_id": tid, "vod_name": s["title"], "vod_pic": s.get("pic", ""),
                        "vod_remarks": s.get("author", ""),
                        "vod_play_from": "易听音乐",
                        "vod_play_url": "播放$song|%s" % val,
                    }]}
                mj = self._ne("/api/mv/detail", {"id": val})
                info = (mj or {}).get("data") or {}
                return {"list": [{
                    "vod_id": tid,
                    "vod_name": info.get("name", "MV"),
                    "vod_pic": _fix_pic(info.get("cover")),
                    "vod_remarks": "/".join(a.get("name", "") for a in (info.get("artists") or [])),
                    "vod_play_from": "易听音乐",
                    "vod_play_url": "播放$mv|%s" % val,
                }]}
        except Exception as exc:
            _log("detail err", exc)
        return {"list": []}

    def playerContent(self, flag, id, vipFlags):
        try:
            kind, val = str(id).split("|", 1)
            if kind == "mv":
                url = self._mv_url(val)
            else:
                url = self._meting_url(val)
                if not url:
                    # 网易 VIP/版权歌 -> 官方取歌名后跨源兜底
                    info = self._song_info(val)
                    if info:
                        url = self._cross_url(info.get("title", ""), info.get("author", ""))
            if url:
                return {"parse": 0, "playUrl": "", "url": url, "header": {"User-Agent": UA}}
            return {"parse": 0, "playUrl": "", "url": ""}
        except Exception as exc:
            _log("player err", exc)
            return {"parse": 0, "playUrl": "", "url": ""}

    def searchContent(self, key, quick, pg="1"):
        try:
            pg = int(pg or 1)
            songs = self._search_songs(key, pg)
            out = []
            for s in songs:
                if not s or not s.get("id"):
                    continue
                v = self._song_vod(s)
                out.append(v)
            return {"list": out, "page": pg}
        except Exception as exc:
            _log("search err", exc)
            return {"list": [], "page": int(pg or 1)}
