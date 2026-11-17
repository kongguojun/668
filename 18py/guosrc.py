# -*- coding: utf-8 -*-
"""
guosrc.py —— 红果 / 禁果 / 剧果 / 黑桃 四站源（OK影视 CatVod Python 爬虫）

独立文件，不依赖 zhenguo.py，不改动它。
用法：OK影视配置里写
    {"key":"guosrc","name":"果源","type":3,"api":"https://你的地址/guosrc.py",
     "searchable":1,"changeable":1,"timeout":30}

接口：标准 CatVod Spider（homeContent / categoryContent / detailContent /
      searchContent / playerContent）。只用标准库，无需 pycryptodome。
"""

import gzip
import json
import re
import threading
import time
import urllib.error
import urllib.parse
import urllib.request
import uuid

try:
    from base.spider import Spider as BaseSpider
except Exception:
    class BaseSpider(object):
        pass

__version__ = "1.0.0"

PC_UA = ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
         "(KHTML, like Gecko) Chrome/131.0.0.0 Safari/537.36")
MOB_UA = ("Mozilla/5.0 (Linux; Android 13; Pixel 7) AppleWebKit/537.36 "
          "(KHTML, like Gecko) Chrome/126.0.0.0 Mobile Safari/537.36")
IPHONE_UA = ("Mozilla/5.0 (iPhone; CPU iPhone OS 18_7 like Mac OS X) "
             "AppleWebKit/605.1.15 (KHTML, like Gecko) Version/18.7 "
             "Mobile/15E148 Safari/604.1")


# ------------------------------------------------------------------ 小工具

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
        s = _s(v)
        if s:
            return s
    return ""


def _pick_int(d, *keys):
    if not isinstance(d, dict):
        return 0
    for k in keys:
        try:
            n = int(float(_s(d.get(k))))
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
    s = re.sub(r"&nbsp;", " ", s)
    s = re.sub(r"\s+", " ", s)
    return s.strip()


def _q(s):
    return urllib.parse.quote(_s(s), safe="")


def _uq(s):
    return urllib.parse.unquote(_s(s))


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


def _leading_json(text, start):
    """从 start 起解析一个完整 JSON 对象/数组。"""
    if start < 0:
        return None
    depth = 0
    in_str = False
    esc = False
    for i in range(start, len(text)):
        c = text[i]
        if in_str:
            if esc:
                esc = False
            elif c == "\\":
                esc = True
            elif c == '"':
                in_str = False
            continue
        if c == '"':
            in_str = True
        elif c in "{[":
            depth += 1
        elif c in "}]":
            depth -= 1
            if depth == 0:
                try:
                    return json.loads(text[start:i + 1])
                except Exception:
                    return None
        elif depth == 0 and c > " ":
            return None
    return None


def _router_page(html, *names):
    """取 Next/Modern SSR 的 _ROUTER_DATA.loaderData 里指定名字的节点。"""
    m = re.search(r"(?:window\.)?_ROUTER_DATA\s*=\s*", html or "")
    if not m:
        return {}
    data = _leading_json(html, m.end())
    if not isinstance(data, dict):
        return {}
    loader = data.get("loaderData") or {}
    for name in names:
        node = loader.get(name)
        if isinstance(node, dict) and node:
            return node
    for key, node in loader.items():
        for name in names:
            prefix = name.rstrip("$")
            if prefix and key.startswith(prefix) and isinstance(node, dict) and node:
                return node
    return {}


def _cf_blocked(html):
    low = (html or "")[:3000].lower()
    return ("just a moment" in low and "cloudflare" in low) or "cf_chl_" in low


# ------------------------------------------------------------------ HTTP 会话

class _Resp(object):
    __slots__ = ("status", "headers", "body", "url", "cookies")

    def __init__(self):
        self.status = 0
        self.headers = {}
        self.body = b""
        self.url = ""
        self.cookies = []

    def text(self, encoding="utf-8"):
        try:
            return self.body.decode(encoding, "ignore")
        except Exception:
            return ""

    def json(self):
        return json.loads(self.text())


def _ssl_ctx():
    import ssl
    try:
        ctx = ssl.create_default_context()
        ctx.check_hostname = False
        ctx.verify_mode = ssl.CERT_NONE
        return ctx
    except Exception:
        return None


_SSL = _ssl_ctx()


class _Session(object):
    """带 Cookie 罐的会话（剧果的 CloudFront 签名需要 Cookie）。"""

    def __init__(self):
        self.cookies = {}
        self._lock = threading.Lock()

    def cookie_header(self):
        with self._lock:
            return "; ".join("%s=%s" % (k, v) for k, v in self.cookies.items())

    def set_cookies(self, pairs):
        with self._lock:
            for k, v in pairs:
                if k:
                    self.cookies[k] = v

    def fetch(self, url, method="GET", headers=None, data=None,
              timeout=20, max_body=16 << 20):
        headers = dict(headers or {})
        low = {k.lower() for k in headers}
        if "cookie" not in low:
            ck = self.cookie_header()
            if ck:
                headers["Cookie"] = ck
        if "user-agent" not in low:
            headers["User-Agent"] = PC_UA
        if "accept-encoding" not in low:
            headers["Accept-Encoding"] = "gzip"
        if isinstance(data, str):
            data = data.encode("utf-8")

        resp = _Resp()
        resp.url = url
        req = urllib.request.Request(url, data=data, headers=headers,
                                     method=method.upper())
        try:
            r = urllib.request.urlopen(req, timeout=timeout, context=_SSL)
            resp.status = getattr(r, "status", 200)
            resp.body = r.read(max_body)
            for k, v in (r.headers.items() if r.headers else []):
                resp.headers.setdefault(k.lower(), []).append(v)
            try:
                resp.url = r.geturl()
            except Exception:
                pass
        except urllib.error.HTTPError as e:
            resp.status = e.code
            try:
                resp.body = e.read()
            except Exception:
                resp.body = b""
            for k, v in (e.headers.items() if e.headers else []):
                resp.headers.setdefault(k.lower(), []).append(v)
        # Set-Cookie 进罐
        for line in resp.headers.get("set-cookie", []):
            head = line.split(";", 1)[0].strip()
            if "=" in head:
                k, v = head.split("=", 1)
                self.set_cookies([(k.strip(), v.strip())])
        # 中央解压
        enc = " ".join(resp.headers.get("content-encoding", [])).lower()
        body = resp.body
        try:
            if body[:2] == b"\x1f\x8b" or "gzip" in enc:
                resp.body = gzip.decompress(body)
            elif body[:2] == b"\x78\x9c" or "deflate" in enc:
                import zlib
                resp.body = zlib.decompress(body)
        except Exception:
            pass
        return resp

    def get_text(self, url, headers=None, timeout=20):
        return self.fetch(url, headers=headers, timeout=timeout).text()

    def get_json(self, url, headers=None, timeout=20):
        return self.fetch(url, headers=headers, timeout=timeout).json()

    def post_json(self, url, obj, headers=None, timeout=20):
        h = dict(headers or {})
        h["Content-Type"] = "application/json; charset=utf-8"
        return self.fetch(url, "POST", h,
                          json.dumps(obj, ensure_ascii=False).encode("utf-8"),
                          timeout=timeout).json()


# ------------------------------------------------------------------ 站源框架

class _SrcErr(Exception):
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


def _vod_item(src, sid, title, pic="", remark="", content=""):
    return {
        "vod_id": _did(src, sid),
        "vod_name": _s(title),
        "vod_pic": _s(pic),
        "vod_remarks": _s(remark),
        "vod_content": _s(content),
    }


def _vod_detail(src, sid, title, pic="", remark="", content="",
                year="", area="", actor="", chapters=()):
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
    if isinstance(e, urllib.error.HTTPError):
        code = int(getattr(e, "code", 0) or 0)
        if code in (401, 403, 412, 429):
            return "站点拒绝访问（HTTP %d），换网络或稍后再试" % code
        return "站点返回 HTTP %d" % code
    if isinstance(e, urllib.error.URLError):
        return "网络连不上：%s" % (getattr(e, "reason", "") or "超时")
    if isinstance(e, _SrcErr):
        return str(e)
    return "%s: %s" % (type(e).__name__, str(e)[:90])


class _Src(object):
    id = ""
    name = ""
    cats = [("", "推荐")]

    def __init__(self):
        self.sess = _Session()
        self.last_err = ""

    def categories(self):
        return self.cats

    def home(self, pg):
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


# ================================================================== 红果
# hongguoduanju.com 网页版（Next/Modern SSR）
#   分类  /category/<route>?page=N   loaderData["category_$"].recommendList
#   详情  /detail?series_id=<sid>    loaderData.detail_page.seriesDetail
#   搜索  /api/search/result/?query= {"searchList":[{"video_data":{...}}]}
#   播放  /video/public/<vid>/360p.mp4 —— 只对前 accessible_episode_cnt 集公开

@_register
class _Hongguo(_Src):
    id = "hongguo"
    name = "红果"
    cats = [("real", "真人剧"), ("comic", "漫剧"), ("ai", "AI剧")]

    BASE = "https://hongguoduanju.com"
    ROUTES = {"real": "real-drama", "comic": "comic-drama", "ai": "ai-drama"}

    def _get(self, path):
        return self.sess.get_text(self.BASE + path, headers={
            "User-Agent": IPHONE_UA, "Referer": self.BASE + "/"}, timeout=25)

    def _row(self, row, tid):
        sid = _pick(row, "series_id")
        if not sid:
            return None
        eps = _pick_int(row, "episode_cnt")
        remark = _pick(row, "episode_right_text") or (("全%d集" % eps) if eps else "")
        return _vod_item(self.id, sid, _pick(row, "series_name"),
                         _pick(row, "series_cover"), remark,
                         _pick(row, "series_intro"))

    def cat(self, catid, pg):
        route = self.ROUTES.get(_s(catid) or "real", "real-drama")
        html = self._get("/category/%s?page=%d" % (route, pg))
        if _cf_blocked(html):
            raise _SrcErr("红果被 Cloudflare 拦截")
        node = _router_page(html, "category_$", "category_page", "category_")
        items = []
        for r in (node.get("recommendList") or []):
            v = self._row(r, catid)
            if v:
                items.append(v)
        pages = _pick_int(node.get("pagination") or {}, "totalPages")
        return items, (pg < pages) if pages else len(items) >= 20

    def search(self, key, pg):
        if pg > 1:
            return [], False
        url = "%s/api/search/result/?query=%s&offset=0&count=20" % (self.BASE, _q(key))
        try:
            j = self.sess.get_json(url, headers={
                "User-Agent": IPHONE_UA, "Referer": self.BASE + "/"}, timeout=25)
        except Exception:
            return [], False
        items = []
        for row in (j.get("searchList") or []):
            data = row.get("video_data") if isinstance(row.get("video_data"), dict) else row
            if not isinstance(data, dict):
                continue
            v = self._row({"series_id": _pick(data, "series_id", "series_id_str"),
                           "series_name": _pick(data, "series_title", "series_name") or _pick(row, "name"),
                           "series_cover": _pick(data, "series_cover"),
                           "series_intro": _pick(data, "series_intro"),
                           "episode_cnt": _pick_int(data, "episode_cnt"),
                           "episode_right_text": _pick(data, "episode_right_text"),
                           "accessible_episode_cnt": _pick_int(data, "accessible_episode_cnt")},
                          "")
            if v and v["vod_name"]:
                items.append(v)
        return items, False

    def _series(self, sid):
        html = self._get("/detail?series_id=" + _q(sid))
        node = _router_page(html, "detail_$", "detail_page", "detail_")
        d = node.get("seriesDetail") or {}
        if not d:
            raise _SrcErr("红果详情为空")
        return d

    def detail(self, sid):
        d = self._series(sid)
        vids = [_s(v) for v in (d.get("vid_list") or []) if _s(v)]
        if not vids:
            raise _SrcErr("红果该剧没有分集")
        access = _pick_int(d, "accessible_episode_cnt") or 3
        chapters = []
        for i, vid in enumerate(vids):
            name = "第%d集" % (i + 1)
            if i < access:
                chapters.append(("%s|%s" % (sid, vid), name))
            else:
                # 非公开集：没有直链，留空让播放器跳过
                chapters.append(("-|%s" % vid, name + "(未公开)"))
        eps = _pick_int(d, "episode_cnt") or len(vids)
        return _vod_detail(
            self, sid, _pick(d, "series_name") or sid,
            _pick(d, "series_cover"),
            "共%d集（公开%d集）" % (eps, min(access, len(vids))),
            _pick(d, "series_intro"), chapters=chapters)

    def play(self, sid, ep):
        parts = _s(ep).split("|", 1)
        if len(parts) != 2 or parts[0] == "-":
            raise _SrcErr("红果该集未公开，仅前几集可直接播放")
        vid = parts[1]
        return (self.BASE + "/video/public/" + _q(vid) + "/360p.mp4",
                {"Referer": self.BASE + "/", "User-Agent": IPHONE_UA})


# ================================================================== 禁果
# jgdj.app / jinguoduanju.app 官方 API
#   POST /api/v1/auth/device  -> token（免登录，任意 deviceId 即可）
#   GET  /api/v1/dramas?page=&pageSize=&sort=latest|heat&q=
#   GET  /api/v1/dramas/<id>  -> {"drama":{...},"episodes":[{id,number,title}]}
#   GET  /api/v1/episodes/<eid>/play -> {"videoUrl": "...m3u8"}   —— 全片可播

@_register
class _Jinguo(_Src):
    id = "jinguo"
    name = "禁果"
    cats = [("rec", "推荐"), ("heat", "热度")]

    BASES = ["https://jgdj.app/api/v1", "https://jinguoduanju.app/api/v1"]
    _st = {"token": "", "base": "", "lock": threading.Lock()}

    def _login(self):
        body = {"attributionToken": "", "channelCode": "",
                "deviceId": "h5:" + str(uuid.uuid4())}
        last = None
        for base in self.BASES:
            origin = base.split("/api")[0]
            for attempt in range(2):
                try:
                    j = self.sess.post_json(base + "/auth/device", body, headers={
                        "User-Agent": IPHONE_UA,
                        "Accept": "application/json, text/plain, */*",
                        "Referer": origin + "/", "Origin": origin}, timeout=25)
                    tok = _pick(j, "token") or _pick(j.get("data") or {}, "token")
                    if tok:
                        self._st["token"] = tok
                        self._st["base"] = base
                        return
                    last = _SrcErr("禁果未返回令牌")
                except Exception as e:
                    last = e
                    time.sleep(1.0)
        raise last or _SrcErr("禁果授权失败")

    def _api(self, path, query=None):
        with self._st["lock"]:
            if not self._st["token"]:
                self._login()
            base, tok = self._st["base"], self._st["token"]
        url = base + path + ("?" + urllib.parse.urlencode(query) if query else "")
        origin = base.split("/api")[0]
        hdrs = {"User-Agent": IPHONE_UA,
                "Accept": "application/json, text/plain, */*",
                "Referer": origin + "/", "Origin": origin,
                "Authorization": "Bearer " + tok}
        last = None
        for attempt in range(2):
            try:
                r = self.sess.fetch(url, headers=hdrs, timeout=30)
            except Exception as e:
                last = e
                time.sleep(0.8)
                continue
            if r.status in (401, 403):
                with self._st["lock"]:
                    self._st["token"] = ""
                return self._api(path, query)
            if r.status == 429:
                last = _SrcErr("禁果接口限流，稍后再试")
                time.sleep(1.5)
                continue
            if r.status != 200:
                raise _SrcErr("禁果接口 HTTP %d" % r.status)
            return r.json()
        raise last or _SrcErr("禁果接口请求失败")

    def _cover(self, value):
        v = _s(value)
        if v.startswith("/"):
            v = "https://jgdj.app" + v
        return v

    def _item(self, row):
        did = _pick(row, "id")
        if not did:
            return None
        eps = _pick_int(row, "episodeCount")
        return _vod_item(self.id, did, _pick(row, "title"),
                         self._cover(row.get("coverUrl")),
                         ("全%d集" % eps) if eps else "",
                         _pick(row, "description", "subtitle"))

    def _list(self, query):
        try:
            rows = self._api("/dramas", query)
        except Exception as e:
            raise _SrcErr(_err_text(e))
        if isinstance(rows, dict):
            rows = rows.get("items") or rows.get("list") or []
        items = []
        for r in (rows or []):
            if isinstance(r, dict):
                v = self._item(r)
                if v:
                    items.append(v)
        return items

    def cat(self, catid, pg):
        q = {"page": pg, "pageSize": 24,
             "sort": "heat" if _s(catid) == "heat" else "latest"}
        items = self._list(q)
        return items, bool(items)

    def search(self, key, pg):
        items = self._list({"page": pg, "pageSize": 24, "q": key, "sort": "latest"})
        return items, bool(items)

    def detail(self, sid):
        j = self._api("/dramas/" + _q(sid))
        drama = j.get("drama") or {}
        eps = j.get("episodes") or []
        chapters = []
        for i, e in enumerate(eps):
            if not isinstance(e, dict):
                continue
            eid = _pick(e, "id")
            if not eid:
                continue
            no = _pick_int(e, "number") or (i + 1)
            chapters.append((eid, _pick(e, "title") or ("第%d集" % no)))
        chapters.sort(key=lambda x: _ep_no(x[1], 0) or 0)
        if not chapters:
            raise _SrcErr("禁果该剧没有分集")
        return _vod_detail(
            self, sid, _pick(drama, "title") or sid,
            self._cover(drama.get("coverUrl")),
            "全%d集" % len(chapters),
            _pick(j, "description") or _pick(drama, "description"),
            year=_pick(drama, "year"), area=_pick(drama, "region"),
            chapters=chapters)

    def play(self, sid, ep):
        j = self._api("/episodes/%s/play" % _q(ep))
        url = _pick(j, "videoUrl") or _pick(j, "url")
        if not url:
            raise _SrcErr("禁果未返回播放地址")
        return url, {"Referer": "https://jgdj.app/", "User-Agent": IPHONE_UA}


# ================================================================== 剧果
# api.huangju.net 官方 API
#   POST /api/v1/auth/guest {deviceId} -> token
#   GET  /api/v1/dramas?page=&sort=hot|new&q=
#   GET  /api/v1/dramas/<slug-id>  -> {"episodes":[{id,epNo,playable}]}
#   GET  /api/v1/play/<epid> -> {"url":"...m3u8"} + Set-Cookie(CloudFront 三件套)
# CloudFront 签名放在 Cookie 里，播放器需要带 Cookie 才能取到 ts，所以
# play() 把 Cookie 塞进 header 返回。

@_register
class _Huangju(_Src):
    id = "huangju"
    name = "剧果"
    cats = [("hot", "热播"), ("new", "最新")]

    SITE = "https://huangju.net"
    API = "https://api.huangju.net"
    _st = {"token": "", "lock": threading.Lock()}

    def _login(self):
        j = self.sess.post_json(self.API + "/auth/guest",
                                {"deviceId": str(uuid.uuid4())},
                                headers=self._hdr(), timeout=25)
        tok = _pick(j, "token") or _pick(j.get("data") or {}, "token")
        if not tok:
            raise _SrcErr("剧果未返回访客令牌")
        self._st["token"] = tok

    def _hdr(self, token=""):
        h = {"User-Agent": MOB_UA,
             "Accept": "application/json, text/plain, */*",
             "Referer": self.SITE + "/", "Origin": self.SITE}
        if token:
            h["Authorization"] = "Bearer " + token
        return h

    def _api(self, path, query=None):
        with self._st["lock"]:
            if not self._st["token"]:
                self._login()
            tok = self._st["token"]
        url = self.API + path + ("?" + urllib.parse.urlencode(query) if query else "")
        r = self.sess.fetch(url, headers=self._hdr(tok), timeout=30)
        if r.status in (401, 403):
            with self._st["lock"]:
                self._st["token"] = ""
            return self._api(path, query)
        if r.status != 200:
            raise _SrcErr("剧果接口 HTTP %d" % r.status)
        return r

    def _item(self, row):
        did = _pick(row, "id")
        slug = _pick(row, "slug")
        if not did or not slug:
            return None
        eps = _pick_int(row, "totalEpisodes")
        return _vod_item(self.id, "%s-%s" % (slug, did), _pick(row, "title"),
                         _pick(row, "coverUrl"),
                         ("全%d集" % eps) if eps else "",
                         _pick(row, "description"))

    def _list(self, query):
        try:
            j = self._api("/dramas", query).json()
        except Exception as e:
            raise _SrcErr(_err_text(e))
        rows = j.get("items") if isinstance(j, dict) else None
        items = []
        for r in (rows or []):
            if isinstance(r, dict):
                v = self._item(r)
                if v:
                    items.append(v)
        return items

    def cat(self, catid, pg):
        q = {"page": pg, "sort": "new" if _s(catid) == "new" else "hot"}
        items = self._list(q)
        return items, bool(items)

    def search(self, key, pg):
        items = self._list({"page": pg, "q": key})
        return items, bool(items)

    def detail(self, sid):
        j = self._api("/dramas/" + _q(sid)).json()
        eps = j.get("episodes") or []
        chapters = []
        for i, e in enumerate(eps):
            if not isinstance(e, dict) or e.get("playable") is False:
                continue
            eid = _pick(e, "id")
            if not eid:
                continue
            no = _pick_int(e, "epNo") or (i + 1)
            chapters.append((eid, _pick(e, "title") or ("第%d集" % no)))
        if not chapters:
            raise _SrcErr("剧果该剧没有可播放分集")
        return _vod_detail(
            self, sid, _pick(j, "title") or sid, _pick(j, "coverUrl"),
            "全%d集" % len(chapters), _pick(j, "description"),
            year=_pick(j, "year"), area=_pick(j, "region"),
            chapters=chapters)

    def play(self, sid, ep):
        r = self._api("/play/" + _q(ep))
        j = r.json()
        url = _pick(j, "url")
        if not url:
            raise _SrcErr("剧果未返回播放地址")
        # CloudFront 签名 Cookie 必须带给 m3u8 和每个 ts
        ck = "; ".join(
            _s(x).split(";", 1)[0].strip()
            for x in r.headers.get("set-cookie", []) if "=" in _s(x))
        h = {"User-Agent": MOB_UA, "Referer": self.SITE + "/"}
        if ck:
            h["Cookie"] = ck
        return url, h


# ================================================================== 黑桃
# heitaodj.com —— MacCMS 站
#   搜索 /index.php/vod/search/wd/<kw>.html
#   详情 /index.php/vod/detail/id/<id>.html
#   播放 /index.php/vod/player/id/<id>/nid/<nid>/sid/<sid>.html 里 player_aaaa
# 注意：媒体服务器只认移动端 UA，不带会是 403。

@_register
class _Heitao(_Src):
    id = "heitao"
    name = "黑桃"
    cats = [("1", "现代都市"), ("2", "古装传奇"), ("3", "仙侠玄幻"),
            ("4", "科幻脑洞"), ("5", "灵异悬疑"), ("6", "其他短剧")]

    BASE = "https://heitaodj.com"
    COOKIE = "heitao_age_confirmed=1"

    def _get(self, path, referer=None):
        return self.sess.get_text(self.BASE + path, headers={
            "User-Agent": MOB_UA,
            "Referer": referer or (self.BASE + "/"),
            "Cookie": self.COOKIE}, timeout=25)

    _CARD = re.compile(
        r'<a\b[^>]*href="(/index\.php/vod/detail/id/(\d+)\.html)"[^>]*>([\s\S]{0,1200}?)</a>')

    def _cards(self, html, page_url):
        items, seen = [], set()
        for m in self._CARD.finditer(html):
            vid, block = m.group(2), m.group(3)
            if vid in seen:
                continue
            title = _strip_tags(block)
            title = re.sub(r"^\s*\d+集\s*", "", title).strip()
            if not title:
                tm = re.search(r'\btitle="([^"]+)"', m.group(0))
                title = _strip_tags(tm.group(1)) if tm else ""
            if not title:
                continue
            seen.add(vid)
            pic = ""
            pm = re.search(r'(?:data-original|data-src|src)="([^"]+)"', block)
            if not pm:
                pm = re.search(r'(?:data-original|data-src|src)="([^"]+)"', m.group(0))
            if pm:
                pic = _abs(page_url, pm.group(1))
            remark = ""
            rm = re.match(r"\s*(\d+)\s*集", _strip_tags(block))
            if rm:
                remark = "全%s集" % rm.group(1)
            items.append(_vod_item(self.id, vid, title, pic, remark))
        return items

    def cat(self, catid, pg):
        if pg <= 1:
            path = "/index.php/vod/type/id/%s.html" % (catid or "1")
        else:
            path = "/index.php/vod/type/id/%s/page/%d.html" % (catid or "1", pg)
        items = self._cards(self._get(path), self.BASE + path)
        return items, bool(items)

    def search(self, key, pg):
        if pg <= 1:
            path = "/index.php/vod/search/wd/%s.html" % _q(key)
        else:
            path = "/index.php/vod/search/page/%d/wd/%s.html" % (pg, _q(key))
        try:
            html = self._get(path)
        except Exception:
            return [], False
        items = self._cards(html, self.BASE + path)
        return items, bool(items)

    def detail(self, sid):
        url = self.BASE + "/index.php/vod/detail/id/%s.html" % _q(sid)
        html = self._get("/index.php/vod/detail/id/%s.html" % _q(sid))
        title = ""
        m = re.search(r"<h1[^>]*>([\s\S]*?)</h1>", html)
        if m:
            title = _strip_tags(m.group(1))
        if not title:
            m = re.search(r'<meta property="og:title" content="([^"]+)"', html)
            title = _strip_tags(m.group(1)) if m else sid
        pic = ""
        m = re.search(r'<meta property="og:image" content="([^"]+)"', html)
        if m:
            pic = _abs(url, m.group(1))
        intro = ""
        m = re.search(r'<meta name="description" content="([^"]+)"', html)
        if m:
            intro = _strip_tags(m.group(1))
        chapters, seen = [], set()
        pat = r'/index\.php/vod/play/id/%s/sid/(\d+)/nid/(\d+)\.html' % re.escape(_s(sid))
        for m in re.finditer(pat, html):
            sid_no, nid = m.group(1), m.group(2)
            key = "%s:%s" % (sid_no, nid)
            if key in seen:
                continue
            seen.add(key)
            chapters.append(("%s|%s|%s" % (sid_no, nid, sid),
                             "第%d集" % (len(chapters) + 1)))
        if not chapters:
            raise _SrcErr("黑桃该剧暂无可播放分集")
        return _vod_detail(self, sid, title, pic, "全%d集" % len(chapters),
                           intro, chapters=chapters)

    def play(self, sid, ep):
        parts = _s(ep).split("|")
        if len(parts) < 3:
            raise _SrcErr("黑桃分集参数无效")
        sid_no, nid, real_sid = parts[0], parts[1], parts[2]
        page = "/index.php/vod/player/id/%s/nid/%s/sid/%s.html" % (
            _q(real_sid), _q(nid), _q(sid_no))
        html = self._get(page)
        idx = html.find("player_aaaa")
        if idx < 0:
            raise _SrcErr("黑桃播放器未返回配置")
        obj = _leading_json(html, html.find("{", idx))
        if not isinstance(obj, dict) or not _s(obj.get("url")):
            raise _SrcErr("黑桃该集暂无播放地址")
        raw = _s(obj.get("url"))
        mode = _pick_int(obj, "encrypt")
        if mode == 2:
            import base64
            try:
                raw = base64.b64decode(raw).decode("utf-8", "ignore")
            except Exception:
                pass
        if mode in (1, 2):
            raw = _uq(raw)
        raw = _abs(self.BASE + page, raw)
        # 媒体服务器只认移动端 UA，否则 403
        return raw, {"User-Agent": MOB_UA, "Referer": self.BASE + "/"}


# ================================================================== Spider

_MAIN_SPIDER = None


class Spider(BaseSpider):

    def getName(self):
        return "果源·红果/禁果/剧果/黑桃"

    def init(self, extend=""):
        global _MAIN_SPIDER
        self.extend = _s(extend)
        _MAIN_SPIDER = self
        return {}

    def destroy(self):
        return {}

    def isVideoFormat(self, url):
        u = _s(url).lower()
        return any(x in u for x in (".m3u8", ".mp4", ".flv", ".ts", ".mkv"))

    def manualVideoCheck(self):
        return False

    # ---------- 首页 ----------
    def _cats_of(self, src):
        try:
            cats = src.categories()
            if cats:
                return cats[:24]
        except Exception:
            pass
        return src.cats or [("", "推荐")]

    def homeContent(self, filter=False):
        classes, filters = [], {}
        for src in _SOURCES:
            tid = _tid(src.id, "")
            classes.append({"type_id": tid, "type_name": src.name})
            try:
                subs = self._cats_of(src)
            except Exception:
                subs = src.cats or [("", "推荐")]
            opts, seen = [], set()
            for cid, cname in subs:
                if not cname or cname in seen:
                    continue
                seen.add(cname)
                opts.append({"n": cname, "v": cid})
            if opts:
                filters[tid] = [{"key": "cat", "name": "分类", "value": opts}]
        vods = []
        try:
            vods, _ = _SOURCES[0].home(1)
            vods = vods[:20]
        except Exception:
            pass
        return {"class": classes, "list": vods, "filters": filters}

    def homeVideoContent(self):
        try:
            items, _ = _SOURCES[0].home(1)
            return {"list": items[:20]}
        except Exception:
            return {"list": []}

    # ---------- 分类 ----------
    def categoryContent(self, tid, pg="1", filter=False, extend=None):
        src_id, _ = _split_tid(tid)
        src = _find_src(src_id)
        if not src:
            return {"list": [], "page": 1, "pagecount": 1, "limit": 20, "total": 0}
        try:
            pg = max(1, int(pg))
        except Exception:
            pg = 1
        ext = extend
        if isinstance(ext, str) and ext:
            try:
                ext = json.loads(ext)
            except Exception:
                ext = {}
        cat = _s(ext.get("cat", "")) if isinstance(ext, dict) else ""
        if cat:
            try:
                cats = self._cats_of(src)
                if cat not in set(c[0] for c in cats):
                    cat = dict((c[1], c[0]) for c in cats).get(cat, "")
            except Exception:
                pass
        if not cat:
            try:
                cats = self._cats_of(src)
                cat = cats[0][0] if cats else ""
            except Exception:
                cat = ""
        try:
            items, more = src.cat(cat, pg)
            if items:
                src.last_err = ""
        except Exception as e:
            src.last_err = _err_text(e)
            items, more = [], False
        if not items and not more:
            items = [_vod_item(src.id, "@@err@@",
                               "⚠ %s：%s" % (src.name, src.last_err or "该分类暂无数据"))]
        return {"list": items, "page": pg,
                "pagecount": 9999 if more else pg,
                "limit": 20, "total": 999999 if more else len(items)}

    # ---------- 详情 ----------
    def detailContent(self, ids):
        did = ids[0] if ids else ""
        src_id, sid = _split_did(did)
        src = _find_src(src_id)
        if not src:
            return {"list": []}
        if sid == "@@err@@":
            vod = _vod_detail(src, sid, "%s 暂时不可用" % src.name, "", "",
                              src.last_err or "该源当前没有返回数据")
            vod["vod_id"] = did
            return {"list": [vod]}
        try:
            vod = src.detail(sid)
        except Exception as e:
            vod = _vod_detail(src, sid, "加载失败", "", "",
                              "原因：%s" % _err_text(e))
            vod["vod_id"] = did
        return {"list": [vod]}

    # ---------- 搜索 ----------
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
            if int(pg) > 1:
                return {"list": []}
        except Exception:
            pass
        out = []
        try:
            from concurrent.futures import ThreadPoolExecutor
            with ThreadPoolExecutor(max_workers=4) as ex:
                futs = {ex.submit(self._search_one, src, key): src for src in _SOURCES}
                for fut in futs:
                    src = futs[fut]
                    try:
                        items = fut.result(timeout=30)
                    except Exception:
                        continue
                    for v in items[:12]:
                        if not v["vod_name"].startswith("[%s]" % src.name):
                            v["vod_name"] = "[%s] %s" % (src.name, v["vod_name"])
                        out.append(v)
        except Exception:
            for src in _SOURCES:
                for v in self._search_one(src, key)[:12]:
                    v["vod_name"] = "[%s] %s" % (src.name, v["vod_name"])
                    out.append(v)
        return {"list": out}

    # ---------- 播放 ----------
    def playerContent(self, flag, id, vipFlags=None):
        src_id, sid, ep = _split_pid(id)
        src = _find_src(src_id)
        if not src:
            return {"parse": 0, "playUrl": "", "url": "", "header": {}}
        try:
            url, header = src.play(sid, ep)
        except Exception:
            return {"parse": 0, "playUrl": "", "url": "", "header": {}}
        return {"parse": 0, "playUrl": "", "url": _s(url),
                "header": dict(header or {})}
