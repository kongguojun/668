# -*- coding: utf-8 -*-
"""
TVB云播 (https://fjcgs.cc/) 采集脚本 - 类式T4版
适用: ok影视 / 安卓影视+ 等支持 T4 类式 Python 采集规范的影视壳子 App
写法参考: 瓜子-muunspgoedyn.py (from base.spider import Spider, class Spider(Spider))

接口约定 (T4 类式):
    getName()                                -> 源名称
    init(extend)                             -> 初始化
    homeContent(filter)                      -> {"class": [...], "filters": {...}}
    homeVideoContent()                       -> {"list": [...]}  首页推荐
    categoryContent(tid, pg, filter, extend) -> {"page":.., "pagecount":.., "limit":.., "total":.., "list":[...]}
    detailContent(ids)                       -> {"list": [...]}  ids为列表
    searchContent(key, quick, pg=1)          -> {"list": [...]}
    playerContent(flag, id, vipFlags)        -> {"parse":0, "playUrl":"", "url":"..."}
    isVideoFormat(url) / manualVideoCheck() / localProxy(params)

站点要点:
    1. 站点为苹果CMS定制版, 桌面UA会触发滑块WAF, 移动端UA/蜘蛛UA不受限,
       所有请求统一使用移动端 Chrome UA。
    2. 分类: 电影1 / 电视剧2 / 综艺3 / 动漫4 / 短视频9 / 即将上映51
       路由: /fjcgcctype/{tid}.html(第1页)  /fjcgcctype/{tid}-{pg}.html(第2页起)
    3. 详情: /fjcgcc/{id}.html  含线路名(name17)与集数(list-number1)
    4. 播放: /fjcgccplay/{id}-{sid}-{nid}.html  页面内 player_aaaa.url 即真实地址
    5. 搜索: /search/-------------.html?wd={kw}  分页 &page=N
"""
import re
import json
import time
import urllib.parse

# base.spider 由 ok影视/安卓影视+ 等壳子运行时提供; 本地调试时回退为桩基类
try:
    from base.spider import Spider
except Exception:
    class Spider(object):
        pass


class Spider(Spider):
    def __init__(self):
        self.name = "TVB云播"
        self.site = "https://fjcgs.cc"
        # 移动UA绕过站点滑块WAF
        self.ua = ("Mozilla/5.0 (Linux; Android 13; SM-G991B) AppleWebKit/537.36 "
                   "(KHTML, like Gecko) Chrome/120.0.0.0 Mobile Safari/537.36")
        self.ua_backup = ("Mozilla/5.0 (iPhone; CPU iPhone OS 17_0 like Mac OS X) "
                          "AppleWebKit/605.1.15 (KHTML, like Gecko) "
                          "Mobile/15E148 MicroMessenger/8.0.49")
        # 解析型播放源(from)才走解析网关, 其余视为直链
        self.parse_from = {"fjyg", "leduo", "qpdz", "qq", "dbyun",
                           "wolong", "ffm3u8", "dbm3u8", "mp4", "link"}
        self.parse_gate = "https://m3u8.nmghytd.com/index.php?url="
        self.media_ext = re.compile(r'\.(m3u8|mp4|flv|ts|m4s)(\?|#|$)', re.I)
        # 简单TTL缓存, 同一URL短时间重复请求直接命中
        self.cache = {}
        self.cache_timeout = 300
        self.cache_max = 400
        # HTTP 会话(连接复用)
        self._session = None
        self._has_requests = False
        self._opener = None
        try:
            import requests as _r
            self._session = _r.Session()
            self._has_requests = True
        except Exception:
            pass

    # ------------------------------------------------------------ 基础方法

    def getName(self):
        return self.name

    def init(self, extend=''):
        pass

    def _abs(self, u):
        if not u:
            return u
        if u.startswith("//"):
            return "https:" + u
        if u.startswith("/"):
            return self.site + u
        if u.startswith("http"):
            return u
        return self.site + "/" + u

    def _fetch(self, url, timeout=15):
        """带连接复用/缓存/UA兜底重试的GET, 失败返回空串"""
        now = time.time()
        hit = self.cache.get(url)
        if hit and now - hit[1] < self.cache_timeout:
            return hit[0]
        text = ""
        for ua in (self.ua, self.ua_backup):
            headers = {
                "User-Agent": ua,
                "Referer": self.site + "/",
                "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
                "Accept-Language": "zh-CN,zh;q=0.9",
            }
            try:
                if self._has_requests and self._session is not None:
                    resp = self._session.get(url, headers=headers,
                                             timeout=(5, timeout),
                                             allow_redirects=True, verify=False)
                    resp.encoding = resp.apparent_encoding or "utf-8"
                    if resp.status_code == 200:
                        text = resp.text
                else:
                    import ssl
                    import urllib.request
                    if self._opener is None:
                        ctx = ssl.create_default_context()
                        ctx.check_hostname = False
                        ctx.verify_mode = ssl.CERT_NONE
                        self._opener = urllib.request.build_opener(
                            urllib.request.HTTPSHandler(context=ctx))
                    req = urllib.request.Request(url, headers=headers)
                    with self._opener.open(req, timeout=timeout) as r:
                        data = r.read()
                        enc = r.headers.get_content_charset() or "utf-8"
                        text = data.decode(enc, errors="ignore")
            except Exception:
                text = ""
            # WAF拦截页特征: 短页面且含防护脚本标记 -> 视为被拦, 换UA重试
            if text and (len(text) < 200 or "_guard" in text or "easy_slider" in text):
                text = ""
            if text:
                break
        if text:
            if len(self.cache) >= self.cache_max:
                self.cache.clear()
            self.cache[url] = (text, now)
        return text

    # ------------------------------------------------------------ 首页

    def homeContent(self, filter):
        classes = [
            {"type_id": "1", "type_name": "电影"},
            {"type_id": "2", "type_name": "电视剧"},
            {"type_id": "3", "type_name": "综艺"},
            {"type_id": "4", "type_name": "动漫"},
            {"type_id": "9", "type_name": "短视频"},
            {"type_id": "51", "type_name": "即将上映"},
        ]
        return {"class": classes, "filters": {}}

    def homeVideoContent(self):
        # 取电影第1页作为首页推荐
        r = self.categoryContent("1", "1", False, {})
        return {"list": r.get("list", [])}

    # ------------------------------------------------------------ 列表解析

    def _parse_vod_list(self, html):
        items = []
        pat = re.compile(
            r'<a[^>]+href="(/fjcgcc/(\d+)\.html)"[^>]*>\s*'
            r'<img[^>]+(?:data-src|src)="([^"]*)"[^>]*alt="([^"]*)"[^>]*>.*?'
            r'<div class="ys-name6">(.*?)</div>',
            re.S,
        )
        for m in pat.finditer(html):
            href, vid, pic, alt, name = m.groups()
            name = (name or alt or "").strip()
            if not name:
                continue
            items.append({
                "vod_id": vid,
                "vod_name": name,
                "vod_pic": self._abs(pic),
                "vod_remarks": "",
            })
        seen, uniq = set(), []
        for it in items:
            if it["vod_id"] in seen:
                continue
            seen.add(it["vod_id"])
            uniq.append(it)
        return uniq

    def _fetch_pages(self, html, tid):
        nums = set()
        for m in re.finditer(r'/fjcgcctype/%s-(\d+)\.html' % re.escape(str(tid)), html):
            try:
                nums.add(int(m.group(1)))
            except Exception:
                pass
        return max(nums) if nums else 1

    def categoryContent(self, tid, pg, filter, extend):
        pg = int(pg) if str(pg).isdigit() else 1
        page = 1 if pg <= 1 else pg
        url = "%s/fjcgcctype/%s.html" % (self.site, tid) if page == 1 else \
            "%s/fjcgcctype/%s-%d.html" % (self.site, tid, page)
        html = self._fetch(url)
        if not html:
            return {"list": [], "page": page, "pagecount": 1,
                    "limit": 30, "total": 0}
        items = self._parse_vod_list(html)
        pagecount = self._fetch_pages(html, str(tid)) if items else 1
        return {
            "page": page,
            "pagecount": pagecount,
            "limit": len(items) or 30,
            "total": (pagecount or 1) * (len(items) or 30),
            "list": items,
        }

    # ------------------------------------------------------------ 搜索

    def searchContent(self, key, quick, pg=1):
        kw = urllib.parse.quote(str(key).strip())
        pg = int(pg) if str(pg).isdigit() and int(pg) > 1 else 1
        url = "%s/search/-------------.html?wd=%s" % (self.site, kw)
        if pg > 1:
            url += "&page=%d" % pg
        html = self._fetch(url)
        items = self._parse_vod_list(html) if html else []
        pagecount = 1
        if html:
            for m in re.finditer(r'/search/[-]+(\d+)\.html', html):
                try:
                    pagecount = max(pagecount, int(m.group(1)))
                except Exception:
                    pass
        return {"list": items, "page": pg, "pagecount": pagecount,
                "limit": len(items) or 20, "total": len(items) * pagecount}

    # ------------------------------------------------------------ 详情

    def _extract_lines(self, html):
        lines = []
        n17s = re.findall(r'<div class="name17">(.*?)</div>', html, re.S)
        lns = re.findall(
            r'<div class="list-number1">(.*?)(?=<div class="list-name23">|<!--|\Z)',
            html, re.S)
        line_names = [n.strip() for n in n17s if n.strip().startswith("线路")]
        for idx, seg in enumerate(lns):
            eps = re.findall(
                r'href="/fjcgccplay/(\d+)-(\d+)-(\d+)\.html"><div>(.*?)</div>',
                seg, re.S)
            if not eps:
                continue
            sid = eps[0][1]
            name = line_names[idx] if idx < len(line_names) else ("线路" + str(sid))
            urls = []
            for _, s, n, ename in eps:
                urls.append("%s$%s/fjcgccplay/%s-%s-%s.html" % (
                    ename.strip() or ("第%s集" % n), self.site, eps[0][0], s, n))
            lines.append((name, "#".join(urls)))
        return lines

    def detailContent(self, ids):
        # T4类式: ids 为列表/元组, 取首个
        if isinstance(ids, (list, tuple)):
            vid = str(ids[0]) if ids else ""
        else:
            vid = str(ids)
        vid = re.sub(r'-\d+$', '', vid.strip())
        if not vid:
            return {"list": []}
        html = self._fetch("%s/fjcgcc/%s.html" % (self.site, vid))
        if not html:
            return {"list": []}

        vod = {"vod_id": vid}

        m = re.search(r'<div class="ys-name18">(.*?)</div>', html, re.S)
        if not m:
            m = re.search(r'<title>(.*?)</title>', html, re.S)
            if m:
                t = m.group(1).strip()
                t = re.sub(r'^《|》.*$', '', t)
                vod["vod_name"] = t
            else:
                vod["vod_name"] = vid
        else:
            vod["vod_name"] = m.group(1).strip()

        m = re.search(r'<img[^>]+data-src="(https?://[^"]+)"', html, re.S)
        vod["vod_pic"] = self._abs(m.group(1)) if m else ""

        def _links(label):
            i = html.find(label)
            if i < 0:
                return ""
            seg = html[i:i + 800]
            names = re.findall(r'<a[^>]+>([^<]+)</a>', seg)
            out = []
            for n in names:
                n = n.strip().replace("\u00a0", "").replace("&nbsp;", "")
                if n:
                    out.append(n)
            return " ".join(out)

        vod["vod_director"] = _links("导演")
        vod["vod_actor"] = _links("主演")

        def _kv(label):
            i = html.find(label)
            if i < 0:
                return ""
            seg = html[i:i + 300]
            m = re.search(r'<a[^>]*>(.*?)</a>', seg, re.S)
            v = m.group(1) if m else ""
            return v.strip().replace("\u00a0", "").replace("&nbsp;", "")

        vod["type_name"] = _kv("类型")
        vod["vod_area"] = _kv("地区")
        vod["vod_year"] = ""
        vod["vod_remarks"] = ""

        m = re.search(r'<div class="vod-descri1"(.*?)>((?:(?!</div>).)*)</div>', html, re.S)
        if not m:
            m = re.search(r'<div class="Synopsis-word"[^>]*>(.*?)</div>', html, re.S)
        vod["vod_content"] = re.sub(r'<[^>]+>|&nbsp;|\u00a0|\s+', ' ',
                                     m.group(2 or 1)).strip() if m else ""

        lines = self._extract_lines(html)
        vod["vod_play_from"] = "$$$".join(nm for nm, _ in lines)
        vod["vod_play_url"] = "$$$".join(u for _, u in lines)

        return {"list": [vod]}

    # ------------------------------------------------------------ 播放

    def playerContent(self, flag, id, vipFlags):
        u = str(id).strip()
        if not u.startswith("http"):
            if u.startswith("/"):
                u = self.site + u
            else:
                parts = re.split(r'[-\/]', u)
                if len(parts) >= 3 and parts[-2].isdigit() and parts[-1].isdigit():
                    u = "%s/fjcgccplay/%s.html" % (self.site, u)
                else:
                    u = "%s/fjcgccplay/%s-1-1.html" % (self.site, u)
        html = self._fetch(u)
        if not html:
            return {"parse": 0, "playUrl": "", "url": ""}

        m = re.search(r'var player_aaaa=(\{.*?\});', html, re.S)
        url, src_from = "", ""
        if m:
            try:
                data = json.loads(m.group(1))
                url = data.get("url", "")
                src_from = data.get("from", "")
            except Exception:
                mm = re.search(r'"url"\s*:\s*"([^"]*)"', m.group(1))
                if mm:
                    url = mm.group(1)
        if not url:
            return {"parse": 0, "playUrl": "", "url": ""}

        url = url.replace("\\/", "/")
        # 直链识别优先: m3u8/mp4 等直接返回, 不套解析网关
        if self.media_ext.search(url):
            return {"parse": 0, "playUrl": "", "url": url,
                    "header": json.dumps({"User-Agent": self.ua,
                                          "Referer": self.site + "/"})}
        if src_from in self.parse_from and not url.startswith(self.parse_gate):
            url = self.parse_gate + urllib.parse.quote(url, safe="")
        return {"parse": 0, "playUrl": "", "url": url}

    # ------------------------------------------------------------ 其他

    def isVideoFormat(self, url):
        video_formats = ['.m3u8', '.mp4', '.avi', '.mkv', '.flv', '.ts']
        u = (url or "").lower().split('?')[0]
        return any(u.endswith(fmt) for fmt in video_formats)

    def manualVideoCheck(self):
        pass

    def localProxy(self, params):
        return None


if __name__ == "__main__":
    # 本地调试: 顶部 try/except 已自动回退桩基类, 此处直接实例化验证
    import sys
    s = Spider()
    arg = sys.argv[1] if len(sys.argv) > 1 else ""
    def p(obj):
        print(json.dumps(obj, ensure_ascii=False, indent=2)[:1200])
    if arg == "home":
        p(s.homeContent(False))
    elif arg == "homevideo":
        p(s.homeVideoContent())
    elif arg == "movie":
        p(s.categoryContent("1", "1", False, {}))
    elif arg.startswith("detail:"):
        p(s.detailContent([arg.split(":", 1)[1]]))
    elif arg.startswith("search:"):
        p(s.searchContent(arg.split(":", 1)[1], False, 1))
    elif arg.startswith("play:"):
        p(s.playerContent("", arg.split(":", 1)[1], []))
    else:
        print("usage: python fjcgs_tvb.py home|homevideo|movie|detail:id|search:key|play:url")