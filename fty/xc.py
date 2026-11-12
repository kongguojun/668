# -*- coding: utf-8 -*-
# 金牌影院（dezhixiaochi.com）
import html
import json
import re
import sys
from urllib.parse import quote

sys.path.append('..')
from base.spider import Spider


class Spider(Spider):

    CATEGORIES = (
        ('电影', '1'),
        ('电视剧', '2'),
        ('综艺', '3'),
        ('动漫', '4'),
        ('短剧', '5'),
    )

    TYPE_OPTIONS = {
        '1': (
            ('动作片', '6'), ('喜剧片', '7'), ('爱情片', '8'),
            ('科幻片', '9'), ('恐怖片', '10'), ('剧情片', '11'),
            ('战争片', '12'), ('纪录片', '13'), ('悬疑片', '14'),
            ('犯罪片', '15'), ('奇幻片', '16'), ('动画片', '31'),
        ),
        '2': (
            ('国产剧', '17'), ('港台剧', '18'), ('日韩剧', '20'),
            ('欧美剧', '21'), ('海外剧', '22'),
        ),
        '3': (
            ('大陆综艺', '23'), ('日韩综艺', '24'),
            ('欧美综艺', '25'), ('港台综艺', '26'),
        ),
        '4': (
            ('国产动漫', '27'), ('日韩动漫', '28'),
            ('欧美动漫', '29'), ('其他动漫', '30'),
        ),
        '5': (
            ('女频恋爱', '32'), ('反转爽剧', '33'),
            ('脑洞悬疑', '34'), ('年代穿越', '35'),
            ('古装仙侠', '36'), ('现代都市', '37'),
        ),
    }

    PLOT_OPTIONS = {
        '1': (
            '喜剧', '爱情', '恐怖', '动作', '科幻', '剧情', '战争',
            '警匪', '犯罪', '动画', '奇幻', '武侠', '冒险', '枪战',
            '悬疑', '惊悚', '经典', '青春', '文艺', '微电影', '古装',
            '历史', '运动', '农村', '儿童', '网络电影',
        ),
        '2': (
            '古装', '战争', '青春偶像', '喜剧', '家庭', '犯罪', '动作',
            '奇幻', '历史', '经典', '乡村', '情景', '商战', '网剧', '其他',
        ),
        '3': (
            '选秀', '情感', '访谈', '播报', '旅游', '音乐', '美食',
            '纪实', '曲艺', '生活', '游戏互动', '财经', '求职',
        ),
        '4': (
            '情感', '科幻', '热血', '推理', '搞笑', '冒险', '萝莉',
            '校园', '动作', '机战', '运动', '战争', '少年', '少女',
            '社会', '原创', '亲子', '益智', '励志', '其他',
        ),
    }

    AREA_OPTIONS = {
        '1': (
            '大陆', '香港', '台湾', '美国', '法国', '英国', '日本',
            '韩国', '德国', '泰国', '印度', '意大利', '西班牙',
            '加拿大', '其他',
        ),
        '2': (
            '内地', '韩国', '香港', '台湾', '日本', '美国', '泰国',
            '英国', '新加坡', '其他',
        ),
        '3': ('内地', '港台', '日韩', '欧美'),
        '4': ('国产', '日本', '欧美', '其他'),
    }

    LANGUAGE_OPTIONS = ('国语', '英语', '粤语', '闽南语', '韩语', '日语', '法语', '德语', '其它')

    YEAR_OPTIONS = {
        '1': tuple(str(year) for year in range(2026, 2009, -1)),
        '2': tuple(str(year) for year in range(2026, 2003, -1)),
        '3': tuple(str(year) for year in range(2026, 2003, -1)),
        '4': tuple(str(year) for year in range(2026, 2003, -1)),
        '5': tuple(str(year) for year in range(2026, 2021, -1)),
    }

    SORT_OPTIONS = (
        ('时间', 'time'),
        ('人气', 'hits'),
        ('评分', 'score'),
    )

    def init(self, extend=""):
        self.host = 'https://www.dezhixiaochi.com'
        self.headers = {
            'User-Agent': (
                'Mozilla/5.0 (Windows NT 10.0; Win64; x64) '
                'AppleWebKit/537.36 (KHTML, like Gecko) '
                'Chrome/131.0.0.0 Safari/537.36'
            ),
            'Accept': 'text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8',
            'Accept-Language': 'zh-CN,zh;q=0.9',
            'Referer': self.host + '/',
        }
        if isinstance(extend, str) and extend.strip():
            try:
                extend = json.loads(extend)
            except Exception:
                extend = {}
        if isinstance(extend, dict) and extend.get('host'):
            self.host = str(extend['host']).rstrip('/')
            self.headers['Referer'] = self.host + '/'

    def getName(self):
        return '金牌影院-德智'

    def isVideoFormat(self, url):
        url = (url or '').lower()
        return '.m3u8' in url or '.mp4' in url or '.flv' in url

    def manualVideoCheck(self):
        return False

    def destroy(self):
        pass

    def homeContent(self, filter):
        result = {
            'class': [
                {'type_name': name, 'type_id': tid}
                for name, tid in self.CATEGORIES
            ],
            'filters': self.get_filters(),
            'list': [],
        }
        try:
            html_text = self.fetch(self.host + '/', headers=self.headers).text
            result['list'] = self.get_vod_list(html_text)
        except Exception as e:
            print(f'homeContent 错误: {e}')
        return result

    def homeVideoContent(self):
        try:
            html_text = self.fetch(self.host + '/', headers=self.headers).text
            return self.get_vod_list(html_text)
        except Exception:
            return []

    def categoryContent(self, tid, pg, filter, extend):
        try:
            page = max(1, int(pg))
        except (TypeError, ValueError):
            page = 1

        result = {
            'list': [],
            'page': page,
            'pagecount': 1,
            'limit': 48,
            'total': 0,
        }
        try:
            tid = str(tid)
            extend = extend or {}
            if isinstance(extend, str):
                try:
                    extend = json.loads(extend)
                except Exception:
                    extend = {}

            category_id = str(extend.get('type') or tid)
            area = quote(str(extend.get('area') or ''), safe='')
            order = str(extend.get('order') or 'time')
            if order not in ('time', 'hits', 'score'):
                order = 'time'
            plot = quote(str(extend.get('class') or ''), safe='')
            language = quote(str(extend.get('lang') or ''), safe='')
            year = quote(str(extend.get('year') or ''), safe='')
            page_value = '' if page == 1 else str(page)

            url = (
                f'{self.host}/jpyisx/{category_id}-{area}-{order}-{plot}-{language}'
                f'----{page_value}---{year}.html'
            )
            html_text = self.fetch(url, headers=self.headers).text
            result['list'] = self.get_vod_list(html_text)
            result['pagecount'] = self.get_pagecount(html_text)
            result['limit'] = max(1, len(result['list']))
            result['total'] = max(
                len(result['list']),
                result['pagecount'] * result['limit']
            )
        except Exception as e:
            print(f'categoryContent 错误: {e}')
        return result

    def searchContent(self, key, quick, pg="1"):
        try:
            page = max(1, int(pg))
        except (TypeError, ValueError):
            page = 1

        result = {
            'list': [],
            'page': page,
            'pagecount': 1,
            'limit': 10,
            'total': 0,
        }
        try:
            encoded_key = quote(str(key), safe='')
            if page == 1:
                url = f'{self.host}/jpyiso/{encoded_key}-------------.html'
            else:
                url = f'{self.host}/jpyiso/{encoded_key}----------{page}---.html'

            html_text = self.fetch(url, headers=self.headers).text
            result['list'] = self.get_search_list(html_text)
            result['pagecount'] = self.get_pagecount(html_text)
            result['limit'] = max(1, len(result['list']))
            result['total'] = max(
                len(result['list']),
                result['pagecount'] * result['limit']
            )
        except Exception as e:
            print(f'searchContent 错误: {e}')
        return result

    def detailContent(self, ids):
        result = {'list': []}
        try:
            detail_url = self.get_detail_url(ids[0])
            html_text = self.fetch(detail_url, headers=self.headers).text
            vod_id_match = re.search(r'/jpyilb/(\d+)\.html', detail_url)
            vod_id = vod_id_match.group(1) if vod_id_match else detail_url

            title = self.get_first(
                html_text,
                r'<h1[^>]*class="[^"]*\btitle\b[^"]*"[^>]*>(.*?)</h1>',
                re.DOTALL
            )
            if not title:
                title = self.get_first(html_text, r'<title>(.*?)</title>', re.DOTALL)
                title = re.split(r'[《》_-]', title)[1] if '《' in title else title

            poster = self.get_first(
                html_text,
                r'<div[^>]*class="[^"]*\bmyui-content__thumb\b[^"]*"[^>]*>'
                r'.*?<img\b[^>]*data-original="([^"]+)"',
                re.DOTALL
            )
            if not poster:
                poster = self.get_first(
                    html_text,
                    r'<meta[^>]*property="og:image"[^>]*content="([^"]+)"',
                    re.DOTALL
                )

            content = self.get_first(
                html_text,
                r"MyTheme\.Layer\.Text\(\s*'剧情简介'\s*,\s*'(.*?)'\s*,"
                r"\s*'500'",
                re.DOTALL
            )
            if not content:
                content = self.get_first(
                    html_text,
                    r'<meta[^>]*name="description"[^>]*content="([^"]+)"',
                    re.DOTALL
                )

            vod = {
                'vod_id': detail_url,
                'vod_name': self.clean_text(title),
                'vod_pic': self.normalize_url(poster),
                'vod_actor': self.get_data_value(html_text, '主演'),
                'vod_director': self.get_data_value(html_text, '导演'),
                'type_name': self.get_link_value(html_text, '分类'),
                'vod_area': self.get_link_value(html_text, '地区'),
                'vod_year': self.get_link_value(html_text, '年份'),
                'vod_remarks': self.get_first(
                    html_text,
                    r'<div[^>]*class="[^"]*\bmyui-content__thumb\b[^"]*"[^>]*>'
                    r'.*?<span[^>]*class="[^"]*\bpic-text\b[^"]*"[^>]*>(.*?)</span>',
                    re.DOTALL
                ),
                'vod_content': self.clean_text(content),
            }
            vod['vod_remarks'] = self.clean_text(vod['vod_remarks'])

            playlist = self.parse_playlist(html_text, vod_id)
            vod['vod_play_from'] = '$$$'.join(item['name'] for item in playlist)
            vod['vod_play_url'] = '$$$'.join(item['episodes'] for item in playlist)
            result['list'].append(vod)
        except Exception as e:
            print(f'detailContent 错误: {e}')
        return result

    def playerContent(self, flag, id, vipFlags):
        play_page = ''
        try:
            play_page = self.normalize_url(id)
            if self.isVideoFormat(play_page) and '/jpyigk/' not in play_page:
                return {
                    'jx': 0,
                    'parse': 0,
                    'url': play_page,
                    'header': self.player_headers(play_page),
                }

            html_text = self.fetch(play_page, headers=self.headers).text
            match = re.search(
                r'var\s+player_aaaa\s*=\s*(\{.*?\})\s*</script>',
                html_text,
                re.DOTALL
            )
            if match:
                player = json.loads(match.group(1))
                play_url = player.get('url') or player.get('url_next') or ''
                if play_url:
                    play_url = html.unescape(play_url).replace('\\/', '/')
                    play_url = self.normalize_url(play_url)
                    if self.isVideoFormat(play_url):
                        return {
                            'jx': 0,
                            'parse': 0,
                            'url': play_url,
                            'header': self.player_headers(play_page),
                        }

            direct_url = self.get_first(
                html_text,
                r'(https?://[^"\'<>\s]+?\.(?:m3u8|mp4)(?:\?[^"\'<>\s]*)?)',
                re.IGNORECASE
            )
            if direct_url:
                direct_url = html.unescape(direct_url).replace('\\/', '/')
                return {
                    'jx': 0,
                    'parse': 0,
                    'url': direct_url,
                    'header': self.player_headers(play_page),
                }

            return {
                'jx': 1,
                'parse': 1,
                'url': play_page,
                'header': self.player_headers(play_page),
            }
        except Exception as e:
            print(f'playerContent 错误: {e}')
            fallback = play_page or self.normalize_url(id)
            return {
                'jx': 1,
                'parse': 1,
                'url': fallback,
                'header': self.player_headers(fallback),
            }

    def localProxy(self, param):
        pass

    def liveContent(self, url):
        pass

    def get_filters(self):
        result = {}
        for _, tid in self.CATEGORIES:
            filters = []

            type_values = [{'n': '全部', 'v': ''}]
            type_values.extend(
                {'n': name, 'v': value}
                for name, value in self.TYPE_OPTIONS.get(tid, ())
            )
            filters.append({
                'key': 'type',
                'name': '类型',
                'value': type_values,
            })

            if self.PLOT_OPTIONS.get(tid):
                plot_values = [{'n': '全部', 'v': ''}]
                plot_values.extend(
                    {'n': value, 'v': value}
                    for value in self.PLOT_OPTIONS[tid]
                )
                filters.append({
                    'key': 'class',
                    'name': '剧情',
                    'value': plot_values,
                })

            if self.AREA_OPTIONS.get(tid):
                area_values = [{'n': '全部', 'v': ''}]
                area_values.extend(
                    {'n': value, 'v': value}
                    for value in self.AREA_OPTIONS[tid]
                )
                filters.append({
                    'key': 'area',
                    'name': '地区',
                    'value': area_values,
                })

            if tid != '5':
                language_values = [{'n': '全部', 'v': ''}]
                language_values.extend(
                    {'n': value, 'v': value}
                    for value in self.LANGUAGE_OPTIONS
                )
                filters.append({
                    'key': 'lang',
                    'name': '语言',
                    'value': language_values,
                })

            year_values = [{'n': '全部', 'v': ''}]
            year_values.extend(
                {'n': value, 'v': value}
                for value in self.YEAR_OPTIONS.get(tid, ())
            )
            filters.append({
                'key': 'year',
                'name': '年份',
                'value': year_values,
            })

            filters.append({
                'key': 'order',
                'name': '排序',
                'value': [
                    {'n': name, 'v': value}
                    for name, value in self.SORT_OPTIONS
                ],
                'init': 'time',
            })
            result[tid] = filters
        return result

    def get_vod_list(self, html_text):
        videos = []
        seen = set()
        markers = list(re.finditer(
            r'<div[^>]*class="[^"]*\bmyui-vodlist__box\b[^"]*"[^>]*>',
            html_text,
            re.DOTALL
        ))
        for index, marker in enumerate(markers):
            end = markers[index + 1].start() if index + 1 < len(markers) else marker.end() + 5000
            block = html_text[marker.start():end]
            attrs = self.get_first(
                block,
                r'<a\b([^>]*class="[^"]*\bmyui-vodlist__thumb\b[^"]*"[^>]*)>',
                re.DOTALL
            )
            href = self.get_attr(attrs, 'href')
            detail_match = re.search(r'/(?:jpyilb|jpyigk)/(\d+)(?:-\d+-\d+)?\.html', href)
            if not detail_match:
                continue

            vod_id = detail_match.group(1)
            if vod_id in seen:
                continue

            title = self.get_attr(attrs, 'title')
            if not title:
                title = self.get_first(
                    block,
                    r'<h4[^>]*class="[^"]*\btitle\b[^"]*"[^>]*>\s*'
                    r'<a\b[^>]*>(.*?)</a>',
                    re.DOTALL
                )
            title = self.clean_text(title)
            if not title:
                continue

            pic = (
                self.get_attr(attrs, 'data-original')
                or self.get_attr(attrs, 'data-src')
                or self.get_attr(attrs, 'src')
            )
            if not pic:
                style = self.get_attr(attrs, 'style')
                style_match = re.search(r'url\(([^)]+)\)', style)
                if style_match:
                    pic = style_match.group(1).strip('"\' ')

            remark = self.get_first(
                block,
                r'<span[^>]*class="[^"]*\bpic-text\b[^"]*"[^>]*>(.*?)</span>',
                re.DOTALL
            )
            seen.add(vod_id)
            videos.append({
                'vod_id': f'{self.host}/jpyilb/{vod_id}.html',
                'vod_name': title,
                'vod_pic': self.normalize_url(pic),
                'vod_remarks': self.clean_text(remark),
            })
        return videos

    def get_search_list(self, html_text):
        videos = []
        seen = set()
        search_list = self.get_first(
            html_text,
            r'<ul\b[^>]*id="searchList"[^>]*>(.*?)</ul>',
            re.DOTALL
        )
        cards = re.finditer(
            r'<li\b[^>]*class="[^"]*\bclearfix\b[^"]*"[^>]*>(.*?)</li>',
            search_list,
            re.DOTALL
        )
        for card in cards:
            block = card.group(1)
            attrs = self.get_first(
                block,
                r'<a\b([^>]*class="[^"]*\bmyui-vodlist__thumb\b[^"]*"[^>]*)>',
                re.DOTALL
            )
            href = self.get_attr(attrs, 'href')
            detail_match = re.search(r'/jpyilb/(\d+)\.html', href)
            if not detail_match:
                continue

            vod_id = detail_match.group(1)
            if vod_id in seen:
                continue
            title = self.get_attr(attrs, 'title')
            if not title:
                title = self.get_first(
                    block,
                    r'<h4[^>]*class="[^"]*\btitle\b[^"]*"[^>]*>\s*'
                    r'<a\b[^>]*>(.*?)</a>',
                    re.DOTALL
                )
            title = self.clean_text(title)
            if not title:
                continue

            pic = (
                self.get_attr(attrs, 'data-original')
                or self.get_attr(attrs, 'data-src')
                or self.get_attr(attrs, 'src')
            )
            remark = self.get_first(
                block,
                r'<span[^>]*class="[^"]*\bpic-text\b[^"]*"[^>]*>(.*?)</span>',
                re.DOTALL
            )
            seen.add(vod_id)
            videos.append({
                'vod_id': self.host + href,
                'vod_name': title,
                'vod_pic': self.normalize_url(pic),
                'vod_remarks': self.clean_text(remark),
            })
        return videos

    def parse_playlist(self, html_text, vod_id):
        source_names = []
        tabs = self.get_first(
            html_text,
            r'<ul[^>]*class="[^"]*\bnav\b[^"]*\bnav-tabs\b[^"]*"[^>]*>(.*?)</ul>',
            re.DOTALL
        )
        for source_id, name in re.findall(
            r'<a\b[^>]*href="#playlist(\d+)"[^>]*>(.*?)</a>',
            tabs,
            re.DOTALL
        ):
            source_names.append((source_id, self.clean_text(name)))

        pane_map = {}
        for source_id, block in re.findall(
            r'<div\b[^>]*id="playlist(\d+)"[^>]*>(.*?)</div>',
            html_text,
            re.DOTALL
        ):
            episodes = []
            seen = set()
            for href, name in re.findall(
                r'<a\b([^>]*href="[^"]*/jpyigk/[^"]+"[^>]*)>(.*?)</a>',
                block,
                re.DOTALL
            ):
                play_href = self.get_attr(href, 'href')
                match = re.search(
                    r'/jpyigk/(\d+)-(\d+)-(\d+)\.html',
                    play_href
                )
                if not match or match.group(1) != str(vod_id):
                    continue
                nid = int(match.group(3))
                if nid in seen:
                    continue
                episode_name = self.clean_text(name)
                episode_name = (
                    episode_name
                    .replace('$', ' ')
                    .replace('#', ' ')
                    .strip()
                    or f'第{nid}集'
                )
                seen.add(nid)
                episodes.append((
                    nid,
                    f'{episode_name}${self.host}{html.unescape(play_href)}'
                ))
            episodes.sort(key=lambda item: item[0])
            if episodes:
                pane_map[source_id] = '#'.join(item[1] for item in episodes)

        result = []
        used = set()
        for source_id, name in source_names:
            if source_id in pane_map and source_id not in used:
                result.append({
                    'name': name or f'线路{source_id}',
                    'episodes': pane_map[source_id],
                })
                used.add(source_id)
        for source_id, episodes in pane_map.items():
            if source_id not in used:
                result.append({
                    'name': f'线路{source_id}',
                    'episodes': episodes,
                })
        return result

    def get_data_value(self, html_text, label):
        value = self.get_first(
            html_text,
            r'<span[^>]*class="[^"]*\btext-muted\b[^"]*"[^>]*>\s*'
            + re.escape(label) + r'：\s*</span>(.*?)</p>',
            re.DOTALL
        )
        return self.clean_text(value)

    def get_link_value(self, html_text, label):
        value = self.get_first(
            html_text,
            r'<span[^>]*class="[^"]*\btext-muted\b[^"]*"[^>]*>\s*'
            + re.escape(label) + r'：\s*</span>\s*<a\b[^>]*>(.*?)</a>',
            re.DOTALL
        )
        return self.clean_text(value)

    def get_pagecount(self, html_text):
        pager = self.get_first(
            html_text,
            r'<ul[^>]*class="[^"]*\bmyui-page\b[^"]*"[^>]*>(.*?)</ul>',
            re.DOTALL
        )
        current = re.search(r'\d+\s*/\s*(\d+)', self.clean_text(pager))
        if current:
            return max(1, int(current.group(1)))

        tail = self.get_first(
            pager,
            r'<a\b[^>]*href="([^"]+)"[^>]*>\s*尾页\s*</a>',
            re.DOTALL
        )
        page_match = re.search(r'-(\d+)---(?:\d{4})?\.html', tail)
        return max(1, int(page_match.group(1))) if page_match else 1

    def get_detail_url(self, value):
        url = self.normalize_url(value)
        play_match = re.search(r'/jpyigk/(\d+)(?:-\d+-\d+)?\.html', url)
        if play_match:
            return f'{self.host}/jpyilb/{play_match.group(1)}.html'
        return url

    def get_first(self, text, pattern, flags=0):
        match = re.search(pattern, text or '', flags)
        return match.group(1).strip() if match else ''

    def get_attr(self, attrs, name):
        match = re.search(
            r'\b' + re.escape(name) + r'\s*=\s*(["\'])(.*?)\1',
            attrs or '',
            re.DOTALL
        )
        return html.unescape(match.group(2)).strip() if match else ''

    def clean_text(self, text):
        text = re.sub(r'<script\b.*?</script>', '', text or '', flags=re.DOTALL | re.IGNORECASE)
        text = re.sub(r'<style\b.*?</style>', '', text, flags=re.DOTALL | re.IGNORECASE)
        text = re.sub(r'<[^>]+>', ' ', text)
        text = html.unescape(text).replace('\xa0', ' ')
        return re.sub(r'\s+', ' ', text).strip()

    def normalize_url(self, url):
        url = html.unescape(str(url or '')).strip().replace('\\/', '/')
        if not url:
            return ''
        if url.startswith('//'):
            return 'https:' + url
        if url.startswith('/'):
            return self.host + url
        return url

    def player_headers(self, referer):
        return {
            'User-Agent': self.headers['User-Agent'],
            'Referer': referer or (self.host + '/'),
        }
