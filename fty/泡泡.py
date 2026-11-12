# -*- coding: utf-8 -*-
# 泡泡影院
import html
import json
import re
import sys
from urllib.parse import quote, urlencode

sys.path.append('..')
from base.spider import Spider


class Spider(Spider):

    CATEGORIES = (
        ('电影', '1'),
        ('电视剧', '2'),
        ('综艺', '3'),
        ('动漫', '4'),
        ('短剧', '36'),
    )

    TYPE_OPTIONS = {
        '1': (
            '喜剧', '爱情', '恐怖', '动作', '科幻', '剧情', '战争',
            '警匪', '犯罪', '动画', '奇幻', '武侠', '冒险', '枪战',
            '悬疑', '惊悚', '经典', '青春', '文艺', '微电影', '古装',
            '历史', '运动', '农村', '儿童', '网络电影',
        ),
        '2': (
            '古装', '战争', '青春偶像', '喜剧', '家庭', '犯罪', '动作',
            '奇幻', '剧情', '历史', '经典', '乡村', '情景', '商战',
            '网剧', '其他',
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
        '36': (
            '古装', '战争', '青春偶像', '喜剧', '家庭', '犯罪', '动作',
            '奇幻', '剧情', '历史', '经典', '乡村', '情景', '商战',
            '网剧', '其他',
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
        '3': (
            '内地', '韩国', '香港', '台湾', '日本', '美国', '泰国',
            '英国', '新加坡', '其他',
        ),
        '4': (
            '内地', '韩国', '香港', '台湾', '日本', '美国', '泰国',
            '英国', '新加坡', '其他',
        ),
        '36': (
            '内地', '韩国', '香港', '台湾', '日本', '美国', '泰国',
            '英国', '新加坡', '其他',
        ),
    }

    LANGUAGE_OPTIONS = ('国语', '英语', '粤语', '闽南语', '韩语', '日语', '法语', '德语', '其它')

    YEAR_OPTIONS = tuple(str(year) for year in range(2026, 1999, -1))

    SORT_OPTIONS = (
        ('时间', 'time'),
        ('人气', 'hits'),
        ('评分', 'score'),
    )

    def init(self, extend=""):
        self.host = 'https://alliancebrh.com'
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
        return '泡泡影院'

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
            'limit': 36,
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

            area = quote(str(extend.get('area') or ''), safe='')
            order = str(extend.get('order') or 'time')
            if order not in ('time', 'hits', 'score'):
                order = 'time'
            plot = quote(str(extend.get('class') or ''), safe='')
            language = quote(str(extend.get('lang') or ''), safe='')
            year = quote(str(extend.get('year') or ''), safe='')
            page_value = '' if page == 1 else str(page)

            url = (
                f'{self.host}/vodshow/{tid}-{area}-{order}-{plot}-{language}'
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
            'limit': 20,
            'total': 0,
        }
        try:
            params = {'wd': key}
            if page > 1:
                params['page'] = str(page)
            url = f'{self.host}/vodsearch/-------------.html?' + urlencode(params)
            html_text = self.fetch(url, headers=self.headers).text
            result['list'] = self.get_search_list(html_text)
            if not result['list']:
                result['list'] = self.get_vod_list(html_text)
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
            detail_url = self.normalize_url(ids[0])
            html_text = self.fetch(detail_url, headers=self.headers).text
            vod_id_match = re.search(r'/voddetail/(\d+)\.html', detail_url)
            vod_id = vod_id_match.group(1) if vod_id_match else detail_url

            title = self.get_first(
                html_text,
                r'<h1[^>]*class="[^"]*detail-info-title[^"]*"[^>]*>(.*?)</h1>',
                re.DOTALL
            )
            if not title:
                title = self.get_first(html_text, r'<title>(.*?)</title>', re.DOTALL)
                title = re.split(r'[-_|]', title, 1)[0].strip()

            poster = self.get_first(
                html_text,
                r'<div[^>]*class="[^"]*block-fea[^"]*"[^>]*data-original="([^"]+)"',
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
                r'<div[^>]*class="[^"]*show_text[^"]*"[^>]*>'
                r'.*?<div[^>]*class="[^"]*entry-content[^"]*"[^>]*>(.*?)</div>',
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
                'vod_actor': self.get_meta_value(html_text, '演员'),
                'vod_director': self.get_meta_value(html_text, '导演'),
                'type_name': self.get_meta_value(html_text, '类型'),
                'vod_remarks': self.get_meta_value(html_text, '状态'),
                'vod_area': self.get_meta_value(html_text, '地区'),
                'vod_year': self.get_meta_value(html_text, '年份'),
                'vod_lang': self.get_meta_value(html_text, '语言'),
                'vod_content': self.clean_text(content),
            }

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
            if self.isVideoFormat(play_page) and '/vodplay/' not in play_page:
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
                direct_url = direct_url.replace('\\/', '/')
                return {
                    'jx': 0,
                    'parse': 0,
                    'url': html.unescape(direct_url),
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

            plot_values = [{'n': '全部', 'v': ''}]
            plot_values.extend(
                {'n': value, 'v': value}
                for value in self.TYPE_OPTIONS.get(tid, ())
            )
            filters.append({
                'key': 'class',
                'name': '剧情',
                'value': plot_values,
            })

            area_values = [{'n': '全部', 'v': ''}]
            area_values.extend(
                {'n': value, 'v': value}
                for value in self.AREA_OPTIONS.get(tid, ())
            )
            filters.append({
                'key': 'area',
                'name': '地区',
                'value': area_values,
            })

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
                for value in self.YEAR_OPTIONS
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
        cards = re.finditer(
            r'<article\b[^>]*class="[^"]*\bpost-list\b[^"]*\bvideo-list\b[^"]*"'
            r'[^>]*>\s*<a\b([^>]*)>(.*?)</a>\s*</article>\s*'
            r'<p\b[^>]*class="[^"]*\bvideo-name\b[^"]*"[^>]*>\s*'
            r'<a\b([^>]*)>(.*?)</a>',
            html_text,
            re.DOTALL
        )
        for card in cards:
            first_attrs = card.group(1)
            body = card.group(2)
            title_attrs = card.group(3)
            title_text = card.group(4)
            href = self.get_attr(first_attrs, 'href')
            detail_match = re.search(r'/voddetail/(\d+)\.html', href)
            if not detail_match:
                continue

            vod_id = detail_match.group(1)
            if vod_id in seen:
                continue

            title = self.get_attr(title_attrs, 'title') or self.clean_text(title_text)
            title = self.clean_text(title)
            if not title:
                continue

            pic = (
                self.get_attr(first_attrs, 'data-original')
                or self.get_attr(first_attrs, 'data-src')
                or self.get_attr(first_attrs, 'src')
            )
            remark = self.get_first(
                body,
                r'<span[^>]*class="[^"]*\bvideo-title\b[^"]*"[^>]*>(.*?)</span>',
                re.DOTALL
            )
            category = self.get_first(
                body,
                r'<em[^>]*class="[^"]*\bvoddate\b[^"]*"[^>]*>(.*?)</em>',
                re.DOTALL
            )
            seen.add(vod_id)
            videos.append({
                'vod_id': self.host + href,
                'vod_name': title,
                'vod_pic': self.normalize_url(pic),
                'vod_remarks': self.clean_text(remark or category),
            })
        return videos

    def get_search_list(self, html_text):
        videos = []
        seen = set()
        cards = re.finditer(
            r'<article\b[^>]*class="[^"]*\bpost-list\b[^"]*\bblockimg\b[^"]*"'
            r'[^>]*>(.*?)</article>',
            html_text,
            re.DOTALL
        )
        for card in cards:
            block = card.group(1)
            poster_attrs = self.get_first(
                block,
                r'<a\b([^>]*class="[^"]*\bblock-fea\b[^"]*"[^>]*)>',
                re.DOTALL
            )
            href = self.get_attr(poster_attrs, 'href')
            detail_match = re.search(r'/voddetail/(\d+)\.html', href)
            if not detail_match:
                continue

            vod_id = detail_match.group(1)
            if vod_id in seen:
                continue

            title_attrs = self.get_first(
                block,
                r'<span[^>]*class="[^"]*\bentry-title\b[^"]*"[^>]*>\s*<a\b([^>]*)>',
                re.DOTALL
            )
            title = self.get_attr(title_attrs, 'title')
            if not title:
                title = self.get_first(
                    block,
                    r'<span[^>]*class="[^"]*\bentry-title\b[^"]*"[^>]*>'
                    r'\s*<a\b[^>]*>(.*?)</a>',
                    re.DOTALL
                )
            title = self.clean_text(title)
            if not title:
                continue

            pic = (
                self.get_attr(poster_attrs, 'data-original')
                or self.get_attr(poster_attrs, 'data-src')
                or self.get_attr(poster_attrs, 'src')
            )
            category = self.get_first(
                block,
                r'<div[^>]*class="[^"]*\bentry-meta\b[^"]*"[^>]*>'
                r'\s*<a\b[^>]*>(.*?)</a>',
                re.DOTALL
            )
            seen.add(vod_id)
            videos.append({
                'vod_id': self.host + href,
                'vod_name': title,
                'vod_pic': self.normalize_url(pic),
                'vod_remarks': self.clean_text(category),
            })
        return videos

    def parse_playlist(self, html_text, vod_id):
        source_names = {}
        for source_id, name in re.findall(
            r'data-target="#ewave-playlist-(\d+)"[^>]*>\s*'
            r'<a\b[^>]*>(.*?)</a>',
            html_text,
            re.DOTALL
        ):
            source_names[source_id] = self.clean_text(name)

        result = []
        lists = re.findall(
            r'<ul\b[^>]*id="ewave-playlist-(\d+)"[^>]*>(.*?)</ul>',
            html_text,
            re.DOTALL
        )
        for source_id, block in lists:
            episodes = []
            seen = set()
            for attrs, name in re.findall(
                r'<a\b([^>]*href="[^"]*/vodplay/[^"]+"[^>]*)>(.*?)</a>',
                block,
                re.DOTALL
            ):
                href = self.get_attr(attrs, 'href')
                match = re.search(
                    r'/vodplay/(\d+)-(\d+)-(\d+)\.html',
                    href
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
                    f'{episode_name}${self.host}{html.unescape(href)}'
                ))

            episodes.sort(key=lambda item: item[0])
            if episodes:
                result.append({
                    'name': source_names.get(source_id) or f'线路{source_id}',
                    'episodes': '#'.join(item[1] for item in episodes),
                })
        return result

    def get_meta_value(self, html_text, label):
        value = self.get_first(
            html_text,
            r'<span>\s*' + re.escape(label) + r'：?\s*</span>(.*?)</p>',
            re.DOTALL
        )
        return self.clean_text(value)

    def get_pagecount(self, html_text):
        current = self.get_first(
            html_text,
            r'<li[^>]*class="[^"]*\bcurrent\b[^"]*"[^>]*>(.*?)</li>',
            re.DOTALL
        )
        current_match = re.search(r'\d+\s*/\s*(\d+)', self.clean_text(current))
        if current_match:
            return max(1, int(current_match.group(1)))

        tail = self.get_first(
            html_text,
            r'<a\b[^>]*href="([^"]+)"[^>]*title="(?:最后一页|尾页)"',
            re.DOTALL
        )
        if not tail:
            tail = self.get_first(
                html_text,
                r'<a\b[^>]*title="(?:最后一页|尾页)"[^>]*href="([^"]+)"',
                re.DOTALL
            )
        page_match = re.search(r'-(\d+)---(?:\d{4})?\.html', tail or '')
        return max(1, int(page_match.group(1))) if page_match else 1

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
