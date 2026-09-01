/*
 * title: 厂长资源
 * author: Spider开发规范
 * host: https://czzy.app/
 * 说明: FongMi/TV · 影视仓 · TVBox JS Spider
 * ext 可选: { "host": "https://czzy.app", "timeout": 8000 }
 */

const MOBILE_UA = 'Mozilla/5.0 (Linux; Android 13; Mobile) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Mobile Safari/537.36';
const DefHeader = { 'User-Agent': MOBILE_UA };
const HOST_CANDIDATES = [
    'https://czzy.app',
    'https://www.cz01.org',
    'https://www.czzy89.com',
    'https://czzy.top',
];

var HOST;
var KParams = {
    headers: { 'User-Agent': MOBILE_UA },
    timeout: 8000,
};

async function init(cfg) {
    try {
        let preferred = '';
        if (typeof cfg === 'string' && cfg.trim()) {
            preferred = cfg.trim();
        } else if (cfg && cfg.ext) {
            if (typeof cfg.ext === 'string') preferred = cfg.ext.trim();
            else if (cfg.ext.host) preferred = String(cfg.ext.host).trim();
        }
        HOST = await pickHost(preferred);
        KParams.headers['Referer'] = HOST + '/';
        let timeout = 0;
        if (cfg && cfg.ext && typeof cfg.ext === 'object' && cfg.ext.timeout) {
            timeout = parseInt(cfg.ext.timeout, 10);
        }
        if (timeout > 0) KParams.timeout = timeout;
    } catch (e) {
        console.error('初始化失败：', e.message);
        HOST = 'https://czzy.app';
        KParams.headers['Referer'] = HOST + '/';
    }
}

async function pickHost(preferred) {
    let list = [];
    if (preferred) list.push(preferred.replace(/\/$/, ''));
    for (let h of HOST_CANDIDATES) {
        if (!list.includes(h)) list.push(h);
    }
    for (let h of list) {
        let html = await requestRaw(h + '/');
        if (isValidSiteHtml(html)) return h;
    }
    return (preferred || HOST_CANDIDATES[0]).replace(/\/$/, '');
}

function isValidSiteHtml(html) {
    if (!html || typeof html !== 'string') return false;
    if (/Access Forbidden|SafeLine|访问已被拦截|WAF/i.test(html)) return false;
    return /bt_img|movie_bt|mi_paly_box|paly_list_btn/i.test(html);
}

async function home(filter) {
    try {
        let kclassName = '全部$movie_bt&电影$movie_bt_series/dyy&剧集$movie_bt_series/dianshiju&动画$movie_bt_series/dohua';
        let classes = kclassName.split('&').map(it => {
            let [cName, cId] = it.split('$');
            return { type_name: cName, type_id: cId };
        });
        let filters = buildFilters(classes);
        return JSON.stringify({ class: classes, filters: filters });
    } catch (e) {
        console.error('获取分类失败：', e.message);
        return JSON.stringify({ class: [], filters: {} });
    }
}

function buildFilters(classes) {
    let filters = {};
    try {
        const nameObj = {
            cateId: 'cateId,分类',
            area: 'area,地区',
            year: 'year,年份',
            class: 'class,影片类型',
            series: 'series,子类',
        };
        const flValues = {
            cateId: {
                'movie_bt_series/dyy': '全部$movie_bt_series/dyy&豆瓣电影Top250$dbtop250&最新电影$zuixindianying&高分影视$gaofenyingshi&热映中$reyingzhong&会员专区$movie_bt_series/huiyuanzhuanqu&站长推荐$movie_bt_series/zhanchangtuijian&华语电影$movie_bt_series/huayudianying&欧美电影$movie_bt_series/meiguodianying&韩国电影$movie_bt_series/hanguodianying&日本电影$movie_bt_series/ribendianying&印度电影$movie_bt_series/yindudianying&俄罗斯电影$movie_bt_series/eluosidianying&加拿大电影$movie_bt_series/jianadadianying',
                'movie_bt_series/dianshiju': '全部$movie_bt_series/dianshiju&国产剧$gcj&美剧$meijutt&韩剧$hanjutv&日剧$movie_bt_series/rj&海外剧$movie_bt_series/hwj',
                'movie_bt_series/dohua': '全部$movie_bt_series/dohua&剧场版$dongmanjuchangban&番剧$fanju',
            },
            area: {
                movie_bt: '全部$&中国台湾$tw&中国大陆$zh&中国香港$hk&美国$meiguo&韩国$hggggg&日本$riben&英国$yinguo&法国$fg&德国$dg&泰国$taiguo&印度$yidu&其他$qt',
            },
            year: {
                movie_bt: '全部$&2026$2026&2025$2025&2024$2024&2023$2023&2022$2022&2021$2021&2020$2020&2019$2019&2018$2018&2017$2017&2016$2016&2015$2015',
            },
            class: {
                movie_bt: '全部$&剧情$juqing&动作$dozuo&喜剧$xiju&爱情$aiqing&科幻$kh&恐怖$kubu&悬疑$xuanyi&动画$dhh&纪录片$jlpp&战争$zhanzheng&犯罪$fanzui',
            },
            series: {
                movie_bt: '全部$&电影$dyy&电视剧$dianshiju&动画$dohua&华语电影$huayudianying&欧美电影$meiguodianying&韩国电影$hanguodianying&日本电影$ribendianying&国产剧$guochanju&美剧$mj&韩剧$hj&日剧$rj',
            },
        };
        for (let item of classes) {
            filters[item.type_id] = Object.entries(nameObj).map(([nObjk, nObjv]) => {
                let [kkey, kname] = nObjv.split(',');
                let fvalue = flValues[kkey]?.[item.type_id]?.split('&') || [];
                let kvalue = fvalue.map(it => {
                    let [n, v] = it.split('$');
                    return { n: n, v: v };
                });
                return { key: kkey, name: kname, value: kvalue };
            }).filter(flt => flt.key && flt.value.length);
        }
    } catch (e) {
        filters = {};
    }
    return filters;
}

async function homeVod() {
    try {
        let resHtml = await request(HOST + '/');
        return JSON.stringify({ list: getVodList(resHtml) });
    } catch (e) {
        console.error('推荐页获取失败：', e.message);
        return JSON.stringify({ list: [] });
    }
}

async function category(tid, pg, filter, extend) {
    try {
        pg = parseInt(pg, 10);
        pg = pg > 0 ? pg : 1;
        let fl = extend || {};
        let cateUrl = `${HOST}/${fl.cateId || tid}` +
            `${fl.area ? `/movie_bt_cat/${fl.area}` : ''}` +
            `${fl.year ? `/year/${fl.year}` : ''}` +
            `${fl.class ? `/movie_bt_tags/${fl.class}` : ''}` +
            `${fl.series ? `/movie_bt_series/${fl.series}` : ''}` +
            `/page/${pg}`;
        let resHtml = await request(cateUrl);
        let VODS = getVodList(resHtml);
        let hasMore = /pagenavi_txt">[^<]*>/.test(resHtml);
        return JSON.stringify({
            list: VODS,
            page: String(pg),
            pagecount: hasMore ? pg + 1 : pg,
            limit: VODS.length || 30,
            total: (VODS.length || 30) * (hasMore ? pg + 1 : pg),
        });
    } catch (e) {
        console.error('类别页获取失败：', e.message);
        return JSON.stringify({ list: [], page: '1', pagecount: 0, limit: 30, total: 0 });
    }
}

async function search(wd, quick, pg) {
    try {
        pg = parseInt(pg, 10);
        pg = pg > 0 ? pg : 1;
        // 站点搜索入口已改为 /nimasile?q=（旧 xsss1O1 / vodsearch 会 403）
        let enc = encodeURIComponent(wd);
        let urls = [
            `${HOST}/nimasile?q=${enc}` + (pg > 1 ? `&paged=${pg}` : ''),
            `${HOST}/xsss1O1?q=${enc}`,
            `${HOST}/?s=${enc}`,
            `${HOST}/vodsearch/${enc}/page/${pg}`,
        ];
        let VODS = [];
        for (let url of urls) {
            let resHtml = await request(url);
            VODS = getVodList(resHtml);
            // 仅在非官方搜索页时做标题过滤，避免首页误匹配
            if (/[?&]s=|vodsearch|xsss/i.test(url)) {
                VODS = VODS.filter(it => it.vod_name && it.vod_name.includes(wd));
            }
            if (VODS.length) break;
        }
        return JSON.stringify({
            list: VODS,
            page: String(pg),
            pagecount: VODS.length ? pg : pg,
            limit: VODS.length || 30,
            total: VODS.length,
        });
    } catch (e) {
        console.error('搜索页获取失败：', e.message);
        return JSON.stringify({ list: [], page: '1', pagecount: 0, limit: 30, total: 0 });
    }
}

function getVodList(khtml) {
    try {
        if (!khtml) throw new Error('源码为空');
        let kvods = [];
        let seen = new Set();
        let listArr = cutStr(khtml, 'bt_img', '</ul>', '', false, 0, true);
        if (!listArr.length || listArr[0] === 'cutErr') {
            listArr = [khtml];
        }
        for (let block of listArr) {
            let items = cutStr(block, '<li', '</li>', '', false, 0, true);
            for (let it of items) {
                if (!/\/movie\//.test(it)) continue;
                let kid = cutStr(it, 'href="', '"', '');
                if (!kid || seen.has(kid)) continue;
                let kname = cutStr(it, 'alt="', '"', '') || cutStr(it, '<h3', '</h3>', '').replace(/<[^>]+>/g, ' ').trim();
                let kpic = cutStr(it, 'data-original="', '"', '') || cutStr(it, 'data-src="', '"', '') || cutStr(it, 'src="', '"', '');
                let kremarks = cutStr(it, 'jidi">', '</') || cutStr(it, 'qb">', '</') || cutStr(it, 'furk">', '</') || cutStr(it, 'rating">', '</') || '';
                if (!kname) continue;
                seen.add(kid);
                kvods.push({
                    vod_name: kname,
                    vod_pic: absUrl(kpic),
                    vod_remarks: kremarks,
                    vod_id: `${kid}@${kname}@${absUrl(kpic)}@${kremarks}`,
                });
            }
        }
        return kvods;
    } catch (e) {
        console.error('生成视频列表失败：', e.message);
        return [];
    }
}

function cleanText(text) {
    if (!text) return '';
    return String(text)
        .replace(/<[^>]+>/g, ' ')
        .replace(/&nbsp;|&#160;/gi, ' ')
        .replace(/&amp;/g, '&')
        .replace(/&lt;/g, '<')
        .replace(/&gt;/g, '>')
        .replace(/&quot;/g, '"')
        .replace(/\s+/g, ' ')
        .trim();
}

function metaValue(html, label) {
    if (!html) return '';
    let block = html;
    let patterns = [
        new RegExp(label + '[：:]\\s*([^<\\n]+)', 'i'),
        new RegExp(label + '[：:][\\s\\S]*?<a[^>]*>([^<]+)</a>', 'i'),
        new RegExp(label + '[：:]([^&]+?)&nbsp;', 'i'),
    ];
    for (let p of patterns) {
        let m = block.match(p);
        if (m && m[1]) {
            let val = cleanText(m[1]);
            if (val && val !== '<a' && val !== 'false' && val !== 'cutErr') return val;
        }
    }
    return '';
}

function playIdFromHref(href) {
    if (!href) return '';
    href = href.trim();
    let m = href.match(/\/v_play\/([^/?#]+)\.html/i);
    if (m) return m[1];
    if (/^https?:\/\//i.test(href)) return href;
    return href.replace(/^\//, '');
}

function buildPlayPageUrl(playId) {
    if (!playId) return '';
    if (/^https?:\/\//i.test(playId)) return playId;
    if (playId.includes('/v_play/')) return absUrl(playId);
    return `${HOST}/v_play/${playId}.html`;
}

async function detail(ids) {
    try {
        let idStr = Array.isArray(ids) ? ids[0] : ids;
        let parts = String(idStr).split('@');
        let id = parts[0];
        let kname = parts[1] || '';
        let kpic = parts[2] || '';
        let kremarks = parts.slice(3).join('@') || '';
        let detailUrl = /^http/.test(id) ? id : `${HOST}${id.startsWith('/') ? id : '/' + id}`;
        let resHtml = await request(detailUrl);
        if (!resHtml) throw new Error('源码为空');

        let intros = cutStr(resHtml, '"dytext', 'mi_paly_box">', '', false);
        if (!intros || intros === 'cutErr') {
            intros = cutStr(resHtml, 'dytext', 'mi_paly_box">', '', false);
        }
        let ktabs = [];
        let kurls = [];

        let playBlocks = [];
        let btnMatch = resHtml.match(/paly_list_btn[\s\S]*?(?=dwonBT|footer|$)/gi) || [];
        playBlocks.push(...btnMatch);
        if (!playBlocks.length) {
            let boxMatch = resHtml.match(/mi_paly_box[\s\S]*?(?=dwonBT|footer|$)/gi) || [];
            playBlocks.push(...boxMatch);
        }
        playBlocks.forEach((item, idx) => {
            let episodes = [];
            let re = /<a[^>]+href="([^"]+)"[^>]*>([\s\S]*?)<\/a>/gi;
            let m;
            while ((m = re.exec(item)) !== null) {
                let href = m[1];
                if (!/\/v_play\//.test(href)) continue;
                let epName = cleanText(m[2]) || '正片';
                let playId = playIdFromHref(href);
                if (playId) episodes.push(`${epName}$${playId}`);
            }
            if (episodes.length) {
                ktabs.push(`厂长在线${idx + 1}`);
                kurls.push(episodes.join('#'));
            }
        });

        let twoCut = cutStr(resHtml, 'dwonBT">', 'footer', '', false);
        if (twoCut) {
            let magnet = [];
            let pan = [];
            let dlRe = /<a[^>]+href="([^"]+)"[^>]*(?:title="([^"]*)")?[^>]*>([\s\S]*?)<\/a>/gi;
            let dm;
            while ((dm = dlRe.exec(twoCut)) !== null) {
                let eUrl = dm[1];
                let eName = cleanText(dm[2] || dm[3]) || '下载';
                if (!eUrl) continue;
                if (/^magnet:/.test(eUrl)) magnet.push(`${eName}$${eUrl}`);
                else if (!/^javascript:/i.test(eUrl)) pan.push(`${eName}$${eUrl.replace(/#/g, '@')}`);
            }
            if (magnet.length) {
                ktabs.push('磁力资源');
                kurls.push(magnet.join('#'));
            }
            if (pan.length) {
                ktabs.push('网盘资源');
                kurls.push(pan.join('#'));
            }
        }

        let title = kname || cleanText((resHtml.match(/<h1[^>]*>([\s\S]*?)<\/h1>/i) || [])[1] || '');
        let pic = kpic || absUrl((resHtml.match(/class="dyimg"[\s\S]*?src="([^"]+)"/i) || [])[1] || '');
        let content = cleanText((resHtml.match(/class="yp_context"[^>]*>([\s\S]*?)<\/div>/i) || [])[1] || '');

        let VOD = {
            vod_id: detailUrl,
            vod_name: title,
            vod_pic: pic,
            vod_remarks: kremarks,
            type_name: metaValue(intros, '类型'),
            vod_year: metaValue(intros, '年份'),
            vod_area: metaValue(intros, '地区'),
            vod_lang: metaValue(intros, '语言'),
            vod_director: metaValue(intros, '导演'),
            vod_actor: metaValue(intros, '主演'),
            vod_content: content || title,
            vod_play_from: ktabs.join('$$$'),
            vod_play_url: kurls.join('$$$'),
        };
        return JSON.stringify({ list: [VOD] });
    } catch (e) {
        console.error('详情页获取失败：', e.message);
        return JSON.stringify({ list: [] });
    }
}

// 防盗链 CDN：带 Referer/Origin 会 403，播放时只留 UA
const NO_REFERER_RE = /py1080p\.com|icve\.com\.cn|xhscdn\.com|ctyunxs\.cn|fj7oss|aliyuncs\.com|qiniucdn|byteimg|129\.|\/hls[34]\//i;
// 可识别为最终媒体地址
const MEDIA_RE = /\.(m3u8|mp4|flv|mkv|ts)(\?|$)/i;

function normalizeMediaUrl(url) {
    if (!url) return '';
    url = String(url).replace(/&amp;/g, '&').replace(/\\\//g, '/').trim();
    // 签名 URL 里的空格多半是 + 被错误解码，还原
    if (/\?(?:.*&)?(?:Signature|AWSAccessKeyId|Expires)=/i.test(url)) {
        url = url.replace(/ /g, '+');
    }
    let m = url.match(/^(https?:\/\/[^/?#]+)([^?#]*)(\?[^#]*)?(#.*)?$/i);
    if (!m) return url;

    let path = m[2] || '';
    for (let i = 0; i < 3; i++) {
        try {
            if (!/%[0-9A-Fa-f]{2}/.test(path)) break;
            let next = decodeURIComponent(path);
            if (next === path) break;
            path = next;
        } catch (e) {
            break;
        }
    }

    let encodedPath = path.split('/').map(seg => {
        if (!seg) return seg;
        if (/^[A-Za-z0-9._~-]+$/.test(seg)) return seg;
        return encodeURIComponent(seg);
    }).join('/');

    // 查询串原样保留（避免破坏 OSS Signature 中的 +/=）
    return m[1] + encodedPath + (m[3] || '') + (m[4] || '');
}

function isPlayerWrapper(url) {
    return /py\.php|player\/py|\/player\?/i.test(url || '');
}

function isDirectMediaUrl(url) {
    if (!url || !/^https?:\/\//i.test(url)) return false;
    if (isPlayerWrapper(url)) return false;
    if (/blank\.gif|logo|thumb|favicon/i.test(url)) return false;
    // 只看路径部分，避免 py.php?url=...m3u8 被误判为直链
    let path = String(url).split(/[?#]/)[0];
    return MEDIA_RE.test(path);
}

function isMediaUrl(url) {
    return isDirectMediaUrl(url);
}

/** 从 py.php 等播放器包装地址里取出真实 m3u8/mp4 */
function unwrapPlayerUrl(url) {
    if (!url) return '';
    url = String(url).replace(/&amp;/g, '&').trim();
    for (let i = 0; i < 4; i++) {
        if (isDirectMediaUrl(url)) return normalizeMediaUrl(url);
        if (!/[?&]url=/i.test(url)) break;
        let m = url.match(/[?&]url=([^&]+)/i);
        if (!m) break;
        try {
            url = decodeURIComponent(m[1]);
        } catch (e) {
            url = m[1];
        }
    }
    return isDirectMediaUrl(url) ? normalizeMediaUrl(url) : '';
}

function finalizePlayUrl(url) {
    if (!url) return { url: '', parse: 1 };
    url = unwrapPlayerUrl(url) || String(url).replace(/&amp;/g, '&').trim();
    url = normalizeMediaUrl(url);
    let parse = isDirectMediaUrl(url) ? 0 : 1;
    return { url, parse };
}

function playHeaders(mediaUrl) {
    // 统一策略：媒体 CDN 一律不带 Referer/Origin，避免一个个域名适配
    return { 'User-Agent': MOBILE_UA };
}

async function proxy(params) {
    try {
        let url = normalizeMediaUrl(params.url || '');
        let headers = { 'User-Agent': MOBILE_UA };
        let opt = { headers, timeout: KParams.timeout, buffer: 2 };
        let res = await req(url, opt);
        if (/\.m3u8(\?|$)/i.test(url) && res?.content) {
            let body = String(res.content);
            let base = url.substring(0, url.lastIndexOf('/') + 1);
            body = body.replace(/^(?!#)([^\s#][^\r\n]*)/gm, line => {
                line = line.trim();
                if (!line || line.startsWith('#')) return line;
                if (/^https?:\/\//i.test(line)) return line;
                return absUrl(line, base);
            });
            return [200, 'application/vnd.apple.mpegurl', body];
        }
        return [res?.code || 200, res?.headers?.['content-type'] || 'application/octet-stream', res?.content || ''];
    } catch (e) {
        return [500, 'text/plain', 'proxy error'];
    }
}

async function play(flag, ids, flags) {
    try {
        let playId = ids;
        let kp = 0;
        let kurl = '';
        let pageUrl = buildPlayPageUrl(playId);

        if (/磁力/.test(flag)) {
            kurl = playId;
        } else if (/网盘/.test(flag)) {
            kurl = `push://${playId.replace(/@/g, '#')}`;
        } else {
            let resHtml = await request(pageUrl, {
                headers: {
                    ...KParams.headers,
                    Referer: pageUrl,
                    Accept: 'text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8',
                },
            });
            kurl = await resolvePlayUrlDeep(resHtml, pageUrl, 0);
            let fin = finalizePlayUrl(kurl);
            kurl = fin.url;
            kp = fin.parse;
            if (!kurl) {
                kp = 1;
                kurl = pageUrl;
            }
        }
        return JSON.stringify({
            jx: 0,
            parse: kp,
            url: kurl,
            header: playHeaders(kurl),
        });
    } catch (e) {
        console.error('播放失败：', e.message);
        return JSON.stringify({ jx: 0, parse: 1, url: buildPlayPageUrl(ids), header: playHeaders('') });
    }
}

/** 统一深挖：页面 → iframe/播放器 → 最终 m3u8/mp4，覆盖厂长全部线路 */
async function resolvePlayUrlDeep(html, pageUrl, depth) {
    if (!html || depth > 3) return '';

    let direct = extractPlayUrl(html, pageUrl);
    if (direct) return direct;

    let candidates = collectPlayerCandidates(html, pageUrl);
    for (let cand of candidates) {
        let quick = unwrapPlayerUrl(cand);
        if (quick) return quick;
        try {
            let ifrHtml = await request(cand, {
                headers: { ...KParams.headers, Referer: pageUrl },
            });
            let url = extractPlayUrl(ifrHtml, cand);
            if (url) return url;
            // 播放器页可能再嵌一层
            url = await resolvePlayUrlDeep(ifrHtml, cand, depth + 1);
            if (url) return url;
        } catch (e) {}
    }
    return '';
}

function collectPlayerCandidates(html, pageUrl) {
    let list = [];
    let push = u => {
        if (!u) return;
        u = absUrl(String(u).replace(/&amp;/g, '&').trim(), pageUrl);
        if (!/^https?:\/\//i.test(u)) return;
        if (list.includes(u)) return;
        list.push(u);
    };

    let iframeRe = /<iframe[^>]+src=["']([^"']+)["']/gi;
    let m;
    while ((m = iframeRe.exec(html)) !== null) push(m[1]);

    // py1080p / 通用播放器
    let playerRe = /https?:\/\/[^"'\\\s]*py1080p\.com[^"'\\\s]*/gi;
    while ((m = playerRe.exec(html)) !== null) push(m[0]);

    let srcRe = /(?:src|url)\s*[:=]\s*["'](https?:[^"']*player[^"']*)["']/gi;
    while ((m = srcRe.exec(html)) !== null) push(m[1]);

    return list;
}

function extractPlayUrl(html, baseUrl) {
    if (!html) return '';
    html = String(html).replace(/&amp;/g, '&');

    // 1. 优先从 py.php 包装参数里取内层媒体
    let wrapRe = /https?:\/\/[^"'\\\s]*py1080p\.com[^"'\\\s]*[?&]url=([^"'\\\s&]+)/gi;
    let wm;
    while ((wm = wrapRe.exec(html)) !== null) {
        let inner = unwrapPlayerUrl('http://x/?url=' + wm[1]) || unwrapPlayerUrl(wm[0]);
        if (inner) return inner;
    }

    let patterns = [
        /(?:const|var)\s+mysvg\s*=\s*['"]([^'"]+)['"]/i,
        /(?:const|var)\s+url\s*=\s*['"](https?:[^'"]+)['"]/i,
        /art\.url\s*=\s*['"]([^'"]+)['"]/i,
        /video\.src\s*=\s*['"]([^'"]+)['"]/i,
        /["']url["']\s*:\s*["'](https?:[^'"]+)["']/i,
        /url\s*[:=]\s*['"](https?:[^'"]+\.(?:m3u8|mp4|flv)[^'"]*)['"]/i,
        /<(?:source|video)[^>]+src=["'](https?:[^"']+)["']/i,
        /https?:\/\/[^"'\\\s]*ctyunxs\.cn[^"'\\\s]*/i,
        /https?:\/\/129[^"'\\\s]+\.(?:m3u8|mp4|flv)[^"'\\\s]*/i,
        /https?:\/\/[a-z0-9.-]+(?::\d+)?\/[^\s"'?#]*\.m3u8(?:\?[^\s"']*)?/i,
        /https?:\/\/[a-z0-9.-]+(?::\d+)?\/[^\s"'?#]*\.mp4(?:\?[^\s"']*)?/i,
    ];

    for (let p of patterns) {
        let m = html.match(p);
        if (!m) continue;
        let raw = m[1] || m[0];
        if (!raw) continue;
        let url = raw.replace(/\\\//g, '/').trim();
        if (isPlayerWrapper(url)) {
            url = unwrapPlayerUrl(url);
            if (url) return url;
            continue;
        }
        if (!/\?/.test(url) && /%/.test(url)) {
            try { url = decodeURIComponent(url); } catch (e) {}
        }
        if (url.startsWith('videos') && url.length > 50) {
            url = url.replace(/^videos/, 'https://129.211.209.237:9091/hls3/hls/');
        }
        if (!/^https?:\/\//i.test(url)) continue;
        if (!isDirectMediaUrl(url)) continue;
        return normalizeMediaUrl(url);
    }

    if (baseUrl) {
        let inner = unwrapPlayerUrl(baseUrl);
        if (inner) return inner;
    }
    return '';
}

function absUrl(url, base) {
    if (!url) return '';
    url = url.trim();
    if (url.startsWith('//')) return 'https:' + url;
    if (url.startsWith('http')) return url;
    if (url.startsWith('/')) return HOST + url;
    if (base && base.startsWith('http')) {
        let u = base.split('/');
        u.pop();
        return u.join('/') + '/' + url.replace(/^\.\//, '');
    }
    return HOST + '/' + url.replace(/^\.\//, '');
}

function cutStr(str, prefix = '', suffix = '', defVal = '', clean = true, i = 0, all = false) {
    try {
        if (typeof str !== 'string') throw new Error('被截取对象必须为字符串');
        const cleanStr = cs => String(cs).replace(/<[^>]*?>/g, ' ').replace(/(\u00a0|[\u0020\u3000\s])+/g, ' ').trim().replace(/\s+/g, ' ');
        const esc = s => String(s).replace(/[.*+?${}()|[\]\\/^]/g, '\\$&');
        let pre = esc(prefix).replace(/£/g, '[^]*?');
        let end = esc(suffix);
        const regex = new RegExp(`${pre || '^'}([^]*?)${end || '$'}`, 'g');
        const matchIter = str.matchAll(regex);
        if (all) {
            let matchArr = [...matchIter];
            if (!matchArr.length) return [defVal];
            return matchArr.map(ela => ela[1] !== undefined ? (clean ? cleanStr(ela[1]) : ela[1]) : defVal);
        }
        const idx = parseInt(i, 10);
        if (isNaN(idx)) throw new Error('序号必须为整数');
        let tgResult, matchIdx = 0;
        for (let elt of matchIter) {
            if (matchIdx++ === idx) {
                tgResult = elt[1];
                break;
            }
        }
        return tgResult !== undefined ? (clean ? (cleanStr(tgResult) || defVal) : tgResult) : defVal;
    } catch (e) {
        return all ? ['cutErr'] : 'cutErr';
    }
}

async function requestRaw(reqUrl, options = {}) {
    try {
        const optObj = {
            headers: { ...KParams.headers, ...(options.headers || {}) },
            timeout: options.timeout || KParams.timeout,
        };
        const res = await req(reqUrl, optObj);
        return res?.content ?? '';
    } catch (e) {
        return '';
    }
}

async function request(reqUrl, options = {}) {
    try {
        if (typeof reqUrl !== 'string' || !reqUrl.trim()) throw new Error('reqUrl无效');
        options.method = (options.method || 'GET').toUpperCase();
        if (['GET', 'HEAD'].includes(options.method)) {
            delete options.body;
            delete options.data;
            delete options.postType;
        }
        let { headers, timeout, ...restOpts } = options;
        const optObj = {
            headers: (headers && typeof headers === 'object') ? headers : KParams.headers,
            timeout: parseInt(timeout, 10) > 0 ? parseInt(timeout, 10) : KParams.timeout,
            ...restOpts,
        };
        const res = await req(reqUrl, optObj);
        if (options.withHeaders) {
            const resHeaders = (res.headers && typeof res.headers === 'object') ? res.headers : {};
            return JSON.stringify({ ...resHeaders, body: res?.content ?? '' });
        }
        return res?.content ?? '';
    } catch (e) {
        console.error(`${reqUrl} 请求失败：`, e.message);
        return options?.withHeaders ? JSON.stringify({ body: '' }) : '';
    }
}

export function __jsEvalReturn() {
    return {
        init,
        home,
        homeVod,
        category,
        search,
        detail,
        play,
        proxy,
    };
}
