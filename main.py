# -*- coding: utf-8 -*-
"""
API de notícias (snapshot horário) — só newspaper3k
- Atualiza a cada 1 hora
- Extrai conteúdo apenas com newspaper3k; se falhar, descarta o artigo
- CORS aberto (Access-Control-Allow-Origin: *)
- Rate limit + mitigação simples de DDoS
Executar: python apinoticias.py
Endpoints:
  - http://127.0.0.1:5000/api/v1/news
  - http://127.0.0.1:5000/api/v1/status
"""
from __future__ import annotations
from flask import Flask, request, jsonify, make_response, abort
import feedparser, re, html, calendar, hashlib, threading, time, os
from datetime import datetime, timedelta, timezone
from email.utils import parsedate_to_datetime, format_datetime
from zoneinfo import ZoneInfo
from urllib.parse import urlparse, urljoin
import requests
from bs4 import BeautifulSoup
from collections import Counter, OrderedDict

# --- extrator único (newspaper3k) ---
try:
    from newspaper import Article as _NPArticle
    _HAS_NEWSPAPER = True
except Exception:
    _HAS_NEWSPAPER = False

# --------------------------------- Config ---------------------------------
TZ = ZoneInfo("America/Fortaleza")

ALL_FEEDS = [
    "https://www.contabeis.com.br/rss/noticias/",
    "https://www.contabeis.com.br/rss/artigos/",
    "https://cfc.org.br/feed/",
    "https://www12.senado.leg.br/noticias/rss",
    "https://agenciabrasil.ebc.com.br/rss.xml",
    "https://www.camara.leg.br/noticias/feed/",
    "https://fdr.com.br/feed/",
    "https://www.jornalcontabil.com.br/feed/",
    "https://diariodocomercio.com.br/feed/",
    "https://mundorh.com.br/feed/",
    "https://fenacon.org.br/feed/",
    "https://www.fecomercio.com.br/feed/",
    "https://administradores.com.br/feed/",
    "https://www.convergenciadigital.com.br/feed/",
]

REFRESH_INTERVAL = timedelta(hours=1)      # <- 1h cravado

# Rate limit / mitigação
RATE_LIMIT_PER_MIN = 60
RATE_LIMIT_BURST = 120
BAN_THRESHOLD_1MIN = 400
BAN_TIME_SECONDS = 15 * 60

# Segurança básica
MAX_CONTENT_LENGTH = 32 * 1024
ALLOWED_METHODS = {"GET", "HEAD", "OPTIONS"}

# Conteúdo
CONTENT_TIMEOUT = 8           # timeout por artigo
CONTENT_MAX_CHARS = 8000      # máximo retornado
_UA_ARTICLE = "Mozilla/5.0 (ContentFetcher; +https://example.local)"

# --------------------------------- App ---------------------------------
app = Flask(__name__)
app.config["MAX_CONTENT_LENGTH"] = MAX_CONTENT_LENGTH

# ----------------------------- Rate limiting -----------------------------
_rate_state = {}  # ip -> {"tokens": float, "last": float, "banned_until": float, "count_1min": int, "window_started": float}
_rate_lock = threading.Lock()

def _now_ts() -> float:
    return time.time()

def _refill(tokens: float, last_ts: float, now_ts: float) -> float:
    elapsed = max(0.0, now_ts - last_ts)
    return min(RATE_LIMIT_BURST, tokens + (RATE_LIMIT_PER_MIN / 60.0) * elapsed)

@app.before_request
def _ddos_and_ratelimit_guard():
    if request.method not in ALLOWED_METHODS:
        abort(405)
    ip = request.headers.get("X-Forwarded-For", request.remote_addr) or "unknown"
    now = _now_ts()
    # log simples
    print(f"➡ {request.method} {request.path} from {ip} Origin={request.headers.get('Origin')!r}")
    with _rate_lock:
        st = _rate_state.get(ip)
        if not st:
            st = {"tokens": RATE_LIMIT_BURST, "last": now, "banned_until": 0.0,
                  "count_1min": 0, "window_started": now}
            _rate_state[ip] = st
        if now - st["window_started"] >= 60.0:
            st["count_1min"] = 0
            st["window_started"] = now
        st["count_1min"] += 1
        if st["count_1min"] > BAN_THRESHOLD_1MIN:
            st["banned_until"] = now + BAN_TIME_SECONDS
        if now < st["banned_until"]:
            abort(make_response(("Too Many Requests (temporary ban)", 429)))
        st["tokens"] = _refill(st["tokens"], st["last"], now)
        st["last"] = now
        if st["tokens"] < 1.0:
            abort(make_response(("Too Many Requests", 429)))
        st["tokens"] -= 1.0

# --------- CORS ABERTO PRA TUDO ---------
@app.after_request
def _add_cors_and_log(resp):
    # CORS liberado
    resp.headers["Access-Control-Allow-Origin"] = "*"
    resp.headers["Access-Control-Allow-Methods"] = "GET, HEAD, OPTIONS"
    resp.headers["Access-Control-Allow-Headers"] = "*"
    # log de saída
    try:
        clen = resp.calculate_content_length()
    except Exception:
        clen = -1
    print(f"⬅ {resp.status} {request.method} {request.path} len={clen} ETag={resp.headers.get('ETag')} Cache={resp.headers.get('Cache-Control')}")
    return resp

# ----------------------------- Helpers limpeza -----------------------------
_cdata_re = re.compile(r"<!\[CDATA\[|\]\]>?|\]\]", re.I)

def _strip_html(text: str) -> str:
    text = text or ""
    text = _cdata_re.sub("", text)
    text = re.sub(r"<[^>]+>", " ", text)
    text = html.unescape(text)
    return re.sub(r"\s+", " ", text).strip()

_defonte = re.compile(r"^Página:\s*Array\s*[–-]\s*", re.I)

def clean_source(src: str) -> str:
    src = _cdata_re.sub("", src or "")
    src = _defonte.sub("", src).strip()
    return src

_leia_mais_re = re.compile(r"(Leia\s+mais\s+em)\s+(https?://\S+)", re.I)
_duracao_fim = re.compile(r"\b\d{1,2}:\d{2}$")
_respostas_glued = re.compile(r"(\D)(\d{1,4})\s*Respostas", re.I)
_img_re = re.compile(r'<img[^>]+src=["\']([^"\']+)["\']', re.I)
_href_re = re.compile(r'<a[^>]+href=["\']([^"\']+)["\']', re.I)

def clean_summary(raw: str):
    raw = _cdata_re.sub("", raw or "")
    txt = _strip_html(raw)
    txt = _respostas_glued.sub(r"\1 — \2 respostas", txt)
    read_more = None
    m = _leia_mais_re.search(txt)
    if m:
        read_more = m.group(2)
        txt = _leia_mais_re.sub("", txt).strip()
    txt = _duracao_fim.sub("", txt).strip(" -–—·•\u2026 ")
    return txt, read_more

def clean_title(raw: str) -> str:
    t = _cdata_re.sub("", raw or "")
    t = _strip_html(t)
    t = re.sub(r"[\]\-–—\s]+$", "", t)
    t = re.sub(r"\s+", " ", t)
    return t

def parse_datetime(entry):
    dt = None
    for key in ("published_parsed", "updated_parsed"):
        if getattr(entry, key, None):
            ts = calendar.timegm(getattr(entry, key))
            dt = datetime.fromtimestamp(ts, timezone.utc).astimezone(TZ)
            break
    if not dt:
        raw = entry.get("published") or entry.get("updated") or ""
        try:
            dt = parsedate_to_datetime(raw)
            if dt.tzinfo is None:
                dt = dt.replace(tzinfo=timezone.utc)
            dt = dt.astimezone(TZ)
        except Exception:
            dt = datetime.now(TZ)
    shown = dt.strftime("%a, %d %b %Y %H:%M:%S %z")
    return dt, shown

def _absolutize(url, base):
    if not url:
        return None
    if url.startswith("//"):
        parsed = urlparse(base or "https://")
        return f"{parsed.scheme}:{url}" if parsed.scheme else f"https:{url}"
    return urljoin(base or "", url)

def _is_tiny_icon(url):
    return bool(re.search(r'(\b|_)(16|24|32|48|64|96)x\1?(16|24|32|48|64|96)\b', url or "", re.I))

def _first_image_in_content(entry, resumo_raw):
    contents = entry.get("content") or []
    for c in contents:
        val = c.get("value") if isinstance(c, dict) else getattr(c, "value", None)
        if val:
            m = _img_re.search(val)
            if m:
                return m.group(1)
    raw_ce = entry.get("content:encoded") or ""
    if raw_ce:
        m = _img_re.search(raw_ce)
        if m:
            return m.group(1)
    m = _img_re.search(resumo_raw or "")
    return m.group(1) if m else None

def _first_href_in_content(entry, base_link):
    contents = entry.get("content") or []
    for c in contents:
        val = c.get("value") if isinstance(c, dict) else getattr(c, "value", None)
        if val:
            m = _href_re.search(val)
            if m:
                return _absolutize(m.group(1), base_link)
    raw_ce = entry.get("content:encoded") or ""
    if raw_ce:
        m = _href_re.search(raw_ce)
        if m:
            return _absolutize(m.group(1), base_link)
    resumo_raw = entry.get("summary") or entry.get("description") or ""
    m = _href_re.search(resumo_raw)
    if m:
        return _absolutize(m.group(1), base_link)
    return None

def _favicon_from(link: str) -> str:
    try:
        u = urlparse(link or "")
        base = f"{u.scheme}://{u.netloc}" if u.scheme and u.netloc else ""
        return urljoin(base, "/favicon.ico") if base else None
    except Exception:
        return None

# --- pega og:image / twitter:image da página ---
_session = requests.Session()
_session.headers.update({
    "User-Agent": "Mozilla/5.0 (RSS Preview Bot; +https://example.local) Python/requests"
})

def get_page_image(article_url: str) -> str | None:
    try:
        resp = _session.get(article_url, timeout=3)
        if resp.status_code >= 400:
            return None
        soup = BeautifulSoup(resp.text, "html.parser")
        og = soup.find("meta", property="og:image") or soup.find("meta", attrs={"name": "og:image"})
        if og and og.get("content"):
            return _absolutize(og["content"].strip(), article_url)
        tw = soup.find("meta", attrs={"name": "twitter:image"}) or soup.find("meta", property="twitter:image")
        if tw and tw.get("content"):
            return _absolutize(tw["content"].strip(), article_url)
        for script in soup.find_all("script", type="application/ld+json"):
            try:
                import json
                data = json.loads(script.string or "")
                imgs = []
                if isinstance(data, dict):
                    imgs = data.get("image") or []
                elif isinstance(data, list):
                    for it in data:
                        if isinstance(it, dict) and it.get("@type") in ("NewsArticle", "Article"):
                            imgs = it.get("image") or []
                            break
                if isinstance(imgs, str):
                    return _absolutize(imgs, article_url)
                if isinstance(imgs, list) and imgs:
                    return _absolutize(imgs[0], article_url)
            except Exception:
                pass
    except Exception:
        return None
    return None

def extract_image(entry, resumo_raw, link, channel_image_url=None):
    base = link or (entry.get("link") if isinstance(entry, dict) else "") or ""
    thumbs = entry.get("media_thumbnail") or entry.get("media_thumbnails") or []
    if thumbs:
        url = (thumbs[0].get("url") if isinstance(thumbs[0], dict)
               else getattr(thumbs[0], "url", None))
        if url:
            url = _absolutize(url, base)
            if url and not _is_tiny_icon(url):
                return url
    media = entry.get("media_content") or []
    for m in media:
        url = (m.get("url") if isinstance(m, dict) else getattr(m, "url", None))
        if url:
            url = _absolutize(url, base)
            if url and not _is_tiny_icon(url):
                return url
    for l in entry.get("links", []):
        rel = l.get("rel") if isinstance(l, dict) else getattr(l, "rel", "")
        typ = l.get("type") if isinstance(l, dict) else getattr(l, "type", "")
        href = l.get("href") if isinstance(l, dict) else getattr(l, "href", "")
        if (rel == "enclosure" or (typ and str(typ).startswith("image/"))) and href:
            href = _absolutize(href, base)
            if href and not _is_tiny_icon(href):
                return href
    inline = _first_image_in_content(entry, resumo_raw)
    if inline:
        inline = _absolutize(inline, base)
        if inline and not _is_tiny_icon(inline):
            return inline
    if link:
        ogimg = get_page_image(link)
        if ogimg and not _is_tiny_icon(ogimg):
            return ogimg
    try:
        host = urlparse(base).netloc
    except Exception:
        host = ""
    if "fecomercio.com.br" in host and channel_image_url:
        return _absolutize(channel_image_url, base)
    if channel_image_url and not _is_tiny_icon(channel_image_url):
        return _absolutize(channel_image_url, base)
    return _favicon_from(base)

# ---------------------- Conteúdo (apenas newspaper3k) ----------------------
def _clean_text_spaces(txt: str) -> str:
    txt = (txt or "").replace("\r", " ").replace("\n", " ")
    txt = re.sub(r"\s+", " ", txt).strip()
    return txt

def _truncate(txt: str, limit: int) -> tuple[str, bool]:
    if txt is None:
        return "", False
    if len(txt) <= limit:
        return txt, False
    return txt[:limit], True

def fetch_article_content_newspaper(url: str) -> dict | None:
    """
    Extrai conteúdo com newspaper3k. Se não conseguir, retorna None.
    """
    if not _HAS_NEWSPAPER:
        return None
    try:
        art = _NPArticle(url, language="pt")
        art.download()
        art.parse()
        txt = _clean_text_spaces(getattr(art, "text", "") or "")
        if not txt:
            return None
        txt, trunc = _truncate(txt, CONTENT_MAX_CHARS)
        return {"texto": txt, "truncado": trunc}
    except Exception:
        return None

# ----------------------------- Coleta & Contagem -----------------------------
def coletar_artigos():
    artigos = []
    print("⏳ Iniciando coleta de feeds...")
    for url in ALL_FEEDS:
        inicio = time.time()
        print(f"→ Lendo {url}")
        try:
            feed = feedparser.parse(url)
            elapsed = time.time() - inicio
            qtd = len(feed.entries)
            print(f"   ✅ {url} carregado em {elapsed:.1f}s com {qtd} itens")

            fonte = clean_source(feed.feed.get("title", url))
            channel_img = None
            imgobj = feed.feed.get("image")
            if isinstance(imgobj, dict):
                channel_img = imgobj.get("href") or imgobj.get("url")
            else:
                channel_img = getattr(imgobj, "href", None) or getattr(imgobj, "url", None)
            if not channel_img:
                channel_img = feed.feed.get("image_url") or feed.feed.get("image_href")

            for e in feed.entries:
                titulo = clean_title(e.get("title"))
                link = (e.get("link") or "").strip()
                resumo_raw = e.get("summary") or e.get("description") or ""
                imagem = extract_image(e, resumo_raw, link, channel_image_url=channel_img)
                resumo, leia_mais = clean_summary(resumo_raw)

                try:
                    host = urlparse(link).netloc
                except Exception:
                    host = ""

                # conteúdo com newspaper; se não vier, NÃO adiciona artigo
                conteudo_info = fetch_article_content_newspaper(link) if link else None
                if not conteudo_info or not conteudo_info.get("texto"):
                    continue  # descarta artigo sem conteúdo

                dt, shown = parse_datetime(e)

                artigos.append({
                    "titulo": titulo,
                    "link": link,
                    "resumo": resumo,
                    "leia_mais": leia_mais,
                    "fonte": fonte,
                    "publicado": shown,
                    "imagem": imagem,
                    "ts": dt.timestamp(),
                    "conteudo": conteudo_info["texto"],
                    "conteudo_len": len(conteudo_info["texto"]),
                    "conteudo_truncado": bool(conteudo_info["truncado"]),
                    "conteudo_source": "newspaper",
                })

        except Exception as ex:
            print(f"❌ Erro no feed {url}: {ex}")
    print(f"🏁 Coleta concluída: {len(artigos)} artigos no total (apenas com conteúdo)")
    artigos.sort(key=lambda x: x["ts"], reverse=True)
    return artigos

def contar_por_fonte(artigos):
    cont = Counter(a["fonte"] for a in artigos)
    ordenado = OrderedDict(sorted(cont.items(), key=lambda kv: (-kv[1], kv[0].lower())))
    total = sum(cont.values())
    return ordenado, total

# ----------------------------- Cache/snapshot -----------------------------
_snapshot_lock = threading.Lock()
_snapshot = {"data": None, "built_at": None, "next_build_at": None, "etag": None}

def _build_snapshot():
    artigos = coletar_artigos()
    contagens, total = contar_por_fonte(artigos)
    built_at = datetime.now(TZ).replace(microsecond=0)
    # agenda próxima virando pra próxima hora + 1h
    next_build_at = (built_at.replace(minute=0, second=0) + REFRESH_INTERVAL)
    payload = {
        "generated_at": built_at.isoformat(),
        "next_refresh_at": next_build_at.isoformat(),
        "total": total,
        "por_fonte": contagens,
        "artigos": artigos,
    }
    etag_src = (str(total) + built_at.isoformat()).encode("utf-8")
    etag = hashlib.sha256(etag_src).hexdigest()[:16]
    with _snapshot_lock:
        _snapshot["data"] = payload
        _snapshot["built_at"] = built_at
        _snapshot["next_build_at"] = next_build_at
        _snapshot["etag"] = etag
    print(f"✅ Snapshot reconstruído às {built_at.isoformat()} (próximo às {next_build_at.isoformat()})")

def _ensure_first_snapshot():
    print("🛠 Garantindo que o primeiro snapshot exista...")
    with _snapshot_lock:
        need = _snapshot["data"] is None
    if need:
        _build_snapshot()
    else:
        print("✅ Snapshot já existente, pulando rebuild.")

def _background_refresher(stop_evt: threading.Event):
    while not stop_evt.is_set():
        try:
            now = datetime.now(TZ)
            with _snapshot_lock:
                nxt = _snapshot["next_build_at"]
            if nxt is None or now >= nxt:
                _build_snapshot()
        except Exception as e:
            print("Erro no refresher:", e)
        stop_evt.wait(15)

_stop_event = threading.Event()
_refresher_thread = threading.Thread(target=_background_refresher, args=(_stop_event,), daemon=True)

# ----------------------------- Respostas HTTP -----------------------------
def _with_http_cache_headers(resp, built_at: datetime, etag: str):
    max_age = int(REFRESH_INTERVAL.total_seconds() - 60) if REFRESH_INTERVAL.total_seconds() > 60 else int(REFRESH_INTERVAL.total_seconds())
    resp.headers["Cache-Control"] = f"public, max-age={max_age}"
    resp.headers["ETag"] = etag
    resp.headers["Last-Modified"] = format_datetime(built_at.astimezone(timezone.utc))
    resp.headers["X-Snapshot-Generated-At"] = built_at.isoformat()
    return resp

@app.get("/api/v1/news")
def api_news():
    """
    Entrega o snapshot mais recente (NÃO reconstrói on-demand).
    Suporta ETag/If-None-Match e If-Modified-Since -> 304 Not Modified.
    """
    _ensure_first_snapshot()
    with _snapshot_lock:
        data = _snapshot["data"]
        built_at = _snapshot["built_at"]
        etag = _snapshot["etag"]

    inm = request.headers.get("If-None-Match")
    ims = request.headers.get("If-Modified-Since")
    if inm and inm == etag:
        return _with_http_cache_headers(make_response(("", 304)), built_at, etag)
    if ims:
        try:
            ims_dt = parsedate_to_datetime(ims)
            if ims_dt.tzinfo is None:
                ims_dt = ims_dt.replace(tzinfo=timezone.utc)
            if built_at <= ims_dt.astimezone(TZ):
                return _with_http_cache_headers(make_response(("", 304)), built_at, etag)
        except Exception:
            pass

    resp = make_response(jsonify(data), 200)
    return _with_http_cache_headers(resp, built_at, etag)

@app.get("/api/v1/status")
def api_status():
    _ensure_first_snapshot()
    with _snapshot_lock:
        built_at = _snapshot["built_at"]
        next_build_at = _snapshot["next_build_at"]
        etag = _snapshot["etag"]
    return {
        "service": "news-snapshot",
        "timezone": str(TZ),
        "generated_at": built_at.isoformat(),
        "next_refresh_at": next_build_at.isoformat(),
        "etag": etag,
        "rate_limit_per_min": RATE_LIMIT_PER_MIN,
        "burst": RATE_LIMIT_BURST,
        "ban_time_seconds": BAN_TIME_SECONDS,
    }

@app.get("/")
def root_tip():
    return {
        "message": "OK",
        "endpoints": {
            "/api/v1/news": "Snapshot JSON das últimas notícias (com conteúdo via newspaper3k).",
            "/api/v1/status": "Status do snapshot/serviço.",
        }
    }

# ----------------------------- Boot ---------------------------------
def _start():
    _ensure_first_snapshot()
    if not _refresher_thread.is_alive():
        _refresher_thread.start()

if __name__ == "__main__":
    import os

    print("🔧 Iniciando API, construindo primeiro snapshot...")
    _start()

    port = int(os.environ.get("PORT", 5000))  # porta que o Render fornece
    print(f"🚀 API pronta em: 0.0.0.0:{port}")
    app.run(host="0.0.0.0", port=port, debug=False, threaded=True)

