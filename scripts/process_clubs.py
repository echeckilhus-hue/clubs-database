#!/usr/bin/env python3
"""
process_clubs.py
-----------------
Reconstitue clubs.txt (base des clubs FFE) depuis echecs.asso.fr, comité par
comité, et génère le fichier au format attendu par parseClubsFile() (main.js) :
  ClubRef<TAB>Nom du Club

⚠️ Différence structurelle avec process_fide.py : la FIDE publie un ZIP
officiel unique et complet (un seul téléchargement suffit). La FFE n'a pas
d'équivalent bulk pour les clubs — on reconstitue la liste complète en
itérant sur tous les comités (départements métropolitains + DOM-TOM) via :

  https://www.echecs.asso.fr/ListeClubs.aspx?Action=CLUBCOMITE&ComiteRef=XX

GET simple, pas de __VIEWSTATE à envoyer pour la 1ère page (confirmé
manuellement sur ComiteRef=9A : 15 clubs, réponse propre). Pagination
ASP.NET (__doPostBack) gérée pour les comités avec beaucoup de clubs, même
principe que detectAspNetPagination()/postback() dans main.js — mais PAS
vérifiée sur un comité réellement paginé (aucun comité testé manuellement
n'en avait besoin). À surveiller sur les premières exécutions réelles,
en particulier les gros comités (75, 92, 93, 94, 59...).

Chaque requête HTTP est réessayée (MAX_RETRIES) en cas d'erreur réseau, de
réponse tronquée, d'erreur 5xx ou de 429 : un raté ponctuel de la FFE ne
coûte plus un comité entier.

Chaque comité est traité individuellement : une erreur réseau persistante ou
une page vide sur UN comité est loggée et ignorée, elle ne fait pas échouer
tout le run (cf. résumé "comités vides / en erreur" en fin d'exécution). Le run
entier échoue seulement si le total de clubs récupérés est trop bas
(MIN_CLUBS) — dans ce cas, clubs.txt n'est PAS écrit, pour ne jamais publier
un fichier tronqué comme release.

Sortie : clubs.txt (ClubRef\tClub, une ligne d'en-tête + une ligne par club)
"""

import os
import re
import sys
import time
import html
import datetime
import http.client
import urllib.request
import urllib.parse
import urllib.error
import http.cookiejar

# ── Configuration ────────────────────────────────────────────────────────────
BASE_URL      = "https://www.echecs.asso.fr/ListeClubs.aspx"
OUTPUT_FILE   = "clubs.txt"
REQUEST_DELAY = 1.5   # secondes entre chaque requête HTTP — reste discret vis-à-vis de la FFE
MAX_PAGES     = 20    # garde-fou anti-boucle-infinie par comité
MIN_CLUBS     = 900   # la FFE annonce ~1007 clubs (juillet 2026) — seuil d'alerte si trop bas
MAX_RETRIES   = 3     # tentatives par requête HTTP (erreur réseau, réponse tronquée, 5xx, 429)
RETRY_DELAY   = 5     # secondes, multiplié par le n° de tentative (5s, 10s...)

# Erreurs "réseau" : ne concernent qu'un comité, jamais tout le run.
# http.client.HTTPException couvre les réponses tronquées (IncompleteRead,
# RemoteDisconnected...) qui ne sont PAS des OSError et faisaient planter le run.
NETWORK_ERRORS = (urllib.error.URLError, TimeoutError, OSError, http.client.HTTPException)


def build_comite_codes():
    """
    Codes des comités départementaux FFE.
    - 96 codes métropolitains : 01-19, 2A, 2B (Corse), 21-95.
      ⚠️ PAS confirmés à 100% contre le paramètre ComiteRef (page Comites.aspx
      utilise une carte cliquable, pas de liste texte) — hypothèse codes INSEE
      standards. Un code invalide ne fait pas planter le run (cf. fetch_comite_clubs).
    - 7 codes DOM-TOM confirmés manuellement sur echecs.asso.fr/Comites.aspx
      et echecs.asso.fr/Clubs.aspx (NE suivent PAS les codes INSEE standards
      971-976 : la FFE utilise son propre schéma 9A-9J).
    """
    codes = [f"{i:02d}" for i in range(1, 20)]         # 01-19
    codes += ["2A", "2B"]                                # Corse
    codes += [f"{i:02d}" for i in range(21, 96)]         # 21-95
    codes += ["9A", "9B", "9C", "9D", "9F", "9G", "9J"]  # DOM-TOM confirmés
    return codes


# ── Helpers ────────────────────────────────────────────────────────────────────
def log(msg: str) -> None:
    ts = datetime.datetime.now().strftime("%H:%M:%S")
    print(f"[{ts}] {msg}", flush=True)


_cookie_jar = http.cookiejar.CookieJar()
_opener = urllib.request.build_opener(urllib.request.HTTPCookieProcessor(_cookie_jar))


def fetch(url: str, body: str = None, referer: str = None) -> str:
    """GET si body est None, POST sinon (postback ASP.NET). Retourne le HTML en texte."""
    headers = {"User-Agent": "TournamentManager/1.0"}
    data = None
    if body is not None:
        headers["Content-Type"] = "application/x-www-form-urlencoded"
        headers["Cache-Control"] = "no-cache"
        headers["Pragma"] = "no-cache"
        if referer:
            headers["Referer"] = referer
        data = body.encode("utf-8")

    req = urllib.request.Request(url, data=data, headers=headers)
    for attempt in range(1, MAX_RETRIES + 1):
        try:
            with _opener.open(req, timeout=30) as resp:
                raw = resp.read()
                charset = resp.headers.get_content_charset() or "utf-8"
            break
        except NETWORK_ERRORS as e:
            # 4xx (hors 429) : la requête elle-même est refusée, inutile d'insister
            if isinstance(e, urllib.error.HTTPError) and e.code < 500 and e.code != 429:
                raise
            if attempt == MAX_RETRIES:
                raise
            wait = RETRY_DELAY * attempt
            log(f"    ↻ {e!r} — nouvelle tentative {attempt + 1}/{MAX_RETRIES} dans {wait}s")
            time.sleep(wait)

    try:
        return raw.decode(charset, errors="replace")
    except LookupError:  # charset annoncé par le serveur inconnu de Python
        return raw.decode("utf-8", errors="replace")


def extract_clubs(page_html: str) -> dict:
    """
    { ref: name } depuis les liens <a href="FicheClub.aspx?Ref=XXX">Nom</a>.
    Même approche que extractClubs() dans main.js : on cible les liens, pas
    la position des colonnes (plus robuste aux variations de mise en page).
    """
    out = {}
    for m in re.finditer(
        r'<a[^>]+href="[^"]*FicheClub\.aspx\?Ref=(\d+)"[^>]*>(.*?)</a>',
        page_html, re.I | re.S
    ):
        ref = m.group(1)
        name = re.sub(r"<[^>]+>", "", m.group(2))  # retire tags imbriqués éventuels (ex: <span>)
        name = html.unescape(name).strip()
        name = re.sub(r"\s+", " ", name)
        if ref and name:
            out[ref] = name
    return out


def extract_hidden_fields(page_html: str) -> dict:
    """Champs cachés ASP.NET (__VIEWSTATE, __EVENTVALIDATION, ...) pour le postback."""
    fields = {}
    for tag in re.finditer(r"<input\b[^>]*type=[\"']hidden[\"'][^>]*>", page_html, re.I):
        tag_str = tag.group(0)
        name_m  = re.search(r'name=["\']([^"\']+)["\']', tag_str, re.I)
        value_m = re.search(r'value=["\']([^"\']*)["\']', tag_str, re.I)
        if name_m:
            fields[name_m.group(1)] = html.unescape(value_m.group(1)) if value_m else ""
    fields.setdefault("__EVENTTARGET", "")
    fields.setdefault("__EVENTARGUMENT", "")
    return fields


def detect_pagination(page_html: str):
    """
    Retourne (event_target, {page_num: argument}) ou None.
    Même logique que detectAspNetPagination() dans main.js, adaptée en regex Python.
    """
    unescaped = html.unescape(page_html)
    pager = {}
    target = None
    for m in re.finditer(r"__doPostBack\(['\"]([^'\"]+)['\"],\s*['\"]([^'\"]*)['\"]\)", unescaped):
        t, arg = m.group(1), m.group(2)
        if "Pager" not in t:
            continue
        target = target or t
        if arg.isdigit():
            pager[int(arg)] = arg

    if not target or not pager:
        return None
    return target, pager


def fetch_comite_clubs(comite_ref: str) -> dict:
    """Récupère tous les clubs d'un comité, avec pagination si nécessaire."""
    url = f"{BASE_URL}?Action=CLUBCOMITE&ComiteRef={comite_ref}"
    page_html = fetch(url)
    clubs = extract_clubs(page_html)

    pagination = detect_pagination(page_html)
    if pagination:
        target, pages = pagination
        total_pages = min(max(pages.keys()), MAX_PAGES)
        for page in range(2, total_pages + 1):
            time.sleep(REQUEST_DELAY)
            fields = extract_hidden_fields(page_html)
            fields["__EVENTTARGET"] = target
            fields["__EVENTARGUMENT"] = pages.get(page, str(page))
            body = urllib.parse.urlencode(fields)
            page_html = fetch(url, body=body, referer=url)
            clubs.update(extract_clubs(page_html))

    return clubs


def sort_key(ref: str):
    """Tri numérique quand possible (les ClubRef observés sont purement numériques)."""
    try:
        return (0, int(ref))
    except ValueError:
        return (1, ref)


# ── Main ───────────────────────────────────────────────────────────────────────
def main():
    start = datetime.datetime.now()
    log("🏰 === FFE Clubs Database Builder ===")
    log(f"Date : {start.strftime('%Y-%m-%d %H:%M:%S')}")

    codes = build_comite_codes()
    log(f"📋 {len(codes)} comités à parcourir")

    all_clubs = {}
    empty = []
    failed = []

    for i, code in enumerate(codes, 1):
        try:
            clubs = fetch_comite_clubs(code)
            if not clubs:
                empty.append(code)
            else:
                all_clubs.update(clubs)
            log(f"  [{i:>3}/{len(codes)}] Comité {code:>3} : {len(clubs):>4} clubs  (cumulé : {len(all_clubs)})")
        except NETWORK_ERRORS as e:
            failed.append(code)
            log(f"  [{i:>3}/{len(codes)}] Comité {code:>3} : ❌ {e}")
        time.sleep(REQUEST_DELAY)

    total = len(all_clubs)
    log("=" * 50)
    log(f"✓ {total:,} clubs uniques récupérés")
    if empty:
        log(f"⚠️  {len(empty)} comités sans club retourné : {', '.join(empty)}")
    if failed:
        log(f"⚠️  {len(failed)} comités en erreur réseau : {', '.join(failed)}")

    # Garde-fou : on n'écrit JAMAIS clubs.txt si le total est suspect
    # (mieux vaut faire échouer le job que publier une release tronquée).
    if total < MIN_CLUBS:
        log(f"❌ ERREUR: seulement {total} clubs (attendu > {MIN_CLUBS}) — clubs.txt non écrit")
        sys.exit(1)

    with open(OUTPUT_FILE, "w", encoding="utf-8", newline="\n") as f:
        f.write("ClubRef\tClub\n")
        for ref in sorted(all_clubs, key=sort_key):
            f.write(f"{ref}\t{all_clubs[ref]}\n")

    size_kb = os.path.getsize(OUTPUT_FILE) / 1024
    duration = (datetime.datetime.now() - start).total_seconds()
    log(f"📁 {OUTPUT_FILE} : {size_kb:.1f} KB")
    log(f"⏱️  Terminé en {duration:.0f}s")

    # Pour GitHub Actions summary (le job appelant lit aussi clubs.txt indépendamment
    # dans son étape "Validate", même principe de défense-en-profondeur que FIDE)
    summary = f"""
## 🏰 FFE Clubs Database — {start.strftime('%Y-%m')}

| | |
|---|---|
| 🏛️ Clubs total | {total:,} |
| ⚠️ Comités vides | {len(empty)} |
| ❌ Comités en erreur | {len(failed)} |
| ⏱️ Durée | {duration:.0f}s |
"""
    if "GITHUB_STEP_SUMMARY" in os.environ:
        with open(os.environ["GITHUB_STEP_SUMMARY"], "a") as f:
            f.write(summary)


if __name__ == "__main__":
    main()
