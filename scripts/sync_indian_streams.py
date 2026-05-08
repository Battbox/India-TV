#!/usr/bin/env python3
"""
sync_indian_streams.py — Smart stream synchronization for Indian TV

Mirrors the architecture of sync_streams.py (used by Libnan TV) but operates
INDEPENDENTLY on indian-tv.html so that Libnan TV's pipeline is never touched.

Strategy (tries each in order until streams found):
  1. EXACT channel ID match against iptv-org streams.json
  2. ALTERNATE IDs (configured per channel)
  3. TITLE FUZZY match against streams.json (catches ID typos & moves)

Then optionally HEAD-checks each candidate URL (8s timeout) before applying.
Failed channels keep their existing URLs (the safety net).

Outputs INDIAN_STREAMS_REPORT.md with per-channel detail.
"""

import json
import os
import re
import sys
import time
import urllib.request
import urllib.error
from concurrent.futures import ThreadPoolExecutor, as_completed
from difflib import SequenceMatcher

HTML_FILE = os.environ.get("HTML_FILE", "indian-tv.html")
REPORT_FILE = os.environ.get("REPORT_FILE", "INDIAN_STREAMS_REPORT.md")
VALIDATE = os.environ.get("VALIDATE_STREAMS", "true").lower() == "true"

MAX_STREAMS_PER_CH = 8
MAX_NEW_FROM_API = 7   # leave room for at least one existing fallback
HEAD_TIMEOUT = 8       # seconds
HEAD_WORKERS = 8       # parallel HEAD checks

BAD_LABELS = {"geo-blocked", "error", "drm", "not 24/7", "offline"}

# ─────────────────────────────────────────────────────────────────────
# Channel mapping. Each entry: (primary_id, [alternate_ids], [title_keywords])
# title_keywords are used for fuzzy fallback if no ID matches.
# Use lowercase for keywords; matching is case-insensitive.
# Primary IDs follow iptv-org convention: <ChannelName>.in
# ─────────────────────────────────────────────────────────────────────
CHANNEL_MAP = {
    # ═══ HINDI — News ═══
    "ndtv-india":      ("NDTVIndia.in",      ["NDTV24x7.in"],                ["ndtv india", "ndtv hindi"]),
    "aajtak":          ("AajTak.in",         ["AajTakHD.in"],                ["aaj tak", "aajtak"]),
    "abp-news":        ("ABPNews.in",        [],                             ["abp news", "abp hindi"]),
    "india-tv":        ("IndiaTV.in",        ["IndiaTVHD.in"],               ["india tv", "indiatv"]),
    "news18-india":    ("News18India.in",    [],                             ["news18 india", "news 18 india"]),
    "zee-news":        ("ZeeNews.in",        [],                             ["zee news"]),
    "republic-bharat": ("RepublicBharat.in", [],                             ["republic bharat"]),
    "tv9-bharatvarsh": ("TV9Bharatvarsh.in", ["TV9Hindi.in"],                ["tv9 bharatvarsh", "tv9 hindi"]),

    # ═══ HINDI — Entertainment ═══
    "zee-tv":          ("ZeeTV.in",          ["ZeeTVHD.in"],                 ["zee tv"]),
    "sab-tv":          ("SonySAB.in",        ["SABTV.in"],                   ["sab tv", "sony sab"]),
    "colors-tv":       ("Colors.in",         ["ColorsHD.in"],                ["colors tv", "colors hd"]),
    "star-bharat":     ("StarBharat.in",     [],                             ["star bharat"]),
    "and-tv":          ("AndTV.in",          ["AndTVHD.in"],                 ["&tv", "and tv"]),

    # ═══ HINDI — Movies ═══
    "zee-cinema":      ("ZeeCinema.in",      ["ZeeCinemaHD.in"],             ["zee cinema"]),
    "and-pictures":    ("AndPictures.in",    [],                             ["&pictures", "and pictures"]),
    "sony-max":        ("SonyMAX.in",        ["SonyMAXHD.in"],               ["sony max"]),
    "b4u-movies":      ("B4UMovies.in",      [],                             ["b4u movies"]),
    "zee-bollywood":   ("ZeeBollywood.in",   [],                             ["zee bollywood"]),

    # ═══ HINDI — Music ═══
    "9xm":             ("9XM.in",            [],                             ["9xm"]),
    "mtv-beats":       ("MTVBeats.in",       ["MTVBeatsHD.in"],              ["mtv beats"]),
    "b4u-music":       ("B4UMusic.in",       [],                             ["b4u music"]),

    # ═══ TAMIL ═══
    "sun-news":        ("SunNews.in",        [],                             ["sun news"]),
    "thanthi-tv":      ("ThanthiTV.in",      [],                             ["thanthi tv"]),
    "polimer-news":    ("PolimerNews.in",    ["Polimer.in"],                 ["polimer news", "polimer"]),
    "sun-tv":          ("SunTV.in",          ["SunTVHD.in"],                 ["sun tv"]),
    "vijay-tv":        ("StarVijay.in",      ["VijayTV.in"],                 ["star vijay", "vijay tv"]),
    "zee-tamil":       ("ZeeTamil.in",       ["ZeeTamilHD.in"],              ["zee tamil"]),
    "colors-tamil":    ("ColorsTamil.in",    ["ColorsTamilHD.in"],           ["colors tamil"]),
    "ktv":             ("KTV.in",            [],                             ["k tv", "ktv tamil"]),
    "sun-music":       ("SunMusic.in",       [],                             ["sun music"]),
    "raj-tv":          ("RajTV.in",          [],                             ["raj tv"]),

    # ═══ TELUGU ═══
    "tv9-telugu":      ("TV9Telugu.in",      [],                             ["tv9 telugu"]),
    "abn-telugu":      ("ABNAndhraJyothy.in",["ABN.in"],                     ["abn andhra", "andhra jyothy"]),
    "ntv-telugu":      ("NTVTelugu.in",      ["NTV.in"],                     ["ntv telugu"]),
    "gemini-tv":       ("GeminiTV.in",       [],                             ["gemini tv"]),
    "etv-telugu":      ("ETVTelugu.in",      ["ETV.in"],                     ["etv telugu"]),
    "star-maa":        ("StarMaa.in",        ["MaaTV.in"],                   ["star maa", "maa tv"]),
    "zee-telugu":      ("ZeeTelugu.in",      ["ZeeTeluguHD.in"],             ["zee telugu"]),
    "sakshi-tv":       ("SakshiTV.in",       [],                             ["sakshi tv"]),

    # ═══ MALAYALAM ═══
    "asianet-news":    ("AsianetNews.in",    [],                             ["asianet news"]),
    "manorama-news":   ("ManoramaNews.in",   [],                             ["manorama news"]),
    "mathrubhumi-news":("MathrubhumiNews.in",[],                             ["mathrubhumi news"]),
    "asianet":         ("Asianet.in",        ["AsianetHD.in"],               ["asianet", "asianet plus"]),
    "surya-tv":        ("SuryaTV.in",        [],                             ["surya tv"]),
    "mazhavil":        ("MazhavilManorama.in",[],                            ["mazhavil manorama"]),
    "flowers-tv":      ("FlowersTV.in",      ["Flowers.in"],                 ["flowers tv"]),

    # ═══ KANNADA ═══
    "tv9-kannada":     ("TV9Kannada.in",     [],                             ["tv9 kannada"]),
    "public-tv":       ("PublicTV.in",       [],                             ["public tv"]),
    "udaya-tv":        ("UdayaTV.in",        [],                             ["udaya tv"]),
    "colors-kannada":  ("ColorsKannada.in",  ["ColorsKannadaHD.in"],         ["colors kannada"]),
    "zee-kannada":     ("ZeeKannada.in",     [],                             ["zee kannada"]),
    "star-suvarna":    ("StarSuvarna.in",    ["AsianetSuvarna.in"],          ["star suvarna", "asianet suvarna"]),

    # ═══ BENGALI ═══
    "zee-bangla":      ("ZeeBangla.in",      [],                             ["zee bangla"]),
    "star-jalsha":     ("StarJalsha.in",     [],                             ["star jalsha"]),
    "colors-bangla":   ("ColorsBangla.in",   [],                             ["colors bangla"]),
    "sun-bangla":      ("SunBangla.in",      [],                             ["sun bangla"]),
    "abp-ananda":      ("ABPAnanda.in",      [],                             ["abp ananda"]),

    # ═══ MARATHI ═══
    "zee-marathi":     ("ZeeMarathi.in",     [],                             ["zee marathi"]),
    "colors-marathi":  ("ColorsMarathi.in",  [],                             ["colors marathi"]),
    "star-pravah":     ("StarPravah.in",     [],                             ["star pravah"]),
    "abp-majha":       ("ABPMajha.in",       [],                             ["abp majha"]),
    "tv9-marathi":     ("TV9Marathi.in",     [],                             ["tv9 marathi"]),

    # ═══ PUNJABI ═══
    "ptc-punjabi":     ("PTCPunjabi.in",     [],                             ["ptc punjabi"]),
    "pitaara":         ("PitaaraTV.in",      ["Pitaara.in"],                 ["pitaara"]),
    "chardikla":       ("ChardiklaTimeTV.in",["ChardiklaTime.in"],           ["chardikla", "chardikla time"]),
    "9x-tashan":       ("9XTashan.in",       [],                             ["9x tashan"]),

    # ═══ ENGLISH / NATIONAL ═══
    "ndtv-247":        ("NDTV24x7.in",       ["NDTV247.in"],                 ["ndtv 24x7", "ndtv 24"]),
    "india-today":     ("IndiaToday.in",     [],                             ["india today"]),
    "republic-tv":     ("RepublicTV.in",     [],                             ["republic tv"]),
    "mirror-now":      ("MirrorNow.in",      [],                             ["mirror now"]),
    "wion":            ("WION.in",           [],                             ["wion", "world is one"]),
    "cnn-news18":      ("CNNNews18.in",      [],                             ["cnn news18", "cnn-news18"]),
    "times-now":       ("TimesNow.in",       [],                             ["times now"]),
    "dd-news":         ("DDNews.in",         [],                             ["dd news"]),
    "dd-national":     ("DDNational.in",     [],                             ["dd national", "doordarshan national"]),
    "dd-sports":       ("DDSports.in",       [],                             ["dd sports", "doordarshan sports"]),

    # ═══ DEVOTIONAL ═══
    "aastha":          ("Aastha.in",         ["AasthaTV.in"],                ["aastha", "aastha tv"]),
    "sanskar":         ("Sanskar.in",        ["SanskarTV.in"],               ["sanskar"]),
    "shubh-tv":        ("ShubhTV.in",        [],                             ["shubh tv"]),

    # ═══ KIDS ═══
    "pogo":            ("Pogo.in",           ["PogoHD.in"],                  ["pogo"]),
    "cartoon-network": ("CartoonNetwork.in", ["CartoonNetworkHD.in"],        ["cartoon network"]),
    "nick-india":      ("Nickelodeon.in",    ["NickIndia.in"],               ["nickelodeon", "nick india"]),
    "disney-india":    ("DisneyChannel.in",  ["DisneyIndia.in"],             ["disney channel", "disney india"]),
}

# ─────────────────────────────────────────────────────────────────────
def fetch_json(path):
    """Load locally-fetched API JSON written by the workflow step."""
    with open(path, encoding="utf-8") as f:
        return json.load(f)


def load_apis():
    streams = fetch_json("streams.json")
    channels = fetch_json("channels.json") if os.path.exists("channels.json") else []
    print(f"Loaded {len(streams)} streams, {len(channels)} channels from iptv-org")
    return streams, channels


def is_good_stream(s):
    """Filter out streams with bad labels, missing URLs, non-m3u8."""
    url = s.get("url", "")
    if not url or ".m3u8" not in url.lower():
        return False
    label = (s.get("label") or "").lower()
    status = (s.get("status") or "").lower()
    if any(bad in label for bad in BAD_LABELS):
        return False
    if status == "error":
        return False
    return True


def build_indexes(streams):
    """Build (channel-id -> [urls]) and (lowercased-channel-id -> [urls]) indexes.

    Note: streams.json from iptv-org has a `channel` field that is the channel ID,
    plus a `title` field with the human name. We index both.
    """
    by_id = {}
    by_title = {}
    for s in streams:
        if not is_good_stream(s):
            continue
        ch_id = s.get("channel") or ""
        url = s["url"]
        title = (s.get("title") or "").lower()
        if ch_id:
            by_id.setdefault(ch_id, []).append(url)
        if title:
            by_title.setdefault(title, []).append(url)
    return by_id, by_title


def find_streams_for(our_id, by_id, by_title):
    """Try exact ID, alternates, then fuzzy title match.
    Returns (urls, strategy_label).
    """
    primary, alts, keywords = CHANNEL_MAP[our_id]

    # Strategy 1: exact ID
    if primary in by_id:
        return by_id[primary], f"exact:{primary}"

    # Strategy 2: alternate IDs
    for alt in alts:
        if alt in by_id:
            return by_id[alt], f"alt:{alt}"

    # Strategy 3: fuzzy title via keywords
    if keywords:
        # Score each title against any keyword
        candidates = []
        for title, urls in by_title.items():
            best = 0
            for kw in keywords:
                if kw in title:
                    best = max(best, 1.0)  # substring hit = perfect
                else:
                    best = max(best, SequenceMatcher(None, kw, title).ratio())
            if best >= 0.7:
                candidates.append((best, urls, title))
        if candidates:
            candidates.sort(reverse=True)
            # Take URLs from top-2 matches, deduplicated
            picked = []
            seen = set()
            for _, urls, _ in candidates[:2]:
                for u in urls:
                    if u not in seen:
                        seen.add(u)
                        picked.append(u)
            return picked, "fuzzy-title"

    return [], "no-match"


def head_check_one(url):
    """HEAD-check one URL. Returns url if alive, None otherwise."""
    try:
        req = urllib.request.Request(url, method="HEAD")
        req.add_header("User-Agent", "Mozilla/5.0")
        with urllib.request.urlopen(req, timeout=HEAD_TIMEOUT) as r:
            if 200 <= r.status < 400:
                return url
    except Exception:
        try:
            # Some CDNs reject HEAD; try GET with Range
            req = urllib.request.Request(url)
            req.add_header("User-Agent", "Mozilla/5.0")
            req.add_header("Range", "bytes=0-1023")
            with urllib.request.urlopen(req, timeout=HEAD_TIMEOUT) as r:
                if 200 <= r.status < 400:
                    return url
        except Exception:
            return None
    return None


def validate_urls(urls):
    """Parallel HEAD-check up to len(urls) URLs."""
    if not urls:
        return []
    alive = []
    with ThreadPoolExecutor(max_workers=HEAD_WORKERS) as ex:
        futures = {ex.submit(head_check_one, u): u for u in urls}
        for fut in as_completed(futures):
            r = fut.result()
            if r:
                alive.append(r)
    # Preserve original order
    return [u for u in urls if u in alive]


def patch_html(html, our_id, urls):
    """Replace the streams:[…] block for `our_id` in the HTML with `urls`,
    keeping any existing URLs as fallbacks (max 5, deduplicated, fresh first).
    Returns (new_html, existing_count, replaced)."""
    pattern = (
        r'(id\s*:\s*"' + re.escape(our_id) + r'"'
        r'.*?streams\s*:\s*\[)'
        r'([^\]]*)'
        r'(\])'
    )
    m = re.search(pattern, html, re.DOTALL)
    if not m:
        return html, 0, False
    existing = re.findall(r'"(https?://[^"]+)"', m.group(2))
    seen, combined = set(), []
    for u in (urls + existing):
        if u not in seen:
            seen.add(u)
            combined.append(u)
    final = combined[:MAX_STREAMS_PER_CH]
    formatted = ",\n     ".join(f'"{u}"' for u in final)
    replacement = m.group(1) + "\n     " + formatted + "\n   " + m.group(3)
    new_html = html[:m.start()] + replacement + html[m.end():]
    return new_html, len(existing), True


# ─────────────────────────────────────────────────────────────────────
def main():
    streams, _channels = load_apis()
    by_id, by_title = build_indexes(streams)
    print(f"Indexed {len(by_id)} channel-IDs, {len(by_title)} unique titles\n")

    with open(HTML_FILE, encoding="utf-8") as f:
        html = f.read()
    print(f"Loaded {HTML_FILE} ({len(html):,} chars)\n")

    rows = []  # (our_id, strategy, n_api, n_validated, n_existing, n_final, status)
    updated = kept = dead = 0

    for our_id in CHANNEL_MAP:
        api_urls, strategy = find_streams_for(our_id, by_id, by_title)
        api_count = len(api_urls)

        # Take some extra so HEAD-validation still leaves enough
        api_urls = api_urls[:MAX_NEW_FROM_API * 2]

        if VALIDATE and api_urls:
            print(f"  [{our_id:<22}] HEAD-checking {len(api_urls)} URLs ({strategy})...", flush=True)
            t0 = time.time()
            api_urls = validate_urls(api_urls)
            print(f"  [{our_id:<22}] {len(api_urls)} alive in {time.time()-t0:.1f}s")

        api_urls = api_urls[:MAX_NEW_FROM_API]

        # Find existing streams (always)
        existing_match = re.search(
            r'id\s*:\s*"' + re.escape(our_id) + r'".*?streams\s*:\s*\[([^\]]*)\]',
            html, re.DOTALL
        )
        in_html = existing_match is not None
        existing = re.findall(r'"(https?://[^"]+)"', existing_match.group(1)) if existing_match else []

        if not in_html:
            status = "NOT_IN_HTML"
            rows.append((our_id, strategy, api_count, 0, 0, 0, status))
            continue

        if api_urls:
            html, n_existing, _ = patch_html(html, our_id, api_urls)
            final_count = min(len(api_urls) + len(existing) - len(set(api_urls) & set(existing)), MAX_STREAMS_PER_CH)
            status = "UPDATED"
            updated += 1
        else:
            n_existing = len(existing)
            final_count = n_existing
            if api_count > 0 and not api_urls:
                # API had streams but all failed validation
                status = "ALL_DEAD"
                dead += 1
            elif n_existing > 0:
                status = "KEPT_OLD"
                kept += 1
            else:
                status = "EMPTY"
                dead += 1

        rows.append((our_id, strategy, api_count, len(api_urls), len(existing), final_count, status))

        emoji = {"UPDATED":"✅","KEPT_OLD":"⚠️","ALL_DEAD":"💀","EMPTY":"❌","NOT_IN_HTML":"🔥"}.get(status, "?")
        print(f"  {emoji} {our_id:<22} {status:<12} strategy={strategy:<22} api={api_count} validated={len(api_urls)} existing={len(existing)} → {final_count}")

    # Write patched HTML
    with open(HTML_FILE, "w", encoding="utf-8") as f:
        f.write(html)

    # Write report
    lines = [
        "# Indian Stream Sync Report",
        "",
        f"**Generated:** {time.strftime('%Y-%m-%d %H:%M UTC', time.gmtime())}",
        f"**Validation:** {'enabled (HEAD-checked)' if VALIDATE else 'disabled'}",
        "",
        f"- **Updated:** {updated}",
        f"- **Kept old (no fresh streams found):** {kept}",
        f"- **Completely dead (no streams anywhere):** {dead}",
        "",
        "## Per-channel detail",
        "",
        "| Channel | Status | Strategy | API found | Validated | Existing | Final |",
        "|---|---|---|---|---|---|---|",
    ]
    for our_id, strategy, api_c, val_c, exist_c, final_c, status in rows:
        lines.append(f"| {our_id} | {status} | {strategy} | {api_c} | {val_c} | {exist_c} | {final_c} |")

    lines += [
        "",
        "## Legend",
        "",
        "- ✅ **UPDATED** — fresh streams from iptv-org applied (existing kept as fallback)",
        "- ⚠️ **KEPT_OLD** — no match in iptv-org, your hardcoded streams preserved",
        "- 💀 **ALL_DEAD** — iptv-org had streams but ALL failed HEAD-check; old streams preserved",
        "- ❌ **EMPTY** — channel exists in HTML but has zero working streams (broken in app)",
        "- 🔥 **NOT_IN_HTML** — channel id from sync map is missing from the HTML (config drift — fix CHANNEL_MAP or HTML)",
        "",
        "## Strategies",
        "",
        "1. exact:<id> — direct iptv-org channel-ID match",
        "2. alt:<id> — alternate ID match (configured fallback)",
        "3. fuzzy-title — title keyword search (catches ID typos & moved channels)",
        "4. no-match — no streams found by any strategy",
    ]

    with open(REPORT_FILE, "w", encoding="utf-8") as f:
        f.write("\n".join(lines))

    print()
    print("=" * 60)
    print(f"  Updated   : {updated}")
    print(f"  Kept old  : {kept}")
    print(f"  Dead      : {dead}")
    print("=" * 60)

    # GitHub Actions outputs
    gh_out = os.environ.get("GITHUB_OUTPUT")
    if gh_out:
        with open(gh_out, "a") as f:
            f.write(f"updated={updated}\n")
            f.write(f"kept={kept}\n")
            f.write(f"dead={dead}\n")


if __name__ == "__main__":
    main()
