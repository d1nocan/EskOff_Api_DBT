#!/usr/bin/env python3
"""
build_all.py — Build & serve eskoff offline assets (standalone, Railway-ready).

Generates files in --output-dir (default: ./output/):
  1. tiles.zip       — Offline map tiles (PNG, z7-z16) as ZIP
  2. geometries.db   — Road graph for Dijkstra routing
  3. manifest.json   — File manifest with sizes + SHA256 checksums

The Flutter app downloads these via HTTP and imports them:
  - tiles.zip      → EskoffStorage.extractTilesZip()
  - geometries.db  → RoadGraphService.loadFromFile()

NO Flutter project dependencies. Does not touch assets/ or pubspec.yaml.
Zero external dependencies — uses only Python 3.8+ stdlib.

Usage:
    # Build everything + upload to S3 bucket:
    python3 build_all.py --upload

    # Build + upload + start HTTP server:
    python3 build_all.py --upload --serve

    # Build only, no upload or server:
    python3 build_all.py

    # Only tiles or db:
    python3 build_all.py --only tiles
    python3 build_all.py --only db

    # Serve existing files (skip build):
    python3 build_all.py --serve-only

    # Custom output dir / port:
    python3 build_all.py --output-dir /data --port 3000 --serve

    # Cache Overpass data (faster re-runs):
    python3 build_all.py --osm-cache /tmp/eskisehir_osm.json

    Environment variables for S3 upload (--upload):
      S3_ENDPOINT     — S3-compatible endpoint URL
      S3_BUCKET       — Bucket name
      S3_ACCESS_KEY   — Access Key ID
      S3_SECRET_KEY   — Secret Access Key
      S3_REGION       — Region (default: auto)
"""

import argparse
import datetime
import gc
import hashlib
import hmac
import json
import math
import os
import resource
import shutil
import socket
import sqlite3
import sys
import tempfile
import time
import urllib.parse
import urllib.request
import xml.sax
import xml.sax.handler
import zipfile
from collections import defaultdict
from concurrent.futures import ThreadPoolExecutor, as_completed
from http.server import HTTPServer, SimpleHTTPRequestHandler
from pathlib import Path
from threading import Lock, Thread

# ─── Constants ───────────────────────────────────────────────
# Eskişehir bounding box: (min_lon, min_lat, max_lon, max_lat)
ESK_BBOX = (29.951658, 39.125883, 31.883232, 40.132722)
# Center bbox for high-zoom tiles (z15-16)
CENTER_BBOX = (30.44765, 39.72707, 30.59102, 39.81402)

DEFAULT_TILE_URL = "https://tile.openstreetmap.org/{z}/{x}/{y}.png"
DEFAULT_API_URL  = "https://web-production-2a883c.up.railway.app/data/routes.json"

# Tile zoom config: (bbox, min_zoom, max_zoom)
TILE_ZONES = [
    (ESK_BBOX,    7, 14),   # Wide area: overview to street level
    (CENTER_BBOX, 15, 16),  # City center: high zoom detail
]

# ─── Highway weight factors (for geometries.db) ─────────────
HIGHWAY_WEIGHTS = {
    "motorway": 0.8,  "motorway_link": 0.8,
    "trunk": 1.1,     "trunk_link": 8.0,
    "primary": 1.0,   "primary_link": 5.0,
    "secondary": 1.0, "secondary_link": 3.0,
    "tertiary": 1.0,  "tertiary_link": 1.5,
    "unclassified": 1.0, "residential": 1.0,
    "living_street": 0.9, "service": 1.0,
    "pedestrian": 0.85, "footway": 0.85,
    "cycleway": 0.9,    "corridor": 0.9,
    "track": 1.2, "path": 1.1, "steps": 1.4, "road": 1.0,
}
ALWAYS_BIDI = {"footway", "path", "pedestrian", "steps", "corridor", "cycleway"}
BLOCKED_ACCESS = {"no", "private", "customers", "delivery", "agricultural"}
SNAP_PENALTY = {
    "trunk": 0, "primary": 0, "secondary": 5, "tertiary": 10,
    "unclassified": 15, "residential": 15, "living_street": 20,
    "service": 20, "road": 15,
    "trunk_link": 50, "primary_link": 50, "secondary_link": 30,
    "tertiary_link": 20,
    "pedestrian": 40, "footway": 40, "cycleway": 40, "corridor": 40,
    "track": 30, "path": 30, "steps": 50,
    "motorway": 60, "motorway_link": 60,
}

DB_SCHEMA = """
CREATE TABLE IF NOT EXISTS metadata(key TEXT PRIMARY KEY, value TEXT);
CREATE TABLE IF NOT EXISTS nodes(
    id  INTEGER PRIMARY KEY, lat REAL NOT NULL, lon REAL NOT NULL);
CREATE TABLE IF NOT EXISTS edges(
    from_node INTEGER NOT NULL, to_node INTEGER NOT NULL,
    dist_mm INTEGER NOT NULL, weight_mm INTEGER NOT NULL,
    edge_type INTEGER NOT NULL DEFAULT 0);
CREATE TABLE IF NOT EXISTS stop_nodes(
    stop_id INTEGER PRIMARY KEY, node_id INTEGER NOT NULL,
    snap_dist_m REAL NOT NULL, lat REAL NOT NULL, lon REAL NOT NULL);
CREATE INDEX IF NOT EXISTS idx_edges_from ON edges(from_node);
CREATE INDEX IF NOT EXISTS idx_nodes_lat  ON nodes(lat);
CREATE INDEX IF NOT EXISTS idx_nodes_lon  ON nodes(lon);
"""


# ═════════════════════════════════════════════════════════════
#  HELPERS
# ═════════════════════════════════════════════════════════════

def fmt_dur(sec):
    h, r = divmod(int(sec), 3600)
    m, s = divmod(r, 60)
    if h: return f"{h}h {m}m {s}s"
    if m: return f"{m}m {s}s"
    return f"{s}s"


def fmt_size(size_bytes):
    if size_bytes >= 1024 * 1024:
        return f"{size_bytes / 1024 / 1024:.1f} MB"
    if size_bytes >= 1024:
        return f"{size_bytes / 1024:.1f} KB"
    return f"{size_bytes} B"


def hav_mm(la1, lo1, la2, lo2):
    R = 6_371_000_000.0
    p = math.pi / 180
    a = (math.sin((la2 - la1) * p / 2) ** 2 +
         math.cos(la1 * p) * math.cos(la2 * p) *
         math.sin((lo2 - lo1) * p / 2) ** 2)
    return int(2 * R * math.atan2(math.sqrt(a), math.sqrt(1 - a)))


def hav_m(la1, lo1, la2, lo2):
    R = 6_371_000.0
    p = math.pi / 180
    a = (math.sin((la2 - la1) * p / 2) ** 2 +
         math.cos(la1 * p) * math.cos(la2 * p) *
         math.sin((lo2 - lo1) * p / 2) ** 2)
    return 2 * R * math.atan2(math.sqrt(a), math.sqrt(1 - a))


def lon2x(lon, z):
    return int((lon + 180.0) / 360.0 * (2 ** z))


def lat2y(lat, z):
    lat_rad = math.radians(lat)
    return int((1.0 - math.log(math.tan(lat_rad) + 1.0 / math.cos(lat_rad))
                / math.pi) / 2.0 * (2 ** z))


def in_bbox(lat, lon):
    return (ESK_BBOX[1] <= lat <= ESK_BBOX[3] and
            ESK_BBOX[0] <= lon <= ESK_BBOX[2])


# ═════════════════════════════════════════════════════════════
#  PART 1: TILE DOWNLOAD → ZIP
# ═════════════════════════════════════════════════════════════

def compute_tile_list():
    """Compute all (z, x, y) tiles to download."""
    tiles = []
    for (bbox, z_min, z_max) in TILE_ZONES:
        min_lon, min_lat, max_lon, max_lat = bbox
        for z in range(z_min, z_max + 1):
            x_min = lon2x(min_lon, z)
            x_max = lon2x(max_lon, z)
            y_min = lat2y(max_lat, z)  # note: y is inverted
            y_max = lat2y(min_lat, z)
            for x in range(min(x_min, x_max), max(x_min, x_max) + 1):
                for y in range(min(y_min, y_max), max(y_min, y_max) + 1):
                    tiles.append((z, x, y))
    return tiles


def download_tile(z, x, y, tile_url, retries=3):
    """Download a single tile. Returns (success, z, x, y, png_bytes)."""
    url = tile_url.format(z=z, x=x, y=y)
    for attempt in range(retries):
        try:
            req = urllib.request.Request(
                url, headers={
                    "User-Agent": "eskoff-tile-builder/2.0 "
                                  "(transit app, one-time bulk download)",
                })
            with urllib.request.urlopen(req, timeout=30) as resp:
                data = resp.read()
                if data and len(data) > 100:  # skip blank tiles
                    return True, z, x, y, data
            return False, z, x, y, None
        except Exception:
            if attempt < retries - 1:
                time.sleep(1.0 * (attempt + 1))
    return False, z, x, y, None


def build_tiles_zip(output_dir, tile_url, parallel=4):
    """Download tiles and package directly into a ZIP file."""
    print(f"\n{'─' * 50}")
    print(f"  HARITA TILE'LARI → tiles.zip")
    print(f"{'─' * 50}")
    t0 = time.time()

    tiles = compute_tile_list()
    total = len(tiles)
    zip_path = output_dir / "tiles.zip"

    print(f"  {total:,} tile hesaplandi")
    print(f"  Kaynak: {tile_url}")
    print(f"  Cikti:  {zip_path}")
    print(f"  {total:,} tile indirilecek ({parallel} paralel)...")

    downloaded = 0
    failed = 0
    lock = Lock()

    with zipfile.ZipFile(str(zip_path), "w", zipfile.ZIP_STORED) as zf:
        def _on_result(ok, z, x, y, data):
            nonlocal downloaded, failed
            if ok and data:
                # ZIP entry: {z}/{x}/{y}.png — app's extractTilesZip auto-detects this
                entry = f"{z}/{x}/{y}.png"
                with lock:
                    zf.writestr(entry, data)
                    downloaded += 1
            else:
                with lock:
                    failed += 1

            with lock:
                done = downloaded + failed
                if done % 200 == 0 or done == total:
                    pct = done / total * 100
                    print(f"\r  {done:,}/{total:,} ({pct:.0f}%)  ",
                          end="", flush=True)

        with ThreadPoolExecutor(max_workers=parallel) as pool:
            futures = {
                pool.submit(download_tile, z, x, y, tile_url): (z, x, y)
                for z, x, y in tiles
            }
            for future in as_completed(futures):
                ok, z, x, y, data = future.result()
                _on_result(ok, z, x, y, data)

    print()
    zip_size = zip_path.stat().st_size
    print(f"  {downloaded:,} tile indirildi, {failed} basarisiz")
    print(f"  ZIP: {fmt_size(zip_size)}")
    print(f"  Sure: {fmt_dur(time.time() - t0)}")
    return downloaded, zip_size


# ═════════════════════════════════════════════════════════════
#  PART 2: GEOMETRIES.DB (road graph)
# ═════════════════════════════════════════════════════════════

class _OSMSAXHandler(xml.sax.handler.ContentHandler):
    """SAX handler: streams OSM XML, builds nodes dict + filtered ways list.

    Memory-efficient: never holds the full XML document in memory.
    Only retains the final nodes {} and ways [] structures.
    """

    def __init__(self):
        super().__init__()
        self.nodes = {}   # osm_id → (lat, lon)
        self.ways = []    # list of (nids, hw_str, weight, is_oneway)
        self._in_way = False
        self._way_nids = []
        self._way_tags = {}

    def startElement(self, name, attrs):
        if name == "node":
            try:
                lat = float(attrs["lat"])
                lon = float(attrs["lon"])
                if in_bbox(lat, lon):
                    self.nodes[int(attrs["id"])] = (lat, lon)
            except (KeyError, ValueError):
                pass
        elif name == "way":
            self._in_way = True
            self._way_nids = []
            self._way_tags = {}
        elif name == "nd" and self._in_way:
            try:
                self._way_nids.append(int(attrs["ref"]))
            except (KeyError, ValueError):
                pass
        elif name == "tag" and self._in_way:
            try:
                self._way_tags[attrs["k"]] = attrs["v"]
            except KeyError:
                pass

    def endElement(self, name):
        if name != "way" or not self._in_way:
            return
        self._in_way = False
        tags = self._way_tags
        hw = tags.get("highway")
        if hw not in HIGHWAY_WEIGHTS:
            return
        foot = tags.get("foot")
        if foot == "no" and hw not in ("motorway", "motorway_link"):
            return
        if (tags.get("access") in BLOCKED_ACCESS and foot != "yes"
                and hw not in ("motorway", "motorway_link")):
            return
        nids = self._way_nids
        if len(nids) < 2:
            return
        if hw in ALWAYS_BIDI:
            ow = False
        elif hw in ("motorway", "motorway_link"):
            ow = tags.get("oneway", "yes") == "yes"
        else:
            ow = tags.get("oneway", "no") == "yes"
        self.ways.append((nids, hw, HIGHWAY_WEIGHTS[hw], ow))


def download_and_parse_overpass(osm_cache=None):
    """Download OSM XML and stream-parse with SAX (low memory).

    Instead of loading the full JSON into memory (~200-400 MB Python dicts),
    this streams the response to a temp file and SAX-parses it element by
    element, keeping only the final nodes dict + filtered ways list (~60 MB).
    """
    min_lon, min_lat, max_lon, max_lat = ESK_BBOX
    overpass_bbox = f"{min_lat},{min_lon},{max_lat},{max_lon}"

    # ── Cache hit ──
    if osm_cache and Path(osm_cache).exists():
        print(f"  Cache: {osm_cache}")
        handler = _OSMSAXHandler()
        try:
            xml.sax.parse(osm_cache, handler)
            return handler.nodes, handler.ways
        except xml.sax.SAXParseException:
            print(f"  Cache XML degil, yeniden indiriliyor...")

    # ── Download (XML format — no [out:json]) ──
    query = f"""
[timeout:600];
way["highway"]({overpass_bbox});
(._;>;);
out body qt;
""".strip()

    overpass_urls = [
        "https://overpass-api.de/api/interpreter",
        "https://overpass.kumi.systems/api/interpreter",
        "https://maps.mail.ru/osm/tools/overpass/api/interpreter",
    ]
    post_data = urllib.parse.urlencode({"data": query}).encode()

    tmp_fd, tmp_path = tempfile.mkstemp(suffix=".osm")
    os.close(tmp_fd)  # we'll reopen per attempt

    max_retries = 5
    for attempt in range(1, max_retries + 1):
        api_url = overpass_urls[(attempt - 1) % len(overpass_urls)]
        print(f"  [{attempt}/{max_retries}] Indiriliyor: {api_url.split('//')[1].split('/')[0]}...")
        try:
            req = urllib.request.Request(
                api_url, data=post_data,
                headers={"User-Agent": "eskoff-geometry-builder/2.0"})

            # Per-read timeout via default socket timeout (restored after)
            old_timeout = socket.getdefaulttimeout()
            socket.setdefaulttimeout(120)  # 120s per read op
            try:
                resp = urllib.request.urlopen(req, timeout=660)
            finally:
                socket.setdefaulttimeout(old_timeout)

            total = int(resp.headers.get("Content-Length", 0))
            dl = 0
            with open(tmp_path, "wb") as tmp:
                while True:
                    # Each read() inherits socket timeout from connection
                    chunk = resp.read(65536)
                    if not chunk:
                        break
                    tmp.write(chunk)
                    dl += len(chunk)
                    mb = dl / 1024 / 1024
                    if total:
                        print(f"\r  {mb:.1f}MB / {total/1024/1024:.1f}MB "
                              f"({dl/total*100:.0f}%)  ",
                              end="", flush=True)
                    else:
                        print(f"\r  {mb:.1f}MB...  ", end="", flush=True)
            resp.close()
            print()

            # Verify XML completeness: must end with </osm>
            with open(tmp_path, "rb") as f:
                f.seek(max(0, os.path.getsize(tmp_path) - 128))
                tail = f.read()
            if b"</osm>" not in tail:
                raise ValueError(
                    f"Eksik XML ({dl/1024/1024:.1f}MB) — </osm> bulunamadi")

            print(f"  Indirme tamam: {dl/1024/1024:.1f}MB")
            break  # success

        except Exception as e:
            print(f"\n  Deneme {attempt} basarisiz: {e}")
            if attempt < max_retries:
                wait = 15 * attempt
                print(f"  {wait}s beklenip tekrar denenecek...")
                time.sleep(wait)
            else:
                raise RuntimeError(
                    f"Overpass indirmesi {max_retries} denemede basarisiz") from e

    try:
        # Save to cache (copy temp file before parsing)
        if osm_cache:
            Path(osm_cache).parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(tmp_path, osm_cache)
            print(f"  Cache yazildi: {osm_cache}")

        # ── SAX parse (streaming, ~60 MB peak) ──
        print(f"  XML parse ediliyor (SAX streaming)...")
        handler = _OSMSAXHandler()
        xml.sax.parse(tmp_path, handler)
        return handler.nodes, handler.ways
    finally:
        if os.path.exists(tmp_path):
            os.unlink(tmp_path)


def build_graph(conn, nodes, ways):
    """Build road graph with ID remapping. Memory-optimized.

    Optimizations vs original:
    - No 'valid' dict copy — uses 'nodes' directly
    - No 'nodes_data' list — writes to DB during remap loop
    - Packed 'seen' set (single int) instead of tuple pairs (~75 MB savings)
    - Stores penalty values (int) instead of highway strings (~20 MB savings)
    """
    needed = set()
    for nids, _, _, _ in ways:
        needed.update(nids)

    # Remap IDs and write nodes directly to DB (no intermediate list)
    remap = {}
    lid = 0
    batch = []
    conn.execute("BEGIN")
    for oid in needed:
        coord = nodes.get(oid)
        if coord is None:
            continue
        lid += 1
        remap[oid] = lid
        batch.append((lid, coord[0], coord[1]))
        if len(batch) >= 100_000:
            conn.executemany("INSERT OR IGNORE INTO nodes VALUES(?,?,?)", batch)
            batch.clear()
    if batch:
        conn.executemany("INSERT OR IGNORE INTO nodes VALUES(?,?,?)", batch)
        batch.clear()
    conn.execute("COMMIT")
    del needed
    gc.collect()

    node_count = lid
    print(f"  {node_count:,} node, {len(ways):,} way")

    # Pack edge key into single int for compact seen-set
    id_shift = max(20, node_count.bit_length())
    node_best_penalty = {}   # remapped_id → int penalty value

    # Build edges
    seen = set()
    batch = []
    skipped = dup = 0
    conn.execute("BEGIN")

    for nids, hw, factor, is_ow in ways:
        penalty = SNAP_PENALTY.get(hw, 99)
        for i in range(len(nids) - 1):
            a_osm, b_osm = nids[i], nids[i + 1]
            a, b = remap.get(a_osm), remap.get(b_osm)
            if a is None or b is None:
                skipped += 1
                continue
            la, lo = nodes[a_osm]
            lb, lo2 = nodes[b_osm]
            dmm = hav_mm(la, lo, lb, lo2)
            wmm = int(dmm * factor)

            for n in (a, b):
                cur = node_best_penalty.get(n)
                if cur is None or penalty < cur:
                    node_best_penalty[n] = penalty

            key_ab = (a << id_shift) | b
            if key_ab not in seen:
                seen.add(key_ab)
                batch.append((a, b, dmm, wmm, 0))
            else:
                dup += 1
            if not is_ow:
                key_ba = (b << id_shift) | a
                if key_ba not in seen:
                    seen.add(key_ba)
                    batch.append((b, a, dmm, wmm, 0))
                else:
                    dup += 1

            if len(batch) >= 100_000:
                conn.executemany(
                    "INSERT INTO edges(from_node,to_node,dist_mm,weight_mm,"
                    "edge_type) VALUES(?,?,?,?,?)", batch)
                batch.clear()

    if batch:
        conn.executemany(
            "INSERT INTO edges(from_node,to_node,dist_mm,weight_mm,"
            "edge_type) VALUES(?,?,?,?,?)", batch)
    conn.execute("COMMIT")
    del seen, batch
    gc.collect()

    ec = conn.execute("SELECT COUNT(*) FROM edges").fetchone()[0]
    print(f"  {node_count:,} node, {ec:,} edge yazildi")
    return node_count, ec, remap, node_best_penalty


def load_stops(routes_json=None, routes_url=None):
    """Load stop coordinates from routes.json (API or local file)."""
    data = None
    if routes_json and Path(routes_json).exists():
        print(f"  Dosya: {routes_json}")
        with open(routes_json, encoding="utf-8") as f:
            data = json.load(f)
    elif routes_url:
        print(f"  URL: {routes_url}")
        req = urllib.request.Request(
            routes_url,
            headers={"User-Agent": "eskoff-geometry-builder/2.0"})
        with urllib.request.urlopen(req, timeout=60) as resp:
            data = json.loads(resp.read())
    else:
        # Default: fetch from Railway API
        print(f"  URL: {DEFAULT_API_URL}")
        try:
            req = urllib.request.Request(
                DEFAULT_API_URL,
                headers={"User-Agent": "eskoff-geometry-builder/2.0"})
            with urllib.request.urlopen(req, timeout=60) as resp:
                data = json.loads(resp.read())
        except Exception as e:
            print(f"  API hatasi: {e}")
            return {}

    if data is None:
        return {}

    rd = data.get("data") or data
    stops = {}
    for rv in rd.values():
        if not isinstance(rv, dict):
            continue
        for d in rv.get("duraklar") or []:
            sid = d.get("StopId") or d.get("id") or d.get("stopId")
            try:
                sid = int(sid)
            except (TypeError, ValueError):
                continue
            lat = d.get("Latitude") or d.get("lat") or d.get("y")
            lon = d.get("Longitude") or d.get("lon") or d.get("x") \
                  or d.get("lng")
            if lat is None:
                pts = d.get("p") or []
                if pts:
                    lat = pts[0].get("y") or pts[0].get("lat")
                    lon = pts[0].get("x") or pts[0].get("lon")
            try:
                lat, lon = float(lat), float(lon)
            except (TypeError, ValueError):
                continue
            stops[sid] = (lat, lon)
    return stops


def snap_stops(conn, stops, remap, nodes, node_best_penalty):
    """Snap stops to nearest graph nodes with road preference."""
    print(f"  {len(stops)} durak")
    spatial = defaultdict(list)
    graph_coords = {}
    for oid, lid in remap.items():
        coord = nodes.get(oid)
        if coord is None:
            continue
        lat, lon = coord
        graph_coords[lid] = (lat, lon)
        spatial[(round(lat, 3), round(lon, 3))].append(lid)

    def penalty(nid):
        return node_best_penalty.get(nid, 30)

    conn.execute("BEGIN")
    conn.execute("DELETE FROM stop_nodes")
    ok = fail = 0
    td = 0.0
    for sid, (slat, slon) in stops.items():
        best_nid, best_sc, best_d = None, float("inf"), 0.0
        bl, bo = round(slat, 3), round(slon, 3)
        for dl in range(-5, 6):
            for dn in range(-5, 6):
                key = (round(bl + dl * 0.001, 3), round(bo + dn * 0.001, 3))
                for nid in spatial.get(key, []):
                    nlat, nlon = graph_coords[nid]
                    d = hav_m(slat, slon, nlat, nlon)
                    if d > 500:
                        continue
                    sc = d + penalty(nid)
                    if sc < best_sc:
                        best_sc, best_nid, best_d = sc, nid, d
        if best_nid is not None:
            nlat, nlon = graph_coords[best_nid]
            conn.execute("INSERT OR REPLACE INTO stop_nodes VALUES(?,?,?,?,?)",
                         (sid, best_nid, best_d, nlat, nlon))
            ok += 1
            td += best_d
        else:
            fail += 1
    conn.execute("COMMIT")
    avg = td / ok if ok else 0
    print(f"  Snap: {ok} tamam, {fail} basarisiz, ort. {avg:.1f}m")
    return ok


def build_geometries_db(output_dir, routes_json, routes_url, osm_cache):
    """Build the complete geometries.db."""
    print(f"\n{'─' * 50}")
    print(f"  GEOMETRIES.DB")
    print(f"{'─' * 50}")

    t0 = time.time()
    db_path = output_dir / "geometries.db"

    # Download + parse OSM data (XML + SAX streaming — low memory)
    print("\n  [DB 1/3] OSM verisi indiriliyor...")
    nodes, ways = download_and_parse_overpass(osm_cache)
    gc.collect()
    print(f"  {len(nodes):,} node, {len(ways):,} way")

    # Build graph
    print("\n  [DB 2/3] Graf olusturuluyor...")
    if db_path.exists():
        db_path.unlink()

    conn = sqlite3.connect(str(db_path))
    conn.execute("PRAGMA journal_mode=WAL")
    conn.execute("PRAGMA synchronous=NORMAL")
    conn.execute("PRAGMA cache_size=-64000")
    conn.execute("PRAGMA temp_store=FILE")
    conn.executescript(DB_SCHEMA)

    nc, ec, remap, nbp = build_graph(conn, nodes, ways)
    del ways
    gc.collect()

    # Snap stops
    print("\n  [DB 3/3] Durak snap...")
    stops = load_stops(routes_json, routes_url)
    sc = 0
    if stops:
        sc = snap_stops(conn, stops, remap, nodes, nbp)
    else:
        print("  Durak verisi bulunamadi.")
    del nodes, remap, nbp
    gc.collect()

    conn.executemany("INSERT OR REPLACE INTO metadata VALUES(?,?)", [
        ("built_at", datetime.datetime.now(datetime.timezone.utc).isoformat()),
        ("source", "overpass-api"),
        ("bbox", ",".join(str(x) for x in ESK_BBOX)),
        ("node_count", str(nc)),
        ("edge_count", str(ec)),
        ("stop_count", str(sc)),
        ("dist_unit", "millimeter"),
        ("id_remapped", "true"),
        ("builder_version", "2.0"),
    ])
    conn.commit()
    conn.execute("VACUUM")
    conn.close()

    db_size = db_path.stat().st_size
    mb = db_size / 1024 / 1024
    peak_mb = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss / 1024
    print(f"\n  DB: {nc:,} node, {ec:,} edge, {sc:,} snap — {mb:.1f} MB")
    print(f"  Peak RAM: {peak_mb:.0f} MB")
    print(f"  Sure: {fmt_dur(time.time() - t0)}")
    return nc, ec, sc, db_size


# ═════════════════════════════════════════════════════════════
#  PART 3: MANIFEST + HTTP SERVER
# ═════════════════════════════════════════════════════════════

def make_manifest(output_dir):
    """Generate manifest.json with file sizes and SHA256 checksums."""
    manifest = {
        "built_at": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "files": {},
    }
    for f in sorted(output_dir.iterdir()):
        if f.is_file() and f.name != "manifest.json":
            size = f.stat().st_size
            sha = hashlib.sha256(f.read_bytes()).hexdigest()
            manifest["files"][f.name] = {
                "size": size,
                "size_human": fmt_size(size),
                "sha256": sha,
            }
    mpath = output_dir / "manifest.json"
    mpath.write_text(json.dumps(manifest, indent=2))
    print(f"  manifest.json yazildi")
    return manifest


# ═════════════════════════════════════════════════════════════
#  PART 3: S3-COMPATIBLE BUCKET UPLOAD
# ═════════════════════════════════════════════════════════════

def _sign_key(key, date_stamp, region, service):
    """Derive AWS Signature V4 signing key."""
    k_date = hmac.new(("AWS4" + key).encode(), date_stamp.encode(), hashlib.sha256).digest()
    k_region = hmac.new(k_date, region.encode(), hashlib.sha256).digest()
    k_service = hmac.new(k_region, service.encode(), hashlib.sha256).digest()
    return hmac.new(k_service, b"aws4_request", hashlib.sha256).digest()


def s3_upload_file(file_path, object_key, endpoint, bucket, access_key,
                   secret_key, region="auto"):
    """Upload a file to S3-compatible bucket using AWS Signature V4."""
    file_data = Path(file_path).read_bytes()
    content_sha = hashlib.sha256(file_data).hexdigest()

    # Parse endpoint
    parsed = urllib.parse.urlparse(endpoint)
    host = parsed.hostname
    scheme = parsed.scheme
    port_str = f":{parsed.port}" if parsed.port and parsed.port not in (80, 443) else ""
    host_header = f"{host}{port_str}"

    # Determine content type
    ext = Path(object_key).suffix.lower()
    content_types = {
        ".json": "application/json",
        ".db": "application/octet-stream",
        ".zip": "application/zip",
    }
    content_type = content_types.get(ext, "application/octet-stream")

    # Timestamps
    now = datetime.datetime.now(datetime.timezone.utc)
    amz_date = now.strftime("%Y%m%dT%H%M%SZ")
    date_stamp = now.strftime("%Y%m%d")

    # Canonical request
    uri = f"/{bucket}/{object_key}"
    canonical_qs = ""
    signed_headers = "content-type;host;x-amz-content-sha256;x-amz-date"
    canonical_headers = (
        f"content-type:{content_type}\n"
        f"host:{host_header}\n"
        f"x-amz-content-sha256:{content_sha}\n"
        f"x-amz-date:{amz_date}\n"
    )
    canonical_request = (
        f"PUT\n{uri}\n{canonical_qs}\n{canonical_headers}\n"
        f"{signed_headers}\n{content_sha}"
    )

    # String to sign
    scope = f"{date_stamp}/{region}/s3/aws4_request"
    canon_hash = hashlib.sha256(canonical_request.encode()).hexdigest()
    string_to_sign = f"AWS4-HMAC-SHA256\n{amz_date}\n{scope}\n{canon_hash}"

    # Signature
    signing_key = _sign_key(secret_key, date_stamp, region, "s3")
    signature = hmac.new(signing_key, string_to_sign.encode(),
                         hashlib.sha256).hexdigest()

    auth = (f"AWS4-HMAC-SHA256 Credential={access_key}/{scope}, "
            f"SignedHeaders={signed_headers}, Signature={signature}")

    url = f"{scheme}://{host_header}{uri}"
    req = urllib.request.Request(url, data=file_data, method="PUT")
    req.add_header("Content-Type", content_type)
    req.add_header("Host", host_header)
    req.add_header("x-amz-content-sha256", content_sha)
    req.add_header("x-amz-date", amz_date)
    req.add_header("Authorization", auth)
    req.add_header("x-amz-acl", "public-read")

    with urllib.request.urlopen(req, timeout=300) as resp:
        return resp.status


def upload_to_bucket(output_dir):
    """Upload all output files to S3-compatible bucket.

    Reads credentials from environment variables:
      S3_ENDPOINT, S3_BUCKET, S3_ACCESS_KEY, S3_SECRET_KEY, S3_REGION
    """
    endpoint = os.environ.get("S3_ENDPOINT", "").rstrip("/")
    bucket = os.environ.get("S3_BUCKET", "")
    access_key = os.environ.get("S3_ACCESS_KEY", "")
    secret_key = os.environ.get("S3_SECRET_KEY", "")
    region = os.environ.get("S3_REGION", "auto")

    if not all([endpoint, bucket, access_key, secret_key]):
        print("  HATA: S3 env degiskenleri eksik!")
        print("  Gerekli: S3_ENDPOINT, S3_BUCKET, S3_ACCESS_KEY, S3_SECRET_KEY")
        return False

    print(f"\n{'─' * 50}")
    print(f"  BUCKET UPLOAD")
    print(f"{'─' * 50}")
    print(f"  Endpoint: {endpoint}")
    print(f"  Bucket:   {bucket}")
    print(f"  Region:   {region}")

    files = [f for f in sorted(output_dir.iterdir()) if f.is_file()]
    ok = fail = 0

    for f in files:
        size = f.stat().st_size
        print(f"  Yukleniyor: {f.name} ({fmt_size(size)})...", end=" ", flush=True)
        try:
            status = s3_upload_file(
                f, f.name, endpoint, bucket, access_key, secret_key, region)
            print(f"OK ({status})")
            ok += 1
        except Exception as e:
            print(f"HATA: {e}")
            fail += 1

    print(f"\n  Upload: {ok} basarili, {fail} basarisiz")
    if ok > 0:
        print(f"  URL ornegi: {endpoint}/{bucket}/{files[0].name}")
    return fail == 0


# ═════════════════════════════════════════════════════════════
#  PART 4: MANIFEST + HTTP SERVER
# ═════════════════════════════════════════════════════════════

class CORSHandler(SimpleHTTPRequestHandler):
    """HTTP handler with CORS headers for cross-origin app access."""

    def __init__(self, *args, directory=None, **kwargs):
        super().__init__(*args, directory=directory, **kwargs)

    def end_headers(self):
        self.send_header("Access-Control-Allow-Origin", "*")
        self.send_header("Access-Control-Allow-Methods", "GET, HEAD, OPTIONS")
        self.send_header("Access-Control-Allow-Headers", "*")
        super().end_headers()

    def do_OPTIONS(self):
        self.send_response(200)
        self.end_headers()

    def log_message(self, format, *args):
        print(f"  [{self.log_date_time_string()}] {format % args}")


def serve_files(output_dir, port):
    """Start HTTP file server on 0.0.0.0:port."""
    serve_dir = str(output_dir)
    handler = lambda *a, **kw: CORSHandler(*a, directory=serve_dir, **kw)
    server = HTTPServer(("0.0.0.0", port), handler)

    print(f"\n{'=' * 58}")
    print(f"  HTTP Server baslatildi")
    print(f"  Port: {port}")
    print(f"  Dizin: {output_dir}")
    print(f"{'─' * 58}")
    for f in sorted(output_dir.iterdir()):
        if f.is_file():
            print(f"  GET /{f.name}  ({fmt_size(f.stat().st_size)})")
    print(f"{'=' * 58}")
    print(f"  Ctrl+C ile durdur\n")

    try:
        server.serve_forever()
    except KeyboardInterrupt:
        print("\n  Server durduruluyor...")
        server.shutdown()


# ═════════════════════════════════════════════════════════════
#  MAIN
# ═════════════════════════════════════════════════════════════

def main():
    parser = argparse.ArgumentParser(
        description="Build & serve eskoff offline assets (tiles.zip + geometries.db)")
    parser.add_argument("--output-dir", default="./output",
                        help="Output directory (default: ./output)")
    parser.add_argument("--only", choices=["tiles", "db"],
                        help="Build only tiles or only db")
    parser.add_argument("--tile-url", default=DEFAULT_TILE_URL,
                        help="Tile server URL template (default: OSM)")
    parser.add_argument("--parallel", type=int, default=4,
                        help="Parallel tile downloads (default: 4)")
    parser.add_argument("--routes-json", default=None,
                        help="Path to routes.json for stop snapping")
    parser.add_argument("--routes-url", default=None,
                        help="URL to fetch routes from")
    parser.add_argument("--osm-cache", default=None,
                        help="Cache Overpass JSON for faster re-runs")
    parser.add_argument("--upload", action="store_true",
                        help="Upload output files to S3 bucket (needs S3_* env vars)")
    parser.add_argument("--serve", action="store_true",
                        help="Start HTTP server after build")
    parser.add_argument("--serve-only", action="store_true",
                        help="Only serve existing files, skip build")
    parser.add_argument("--port", type=int,
                        default=int(os.environ.get("PORT", "8080")),
                        help="Server port (default: PORT env or 8080)")
    args = parser.parse_args()

    output_dir = Path(args.output_dir).resolve()
    output_dir.mkdir(parents=True, exist_ok=True)

    # ── Serve only mode ──
    if args.serve_only:
        print("=" * 58)
        print("  eskoff Asset Server")
        print("=" * 58)
        make_manifest(output_dir)
        serve_files(output_dir, args.port)
        return

    # ── If --serve, start HTTP server immediately so Railway sees the port ──
    if args.serve:
        serve_dir = str(output_dir)
        handler = lambda *a, **kw: CORSHandler(*a, directory=serve_dir, **kw)
        server = HTTPServer(("0.0.0.0", args.port), handler)
        srv_thread = Thread(target=server.serve_forever, daemon=True)
        srv_thread.start()
        print(f"  HTTP Server baslatildi (port {args.port}) — build arka planda baslayacak")

    # ── Build mode ──
    print("=" * 58)
    print("  eskoff Asset Builder v2.0")
    print(f"  Tarih:  {datetime.datetime.now().strftime('%Y-%m-%d %H:%M')}")
    print(f"  Hedef:  {args.only or 'tiles + db'}")
    print(f"  Cikti:  {output_dir}")
    print("=" * 58)

    t0 = time.time()

    # ── Tiles → ZIP ──
    tile_count = 0
    tile_size = 0
    if args.only != "db":
        tile_count, tile_size = build_tiles_zip(
            output_dir, args.tile_url, args.parallel)

    # ── geometries.db ──
    nc = ec = sc = 0
    db_size = 0
    if args.only != "tiles":
        nc, ec, sc, db_size = build_geometries_db(
            output_dir, args.routes_json, args.routes_url, args.osm_cache)

    # ── Manifest ──
    print(f"\n  Manifest olusturuluyor...")
    make_manifest(output_dir)

    # ── Summary ──
    total_size = tile_size + db_size
    elapsed = time.time() - t0

    print(f"\n{'=' * 58}")
    print(f"  TAMAMLANDI — {fmt_dur(elapsed)}")
    print(f"{'─' * 58}")
    if args.only != "db":
        print(f"  tiles.zip:      {tile_count:,} tile ({fmt_size(tile_size)})")
    if args.only != "tiles":
        print(f"  geometries.db:  {nc:,} node, {ec:,} edge, {sc:,} snap ({fmt_size(db_size)})")
    print(f"  Toplam:         {fmt_size(total_size)}")
    print(f"  Cikti:          {output_dir}")
    print(f"{'=' * 58}")

    # ── Upload ──
    if args.upload:
        upload_to_bucket(output_dir)

    # ── Serve (block main thread if server is running) ──
    if args.serve:
        print(f"\n  HTTP Server dinliyor: 0.0.0.0:{args.port}")
        print(f"  Ctrl+C ile durdur\n")
        try:
            srv_thread.join()
        except KeyboardInterrupt:
            print("\n  Server durduruluyor...")
            server.shutdown()


if __name__ == "__main__":
    main()
