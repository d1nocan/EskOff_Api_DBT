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
    # Build everything + start HTTP server:
    python3 build_all.py --serve

    # Build only, no server:
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
"""

import argparse
import datetime
import hashlib
import json
import math
import os
import sqlite3
import sys
import time
import urllib.parse
import urllib.request
import zipfile
from collections import defaultdict
from concurrent.futures import ThreadPoolExecutor, as_completed
from http.server import HTTPServer, SimpleHTTPRequestHandler
from pathlib import Path
from threading import Lock

# ─── Constants ───────────────────────────────────────────────
# Eskişehir bounding box: (min_lon, min_lat, max_lon, max_lat)
ESK_BBOX = (29.951658, 39.125883, 31.883232, 40.132722)
# Center bbox for high-zoom tiles (z15-16)
CENTER_BBOX = (30.44765, 39.72707, 30.59102, 39.81402)

DEFAULT_TILE_URL = "https://tile.openstreetmap.org/{z}/{x}/{y}.png"
DEFAULT_API_URL  = "https://web-production-2a883c.up.railway.app/routes"

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

def download_overpass(osm_cache=None):
    """Download highway data from Overpass API."""
    min_lon, min_lat, max_lon, max_lat = ESK_BBOX
    overpass_bbox = f"{min_lat},{min_lon},{max_lat},{max_lon}"

    if osm_cache and Path(osm_cache).exists():
        print(f"  Cache: {osm_cache}")
        with open(osm_cache, encoding="utf-8") as f:
            return json.load(f)

    query = f"""
[out:json][timeout:600];
way["highway"]({overpass_bbox});
(._;>;);
out body qt;
""".strip()

    url = "https://overpass-api.de/api/interpreter"
    post_data = urllib.parse.urlencode({"data": query}).encode()
    print(f"  Overpass API'den indiriliyor (BBOX: {overpass_bbox})...")

    req = urllib.request.Request(
        url, data=post_data,
        headers={"User-Agent": "eskoff-geometry-builder/2.0"})

    with urllib.request.urlopen(req, timeout=660) as resp:
        total = int(resp.headers.get("Content-Length", 0))
        chunks = []
        dl = 0
        while True:
            chunk = resp.read(65536)
            if not chunk:
                break
            chunks.append(chunk)
            dl += len(chunk)
            mb = dl / 1024 / 1024
            if total:
                print(f"\r  {mb:.1f}MB / {total / 1024 / 1024:.1f}MB "
                      f"({dl / total * 100:.0f}%)  ", end="", flush=True)
            else:
                print(f"\r  {mb:.1f}MB...  ", end="", flush=True)
        print()

    raw = b"".join(chunks)
    data = json.loads(raw)

    if osm_cache:
        Path(osm_cache).parent.mkdir(parents=True, exist_ok=True)
        with open(osm_cache, "w") as f:
            json.dump(data, f)
        print(f"  Cache yazildi: {osm_cache}")

    return data


def parse_overpass(osm_data):
    """Parse Overpass JSON → (nodes, ways)."""
    nodes = {}
    ways = []
    for elem in osm_data.get("elements", []):
        t = elem.get("type")
        if t == "node":
            lat, lon = float(elem["lat"]), float(elem["lon"])
            if in_bbox(lat, lon):
                nodes[elem["id"]] = (lat, lon)
        elif t == "way":
            tags = elem.get("tags", {})
            hw = tags.get("highway")
            if hw not in HIGHWAY_WEIGHTS:
                continue
            foot = tags.get("foot")
            if foot == "no" and hw not in ("motorway", "motorway_link"):
                continue
            if (tags.get("access") in BLOCKED_ACCESS and foot != "yes"
                    and hw not in ("motorway", "motorway_link")):
                continue
            nids = elem.get("nodes", [])
            if len(nids) < 2:
                continue
            if hw in ALWAYS_BIDI:
                ow = False
            elif hw in ("motorway", "motorway_link"):
                ow = tags.get("oneway", "yes") == "yes"
            else:
                ow = tags.get("oneway", "no") == "yes"
            ways.append((nids, hw, HIGHWAY_WEIGHTS[hw], ow))
    return nodes, ways


def build_graph(conn, nodes, ways):
    """Build road graph with ID remapping."""
    needed = set()
    for nids, _, _, _ in ways:
        needed.update(nids)

    valid = {n: c for n, c in nodes.items() if n in needed}
    print(f"  {len(valid):,} node, {len(ways):,} way")

    # ID remap
    remap = {}
    nodes_data = []
    for lid, (oid, (lat, lon)) in enumerate(valid.items(), 1):
        remap[oid] = lid
        nodes_data.append((lid, lat, lon))

    node_best_hw = {}

    # Write nodes
    conn.execute("BEGIN")
    for i in range(0, len(nodes_data), 100_000):
        conn.executemany("INSERT OR IGNORE INTO nodes VALUES(?,?,?)",
                         nodes_data[i:i + 100_000])
    conn.execute("COMMIT")

    # Build edges
    seen = set()
    batch = []
    skipped = dup = 0
    conn.execute("BEGIN")

    for nids, hw, factor, is_ow in ways:
        for i in range(len(nids) - 1):
            a_osm, b_osm = nids[i], nids[i + 1]
            a, b = remap.get(a_osm), remap.get(b_osm)
            if a is None or b is None:
                skipped += 1
                continue
            la, lo = valid[a_osm]
            lb, lo2 = valid[b_osm]
            dmm = hav_mm(la, lo, lb, lo2)
            wmm = int(dmm * factor)

            penalty = SNAP_PENALTY.get(hw, 99)
            for n in (a, b):
                cur = node_best_hw.get(n)
                if cur is None or penalty < SNAP_PENALTY.get(cur, 99):
                    node_best_hw[n] = hw

            if (a, b) not in seen:
                seen.add((a, b))
                batch.append((a, b, dmm, wmm, 0))
            else:
                dup += 1
            if not is_ow and (b, a) not in seen:
                seen.add((b, a))
                batch.append((b, a, dmm, wmm, 0))
            elif not is_ow:
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
    del seen

    nc = len(nodes_data)
    ec = conn.execute("SELECT COUNT(*) FROM edges").fetchone()[0]
    print(f"  {nc:,} node, {ec:,} edge yazildi")
    return nc, ec, valid, remap, node_best_hw


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


def snap_stops(conn, stops, remap, valid_nodes, node_best_hw):
    """Snap stops to nearest graph nodes with road preference."""
    print(f"  {len(stops)} durak")
    spatial = defaultdict(list)
    graph_coords = {}
    for oid, lid in remap.items():
        lat, lon = valid_nodes[oid]
        graph_coords[lid] = (lat, lon)
        spatial[(round(lat, 3), round(lon, 3))].append(lid)

    def penalty(nid):
        hw = node_best_hw.get(nid)
        return SNAP_PENALTY.get(hw, 30) if hw else 30

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

    # Download OSM data
    print("\n  [DB 1/3] OSM verisi indiriliyor...")
    osm_data = download_overpass(osm_cache)
    nodes, ways = parse_overpass(osm_data)
    del osm_data
    print(f"  {len(nodes):,} node, {len(ways):,} way")

    # Build graph
    print("\n  [DB 2/3] Graf olusturuluyor...")
    if db_path.exists():
        db_path.unlink()

    conn = sqlite3.connect(str(db_path))
    conn.execute("PRAGMA journal_mode=WAL")
    conn.execute("PRAGMA synchronous=NORMAL")
    conn.execute("PRAGMA cache_size=-128000")
    conn.execute("PRAGMA temp_store=MEMORY")
    conn.executescript(DB_SCHEMA)

    nc, ec, valid, remap, nbh = build_graph(conn, nodes, ways)
    del nodes, ways

    # Snap stops
    print("\n  [DB 3/3] Durak snap...")
    stops = load_stops(routes_json, routes_url)
    sc = 0
    if stops:
        sc = snap_stops(conn, stops, remap, valid, nbh)
    else:
        print("  Durak verisi bulunamadi.")

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
    print(f"\n  DB: {nc:,} node, {ec:,} edge, {sc:,} snap — {mb:.1f} MB")
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

    # ── Serve ──
    if args.serve:
        serve_files(output_dir, args.port)


if __name__ == "__main__":
    main()
