#!/usr/bin/env bash
#
# sync_api_data.sh — Downloads API data files (routes, schedules, coordinates)
# only if the remote version is newer than the local one.
#
# Usage:
#   ./scripts/sync_api_data.sh          # sync then optionally build
#   ./scripts/sync_api_data.sh --build  # sync then flutter build apk
#
set -euo pipefail

BASE_URL="https://web-production-2a883c.up.railway.app"
SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROJECT_DIR="$(cd "$SCRIPT_DIR/.." && pwd)"
DATA_DIR="$PROJECT_DIR/assets/data"
VERSION_FILE="$DATA_DIR/.api_version"

mkdir -p "$DATA_DIR"

echo "▶ Checking remote version…"
MANIFEST=$(curl -sf "$BASE_URL/version" 2>/dev/null) || {
  echo "✗ Could not reach API at $BASE_URL/version"
  exit 1
}

REMOTE_VERSION=$(echo "$MANIFEST" | python3 -c "import sys,json; print(json.load(sys.stdin).get('version',0))")
IS_COMPLETE=$(echo "$MANIFEST" | python3 -c "import sys,json; print(json.load(sys.stdin).get('isComplete',False))")

if [ "$IS_COMPLETE" != "True" ]; then
  echo "✗ API data is not complete yet (sync in progress). Skipping."
  exit 0
fi

LOCAL_VERSION=0
if [ -f "$VERSION_FILE" ]; then
  LOCAL_VERSION=$(cat "$VERSION_FILE" 2>/dev/null || echo 0)
fi

echo "  Remote version: $REMOTE_VERSION"
echo "  Local version:  $LOCAL_VERSION"

if [ "$REMOTE_VERSION" -le "$LOCAL_VERSION" ] 2>/dev/null; then
  echo "✓ Data is already up to date."
else
  echo "▶ Downloading routes.json…"
  curl -sf "$BASE_URL/data/routes.json" -o "$DATA_DIR/routes.json"
  echo "  ✓ routes.json ($(du -h "$DATA_DIR/routes.json" | cut -f1))"

  echo "▶ Downloading schedules.json…"
  curl -sf "$BASE_URL/data/schedules.json" -o "$DATA_DIR/schedules.json"
  echo "  ✓ schedules.json ($(du -h "$DATA_DIR/schedules.json" | cut -f1))"

  echo "▶ Downloading coordinates.json…"
  curl -sf "$BASE_URL/data/coordinates.json" -o "$DATA_DIR/coordinates.json"
  echo "  ✓ coordinates.json ($(du -h "$DATA_DIR/coordinates.json" | cut -f1))"

  echo "$REMOTE_VERSION" > "$VERSION_FILE"
  echo "✓ All data downloaded. Version saved: $REMOTE_VERSION"
fi

# Optionally build
if [ "${1:-}" = "--build" ]; then
  echo ""
  echo "▶ Running flutter build apk…"
  cd "$PROJECT_DIR"
  flutter build apk
fi
