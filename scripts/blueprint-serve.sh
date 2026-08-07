#!/usr/bin/env bash
# scripts/blueprint-serve.sh — serve the built blueprint website locally.
#
# The dependency-graph page (dep_graph_document.html) draws itself with
# client-side JavaScript that browsers refuse to run from file:// URLs,
# so the site must be served over HTTP. This serves blueprint/web on
# localhost and opens the dependency graph in the default browser.
#
# Usage:
#   scripts/blueprint-serve.sh [port]   # default port 8123
#
# Rebuild the site first with scripts/blueprint.sh if it is stale.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" >/dev/null 2>&1 && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/.." >/dev/null 2>&1 && pwd)"
PORT="${1:-8123}"
WEB_DIR="$REPO_ROOT/blueprint/web"

if [ ! -f "$WEB_DIR/index.html" ]; then
  echo "blueprint/web not built yet — run scripts/blueprint.sh first." >&2
  exit 1
fi

echo "Serving $WEB_DIR at http://localhost:$PORT (Ctrl-C to stop)"
# Open the dependency graph once the server is up (macOS `open`).
( sleep 1; open "http://localhost:$PORT/dep_graph_document.html" ) &
exec python3 -m http.server "$PORT" -d "$WEB_DIR"
