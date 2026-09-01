#!/usr/bin/env bash
#
# progress-cockpit.sh — stamp the kernel-checked cockpit JSON for the
# GitHub Pages viewer (`docs/index.html` + `docs/cockpit/`).
#
# Modes:
#   scripts/progress-cockpit.sh --write            # docs/cockpit/snapshot.{json,js}
#   scripts/progress-cockpit.sh --write <path>     # write JSON to <path>; JS beside it
#
# The snapshot is a GENERATED ARTIFACT and is NOT committed (#12683): the
# same conflict class as PROGRESS.md. The viewer HTML/CSS/JS are committed
# and count-free. CI (`.github/workflows/progress-cockpit.yml`) writes the
# snapshot into the Pages artifact on every push to main.
#
# Lean emits a deterministic body (`lake exe progress-report cockpit` —
# no date/SHA). This wrapper force-builds MainProgress, then stamps git
# + toolchain pins around that body so the published page can show an
# as-of pill that matches HEAD.
#
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

MODE="${1:-}"
case "$MODE" in
  --write) ;;
  *) echo "usage: $0 --write [output-path]" >&2; exit 2 ;;
esac
OUT="${2:-docs/cockpit/snapshot.json}"

GIT_SHA="$(git rev-parse HEAD)"
GIT_SHORT="$(git rev-parse --short HEAD)"
TODAY="$(date -u +%Y-%m-%d)"
DISPLAY_DATE="$(date -u +'%-d %b %Y' 2>/dev/null || date -u +'%d %b %Y')"
LEAN_TOOLCHAIN="$(cat lean-toolchain)"
BRANCH="$(git branch --show-current 2>/dev/null || echo main)"

LEAN_TMP="$(mktemp)"
STAMPED_TMP="$(mktemp)"
trap 'rm -f "$LEAN_TMP" "$STAMPED_TMP"' EXIT

source "$ROOT/scripts/lib/report-fresh-lean.sh"
report_fresh_lean "$LEAN_TMP" progress-report cockpit

python3 - "$LEAN_TMP" "$STAMPED_TMP" <<PY
import json, sys

src, dst = sys.argv[1], sys.argv[2]
with open(src, encoding="utf-8") as f:
    body = json.load(f)

required = (
    "opcodes", "opcodeCounts", "routineCounts", "routineSymbols",
    "imageCoverage", "obligationCounts", "obligations", "correspondence",
)
missing = [k for k in required if k not in body]
if missing:
    sys.exit(f"progress-cockpit: Lean JSON missing keys: {missing}")

body["date"] = "${TODAY}"
body["displayDate"] = "${DISPLAY_DATE}"
body["sha"] = "${GIT_SHORT}"
body["githubSha"] = "${GIT_SHA}"
body["toolchain"] = "${LEAN_TOOLCHAIN}"
body["branch"] = "${BRANCH}"
body["matchesHead"] = True
body["source"] = (
    "checked-out ${BRANCH} @ HEAD · live Lean registries "
    "(DRIFT.md + Progress/*.lean; PROGRESS.md retired #12683)"
)

with open(dst, "w", encoding="utf-8") as f:
    json.dump(body, f, indent=2, ensure_ascii=False)
    f.write("\n")
PY

mkdir -p "$(dirname "$OUT")"
mv "$STAMPED_TMP" "$OUT"
JS_OUT="${OUT%.json}.js"
if [[ "$JS_OUT" == "$OUT" ]]; then
  JS_OUT="${OUT}.js"
fi
# Script form so `open docs/index.html` (file://) can load the snapshot.
# Browsers block fetch() of local JSON (HTTP status 0).
python3 - "$OUT" "$JS_OUT" <<'PY'
import json, sys
src, js_dst = sys.argv[1], sys.argv[2]
with open(src, encoding="utf-8") as f:
    body = json.load(f)
payload = json.dumps(body, indent=2, ensure_ascii=False).replace("<", "\\u003c")
with open(js_dst, "w", encoding="utf-8") as f:
    f.write("window.__COCKPIT_SNAPSHOT__ = ")
    f.write(payload)
    f.write(";\n")
PY
trap 'rm -f "$LEAN_TMP"' EXIT
echo "Wrote $OUT"
echo "Wrote $JS_OUT"
