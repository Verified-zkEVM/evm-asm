#!/usr/bin/env bash
# oleansize_collect.sh — capture the per-module compiled-artifact (.olean) byte
# size for the EvmAsm tree and merge the top-N largest into lakeprof.topn.json
# under an `olean_sizes` key (report R-F2, proof-SIZE half of the cost trend).
#
# WHY a size metric alongside lakeprof time: build TIME on a shared CI runner is
# noisy (R-F2 keeps it deliberately threshold-free). Compiled-artifact SIZE is
# DETERMINISTIC for a given commit — a proof term that balloons (the n=4
# division proofs are the prime suspects) shows up as a monotone size jump even
# when the wall-clock is too noisy to read. Still trend-only, NEVER a gate, and
# NEVER a reason to bump maxHeartbeats (R-F2 / non-goals).
#
# CAVEAT for whoever reads the trend: `.olean` byte sizes also step-change on a
# `lean-toolchain` bump (new compiler / metadata layout) with ZERO proof change.
# Compare sizes WITHIN a toolchain era, not across one — a jump coinciding with
# a toolchain bump is not proof bloat.
#
# Inputs (env):
#   OLEANSIZE_TOP_N    — how many largest modules to keep (default 30)
#   TOPN_JSON          — lakeprof.topn.json to merge into (default ./lakeprof.topn.json)
#   LAKE_BUILD_LIB     — olean root. Current Lean lays oleans under
#                        .lake/build/lib/lean/EvmAsm (older layouts used
#                        .lake/build/lib/EvmAsm). Default tries the modern path
#                        and falls back to the legacy one.
#
# Pure bash + python3 (for the JSON merge). No network.
set -euo pipefail

TOP_N="${OLEANSIZE_TOP_N:-30}"
TOPN_JSON="${TOPN_JSON:-./lakeprof.topn.json}"
LIB="${LAKE_BUILD_LIB:-}"
if [[ -z "$LIB" ]]; then
  for cand in .lake/build/lib/lean/EvmAsm .lake/build/lib/EvmAsm; do
    [[ -d "$cand" ]] && { LIB="$cand"; break; }
  done
  LIB="${LIB:-.lake/build/lib/lean/EvmAsm}"
fi

if [[ ! -d "$LIB" ]]; then
  echo "oleansize_collect: $LIB not found (build incomplete?); skipping." >&2
  exit 0
fi

# module path (EvmAsm.Foo.Bar) + byte size, largest first, top N.
tmp="$(mktemp)"
# `|| true`: head closes the pipe after N lines, which SIGPIPEs find/sort;
# under `set -o pipefail` that would otherwise abort the script.
find "$LIB" -name '*.olean' -printf '%s\t%p\n' 2>/dev/null \
  | sort -rn | head -n "$TOP_N" > "$tmp" || true

export TMP_LIST="$tmp" TOPN_JSON_ABS="$(readlink -f "$TOPN_JSON" 2>/dev/null || echo "$TOPN_JSON")" TOP_N
python3 - <<'PY'
import json, os
rows = []
with open(os.environ["TMP_LIST"], encoding="utf-8") as f:
    for line in f:
        line = line.rstrip("\n")
        if not line:
            continue
        size, path = line.split("\t", 1)
        # .lake/build/lib/[lean/]EvmAsm/Foo/Bar.olean -> EvmAsm.Foo.Bar
        rel = path.split("/lib/", 1)[-1]
        if rel.startswith("lean/"):          # strip the modern layout segment
            rel = rel[len("lean/"):]
        mod = rel[:-len(".olean")].replace("/", ".") if rel.endswith(".olean") else rel
        rows.append({"module": mod, "bytes": int(size)})

p = os.environ["TOPN_JSON_ABS"]
data = {}
if os.path.exists(p):
    try:
        with open(p, encoding="utf-8") as f:
            data = json.load(f) or {}
    except Exception:
        data = {}
data["olean_sizes"] = rows
with open(p, "w", encoding="utf-8") as f:
    json.dump(data, f, sort_keys=True)
print(f"oleansize_collect: merged {len(rows)} olean sizes into {p}")
PY
rm -f "$tmp"
