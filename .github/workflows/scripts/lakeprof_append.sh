#!/usr/bin/env bash
# Append a lakeprof top-N record to the benchmark-history orphan branch.
#
# Record construction remains lakeprof-specific; the shared
# orphan-history-append.sh owns clone/checkout/append/retry mechanics.
#
# Inputs (env):
#   GITHUB_TOKEN      — write-capable token for the repo
#   GITHUB_REPOSITORY — owner/repo (set by Actions)
#   GITHUB_SHA        — commit benchmarked
#   GITHUB_REF        — branch / ref triggering the run
#   GITHUB_RUN_ID     — run ID
#   GITHUB_EVENT_NAME — event ('schedule' / 'workflow_dispatch')
#   LAKEPROF_TOPN_JSON — path to lakeprof.topn.json (default: ./lakeprof.topn.json)
#
# The record's `kind` field distinguishes lakeprof entries from the
# build (wall+RSS) records appended by the sibling `benchmark` job.
# Existing pre-#949-followup records have neither key; consumers default
# to `"build"` when absent (per docs/949-lakeprof-design.md §5).

set -euo pipefail

TOPN_JSON="${LAKEPROF_TOPN_JSON:-./lakeprof.topn.json}"

if [ ! -f "$TOPN_JSON" ]; then
  echo "lakeprof_append: $TOPN_JSON not found, skipping history append" >&2
  exit 0
fi

tmpdir="$(mktemp -d)"
trap 'rm -rf "$tmpdir"' EXIT
export TOPN_JSON_ABS="$(readlink -f "$TOPN_JSON")"
export TIMESTAMP="$(date -u +%Y-%m-%dT%H:%M:%SZ)"
record="$tmpdir/lakeprof-record.jsonl"
python3 - "$record" <<'PY'
import json, os
with open(os.environ["TOPN_JSON_ABS"], "r", encoding="utf-8") as f:
    _doc = json.load(f)
topn = _doc.get("top_modules") or []
olean_sizes = _doc.get("olean_sizes") or []   # merged by oleansize_collect.sh (R-F2); [] if absent
rec = {
    "kind":         "lakeprof",
    "commit":       os.environ["GITHUB_SHA"],
    "ref":          os.environ["GITHUB_REF"],
    "timestamp":    os.environ["TIMESTAMP"],
    "trigger":      os.environ["GITHUB_EVENT_NAME"],
    "run_id":       os.environ["GITHUB_RUN_ID"],
    "top_modules":  topn,
    "olean_sizes":  olean_sizes,
}
with open(__import__("sys").argv[1], "w", encoding="utf-8") as f:
    f.write(json.dumps(rec, sort_keys=True) + "\n")
PY
top_count="$(python3 -c 'import json,os; print(len(json.load(open(os.environ["TOPN_JSON_ABS"])).get("top_modules") or []))')"
helper="$(cd "$(dirname "$0")" && pwd)/orphan-history-append.sh"
"$helper" \
  --branch benchmark-history \
  --history-file history.jsonl \
  --record-file "$record" \
  --message "lakeprof: ${GITHUB_SHA::12} top=${top_count}"
