#!/usr/bin/env bash
# Persist validated cycles-history records on the cycles-history orphan branch.
#
# The producer intentionally appends to the ignored working-tree file while a
# run is in progress.  This command is the serialized hand-off to durable
# storage; it delegates clone/initialize/retry mechanics to the shared
# orphan-history helper used by the other history workflows.

set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

RECORD_FILE="${CYCLES_HISTORY_RECORD_FILE:-$ROOT/cycles-history.jsonl}"
BRANCH="cycles-history"
HISTORY_FILE="cycles-history.jsonl"
ORIGIN_URL="${HISTORY_ORIGIN_URL:-}"
COMMIT_REF="${CYCLES_HISTORY_COMMIT_REF:-HEAD}"
COMMIT="$(git rev-parse "$COMMIT_REF" 2>/dev/null || printf '%s' "$COMMIT_REF")"

usage() {
  cat <<'USAGE'
Usage: scripts/cycles-history-persist.sh [--record-file PATH] [--origin URL]

Environment:
  CYCLES_HISTORY_RECORD_FILE  local JSONL file (default: cycles-history.jsonl)
  CYCLES_HISTORY_COMMIT_REF   commit recorded in the producer (default: HEAD)
  HISTORY_ORIGIN_URL           local/test remote URL; CI defaults to GitHub
USAGE
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    --record-file)
      [[ $# -ge 2 && -n "${2:-}" ]] || { echo "--record-file requires a path" >&2; exit 2; }
      RECORD_FILE="$2"; shift 2 ;;
    --origin)
      [[ $# -ge 2 && -n "${2:-}" ]] || { echo "--origin requires a URL" >&2; exit 2; }
      ORIGIN_URL="$2"; shift 2 ;;
    -h|--help) usage; exit 0 ;;
    *) echo "unknown argument: $1" >&2; usage >&2; exit 2 ;;
  esac
done

[[ -r "$RECORD_FILE" ]] || { echo "cycles-history: record file is not readable: $RECORD_FILE" >&2; exit 2; }
[[ "$BRANCH" == cycles-history ]] || { echo "cycles-history: branch must be cycles-history" >&2; exit 2; }
[[ "$HISTORY_FILE" == cycles-history.jsonl ]] || { echo "cycles-history: file must be cycles-history.jsonl" >&2; exit 2; }

command -v jq >/dev/null 2>&1 || { echo "cycles-history: jq is required" >&2; exit 2; }
record_count="$(jq -s -e '
  length > 0 and all(.[];
    type == "object" and
    (.steps | type == "number") and
    (.halted == true))
' "$RECORD_FILE" >/dev/null && awk 'NF { n++ } END { print n + 0 }' "$RECORD_FILE")" || {
  echo "cycles-history: every non-empty record must be an object with numeric steps and halted=true" >&2
  exit 2
}

readme="$ROOT/.cycles-history-README.tmp"
trap 'rm -f "$readme"' EXIT
cat > "$readme" <<'README'
# cycles-history

Append-only consumed-step datapoints from the Spike EEST stateless-guest
producer (`scripts/codegen-eest-stateless-check.sh --append-cycles`).

One JSON object per line in `cycles-history.jsonl`:

- `commit`, `date`, `eest_tag`: source and fixture provenance
- `program`, `elf`: logical case and guest artifact path
- `steps`: exact retired RISC-V instructions from Spike's `minstret`
- `cycles`: nullable zkVM-cycle field (not emitted by Spike)
- `halted`: clean-halt marker; persisted records must be `true`
- `source`: producer script

The branch is performance history only, not a conformance or verification
signal.
README

helper="$ROOT/.github/workflows/scripts/orphan-history-append.sh"
[[ -x "$helper" ]] || { echo "cycles-history: missing helper: $helper" >&2; exit 2; }
args=(
  --branch "$BRANCH"
  --history-file "$HISTORY_FILE"
  --record-file "$RECORD_FILE"
  --readme-file "$readme"
  --message "cycles: ${COMMIT:0:12} append ${record_count} Spike datapoint(s)"
)
[[ -n "$ORIGIN_URL" ]] && args+=(--origin "$ORIGIN_URL")
"$helper" "${args[@]}"
