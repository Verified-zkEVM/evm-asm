#!/usr/bin/env bash
# eest-run-monitor.sh -- summarize a running codegen-eest-stateless-check run.
#
# Usage:
#   scripts/eest-run-monitor.sh [--pid PID] [--interval SEC] [--once] [RUN_DIR]
#
# If RUN_DIR is omitted, the newest gen-out/eest-run/run-* directory is used.
# The monitor prints compact progress, result classification, ziskemu RSS, and
# optional parent-process liveness. It is read-only and safe to run while a test
# script is still writing result files.
set -euo pipefail

cd "$(dirname "$0")/.."

PID=""
INTERVAL=10
ONCE=0
RUN_DIR=""

usage() {
  cat <<'USAGE'
Usage:
  scripts/eest-run-monitor.sh [options] [RUN_DIR]

Options:
  --pid PID          parent test-script PID to watch for liveness
  --interval SEC     seconds between updates (default 10)
  --once             print one snapshot and exit
  -h, --help         show this help
USAGE
}

require_arg() {
  local opt="$1"
  if [[ $# -lt 2 || -z "${2:-}" ]]; then
    echo "$opt requires an argument" >&2
    usage >&2
    exit 1
  fi
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    -h|--help) usage; exit 0 ;;
    --pid) require_arg "$1" "${2:-}"; PID="$2"; shift 2 ;;
    --interval) require_arg "$1" "${2:-}"; INTERVAL="$2"; shift 2 ;;
    --once) ONCE=1; shift ;;
    *)
      if [[ -n "$RUN_DIR" ]]; then
        echo "unexpected argument: $1" >&2
        usage >&2
        exit 1
      fi
      RUN_DIR="$1"
      shift
      ;;
  esac
done

if [[ -n "$PID" && ! "$PID" =~ ^[0-9]+$ ]]; then
  echo "--pid must be numeric (got: $PID)" >&2
  exit 1
fi
if ! [[ "$INTERVAL" =~ ^[0-9]+$ ]] || [[ "$INTERVAL" -lt 1 ]]; then
  echo "--interval must be a positive integer (got: $INTERVAL)" >&2
  exit 1
fi

if [[ -z "$RUN_DIR" ]]; then
  RUN_DIR="$(find gen-out/eest-run -maxdepth 1 -type d -name 'run-*' 2>/dev/null | sort | tail -n 1 || true)"
fi
if [[ -z "$RUN_DIR" || ! -d "$RUN_DIR" ]]; then
  echo "run directory not found: ${RUN_DIR:-<latest>}" >&2
  exit 1
fi

MANIFEST="$RUN_DIR/manifest.tsv"

snapshot() {
  local now selected completed ok err full succ root tail fail rod running note
  now="$(date -u '+%Y-%m-%dT%H:%M:%SZ')"
  selected=0
  [[ -f "$MANIFEST" ]] && selected="$(wc -l < "$MANIFEST" | tr -d ' ')"
  completed="$(find "$RUN_DIR" -maxdepth 1 -name '*.result.tsv' 2>/dev/null | wc -l | tr -d ' ')"
  running="$(pgrep -fc "ziskemu .*${RUN_DIR}" || true)"
  note=""
  if [[ -n "$PID" ]]; then
    if kill -0 "$PID" 2>/dev/null; then
      note="parent=alive"
    else
      note="parent=exited"
    fi
  fi

  read -r ok err full succ root tail fail rod < <(
    awk -F '\t' '
      BEGIN { ok=err=full=succ=root=tail=fail=rod=0 }
      FNR==NR {
        expected_by_label[$1] = substr($3, 1, 210)
        rel[$1] = $7
        next
      }
      {
        label = FILENAME
        sub(/^.*\//, "", label)
        sub(/\.result\.tsv$/, "", label)
        if ($1 != "OK") { err++; next }
        ok++
        actual = $2
        expected = expected_by_label[label]
        r = (substr(actual, 1, 64) == substr(expected, 1, 64))
        s = (substr(actual, 65, 2) == substr(expected, 65, 2))
        t = (substr(actual, 67, 144) == substr(expected, 67, 144))
        if (r) root++
        if (s) succ++
        if (t) tail++
        if (actual == expected) full++
        else {
          fail++
          if (!r && s && t) rod++
        }
      }
      END { print ok, err, full, succ, root, tail, fail, rod }
    ' "$MANIFEST" "$RUN_DIR"/*.result.tsv 2>/dev/null || echo "0 0 0 0 0 0 0 0"
  )

  printf '%s run=%s selected=%s completed=%s ok=%s err=%s full=%s succ=%s root=%s tail=%s fail=%s root_only=%s ziskemu=%s %s\n' \
    "$now" "$RUN_DIR" "$selected" "$completed" "$ok" "$err" "$full" "$succ" "$root" "$tail" "$fail" "$rod" "$running" "$note"

  ps -o pid,ppid,rss,comm,args -C ziskemu 2>/dev/null \
    | awk -v run="$RUN_DIR" 'NR == 1 || index($0, run) { print "  " $0 }'
}

while true; do
  snapshot
  [[ "$ONCE" -eq 1 ]] && exit 0
  if [[ -n "$PID" ]] && ! kill -0 "$PID" 2>/dev/null; then
    exit 0
  fi
  sleep "$INTERVAL"
done
