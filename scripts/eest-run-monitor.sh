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
  # Count in-flight workers for EITHER backend. Two bugs were fixed here:
  #  * matching only `ziskemu` reported 0 for Spike-backed runs, and Spike is
  #    the normal full-corpus backend — so the column read "nothing running"
  #    for exactly the runs where it mattered most;
  #  * `pgrep -f '<backend> .*RUN_DIR'` OVER-counts, because the harness's
  #    per-case `bash` wrappers carry the backend name and the run dir in their
  #    own command lines too (observed 53 matches for 22 real workers).
  # So: select on the process NAME (-C, same list as the `ps` block below) and
  # filter on the run dir appearing in the args.
  running="$(ps -o comm=,args= -C ziskemu -C spike -C spike_run 2>/dev/null \
    | awk -v run="$RUN_DIR" 'index($0, run) { n++ } END { print n+0 }')"
  note=""
  if [[ -n "$PID" ]]; then
    if kill -0 "$PID" 2>/dev/null; then
      note="parent=alive"
    else
      note="parent=exited"
    fi
  fi

  # The result-file list is STREAMED on stdin (NUL-separated) and each file is
  # opened by awk via getline. It must never be passed as argv: a full-corpus
  # run dir holds tens of thousands of files (72,393 observed for a
  # 26,104-fixture sweep), which exceeds ARG_MAX, so `awk … "$RUN_DIR"/*` never
  # execs. That failure USED to fall through to `echo "0 0 0 …"`, printing
  # `fail=0` — a broken instrument that reads as a clean sweep. It also
  # degraded silently *as a run progressed*: correct while few files existed,
  # all-zero once the count crossed the limit.
  #
  # The fallback now emits `ERR` per field rather than zeros, and stderr is NOT
  # suppressed, so a failure is unmistakable and its cause is visible.
  read -r ok err full succ root tail fail rod < <(
    # `-print` (newline-separated), NOT `-print0`: `RS` is global in awk, so a
    # NUL record separator would also apply to the `getline < file` reads below,
    # making each whole file a single record — which silently mis-parses the
    # manifest into one giant record and yields wrong counts rather than an
    # error. Result-file names are harness-generated (`<label>.result.tsv`) and
    # contain no newlines, so newline separation is safe here.
    find "$RUN_DIR" -maxdepth 1 -name '*.result.tsv' -print \
    | awk -v manifest="$MANIFEST" '
      BEGIN {
        ok=err=full=succ=root=tail=fail=rod=0
        while ((getline mline < manifest) > 0) {
          n = split(mline, mc, "\t")
          if (n >= 3) expected_by_label[mc[1]] = substr(mc[3], 1, 210)
        }
        close(manifest)
      }
      {
        path = $0
        if (path == "") next
        label = path
        sub(/^.*\//, "", label)
        sub(/\.result\.tsv$/, "", label)
        if ((getline rline < path) <= 0) { close(path); next }
        close(path)
        split(rline, rf, "\t")
        if (rf[1] != "OK") { err++; next }
        ok++
        actual = rf[2]
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
    ' || echo "ERR ERR ERR ERR ERR ERR ERR ERR"
  )

  # `workers=` rather than `ziskemu=`: the column counts either backend now, and
  # a backend-specific label invited the same Spike-blind misreading the count
  # itself had.
  printf '%s run=%s selected=%s completed=%s ok=%s err=%s full=%s succ=%s root=%s tail=%s fail=%s root_only=%s workers=%s %s\n' \
    "$now" "$RUN_DIR" "$selected" "$completed" "$ok" "$err" "$full" "$succ" "$root" "$tail" "$fail" "$rod" "$running" "$note"

  ps -o pid,ppid,rss,comm,args -C ziskemu -C spike -C spike_run 2>/dev/null \
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
