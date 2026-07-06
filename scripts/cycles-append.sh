#!/usr/bin/env bash
#
# cycles-append.sh — append one ziskemu cycle-count datapoint to
# cycles-history.jsonl (report R-F1). This is the ONLY path to validating the
# project's founding "better zkVM performance" claim, which is currently
# entirely unmeasured.
#
# SCHEMA (one JSON object per line; mirrors progress-snapshot.sh's house
# style — git-derived commit/date, pinned EEST tag):
#
#   {
#     "commit":   "<full sha>",          # git rev-parse HEAD (or --ref)
#     "date":     "<ISO-8601 UTC>",
#     "eest_tag": "<scripts/eest-fixture-tag.txt>",
#     "program":  "<logical name, e.g. evm_add | divmod | eest:exp-frontier>",
#     "elf":      "<path to the .elf run, or "">",
#     "steps":    <int|null>,            # executed RISC-V steps (ziskemu -n / step count)
#     "cycles":   <int|null>,            # zkVM cycles if the build reports them
#     "halted":   <true|false|null>,     # did the guest reach a clean halt
#     "source":   "<which script emitted this>"
#   }
#
# `steps`/`cycles` are nullable: ziskemu is NOT yet wired here (no working
# emulator in this environment), so the LIVE PARSE is DEFERRED. Two ways to
# populate them:
#   (a) explicitly:  --steps N [--cycles M]   (a caller that already knows)
#   (b) from a log:  --from-log <file>        (greps ZISKEMU_STEP_COUNT_RE /
#                                              ZISKEMU_CYCLE_COUNT_RE — phrasing
#                                              configurable per ziskemu build)
# If neither yields a number, the record is still appended with null, so the
# schema + history file exist and codegen scripts can start emitting now;
# back-fill the parse once a ziskemu build is available.
#
# DEFERRED WIRING (honest scope — landed: schema + this appender; NOT yet
# landed): (1) no codegen-*.sh calls this yet (no working ziskemu); (2)
# cycles-history.jsonl is written to the WORKING TREE and is .gitignored — there
# is no persistence to an orphan branch yet, so export-metrics.yml currently
# finds it empty. When ziskemu lands, mirror the benchmark-history orphan-branch
# pattern (.github/workflows/benchmark.yml) to persist + a caller to populate.
#
# Usage:
#   scripts/cycles-append.sh --program evm_add --steps 1234 [--cycles N] \
#       [--elf gen-out/evm_add.elf] [--halted true] [--source codegen-evm_add-check.sh]
#   scripts/cycles-append.sh --program divmod --from-log ziskemu.log
#   scripts/cycles-append.sh --program X --print   # print record to stdout, do NOT append
#
# Deps: jq, git. POSIX/bash.

set -uo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

HISTORY="cycles-history.jsonl"
PROGRAM=""
ELF=""
STEPS=""
CYCLES=""
HALTED=""
SOURCE=""
FROM_LOG=""
PRINT_ONLY=0
REF=""

# ziskemu step/cycle phrasing — override per emulator build (see --from-log).
STEP_RE="${ZISKEMU_STEP_COUNT_RE:-(executed|ran|total)?[^0-9]*([0-9][0-9,_]*)[[:space:]]*steps?\b|steps?[[:space:]]*[:=][[:space:]]*([0-9][0-9,_]*)}"
CYCLE_RE="${ZISKEMU_CYCLE_COUNT_RE:-cycles?[[:space:]]*[:=]?[[:space:]]*([0-9][0-9,_]*)}"

while [[ $# -gt 0 ]]; do
  case "$1" in
    --program) PROGRAM="$2"; shift 2 ;;
    --elf) ELF="$2"; shift 2 ;;
    --steps) STEPS="$2"; shift 2 ;;
    --cycles) CYCLES="$2"; shift 2 ;;
    --halted) HALTED="$2"; shift 2 ;;
    --source) SOURCE="$2"; shift 2 ;;
    --from-log) FROM_LOG="$2"; shift 2 ;;
    --ref) REF="$2"; shift 2 ;;
    --print) PRINT_ONLY=1; shift ;;
    *) echo "usage: $0 --program <name> [--steps N|--from-log f] [--cycles N] [--elf p] [--halted b] [--source s] [--print]" >&2; exit 2 ;;
  esac
done

if [[ -z "$PROGRAM" ]]; then
  echo "cycles-append: --program is required" >&2; exit 2
fi
command -v jq >/dev/null 2>&1 || { echo "cycles-append: jq required" >&2; exit 2; }

# Normalize direct numeric args (strip thousands separators) so `--steps 1,234`
# and `--steps 1_234` behave like the --from-log path (which already strips).
STEPS="${STEPS//[,_]/}"
CYCLES="${CYCLES//[,_]/}"

# ---- best-effort numeric extraction from a ziskemu log ----------------
# The default STEP_RE/CYCLE_RE assume DECIMAL counts. ziskemu's real output
# format is unverified (no emulator this session); when it lands, calibrate the
# overridable ZISKEMU_*_COUNT_RE env vars to the actual phrasing (incl. hex like
# `0x1F4` if used — the decimal default would misparse it). Deferred with D8.
extract() { # <regex> <file>  -> first numeric capture (commas/underscores stripped)
  local re="$1" file="$2"
  [[ -f "$file" ]] || return 1
  grep -ioE "$re" "$file" 2>/dev/null | grep -oE '[0-9][0-9,_]*' | tail -1 | tr -d ',_'
}
if [[ -n "$FROM_LOG" ]]; then
  [[ -z "$STEPS"  ]] && STEPS="$(extract "$STEP_RE"  "$FROM_LOG" || true)"
  [[ -z "$CYCLES" ]] && CYCLES="$(extract "$CYCLE_RE" "$FROM_LOG" || true)"
  if [[ -z "$STEPS" && -z "$CYCLES" ]]; then
    echo "cycles-append: no step/cycle count parsed from $FROM_LOG (ziskemu live-parse deferred); recording nulls." >&2
  fi
fi

# ---- git-derived identity (house style) -------------------------------
if [[ -n "$REF" ]]; then COMMIT="$(git rev-parse "$REF" 2>/dev/null || echo "$REF")"; else COMMIT="$(git rev-parse HEAD 2>/dev/null || echo unknown)"; fi
DATE="$(date -u +%Y-%m-%dT%H:%M:%SZ)"
EEST_TAG="$(tr -d ' \n' < scripts/eest-fixture-tag.txt 2>/dev/null || echo unknown)"
[[ -z "$EEST_TAG" ]] && EEST_TAG="unknown"

jnum() { [[ "$1" =~ ^[0-9]+$ ]] && printf '%s' "$1" || printf 'null'; }
jbool() { case "$1" in true) printf 'true' ;; false) printf 'false' ;; *) printf 'null' ;; esac; }

REC="$(jq -cn \
  --arg commit "$COMMIT" --arg date "$DATE" --arg eest "$EEST_TAG" \
  --arg program "$PROGRAM" --arg elf "$ELF" --arg source "${SOURCE:-cycles-append.sh}" \
  --argjson steps "$(jnum "${STEPS:-}")" --argjson cycles "$(jnum "${CYCLES:-}")" \
  --argjson halted "$(jbool "${HALTED:-}")" \
  '{commit:$commit, date:$date, eest_tag:$eest, program:$program, elf:$elf, steps:$steps, cycles:$cycles, halted:$halted, source:$source}')"

if (( PRINT_ONLY )); then
  printf '%s\n' "$REC"
  exit 0
fi

printf '%s\n' "$REC" >> "$HISTORY"
echo "cycles-append: appended to $HISTORY -> $REC"
exit 0
