#!/usr/bin/env bash
# codegen-eest-warm-cold-bal-visibility-check.sh -- focused warm/cold BAL visibility frontier.
#
# This is a small EEST surface for access-outcome descriptor plumbing. It runs
# representative fixtures that exercise EIP-2929 warm/cold account access and
# precompile warming, then rejects harness ERROR/BUDGET outcomes so descriptor
# plumbing regressions are visible as semantic PASS/FAIL rows.
set -euo pipefail

cd "$(dirname "$0")/.."

TAG="${EEST_FIXTURE_TAG:-zkevm@v0.4.0}"
JOBS="${EEST_WARM_COLD_BAL_JOBS:-${EEST_JOBS:-1}}"
STEPS="${EEST_WARM_COLD_BAL_STEPS:-${EEST_STEPS:-1000000000}}"
LIMIT="${EEST_WARM_COLD_BAL_LIMIT:-1}"
SKIP="${EEST_WARM_COLD_BAL_SKIP:-0}"
MAX_FAILURES="${EEST_WARM_COLD_BAL_MAX_FAILURES:-1}"
RUN_DIR="${EEST_WARM_COLD_BAL_RUN_DIR:-gen-out/eest-warm-cold-bal-visibility}"
MIN_FULL="${EEST_WARM_COLD_BAL_MIN_FULL:-}"
NO_BUILD=0
FILTERS=()

DEFAULT_FILTERS=(
  "eip2929_gas_cost_increases/precompile_warming/precompile_warming.json"
  "stEIP150singleCodeGasPrices/eip2929/eip2929.json"
)

usage() {
  cat <<'USAGE'
Usage:
  scripts/codegen-eest-warm-cold-bal-visibility-check.sh [options]

Options:
  --filter SUBSTR              add a fixture path substring filter
  --limit N                    per-filter row cap after skip (default: 1)
  --skip N                     per-filter rows to skip (default: 0)
  --jobs N|auto                ziskemu jobs (default: $EEST_WARM_COLD_BAL_JOBS, $EEST_JOBS, or 1)
  --steps N                    ziskemu max steps (default: 1000000000)
  --max-failures N             per-filter FAIL/ERROR stop cap (default: 1)
  --min-full N                 require at least N full matches per filter
  --run-dir DIR                output directory
  --tag TAG                    EEST fixture tag (default: zkevm@v0.4.0)
  --no-build                   pass --no-build after the first inner run
  -h, --help                   show this help

Environment:
  EEST_WARM_COLD_BAL_FILTERS   whitespace-separated replacement filter list.
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

is_nonnegative_int() {
  [[ "$1" =~ ^[0-9]+$ ]]
}

is_positive_int() {
  [[ "$1" =~ ^[0-9]+$ && "$1" -gt 0 ]]
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    -h|--help) usage; exit 0 ;;
    --filter) require_arg "$1" "${2:-}"; FILTERS+=("$2"); shift 2 ;;
    --limit) require_arg "$1" "${2:-}"; LIMIT="$2"; shift 2 ;;
    --skip) require_arg "$1" "${2:-}"; SKIP="$2"; shift 2 ;;
    --jobs) require_arg "$1" "${2:-}"; JOBS="$2"; shift 2 ;;
    --steps) require_arg "$1" "${2:-}"; STEPS="$2"; shift 2 ;;
    --max-failures|--stop-after-failures) require_arg "$1" "${2:-}"; MAX_FAILURES="$2"; shift 2 ;;
    --min-full) require_arg "$1" "${2:-}"; MIN_FULL="$2"; shift 2 ;;
    --run-dir) require_arg "$1" "${2:-}"; RUN_DIR="$2"; shift 2 ;;
    --tag) require_arg "$1" "${2:-}"; TAG="$2"; shift 2 ;;
    --no-build) NO_BUILD=1; shift ;;
    *) echo "unknown arg: $1" >&2; usage >&2; exit 1 ;;
  esac
done

if [[ "${#FILTERS[@]}" -eq 0 ]]; then
  if [[ -n "${EEST_WARM_COLD_BAL_FILTERS:-}" ]]; then
    read -r -a FILTERS <<< "$EEST_WARM_COLD_BAL_FILTERS"
  else
    FILTERS=("${DEFAULT_FILTERS[@]}")
  fi
fi

is_nonnegative_int "$SKIP" || { echo "--skip must be a nonnegative integer (got: $SKIP)" >&2; exit 1; }
is_positive_int "$LIMIT" || { echo "--limit must be positive (got: $LIMIT)" >&2; exit 1; }
is_positive_int "$MAX_FAILURES" || { echo "--max-failures must be positive (got: $MAX_FAILURES)" >&2; exit 1; }
if [[ "$JOBS" != "auto" ]] && ! is_positive_int "$JOBS"; then
  echo "--jobs must be a positive integer or auto (got: $JOBS)" >&2
  exit 1
fi
is_positive_int "$STEPS" || { echo "--steps must be positive (got: $STEPS)" >&2; exit 1; }
if [[ -n "$MIN_FULL" ]]; then
  is_positive_int "$MIN_FULL" || { echo "--min-full must be positive (got: $MIN_FULL)" >&2; exit 1; }
fi

FX="${EEST_FIXTURES_DIR:-$(pwd)/gen-out/eest-fixtures/$TAG/fixtures/fixtures}"
[[ -d "$FX" ]] || { echo "fixtures not found at $FX (run scripts/eest-fetch-fixtures.sh '$TAG')" >&2; exit 1; }

mkdir -p "$RUN_DIR"
first=1
summary="$RUN_DIR/warm-cold-bal-visibility.tsv"
printf 'filter\tselected\tran\tfull\tfail\terrored\tbudget\n' >"$summary"

for index in "${!FILTERS[@]}"; do
  filter="${FILTERS[$index]}"
  label="$(printf '%02d-%s' "$index" "$(echo "$filter" | tr '/ .' '---' | tr -cd 'A-Za-z0-9_-')")"
  count_dir="$RUN_DIR/$label-count"
  case_dir="$RUN_DIR/$label"
  rm -rf "$count_dir" "$case_dir"
  mkdir -p "$count_dir" "$case_dir"

  python3 scripts/eest-stateless-to-input.py \
    --fixtures-dir "$FX" \
    --out-dir "$count_dir" \
    --filter "$filter" \
    >/dev/null
  manifest="$count_dir/manifest.tsv"
  [[ -s "$manifest" ]] || { echo "no stateless blocks selected for warm/cold BAL filter: $filter" >&2; exit 1; }

  args=(
    --filter "$filter"
    --skip "$SKIP"
    --limit "$LIMIT"
    --jobs "$JOBS"
    --quiet-passes
    --steps "$STEPS"
    --max-failures "$MAX_FAILURES"
    --run-dir "$case_dir"
  )
  if [[ -n "$MIN_FULL" ]]; then
    args+=(--min-full "$MIN_FULL")
  fi
  if [[ "$NO_BUILD" -eq 1 || "$first" -eq 0 ]]; then
    args+=(--no-build)
  fi

  echo "==> warm/cold BAL visibility filter: $filter"
  scripts/codegen-eest-stateless-check.sh "${args[@]}"
  first=0

  baseline="$case_dir/eest-baseline.txt"
  [[ -s "$baseline" ]] || { echo "missing baseline for filter: $filter" >&2; exit 1; }
  selected="$(awk '/^  selected:/ {print $2}' "$baseline")"
  ran="$(awk '/^  ran:/ {print $2}' "$baseline")"
  full="$(awk '/^  full match:/ {print $3}' "$baseline")"
  fail="$(awk '/^  fail:/ {print $2}' "$baseline")"
  errored="$(awk '/^  errored:/ {print $2}' "$baseline")"
  budget="$(awk '/^  budget:/ {print $2}' "$baseline")"
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$filter" "$selected" "$ran" "$full" "$fail" "$errored" "$budget" >>"$summary"
  if [[ "${errored:-0}" != "0" || "${budget:-0}" != "0" ]]; then
    echo "warm/cold BAL visibility filter produced ERROR/BUDGET rows: $filter" >&2
    exit 1
  fi
done

echo "==> PASS: warm/cold BAL visibility frontier produced semantic outcomes"
echo "    summary: $summary"
