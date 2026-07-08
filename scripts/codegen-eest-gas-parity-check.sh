#!/usr/bin/env bash
# codegen-eest-gas-parity-check.sh -- focused EEST gas-sensitive comparison.
#
# Runs a curated set of gas-sensitive stateless EEST filters through the
# RISC-V guest and prints Python execution-spec transaction-gas context for
# successful_validation mismatches. This is a fast triage surface for gas
# parity PRs; it is not meant to replace the broad EEST run.
set -euo pipefail

cd "$(dirname "$0")/.."

TAG="${EEST_FIXTURE_TAG:-tests-zkevm@v0.5.0}"
JOBS="${EEST_GAS_PARITY_JOBS:-${EEST_JOBS:-2}}"
STEPS="${EEST_GAS_PARITY_STEPS:-${EEST_STEPS:-1000000000}}"
LIMIT="${EEST_GAS_PARITY_LIMIT:-1}"
SKIP="${EEST_GAS_PARITY_SKIP:-0}"
MAX_FAILURES="${EEST_GAS_PARITY_MAX_FAILURES:-1}"
RUN_DIR="${EEST_GAS_PARITY_RUN_DIR:-gen-out/eest-gas-parity}"
ALLOW_EMPTY=0
LIST_FILTERS=0
NO_BUILD=0
FILTERS=()

DEFAULT_FILTERS=(
  "eip7778_block_gas_accounting_without_refunds/gas_accounting/multi_transaction_gas_accounting.json"
  "eip8037_state_creation_gas_cost_increase/block_2d_gas_accounting/tx_inclusion_at_regular_gas_block_limit_small.json"
  "eip7825_transaction_gas_limit_cap/tx_gas_limit/maximum_gas_refund.json"
  "stEIP150singleCodeGasPrices/eip2929/eip2929.json"
  "eip7976_increase_calldata_floor_cost/transaction_validity/transaction_validity_type_0.json"
  "ported_static/stCreate2/create2_oo_gafter_init_code.json"
  "eip2929_gas_cost_increases/precompile_warming/precompile_warming.json"
)

usage() {
  cat <<'USAGE'
Usage:
  scripts/codegen-eest-gas-parity-check.sh [options]

Options:
  --filter SUBSTR              add a fixture path substring filter
  --limit N                    per-filter row cap after skip (default: 1)
  --skip N                     per-filter rows to skip (default: 0)
  --jobs N|auto                ziskemu jobs (default: $EEST_GAS_PARITY_JOBS, $EEST_JOBS, or 2)
  --steps N                    ziskemu max steps (default: 1000000000)
  --max-failures N             per-filter FAIL/ERROR stop cap (default: 1)
  --run-dir DIR                output directory (default: gen-out/eest-gas-parity)
  --tag TAG                    EEST fixture tag (default: tests-zkevm@v0.5.0)
  --no-build                   pass --no-build to every inner stateless run
  --allow-empty                skip filters that select no stateless blocks
  --list-filters               print selected filters and exit
  -h, --help                   show this help

Environment:
  EEST_GAS_PARITY_FILTERS      whitespace-separated replacement filter list.
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
    --run-dir) require_arg "$1" "${2:-}"; RUN_DIR="$2"; shift 2 ;;
    --tag) require_arg "$1" "${2:-}"; TAG="$2"; shift 2 ;;
    --no-build) NO_BUILD=1; shift ;;
    --allow-empty) ALLOW_EMPTY=1; shift ;;
    --list-filters) LIST_FILTERS=1; shift ;;
    *) echo "unknown arg: $1" >&2; usage >&2; exit 1 ;;
  esac
done

if [[ "${#FILTERS[@]}" -eq 0 ]]; then
  if [[ -n "${EEST_GAS_PARITY_FILTERS:-}" ]]; then
    read -r -a FILTERS <<< "$EEST_GAS_PARITY_FILTERS"
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

if [[ "$LIST_FILTERS" -eq 1 ]]; then
  printf '%s\n' "${FILTERS[@]}"
  exit 0
fi

FX="${EEST_FIXTURES_DIR:-$(pwd)/gen-out/eest-fixtures/$TAG/fixtures/fixtures}"
[[ -d "$FX" ]] || { echo "fixtures not found at $FX (run scripts/eest-fetch-fixtures.sh '$TAG')" >&2; exit 1; }

mkdir -p "$RUN_DIR"
SUMMARY="$RUN_DIR/gas-parity-summary.tsv"
REPORT="$RUN_DIR/gas-parity-succ-mismatches.tsv"
printf 'filter\tselected\tskip\tlimit\trun_dir\tfull\tfail\terror\tbudget\n' > "$SUMMARY"
printf 'filter\tlabel\tguest_succ\texpected_succ\tcontext\tfixture\n' > "$REPORT"

count_filter() {
  local filter="$1"
  local count_dir
  count_dir="$(pwd)/gen-out/eest-gas-parity-count-$(echo "$filter" | tr -c 'A-Za-z0-9._-' '_')"
  rm -rf "$count_dir"
  mkdir -p "$count_dir"
  python3 scripts/eest-stateless-to-input.py \
    --fixtures-dir "$FX" \
    --out-dir "$count_dir" \
    --filter "$filter" \
    >/dev/null
  local manifest="$count_dir/manifest.tsv"
  if [[ ! -s "$manifest" ]]; then
    echo 0
  else
    wc -l < "$manifest" | tr -d ' '
  fi
}

baseline_value() {
  local baseline="$1"
  local label="$2"
  awk -F: -v label="$label" '$1 ~ label { gsub(/^[ \t]+|[ \t]+$/, "", $2); split($2, a, /[ \t]+/); print a[1]; exit }' "$baseline"
}

ran_filters=0
selected_total=0
first_run=1

for filter in "${FILTERS[@]}"; do
  count="$(count_filter "$filter")"
  if [[ "$count" -eq 0 ]]; then
    if [[ "$ALLOW_EMPTY" -eq 1 ]]; then
      echo "==> gas-parity filter selected 0 row(s), skipping: $filter"
      continue
    fi
    echo "no stateless blocks selected for gas-parity filter: $filter" >&2
    exit 1
  fi
  if [[ "$SKIP" -ge "$count" ]]; then
    if [[ "$ALLOW_EMPTY" -eq 1 ]]; then
      echo "==> gas-parity filter count=$count skip=$SKIP leaves 0 row(s), skipping: $filter"
      continue
    fi
    echo "gas-parity filter count=$count but skip=$SKIP leaves 0 row(s): $filter" >&2
    exit 1
  fi

  remaining=$((count - SKIP))
  run_limit="$LIMIT"
  [[ "$remaining" -lt "$run_limit" ]] && run_limit="$remaining"
  safe_filter="$(echo "$filter" | tr -c 'A-Za-z0-9._-' '_')"
  filter_run_dir="$RUN_DIR/$safe_filter"

  args=(
    --filter "$filter"
    --skip "$SKIP"
    --limit "$run_limit"
    --jobs "$JOBS"
    --quiet-passes
    --max-failures "$MAX_FAILURES"
    --steps "$STEPS"
    --run-dir "$filter_run_dir"
    --tag "$TAG"
  )
  if [[ "$NO_BUILD" -eq 1 || "$first_run" -eq 0 ]]; then
    args+=(--no-build)
  fi

  echo "==> gas-parity filter=$filter count=$count skip=$SKIP limit=$run_limit"
  scripts/codegen-eest-stateless-check.sh "${args[@]}"
  first_run=0

  baseline="$filter_run_dir/eest-baseline.txt"
  full="$(baseline_value "$baseline" "full match")"
  fail="$(baseline_value "$baseline" "fail")"
  err="$(baseline_value "$baseline" "errored")"
  budget="$(baseline_value "$baseline" "budget")"
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
    "$filter" "$count" "$SKIP" "$run_limit" "$filter_run_dir" \
    "${full:-0}" "${fail:-0}" "${err:-0}" "${budget:-0}" >> "$SUMMARY"

  mismatch_tmp="$filter_run_dir/succ-mismatches.tsv"
  manifest_abs="$(cd "$(dirname "$filter_run_dir/manifest.tsv")" && pwd)/manifest.tsv"
  results_abs="$(cd "$filter_run_dir" && pwd)"
  uv run --directory execution-specs --quiet python3 \
    ../scripts/eest-succ-mismatch-report.py \
    --manifest "$manifest_abs" \
    --results-dir "$results_abs" \
    > "$mismatch_tmp"
  awk -v filter="$filter" 'NR > 1 { print filter "\t" $0 }' "$mismatch_tmp" >> "$REPORT"

  ran_filters=$((ran_filters + 1))
  selected_total=$((selected_total + run_limit))
done

if [[ "$ran_filters" -eq 0 ]]; then
  echo "no gas-parity filters ran" >&2
  exit 1
fi

echo "==> wrote gas parity summary: $SUMMARY"
echo "==> wrote gas parity successful_validation mismatch report: $REPORT"
echo "==> PASS: gas-parity focused EEST run completed filters=$ran_filters selected=$selected_total"
