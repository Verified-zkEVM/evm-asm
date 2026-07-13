#!/usr/bin/env bash
# codegen-eest-create-child-frontier-check.sh -- CREATE/CREATE2 child execution EEST frontier.
#
# This wrapper keeps the CREATE child-execution surface visible in the EEST
# stateless harness. It discovers rows through path filters rather than a
# hardcoded fixture list, so new matching CREATE fixtures in future tags are
# selected automatically.
set -euo pipefail

cd "$(dirname "$0")/.."

TAG="${EEST_FIXTURE_TAG:-tests-zkevm@v0.6.1}"
JOBS="${EEST_CREATE_CHILD_JOBS:-${EEST_JOBS:-2}}"
STEPS="${EEST_CREATE_CHILD_STEPS:-${EEST_STEPS:-1000000000}}"
RUN_DIR="${EEST_CREATE_CHILD_RUN_DIR:-gen-out/eest-create-child-frontier}"
FX="${EEST_FIXTURES_DIR:-$(pwd)/gen-out/eest-fixtures/$TAG/fixtures/fixtures}"
SKIP="${EEST_CREATE_CHILD_SKIP:-0}"
LIMIT_OVERRIDE="${EEST_CREATE_CHILD_LIMIT:-}"
MAX_FAILURES="${EEST_CREATE_CHILD_MAX_FAILURES:-1}"
REQUIRE_FULL="${EEST_CREATE_CHILD_REQUIRE_FULL:-0}"
FILTERS=()
EXTRA_ARGS=()

usage() {
  cat <<'USAGE'
Usage:
  scripts/codegen-eest-create-child-frontier-check.sh [options] [-- extra harness args]

Options:
  --filter SUBSTR              add a fixture path substring filter
                               (default: stCreateTest, stCreate2, and EIP-8037 state_gas_create)
  --skip N                     skip first N selected fixtures per filter (default: 0)
  --limit N                    per-filter fixture cap (default: all selected rows after --skip)
  --jobs N|auto                ziskemu jobs (default: $EEST_CREATE_CHILD_JOBS, $EEST_JOBS, or 2)
  --steps N                    ziskemu max steps (default: $EEST_CREATE_CHILD_STEPS, $EEST_STEPS, or 1000000000)
  --max-failures N             stop each filter after N failures in baseline mode (default: 1)
  --require-full               require every selected row in each filter to full-match
  --allow-empty                do not fail if a filter selects no rows
  -h, --help                   show this help

Any arguments after `--` are forwarded to codegen-eest-stateless-check.sh.
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

ALLOW_EMPTY="${EEST_CREATE_CHILD_ALLOW_EMPTY:-0}"

while [[ $# -gt 0 ]]; do
  case "$1" in
    -h|--help) usage; exit 0 ;;
    --filter) require_arg "$1" "${2:-}"; FILTERS+=("$2"); shift 2 ;;
    --skip) require_arg "$1" "${2:-}"; SKIP="$2"; shift 2 ;;
    --limit) require_arg "$1" "${2:-}"; LIMIT_OVERRIDE="$2"; shift 2 ;;
    --jobs) require_arg "$1" "${2:-}"; JOBS="$2"; shift 2 ;;
    --steps) require_arg "$1" "${2:-}"; STEPS="$2"; shift 2 ;;
    --max-failures|--stop-after-failures)
      require_arg "$1" "${2:-}"; MAX_FAILURES="$2"; shift 2 ;;
    --require-full) REQUIRE_FULL=1; shift ;;
    --allow-empty) ALLOW_EMPTY=1; shift ;;
    --) shift; EXTRA_ARGS+=("$@"); break ;;
    *) echo "unknown option: $1" >&2; usage >&2; exit 1 ;;
  esac
done

if ! [[ "$SKIP" =~ ^[0-9]+$ ]]; then
  echo "--skip must be a nonnegative integer (got: $SKIP)" >&2
  exit 1
fi
if [[ -n "$LIMIT_OVERRIDE" ]] && { ! [[ "$LIMIT_OVERRIDE" =~ ^[0-9]+$ ]] || [[ "$LIMIT_OVERRIDE" -lt 1 ]]; }; then
  echo "--limit must be a positive integer when set (got: $LIMIT_OVERRIDE)" >&2
  exit 1
fi
if ! [[ "$MAX_FAILURES" =~ ^[0-9]+$ ]] || [[ "$MAX_FAILURES" -lt 1 ]]; then
  echo "--max-failures must be a positive integer (got: $MAX_FAILURES)" >&2
  exit 1
fi
if [[ "$REQUIRE_FULL" != "0" && "$REQUIRE_FULL" != "1" ]]; then
  echo "EEST_CREATE_CHILD_REQUIRE_FULL must be 0 or 1 (got: $REQUIRE_FULL)" >&2
  exit 1
fi
if [[ "$ALLOW_EMPTY" != "0" && "$ALLOW_EMPTY" != "1" ]]; then
  echo "EEST_CREATE_CHILD_ALLOW_EMPTY must be 0 or 1 (got: $ALLOW_EMPTY)" >&2
  exit 1
fi

if [[ "${#FILTERS[@]}" -eq 0 ]]; then
  if [[ -n "${EEST_CREATE_CHILD_FILTERS:-}" ]]; then
    read -r -a FILTERS <<< "$EEST_CREATE_CHILD_FILTERS"
  else
    FILTERS=(
      "ported_static/stCreateTest"
      "ported_static/stCreate2"
      "eip8037_state_creation_gas_cost_increase/state_gas_create"
    )
  fi
fi

[[ -d "$FX" ]] || { echo "fixtures not found at $FX (run scripts/eest-fetch-fixtures.sh '$TAG')" >&2; exit 1; }

selected_total=0
ran_filters=0

for filter in "${FILTERS[@]}"; do
  safe_filter="$(printf '%s' "$filter" | tr -c 'A-Za-z0-9_.-' '_')"
  count_dir="$(pwd)/gen-out/eest-create-child-count-$safe_filter"
  rm -rf "$count_dir"
  mkdir -p "$count_dir"
  python3 scripts/eest-stateless-to-input.py \
    --fixtures-dir "$FX" \
    --out-dir "$count_dir" \
    --filter "$filter" \
    >/dev/null

  manifest="$count_dir/manifest.tsv"
  if [[ ! -s "$manifest" ]]; then
    if [[ "$ALLOW_EMPTY" == "1" ]]; then
      echo "==> CREATE child frontier filter selected no rows: $filter"
      continue
    fi
    echo "no stateless blocks selected for $filter" >&2
    exit 1
  fi

  count="$(wc -l < "$manifest" | tr -d ' ')"
  if [[ "$SKIP" -ge "$count" ]]; then
    if [[ "$ALLOW_EMPTY" == "1" ]]; then
      echo "==> CREATE child frontier filter skipped all rows: $filter selected=$count skip=$SKIP"
      continue
    fi
    echo "skip $SKIP leaves no rows for $filter (selected $count)" >&2
    exit 1
  fi
  remaining=$((count - SKIP))
  limit="${LIMIT_OVERRIDE:-$remaining}"
  if [[ "$limit" -gt "$remaining" ]]; then
    limit="$remaining"
  fi

  args=(
    --filter "$filter"
    --skip "$SKIP"
    --limit "$limit"
    --jobs "$JOBS"
    --steps "$STEPS"
    --quiet-passes
    --run-dir "$RUN_DIR/$safe_filter"
  )
  if [[ "$REQUIRE_FULL" == "1" ]]; then
    args+=(--min-full "$limit")
  else
    args+=(--max-failures "$MAX_FAILURES")
  fi

  echo "==> CREATE child frontier filter: $filter selected=$count skip=$SKIP limit=$limit require_full=$REQUIRE_FULL"
  scripts/codegen-eest-stateless-check.sh "${args[@]}" "${EXTRA_ARGS[@]}"
  selected_total=$((selected_total + limit))
  ran_filters=$((ran_filters + 1))
done

if [[ "$ran_filters" -eq 0 ]]; then
  echo "no CREATE child frontier filters ran" >&2
  exit 1
fi

echo "==> PASS: CREATE child EEST frontier probe completed filters=$ran_filters selected=$selected_total"
