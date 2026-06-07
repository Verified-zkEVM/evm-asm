#!/usr/bin/env bash
# codegen-eest-bls12-pairing-map-frontier-check.sh -- BLS12 pairing/map EEST frontier.
#
# The default filters target the EIP-2537 pairing, map-Fp-to-G1, and
# map-Fp2-to-G2 fixture families. Counts are discovered from the active
# fixture tag so newly generated matching rows are included automatically
# instead of pinning a fixed skip/limit window.
set -euo pipefail

cd "$(dirname "$0")/.."

TAG="${EEST_FIXTURE_TAG:-zkevm@v0.4.0}"
JOBS="${EEST_BLS12_PAIRING_MAP_JOBS:-${EEST_JOBS:-2}}"
STEPS="${EEST_BLS12_PAIRING_MAP_STEPS:-${EEST_STEPS:-1000000000}}"
RUN_DIR="${EEST_BLS12_PAIRING_MAP_RUN_DIR:-gen-out/eest-bls12-pairing-map-frontier}"
FX="${EEST_FIXTURES_DIR:-$(pwd)/gen-out/eest-fixtures/$TAG/fixtures/fixtures}"
SKIP="${EEST_BLS12_PAIRING_MAP_SKIP:-0}"
LIMIT_OVERRIDE="${EEST_BLS12_PAIRING_MAP_LIMIT:-}"
MAX_FAILURES="${EEST_BLS12_PAIRING_MAP_MAX_FAILURES:-1}"
REQUIRE_FULL="${EEST_BLS12_PAIRING_MAP_REQUIRE_FULL:-0}"
ALLOW_EMPTY="${EEST_BLS12_PAIRING_MAP_ALLOW_EMPTY:-0}"
FILTERS=()
EXTRA_ARGS=()

usage() {
  cat <<'USAGE'
Usage:
  scripts/codegen-eest-bls12-pairing-map-frontier-check.sh [options] [-- extra harness args]

Options:
  --filter SUBSTR              add a fixture path substring filter
                               (default: bls12_pairing,
                               bls12_map_fp_to_g1, and
                               bls12_map_fp2_to_g2, or words from
                               $EEST_BLS12_PAIRING_MAP_FILTERS)
  --skip N                     skip first N selected rows per filter (default: 0)
  --limit N                    per-filter row cap after skip (default: all selected)
  --jobs N|auto                ziskemu jobs (default:
                               $EEST_BLS12_PAIRING_MAP_JOBS, $EEST_JOBS, or 2)
  --steps N                    ziskemu max steps (default: 1000000000)
  --max-failures N             stop each filter after N FAIL/ERROR rows (default: 1)
  --stop-after-failures N      alias for --max-failures
  --require-full               require every selected row to full-match
  --allow-empty                exit successfully if no default/added filter selects rows
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

is_nonnegative_int() {
  [[ "$1" =~ ^[0-9]+$ ]]
}

is_positive_int() {
  [[ "$1" =~ ^[1-9][0-9]*$ ]]
}

count_filter() {
  local filter="$1"
  local count_dir
  count_dir="$(pwd)/gen-out/eest-bls12-pairing-map-count-$(echo "$filter" | tr -c 'A-Za-z0-9._-' '_')"
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
    return
  fi
  wc -l < "$manifest" | tr -d " "
}

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

if [[ "${#FILTERS[@]}" -eq 0 ]]; then
  if [[ -n "${EEST_BLS12_PAIRING_MAP_FILTERS:-}" ]]; then
    read -r -a FILTERS <<< "$EEST_BLS12_PAIRING_MAP_FILTERS"
  else
    FILTERS=("bls12_pairing" "bls12_map_fp_to_g1" "bls12_map_fp2_to_g2")
  fi
fi

[[ -d "$FX" ]] || { echo "fixtures not found at $FX (run scripts/eest-fetch-fixtures.sh '$TAG')" >&2; exit 1; }
is_nonnegative_int "$SKIP" || { echo "--skip must be a nonnegative integer (got: $SKIP)" >&2; exit 1; }
if [[ -n "$LIMIT_OVERRIDE" ]]; then
  is_positive_int "$LIMIT_OVERRIDE" || { echo "--limit must be positive when set (got: $LIMIT_OVERRIDE)" >&2; exit 1; }
fi
is_positive_int "$MAX_FAILURES" || { echo "--max-failures must be positive (got: $MAX_FAILURES)" >&2; exit 1; }

ran_filters=0
selected_total=0

for filter in "${FILTERS[@]}"; do
  count="$(count_filter "$filter")"
  if [[ "$count" -eq 0 ]]; then
    echo "==> BLS12 pairing/map filter=$filter selected=0 (skipping)"
    continue
  fi
  if [[ "$SKIP" -ge "$count" ]]; then
    echo "==> BLS12 pairing/map filter=$filter selected=$count skip=$SKIP leaves 0 row(s) (skipping)"
    continue
  fi

  remaining=$((count - SKIP))
  limit="${LIMIT_OVERRIDE:-$remaining}"
  if [[ "$limit" -gt "$remaining" ]]; then
    limit="$remaining"
  fi

  run_dir="$RUN_DIR/$(echo "$filter" | tr -c 'A-Za-z0-9._-' '_')"
  args=(
    --filter "$filter"
    --skip "$SKIP"
    --limit "$limit"
    --jobs "$JOBS"
    --quiet-passes
    --max-failures "$MAX_FAILURES"
    --steps "$STEPS"
    --run-dir "$run_dir"
  )
  if [[ "$REQUIRE_FULL" == "1" ]]; then
    args+=(--min-full "$limit")
  fi

  echo "==> BLS12 pairing/map filter=$filter count=$count skip=$SKIP limit=$limit require_full=$REQUIRE_FULL"
  scripts/codegen-eest-stateless-check.sh "${args[@]}" "${EXTRA_ARGS[@]}"
  ran_filters=$((ran_filters + 1))
  selected_total=$((selected_total + limit))
done

if [[ "$ran_filters" -eq 0 ]]; then
  msg="no BLS12 pairing/map stateless blocks selected in $FX"
  if [[ "$ALLOW_EMPTY" == "1" ]]; then
    echo "==> $msg"
    exit 0
  fi
  echo "$msg" >&2
  echo "try a fixture tag containing Prague EIP-2537 fixtures or override --filter" >&2
  exit 1
fi

echo "==> PASS: BLS12 pairing/map EEST frontier probe completed filters=$ran_filters selected=$selected_total"
