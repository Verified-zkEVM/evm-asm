#!/usr/bin/env bash
# codegen-eest-simple-value-transfer-frontier-check.sh -- focused simple
# value-transfer transaction EEST gate.
#
# Promotes the former baseline probe into a passing gate. For each owned
# fixture filter it derives the selected stateless block count from the
# converted manifest and requires every selected block to full-match
# (--min-full == per-filter count). New rows added to the owned fixtures are
# covered automatically because the count is recomputed from the manifest on
# every run, so the wrapper stays future-proof without a hardcoded fixture
# list.
#
# The gated default selects the canonical "Simple tx/value transfer" surface
# from docs/eest-feature-surfaces.md (`validation/transaction`). Broader
# transaction-validity filters (eip79xx calldata/access-list pricing, type-3
# blob validity, etc.) are NOT simple value transfers and are not part of this
# gate; pass `--filter SUBSTR` explicitly to probe them, but do not treat their
# selection as a simple-transfer pass claim.
set -euo pipefail

cd "$(dirname "$0")/.."

TAG="${EEST_FIXTURE_TAG:-tests-zkevm@v0.5.0}"
LIMIT="${EEST_SIMPLE_TRANSFER_LIMIT:-1}"
SKIP="${EEST_SIMPLE_TRANSFER_SKIP:-0}"
JOBS="${EEST_SIMPLE_TRANSFER_JOBS:-${EEST_JOBS:-2}}"
STEPS="${EEST_SIMPLE_TRANSFER_STEPS:-${EEST_STEPS:-1000000000}}"
RUN_DIR="${EEST_SIMPLE_TRANSFER_RUN_DIR:-gen-out/eest-simple-transfer-frontier}"
FX="${EEST_FIXTURES_DIR:-$(pwd)/gen-out/eest-fixtures/$TAG/fixtures/fixtures}"
LIMIT_OVERRIDE="${EEST_SIMPLE_TRANSFER_LIMIT:-}"
FILTERS=()
EXTRA_ARGS=()

usage() {
  cat <<'USAGE'
Usage:
  scripts/codegen-eest-simple-value-transfer-frontier-check.sh [options] [-- extra harness args]

For each selected filter the wrapper counts the stateless blocks the fixture
converter selects, then requires every selected block to full-match
(--min-full == that count). New rows added to the owned fixtures are picked up
automatically.

Options:
  --filter SUBSTR              add a fixture path substring filter
                               (default: validation/transaction and transaction_validity)
  --skip N                     skip first N selected fixtures per filter (default: 0)
  --limit N                    per-filter fixture cap (default: 1)
  --jobs N|auto                ziskemu jobs (default: $EEST_SIMPLE_TRANSFER_JOBS, $EEST_JOBS, or 2)
  --steps N                    ziskemu max steps (default: $EEST_SIMPLE_TRANSFER_STEPS, $EEST_STEPS, or 1000000000)
  --max-failures N             stop each filter after N failures (default: 1)
  --stop-after-failures N      alias for --max-failures
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

while [[ $# -gt 0 ]]; do
  case "$1" in
    -h|--help) usage; exit 0 ;;
    --filter) require_arg "$1" "${2:-}"; FILTERS+=("$2"); shift 2 ;;
    --limit) require_arg "$1" "${2:-}"; LIMIT_OVERRIDE="$2"; shift 2 ;;
    --jobs) require_arg "$1" "${2:-}"; JOBS="$2"; shift 2 ;;
    --steps) require_arg "$1" "${2:-}"; STEPS="$2"; shift 2 ;;
    --) shift; EXTRA_ARGS+=("$@"); break ;;
    *) echo "unknown option: $1" >&2; usage >&2; exit 1 ;;
  esac
done

if [[ "${#FILTERS[@]}" -eq 0 ]]; then
  FILTERS=("validation/transaction")
fi

[[ -d "$FX" ]] || { echo "fixtures not found at $FX (run scripts/eest-fetch-fixtures.sh '$TAG')" >&2; exit 1; }

count_root="$(pwd)/gen-out/eest-simple-transfer-frontier-count"
rm -rf "$count_root"
mkdir -p "$count_root"

for filter in "${FILTERS[@]}"; do
  echo "==> simple value-transfer frontier filter: $filter"
  cdir="$count_root/$(printf '%s' "$filter" | tr '/ ' '__')"
  mkdir -p "$cdir"
  python3 scripts/eest-stateless-to-input.py \
    --fixtures-dir "$FX" \
    --out-dir "$cdir" \
    --filter "$filter" \
    >/dev/null

  manifest="$cdir/manifest.tsv"
  [[ -s "$manifest" ]] || { echo "no stateless blocks selected for filter: $filter" >&2; exit 1; }
  COUNT="$(wc -l < "$manifest" | tr -d ' ')"
  LIMIT="${LIMIT_OVERRIDE:-$COUNT}"

  scripts/codegen-eest-stateless-check.sh \
    --filter "$filter" \
    --limit "$LIMIT" \
    --jobs "$JOBS" \
    --quiet-passes \
    --min-full "$LIMIT" \
    --steps "$STEPS" \
    --run-dir "$RUN_DIR" \
    "${EXTRA_ARGS[@]}"

  echo "==> filter full-matched selected=$LIMIT of available=$COUNT: $filter"
done

echo "==> PASS: simple value-transfer frontier full-matched all selected filters"
