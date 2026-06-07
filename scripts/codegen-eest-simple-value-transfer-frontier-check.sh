#!/usr/bin/env bash
# Probe simple value-transfer transaction frontiers through the stateless guest.
#
# This wrapper intentionally delegates fixture discovery to
# codegen-eest-stateless-check.sh. It loops over path filters owned by the
# simple tx/value-transfer surface so newly added matching fixtures are covered
# without maintaining a hardcoded fixture list.
set -euo pipefail

cd "$(dirname "$0")/.."

LIMIT="${EEST_SIMPLE_TRANSFER_LIMIT:-1}"
SKIP="${EEST_SIMPLE_TRANSFER_SKIP:-0}"
JOBS="${EEST_SIMPLE_TRANSFER_JOBS:-${EEST_JOBS:-2}}"
STEPS="${EEST_SIMPLE_TRANSFER_STEPS:-${EEST_STEPS:-1000000000}}"
MAX_FAILURES="${EEST_SIMPLE_TRANSFER_MAX_FAILURES:-1}"
FILTERS=()
EXTRA_ARGS=()

usage() {
  cat <<'USAGE'
Usage:
  scripts/codegen-eest-simple-value-transfer-frontier-check.sh [options] [-- extra harness args]

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
    --skip) require_arg "$1" "${2:-}"; SKIP="$2"; shift 2 ;;
    --limit) require_arg "$1" "${2:-}"; LIMIT="$2"; shift 2 ;;
    --jobs) require_arg "$1" "${2:-}"; JOBS="$2"; shift 2 ;;
    --steps) require_arg "$1" "${2:-}"; STEPS="$2"; shift 2 ;;
    --max-failures|--stop-after-failures)
      require_arg "$1" "${2:-}"; MAX_FAILURES="$2"; shift 2 ;;
    --) shift; EXTRA_ARGS+=("$@"); break ;;
    *) echo "unknown option: $1" >&2; usage >&2; exit 1 ;;
  esac
done

if [[ "${#FILTERS[@]}" -eq 0 ]]; then
  FILTERS=("validation/transaction" "transaction_validity")
fi

for filter in "${FILTERS[@]}"; do
  echo "==> simple value-transfer frontier filter: $filter"
  scripts/codegen-eest-stateless-check.sh \
    --filter "$filter" \
    --skip "$SKIP" \
    --limit "$LIMIT" \
    --jobs "$JOBS" \
    --steps "$STEPS" \
    --max-failures "$MAX_FAILURES" \
    --quiet-passes \
    "${EXTRA_ARGS[@]}"
done

echo "==> PASS: simple value-transfer frontier probe completed"
