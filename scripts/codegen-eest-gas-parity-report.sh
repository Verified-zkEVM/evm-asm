#!/usr/bin/env bash
# Run a focused EEST stateless guest selection and compare ziskemu output with
# Python execution-specs on the exact same guest-visible input bytes.
set -euo pipefail

cd "$(dirname "$0")/.."

usage() {
  cat <<'USAGE'
Usage:
  scripts/codegen-eest-gas-parity-report.sh [codegen-eest-stateless-check options] [--tsv]

Examples:
  scripts/codegen-eest-gas-parity-report.sh \
    --filter eip7778_block_gas_accounting_without_refunds/gas_accounting/multi_transaction_gas_accounting.json \
    --limit 1 --jobs 1 --max-failures 1

  scripts/codegen-eest-gas-parity-report.sh \
    --filter eip7825_transaction_gas_limit_cap/tx_gas_limit/maximum_gas_refund.json \
    --limit 1 --jobs 1 --tsv

All normal codegen-eest-stateless-check.sh options are forwarded. The wrapper
forces --verify-execution-spec-input, then runs scripts/eest-gas-parity-report.py
through the local execution-specs checkout.
USAGE
}

TSV=0
HARNESS_ARGS=()
while [[ $# -gt 0 ]]; do
  case "$1" in
    -h|--help) usage; exit 0 ;;
    --tsv) TSV=1; shift ;;
    *) HARNESS_ARGS+=("$1"); shift ;;
  esac
done

RUN_DIR="${EEST_GAS_PARITY_RUN_DIR:-gen-out/eest-gas-parity/run-$(date -u +%Y%m%dT%H%M%SZ)-$$}"
case "$RUN_DIR" in
  /*) ;;
  *) RUN_DIR="$PWD/$RUN_DIR" ;;
esac
mkdir -p "$(dirname "$RUN_DIR")"

scripts/codegen-eest-stateless-check.sh \
  --run-dir "$RUN_DIR" \
  --verify-execution-spec-input \
  "${HARNESS_ARGS[@]}"

report_args=(--run-dir "$RUN_DIR")
[[ "$TSV" -eq 1 ]] && report_args+=(--tsv)

uv run --directory execution-specs --quiet python3 \
  "$PWD/scripts/eest-gas-parity-report.py" "${report_args[@]}"
