#!/usr/bin/env bash
# codegen-eest-bmvmx-dispatcher-check.sh -- focused regression for the runtime
# dispatcher-backed transaction class (bmvmx.1 stateless-verdict integration).
#
# This protects a transaction row that passes BECAUSE block_verdict executed the
# transaction through the runtime dispatcher, not merely because BAL replay
# supplied the post-state:
#
#   * The selected `simple_transfer_emits_log` row is a single-tx legacy EOA
#     value transfer. Under EIP-7708 every ETH transfer emits a transfer log, so
#     the row's receipts/log root is only correct if the dispatcher actually
#     EXECUTED the transfer and emitted the log -- BAL replay alone cannot
#     synthesize it.
#   * It is the supported class for the bmvmx.1.4 execution-derived post-state
#     gate: block_verdict computes the execution-derived sender gas-settlement
#     debit (gas_used*eff_gas_price + value) and coinbase fee credit
#     (priority_fee*gas_used) and asserts the BAL sender/coinbase POST balances
#     equal sender_pre-debit / coinbase_pre+credit, rejecting on mismatch
#     (bmvmx.1.4.3.2). So a full match means execution and the witness BAL agree
#     -- the post-state is execution-validated, not blindly trusted.
#
# Unsupported tx classes still fall back conservatively (no regression): non-
# legacy txs (2930/1559/4844/7702), multi-tx blocks, and contract recipients
# that read un-staged state set bmvmx_avail=0 / the dispatcher bails, so the
# verdict relies on the recomputed post-state root + BAL replay as before.
#
# The run limit is derived from the converted manifest so future parameter rows
# for the fixture are included automatically.
set -euo pipefail

cd "$(dirname "$0")/.."

TAG="${EEST_FIXTURE_TAG:-zkevm@v0.4.0}"
JOBS="${EEST_BMVMX_DISPATCHER_JOBS:-${EEST_JOBS:-2}}"
STEPS="${EEST_BMVMX_DISPATCHER_STEPS:-${EEST_STEPS:-1000000000}}"
RUN_DIR="${EEST_BMVMX_DISPATCHER_RUN_DIR:-gen-out/eest-bmvmx-dispatcher}"
FX="${EEST_FIXTURES_DIR:-$(pwd)/gen-out/eest-fixtures/$TAG/fixtures/fixtures}"
FILTER="${EEST_BMVMX_DISPATCHER_FILTER:-simple_transfer_emits_log}"
LIMIT_OVERRIDE="${EEST_BMVMX_DISPATCHER_LIMIT:-}"

[[ -d "$FX" ]] || { echo "fixtures not found at $FX (run scripts/eest-fetch-fixtures.sh '$TAG')" >&2; exit 1; }

count_dir="$(pwd)/gen-out/eest-bmvmx-dispatcher-count"
rm -rf "$count_dir"
mkdir -p "$count_dir"
python3 scripts/eest-stateless-to-input.py \
  --fixtures-dir "$FX" \
  --out-dir "$count_dir" \
  --filter "$FILTER" \
  >/dev/null
manifest="$count_dir/manifest.tsv"
[[ -s "$manifest" ]] || { echo "no stateless blocks selected for $FILTER" >&2; exit 1; }
COUNT="$(wc -l < "$manifest" | tr -d " ")"
LIMIT="${LIMIT_OVERRIDE:-$COUNT}"

scripts/codegen-eest-stateless-check.sh \
  --filter "$FILTER" \
  --limit "$LIMIT" \
  --jobs "$JOBS" \
  --quiet-passes \
  --steps "$STEPS" \
  --run-dir "$RUN_DIR" \
  "$@"

RUN_MANIFEST="$RUN_DIR/manifest.tsv"
[[ -s "$RUN_MANIFEST" ]] || { echo "missing run manifest: $RUN_MANIFEST" >&2; exit 1; }

selected=0
ok_full=0
errors=0
missing_results=0
semantic_failures=0

while IFS=$'\t' read -r label input expected_hex succ_bit input_len gas_limit relpath; do
  selected=$((selected + 1))
  result="$RUN_DIR/$label.result.tsv"
  if [[ ! -f "$result" ]]; then
    missing_results=$((missing_results + 1))
    echo "missing result for $relpath" >&2
    continue
  fi

  if IFS=$'\t' read -r status detail < "$result"; then
    if [[ "$status" == "OK" && "${detail:0:210}" == "${expected_hex:0:210}" ]]; then
      ok_full=$((ok_full + 1))
    elif [[ "$status" == ERROR* ]]; then
      errors=$((errors + 1))
      echo "bmvmx dispatcher error for $relpath: $status $detail" >&2
    else
      semantic_failures=$((semantic_failures + 1))
      echo "bmvmx dispatcher mismatch for $relpath: status=$status" >&2
    fi
  fi
done < "$RUN_MANIFEST"

if [[ "$selected" -eq 0 ]]; then
  echo "no bmvmx dispatcher-backed rows selected" >&2
  exit 1
fi
if [[ "$missing_results" -ne 0 ]]; then
  echo "missing $missing_results bmvmx dispatcher result file(s)" >&2
  exit 1
fi
if [[ "$errors" -ne 0 ]]; then
  echo "found $errors bmvmx dispatcher error row(s)" >&2
  exit 1
fi
if [[ "$semantic_failures" -ne 0 ]]; then
  echo "found $semantic_failures bmvmx dispatcher semantic mismatch row(s)" >&2
  exit 1
fi
if [[ "$ok_full" -ne "$selected" ]]; then
  echo "only $ok_full of $selected bmvmx dispatcher-backed row(s) full-matched" >&2
  exit 1
fi

echo "==> PASS: bmvmx dispatcher-backed rows full-match selected=$selected full=$ok_full"
