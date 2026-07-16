#!/usr/bin/env bash
# codegen-eest-eip7702-delegation-codes-base-check.sh -- EIP-7702 delegation
# code-pointer regression gate (evm-asm-uzb6b).
#
# bal_same_block_delegation_code_resolve used to re-base cahsr_code_offset
# against *(caller-x20+608), but top-level callers (dispatch_tx_runtime_code,
# block_verdict single-tx contract path, multi-tx path) have no runtime env in
# x20 (x20 is evm_env scratch there; slot 608 is unread zero-page .bss), while
# the top-level `.Ldtrc_have_code` re-adds *svf_codes_ptr. The wild pointer
# faulted (load-access fault) in bytecode_is_self_contained on the
# tx_into_{chain,self}_delegating_set_code and pointer_to_pointer EEST rows.
# The resolver now takes the codes base as an explicit a4 argument; this gate
# requires every row of the affected cluster to full-match the fixture's exact
# expected output bytes.
set -euo pipefail

cd "$(dirname "$0")/.."

TAG="${EEST_FIXTURE_TAG:-$(cat scripts/eest-fixture-tag.txt)}"
JOBS="${EEST_EIP7702_DELEG_CODES_BASE_JOBS:-${EEST_JOBS:-2}}"
STEPS="${EEST_EIP7702_DELEG_CODES_BASE_STEPS:-${EEST_STEPS:-1000000000}}"
RUN_DIR="${EEST_EIP7702_DELEG_CODES_BASE_RUN_DIR:-gen-out/eest-eip7702-delegation-codes-base}"
FX="${EEST_FIXTURES_DIR:-$(pwd)/gen-out/eest-fixtures/$TAG/fixtures/fixtures}"
FILTERS=(
  "tx_into_chain_delegating_set_code"
  "tx_into_self_delegating_set_code"
  "pointer_to_pointer"
)

[[ -d "$FX" ]] || { echo "fixtures not found at $FX (run scripts/eest-fetch-fixtures.sh '$TAG')" >&2; exit 1; }

total_selected=0
total_ok_full=0

for FILTER in "${FILTERS[@]}"; do
  count_dir="$(pwd)/gen-out/eest-eip7702-delegation-codes-base-count"
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

  scripts/codegen-eest-stateless-check.sh \
    --filter "$FILTER" \
    --limit "$COUNT" \
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
        echo "EIP-7702 delegation codes-base error for $relpath: $status $detail" >&2
      else
        semantic_failures=$((semantic_failures + 1))
        echo "EIP-7702 delegation codes-base mismatch for $relpath: status=$status" >&2
      fi
    fi
  done < "$RUN_MANIFEST"

  if [[ "$missing_results" -ne 0 ]]; then
    echo "missing $missing_results result file(s) for filter $FILTER" >&2
    exit 1
  fi
  if [[ "$errors" -ne 0 ]]; then
    echo "found $errors error row(s) for filter $FILTER" >&2
    exit 1
  fi
  if [[ "$semantic_failures" -ne 0 ]]; then
    echo "found $semantic_failures semantic mismatch row(s) for filter $FILTER" >&2
    exit 1
  fi
  if [[ "$ok_full" -ne "$selected" ]]; then
    echo "only $ok_full of $selected row(s) full-matched for filter $FILTER" >&2
    exit 1
  fi

  total_selected=$((total_selected + selected))
  total_ok_full=$((total_ok_full + ok_full))
done

if [[ "$total_selected" -eq 0 ]]; then
  echo "no EIP-7702 delegation codes-base rows selected" >&2
  exit 1
fi

echo "==> PASS: EIP-7702 delegation codes-base rows full-match selected=$total_selected full=$total_ok_full"
