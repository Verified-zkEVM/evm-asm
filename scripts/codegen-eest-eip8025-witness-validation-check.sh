#!/usr/bin/env bash
# codegen-eest-eip8025-witness-validation-check.sh -- regression guard for the
# EIP-8025 witness code-preimage rejects.
#
# These soundness rejects have a documented history of REGRESSING:
#   * .58.5 (current-frame code preimage) was "fixed" then came undone -> ok3nl
#     re-opened the same false-accept; the real fix is #8638 (require the
#     recipient code_hash in witness.codes at .Lbv_contract_dispatch).
#   * mkwwf (implicit system-contract code) was masked by witness_lookup_by_hash's
#     64 KiB linear-scan cap false-missing >64 KiB codes sections, papered over by
#     a blanket system-contract reprieve; the real fix is #8647 (drop the cap +
#     remove the reprieve).
#
# Each `validation_codes_missing_*` fixture is a block the spec REJECTS because
# execution reads a code_hash absent from witness.codes (WitnessState.get_code
# raises). The guest must reject (succ=0). This check reruns the whole
# witness_validation_codes group and asserts a full 105-byte match (i.e. every
# row rejects exactly as the spec does) -- so any future change that lets a
# missing-code block slip back to accept (the recurring false-accept class) is
# caught here instead of in a re-opened P0 soundness bead.
#
# The run limit is derived from the converted manifest so future parameter rows
# are included automatically.
set -euo pipefail

cd "$(dirname "$0")/.."

TAG="${EEST_FIXTURE_TAG:-zkevm@v0.4.0}"
JOBS="${EEST_EIP8025_WITNESS_JOBS:-${EEST_JOBS:-2}}"
STEPS="${EEST_EIP8025_WITNESS_STEPS:-${EEST_STEPS:-1000000000}}"
RUN_DIR="${EEST_EIP8025_WITNESS_RUN_DIR:-gen-out/eest-eip8025-witness-validation}"
FX="${EEST_FIXTURES_DIR:-$(pwd)/gen-out/eest-fixtures/$TAG/fixtures/fixtures}"
FILTER="${EEST_EIP8025_WITNESS_FILTER:-validation_codes_missing}"
LIMIT_OVERRIDE="${EEST_EIP8025_WITNESS_LIMIT:-}"

[[ -d "$FX" ]] || { echo "fixtures not found at $FX (run scripts/eest-fetch-fixtures.sh '$TAG')" >&2; exit 1; }

count_dir="$(pwd)/gen-out/eest-eip8025-witness-validation-count"
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
      echo "eip8025 witness-validation error for $relpath: $status $detail" >&2
    else
      semantic_failures=$((semantic_failures + 1))
      echo "eip8025 witness-validation mismatch for $relpath: status=$status (a missing-code block must reject; succ guest=${detail:64:2})" >&2
    fi
  fi
done < "$RUN_MANIFEST"

if [[ "$selected" -eq 0 ]]; then
  echo "no eip8025 witness-validation rows selected" >&2
  exit 1
fi
if [[ "$missing_results" -ne 0 ]]; then
  echo "missing $missing_results eip8025 witness-validation result file(s)" >&2
  exit 1
fi
if [[ "$errors" -ne 0 ]]; then
  echo "found $errors eip8025 witness-validation error row(s)" >&2
  exit 1
fi
if [[ "$semantic_failures" -ne 0 ]]; then
  echo "found $semantic_failures eip8025 witness-validation semantic mismatch row(s) -- a missing-code false-accept regressed" >&2
  exit 1
fi
if [[ "$ok_full" -ne "$selected" ]]; then
  echo "only $ok_full of $selected eip8025 witness-validation row(s) full-matched" >&2
  exit 1
fi

echo "==> PASS: eip8025 witness-validation rejects full-match selected=$selected full=$ok_full"
