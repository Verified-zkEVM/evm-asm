#!/usr/bin/env bash
# codegen-eest-eip7002-system-errors-check.sh -- EIP-7002 system-contract-errors gate.
#
# Full-match gate for the modified-withdrawal-contract system_contract_errors
# rows (out_of_gas / reaches_gas_limit / reverts / throws). The previously-failing
# system_contract_reaches_gas_limit row carries a ~73 KB witness.codes section;
# PR #8647 -- drop the witness_lookup_by_hash 64 KiB linear-scan cap that
# false-missed >64 KiB sections, and remove the 36141b1cb blanket system-contract
# reprieve that masked it -- is the repair that turned this into a full-match gate
# (it previously sat at full=3/succ=3/fail=1). The gate now protects that fix from
# a perf-cap regression: re-capping the lookup would false-reject the >64 KiB row
# again (the recurring class behind mkwwf's false-accept).
set -euo pipefail

cd "$(dirname "$0")/.."

TAG="${EEST_FIXTURE_TAG:-zkevm@v0.4.0}"
JOBS="${EEST_EIP7002_SYSTEM_ERRORS_JOBS:-${EEST_JOBS:-2}}"
STEPS="${EEST_EIP7002_SYSTEM_ERRORS_STEPS:-${EEST_STEPS:-1000000000}}"
RUN_DIR="${EEST_EIP7002_SYSTEM_ERRORS_RUN_DIR:-gen-out/eest-eip7002-system-errors}"
FX="${EEST_FIXTURES_DIR:-$(pwd)/gen-out/eest-fixtures/$TAG/fixtures/fixtures}"
FILTER="${EEST_EIP7002_SYSTEM_ERRORS_FILTER:-modified_withdrawal_contract/system_contract_errors.json}"
REQUIRED="eip7002_el_triggerable_withdrawals/modified_withdrawal_contract/system_contract_errors.json"

[[ -d "$FX" ]] || { echo "fixtures not found at $FX (run scripts/eest-fetch-fixtures.sh '$TAG')" >&2; exit 1; }

count_dir="$(pwd)/gen-out/eest-eip7002-system-errors-count"
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

if [[ "$COUNT" -ne 4 ]]; then
  echo "expected four EIP-7002 system-contract-error rows, selected $COUNT" >&2
  exit 1
fi
if ! awk -F'\t' -v required="$REQUIRED" '$7 ~ required { found += 1 } END { exit found == 4 ? 0 : 1 }' "$manifest"; then
  echo "required EIP-7002 fixture rows not selected by $FILTER: $REQUIRED" >&2
  exit 1
fi

scripts/codegen-eest-stateless-check.sh \
  --filter "$FILTER" \
  --limit "$COUNT" \
  --jobs "$JOBS" \
  --quiet-passes \
  --max-failures "$COUNT" \
  --steps "$STEPS" \
  --run-dir "$RUN_DIR" \
  "$@"

baseline="$RUN_DIR/eest-baseline.txt"
[[ -s "$baseline" ]] || { echo "missing EEST baseline: $baseline" >&2; exit 1; }

baseline_value() {
  local label="$1"
  awk -F: -v label="$label" '$1 ~ label { gsub(/^[ \t]+|[ \t]+$/, "", $2); split($2, a, /[ \t]+/); print a[1]; exit }' "$baseline"
}

selected="$(baseline_value "selected")"
errored="$(baseline_value "errored")"
budget="$(baseline_value "budget")"
ran="$(baseline_value "ran")"
full="$(baseline_value "full match")"
root="$(baseline_value "root match")"
succ="$(baseline_value "succ match")"
tail="$(baseline_value "tail match")"
fail="$(baseline_value "fail")"

[[ "$selected" == "4" ]] || { echo "expected selected=4, got $selected" >&2; exit 1; }
[[ "$errored" == "0" ]] || { echo "expected errored=0, got $errored" >&2; exit 1; }
[[ "$budget" == "0" ]] || { echo "expected budget=0, got $budget" >&2; exit 1; }
[[ "$ran" == "4" ]] || { echo "expected ran=4, got $ran" >&2; exit 1; }
[[ "$full" == "4" ]] || { echo "expected full=4 (all rows full-match post-#8647; a regression here means the >64KiB witness.codes lookup broke again), got $full" >&2; exit 1; }
[[ "$root" == "4" ]] || { echo "expected root=4, got $root" >&2; exit 1; }
[[ "$succ" == "4" ]] || { echo "expected succ=4, got $succ" >&2; exit 1; }
[[ "$tail" == "4" ]] || { echo "expected tail=4, got $tail" >&2; exit 1; }
[[ "$fail" == "0" ]] || { echo "expected fail=0, got $fail" >&2; exit 1; }

echo "==> PASS: EIP-7002 system-contract-errors full-match gate selected=4 full=4"
