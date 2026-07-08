#!/usr/bin/env bash
# codegen-eest-eip7708-simple-transfer-check.sh -- EIP-7708 simple transfer log regression.
#
# The default selection covers every stateless row selected by the
# simple_transfer_emits_log fixture filter. It derives the run limit from the
# converted manifest so future parameter rows for that fixture are included
# automatically.
set -euo pipefail

cd "$(dirname "$0")/.."

TAG="${EEST_FIXTURE_TAG:-tests-zkevm@v0.5.0}"
JOBS="${EEST_EIP7708_SIMPLE_TRANSFER_JOBS:-${EEST_JOBS:-2}}"
STEPS="${EEST_EIP7708_SIMPLE_TRANSFER_STEPS:-${EEST_STEPS:-1000000000}}"
RUN_DIR="${EEST_EIP7708_SIMPLE_TRANSFER_RUN_DIR:-gen-out/eest-eip7708-simple-transfer}"
FX="${EEST_FIXTURES_DIR:-$(pwd)/gen-out/eest-fixtures/$TAG/fixtures/fixtures}"
FILTER="${EEST_EIP7708_SIMPLE_TRANSFER_FILTER:-simple_transfer_emits_log}"
LIMIT_OVERRIDE="${EEST_EIP7708_SIMPLE_TRANSFER_LIMIT:-}"

[[ -d "$FX" ]] || { echo "fixtures not found at $FX (run scripts/eest-fetch-fixtures.sh '$TAG')" >&2; exit 1; }

count_dir="$(pwd)/gen-out/eest-eip7708-simple-transfer-count"
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
      echo "EIP-7708 simple-transfer error for $relpath: $status $detail" >&2
    else
      semantic_failures=$((semantic_failures + 1))
      echo "EIP-7708 simple-transfer mismatch for $relpath: status=$status" >&2
    fi
  fi
done < "$RUN_MANIFEST"

if [[ "$selected" -eq 0 ]]; then
  echo "no EIP-7708 simple-transfer rows selected" >&2
  exit 1
fi
if [[ "$missing_results" -ne 0 ]]; then
  echo "missing $missing_results EIP-7708 simple-transfer result file(s)" >&2
  exit 1
fi
if [[ "$errors" -ne 0 ]]; then
  echo "found $errors EIP-7708 simple-transfer error row(s)" >&2
  exit 1
fi
if [[ "$semantic_failures" -ne 0 ]]; then
  echo "found $semantic_failures EIP-7708 simple-transfer semantic mismatch row(s)" >&2
  exit 1
fi
if [[ "$ok_full" -ne "$selected" ]]; then
  echo "only $ok_full of $selected EIP-7708 simple-transfer row(s) full-matched" >&2
  exit 1
fi

echo "==> PASS: EIP-7708 simple-transfer rows full-match selected=$selected full=$ok_full"
