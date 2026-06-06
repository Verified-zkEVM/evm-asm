#!/usr/bin/env bash
# codegen-eest-precompile-absence-check.sh -- inactive precompile absence EEST gate.
#
# The default selection covers every stateless row selected by the
# precompile_absence fixture filter. It derives the run limit from the converted
# manifest so future parameter rows for that fixture are included automatically.
set -euo pipefail

cd "$(dirname "$0")/.."

TAG="${EEST_FIXTURE_TAG:-zkevm@v0.4.0}"
JOBS="${EEST_PRECOMPILE_ABSENCE_JOBS:-${EEST_JOBS:-3}}"
STEPS="${EEST_PRECOMPILE_ABSENCE_STEPS:-${EEST_STEPS:-1000000000}}"
RUN_DIR="${EEST_PRECOMPILE_ABSENCE_RUN_DIR:-gen-out/eest-precompile-absence}"
FX="${EEST_FIXTURES_DIR:-$(pwd)/gen-out/eest-fixtures/$TAG/fixtures/fixtures}"
FILTER="${EEST_PRECOMPILE_ABSENCE_FILTER:-precompile_absence}"
LIMIT_OVERRIDE="${EEST_PRECOMPILE_ABSENCE_LIMIT:-}"

[[ -d "$FX" ]] || { echo "fixtures not found at $FX (run scripts/eest-fetch-fixtures.sh '$TAG')" >&2; exit 1; }

count_dir="$(pwd)/gen-out/eest-precompile-absence-count"
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
  --min-full "$LIMIT" \
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
      echo "precompile_absence error for $relpath: $status $detail" >&2
    else
      semantic_failures=$((semantic_failures + 1))
      echo "precompile_absence mismatch for $relpath: status=$status" >&2
    fi
  fi
done < "$RUN_MANIFEST"

if [[ "$selected" -eq 0 ]]; then
  echo "no precompile_absence rows selected" >&2
  exit 1
fi
if [[ "$missing_results" -ne 0 ]]; then
  echo "missing $missing_results precompile_absence result file(s)" >&2
  exit 1
fi
if [[ "$errors" -ne 0 ]]; then
  echo "found $errors precompile_absence error row(s)" >&2
  exit 1
fi
if [[ "$semantic_failures" -ne 0 ]]; then
  echo "found $semantic_failures precompile_absence semantic mismatch row(s)" >&2
  exit 1
fi
if [[ "$ok_full" -ne "$selected" ]]; then
  echo "only $ok_full of $selected precompile_absence row(s) full-matched" >&2
  exit 1
fi

echo "==> PASS: precompile_absence rows full-match selected=$selected full=$ok_full"
