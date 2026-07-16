#!/usr/bin/env bash
# Regress the bounded account-root extension-split old/direct child ABI.
#
# This EEST case reaches mpt_bounded_split_extension's old/direct arm.  Before
# the fix that arm wrote the child length into bsr_builder_result_ref instead
# of bsr_builder_result_len, leaving a stale raw child reference and faulting
# at RAM_END.  Require the complete fixture output, not merely a clean exit.
set -euo pipefail

cd "$(dirname "$0")/.."

JOBS="${EEST_BOUNDED_EXTENSION_SPLIT_JOBS:-${EEST_JOBS:-1}}"
RUN_DIR="${EEST_BOUNDED_EXTENSION_SPLIT_RUN_DIR:-gen-out/eest-bounded-extension-split}"
FILTER="${EEST_BOUNDED_EXTENSION_SPLIT_FILTER:-test_program_program_BASEFEE-debug__b20}"

scripts/codegen-eest-stateless-check.sh \
  --filter "$FILTER" \
  --limit 1 \
  --jobs "$JOBS" \
  --quiet-passes \
  --max-failures 1 \
  --min-full 1 \
  --run-dir "$RUN_DIR" \
  "$@"

BASELINE="$RUN_DIR/eest-baseline.txt"
[[ -s "$BASELINE" ]] || { echo "missing baseline: $BASELINE" >&2; exit 1; }

baseline_value() {
  local label="$1"
  awk -F: -v label="$label" \
    '$1 ~ label { gsub(/^[ \t]+|[ \t]+$/, "", $2); split($2, a, /[ \t]+/); print a[1]; exit }' \
    "$BASELINE"
}

selected="$(baseline_value "selected")"
ran="$(baseline_value "ran")"
errored="$(baseline_value "errored")"
full="$(baseline_value "full match")"

[[ "$selected" == "1" ]] || { echo "expected selected=1, got ${selected:-missing}" >&2; exit 1; }
[[ "$ran" == "1" ]] || { echo "expected ran=1, got ${ran:-missing}" >&2; exit 1; }
[[ "${errored:-missing}" == "0" ]] || { echo "expected errored=0, got ${errored:-missing}" >&2; exit 1; }
[[ "$full" == "1" ]] || { echo "expected full match=1, got ${full:-missing}" >&2; exit 1; }

echo "==> PASS: bounded extension old/direct split matches the BASEFEE EEST fixture"
