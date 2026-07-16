#!/usr/bin/env bash
# Regress the bounded account-root extension-split old/direct child ABI.
#
# This EEST case reaches mpt_bounded_split_extension's old/direct arm.  Before
# the fix that arm wrote the child length into bsr_builder_result_ref instead
# of bsr_builder_result_len, leaving a stale raw child reference and faulting
# at RAM_END.  Require complete fixture output for every clean corpus case that
# reaches the arm, not merely a clean exit.  Two further corpus cases now reach
# the same arm but remain covered by the bounded-storage-root false-reject
# frontier, so they are intentionally not asserted here.
set -euo pipefail

cd "$(dirname "$0")/.."

JOBS="${EEST_BOUNDED_EXTENSION_SPLIT_JOBS:-${EEST_JOBS:-1}}"
RUN_DIR="${EEST_BOUNDED_EXTENSION_SPLIT_RUN_DIR:-gen-out/eest-bounded-extension-split}"

filters=(
  test_program_program_BASEFEE-debug__b20
  test_day_limit_set_daily_limit_fork_Amsterdam-blockchain_test_from_state_test__b0
  test_day_limit_set_daily_limit_no_data_fork_Amsterdam-blockchain_test_from_state_test__b0
  test_wallet_execute_over_daily_limit_only_one_owner_new_fork_Amsterdam-blockchain_test_from_stat
  test_withdrawal_requests_fork_Amsterdam-blockchain_test-single_block_single_withdrawal_request_f
)

baseline_value() {
  local baseline="$1"
  local label="$2"
  awk -F: -v label="$label" \
    '$1 ~ label { gsub(/^[ \t]+|[ \t]+$/, "", $2); split($2, a, /[ \t]+/); print a[1]; exit }' \
    "$baseline"
}

for i in "${!filters[@]}"; do
  case_dir="$RUN_DIR/$i"
  args=(
    --filter "${filters[$i]}"
    --limit 1
    --jobs "$JOBS"
    --quiet-passes
    --max-failures 1
    --min-full 1
    --run-dir "$case_dir"
  )
  [[ "$i" != "0" ]] && args+=(--no-build)
  scripts/codegen-eest-stateless-check.sh "${args[@]}" "$@"

  baseline="$case_dir/eest-baseline.txt"
  [[ -s "$baseline" ]] || { echo "missing baseline: $baseline" >&2; exit 1; }
  selected="$(baseline_value "$baseline" "selected")"
  ran="$(baseline_value "$baseline" "ran")"
  errored="$(baseline_value "$baseline" "errored")"
  full="$(baseline_value "$baseline" "full match")"

  [[ "$selected" == "1" ]] || { echo "expected selected=1, got ${selected:-missing}" >&2; exit 1; }
  [[ "$ran" == "1" ]] || { echo "expected ran=1, got ${ran:-missing}" >&2; exit 1; }
  [[ "${errored:-missing}" == "0" ]] || { echo "expected errored=0, got ${errored:-missing}" >&2; exit 1; }
  [[ "$full" == "1" ]] || { echo "expected full match=1, got ${full:-missing}" >&2; exit 1; }
done

echo "==> PASS: bounded extension old/direct split matches five exact EEST fixtures"
