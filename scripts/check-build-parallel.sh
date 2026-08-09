#!/usr/bin/env bash
# Run independent build-dependent CI gates concurrently on one prepared runner.
set -euo pipefail

cd "$(dirname "$0")/.."

work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT

names=()
pids=()
declare -A expected_steps=(
  [codegen]=5
  [guestaddrs-starts]=1
  [asm-to-program]=1
  [reports]=3
  [axioms]=1
  [arithmetic-fuzz]=1
)

start() {
  local name="$1"
  shift
  names+=("$name")
  ( "$@" ) >"$work/$name.log" 2>&1 &
  pids+=("$!")
}

run_step() {
  printf 'CHECK_BUILD_PARALLEL_STEP'
  printf ' %q' "$@"
  printf '\n'
  "$@"
}

codegen_checks() {
  run_step scripts/codegen-stateless-link-check.sh --no-build
  # GH #10637: the line above links stateless_guest ONLY, so a unit that mirrors
  # guest handlers can reference an undefined symbol with every gate green.
  run_step scripts/check-build-units-link.sh
  run_step scripts/check-region-map.sh
  # check-region-map compares the DECLARED map against the ELF, so a region that
  # is not declared is not checked. Three in-use anchors were dropped from
  # RegionMap by a merge resolution with every gate green; this asserts the
  # missing invariant (declared anchor => has a region entry). Pure grep, instant.
  run_step scripts/check-memorylayout-region-coverage.sh
  run_step scripts/check-guarded-handler-bytes.sh
}

report_checks() {
  run_step scripts/check-progress.sh
  run_step scripts/check-drift.sh
  # #11637: row EXISTENCE, which nothing gated before -- every other registry
  # invariant quantifies over rows that are already there, so a linked, proven
  # routine with no row at all tripped nothing. Pure source scan, instant.
  run_step scripts/check-registry-coverage.py
}

start codegen codegen_checks
start guestaddrs-starts scripts/check-guestaddrs-starts.sh
start asm-to-program scripts/check-asm-to-program.sh
start reports report_checks
start axioms scripts/check-axioms.sh
start arithmetic-fuzz scripts/fuzz-arith-diff.sh

status=0
for i in "${!pids[@]}"; do
  name="${names[$i]}"
  lane_status=PASS
  if ! wait "${pids[$i]}"; then
    lane_status=FAIL
    status=1
  fi

  log="$work/$name.log"
  steps="$(grep -c '^CHECK_BUILD_PARALLEL_STEP ' "$log" || true)"
  skips="$(grep -Eic '(^|[^[:alpha:]])(skip|skipping)([^[:alpha:]]|$)' "$log" || true)"
  expected="${expected_steps[$name]}"

  if [[ "$lane_status" == PASS && "$skips" -gt 0 ]]; then
    # A child gate may intentionally return zero after deciding it cannot run.
    # That is not evidence for a green aggregate: make the third state visible
    # and fail the wrapper so CI cannot mistake it for a completed lane.
    lane_status=SKIP
    status=1
  elif [[ "$lane_status" == PASS && "$steps" -ne "$expected" ]]; then
    # set -e can stop a lane before its later children start. Report that loss
    # of coverage explicitly even when a future child changes its exit policy.
    lane_status=INCOMPLETE
    status=1
  fi

  if [[ "$lane_status" == PASS ]]; then
    echo "==> $name: PASS (steps=$steps/$expected, skips=$skips)"
  elif [[ "$lane_status" == FAIL ]]; then
    echo "==> $name: FAIL (steps=$steps/$expected, skips=$skips)" >&2
  else
    echo "==> $name: $lane_status (steps=$steps/$expected, skips=$skips)" >&2
  fi
  sed "s/^/[$name] /" "$log"
done

exit "$status"
