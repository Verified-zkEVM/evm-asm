#!/usr/bin/env bash
# Run independent build-dependent CI gates concurrently on one prepared runner.
set -euo pipefail

cd "$(dirname "$0")/.."

work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT

names=()
pids=()

start() {
  local name="$1"
  shift
  names+=("$name")
  ( "$@" ) >"$work/$name.log" 2>&1 &
  pids+=("$!")
}

codegen_checks() {
  scripts/codegen-stateless-link-check.sh --no-build
  # GH #10637: the line above links stateless_guest ONLY, so a unit that mirrors
  # guest handlers can reference an undefined symbol with every gate green.
  scripts/check-build-units-link.sh
  scripts/check-region-map.sh
  # check-region-map compares the DECLARED map against the ELF, so a region that
  # is not declared is not checked. Three in-use anchors were dropped from
  # RegionMap by a merge resolution with every gate green; this asserts the
  # missing invariant (declared anchor => has a region entry). Pure grep, instant.
  scripts/check-memorylayout-region-coverage.sh
  scripts/check-guarded-handler-bytes.sh
}

report_checks() {
  scripts/check-progress.sh
  scripts/check-drift.sh
  # #11637: row EXISTENCE, which nothing gated before -- every other registry
  # invariant quantifies over rows that are already there, so a linked, proven
  # routine with no row at all tripped nothing. Pure source scan, instant.
  scripts/check-registry-coverage.py
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
  if wait "${pids[$i]}"; then
    echo "==> $name: PASS"
  else
    echo "==> $name: FAIL" >&2
    status=1
  fi
  sed "s/^/[$name] /" "$work/$name.log"
done

exit "$status"
