#!/usr/bin/env bash
# Run independent build-dependent CI gates concurrently on one prepared runner.
set -euo pipefail

cd "$(dirname "$0")/.."

if [[ "${EVMASM_BUILD_LOCK_HELD:-0}" != 1 ]]; then
  exec scripts/lib/worktree-build-lock.sh "$0" "$@"
fi

work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT

names=()
pids=()
declare -A expected_steps=(
  [codegen]=9
  # 8 since check-orphan-blocks.sh (#12259) — whole-image CFG on the linked ELF.
  # 9 since check-rowed-liveness.sh (#12381) — rowed symbols must be REACHED on
  # that same image, not merely present in its symbol census.
  [guestaddrs-starts]=1
  [asm-to-program]=1
  # 9 since check-codegen-counts.sh (#12322) was added alongside the existing
  # report checks (the count grew 5 → 6 → 7 → 8 → 9). ⚠️ This count is asserted
  # exactly: adding a `run_step` to a lane without bumping it here reports the
  # lane INCOMPLETE and fails the wrapper.
  [reports]=9
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
  # GH #11186: retired layout literals must not reappear after a relocate.
  # Pure rg, no toolchain. Declared step so an unwired guard cannot green-pass.
  run_step scripts/check-layout-residual-literals.sh
  # GH #12145: probe-only fixtures skip the linking consistency leg, so leg (a)
  # is callee-name-blind (unlinked jal encodes identically for any target).
  # This gate compares fixture relocation tables against lean RelocTables.
  run_step scripts/check-fixture-reloc-targets.sh
  # GH #12259: orphaned basic blocks (zero static incoming) on the linked ELF.
  # Catches the #12254 lost-edge class. Needs the regionmap guest from the
  # link check above. Self-test (verdict flip) runs inside the wrapper.
  run_step scripts/check-orphan-blocks.sh
  # GH #12381: a registry row asserts proven code is part of the guest's story,
  # and nothing checked that the code RUNS. #11303's routine-liveness answers
  # PRESENT and accepts census presence as liveness by design; three .proven
  # rows sat on uncalled code (#12351) and this gate's instrument found five
  # more (#12386). Whole-image reachability, so it belongs here beside the
  # orphan gate rather than in source-checks. Self-test runs inside the wrapper.
  run_step scripts/check-rowed-liveness.sh
}

report_checks() {
  run_step scripts/check-progress.sh
  run_step scripts/check-drift.sh
  # #12322: CODEGEN.md has two independently maintained opcode-count sites.
  # Compare both against the built Lean registry and derive h_invalid as
  # 256 - wired, rather than pinning a second literal.
  run_step scripts/check-codegen-counts.sh
  # Same defect one file over: the guest-image coverage md embeds generator
  # numbers but was hand-maintained, so it drifted invisibly (24.19% vs live
  # 23.65%). The doc is now fully generated; this is the regenerate-and-
  # compare guard. Pure Python over committed fixtures, instant.
  run_step scripts/check-guest-image-coverage.sh
  # #11637: row EXISTENCE, which nothing gated before -- every other registry
  # invariant quantifies over rows that are already there, so a linked, proven
  # routine with no row at all tripped nothing. Pure source scan, instant.
  #
  # The self-test runs FIRST and is not ceremony: this gate's own pattern had a
  # blind spot (`_fnspec`, three linked spec-bearing routines it scanned straight
  # past), and a census that cannot see a convention passes while covering
  # nothing. The self-test plants one name per convention so that failure mode is
  # a build error rather than a clean report.
  run_step scripts/check-registry-coverage.py --self-test
  run_step scripts/check-registry-coverage.py
  # #12210: AxiomWitnesses is generated from the registry, so a deletion can
  # shrink both the expected and reported sets. Pin the independent name set.
  # Self-test first: grow was observed (#12258); shrink had never flipped the
  # lane — inject a deleted binding and require FAIL then PASS on restore.
  run_step scripts/check-axiom-witness-registry.py --self-test
  run_step scripts/check-axiom-witness-registry.py
  # #12146: MANIFEST ↔ GuestImageEntries agreement (legs 1–2). Self-test is
  # inside the script (inject MANIFEST row deletion → must fail). Leg 3 is a
  # post-link measurement in codegen-stateless-link-check.sh (#12151).
  run_step scripts/check-manifest-guestimage.py
}

start codegen codegen_checks
start guestaddrs-starts run_step scripts/check-guestaddrs-starts.sh
start asm-to-program run_step scripts/check-asm-to-program.sh
start reports report_checks
start axioms run_step scripts/check-axioms.sh
start arithmetic-fuzz run_step scripts/fuzz-arith-diff.sh

status=0
for i in "${!pids[@]}"; do
  name="${names[$i]}"
  lane_status=PASS
  child_failed=0
  if ! wait "${pids[$i]}"; then
    child_failed=1
    status=1
  fi

  log="$work/$name.log"
  steps="$(grep -c '^CHECK_BUILD_PARALLEL_STEP ' "$log" || true)"
  # These are the deliberate, machine-readable skip lines emitted by the
  # current child gates. Do not grep for the word "skip" anywhere: region-map
  # also has prose about skipped sub-checks, and an unrelated filename or
  # informational sentence must not turn a passing lane into a false failure.
  skips="$(grep -Eic '^check-build-units-link: SKIP|^check-(guarded-handler-bytes|asm-to-program): .*skipping \(install to enable\)|^[[:space:]]+SKIP emitted-reality|^[[:space:]]+skip Class-A BAL ratchet' "$log" || true)"
  expected="${expected_steps[$name]}"

  if [[ "$steps" -ne "$expected" ]]; then
    # set -e can stop a lane before its later children start. Report that loss
    # of coverage explicitly even when the child that stopped it failed.
    lane_status=INCOMPLETE
    status=1
  elif [[ "$child_failed" -eq 1 ]]; then
    lane_status=FAIL
  elif [[ "$skips" -gt 0 ]]; then
    # A child gate may intentionally return zero after deciding it cannot run.
    # That is not evidence for a green aggregate: make the third state visible
    # and fail the wrapper so CI cannot mistake it for a completed lane.
    lane_status=SKIP
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
