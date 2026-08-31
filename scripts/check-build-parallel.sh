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
  # 8 since check-orphan-blocks.sh (#12259) — whole-image CFG on the linked ELF.
  # 9 since check-rowed-liveness.sh (#12381) — rowed symbols must be REACHED on
  # that same image, not merely present in its symbol census.
  # 10 since check-hed-arity-guard.sh (#12462) — every jal to
  # header_extended_decode must be preceded by the arity-check jal.
  # 11 since check-opcode-tables.sh (#12496) — ELF↔Lean opcode_gas_costs /
  # opcode_handlers byte identity; was documented as CI but never wired.
  # 12 since check-transcription-queue.sh (#12496) — regenerate-and-compare
  # for docs/4ch8f-transcription-queue.md; was documented as CI but never
  # wired, and on first measure was red (stale committed queue).
  # 13 since check-misaligned-access.sh (#12560) — PARTIAL linked-guest
  # wide-access alignment: statically-resolvable bases only; UNKNOWN bases
  # (callee args, sp-relative and call-clobbered) are reported, not checked.
  # 14 since check-no-seed-csr.sh (#10796) — the SailEquiv bridge excludes
  # Sail's nondeterministic Zkr seed CSR; this scans the linked production ELF
  # and fails if that excluded instruction ever appears.
  [codegen]=14
  [guestaddrs-starts]=1
  [asm-to-program]=1
  # The report count grew 5 → 6 → 7 → 8 → 9 → 10 when check-doc-links.sh
  # (#12572) was added, then back to 9 in #12683 when check-progress.sh was
  # retired with the committed PROGRESS.md. It is 10 again since #12908 added
  # check-file-size.sh below.
  # ⚠️ This count is asserted exactly, in BOTH directions: adding a `run_step`
  # to a lane without bumping it here reports the lane INCOMPLETE, and so does
  # removing one without lowering it (that is how this edit was caught).
  # 10 since check-file-size.sh (#12908) was added to this post-build bundle;
  # it is also a direct source-check gate, so the bundle-sync audit requires
  # both appearances to stay aligned.
  [reports]=10
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
  # GH #10796: SailEquiv deliberately excludes generated CSR constructors,
  # including nondeterministic Zkr seed CSR.  Scan the linked production image
  # rather than a hand fixture; a missing ELF/toolchain is a hard failure, not
  # a skip, because an unchecked scope assertion must never read as green.
  run_step scripts/check-no-seed-csr.sh --guest-elf gen-out/regionmap/stateless_guest.elf
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
  # GH #12560: the verified RV64 semantics reject misaligned wide accesses,
  # while ziskemu tolerates them.  PARTIAL gate: scan statically-resolvable
  # bases, print the UNKNOWN population, and run the real pre-fix
  # validate_parent_hash_link control as an explicit informational blind-spot
  # check alongside the planted failure self-test.
  run_step scripts/check-misaligned-access.sh
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
  # GH #12462: every jal to header_extended_decode must be preceded by
  # header_extended_decode_arity_check (linked disassembly). Catches the
  # #12438 class (checker exists but call-site convention is unenforced).
  # Self-test runs inside the wrapper; needs the regionmap guest ELF.
  run_step scripts/check-hed-arity-guard.sh
  # GH #12496: opcode dispatch tables — Lean OpcodeTables mirror vs linked
  # ELF .data for opcode_gas_costs / opcode_handlers. Documented as a CI
  # drift guard but never wired; same dormant-gate class as #12494.
  # Needs the guest ELF + riscv toolchain; skips (exit 0) if toolchain absent.
  run_step scripts/check-opcode-tables.sh
  # GH #12496: demand-first transcription queue doc drift guard. Same shape as
  # check-guest-image-coverage.sh (self-test + --check-doc). Was titled "CI
  # entry point" but never wired; first run on main failed — dormant AND
  # hiding real ranking/table drift (unlike opcode-tables, which was clean).
  # Pure Python over committed fixtures; no ELF / toolchain.
  run_step scripts/check-transcription-queue.sh
}

report_checks() {
  # #12908: file-size is a blocking source-shape gate.  Keep it in the local
  # post-build bundle as well as its direct workflow step so this lane catches
  # the same per-file cap on a prepared checkout.
  run_step scripts/check-file-size.sh
  # NOTE (#12683): `check-progress.sh` used to head this lane. PROGRESS.md is
  # no longer committed (it is generated on demand by
  # `scripts/progress-report.sh --write`), so there is nothing to compare a
  # regeneration against and the gate was retired with the file. DRIFT.md is
  # still committed and still drift-gated below — do not read the absence of a
  # progress gate as the drift discipline being dropped.
  run_step scripts/check-drift.sh
  # GH #12560/#12572: direct docs/*.md references must name files that exist.
  # The gate is existence-only (not section-anchor validation) and carries a
  # synthetic failure self-test; the live removed merge-queue reference was
  # repaired rather than allowlisted.
  run_step scripts/check-doc-links.sh
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

# These are the deliberate, machine-readable skip lines emitted by the child
# gates. Do not grep for the word "skip" anywhere: region-map also has prose
# about skipped sub-checks, and an unrelated filename or informational sentence
# must not turn a passing lane into a false failure.
#
# The LAST alternative is deliberately generic over the program name, because it
# matches the shared `require_riscv_tools_or_skip` helper in
# scripts/lib/riscv-tools.sh (#12503). Every gate that adopts that helper is then
# counted automatically. ⛔ It was not generic before, and that reopened exactly
# the hole this counting exists to close: #12503 moved
# `check-orphan-blocks.sh` and `check-fixture-reloc-targets.sh` onto the helper,
# whose miss path exits 0, while the per-gate alternatives here only named
# build-units-link / guarded-handler-bytes / asm-to-program. So a missing
# toolchain made those two exit 0 having checked nothing and this wrapper report
# `codegen: PASS (skips=0)`. For orphan-blocks that was a REGRESSION: it used to
# die loudly (`orphan_blocks: <tool> not found`, exit 1).
#
# `check-opcode-tables` (#12496) used to be a third lane gate with TWO bespoke
# wordings of its own, both listed here. #12156 moved it onto
# `scripts/lib/riscv-tools.sh`, so it now emits the SHARED miss wording matched
# by the `: skipping — RISC-V toolchain not found` alternative below, and both
# bespoke entries were removed rather than left to rot unmatched. That is the
# direction #12515 asks for: fewer per-gate patterns, because a pattern that no
# longer matches anything is indistinguishable from one that does.
#
# ⚠️ NOT YET GENERIC, deliberately. The honest end state is one rule —
# `^check-[a-z0-9-]+: .*skipping` — since every lane gate announcing a skip should
# be counted. It is not done here because that would also newly count gates whose
# skip paths I have not verified against a real CI run, and a wrong guess turns the
# whole build red for an unrelated reason. Uncounted `skipping` lines that exist
# today, for whoever takes that step: `check-embedded-counts` (reports lane),
# and outside the lanes `check-duplication`, `check-naming`,
# `check-obligation-blockers`.
SKIP_RE='^check-build-units-link: SKIP'
SKIP_RE+='|^check-(guarded-handler-bytes|asm-to-program): .*skipping \(install to enable\)'
SKIP_RE+='|^[[:space:]]+SKIP emitted-reality'
SKIP_RE+='|^[[:space:]]+skip Class-A BAL ratchet'
SKIP_RE+='|^[A-Za-z0-9_.-]+: skipping — RISC-V toolchain not found'

# Assert the pattern above still matches what the helper actually prints, by
# asking the helper itself for a miss line rather than trusting a copied string.
# A gate that stops being counted because someone reworded its skip message is
# indistinguishable from a gate that ran, so this invariant is machine-checked.
# ⚠️ Two traps here, both hit while writing this:
#  1. No pipe. Piping the helper into `head -1` makes it die of SIGPIPE, and with
#     `set -o pipefail` that status propagates out of the command substitution and
#     kills this script under `set -e` (observed: exit 141, no output, no lanes).
#  2. Ask whether ANY LINE matches, not whether the first one does. This probe must
#     pose exactly the question the lane loop poses of a lane log. Taking the first
#     line broke under `bash -x`, where xtrace output lands on the captured stderr
#     ahead of the message — a debugging run would then fail the whole wrapper.
#     `set +x` keeps the sample clean; the any-line test makes it not matter.
skip_probe="$(
  set +x
  {
    # shellcheck source=lib/riscv-tools.sh
    source scripts/lib/riscv-tools.sh
    require_riscv_tools_or_skip __skipfmt_probe __evmasm_no_such_tool
  } 2>&1 || true
)"
if ! printf '%s\n' "$skip_probe" | grep -Eq "$SKIP_RE"; then
  echo "check-build-parallel: FAIL — the skip-detection pattern no longer matches" >&2
  echo "  scripts/lib/riscv-tools.sh's miss message, so toolchain skips would be" >&2
  echo "  counted as clean runs. Update SKIP_RE (or the helper) so they agree." >&2
  printf '%s\n' "$skip_probe" | sed 's/^/  helper printed: /' >&2
  exit 1
fi

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
  skips="$(grep -Eic "$SKIP_RE" "$log" || true)"
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
