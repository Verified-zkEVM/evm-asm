import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.BalRlpEncode
import EvmAsm.Codegen.Programs.BalCanonicalSort
import EvmAsm.Codegen.Programs.KeccakIncremental
import EvmAsm.Codegen.Programs.HashBridge

/-!
# `zisk_bal_selftests` -- run the two BAL self-tests that have never executed

`bal_rlp_encode_selftest` (15 per-case assertions) and `bal_canonical_sort_selftest`
(three row sets) are referenced only inside their own defining files: zero callers, no
build unit, no script, no workflow. They have never run. GH #10754 covers the general
form -- `check-build-units-link.sh` asserts that units LINK, so a linkage gate stands
where a behaviour gate is assumed.

These are therefore UNVALIDATED TESTS, not a safety net being switched on. A case that
has never run has never been debugged either, so a failure here is information about the
test vector as much as about the code, and the first-run counts are reported as measured.

Both self-tests return 0 on pass and a nonzero case identifier on failure:
`bal_rlp_encode_selftest` returns `100 + case index`, `bal_canonical_sort_selftest`
returns the failing row-set number. Those codes are published rather than collapsed to a
boolean, because "which case" is the entire diagnostic value.
-/

namespace EvmAsm.Codegen

open EvmAsm.Rv64

def ziskBalSelftestsPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li s0, 0xa0010000\n" ++
  -- a0 = scratch (>= 33 bytes), a1 = keccak ctx, a2 = 32-byte field work area
  -- Seed both output slots with a sentinel neither self-test can return, so a fault
  -- before the stores reads as 0xdead rather than as two clean zeros.
  "  li t0, 0xdead; sd t0, 0(s0); sd t0, 8(s0)\n" ++
  "  la a0, bslf_scratch; la a1, bslf_ctx; la a2, bslf_field\n" ++
  "  jal ra, bal_rlp_encode_selftest\n" ++
  "  sd a0, 0(s0)\n" ++
  -- a0 = a scratch arena of at least 4 * 128 bytes, 8-aligned. Passing nothing here
  -- leaves a0 holding the PREVIOUS self-test's return value, which is 0 on pass, so
  -- the sorter stores to address 0 and faults -- and the two output slots then read
  -- back as the untouched buffer, i.e. two zeros, i.e. two passes.
  "  la a0, bslf_sort_arena\n" ++
  "  jal ra, bal_canonical_sort_selftest\n" ++
  "  sd a0, 8(s0)\n" ++
  "  j .Lbslf_done\n" ++
  keccakIncrementalFunctions ++
  zkvmKeccak256Function ++ "\n" ++
  balRlpEncodeFunctions ++
  -- Only the sorter and its self-test. The full `balCanonicalSortFunctions` aggregate
  -- also carries the storage- and account-write sorters, which reference
  -- `storage_writes_count` and would drag the whole write-map arena into a probe that
  -- does not use it.
  balCanonicalSortFunction ++
  balCanonicalSortSelftestFunction ++
  ".Lbslf_done:"

def ziskBalSelftestsDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "bslf_scratch:\n  .zero 256\n" ++
  "bslf_ctx:\n  .zero 512\n" ++
  "bslf_field:\n  .zero 64\n" ++
  -- `zkvm_keccak256`'s 200-byte sponge state. Declared here rather than pulling in
  -- AccountApplyStorage's data section, which carries arenas this probe never touches.
  ".balign 8\n" ++
  "zk3_state:\n  .zero 200\n" ++
  ".balign 8\n" ++
  "bslf_sort_arena:\n  .zero 512\n" ++
  keccakIncrementalDataSection ++
  balCanonicalSortDataSection

def ziskBalSelftestsProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBalSelftestsPrologue
  dataAsm     := ziskBalSelftestsDataSection
}

/-! ## Guards -/

-- Both self-tests must actually be CALLED. Splicing their bodies in without calling them
-- links cleanly and reports two zeros -- which reads as two passes.
#guard (ziskBalSelftestsPrologue.splitOn "jal ra, bal_rlp_encode_selftest").length == 2
#guard (ziskBalSelftestsPrologue.splitOn "jal ra, bal_canonical_sort_selftest").length == 2

-- Two DISTINCT output slots. Publishing both to the same offset makes the second
-- silently overwrite the first, and one zero would stand for two passes.
#guard (ziskBalSelftestsPrologue.splitOn "sd a0, 0(s0)").length == 2

-- The sort self-test takes a 4*128-byte arena in a0. Without this it inherits the
-- previous return value and faults on a store to 0.
#guard (ziskBalSelftestsPrologue.splitOn "la a0, bslf_sort_arena").length == 2

-- Sentinel seeding: a fault before the stores must not read back as two passes.
#guard (ziskBalSelftestsPrologue.splitOn "li t0, 0xdead; sd t0, 0(s0); sd t0, 8(s0)").length == 2
#guard (ziskBalSelftestsPrologue.splitOn "sd a0, 8(s0)").length == 2

end EvmAsm.Codegen
