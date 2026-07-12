/-
  EvmAsm.Codegen.Programs.SparseEpochProbe

  `zisk_sparse_epoch_probe` — same-depth-sibling aliasing witness for the
  sparse memory store's epoch-aware scans (bead evm-asm-m8pdu).

  Scenario: sibling frame A enters depth 1 (via the real `call_frame_enter`,
  which stamps a fresh depth-epoch), performs a beyond-dense sparse MSTORE at
  offset 0xa0000 (the real `sparseMemoryStoreWordAsm` scan code), and returns
  (depth pops to 0). Sibling frame B then enters depth 1 (fresh epoch) and
  reads offset 0xa0000 three ways: the real `sparseMemoryLoadWordAsm` scan,
  `sparse_window_read`, and (after writing its own entries) the write-back
  scan inside `sparse_window_write`. A third sibling C repeats the stale-read
  check against B's write-back entry.

  Per execution-specs, a frame's memory starts EMPTY: B and C must read
  ZEROS at offsets only a returned sibling wrote. Pre-fix (scans matched on
  raw depth) the stale sibling entry shadows and the reads return the
  sibling's bytes; post-fix (scans match the (epoch << 16) | depth tag) they
  return zeros, while same-frame reads still see their own writes.

  Output (OUTPUT_ADDR = 0xa0010000):
    +0   sparse entry count after A's store          (expect 1)
    +8   B's MLOAD-scan result, limb 0               (expect 0; pre-fix 0x7777…)
    +16  B's sparse_window_read result, first 8 B    (expect 0; pre-fix 0x7777…)
    +24  B's OWN store → MLOAD-scan readback, limb 0 (expect 0x4242… both)
    +32  B's OWN store → window-read, first 8 B      (expect 0x4242… both)
    +40  B's sparse_window_write → MLOAD-scan, limb 0 (expect 0x9999… both)
    +48  C's stale MLOAD-scan of B's write-back entry (expect 0; pre-fix 0x9999…)
-/

import EvmAsm.Codegen.Programs.EvmMemoryHandlers
import EvmAsm.Codegen.Programs.CallFrameDescend
import EvmAsm.Codegen.Programs.CallFrameReturn

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-- Load a 64-bit immediate pattern via lui/slli composition-free path:
    emit `li` (the assembler expands). -/
private def sepEnterSibling : String :=
  -- call_frame_enter(a0 = 1): stamps evm_sparse_memory_epoch_by_depth[1] with
  -- a fresh epoch and zero-inits the depth-1 dense frame; then set
  -- evm_call_depth = 1 (the descend normally does this via frame_depth_push).
  "  li a0, 1\n" ++
  "  jal ra, call_frame_enter\n" ++
  "  la t0, evm_call_depth\n" ++
  "  li t1, 1\n" ++
  "  sd t1, 0(t0)\n"

/-- Stage a fake EVM stack word pair at `stackLabel`: offset word = `off`
    (low limb only), value word = 4 × `pat` limbs; leave x12 = stackLabel,
    x15 = off (the handler scan entry contract). -/
private def sepStageStack (stackLabel : String) (off : Nat) (pat : String) : String :=
  "  la x12, " ++ stackLabel ++ "\n" ++
  "  li t0, " ++ toString off ++ "\n" ++
  "  sd t0, 0(x12)\n" ++
  "  sd x0, 8(x12)\n  sd x0, 16(x12)\n  sd x0, 24(x12)\n" ++
  (if pat == "" then "" else
    "  li t0, " ++ pat ++ "\n" ++
    "  sd t0, 32(x12)\n  sd t0, 40(x12)\n  sd t0, 48(x12)\n  sd t0, 56(x12)\n") ++
  "  ld x15, 0(x12)\n"

def sparseEpochProbePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li s0, 0xa0010000\n" ++
  -- ---- Sibling A @ depth 1: sparse MSTORE(0xa0000, 0x77…) ----
  sepEnterSibling ++
  sepStageStack "sep_stack_a" 0xa0000 "0x7777777777777777" ++
  "  jal x1, sep_store\n" ++
  "  la t0, evm_sparse_memory_count\n  ld t1, 0(t0)\n  sd t1, 0(s0)\n" ++
  -- A returns: depth pops to 0 (frame_return does this in the real guest).
  "  la t0, evm_call_depth\n  sd x0, 0(t0)\n" ++
  -- ---- Sibling B @ depth 1 (fresh epoch): stale reads of A's offset ----
  sepEnterSibling ++
  sepStageStack "sep_stack_b" 0xa0000 "" ++
  "  jal x1, sep_load\n" ++
  "  ld t1, 0(x12)\n  sd t1, 8(s0)\n" ++
  "  la a0, sep_win\n  li a1, 0xa0000\n  li a2, 32\n  la a3, call_frame_arena\n" ++
  "  jal ra, sparse_window_read\n" ++
  "  la t0, sep_win\n  ld t1, 0(t0)\n  sd t1, 16(s0)\n" ++
  -- ---- B's own store → both readers must still see it (no over-fix) ----
  sepStageStack "sep_stack_c" 0xa0000 "0x4242424242424242" ++
  "  jal x1, sep_store\n" ++
  sepStageStack "sep_stack_d" 0xa0000 "" ++
  "  jal x1, sep_load\n" ++
  "  ld t1, 0(x12)\n  sd t1, 24(s0)\n" ++
  "  la a0, sep_win\n  li a1, 0xa0000\n  li a2, 32\n  la a3, call_frame_arena\n" ++
  "  jal ra, sparse_window_read\n" ++
  "  la t0, sep_win\n  ld t1, 0(t0)\n  sd t1, 32(s0)\n" ++
  -- ---- B's sparse_window_write(0xa0040, 32) → own MLOAD-scan sees it ----
  "  la t0, sep_src\n  li t1, 0x9999999999999999\n" ++
  "  sd t1, 0(t0)\n  sd t1, 8(t0)\n  sd t1, 16(t0)\n  sd t1, 24(t0)\n" ++
  "  la a0, sep_src\n  li a1, 0xa0040\n  li a2, 32\n  la a3, call_frame_arena\n  li a4, 1\n" ++
  "  jal ra, sparse_window_write\n" ++
  sepStageStack "sep_stack_e" 0xa0040 "" ++
  "  jal x1, sep_load\n" ++
  "  ld t1, 0(x12)\n  sd t1, 40(s0)\n" ++
  -- B returns.
  "  la t0, evm_call_depth\n  sd x0, 0(t0)\n" ++
  -- ---- Sibling C @ depth 1 (fresh epoch): stale read of B's write-back ----
  sepEnterSibling ++
  sepStageStack "sep_stack_f" 0xa0040 "" ++
  "  jal x1, sep_load\n" ++
  "  ld t1, 0(x12)\n  sd t1, 48(s0)\n" ++
  "  j .Lsep_done\n" ++
  -- Handler-scan wrappers: the REAL emitted scan code (same Lean defs the
  -- guest registry instantiates), callable via `jal x1`. The sparse path
  -- `ret`s from its own tail; the dense fallthrough label (never taken —
  -- 0xa00xx + 32 > the 0x20000 depth-1 limit) falls into an explicit `ret`.
  "sep_store:\n" ++
  sparseMemoryStoreWordAsm "sepp" ++
  "  ret\n" ++
  "sep_load:\n" ++
  sparseMemoryLoadWordAsm "sepp" ++
  "  ret\n" ++
  -- Capacity-overflow target (never reached: the probe appends ≤ 4 entries).
  ".exit_outofgas:\n" ++
  "  li t0, 0xdead\n  sd t0, 56(s0)\n" ++
  "  j .Lsep_done\n" ++
  frameBaseFunction ++ "\n" ++
  callFrameEnterFunction ++ "\n" ++
  sparseWindowReadFunction ++ "\n" ++
  sparseWindowWriteFunction ++ "\n" ++
  -- Execution resumes here (falls through to the unit body/halt).
  ".Lsep_done:\n"

def sparseEpochProbeDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "evm_call_depth:\n  .zero 8\n" ++
  "evm_sparse_memory_count:\n  .zero 8\n" ++
  "evm_sparse_memory_next_epoch:\n  .dword 1\n" ++
  "evm_sparse_memory_epoch_by_depth:\n  .zero " ++ toString (1025 * 8) ++ "\n" ++
  "evm_sparse_memory_entries:\n  .zero " ++ toString (4096 * 56) ++ "\n" ++
  ".balign 32\n" ++
  "call_frame_arena:\n  .zero " ++ toString (0x39000 : Nat) ++ "\n" ++
  ".balign 32\n" ++
  "sep_stack_a:\n  .zero 64\n" ++
  "sep_stack_b:\n  .zero 64\n" ++
  "sep_stack_c:\n  .zero 64\n" ++
  "sep_stack_d:\n  .zero 64\n" ++
  "sep_stack_e:\n  .zero 64\n" ++
  "sep_stack_f:\n  .zero 64\n" ++
  "sep_win:\n  .zero 64\n" ++
  "sep_src:\n  .zero 64\n" ++
  ".balign 8\n" ++
  "sep_tail_pad:\n  .byte 0xde, 0xad, 0xbe, 0xef, 0xde, 0xad, 0xbe, 0xef\n"

def ziskSparseEpochProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := sparseEpochProbePrologue
  dataAsm     := sparseEpochProbeDataSection
}

end EvmAsm.Codegen
