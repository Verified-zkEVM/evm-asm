/-
  EvmAsm.Rv64.RLP.Phase3SingleByte

  EL.3 Phase 3 (single-byte exit): the trivial flat-decode case.

  When Phase 1's classifier reaches `e1` — i.e. the prefix byte `p < 0x80` —
  the RLP item is a *single-byte string* whose data is the prefix byte
  itself. The flat-decode output is therefore:

      length   = 1
      data_ptr = input_ptr   (unchanged: the prefix byte at `mem[ptr]`
                              IS the entire data payload)

  This file provides the one-instruction spec that materializes the
  length in `x11`. The data pointer in `x13` is preserved as a frame.

  Register usage:
    x11 — output: payload length (= 1 after this step)
    x0  — zero register (unchanged)

  This is the smallest of the six Phase 3 exits; the other four
  (short string, long string, short/long list error) follow in
  separate files.
-/

import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.Tactics.XSimp

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.Rv64.Tactics

-- ============================================================================
-- Program definition
-- ============================================================================

/-- One-instruction "set length = 1" emitter for the single-byte exit:
    `ADDI x11, x0, 1`. -/
def rlp_phase3_single_byte_prog : Program :=
  [.ADDI .x11 .x0 1]

example : rlp_phase3_single_byte_prog.length = 1 := rfl

-- ============================================================================
-- Spec
-- ============================================================================

/-- `cpsTripleWithin` spec for the single-byte length emitter. After the one
    instruction, `x11 = 1`. `x0` stays zero (RISC-V invariant); the caller
    is expected to keep its data pointer (typically in `x13`) framed
    through this step.

    The triple does not name `x13` — the caller owns it as a frame
    atom and threads it through unchanged via `cpsTriple_frameR`. -/
theorem rlp_phase3_single_byte_spec_within (v11Old : Word) (base : Word) :
    cpsTripleWithin 1 base (base + 4)
      (CodeReq.ofProg base rlp_phase3_single_byte_prog)
      ((.x11 ↦ᵣ v11Old) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x11 ↦ᵣ (1 : Word)) ** (.x0 ↦ᵣ (0 : Word))) := by
  -- The one-instruction `ofProg` reduces to a singleton CodeReq.
  rw [show CodeReq.ofProg base rlp_phase3_single_byte_prog =
      CodeReq.singleton base (.ADDI .x11 .x0 1) from CodeReq.ofProg_singleton]
  -- ADDI x11, x0, 1: x11 ← 0 + signExtend12 1 = 1.
  have h := addi_spec_gen_within .x11 .x0 v11Old (0 : Word) 1 base (by nofun)
  -- Normalize the post: 0 + signExtend12 1 = 1.
  have hsig : (0 : Word) + signExtend12 (1 : BitVec 12) = (1 : Word) := by decide
  rw [hsig] at h
  -- `addi_spec_gen` produces `(rs1 ↦ᵣ ...) ** (rd ↦ᵣ ...)` (rs1 first);
  -- the spec statement uses `(rd ↦ᵣ ...) ** (rs1 ↦ᵣ ...)`. Permute.
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp)
    h

example : rlp_phase3_single_byte_prog =
    [.ADDI .x11 .x0 1] := rfl

end EvmAsm.Rv64.RLP
