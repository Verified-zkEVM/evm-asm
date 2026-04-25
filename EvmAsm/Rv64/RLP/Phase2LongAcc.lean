/-
  EvmAsm.Rv64.RLP.Phase2LongAcc

  EL.3 Phase 2 (long form) — big-endian accumulation step.

  For a long-form RLP prefix (`0xB8..0xBF` byte string or `0xF8..0xFF` list),
  the payload length is encoded as the next `lenLen` bytes in big-endian.
  Decoding loops over those bytes, accumulating:

      length = length * 256 + next_byte

  This file defines the two-instruction arithmetic core of that loop:

      SLLI x11, x11, 8        ; length <<= 8      (i.e. length *= 256)
      ADD  x11, x11, x12      ; length += byte

  The surrounding loop (byte load, counter decrement, branch-back) is
  layered on top in a follow-up. Keeping the arithmetic step as a
  self-contained spec makes the loop proof's invariant step a direct
  application of this lemma.

  Register usage:
    x11 — accumulated length (mutated)
    x12 — input byte, assumed zero-extended (low 8 bits) (preserved)
-/

import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.AddrNorm

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (bv6_toNat_8)

-- ============================================================================
-- Program definition
-- ============================================================================

/-- Two-instruction big-endian accumulation step:
    `SLLI x11, x11, 8 ; ADD x11, x11, x12`. -/
def rlp_phase2_long_acc_prog : Program :=
  [.SLLI .x11 .x11 8, .ADD .x11 .x11 .x12]

example : rlp_phase2_long_acc_prog.length = 2 := rfl

-- ============================================================================
-- Spec
-- ============================================================================

/-- Bundled postcondition for the accumulation step: `x11` now holds
    `(length <<< 8) + byte`; `x12` is unchanged. -/
@[irreducible]
def rlp_phase2_long_acc_post (len byte : Word) : Assertion :=
  let length' := (len <<< 8) + byte
  (.x11 ↦ᵣ length') ** (.x12 ↦ᵣ byte)

theorem rlp_phase2_long_acc_post_unfold {len byte : Word} :
    rlp_phase2_long_acc_post len byte =
    ((.x11 ↦ᵣ ((len <<< 8) + byte)) ** (.x12 ↦ᵣ byte)) := by
  delta rlp_phase2_long_acc_post; rfl

/-- `cpsTriple` spec for the big-endian accumulation step. Composes SLLI
    (mutates x11 in place) with ADD rd=rs1 (folds x12 into x11).

    The caller must supply a `byte` value whose high 56 bits are zero (the
    natural result of an `LBU` load); this spec does not enforce that
    constraint, so the post `(len <<< 8) + byte` is exact BitVec arithmetic
    even if the high bits are set — only the low 8 bits are "meaningful"
    for RLP length decoding. -/
theorem rlp_phase2_long_acc_spec (len byte : Word) (base : Word) :
    cpsTriple base (base + 8)
      (CodeReq.ofProg base rlp_phase2_long_acc_prog)
      ((.x11 ↦ᵣ len) ** (.x12 ↦ᵣ byte))
      (rlp_phase2_long_acc_post len byte) := by
  simp only [rlp_phase2_long_acc_post_unfold]
  -- Reshape the code requirement: a 2-instruction `ofProg` is the disjoint
  -- union of two singletons.
  have hcr_eq : CodeReq.ofProg base rlp_phase2_long_acc_prog =
      (CodeReq.singleton base (.SLLI .x11 .x11 8)).union
      (CodeReq.singleton (base + 4) (.ADD .x11 .x11 .x12)) := by
    funext a
    simp only [rlp_phase2_long_acc_prog, CodeReq.ofProg_cons, CodeReq.ofProg_nil,
      CodeReq.union, CodeReq.empty]
    cases (CodeReq.singleton (base + 4) (.ADD .x11 .x11 .x12)) a <;> rfl
  rw [hcr_eq]
  -- Disjointness of the two singletons (distinct PCs).
  have hd : CodeReq.Disjoint
      (CodeReq.singleton base (.SLLI .x11 .x11 8))
      (CodeReq.singleton (base + 4) (.ADD .x11 .x11 .x12)) :=
    CodeReq.Disjoint.singleton (by bv_omega)
  -- Step 1: SLLI x11, x11, 8 — use `slli_spec_gen_same` (rd = rs1),
  -- then frame with x12 to bring it into scope.
  have s1Base := slli_spec_gen_same .x11 len 8 base (by nofun)
  have s1 : cpsTriple base (base + 4)
      (CodeReq.singleton base (.SLLI .x11 .x11 8))
      ((.x11 ↦ᵣ len) ** (.x12 ↦ᵣ byte))
      ((.x11 ↦ᵣ (len <<< (8 : BitVec 6).toNat)) ** (.x12 ↦ᵣ byte)) :=
    cpsTriple_frameR (.x12 ↦ᵣ byte) (by pcFree) s1Base
  -- Step 2: ADD x11, x11, x12 — `add_spec_gen_rd_eq_rs1` (rd = rs1 = x11,
  -- rs2 = x12). No framing needed.
  have s2 := add_spec_gen_rd_eq_rs1 .x11 .x12
    (len <<< (8 : BitVec 6).toNat) byte (base + 4) (by nofun)
  rw [show (base + 4 : Word) + 4 = base + 8 from by bv_omega] at s2
  -- Compose. `(8 : BitVec 6).toNat = 8` so the result matches.
  rw [bv6_toNat_8] at s1
  exact cpsTriple_seq hd s1 s2

/-! ## Concrete sanity checks -/

-- One accumulation step starting from 0: length = 0 * 256 + byte = byte.
example : (((0 : Word) <<< 8) + (0x42 : Word)) = (0x42 : Word) := by decide

-- Accumulating 2 bytes (0x01, 0x00) gives 0x100 = 256.
example : ((((0 : Word) <<< 8) + (0x01 : Word)) <<< 8) + (0x00 : Word) =
    (0x100 : Word) := by decide

-- Accumulating 3 bytes (0x01, 0x02, 0x03) gives 0x010203 = 66051.
example : (((((0 : Word) <<< 8) + (0x01 : Word)) <<< 8) + (0x02 : Word)) <<< 8 +
    (0x03 : Word) = (0x010203 : Word) := by decide

end EvmAsm.Rv64.RLP
