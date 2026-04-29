/-
  EvmAsm.Rv64.RLP.Phase2LongLoopThree

  EL.3 Phase 2 (long form) — three-iteration closure of the loop body.

  Specializes `rlp_phase2_long_loop_body_spec` (#333) at `x14 = 3`,
  composed with `rlp_phase2_long_loop_two_byte_spec` (#336) for the
  remaining two iterations. Execution:

      iter 1 @ base → state at base (BNE taken, cnt 3→2)
      iter 2+3 @ base (via two-byte closure) → state at base + 24

  Produces a `cpsTriple` from `base` to `base + 24` that decodes three
  big-endian bytes. Corresponds to RLP prefixes `0xBA` and `0xFA`
  (`lenLen = 3`).

  Memory model: all three bytes (`mem[ptr]`, `mem[ptr + 1]`,
  `mem[ptr + 2]`) are assumed to live in the same doubleword at
  `dwordAddr`. Cross-doubleword reads are a future refinement.
-/

import EvmAsm.Rv64.RLP.Phase2LongLoopTwo

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64

-- ============================================================================
-- Spec
-- ============================================================================

/-- Bundled post for the three-iteration loop closure: registers in the
    "three iterations done" state, `x14 = 0`, three bytes folded into
    `x11` in big-endian order. -/
@[irreducible]
def rlp_phase2_long_loop_three_byte_post
    (len ptr byte1 byte2 byte3 wordVal dwordAddr : Word) : Assertion :=
  let length' := ((((len <<< 8) + byte1) <<< 8 + byte2) <<< 8) + byte3
  let ptr'    := ptr + 3
  (.x11 ↦ᵣ length') ** (.x13 ↦ᵣ ptr') ** (.x14 ↦ᵣ (0 : Word)) **
    (.x12 ↦ᵣ byte3) ** (.x0 ↦ᵣ (0 : Word)) **
    (dwordAddr ↦ₘ wordVal)

theorem rlp_phase2_long_loop_three_byte_post_unfold
    (len ptr byte1 byte2 byte3 wordVal dwordAddr : Word) :
    rlp_phase2_long_loop_three_byte_post len ptr byte1 byte2 byte3 wordVal
        dwordAddr =
    ((.x11 ↦ᵣ ((((len <<< 8) + byte1) <<< 8 + byte2) <<< 8 + byte3)) **
     (.x13 ↦ᵣ (ptr + 3)) **
     (.x14 ↦ᵣ (0 : Word)) **
     (.x12 ↦ᵣ byte3) ** (.x0 ↦ᵣ (0 : Word)) **
     (dwordAddr ↦ₘ wordVal)) := by
  delta rlp_phase2_long_loop_three_byte_post; rfl

/-- `cpsTriple` spec for the three-iteration (lenLen = 3) closure of
    the long-form length loop.

    The first iteration runs at `cnt = 3` (BNE taken back to `base` with
    `cnt' = 2 ≠ 0`); the remaining two iterations are folded into
    `rlp_phase2_long_loop_two_byte_spec` (#336). -/
theorem rlp_phase2_long_loop_three_byte_spec
    (len ptr v12Old wordVal dwordAddr : Word)
    (base : Word) (back : BitVec 13)
    (halign1 : alignToDword ptr = dwordAddr)
    (halign2 : alignToDword (ptr + 1) = dwordAddr)
    (halign3 : alignToDword (ptr + 2) = dwordAddr)
    (hvalid1 : isValidByteAccess ptr = true)
    (hvalid2 : isValidByteAccess (ptr + 1) = true)
    (hvalid3 : isValidByteAccess (ptr + 2) = true)
    (hback : (base + 20) + signExtend13 back = base) :
    cpsTriple base (base + 24)
      (CodeReq.ofProg base (rlp_phase2_long_loop_body_prog back))
      ((.x11 ↦ᵣ len) ** (.x13 ↦ᵣ ptr) ** (.x14 ↦ᵣ (3 : Word)) **
       (.x12 ↦ᵣ v12Old) ** (.x0 ↦ᵣ (0 : Word)) **
       (dwordAddr ↦ₘ wordVal))
      (rlp_phase2_long_loop_three_byte_post len ptr
        ((extractByte wordVal (byteOffset ptr)).zeroExtend 64)
        ((extractByte wordVal (byteOffset (ptr + 1))).zeroExtend 64)
        ((extractByte wordVal (byteOffset (ptr + 2))).zeroExtend 64)
        wordVal dwordAddr) := by
  simp only [rlp_phase2_long_loop_three_byte_post_unfold]
  -- Iter 1: body spec at cnt = 3. cnt' = 2.
  have body := rlp_phase2_long_loop_body_spec len ptr (3 : Word) v12Old
    wordVal dwordAddr base back halign1 hvalid1
  have hcnt' : (3 : Word) + signExtend12 (-1 : BitVec 12) = (2 : Word) := by
    decide
  rw [hcnt'] at body
  -- The fall-through carries `⌜(2 : Word) = 0⌝`, which is False.
  set byte1 := (extractByte wordVal (byteOffset ptr)).zeroExtend 64
  have h_absurd : ∀ hp,
      rlp_phase2_long_loop_body_post len ptr (3 : Word) byte1 wordVal
         dwordAddr ((2 : Word) = 0) hp → False := fun hp hpost =>
    absurd (rlp_phase2_long_loop_body_post_pure hp hpost) (by decide)
  have tri1 := cpsBranch_takenPath body h_absurd
  rw [hback] at tri1
  -- Weaken: unfold @[irreducible] + strip trailing `⌜(2 : Word) ≠ 0⌝`.
  have tri1' : cpsTriple base base
      (CodeReq.ofProg base (rlp_phase2_long_loop_body_prog back))
      ((.x11 ↦ᵣ len) ** (.x13 ↦ᵣ ptr) ** (.x14 ↦ᵣ (3 : Word)) **
       (.x12 ↦ᵣ v12Old) ** (.x0 ↦ᵣ (0 : Word)) **
       (dwordAddr ↦ₘ wordVal))
      ((.x11 ↦ᵣ ((len <<< 8) + byte1)) ** (.x13 ↦ᵣ (ptr + 1)) **
       (.x14 ↦ᵣ (2 : Word)) ** (.x12 ↦ᵣ byte1) **
       (.x0 ↦ᵣ (0 : Word)) ** (dwordAddr ↦ₘ wordVal)) :=
    cpsTriple_weaken
      (fun _ hp => hp)
      (fun h hp => by
        simp only [rlp_phase2_long_loop_body_post_unfold] at hp
        refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right ?_)))) h hp
        intro h' hp'
        exact ((sepConj_pure_right _).1 hp').1)
      tri1
  -- Iter 2+3: two-byte closure starting at base with ptr+1, cnt = 2.
  have two_byte := rlp_phase2_long_loop_two_byte_spec ((len <<< 8) + byte1)
    (ptr + 1) byte1 wordVal dwordAddr base back
    halign2
    (by rw [show (ptr + 1 : Word) + 1 = ptr + 2 from by bv_omega]; exact halign3)
    hvalid2
    (by rw [show (ptr + 1 : Word) + 1 = ptr + 2 from by bv_omega]; exact hvalid3)
    hback
  simp only [rlp_phase2_long_loop_two_byte_post_unfold] at two_byte
  -- Address normalisation inside two_byte: `(ptr + 1) + 1 = ptr + 2`, etc.
  have h_ptr_2 : (ptr + 1 : Word) + 1 = ptr + 2 := by bv_omega
  have h_ptr_3 : (ptr + 1 : Word) + 2 = ptr + 3 := by bv_omega
  rw [h_ptr_2, h_ptr_3] at two_byte
  have composed :=
    cpsTriple_seq_perm_same_cr
      (fun h hp => by xperm_hyp hp) tri1' two_byte
  exact cpsTriple_weaken
    (fun _ hp => hp)
    (fun h hp => by xperm_hyp hp)
    composed

end EvmAsm.Rv64.RLP
