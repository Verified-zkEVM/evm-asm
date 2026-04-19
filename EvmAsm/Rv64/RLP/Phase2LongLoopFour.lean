/-
  EvmAsm.Rv64.RLP.Phase2LongLoopFour

  EL.3 Phase 2 (long form) — four-iteration closure of the loop body.

  Specializes `rlp_phase2_long_loop_body_spec` (#333) at `x14 = 4`,
  composed with `rlp_phase2_long_loop_three_byte_spec` (#337) for the
  remaining three iterations.

  Corresponds to RLP prefixes `0xBB` and `0xFB` (`lenLen = 4`).

  Memory model: all four bytes assumed in the same doubleword. This
  holds whenever `byteOffset ptr ≤ 4`, i.e., the four bytes fit within
  the 8-byte block containing `ptr`.
-/

import EvmAsm.Rv64.RLP.Phase2LongLoopThree

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64

-- ============================================================================
-- Spec
-- ============================================================================

/-- Bundled post for the four-iteration loop closure. -/
@[irreducible]
def rlp_phase2_long_loop_four_byte_post
    (len ptr byte1 byte2 byte3 byte4 word_val dwordAddr : Word) : Assertion :=
  let length' :=
    ((((((len <<< 8) + byte1) <<< 8) + byte2) <<< 8) + byte3) <<< 8 + byte4
  let ptr'    := ptr + 4
  (.x11 ↦ᵣ length') ** (.x13 ↦ᵣ ptr') ** (.x14 ↦ᵣ (0 : Word)) **
    (.x12 ↦ᵣ byte4) ** (.x0 ↦ᵣ (0 : Word)) **
    (dwordAddr ↦ₘ word_val)

theorem rlp_phase2_long_loop_four_byte_post_unfold
    (len ptr byte1 byte2 byte3 byte4 word_val dwordAddr : Word) :
    rlp_phase2_long_loop_four_byte_post len ptr byte1 byte2 byte3 byte4
        word_val dwordAddr =
    ((.x11 ↦ᵣ (((((len <<< 8) + byte1) <<< 8 + byte2) <<< 8 + byte3) <<< 8
               + byte4)) **
     (.x13 ↦ᵣ (ptr + 4)) **
     (.x14 ↦ᵣ (0 : Word)) **
     (.x12 ↦ᵣ byte4) ** (.x0 ↦ᵣ (0 : Word)) **
     (dwordAddr ↦ₘ word_val)) := by
  delta rlp_phase2_long_loop_four_byte_post; rfl

/-- `cpsTriple` spec for the four-iteration (lenLen = 4) closure.

    Iter 1 (cnt 4→3, BNE taken) + three-byte closure (iters 2–4). -/
theorem rlp_phase2_long_loop_four_byte_spec
    (len ptr v12_old word_val dwordAddr : Word)
    (base : Word) (back : BitVec 13)
    (halign1 : alignToDword ptr = dwordAddr)
    (halign2 : alignToDword (ptr + 1) = dwordAddr)
    (halign3 : alignToDword (ptr + 2) = dwordAddr)
    (halign4 : alignToDword (ptr + 3) = dwordAddr)
    (hvalid1 : isValidByteAccess ptr = true)
    (hvalid2 : isValidByteAccess (ptr + 1) = true)
    (hvalid3 : isValidByteAccess (ptr + 2) = true)
    (hvalid4 : isValidByteAccess (ptr + 3) = true)
    (hback : (base + 20) + signExtend13 back = base) :
    cpsTriple base (base + 24)
      (CodeReq.ofProg base (rlp_phase2_long_loop_body_prog back))
      ((.x11 ↦ᵣ len) ** (.x13 ↦ᵣ ptr) ** (.x14 ↦ᵣ (4 : Word)) **
       (.x12 ↦ᵣ v12_old) ** (.x0 ↦ᵣ (0 : Word)) **
       (dwordAddr ↦ₘ word_val))
      (rlp_phase2_long_loop_four_byte_post len ptr
        ((extractByte word_val (byteOffset ptr)).zeroExtend 64)
        ((extractByte word_val (byteOffset (ptr + 1))).zeroExtend 64)
        ((extractByte word_val (byteOffset (ptr + 2))).zeroExtend 64)
        ((extractByte word_val (byteOffset (ptr + 3))).zeroExtend 64)
        word_val dwordAddr) := by
  simp only [rlp_phase2_long_loop_four_byte_post_unfold]
  -- Iter 1: body at cnt = 4. cnt' = 3.
  have body := rlp_phase2_long_loop_body_spec len ptr (4 : Word) v12_old
    word_val dwordAddr base back halign1 hvalid1
  have hcnt' : (4 : Word) + signExtend12 (-1 : BitVec 12) = (3 : Word) := by
    decide
  rw [hcnt'] at body
  set byte1 := (extractByte word_val (byteOffset ptr)).zeroExtend 64
  have h_absurd : ∀ hp,
      rlp_phase2_long_loop_body_post len ptr (4 : Word) byte1 word_val
         dwordAddr ((3 : Word) = 0) hp → False := by
    intro hp hpost
    simp only [rlp_phase2_long_loop_body_post_unfold] at hpost
    obtain ⟨_, _, _, _, _, hpost⟩ := hpost
    obtain ⟨_, _, _, _, _, hpost⟩ := hpost
    obtain ⟨_, _, _, _, _, hpost⟩ := hpost
    obtain ⟨_, _, _, _, _, hpost⟩ := hpost
    obtain ⟨_, _, _, _, _, hpost⟩ := hpost
    obtain ⟨_, _, _, _, _, hpost⟩ := hpost
    exact absurd hpost.2 (by decide)
  have tri1 := cpsBranch_takenPath body h_absurd
  rw [hback] at tri1
  have tri1' : cpsTriple base base
      (CodeReq.ofProg base (rlp_phase2_long_loop_body_prog back))
      ((.x11 ↦ᵣ len) ** (.x13 ↦ᵣ ptr) ** (.x14 ↦ᵣ (4 : Word)) **
       (.x12 ↦ᵣ v12_old) ** (.x0 ↦ᵣ (0 : Word)) **
       (dwordAddr ↦ₘ word_val))
      ((.x11 ↦ᵣ ((len <<< 8) + byte1)) ** (.x13 ↦ᵣ (ptr + 1)) **
       (.x14 ↦ᵣ (3 : Word)) ** (.x12 ↦ᵣ byte1) **
       (.x0 ↦ᵣ (0 : Word)) ** (dwordAddr ↦ₘ word_val)) :=
    cpsTriple_weaken
      (fun _ hp => hp)
      (fun h hp => by
        simp only [rlp_phase2_long_loop_body_post_unfold] at hp
        refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right ?_)))) h hp
        intro h' hp'
        exact ((sepConj_pure_right _ _ _).1 hp').1)
      tri1
  -- Iters 2-4: three-byte closure at base with (ptr+1, cnt=3).
  have three_byte := rlp_phase2_long_loop_three_byte_spec ((len <<< 8) + byte1)
    (ptr + 1) byte1 word_val dwordAddr base back
    halign2
    (by rw [show (ptr + 1 : Word) + 1 = ptr + 2 from by bv_omega]; exact halign3)
    (by rw [show (ptr + 1 : Word) + 2 = ptr + 3 from by bv_omega]; exact halign4)
    hvalid2
    (by rw [show (ptr + 1 : Word) + 1 = ptr + 2 from by bv_omega]; exact hvalid3)
    (by rw [show (ptr + 1 : Word) + 2 = ptr + 3 from by bv_omega]; exact hvalid4)
    hback
  simp only [rlp_phase2_long_loop_three_byte_post_unfold] at three_byte
  have h_ptr_2 : (ptr + 1 : Word) + 1 = ptr + 2 := by bv_omega
  have h_ptr_3 : (ptr + 1 : Word) + 2 = ptr + 3 := by bv_omega
  have h_ptr_4 : (ptr + 1 : Word) + 3 = ptr + 4 := by bv_omega
  rw [h_ptr_2, h_ptr_3, h_ptr_4] at three_byte
  have composed :=
    cpsTriple_seq_with_perm_same_cr base base (base + 24) _ _ _ _ _
      (fun h hp => by xperm_hyp hp) tri1' three_byte
  exact cpsTriple_weaken
    (fun _ hp => hp)
    (fun h hp => by xperm_hyp hp)
    composed

end EvmAsm.Rv64.RLP
