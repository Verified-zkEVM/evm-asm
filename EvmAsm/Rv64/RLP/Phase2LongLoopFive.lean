/-
  EvmAsm.Rv64.RLP.Phase2LongLoopFive

  EL.3 Phase 2 (long form) — five-iteration closure of the loop body.

  Specializes `rlp_phase2_long_loop_body_spec` at `x14 = 5`, composed
  with `rlp_phase2_long_loop_four_byte_spec` (#339) for the remaining
  four iterations.

  Corresponds to RLP prefixes `0xBC` and `0xFC` (`lenLen = 5`).

  Memory model: all five bytes assumed in the same doubleword. Holds
  whenever `byteOffset ptr ≤ 3`.
-/

import EvmAsm.Rv64.RLP.Phase2LongLoopFour

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64

-- ============================================================================
-- Spec
-- ============================================================================

/-- Bundled post for the five-iteration loop closure. -/
@[irreducible]
def rlp_phase2_long_loop_five_byte_post
    (len ptr byte1 byte2 byte3 byte4 byte5 wordVal dwordAddr : Word) :
    Assertion :=
  let length' :=
    (((((((len <<< 8) + byte1) <<< 8) + byte2) <<< 8) + byte3) <<< 8
      + byte4) <<< 8 + byte5
  let ptr'    := ptr + 5
  (.x11 ↦ᵣ length') ** (.x13 ↦ᵣ ptr') ** (.x14 ↦ᵣ (0 : Word)) **
    (.x12 ↦ᵣ byte5) ** (.x0 ↦ᵣ (0 : Word)) **
    (dwordAddr ↦ₘ wordVal)

theorem rlp_phase2_long_loop_five_byte_post_unfold
    (len ptr byte1 byte2 byte3 byte4 byte5 wordVal dwordAddr : Word) :
    rlp_phase2_long_loop_five_byte_post len ptr byte1 byte2 byte3 byte4 byte5
        wordVal dwordAddr =
    ((.x11 ↦ᵣ ((((((len <<< 8) + byte1) <<< 8 + byte2) <<< 8 + byte3) <<< 8
                + byte4) <<< 8 + byte5)) **
     (.x13 ↦ᵣ (ptr + 5)) **
     (.x14 ↦ᵣ (0 : Word)) **
     (.x12 ↦ᵣ byte5) ** (.x0 ↦ᵣ (0 : Word)) **
     (dwordAddr ↦ₘ wordVal)) := by
  delta rlp_phase2_long_loop_five_byte_post; rfl

/-- `cpsTriple` spec for the five-iteration (lenLen = 5) closure.

    Iter 1 (cnt 5→4, BNE taken) + four-byte closure (iters 2–5). -/
theorem rlp_phase2_long_loop_five_byte_spec
    (len ptr v12_old wordVal dwordAddr : Word)
    (base : Word) (back : BitVec 13)
    (halign1 : alignToDword ptr = dwordAddr)
    (halign2 : alignToDword (ptr + 1) = dwordAddr)
    (halign3 : alignToDword (ptr + 2) = dwordAddr)
    (halign4 : alignToDword (ptr + 3) = dwordAddr)
    (halign5 : alignToDword (ptr + 4) = dwordAddr)
    (hvalid1 : isValidByteAccess ptr = true)
    (hvalid2 : isValidByteAccess (ptr + 1) = true)
    (hvalid3 : isValidByteAccess (ptr + 2) = true)
    (hvalid4 : isValidByteAccess (ptr + 3) = true)
    (hvalid5 : isValidByteAccess (ptr + 4) = true)
    (hback : (base + 20) + signExtend13 back = base) :
    cpsTriple base (base + 24)
      (CodeReq.ofProg base (rlp_phase2_long_loop_body_prog back))
      ((.x11 ↦ᵣ len) ** (.x13 ↦ᵣ ptr) ** (.x14 ↦ᵣ (5 : Word)) **
       (.x12 ↦ᵣ v12_old) ** (.x0 ↦ᵣ (0 : Word)) **
       (dwordAddr ↦ₘ wordVal))
      (rlp_phase2_long_loop_five_byte_post len ptr
        ((extractByte wordVal (byteOffset ptr)).zeroExtend 64)
        ((extractByte wordVal (byteOffset (ptr + 1))).zeroExtend 64)
        ((extractByte wordVal (byteOffset (ptr + 2))).zeroExtend 64)
        ((extractByte wordVal (byteOffset (ptr + 3))).zeroExtend 64)
        ((extractByte wordVal (byteOffset (ptr + 4))).zeroExtend 64)
        wordVal dwordAddr) := by
  simp only [rlp_phase2_long_loop_five_byte_post_unfold]
  have body := rlp_phase2_long_loop_body_spec len ptr (5 : Word) v12_old
    wordVal dwordAddr base back halign1 hvalid1
  have hcnt' : (5 : Word) + signExtend12 (-1 : BitVec 12) = (4 : Word) := by
    decide
  rw [hcnt'] at body
  set byte1 := (extractByte wordVal (byteOffset ptr)).zeroExtend 64
  have h_absurd : ∀ hp,
      rlp_phase2_long_loop_body_post len ptr (5 : Word) byte1 wordVal
         dwordAddr ((4 : Word) = 0) hp → False := by
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
      ((.x11 ↦ᵣ len) ** (.x13 ↦ᵣ ptr) ** (.x14 ↦ᵣ (5 : Word)) **
       (.x12 ↦ᵣ v12_old) ** (.x0 ↦ᵣ (0 : Word)) **
       (dwordAddr ↦ₘ wordVal))
      ((.x11 ↦ᵣ ((len <<< 8) + byte1)) ** (.x13 ↦ᵣ (ptr + 1)) **
       (.x14 ↦ᵣ (4 : Word)) ** (.x12 ↦ᵣ byte1) **
       (.x0 ↦ᵣ (0 : Word)) ** (dwordAddr ↦ₘ wordVal)) :=
    cpsTriple_weaken
      (fun _ hp => hp)
      (fun h hp => by
        simp only [rlp_phase2_long_loop_body_post_unfold] at hp
        refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right ?_)))) h hp
        intro h' hp'
        exact ((sepConj_pure_right _ _ _).1 hp').1)
      tri1
  -- Iters 2-5: four-byte closure at base with (ptr+1, cnt=4).
  have four_byte := rlp_phase2_long_loop_four_byte_spec ((len <<< 8) + byte1)
    (ptr + 1) byte1 wordVal dwordAddr base back
    halign2
    (by rw [show (ptr + 1 : Word) + 1 = ptr + 2 from by bv_omega]; exact halign3)
    (by rw [show (ptr + 1 : Word) + 2 = ptr + 3 from by bv_omega]; exact halign4)
    (by rw [show (ptr + 1 : Word) + 3 = ptr + 4 from by bv_omega]; exact halign5)
    hvalid2
    (by rw [show (ptr + 1 : Word) + 1 = ptr + 2 from by bv_omega]; exact hvalid3)
    (by rw [show (ptr + 1 : Word) + 2 = ptr + 3 from by bv_omega]; exact hvalid4)
    (by rw [show (ptr + 1 : Word) + 3 = ptr + 4 from by bv_omega]; exact hvalid5)
    hback
  simp only [rlp_phase2_long_loop_four_byte_post_unfold] at four_byte
  have h_ptr_2 : (ptr + 1 : Word) + 1 = ptr + 2 := by bv_omega
  have h_ptr_3 : (ptr + 1 : Word) + 2 = ptr + 3 := by bv_omega
  have h_ptr_4 : (ptr + 1 : Word) + 3 = ptr + 4 := by bv_omega
  have h_ptr_5 : (ptr + 1 : Word) + 4 = ptr + 5 := by bv_omega
  rw [h_ptr_2, h_ptr_3, h_ptr_4, h_ptr_5] at four_byte
  have composed :=
    cpsTriple_seq_perm_same_cr
      (fun h hp => by xperm_hyp hp) tri1' four_byte
  exact cpsTriple_weaken
    (fun _ hp => hp)
    (fun h hp => by xperm_hyp hp)
    composed

end EvmAsm.Rv64.RLP
