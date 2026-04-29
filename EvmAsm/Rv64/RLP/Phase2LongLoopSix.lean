/-
  EvmAsm.Rv64.RLP.Phase2LongLoopSix

  EL.3 Phase 2 (long form) — six-iteration closure of the loop body.

  Specializes `rlp_phase2_long_loop_body_spec` at `x14 = 6`, composed
  with `rlp_phase2_long_loop_five_byte_spec` for the remaining five
  iterations.

  Corresponds to RLP prefixes `0xBD` and `0xFD` (`lenLen = 6`).

  Memory model: all six bytes assumed in the same doubleword. Holds
  whenever `byteOffset ptr ≤ 2`.
-/

import EvmAsm.Rv64.RLP.Phase2LongLoopFive

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64

-- ============================================================================
-- Spec
-- ============================================================================

/-- Bundled post for the six-iteration loop closure. -/
@[irreducible]
def rlp_phase2_long_loop_six_byte_post
    (len ptr byte1 byte2 byte3 byte4 byte5 byte6 wordVal dwordAddr : Word) :
    Assertion :=
  let length' :=
    (((((((((len <<< 8) + byte1) <<< 8) + byte2) <<< 8) + byte3) <<< 8
        + byte4) <<< 8 + byte5) <<< 8) + byte6
  let ptr'    := ptr + 6
  (.x11 ↦ᵣ length') ** (.x13 ↦ᵣ ptr') ** (.x14 ↦ᵣ (0 : Word)) **
    (.x12 ↦ᵣ byte6) ** (.x0 ↦ᵣ (0 : Word)) **
    (dwordAddr ↦ₘ wordVal)

theorem rlp_phase2_long_loop_six_byte_post_unfold
    (len ptr byte1 byte2 byte3 byte4 byte5 byte6 wordVal dwordAddr : Word) :
    rlp_phase2_long_loop_six_byte_post len ptr byte1 byte2 byte3 byte4 byte5
        byte6 wordVal dwordAddr =
    ((.x11 ↦ᵣ ((((((((len <<< 8) + byte1) <<< 8 + byte2) <<< 8 + byte3) <<< 8
                + byte4) <<< 8 + byte5) <<< 8) + byte6)) **
     (.x13 ↦ᵣ (ptr + 6)) **
     (.x14 ↦ᵣ (0 : Word)) **
     (.x12 ↦ᵣ byte6) ** (.x0 ↦ᵣ (0 : Word)) **
     (dwordAddr ↦ₘ wordVal)) := by
  delta rlp_phase2_long_loop_six_byte_post; rfl

/-- `cpsTriple` spec for the six-iteration (lenLen = 6) closure.

    Iter 1 (cnt 6→5, BNE taken) + five-byte closure (iters 2–6). -/
theorem rlp_phase2_long_loop_six_byte_spec
    (len ptr v12Old wordVal dwordAddr : Word)
    (base : Word) (back : BitVec 13)
    (halign1 : alignToDword ptr = dwordAddr)
    (halign2 : alignToDword (ptr + 1) = dwordAddr)
    (halign3 : alignToDword (ptr + 2) = dwordAddr)
    (halign4 : alignToDword (ptr + 3) = dwordAddr)
    (halign5 : alignToDword (ptr + 4) = dwordAddr)
    (halign6 : alignToDword (ptr + 5) = dwordAddr)
    (hvalid1 : isValidByteAccess ptr = true)
    (hvalid2 : isValidByteAccess (ptr + 1) = true)
    (hvalid3 : isValidByteAccess (ptr + 2) = true)
    (hvalid4 : isValidByteAccess (ptr + 3) = true)
    (hvalid5 : isValidByteAccess (ptr + 4) = true)
    (hvalid6 : isValidByteAccess (ptr + 5) = true)
    (hback : (base + 20) + signExtend13 back = base) :
    cpsTriple base (base + 24)
      (CodeReq.ofProg base (rlp_phase2_long_loop_body_prog back))
      ((.x11 ↦ᵣ len) ** (.x13 ↦ᵣ ptr) ** (.x14 ↦ᵣ (6 : Word)) **
       (.x12 ↦ᵣ v12Old) ** (.x0 ↦ᵣ (0 : Word)) **
       (dwordAddr ↦ₘ wordVal))
      (rlp_phase2_long_loop_six_byte_post len ptr
        ((extractByte wordVal (byteOffset ptr)).zeroExtend 64)
        ((extractByte wordVal (byteOffset (ptr + 1))).zeroExtend 64)
        ((extractByte wordVal (byteOffset (ptr + 2))).zeroExtend 64)
        ((extractByte wordVal (byteOffset (ptr + 3))).zeroExtend 64)
        ((extractByte wordVal (byteOffset (ptr + 4))).zeroExtend 64)
        ((extractByte wordVal (byteOffset (ptr + 5))).zeroExtend 64)
        wordVal dwordAddr) := by
  simp only [rlp_phase2_long_loop_six_byte_post_unfold]
  have body := rlp_phase2_long_loop_body_spec len ptr (6 : Word) v12Old
    wordVal dwordAddr base back halign1 hvalid1
  rw [cnt_dec_6] at body
  set byte1 := (extractByte wordVal (byteOffset ptr)).zeroExtend 64
  have h_absurd : ∀ hp,
      rlp_phase2_long_loop_body_post len ptr (6 : Word) byte1 wordVal
         dwordAddr ((5 : Word) = 0) hp → False := fun hp hpost =>
    absurd (rlp_phase2_long_loop_body_post_pure hp hpost) (by decide)
  have tri1 := cpsBranch_takenPath body h_absurd
  rw [hback] at tri1
  have tri1' : cpsTriple base base
      (CodeReq.ofProg base (rlp_phase2_long_loop_body_prog back))
      ((.x11 ↦ᵣ len) ** (.x13 ↦ᵣ ptr) ** (.x14 ↦ᵣ (6 : Word)) **
       (.x12 ↦ᵣ v12Old) ** (.x0 ↦ᵣ (0 : Word)) **
       (dwordAddr ↦ₘ wordVal))
      ((.x11 ↦ᵣ ((len <<< 8) + byte1)) ** (.x13 ↦ᵣ (ptr + 1)) **
       (.x14 ↦ᵣ (5 : Word)) ** (.x12 ↦ᵣ byte1) **
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
  -- Iters 2-6: five-byte closure at base with (ptr+1, cnt=5).
  have five_byte := rlp_phase2_long_loop_five_byte_spec ((len <<< 8) + byte1)
    (ptr + 1) byte1 wordVal dwordAddr base back
    halign2
    (by rw [show (ptr + 1 : Word) + 1 = ptr + 2 from by bv_omega]; exact halign3)
    (by rw [show (ptr + 1 : Word) + 2 = ptr + 3 from by bv_omega]; exact halign4)
    (by rw [show (ptr + 1 : Word) + 3 = ptr + 4 from by bv_omega]; exact halign5)
    (by rw [show (ptr + 1 : Word) + 4 = ptr + 5 from by bv_omega]; exact halign6)
    hvalid2
    (by rw [show (ptr + 1 : Word) + 1 = ptr + 2 from by bv_omega]; exact hvalid3)
    (by rw [show (ptr + 1 : Word) + 2 = ptr + 3 from by bv_omega]; exact hvalid4)
    (by rw [show (ptr + 1 : Word) + 3 = ptr + 4 from by bv_omega]; exact hvalid5)
    (by rw [show (ptr + 1 : Word) + 4 = ptr + 5 from by bv_omega]; exact hvalid6)
    hback
  simp only [rlp_phase2_long_loop_five_byte_post_unfold] at five_byte
  have h_ptr_2 : (ptr + 1 : Word) + 1 = ptr + 2 := by bv_omega
  have h_ptr_3 : (ptr + 1 : Word) + 2 = ptr + 3 := by bv_omega
  have h_ptr_4 : (ptr + 1 : Word) + 3 = ptr + 4 := by bv_omega
  have h_ptr_5 : (ptr + 1 : Word) + 4 = ptr + 5 := by bv_omega
  have h_ptr_6 : (ptr + 1 : Word) + 5 = ptr + 6 := by bv_omega
  rw [h_ptr_2, h_ptr_3, h_ptr_4, h_ptr_5, h_ptr_6] at five_byte
  have composed :=
    cpsTriple_seq_perm_same_cr
      (fun h hp => by xperm_hyp hp) tri1' five_byte
  exact cpsTriple_weaken
    (fun _ hp => hp)
    (fun h hp => by xperm_hyp hp)
    composed

end EvmAsm.Rv64.RLP
