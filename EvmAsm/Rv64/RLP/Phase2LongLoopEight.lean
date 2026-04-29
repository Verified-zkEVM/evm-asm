/-
  EvmAsm.Rv64.RLP.Phase2LongLoopEight

  EL.3 Phase 2 (long form) — eight-iteration closure of the loop body.

  Specializes `rlp_phase2_long_loop_body_spec` at `x14 = 8`, composed
  with `rlp_phase2_long_loop_seven_byte_spec` for the remaining seven
  iterations.

  Corresponds to RLP prefixes `0xBF` and `0xFF` (`lenLen = 8`). This is
  the maximum lenLen permitted by the RLP encoding (the prefix byte
  range `0xB7+1..0xB7+8` and `0xF7+1..0xF7+8` saturate at 8 length
  bytes).

  Memory model: all eight bytes assumed in the same doubleword. Holds
  whenever `byteOffset ptr = 0` (i.e., `ptr` is doubleword-aligned).
-/

import EvmAsm.Rv64.RLP.Phase2LongLoopSeven

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64

-- ============================================================================
-- Spec
-- ============================================================================

/-- Bundled post for the eight-iteration loop closure. -/
@[irreducible]
def rlp_phase2_long_loop_eight_byte_post
    (len ptr byte1 byte2 byte3 byte4 byte5 byte6 byte7 byte8
     wordVal dwordAddr : Word) :
    Assertion :=
  let length' :=
    (((((((((((((len <<< 8) + byte1) <<< 8) + byte2) <<< 8) + byte3) <<< 8
        + byte4) <<< 8 + byte5) <<< 8) + byte6) <<< 8) + byte7) <<< 8) + byte8
  let ptr'    := ptr + 8
  (.x11 ↦ᵣ length') ** (.x13 ↦ᵣ ptr') ** (.x14 ↦ᵣ (0 : Word)) **
    (.x12 ↦ᵣ byte8) ** (.x0 ↦ᵣ (0 : Word)) **
    (dwordAddr ↦ₘ wordVal)

theorem rlp_phase2_long_loop_eight_byte_post_unfold
    (len ptr byte1 byte2 byte3 byte4 byte5 byte6 byte7 byte8
     wordVal dwordAddr : Word) :
    rlp_phase2_long_loop_eight_byte_post len ptr byte1 byte2 byte3 byte4
        byte5 byte6 byte7 byte8 wordVal dwordAddr =
    ((.x11 ↦ᵣ ((((((((((((len <<< 8) + byte1) <<< 8 + byte2) <<< 8 + byte3) <<< 8
                + byte4) <<< 8 + byte5) <<< 8) + byte6) <<< 8) + byte7) <<< 8)
                + byte8)) **
     (.x13 ↦ᵣ (ptr + 8)) **
     (.x14 ↦ᵣ (0 : Word)) **
     (.x12 ↦ᵣ byte8) ** (.x0 ↦ᵣ (0 : Word)) **
     (dwordAddr ↦ₘ wordVal)) := by
  delta rlp_phase2_long_loop_eight_byte_post; rfl

/-- `cpsTriple` spec for the eight-iteration (lenLen = 8) closure.

    Iter 1 (cnt 8→7, BNE taken) + seven-byte closure (iters 2–8). -/
theorem rlp_phase2_long_loop_eight_byte_spec
    (len ptr v12Old wordVal dwordAddr : Word)
    (base : Word) (back : BitVec 13)
    (halign1 : alignToDword ptr = dwordAddr)
    (halign2 : alignToDword (ptr + 1) = dwordAddr)
    (halign3 : alignToDword (ptr + 2) = dwordAddr)
    (halign4 : alignToDword (ptr + 3) = dwordAddr)
    (halign5 : alignToDword (ptr + 4) = dwordAddr)
    (halign6 : alignToDword (ptr + 5) = dwordAddr)
    (halign7 : alignToDword (ptr + 6) = dwordAddr)
    (halign8 : alignToDword (ptr + 7) = dwordAddr)
    (hvalid1 : isValidByteAccess ptr = true)
    (hvalid2 : isValidByteAccess (ptr + 1) = true)
    (hvalid3 : isValidByteAccess (ptr + 2) = true)
    (hvalid4 : isValidByteAccess (ptr + 3) = true)
    (hvalid5 : isValidByteAccess (ptr + 4) = true)
    (hvalid6 : isValidByteAccess (ptr + 5) = true)
    (hvalid7 : isValidByteAccess (ptr + 6) = true)
    (hvalid8 : isValidByteAccess (ptr + 7) = true)
    (hback : (base + 20) + signExtend13 back = base) :
    cpsTriple base (base + 24)
      (CodeReq.ofProg base (rlp_phase2_long_loop_body_prog back))
      ((.x11 ↦ᵣ len) ** (.x13 ↦ᵣ ptr) ** (.x14 ↦ᵣ (8 : Word)) **
       (.x12 ↦ᵣ v12Old) ** (.x0 ↦ᵣ (0 : Word)) **
       (dwordAddr ↦ₘ wordVal))
      (rlp_phase2_long_loop_eight_byte_post len ptr
        ((extractByte wordVal (byteOffset ptr)).zeroExtend 64)
        ((extractByte wordVal (byteOffset (ptr + 1))).zeroExtend 64)
        ((extractByte wordVal (byteOffset (ptr + 2))).zeroExtend 64)
        ((extractByte wordVal (byteOffset (ptr + 3))).zeroExtend 64)
        ((extractByte wordVal (byteOffset (ptr + 4))).zeroExtend 64)
        ((extractByte wordVal (byteOffset (ptr + 5))).zeroExtend 64)
        ((extractByte wordVal (byteOffset (ptr + 6))).zeroExtend 64)
        ((extractByte wordVal (byteOffset (ptr + 7))).zeroExtend 64)
        wordVal dwordAddr) := by
  simp only [rlp_phase2_long_loop_eight_byte_post_unfold]
  have body := rlp_phase2_long_loop_body_spec len ptr (8 : Word) v12Old
    wordVal dwordAddr base back halign1 hvalid1
  rw [cnt_dec_8] at body
  set byte1 := (extractByte wordVal (byteOffset ptr)).zeroExtend 64
  have h_absurd : ∀ hp,
      rlp_phase2_long_loop_body_post len ptr (8 : Word) byte1 wordVal
         dwordAddr ((7 : Word) = 0) hp → False := fun hp hpost =>
    absurd (rlp_phase2_long_loop_body_post_pure hp hpost) (by decide)
  have tri1 := cpsBranch_takenPath body h_absurd
  rw [hback] at tri1
  have tri1' : cpsTriple base base
      (CodeReq.ofProg base (rlp_phase2_long_loop_body_prog back))
      ((.x11 ↦ᵣ len) ** (.x13 ↦ᵣ ptr) ** (.x14 ↦ᵣ (8 : Word)) **
       (.x12 ↦ᵣ v12Old) ** (.x0 ↦ᵣ (0 : Word)) **
       (dwordAddr ↦ₘ wordVal))
      ((.x11 ↦ᵣ ((len <<< 8) + byte1)) ** (.x13 ↦ᵣ (ptr + 1)) **
       (.x14 ↦ᵣ (7 : Word)) ** (.x12 ↦ᵣ byte1) **
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
  -- Iters 2-8: seven-byte closure at base with (ptr+1, cnt=7).
  have seven_byte := rlp_phase2_long_loop_seven_byte_spec ((len <<< 8) + byte1)
    (ptr + 1) byte1 wordVal dwordAddr base back
    halign2
    (by rw [show (ptr + 1 : Word) + 1 = ptr + 2 from by bv_omega]; exact halign3)
    (by rw [show (ptr + 1 : Word) + 2 = ptr + 3 from by bv_omega]; exact halign4)
    (by rw [show (ptr + 1 : Word) + 3 = ptr + 4 from by bv_omega]; exact halign5)
    (by rw [show (ptr + 1 : Word) + 4 = ptr + 5 from by bv_omega]; exact halign6)
    (by rw [show (ptr + 1 : Word) + 5 = ptr + 6 from by bv_omega]; exact halign7)
    (by rw [show (ptr + 1 : Word) + 6 = ptr + 7 from by bv_omega]; exact halign8)
    hvalid2
    (by rw [show (ptr + 1 : Word) + 1 = ptr + 2 from by bv_omega]; exact hvalid3)
    (by rw [show (ptr + 1 : Word) + 2 = ptr + 3 from by bv_omega]; exact hvalid4)
    (by rw [show (ptr + 1 : Word) + 3 = ptr + 4 from by bv_omega]; exact hvalid5)
    (by rw [show (ptr + 1 : Word) + 4 = ptr + 5 from by bv_omega]; exact hvalid6)
    (by rw [show (ptr + 1 : Word) + 5 = ptr + 6 from by bv_omega]; exact hvalid7)
    (by rw [show (ptr + 1 : Word) + 6 = ptr + 7 from by bv_omega]; exact hvalid8)
    hback
  simp only [rlp_phase2_long_loop_seven_byte_post_unfold] at seven_byte
  have h_ptr_2 : (ptr + 1 : Word) + 1 = ptr + 2 := by bv_omega
  have h_ptr_3 : (ptr + 1 : Word) + 2 = ptr + 3 := by bv_omega
  have h_ptr_4 : (ptr + 1 : Word) + 3 = ptr + 4 := by bv_omega
  have h_ptr_5 : (ptr + 1 : Word) + 4 = ptr + 5 := by bv_omega
  have h_ptr_6 : (ptr + 1 : Word) + 5 = ptr + 6 := by bv_omega
  have h_ptr_7 : (ptr + 1 : Word) + 6 = ptr + 7 := by bv_omega
  have h_ptr_8 : (ptr + 1 : Word) + 7 = ptr + 8 := by bv_omega
  rw [h_ptr_2, h_ptr_3, h_ptr_4, h_ptr_5, h_ptr_6, h_ptr_7, h_ptr_8] at seven_byte
  have composed :=
    cpsTriple_seq_perm_same_cr
      (fun h hp => by xperm_hyp hp) tri1' seven_byte
  exact cpsTriple_weaken
    (fun _ hp => hp)
    (fun h hp => by xperm_hyp hp)
    composed

end EvmAsm.Rv64.RLP
