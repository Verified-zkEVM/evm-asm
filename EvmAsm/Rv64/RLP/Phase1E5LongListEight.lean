/-
  EvmAsm.Rv64.RLP.Phase1E5LongListEight

  EL.3 full Phase 1 → Phase 3 → Phase 2 path for the long-list prefix
  `0xFF` (length-of-length = 8, the maximum permitted by RLP).

  Composes the full Phase 1 e5 path specialized to prefix `0xFF`, the Phase 3
  long-list entry (`lenLen = 8`, `len_acc = 0`, pointer advanced past the
  prefix), and the eight-byte Phase 2 long-form length loop.

  The postcondition reuses `rlp_phase2_long_loop_eight_byte_post` (instantiated
  at `len = 0`) so the big-endian length accumulation is stated by reference to
  the proven loop closure rather than re-transcribed here.

  Long-list analogue of `rlp_phase1_e3_0xB8_one_byte_length_spec_within`
  (`Phase1E3LongStringOne.lean`) for `lenLen = 8`.
-/

import EvmAsm.Rv64.RLP.Phase1E5FullPath
import EvmAsm.Rv64.RLP.Phase2LongLoopEight

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.Rv64.Tactics

-- ============================================================================
-- Spec
-- ============================================================================

/-- Concrete `0xFF` long-list flat-decode path (`lenLen = 8`).

    Leaves `x11` holding the big-endian length over the eight length bytes at
    `v13 + 1 .. v13 + 8` (per `rlp_phase2_long_loop_eight_byte_post`),
    `x13 = (v13 + 1) + 8` pointing at the payload, `x14 = 0`, `x12` the last
    length byte, and `x5`/`x10`/`x0`/the source doubleword preserved. -/
theorem rlp_phase1_e5_0xFF_eight_byte_length_spec_within
    (v10 v11Old v12Old v13 v14Old wordVal dwordAddr : Word)
    (off1 off2 off3 off4 back : BitVec 13)
    (base : Word)
    (halign1 : alignToDword (v13 + signExtend12 (1 : BitVec 12)) = dwordAddr)
    (halign2 : alignToDword ((v13 + signExtend12 (1 : BitVec 12)) + 1) = dwordAddr)
    (halign3 : alignToDword ((v13 + signExtend12 (1 : BitVec 12)) + 2) = dwordAddr)
    (halign4 : alignToDword ((v13 + signExtend12 (1 : BitVec 12)) + 3) = dwordAddr)
    (halign5 : alignToDword ((v13 + signExtend12 (1 : BitVec 12)) + 4) = dwordAddr)
    (halign6 : alignToDword ((v13 + signExtend12 (1 : BitVec 12)) + 5) = dwordAddr)
    (halign7 : alignToDword ((v13 + signExtend12 (1 : BitVec 12)) + 6) = dwordAddr)
    (halign8 : alignToDword ((v13 + signExtend12 (1 : BitVec 12)) + 7) = dwordAddr)
    (hvalid1 : isValidByteAccess (v13 + signExtend12 (1 : BitVec 12)) = true)
    (hvalid2 : isValidByteAccess ((v13 + signExtend12 (1 : BitVec 12)) + 1) = true)
    (hvalid3 : isValidByteAccess ((v13 + signExtend12 (1 : BitVec 12)) + 2) = true)
    (hvalid4 : isValidByteAccess ((v13 + signExtend12 (1 : BitVec 12)) + 3) = true)
    (hvalid5 : isValidByteAccess ((v13 + signExtend12 (1 : BitVec 12)) + 4) = true)
    (hvalid6 : isValidByteAccess ((v13 + signExtend12 (1 : BitVec 12)) + 5) = true)
    (hvalid7 : isValidByteAccess ((v13 + signExtend12 (1 : BitVec 12)) + 6) = true)
    (hvalid8 : isValidByteAccess ((v13 + signExtend12 (1 : BitVec 12)) + 7) = true)
    (hback : ((base + 44) + 20) + signExtend13 back = (base + 44))
    (hd_phase3 :
      (((rlp_phase1_step_code 0x80 off1 base).union
        ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
          ((rlp_phase1_step_code 0xC0 off3 (base + 16)).union
            (rlp_phase1_step_code 0xF8 off4 (base + 24)))))).Disjoint
        (CodeReq.ofProg (base + 32) rlp_phase3_long_list_prog))
    (hd_loop :
      ((((rlp_phase1_step_code 0x80 off1 base).union
        ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
          ((rlp_phase1_step_code 0xC0 off3 (base + 16)).union
            (rlp_phase1_step_code 0xF8 off4 (base + 24))))).union
        (CodeReq.ofProg (base + 32) rlp_phase3_long_list_prog))).Disjoint
        (CodeReq.ofProg (base + 44) (rlp_phase2_long_loop_body_prog back))) :
    let ptr := v13 + signExtend12 (1 : BitVec 12)
    let b1 := (extractByte wordVal (byteOffset ptr)).zeroExtend 64
    let b2 := (extractByte wordVal (byteOffset (ptr + 1))).zeroExtend 64
    let b3 := (extractByte wordVal (byteOffset (ptr + 2))).zeroExtend 64
    let b4 := (extractByte wordVal (byteOffset (ptr + 3))).zeroExtend 64
    let b5 := (extractByte wordVal (byteOffset (ptr + 4))).zeroExtend 64
    let b6 := (extractByte wordVal (byteOffset (ptr + 5))).zeroExtend 64
    let b7 := (extractByte wordVal (byteOffset (ptr + 6))).zeroExtend 64
    let b8 := (extractByte wordVal (byteOffset (ptr + 7))).zeroExtend 64
    cpsTripleWithin 59 base ((base + 44) + 24)
      (((((rlp_phase1_step_code 0x80 off1 base).union
        ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
          ((rlp_phase1_step_code 0xC0 off3 (base + 16)).union
            (rlp_phase1_step_code 0xF8 off4 (base + 24))))).union
        (CodeReq.ofProg (base + 32) rlp_phase3_long_list_prog))).union
        (CodeReq.ofProg (base + 44) (rlp_phase2_long_loop_body_prog back)))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (0xFF : Word)) ** (.x10 ↦ᵣ v10) **
        (.x11 ↦ᵣ v11Old) ** (.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ v13) **
        (.x14 ↦ᵣ v14Old) ** (dwordAddr ↦ₘ wordVal))
      ((.x5 ↦ᵣ (0xFF : Word)) **
        (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xF8 : BitVec 12))) **
        rlp_phase2_long_loop_eight_byte_post (0 : Word) ptr
          b1 b2 b3 b4 b5 b6 b7 b8 wordVal dwordAddr) := by
  intro ptr b1 b2 b3 b4 b5 b6 b7 b8
  have hv5_lo :
      ¬ BitVec.ult (0xFF : Word) ((0 : Word) + signExtend12 (0x80 : BitVec 12)) := by
    decide
  have hv5_2 :
      ¬ BitVec.ult (0xFF : Word) ((0 : Word) + signExtend12 (0xB8 : BitVec 12)) := by
    decide
  have hv5_3 :
      ¬ BitVec.ult (0xFF : Word) ((0 : Word) + signExtend12 (0xC0 : BitVec 12)) := by
    decide
  have hv5_hi :
      ¬ BitVec.ult (0xFF : Word) ((0 : Word) + signExtend12 (0xF8 : BitVec 12)) := by
    decide
  have prefixSpec := rlp_phase1_e5_full_path_spec'_within
    (0xFF : Word) v10 v11Old v13 v14Old off1 off2 off3 off4 base
    hv5_lo hv5_2 hv5_3 hv5_hi hd_phase3
  have h_lenLen :
      (0xFF : Word) + signExtend12 (-(0xF7 : BitVec 12)) = (8 : Word) := by
    decide
  rw [h_lenLen] at prefixSpec
  have prefix' : cpsTripleWithin 11 base (base + 44)
      ((((rlp_phase1_step_code 0x80 off1 base).union
        ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
          ((rlp_phase1_step_code 0xC0 off3 (base + 16)).union
            (rlp_phase1_step_code 0xF8 off4 (base + 24))))).union
        (CodeReq.ofProg (base + 32) rlp_phase3_long_list_prog)))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (0xFF : Word)) ** (.x10 ↦ᵣ v10) **
        (.x11 ↦ᵣ v11Old) ** (.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ v13) **
        (.x14 ↦ᵣ v14Old) ** (dwordAddr ↦ₘ wordVal))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (0xFF : Word)) **
        (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xF8 : BitVec 12))) **
        (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ v12Old) **
        (.x13 ↦ᵣ (v13 + signExtend12 (1 : BitVec 12))) **
        (.x14 ↦ᵣ (8 : Word)) ** (dwordAddr ↦ₘ wordVal)) :=
    cpsTripleWithin_weaken
      (fun _ hp => by xperm_hyp hp)
      (fun _ hp => by xperm_hyp hp)
      (cpsTripleWithin_frameR
        ((.x12 ↦ᵣ v12Old) ** (dwordAddr ↦ₘ wordVal)) (by pcFree) prefixSpec)
  have loop := rlp_phase2_long_loop_eight_byte_spec_within
    (0 : Word) ptr v12Old wordVal dwordAddr
    (base + 44) back
    halign1 halign2 halign3 halign4 halign5 halign6 halign7 halign8
    hvalid1 hvalid2 hvalid3 hvalid4 hvalid5 hvalid6 hvalid7 hvalid8 hback
  have loop' : cpsTripleWithin 48 (base + 44) ((base + 44) + 24)
      (CodeReq.ofProg (base + 44) (rlp_phase2_long_loop_body_prog back))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (0xFF : Word)) **
        (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xF8 : BitVec 12))) **
        (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ v12Old) **
        (.x13 ↦ᵣ (v13 + signExtend12 (1 : BitVec 12))) **
        (.x14 ↦ᵣ (8 : Word)) ** (dwordAddr ↦ₘ wordVal))
      ((.x5 ↦ᵣ (0xFF : Word)) **
        (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xF8 : BitVec 12))) **
        rlp_phase2_long_loop_eight_byte_post (0 : Word) ptr
          b1 b2 b3 b4 b5 b6 b7 b8 wordVal dwordAddr) := by
    have framed := cpsTripleWithin_frameR
      ((.x5 ↦ᵣ (0xFF : Word)) **
       (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xF8 : BitVec 12))))
      (by pcFree) loop
    exact cpsTripleWithin_weaken
      (fun _ hp => by xperm_hyp hp)
      (fun _ hp => by xperm_hyp hp)
      framed
  exact cpsTripleWithin_seq hd_loop prefix' loop'

end EvmAsm.Rv64.RLP
