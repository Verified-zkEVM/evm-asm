/-
  EvmAsm.Rv64.RLP.Phase1E3LongStringOne

  EL.3 full Phase 1 → Phase 3 → Phase 2 path for the smallest long-string
  prefix, `0xB8`.

  RLP long byte strings with prefix `0xB8` have exactly one length byte after
  the prefix. This composes:

    * the full Phase 1 e3 path specialized to prefix `0xB8`,
    * the Phase 3 long-string entry (`lenLen = 1`, `len_acc = 0`,
      pointer advanced past the prefix),
    * the one-byte Phase 2 long-form length loop.

  Result: `x11` holds the payload length byte and `x13` points at the payload.
-/

import EvmAsm.Rv64.RLP.Phase1E3FullPath
import EvmAsm.Rv64.RLP.Phase2LongLoopOne

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.Rv64.Tactics

-- ============================================================================
-- Spec
-- ============================================================================

/-- Concrete `0xB8` long-string flat-decode path.

    Starting with the prefix byte already loaded in `x5 = 0xB8` and `x13`
    pointing at that prefix byte, this path leaves:

    * `x11 = length_byte`, where `length_byte` is the zero-extended byte at
      `v13 + 1`;
    * `x13 = v13 + 2`, the first payload byte after prefix and one length byte;
    * `x14 = 0`, the consumed length-of-length counter;
    * `x12 = length_byte`, the last byte loaded by the Phase 2 loop;
    * `x5`, `x10`, `x0`, and the source doubleword preserved.

    This is the first executable RISC-V bridge from Phase 1 classification to
    a usable zero-copy `(payload_ptr, payload_len)` pair for long strings. -/
theorem rlp_phase1_e3_0xB8_one_byte_length_spec
    (v10 v11Old v12Old v13 v14Old wordVal dwordAddr : Word)
    (off1 off2 off3 back : BitVec 13)
    (base e3_target : Word)
    (htarget : (base + 16 + 4) + signExtend13 off3 = e3_target)
    (halign : alignToDword (v13 + signExtend12 (1 : BitVec 12)) = dwordAddr)
    (hvalid : isValidByteAccess (v13 + signExtend12 (1 : BitVec 12)) = true)
    (hd_phase3 :
      (((rlp_phase1_step_code 0x80 off1 base).union
        ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
          (rlp_phase1_step_code 0xC0 off3 (base + 16))))).Disjoint
        (CodeReq.ofProg e3_target rlp_phase3_long_string_prog))
    (hd_loop :
      ((((rlp_phase1_step_code 0x80 off1 base).union
         ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
           (rlp_phase1_step_code 0xC0 off3 (base + 16)))).union
         (CodeReq.ofProg e3_target rlp_phase3_long_string_prog))).Disjoint
        (CodeReq.ofProg (e3_target + 12) (rlp_phase2_long_loop_body_prog back))) :
    let lenByte :=
      (extractByte wordVal
        (byteOffset (v13 + signExtend12 (1 : BitVec 12)))).zeroExtend 64
    cpsTriple base ((e3_target + 12) + 24)
      (((((rlp_phase1_step_code 0x80 off1 base).union
          ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
            (rlp_phase1_step_code 0xC0 off3 (base + 16)))).union
          (CodeReq.ofProg e3_target rlp_phase3_long_string_prog))).union
          (CodeReq.ofProg (e3_target + 12) (rlp_phase2_long_loop_body_prog back)))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (0xB8 : Word)) ** (.x10 ↦ᵣ v10) **
        (.x11 ↦ᵣ v11Old) ** (.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ v13) **
        (.x14 ↦ᵣ v14Old) ** (dwordAddr ↦ₘ wordVal))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (0xB8 : Word)) **
        (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xC0 : BitVec 12))) **
        (.x11 ↦ᵣ lenByte) ** (.x12 ↦ᵣ lenByte) **
        (.x13 ↦ᵣ ((v13 + signExtend12 (1 : BitVec 12)) + 1)) **
        (.x14 ↦ᵣ (0 : Word)) ** (dwordAddr ↦ₘ wordVal)) := by
  intro lenByte
  have hv5_lo :
      ¬ BitVec.ult (0xB8 : Word) ((0 : Word) + signExtend12 (0x80 : BitVec 12)) := by
    decide
  have hv5_mid :
      ¬ BitVec.ult (0xB8 : Word) ((0 : Word) + signExtend12 (0xB8 : BitVec 12)) := by
    decide
  have hv5_hi :
      BitVec.ult (0xB8 : Word) ((0 : Word) + signExtend12 (0xC0 : BitVec 12)) := by
    decide
  have prefixSpec := rlp_phase1_e3_full_path_spec'
    (0xB8 : Word) v10 v11Old v13 v14Old off1 off2 off3 base e3_target
    htarget hv5_lo hv5_mid hv5_hi hd_phase3
  have h_lenLen :
      (0xB8 : Word) + signExtend12 (-(0xB7 : BitVec 12)) = (1 : Word) := by
    decide
  rw [h_lenLen] at prefixSpec
  have prefix' : cpsTriple base (e3_target + 12)
      (((rlp_phase1_step_code 0x80 off1 base).union
         ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
           (rlp_phase1_step_code 0xC0 off3 (base + 16)))).union
         (CodeReq.ofProg e3_target rlp_phase3_long_string_prog))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (0xB8 : Word)) ** (.x10 ↦ᵣ v10) **
        (.x11 ↦ᵣ v11Old) ** (.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ v13) **
        (.x14 ↦ᵣ v14Old) ** (dwordAddr ↦ₘ wordVal))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (0xB8 : Word)) **
        (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xC0 : BitVec 12))) **
        (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ v12Old) **
        (.x13 ↦ᵣ (v13 + signExtend12 (1 : BitVec 12))) **
        (.x14 ↦ᵣ (1 : Word)) ** (dwordAddr ↦ₘ wordVal)) :=
    cpsTriple_weaken
      (fun _ hp => by xperm_hyp hp)
      (fun _ hp => by xperm_hyp hp)
      (cpsTriple_frameR
        ((.x12 ↦ᵣ v12Old) ** (dwordAddr ↦ₘ wordVal)) (by pcFree) prefixSpec)
  have loop := rlp_phase2_long_loop_one_byte_spec
    (0 : Word) (v13 + signExtend12 (1 : BitVec 12)) v12Old wordVal dwordAddr
    (e3_target + 12) back halign hvalid
  simp only [rlp_phase2_long_loop_one_byte_post_unfold] at loop
  have h_zero_len : (((0 : Word) <<< 8) + lenByte) = lenByte := by
    simp
  rw [h_zero_len] at loop
  have loop' : cpsTriple (e3_target + 12) ((e3_target + 12) + 24)
      (CodeReq.ofProg (e3_target + 12) (rlp_phase2_long_loop_body_prog back))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (0xB8 : Word)) **
        (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xC0 : BitVec 12))) **
        (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ v12Old) **
        (.x13 ↦ᵣ (v13 + signExtend12 (1 : BitVec 12))) **
        (.x14 ↦ᵣ (1 : Word)) ** (dwordAddr ↦ₘ wordVal))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (0xB8 : Word)) **
        (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xC0 : BitVec 12))) **
        (.x11 ↦ᵣ lenByte) ** (.x12 ↦ᵣ lenByte) **
        (.x13 ↦ᵣ ((v13 + signExtend12 (1 : BitVec 12)) + 1)) **
        (.x14 ↦ᵣ (0 : Word)) ** (dwordAddr ↦ₘ wordVal)) := by
    have framed := cpsTriple_frameR
      ((.x5 ↦ᵣ (0xB8 : Word)) **
       (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xC0 : BitVec 12))))
      (by pcFree) loop
    exact cpsTriple_weaken
      (fun _ hp => by xperm_hyp hp)
      (fun _ hp => by
        unfold lenByte
        xperm_hyp hp)
      framed
  exact cpsTriple_seq hd_loop prefix' loop'

end EvmAsm.Rv64.RLP
