/-
  EvmAsm.Rv64.RLP.UnifiedDecodeItemReconvergeAll

  EL.3 — the COMPLETE 5-class reconvergence of the unified single-item decoder.

  `UnifiedDecodeItemReconverge.lean` reconverged the 3 flat classes; this file
  adds the 2 long classes (`longBytes` / `longList`, which carry
  `(dwordAddr ↦ₘ wordVal)` + `x12`/`x14` and have variable step counts), giving
  a single `cpsTripleWithin 60 base joinPC cr` over ALL of `classifyPrefix pfx`:
  each class handler runs to its exit, then an unconditional `JAL x0` jumps to a
  common `joinPC`, and the uniform post exposes the cascade residue / payload
  length / payload pointer (and the long-only `x12`/`x14`/memory) via
  `classifyPrefix`-dispatched helpers. A list loop can then advance uniformly by
  `x13 += x11` for items of any class.
-/

import EvmAsm.Rv64.RLP.UnifiedDecodeItem
import EvmAsm.Rv64.Tactics.XSimp

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.EL.RLP

-- ============================================================================
-- Uniform-post helpers (all 5 classes, classifyPrefix-dispatched)
-- ============================================================================

/-- `x10` cascade residue per class. -/
def itemResidue (pfx : Byte) : Word :=
  match classifyPrefix pfx with
  | .singleByte => (0 : Word) + signExtend12 (0x80 : BitVec 12)
  | .shortBytes => (0 : Word) + signExtend12 (0xB8 : BitVec 12)
  | .longBytes  => (0 : Word) + signExtend12 (0xC0 : BitVec 12)
  | .shortList  => (0 : Word) + signExtend12 (0xF8 : BitVec 12)
  | .longList   => (0 : Word) + signExtend12 (0xF8 : BitVec 12)

/-- `x11` decoded payload length per class. -/
def itemLen (pfx : Byte) (wordVal v13 : Word) : Word :=
  match classifyPrefix pfx with
  | .singleByte => 1
  | .shortBytes => BitVec.ofNat 64 (rlpPrefixShortBytesPayloadLen pfx)
  | .longBytes  => BitVec.ofNat 64
      (Nat.fromBytesBE (rlpLoopByteList wordVal (v13 + signExtend12 (1 : BitVec 12))
        (rlpPrefixLongBytesLenOfLen pfx)))
  | .shortList  => BitVec.ofNat 64 (rlpPrefixShortListPayloadLen pfx)
  | .longList   => BitVec.ofNat 64
      (Nat.fromBytesBE (rlpLoopByteList wordVal (v13 + signExtend12 (1 : BitVec 12))
        (rlpPrefixLongListLenOfLen pfx)))

/-- `x13` payload pointer per class. -/
def itemPtr (pfx : Byte) (v13 : Word) : Word :=
  match classifyPrefix pfx with
  | .singleByte => v13
  | .shortBytes => v13 + signExtend12 (1 : BitVec 12)
  | .longBytes  => (v13 + signExtend12 (1 : BitVec 12))
                     + BitVec.ofNat 64 (rlpPrefixLongBytesLenOfLen pfx)
  | .shortList  => v13 + signExtend12 (1 : BitVec 12)
  | .longList   => (v13 + signExtend12 (1 : BitVec 12))
                     + BitVec.ofNat 64 (rlpPrefixLongListLenOfLen pfx)

/-- `x12` scratch per class (long forms hold the last length byte; flat forms
    leave the framed-in value `v12Old`). -/
def itemX12 (pfx : Byte) (wordVal v13 v12Old : Word) : Word :=
  match classifyPrefix pfx with
  | .longBytes => (extractByte wordVal (byteOffset ((v13 + signExtend12 (1 : BitVec 12))
      + BitVec.ofNat 64 (rlpPrefixLongBytesLenOfLen pfx - 1)))).zeroExtend 64
  | .longList  => (extractByte wordVal (byteOffset ((v13 + signExtend12 (1 : BitVec 12))
      + BitVec.ofNat 64 (rlpPrefixLongListLenOfLen pfx - 1)))).zeroExtend 64
  | _ => v12Old

/-- `x14` counter per class (long forms exhaust it to `0`; flat forms leave the
    framed-in value `v14Old`). -/
def itemX14 (pfx : Byte) (v14Old : Word) : Word :=
  match classifyPrefix pfx with
  | .longBytes => 0
  | .longList  => 0
  | _ => v14Old

-- ============================================================================
-- Bound-parameterized reconvergence arm
-- ============================================================================

/-- A class handler reaching `eC` (uniform pre `P`, uniform post `R`), followed
    by an unconditional `JAL x0` to `joinPC`, lifted into the shared code `cr`
    and to the common step bound `N`. -/
theorem reconverge_arm_n
    {N sC : Nat} (hsC : sC + 1 ≤ N)
    {base eC joinPC : Word} {cr handlerCR : CodeReq} {joff : BitVec 21}
    {P R : Assertion} (hRpc : R.pcFree)
    (handler : cpsTripleWithin sC base eC handlerCR P R)
    (hjoin : eC + signExtend21 joff = joinPC)
    (hd_jal : handlerCR.Disjoint (CodeReq.singleton eC (.JAL .x0 joff)))
    (hsub : ∀ a i,
      (handlerCR.union (CodeReq.singleton eC (.JAL .x0 joff))) a = some i → cr a = some i) :
    cpsTripleWithin N base joinPC cr P R := by
  have jal := jal_x0_spec_gen_within joff eC
  rw [hjoin] at jal
  have jalR : cpsTripleWithin 1 eC joinPC
      (CodeReq.singleton eC (.JAL .x0 joff)) R R := by
    have hf := cpsTripleWithin_frameR R hRpc jal
    rwa [sepConj_emp_left'] at hf
  have seq := cpsTripleWithin_seq hd_jal handler jalR
  have ext := cpsTripleWithin_extend_code hsub seq
  exact cpsTripleWithin_mono_nSteps hsC ext

-- ============================================================================
-- Complete 5-class reconverged single-item decode
-- ============================================================================

/-- **Complete reconverged single-item decode.** For ANY prefix byte, the decoder
    runs from `base`, and an unconditional `JAL x0` at the class exit jumps to the
    common `joinPC`. The uniform post exposes `x10`/`x11`/`x12`/`x13`/`x14` (and
    the preserved memory) via the `classifyPrefix`-dispatched helpers, so a list
    loop can advance uniformly by `x13 += x11`. The shared decoder code is the
    parameter `cr`; each class's handler+JAL code is a sub-CR of it (`hsub_*`). -/
theorem rlp_decode_single_item_reconverged_all
    (pfx : Byte)
    (v10 v11Old v12Old v13 v14Old wordVal dwordAddr : Word)
    (off1 off2 off3 off4 back : BitVec 13)
    (joff1 joff2 joff3 joff4 joff5 : BitVec 21)
    (base e1_target e2_target e3_target e4_target joinPC : Word) (cr : CodeReq)
    (htarget1 : (base + 4) + signExtend13 off1 = e1_target)
    (htarget2 : (base + 8 + 4) + signExtend13 off2 = e2_target)
    (htarget3 : (base + 16 + 4) + signExtend13 off3 = e3_target)
    (htarget4 : (base + 24 + 4) + signExtend13 off4 = e4_target)
    (hlong : rlpDecodeLongHyps pfx v13 dwordAddr base back e3_target)
    (hd_e1 : (rlp_phase1_step_code 0x80 off1 base).Disjoint
              (CodeReq.ofProg e1_target rlp_phase3_single_byte_prog))
    (hd_e2 : ((rlp_phase1_step_code 0x80 off1 base).union
                (rlp_phase1_step_code 0xB8 off2 (base + 8))).Disjoint
              (CodeReq.ofProg e2_target rlp_phase3_short_string_prog))
    (hd_e3_phase3 :
      (((rlp_phase1_step_code 0x80 off1 base).union
        ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
          (rlp_phase1_step_code 0xC0 off3 (base + 16))))).Disjoint
        (CodeReq.ofProg e3_target rlp_phase3_long_string_prog))
    (hd_e3_loop :
      ((((rlp_phase1_step_code 0x80 off1 base).union
         ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
           (rlp_phase1_step_code 0xC0 off3 (base + 16)))).union
         (CodeReq.ofProg e3_target rlp_phase3_long_string_prog))).Disjoint
        (CodeReq.ofProg (e3_target + 12) (rlp_phase2_long_loop_body_prog back)))
    (hd_e4 :
      (((rlp_phase1_step_code 0x80 off1 base).union
        ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
          ((rlp_phase1_step_code 0xC0 off3 (base + 16)).union
            (rlp_phase1_step_code 0xF8 off4 (base + 24)))))).Disjoint
        (CodeReq.ofProg e4_target rlp_phase3_short_list_prog))
    (hd_e5_phase3 :
      (((rlp_phase1_step_code 0x80 off1 base).union
        ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
          ((rlp_phase1_step_code 0xC0 off3 (base + 16)).union
            (rlp_phase1_step_code 0xF8 off4 (base + 24)))))).Disjoint
        (CodeReq.ofProg (base + 32) rlp_phase3_long_list_prog))
    (hd_e5_loop :
      ((((rlp_phase1_step_code 0x80 off1 base).union
        ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
          ((rlp_phase1_step_code 0xC0 off3 (base + 16)).union
            (rlp_phase1_step_code 0xF8 off4 (base + 24))))).union
        (CodeReq.ofProg (base + 32) rlp_phase3_long_list_prog))).Disjoint
        (CodeReq.ofProg (base + 44) (rlp_phase2_long_loop_body_prog back)))
    (hjoin1 : (e1_target + 4) + signExtend21 joff1 = joinPC)
    (hjoin2 : (e2_target + 8) + signExtend21 joff2 = joinPC)
    (hjoin3 : ((e3_target + 12) + 24) + signExtend21 joff3 = joinPC)
    (hjoin4 : (e4_target + 8) + signExtend21 joff4 = joinPC)
    (hjoin5 : ((base + 44) + 24) + signExtend21 joff5 = joinPC)
    (hd_jal1 : ((rlp_phase1_step_code 0x80 off1 base).union
                  (CodeReq.ofProg e1_target rlp_phase3_single_byte_prog)).Disjoint
                (CodeReq.singleton (e1_target + 4) (.JAL .x0 joff1)))
    (hd_jal2 : (((rlp_phase1_step_code 0x80 off1 base).union
                  (rlp_phase1_step_code 0xB8 off2 (base + 8))).union
                  (CodeReq.ofProg e2_target rlp_phase3_short_string_prog)).Disjoint
                (CodeReq.singleton (e2_target + 8) (.JAL .x0 joff2)))
    (hd_jal3 : (((((rlp_phase1_step_code 0x80 off1 base).union
                  ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
                    (rlp_phase1_step_code 0xC0 off3 (base + 16)))).union
                  (CodeReq.ofProg e3_target rlp_phase3_long_string_prog))).union
                  (CodeReq.ofProg (e3_target + 12) (rlp_phase2_long_loop_body_prog back))).Disjoint
                (CodeReq.singleton ((e3_target + 12) + 24) (.JAL .x0 joff3)))
    (hd_jal4 : (((rlp_phase1_step_code 0x80 off1 base).union
                  ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
                    ((rlp_phase1_step_code 0xC0 off3 (base + 16)).union
                      (rlp_phase1_step_code 0xF8 off4 (base + 24))))).union
                  (CodeReq.ofProg e4_target rlp_phase3_short_list_prog)).Disjoint
                (CodeReq.singleton (e4_target + 8) (.JAL .x0 joff4)))
    (hd_jal5 : (((((rlp_phase1_step_code 0x80 off1 base).union
                  ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
                    ((rlp_phase1_step_code 0xC0 off3 (base + 16)).union
                      (rlp_phase1_step_code 0xF8 off4 (base + 24))))).union
                  (CodeReq.ofProg (base + 32) rlp_phase3_long_list_prog))).union
                  (CodeReq.ofProg (base + 44) (rlp_phase2_long_loop_body_prog back))).Disjoint
                (CodeReq.singleton ((base + 44) + 24) (.JAL .x0 joff5)))
    (hsub1 : ∀ a i, (((rlp_phase1_step_code 0x80 off1 base).union
                  (CodeReq.ofProg e1_target rlp_phase3_single_byte_prog)).union
                  (CodeReq.singleton (e1_target + 4) (.JAL .x0 joff1))) a = some i → cr a = some i)
    (hsub2 : ∀ a i, ((((rlp_phase1_step_code 0x80 off1 base).union
                  (rlp_phase1_step_code 0xB8 off2 (base + 8))).union
                  (CodeReq.ofProg e2_target rlp_phase3_short_string_prog)).union
                  (CodeReq.singleton (e2_target + 8) (.JAL .x0 joff2))) a = some i → cr a = some i)
    (hsub3 : ∀ a i, ((((((rlp_phase1_step_code 0x80 off1 base).union
                  ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
                    (rlp_phase1_step_code 0xC0 off3 (base + 16)))).union
                  (CodeReq.ofProg e3_target rlp_phase3_long_string_prog))).union
                  (CodeReq.ofProg (e3_target + 12) (rlp_phase2_long_loop_body_prog back))).union
                  (CodeReq.singleton ((e3_target + 12) + 24) (.JAL .x0 joff3))) a = some i →
                cr a = some i)
    (hsub4 : ∀ a i, ((((rlp_phase1_step_code 0x80 off1 base).union
                  ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
                    ((rlp_phase1_step_code 0xC0 off3 (base + 16)).union
                      (rlp_phase1_step_code 0xF8 off4 (base + 24))))).union
                  (CodeReq.ofProg e4_target rlp_phase3_short_list_prog)).union
                  (CodeReq.singleton (e4_target + 8) (.JAL .x0 joff4))) a = some i → cr a = some i)
    (hsub5 : ∀ a i, ((((((rlp_phase1_step_code 0x80 off1 base).union
                  ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
                    ((rlp_phase1_step_code 0xC0 off3 (base + 16)).union
                      (rlp_phase1_step_code 0xF8 off4 (base + 24))))).union
                  (CodeReq.ofProg (base + 32) rlp_phase3_long_list_prog))).union
                  (CodeReq.ofProg (base + 44) (rlp_phase2_long_loop_body_prog back))).union
                  (CodeReq.singleton ((base + 44) + 24) (.JAL .x0 joff5))) a = some i →
                cr a = some i) :
    cpsTripleWithin 60 base joinPC cr
      ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) **
       (.x11 ↦ᵣ v11Old) ** (.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14Old) **
       (dwordAddr ↦ₘ wordVal))
      ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x10 ↦ᵣ itemResidue pfx) ** (.x11 ↦ᵣ itemLen pfx wordVal v13) **
       (.x12 ↦ᵣ itemX12 pfx wordVal v13 v12Old) ** (.x13 ↦ᵣ itemPtr pfx v13) **
       (.x14 ↦ᵣ itemX14 pfx v14Old) ** (dwordAddr ↦ₘ wordVal)) := by
  cases h : classifyPrefix pfx with
  | singleByte =>
    have handler := rlp_phase1_e1_single_byte_of_class_spec_within pfx v10 v11Old off1 base
      e1_target htarget1 h hd_e1
    have handler' : cpsTripleWithin 3 base (e1_target + 4)
        ((rlp_phase1_step_code 0x80 off1 base).union
          (CodeReq.ofProg e1_target rlp_phase3_single_byte_prog))
        ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) **
         (.x11 ↦ᵣ v11Old) ** (.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14Old) **
         (dwordAddr ↦ₘ wordVal))
        ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
         (.x10 ↦ᵣ itemResidue pfx) ** (.x11 ↦ᵣ itemLen pfx wordVal v13) **
         (.x12 ↦ᵣ itemX12 pfx wordVal v13 v12Old) ** (.x13 ↦ᵣ itemPtr pfx v13) **
         (.x14 ↦ᵣ itemX14 pfx v14Old) ** (dwordAddr ↦ₘ wordVal)) := by
      refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
        (fun _ hp => by
          simp only [itemResidue, itemLen, itemPtr, itemX12, itemX14, h]
          xperm_hyp hp)
        (cpsTripleWithin_frameR
          ((.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14Old) ** (dwordAddr ↦ₘ wordVal))
          (by pcFree) handler)
    exact reconverge_arm_n (by omega) (by pcFree) handler' hjoin1 hd_jal1 hsub1
  | shortBytes =>
    have handler := rlp_phase1_e2_full_path_payload_len_of_class_spec_within pfx v10 v11Old v13
      off1 off2 base e2_target htarget2 h hd_e2
    have handler' : cpsTripleWithin 6 base (e2_target + 8)
        (((rlp_phase1_step_code 0x80 off1 base).union
            (rlp_phase1_step_code 0xB8 off2 (base + 8))).union
          (CodeReq.ofProg e2_target rlp_phase3_short_string_prog))
        ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) **
         (.x11 ↦ᵣ v11Old) ** (.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14Old) **
         (dwordAddr ↦ₘ wordVal))
        ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
         (.x10 ↦ᵣ itemResidue pfx) ** (.x11 ↦ᵣ itemLen pfx wordVal v13) **
         (.x12 ↦ᵣ itemX12 pfx wordVal v13 v12Old) ** (.x13 ↦ᵣ itemPtr pfx v13) **
         (.x14 ↦ᵣ itemX14 pfx v14Old) ** (dwordAddr ↦ₘ wordVal)) := by
      refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
        (fun _ hp => by
          simp only [itemResidue, itemLen, itemPtr, itemX12, itemX14, h]
          xperm_hyp hp)
        (cpsTripleWithin_frameR
          ((.x12 ↦ᵣ v12Old) ** (.x14 ↦ᵣ v14Old) ** (dwordAddr ↦ₘ wordVal))
          (by pcFree) handler)
    exact reconverge_arm_n (by omega) (by pcFree) handler' hjoin2 hd_jal2 hsub2
  | longBytes =>
    simp only [rlpDecodeLongHyps, h] at hlong
    obtain ⟨hwin, hback⟩ := hlong
    have handler := rlp_phase1_e3_longBytes_full_spec_within pfx v10 v11Old v12Old v13 v14Old
      wordVal dwordAddr off1 off2 off3 back base e3_target htarget3 h hwin hback
      hd_e3_phase3 hd_e3_loop
    have handler' : cpsTripleWithin (9 + 6 * rlpPrefixLongBytesLenOfLen pfx) base
        ((e3_target + 12) + 24)
        (((((rlp_phase1_step_code 0x80 off1 base).union
            ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
              (rlp_phase1_step_code 0xC0 off3 (base + 16)))).union
            (CodeReq.ofProg e3_target rlp_phase3_long_string_prog))).union
            (CodeReq.ofProg (e3_target + 12) (rlp_phase2_long_loop_body_prog back)))
        ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) **
         (.x11 ↦ᵣ v11Old) ** (.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14Old) **
         (dwordAddr ↦ₘ wordVal))
        ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
         (.x10 ↦ᵣ itemResidue pfx) ** (.x11 ↦ᵣ itemLen pfx wordVal v13) **
         (.x12 ↦ᵣ itemX12 pfx wordVal v13 v12Old) ** (.x13 ↦ᵣ itemPtr pfx v13) **
         (.x14 ↦ᵣ itemX14 pfx v14Old) ** (dwordAddr ↦ₘ wordVal)) := by
      refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
        (fun _ hp => by
          simp only [itemResidue, itemLen, itemPtr, itemX12, itemX14, h]
          xperm_hyp hp) handler
    have hn := rlpPrefixLongBytesLenOfLen_le_8_of_class h
    exact reconverge_arm_n (by omega) (by pcFree) handler' hjoin3 hd_jal3 hsub3
  | shortList =>
    have handler := rlp_phase1_e4_full_path_payload_len_of_class_spec_within pfx v10 v11Old v13
      off1 off2 off3 off4 base e4_target htarget4 h hd_e4
    have handler' : cpsTripleWithin 10 base (e4_target + 8)
        (((rlp_phase1_step_code 0x80 off1 base).union
          ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
            ((rlp_phase1_step_code 0xC0 off3 (base + 16)).union
              (rlp_phase1_step_code 0xF8 off4 (base + 24))))).union
          (CodeReq.ofProg e4_target rlp_phase3_short_list_prog))
        ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) **
         (.x11 ↦ᵣ v11Old) ** (.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14Old) **
         (dwordAddr ↦ₘ wordVal))
        ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
         (.x10 ↦ᵣ itemResidue pfx) ** (.x11 ↦ᵣ itemLen pfx wordVal v13) **
         (.x12 ↦ᵣ itemX12 pfx wordVal v13 v12Old) ** (.x13 ↦ᵣ itemPtr pfx v13) **
         (.x14 ↦ᵣ itemX14 pfx v14Old) ** (dwordAddr ↦ₘ wordVal)) := by
      refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
        (fun _ hp => by
          simp only [itemResidue, itemLen, itemPtr, itemX12, itemX14, h]
          xperm_hyp hp)
        (cpsTripleWithin_frameR
          ((.x12 ↦ᵣ v12Old) ** (.x14 ↦ᵣ v14Old) ** (dwordAddr ↦ₘ wordVal))
          (by pcFree) handler)
    exact reconverge_arm_n (by omega) (by pcFree) handler' hjoin4 hd_jal4 hsub4
  | longList =>
    simp only [rlpDecodeLongHyps, h] at hlong
    obtain ⟨hwin, hback⟩ := hlong
    have handler := rlp_phase1_e5_longList_full_spec_within pfx v10 v11Old v12Old v13 v14Old
      wordVal dwordAddr off1 off2 off3 off4 back base h hwin hback hd_e5_phase3 hd_e5_loop
    have handler' : cpsTripleWithin (11 + 6 * rlpPrefixLongListLenOfLen pfx) base
        ((base + 44) + 24)
        (((((rlp_phase1_step_code 0x80 off1 base).union
          ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
            ((rlp_phase1_step_code 0xC0 off3 (base + 16)).union
              (rlp_phase1_step_code 0xF8 off4 (base + 24))))).union
          (CodeReq.ofProg (base + 32) rlp_phase3_long_list_prog))).union
          (CodeReq.ofProg (base + 44) (rlp_phase2_long_loop_body_prog back)))
        ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) **
         (.x11 ↦ᵣ v11Old) ** (.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14Old) **
         (dwordAddr ↦ₘ wordVal))
        ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
         (.x10 ↦ᵣ itemResidue pfx) ** (.x11 ↦ᵣ itemLen pfx wordVal v13) **
         (.x12 ↦ᵣ itemX12 pfx wordVal v13 v12Old) ** (.x13 ↦ᵣ itemPtr pfx v13) **
         (.x14 ↦ᵣ itemX14 pfx v14Old) ** (dwordAddr ↦ₘ wordVal)) := by
      refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
        (fun _ hp => by
          simp only [itemResidue, itemLen, itemPtr, itemX12, itemX14, h]
          xperm_hyp hp) handler
    have hn := rlpPrefixLongListLenOfLen_le_8_of_class h
    exact reconverge_arm_n (by omega) (by pcFree) handler' hjoin5 hd_jal5 hsub5

-- Sanity: the uniform-post helpers reduce to the spec-correct per-class values.
example (wordVal v13 : Word) : itemLen (0x00 : Byte) wordVal v13 = (1 : Word) := by
  rw [itemLen, show classifyPrefix (0x00 : Byte) = .singleByte from by decide]
example (wordVal v13 : Word) :
    itemLen (0x83 : Byte) wordVal v13 = BitVec.ofNat 64 (rlpPrefixShortBytesPayloadLen 0x83) := by
  rw [itemLen, show classifyPrefix (0x83 : Byte) = .shortBytes from by decide]
example : itemResidue (0xC5 : Byte) = (0 : Word) + signExtend12 (0xF8 : BitVec 12) := by
  rw [itemResidue, show classifyPrefix (0xC5 : Byte) = .shortList from by decide]
example (v14Old : Word) : itemX14 (0xBA : Byte) v14Old = (0 : Word) := by
  rw [itemX14, show classifyPrefix (0xBA : Byte) = .longBytes from by decide]

end EvmAsm.Rv64.RLP
