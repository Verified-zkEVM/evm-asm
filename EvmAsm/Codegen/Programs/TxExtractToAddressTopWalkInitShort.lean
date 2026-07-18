/-
  Short-list walk_init packaging: typeLoad shape → AfterSave without
  universal walkInitOkFail_drop (uses extractWalkInitCall_short).
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Codegen.Programs.TxExtractToAddressTopWalkInit
import EvmAsm.Codegen.Programs.TxExtractToAddressTopWalkInitNorm
import EvmAsm.Codegen.Programs.TxExtractToAddressWalkInit
import EvmAsm.Codegen.Programs.TxTypeDispatchSpec

namespace EvmAsm.Codegen.TxExtractToAddressSpec

open EvmAsm.Rv64
open EvmAsm.Codegen
open EvmAsm.Codegen.TxTypeDispatchSpec (teerTxTypeDispatch)

local macro "pcf" : tactic => `(tactic|
  repeat first
    | apply pcFree_sepConj
    | exact pcFree_regIs
    | exact pcFree_regOwn
    | exact pcFree_memIs
    | exact pcFree_memOwn
    | exact pcFree_emp
    | exact pcFree_pure
    | exact bytesRegion_pcFree _ _)

private theorem regIs_imp_regOwn (r : Reg) (v : Word) :
    ∀ h, (r ↦ᵣ v) h → regOwn r h :=
  fun _ hx => ⟨v, hx⟩

/-- Concrete short OK cursor/end from walk_init short leaf. -/
def shortWalkCursor (txBase : Word) (listOff : Nat) : Word :=
  (txBase + BitVec.ofNat 64 listOff) + signExtend12 (1 : BitVec 12)

def shortWalkEnd (txBase listLen : Word) (listOff : Nat) : Word :=
  (txBase + BitVec.ofNat 64 listOff) + listLen

set_option maxRecDepth 8000 in
/-- WalkInitJalPc → LinkWalkInit short path; post ambient ** common ** concrete OK regs.
    Short pure from extractSuccess_short_walkInit_guards (+ listLen = lenW − inner). -/
theorem extractWalkInitCall_short_fromTypeLoad
    (txBase lenW : Word) (txBytes : List (BitVec 8))
    (old1 : Word)
    (hsalign : txBase.toNat % 8 = 0)
    (hoff : (teerTxTypeDispatch txBytes).2.2.toNat < txBytes.length)
    (hover : txBase.toNat + (teerTxTypeDispatch txBytes).2.2.toNat < 2 ^ 64)
    (hvalid : isValidByteAccess
      (txBase + BitVec.ofNat 64 (teerTxTypeDispatch txBytes).2.2.toNat) = true)
    (hlen : (lenW - (teerTxTypeDispatch txBytes).2.2) ≠ (0 : Word))
    (h_ge : ¬ BitVec.ult
        ((txBytes[(teerTxTypeDispatch txBytes).2.2.toNat]'hoff).zeroExtend 64)
        (0xc0 : Word) = true)
    (h_hi : BitVec.ult
        ((txBytes[(teerTxTypeDispatch txBytes).2.2.toNat]'hoff).zeroExtend 64)
        (0xf8 : Word) = true)
    (h_exact : (txBase + BitVec.ofNat 64 (teerTxTypeDispatch txBytes).2.2.toNat) +
        (((txBytes[(teerTxTypeDispatch txBytes).2.2.toNat]'hoff).zeroExtend 64 -
          (0xc0 : Word)) + signExtend12 (1 : BitVec 12)) =
      (txBase + BitVec.ofNat 64 (teerTxTypeDispatch txBytes).2.2.toNat) +
        (lenW - (teerTxTypeDispatch txBytes).2.2)) :
    cpsTripleWithin (1 + 15) WalkInitJalPc LinkWalkInit extractLinkedCode
      ((.x1 ↦ᵣ old1) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
        (.x5 ↦ᵣ TeaInnerAddr) **
        (.x10 ↦ᵣ (txBase + (teerTxTypeDispatch txBytes).2.2)) **
        (.x11 ↦ᵣ (lenW - (teerTxTypeDispatch txBytes).2.2)) **
        (.x20 ↦ᵣ (teerTxTypeDispatch txBytes).2.1) **
        (.x30 ↦ᵣ (teerTxTypeDispatch txBytes).2.2) **
        bytesRegion txBase txBytes **
        (TeaTypeAddr ↦ₘ (teerTxTypeDispatch txBytes).2.1) **
        (TeaInnerAddr ↦ₘ (teerTxTypeDispatch txBytes).2.2) **
        regOwn .x6 ** regOwn .x7 ** regOwn .x12 **
        regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x31)
      (walkInitAmbient txBase lenW
          (teerTxTypeDispatch txBytes).2.1 (teerTxTypeDispatch txBytes).2.2 **
        extractWalkInitCommon txBase txBytes **
        extractWalkInitShortOkRegs txBase (lenW - (teerTxTypeDispatch txBytes).2.2)
          (teerTxTypeDispatch txBytes).2.2.toNat) := by
  set inner := (teerTxTypeDispatch txBytes).2.2 with h_inner
  set typeW := (teerTxTypeDispatch txBytes).2.1 with h_type
  set listOff := inner.toNat with h_listOff
  set listLen := lenW - inner with h_listLen
  have h_off : BitVec.ofNat 64 listOff = inner := by
    simp only [listOff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have h_a0 : txBase + inner = txBase + BitVec.ofNat 64 listOff := by rw [h_off]
  -- peels rightmost: x31, x29, x28, x12, x7, x6 (same as full fromTypeLoad)
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ h => h)
    (cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x31)
      (P := (.x1 ↦ᵣ old1) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
        (.x5 ↦ᵣ TeaInnerAddr) **
        (.x10 ↦ᵣ (txBase + inner)) ** (.x11 ↦ᵣ listLen) **
        (.x20 ↦ᵣ typeW) ** (.x30 ↦ᵣ inner) **
        bytesRegion txBase txBytes **
        (TeaTypeAddr ↦ₘ typeW) ** (TeaInnerAddr ↦ₘ inner) **
        regOwn .x6 ** regOwn .x7 ** regOwn .x12 **
        regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
        regOwn .x28 ** regOwn .x29)
      (fun t6Old => ?_))
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ h => h)
    (cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x29)
      (P := (.x1 ↦ᵣ old1) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
        (.x5 ↦ᵣ TeaInnerAddr) **
        (.x10 ↦ᵣ (txBase + inner)) ** (.x11 ↦ᵣ listLen) **
        (.x20 ↦ᵣ typeW) ** (.x30 ↦ᵣ inner) **
        bytesRegion txBase txBytes **
        (TeaTypeAddr ↦ₘ typeW) ** (TeaInnerAddr ↦ₘ inner) **
        regOwn .x6 ** regOwn .x7 ** regOwn .x12 **
        regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
        regOwn .x28 ** (.x31 ↦ᵣ t6Old))
      (fun t4Old => ?_))
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ h => h)
    (cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x28)
      (P := (.x1 ↦ᵣ old1) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
        (.x5 ↦ᵣ TeaInnerAddr) **
        (.x10 ↦ᵣ (txBase + inner)) ** (.x11 ↦ᵣ listLen) **
        (.x20 ↦ᵣ typeW) ** (.x30 ↦ᵣ inner) **
        bytesRegion txBase txBytes **
        (TeaTypeAddr ↦ₘ typeW) ** (TeaInnerAddr ↦ₘ inner) **
        regOwn .x6 ** regOwn .x7 ** regOwn .x12 **
        regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
        (.x31 ↦ᵣ t6Old) ** (.x29 ↦ᵣ t4Old))
      (fun t3Old => ?_))
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ h => h)
    (cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x12)
      (P := (.x1 ↦ᵣ old1) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
        (.x5 ↦ᵣ TeaInnerAddr) **
        (.x10 ↦ᵣ (txBase + inner)) ** (.x11 ↦ᵣ listLen) **
        (.x20 ↦ᵣ typeW) ** (.x30 ↦ᵣ inner) **
        bytesRegion txBase txBytes **
        (TeaTypeAddr ↦ₘ typeW) ** (TeaInnerAddr ↦ₘ inner) **
        regOwn .x6 ** regOwn .x7 **
        regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
        (.x31 ↦ᵣ t6Old) ** (.x29 ↦ᵣ t4Old) ** (.x28 ↦ᵣ t3Old))
      (fun a2Old => ?_))
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ h => h)
    (cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x7)
      (P := (.x1 ↦ᵣ old1) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
        (.x5 ↦ᵣ TeaInnerAddr) **
        (.x10 ↦ᵣ (txBase + inner)) ** (.x11 ↦ᵣ listLen) **
        (.x20 ↦ᵣ typeW) ** (.x30 ↦ᵣ inner) **
        bytesRegion txBase txBytes **
        (TeaTypeAddr ↦ₘ typeW) ** (TeaInnerAddr ↦ₘ inner) **
        regOwn .x6 **
        regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
        (.x31 ↦ᵣ t6Old) ** (.x29 ↦ᵣ t4Old) ** (.x28 ↦ᵣ t3Old) **
        (.x12 ↦ᵣ a2Old))
      (fun t2Old => ?_))
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ h => h)
    (cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x6)
      (P := (.x1 ↦ᵣ old1) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
        (.x5 ↦ᵣ TeaInnerAddr) **
        (.x10 ↦ᵣ (txBase + inner)) ** (.x11 ↦ᵣ listLen) **
        (.x20 ↦ᵣ typeW) ** (.x30 ↦ᵣ inner) **
        bytesRegion txBase txBytes **
        (TeaTypeAddr ↦ₘ typeW) ** (TeaInnerAddr ↦ₘ inner) **
        regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
        (.x31 ↦ᵣ t6Old) ** (.x29 ↦ᵣ t4Old) ** (.x28 ↦ᵣ t3Old) **
        (.x12 ↦ᵣ a2Old) ** (.x7 ↦ᵣ t2Old))
      (fun t1Old => ?_))
  -- short pure under set aliases
  have hlen' : listLen ≠ (0 : Word) := by simpa only [listLen, h_listLen] using hlen
  have h_ge' : ¬ BitVec.ult ((txBytes[listOff]'hoff).zeroExtend 64) (0xc0 : Word) = true := by
    simpa only [listOff, h_listOff, h_inner] using h_ge
  have h_hi' : BitVec.ult ((txBytes[listOff]'hoff).zeroExtend 64) (0xf8 : Word) = true := by
    simpa only [listOff, h_listOff, h_inner] using h_hi
  have h_exact' : (txBase + BitVec.ofNat 64 listOff) +
      (((txBytes[listOff]'hoff).zeroExtend 64 - (0xc0 : Word)) +
        signExtend12 (1 : BitVec 12)) =
    (txBase + BitVec.ofNat 64 listOff) + listLen := by
    simpa only [listOff, listLen, h_listOff, h_listLen, h_inner, h_off] using h_exact
  have hcall := extractWalkInitCall_short txBase listLen a2Old TeaInnerAddr t1Old t2Old
    t3Old t4Old inner t6Old txBytes listOff old1
    hsalign hoff hover hvalid hlen' h_ge' h_hi' h_exact'
  have hcallF := cpsTripleWithin_frameR
    (walkInitAmbient txBase lenW typeW inner) (by pcf) hcall
  have hcallW : cpsTripleWithin (1 + 15) WalkInitJalPc LinkWalkInit extractLinkedCode
      ((.x1 ↦ᵣ old1) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
        (.x5 ↦ᵣ TeaInnerAddr) **
        (.x10 ↦ᵣ (txBase + inner)) ** (.x11 ↦ᵣ listLen) **
        (.x20 ↦ᵣ typeW) ** (.x30 ↦ᵣ inner) **
        bytesRegion txBase txBytes **
        (TeaTypeAddr ↦ₘ typeW) ** (TeaInnerAddr ↦ₘ inner) **
        regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
        (.x31 ↦ᵣ t6Old) ** (.x29 ↦ᵣ t4Old) ** (.x28 ↦ᵣ t3Old) **
        (.x12 ↦ᵣ a2Old) ** (.x7 ↦ᵣ t2Old) ** (.x6 ↦ᵣ t1Old))
      (walkInitAmbient txBase lenW typeW inner **
        extractWalkInitShortPost txBase listLen txBytes listOff inner t6Old) := by
    refine cpsTripleWithin_weaken (fun _ hp => by
      simp only [extractWalkInitPrest, walkInitAmbient, h_a0] at hp ⊢
      xperm_hyp hp) (fun _ hq => by
      simp only [walkInitAmbient] at hq ⊢
      xperm_hyp hq) hcallF
  -- ShortPost → common (regOwn x30/x31) ** concrete ShortOkRegs
  refine cpsTripleWithin_weaken (fun _ hp => by
    simp only [inner, typeW, listLen] at hp ⊢
    xperm_hyp hp) (fun h hq => by
    simp only [inner, typeW, listLen] at hq
    have hq' :
        (walkInitAmbient txBase lenW typeW inner **
          extractWalkInitShortPost txBase listLen txBytes listOff inner t6Old) h := by
      xperm_hyp hq
    obtain ⟨hA, hP, hd, hu, hamb, hpost⟩ := hq'
    have hconc := extractWalkInitShortPost_to_okConcrete txBase listLen txBytes
      listOff inner t6Old _ hpost
    obtain ⟨hL, hR, hd2, hu2, htemps, hRegs⟩ := hconc
    -- convert x30/x31 concrete → regOwn for extractWalkInitCommon
    have htemps' : (extractWalkInitCommon txBase txBytes) hL := by
      simp only [extractWalkInitCommon] at htemps ⊢
      have hflat :
          ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
              (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkWalkInit) **
              bytesRegion txBase txBytes) **
            (.x30 ↦ᵣ inner) ** (.x31 ↦ᵣ t6Old)) hL := by
        xperm_hyp htemps
      have mtemps :=
        sepConj_mono (fun _ x => x)
          (sepConj_mono (regIs_imp_regOwn .x30 inner)
            (regIs_imp_regOwn .x31 t6Old)) hL hflat
      xperm_hyp mtemps
    have hmid :
        (extractWalkInitCommon txBase txBytes **
          extractWalkInitShortOkRegs txBase listLen listOff) hP :=
      ⟨hL, hR, hd2, hu2, htemps', hRegs⟩
    -- goal wants ShortOkRegs with teer inner / lenW-inner
    have hmid' :
        (extractWalkInitCommon txBase txBytes **
          extractWalkInitShortOkRegs txBase (lenW - inner) inner.toNat) hP := by
      simpa only [listLen, listOff, h_listLen, h_listOff, h_inner] using hmid
    exact ⟨hA, hP, hd, hu, hamb, hmid'⟩) hcallW

set_option maxRecDepth 8000 in
/-- Frame s5/s6 through short call_fromTypeLoad. -/
theorem extractWalkInitCall_short_ok_framed_s5s6
    (txBase lenW : Word) (txBytes : List (BitVec 8))
    (old1 : Word)
    (hsalign : txBase.toNat % 8 = 0)
    (hoff : (teerTxTypeDispatch txBytes).2.2.toNat < txBytes.length)
    (hover : txBase.toNat + (teerTxTypeDispatch txBytes).2.2.toNat < 2 ^ 64)
    (hvalid : isValidByteAccess
      (txBase + BitVec.ofNat 64 (teerTxTypeDispatch txBytes).2.2.toNat) = true)
    (hlen : (lenW - (teerTxTypeDispatch txBytes).2.2) ≠ (0 : Word))
    (h_ge : ¬ BitVec.ult
        ((txBytes[(teerTxTypeDispatch txBytes).2.2.toNat]'hoff).zeroExtend 64)
        (0xc0 : Word) = true)
    (h_hi : BitVec.ult
        ((txBytes[(teerTxTypeDispatch txBytes).2.2.toNat]'hoff).zeroExtend 64)
        (0xf8 : Word) = true)
    (h_exact : (txBase + BitVec.ofNat 64 (teerTxTypeDispatch txBytes).2.2.toNat) +
        (((txBytes[(teerTxTypeDispatch txBytes).2.2.toNat]'hoff).zeroExtend 64 -
          (0xc0 : Word)) + signExtend12 (1 : BitVec 12)) =
      (txBase + BitVec.ofNat 64 (teerTxTypeDispatch txBytes).2.2.toNat) +
        (lenW - (teerTxTypeDispatch txBytes).2.2)) :
    cpsTripleWithin (1 + 15) WalkInitJalPc LinkWalkInit extractLinkedCode
      ((.x1 ↦ᵣ old1) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
        (.x5 ↦ᵣ TeaInnerAddr) **
        (.x10 ↦ᵣ (txBase + (teerTxTypeDispatch txBytes).2.2)) **
        (.x11 ↦ᵣ (lenW - (teerTxTypeDispatch txBytes).2.2)) **
        (.x20 ↦ᵣ (teerTxTypeDispatch txBytes).2.1) **
        (.x30 ↦ᵣ (teerTxTypeDispatch txBytes).2.2) **
        bytesRegion txBase txBytes **
        (TeaTypeAddr ↦ₘ (teerTxTypeDispatch txBytes).2.1) **
        (TeaInnerAddr ↦ₘ (teerTxTypeDispatch txBytes).2.2) **
        regOwn .x6 ** regOwn .x7 ** regOwn .x12 **
        regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x31 **
        regOwn .x21 ** regOwn .x22)
      (walkInitAmbient txBase lenW
          (teerTxTypeDispatch txBytes).2.1 (teerTxTypeDispatch txBytes).2.2 **
        extractWalkInitCommon txBase txBytes **
        extractWalkInitShortOkRegs txBase (lenW - (teerTxTypeDispatch txBytes).2.2)
          (teerTxTypeDispatch txBytes).2.2.toNat **
        regOwn .x21 ** regOwn .x22) := by
  have h0 := extractWalkInitCall_short_fromTypeLoad txBase lenW txBytes old1
    hsalign hoff hover hvalid hlen h_ge h_hi h_exact
  have hF := cpsTripleWithin_frameR (regOwn .x21 ** regOwn .x22) (by pcf) h0
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hF

#print axioms extractWalkInitCall_short_fromTypeLoad
#print axioms extractWalkInitCall_short_ok_framed_s5s6

end EvmAsm.Codegen.TxExtractToAddressSpec
