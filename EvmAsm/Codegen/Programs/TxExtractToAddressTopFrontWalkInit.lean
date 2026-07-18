/-
  Front typeLoad post → walk_init OkFail under stack/toBuf ambient.
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.SAsm.AbiFrame
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Codegen.Programs.TxExtractToAddressTopFrontMid
import EvmAsm.Codegen.Programs.TxExtractToAddressTopWalkInitNorm
import EvmAsm.Codegen.Programs.TxIntrinsicStateGasSpec
import EvmAsm.Codegen.Programs.TxTypeDispatchSpec

namespace EvmAsm.Codegen.TxExtractToAddressSpec

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
open EvmAsm.Codegen.TxIntrinsicStateGasSpec (extractToBufOwn)
open EvmAsm.Codegen.TxTypeDispatchSpec (teerTxTypeDispatch)

local macro "pcf" : tactic =>
  `(tactic| repeat
      first
      | apply pcFree_sepConj
      | exact pcFree_regIs
      | exact pcFree_regOwn
      | exact pcFree_memIs
      | exact pcFree_memOwn
      | exact pcFree_emp
      | exact pcFree_pure
      | exact pcFree_regsAt _ _
      | exact pcFree_frameSlotsSaved _ _ _
      | exact pcFree_frameSlotsOwn _ _
      | exact bytesRegion_pcFree _ _
      | exact midOwned_pcFree _ _ _ _ _)

/-- Stack + toBuf owns framed across walk_init (no x21/x22 — call owns those). -/
def walkFrameAmbient (spC : Word) (s : ExtractSaved)
    (toBuf isCreationPtr : Word) : Assertion :=
  (.x2 ↦ᵣ spC) **
    frameSlotsSaved extractFrame spC (extractSavedVals s) **
    extractSpareSlot spC **
    (.x18 ↦ᵣ toBuf) ** (.x19 ↦ᵣ isCreationPtr) **
    (Reg.x23 ↦ᵣ s.s7) **
    extractToBufOwn toBuf ** memOwn isCreationPtr

private theorem walkFrameAmbient_pcFree (spC : Word) (s : ExtractSaved)
    (toBuf isCreationPtr : Word) :
    (walkFrameAmbient spC s toBuf isCreationPtr).pcFree := by
  unfold walkFrameAmbient extractToBufOwn; pcf

private theorem regIs_imp_regOwn (r : Reg) (v : Word) :
    ∀ h, (r ↦ᵣ v) h → regOwn r h :=
  fun _ hx => ⟨v, hx⟩

/-- Post at LinkWalkInit: walkFrame + ambient + common + OkFail + s5/s6. -/
def frontWalkInitOkFailPost (spC : Word) (s : ExtractSaved)
    (txBase lenW toBuf isCreationPtr : Word)
    (txBytes : List (BitVec 8)) : Assertion :=
  walkFrameAmbient spC s toBuf isCreationPtr **
    walkInitAmbient txBase lenW
      (teerTxTypeDispatch txBytes).2.1 (teerTxTypeDispatch txBytes).2.2 **
    extractWalkInitCommon txBase txBytes ** extractWalkInitOkFail **
    regOwn .x21 ** regOwn .x22

set_option maxRecDepth 8000 in
/-- WalkInitJalPc → LinkWalkInit under frontTypeLoadPost ambient. -/
theorem extractWalkInitCall_fromFrontTypeLoad_owned
    (spC : Word) (s : ExtractSaved)
    (txBase lenW toBuf isCreationPtr : Word)
    (txBytes : List (BitVec 8))
    (hsalign : txBase.toNat % 8 = 0)
    (hoff : (teerTxTypeDispatch txBytes).2.2.toNat < txBytes.length)
    (hover : txBase.toNat + (teerTxTypeDispatch txBytes).2.2.toNat < 2 ^ 64)
    (hvalid : isValidByteAccess
      (txBase + BitVec.ofNat 64 (teerTxTypeDispatch txBytes).2.2.toNat) = true)
    (hll_len : ¬ BitVec.ult
        ((txBytes[(teerTxTypeDispatch txBytes).2.2.toNat]'hoff).zeroExtend 64)
        (0xf8 : Word) = true →
      (teerTxTypeDispatch txBytes).2.2.toNat + 1 +
        ((txBytes[(teerTxTypeDispatch txBytes).2.2.toNat]'hoff).zeroExtend 64 -
          (0xf7 : Word)).toNat
        ≤ txBytes.length)
    (hll_over : ¬ BitVec.ult
        ((txBytes[(teerTxTypeDispatch txBytes).2.2.toNat]'hoff).zeroExtend 64)
        (0xf8 : Word) = true →
      txBase.toNat + ((teerTxTypeDispatch txBytes).2.2.toNat + 1 +
        ((txBytes[(teerTxTypeDispatch txBytes).2.2.toNat]'hoff).zeroExtend 64 -
          (0xf7 : Word)).toNat) ≤ 2 ^ 64)
    (hll_valid : ¬ BitVec.ult
        ((txBytes[(teerTxTypeDispatch txBytes).2.2.toNat]'hoff).zeroExtend 64)
        (0xf8 : Word) = true →
      ∀ k, k < ((txBytes[(teerTxTypeDispatch txBytes).2.2.toNat]'hoff).zeroExtend 64 -
          (0xf7 : Word)).toNat →
        isValidByteAccess (txBase + BitVec.ofNat 64
          ((teerTxTypeDispatch txBytes).2.2.toNat + 1 + k)) = true) :
    cpsTripleWithin (1 + 81) WalkInitJalPc LinkWalkInit extractLinkedCode
      (frontTypeLoadPost spC s txBase lenW toBuf isCreationPtr txBytes)
      (frontWalkInitOkFailPost spC s txBase lenW toBuf isCreationPtr txBytes) := by
  have h0 := extractWalkInitCall_okFail_framed_s5s6 txBase lenW txBytes LinkType
    hsalign hoff hover hvalid hll_len hll_over hll_valid
  have hF := cpsTripleWithin_frameR
    (walkFrameAmbient spC s toBuf isCreationPtr)
    (walkFrameAmbient_pcFree spC s toBuf isCreationPtr) h0
  refine cpsTripleWithin_weaken (fun h hp => ?_) (fun _ hq => by
      simp only [frontWalkInitOkFailPost] at hq ⊢
      xperm_hyp hq) hF
  -- frontTypeLoadPost → call pre ** walkFrame
  -- typeMidAmbient = walkFrame ** x21 ** x22 (concrete)
  have hp1 :
      (walkFrameAmbient spC s toBuf isCreationPtr **
        ((.x1 ↦ᵣ LinkType) ** (.x0 ↦ᵣ (0 : Word)) **
          (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
          (.x5 ↦ᵣ TeaInnerAddr) **
          (.x10 ↦ᵣ (txBase + (teerTxTypeDispatch txBytes).2.2)) **
          (.x11 ↦ᵣ (lenW - (teerTxTypeDispatch txBytes).2.2)) **
          (.x20 ↦ᵣ (teerTxTypeDispatch txBytes).2.1) **
          (.x30 ↦ᵣ (teerTxTypeDispatch txBytes).2.2) **
          bytesRegion txBase txBytes **
          (TeaTypeAddr ↦ₘ (teerTxTypeDispatch txBytes).2.1) **
          (TeaInnerAddr ↦ₘ (teerTxTypeDispatch txBytes).2.2) **
          regOwn .x6 ** regOwn .x7 **
          regOwn .x12 ** regOwn .x13 **
          regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x31 **
          (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6))) h := by
    simp only [frontTypeLoadPost, typeMidAmbient, walkFrameAmbient,
      extractToBufOwn] at hp ⊢
    xperm_hyp hp
  -- convert x21/x22 concrete → regOwn
  have hnest :
      ((walkFrameAmbient spC s toBuf isCreationPtr **
          ((.x1 ↦ᵣ LinkType) ** (.x0 ↦ᵣ (0 : Word)) **
            (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
            (.x5 ↦ᵣ TeaInnerAddr) **
            (.x10 ↦ᵣ (txBase + (teerTxTypeDispatch txBytes).2.2)) **
            (.x11 ↦ᵣ (lenW - (teerTxTypeDispatch txBytes).2.2)) **
            (.x20 ↦ᵣ (teerTxTypeDispatch txBytes).2.1) **
            (.x30 ↦ᵣ (teerTxTypeDispatch txBytes).2.2) **
            bytesRegion txBase txBytes **
            (TeaTypeAddr ↦ₘ (teerTxTypeDispatch txBytes).2.1) **
            (TeaInnerAddr ↦ₘ (teerTxTypeDispatch txBytes).2.2) **
            regOwn .x6 ** regOwn .x7 **
            regOwn .x12 ** regOwn .x13 **
            regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
            regOwn .x28 ** regOwn .x29 ** regOwn .x31)) **
        (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6)) h := by
    xperm_hyp hp1
  have mtemps :=
    sepConj_mono (fun _ x => x)
      (sepConj_mono (regIs_imp_regOwn .x21 s.s5)
        (regIs_imp_regOwn .x22 s.s6)) h hnest
  xperm_hyp mtemps

#print axioms extractWalkInitCall_fromFrontTypeLoad_owned

end EvmAsm.Codegen.TxExtractToAddressSpec
