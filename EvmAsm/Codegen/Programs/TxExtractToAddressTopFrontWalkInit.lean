/-
  Front typeLoad post → walk_init OkFail under stack/toBuf ambient.
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.SAsm.AbiFrame
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Codegen.Programs.TxExtractToAddressTopFrontMid
import EvmAsm.Codegen.Programs.TxExtractToAddressTopWalkInitNorm
import EvmAsm.Codegen.Programs.TxExtractToAddressTopWalkInitOk
import EvmAsm.Codegen.Programs.TxExtractToAddressTopWalkInitShort
import EvmAsm.Codegen.Programs.TxIntrinsicStateGasSpec
import EvmAsm.Codegen.Programs.TxTypeDispatchSpec

namespace EvmAsm.Codegen.TxExtractToAddressSpec

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
open EvmAsm.Codegen.TxIntrinsicStateGasSpec (extractToBufOwn nTypeSteps)
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

/-- AfterSave under walkFrame: ∃ cursor,end. -/
def frontAfterSavePost (spC : Word) (s : ExtractSaved)
    (txBase lenW toBuf isCreationPtr : Word)
    (txBytes : List (BitVec 8)) : Assertion :=
  fun h => ∃ cursor endPtr : Word,
    (walkFrameAmbient spC s toBuf isCreationPtr **
      extractAfterSavePost txBase lenW
        (teerTxTypeDispatch txBytes).2.1 (teerTxTypeDispatch txBytes).2.2
        cursor endPtr txBytes) h

set_option maxRecDepth 8000 in
/-- OkNested BNE+save framed with walkFrameAmbient. -/
theorem extractWalkInitOkNested_owned
    (spC : Word) (s : ExtractSaved)
    (txBase lenW toBuf isCreationPtr : Word)
    (txBytes : List (BitVec 8)) :
    cpsTripleWithin (1 + (1 + 1)) LinkWalkInit AfterSaveCursor extractLinkedCode
      (walkFrameAmbient spC s toBuf isCreationPtr **
        walkInitAmbient txBase lenW
          (teerTxTypeDispatch txBytes).2.1 (teerTxTypeDispatch txBytes).2.2 **
        extractWalkInitCommon txBase txBytes **
        (fun st => ∃ cursor endPtr : Word,
          ((.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ (0 : Word))) st) **
        regOwn .x21 ** regOwn .x22)
      (frontAfterSavePost spC s txBase lenW toBuf isCreationPtr txBytes) := by
  have h0 := extractWalkInitOkNested_bneSave txBase lenW
    (teerTxTypeDispatch txBytes).2.1 (teerTxTypeDispatch txBytes).2.2 txBytes
  have hF := cpsTripleWithin_frameR
    (walkFrameAmbient spC s toBuf isCreationPtr)
    (walkFrameAmbient_pcFree spC s toBuf isCreationPtr) h0
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun h hq => by
      -- frameR post: (∃ c e, afterSave) ** walkFrame
      have hq' :
          ((fun st => ∃ cursor endPtr : Word,
              extractAfterSavePost txBase lenW
                (teerTxTypeDispatch txBytes).2.1
                (teerTxTypeDispatch txBytes).2.2
                cursor endPtr txBytes st) **
            walkFrameAmbient spC s toBuf isCreationPtr) h := by
        xperm_hyp hq
      obtain ⟨h1, h2, hd, hu, hEx, hW⟩ := hq'
      obtain ⟨cursor, endPtr, hPost⟩ := hEx
      -- rebuild walkFrame ** afterSave
      have hgoal :
          (walkFrameAmbient spC s toBuf isCreationPtr **
            extractAfterSavePost txBase lenW
              (teerTxTypeDispatch txBytes).2.1
              (teerTxTypeDispatch txBytes).2.2
              cursor endPtr txBytes) h :=
        ⟨h2, h1, hd.symm,
          by rw [PartialState.union_comm_of_disjoint hd.symm, hu],
          hW, hPost⟩
      exact ⟨cursor, endPtr, hgoal⟩) hF

/-- Drop-fail: OkFail implies the a2=0 OK arm (honesty residual from extractSuccess). -/
def walkInitOkFail_drop : Prop :=
  ∀ h, extractWalkInitOkFail h →
    ∃ cursor endPtr : Word,
      ((.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ (0 : Word))) h

set_option maxRecDepth 8000 in
/-- LinkWalkInit OkFail post → AfterSave under drop-fail + walkFrame. -/
theorem extractWalkInitOkFail_toAfterSave_owned
    (spC : Word) (s : ExtractSaved)
    (txBase lenW toBuf isCreationPtr : Word)
    (txBytes : List (BitVec 8))
    (hdrop : walkInitOkFail_drop) :
    cpsTripleWithin (1 + (1 + 1)) LinkWalkInit AfterSaveCursor extractLinkedCode
      (frontWalkInitOkFailPost spC s txBase lenW toBuf isCreationPtr txBytes)
      (frontAfterSavePost spC s txBase lenW toBuf isCreationPtr txBytes) := by
  have h0 := extractWalkInitOkNested_owned spC s txBase lenW
    toBuf isCreationPtr txBytes
  refine cpsTripleWithin_weaken (fun h hp => ?_) (fun _ hq => hq) h0
  simp only [frontWalkInitOkFailPost] at hp
  have hflat :
      ((walkFrameAmbient spC s toBuf isCreationPtr **
          walkInitAmbient txBase lenW
            (teerTxTypeDispatch txBytes).2.1 (teerTxTypeDispatch txBytes).2.2 **
          extractWalkInitCommon txBase txBytes **
          regOwn .x21 ** regOwn .x22) **
        extractWalkInitOkFail) h := by
    xperm_hyp hp
  obtain ⟨hL, hR, hd, hu, hRest, hOkFail⟩ := hflat
  have hOk := hdrop hR hOkFail
  have h2 :
      ((walkFrameAmbient spC s toBuf isCreationPtr **
          walkInitAmbient txBase lenW
            (teerTxTypeDispatch txBytes).2.1 (teerTxTypeDispatch txBytes).2.2 **
          extractWalkInitCommon txBase txBytes **
          regOwn .x21 ** regOwn .x22) **
        (fun st => ∃ cursor endPtr : Word,
          ((.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) **
            (.x12 ↦ᵣ (0 : Word))) st)) h :=
    ⟨hL, hR, hd, hu, hRest, hOk⟩
  xperm_hyp h2

set_option maxRecDepth 8000 in
/-- WalkInitJalPc → AfterSaveCursor under front ambient + drop-fail. -/
theorem extractWalkInitCall_toAfterSave_owned
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
          ((teerTxTypeDispatch txBytes).2.2.toNat + 1 + k)) = true)
    (hdrop : walkInitOkFail_drop) :
    cpsTripleWithin ((1 + 81) + (1 + (1 + 1)))
      WalkInitJalPc AfterSaveCursor extractLinkedCode
      (frontTypeLoadPost spC s txBase lenW toBuf isCreationPtr txBytes)
      (frontAfterSavePost spC s txBase lenW toBuf isCreationPtr txBytes) := by
  have hCall := extractWalkInitCall_fromFrontTypeLoad_owned spC s
    txBase lenW toBuf isCreationPtr txBytes
    hsalign hoff hover hvalid hll_len hll_over hll_valid
  have hSave := extractWalkInitOkFail_toAfterSave_owned spC s
    txBase lenW toBuf isCreationPtr txBytes hdrop
  exact cpsTripleWithin_seq_same_cr hCall hSave

set_option maxRecDepth 8000 in
/-- E → AfterSaveCursor: front + typeLoad + walk_init OK under drop-fail. -/
theorem extractFrontToAfterSave
    (sp0 spC : Word) (s : ExtractSaved)
    (txBase lenW toBuf isCreationPtr : Word)
    (old5 old6 old7 old14 old15 old16 : Word)
    (txBytes : List (BitVec 8))
    (hspC : spC = sp0 + signExtend12 (-80 : BitVec 12))
    (htalign : toBuf.toNat % 8 = 0)
    (htover : toBuf.toNat + 16 < 2 ^ 64)
    (htvalid : isValidMemAccess (toBuf + (16 : Word)) = true)
    (hlen : lenW = BitVec.ofNat 64 txBytes.length)
    (hsuccess : (teerTxTypeDispatch txBytes).1 = (0 : Word))
    (halign : txBase.toNat % 8 = 0)
    (hover : txBase.toNat + txBytes.length < 2 ^ 64)
    (hvalid0 : isValidByteAccess (txBase + BitVec.ofNat 64 0) = true)
    (hoff : (teerTxTypeDispatch txBytes).2.2.toNat < txBytes.length)
    (hinover : txBase.toNat + (teerTxTypeDispatch txBytes).2.2.toNat < 2 ^ 64)
    (hinvalid : isValidByteAccess
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
          ((teerTxTypeDispatch txBytes).2.2.toNat + 1 + k)) = true)
    (hdrop : walkInitOkFail_drop) :
    cpsTripleWithin
      (((14 + 4) + ((6 + (1 + nTypeSteps) + 1) + 8)) +
        ((1 + 81) + (1 + (1 + 1))))
      E AfterSaveCursor extractLinkedCode
      ((.x2 ↦ᵣ sp0) ** regsAt extractFrame (extractSavedVals s) **
        frameSlotsOwn extractFrame spC ** extractSpareSlot spC **
        prologueAbiRest txBase lenW toBuf isCreationPtr
          old5 old6 old7 old14 old15 old16 **
        extractToBufOwn toBuf ** memOwn isCreationPtr **
        frontExtraAmbient txBase txBytes)
      (frontAfterSavePost spC s txBase lenW toBuf isCreationPtr txBytes) := by
  have hF := extractFrontThenTypeLoad sp0 spC s txBase lenW toBuf isCreationPtr
    old5 old6 old7 old14 old15 old16 txBytes
    hspC htalign htover htvalid hlen hsuccess halign hover hvalid0
  have hW := extractWalkInitCall_toAfterSave_owned spC s
    txBase lenW toBuf isCreationPtr txBytes
    halign hoff hinover hinvalid hll_len hll_over hll_valid hdrop
  exact cpsTripleWithin_seq_same_cr hF hW

set_option maxRecDepth 8000 in
/-- Short-path walk_init from front typeLoad: LinkWalkInit OK exists (no hdrop). -/
theorem extractWalkInitCall_short_fromFrontTypeLoad_owned
    (spC : Word) (s : ExtractSaved)
    (txBase lenW toBuf isCreationPtr : Word)
    (txBytes : List (BitVec 8))
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
      (frontTypeLoadPost spC s txBase lenW toBuf isCreationPtr txBytes)
      (walkFrameAmbient spC s toBuf isCreationPtr **
        walkInitAmbient txBase lenW
          (teerTxTypeDispatch txBytes).2.1 (teerTxTypeDispatch txBytes).2.2 **
        extractWalkInitCommon txBase txBytes **
        extractWalkInitShortOkRegs txBase (lenW - (teerTxTypeDispatch txBytes).2.2)
          (teerTxTypeDispatch txBytes).2.2.toNat **
        regOwn .x21 ** regOwn .x22) := by
  have h0 := extractWalkInitCall_short_ok_framed_s5s6 txBase lenW txBytes LinkType
    hsalign hoff hover hvalid hlen h_ge h_hi h_exact
  have hF := cpsTripleWithin_frameR
    (walkFrameAmbient spC s toBuf isCreationPtr)
    (walkFrameAmbient_pcFree spC s toBuf isCreationPtr) h0
  refine cpsTripleWithin_weaken (fun h hp => ?_) (fun _ hq => by xperm_hyp hq) hF
  -- frontTypeLoadPost → call pre ** walkFrame (same as full path)
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

set_option maxRecDepth 8000 in
/-- Concrete AfterSave under walkFrame for fixed cursor/end. -/
theorem extractWalkInitBneSave_owned
    (spC : Word) (s : ExtractSaved)
    (txBase lenW toBuf isCreationPtr cursor endPtr : Word)
    (txBytes : List (BitVec 8)) :
    cpsTripleWithin (1 + (1 + 1)) LinkWalkInit AfterSaveCursor extractLinkedCode
      (walkFrameAmbient spC s toBuf isCreationPtr **
        walkInitAmbient txBase lenW
          (teerTxTypeDispatch txBytes).2.1 (teerTxTypeDispatch txBytes).2.2 **
        extractWalkInitCommon txBase txBytes **
        ((.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ (0 : Word))) **
        regOwn .x21 ** regOwn .x22)
      (walkFrameAmbient spC s toBuf isCreationPtr **
        extractAfterSavePost txBase lenW
          (teerTxTypeDispatch txBytes).2.1 (teerTxTypeDispatch txBytes).2.2
          cursor endPtr txBytes) := by
  -- extractWalkInitCommon has x0; BneSave wants walkInitRest (no x0 in rest — x0 separate)
  have h0 := extractWalkInitBneSave txBase lenW
    (teerTxTypeDispatch txBytes).2.1 (teerTxTypeDispatch txBytes).2.2
    cursor endPtr txBytes
  have hF := cpsTripleWithin_frameR
    (walkFrameAmbient spC s toBuf isCreationPtr)
    (walkFrameAmbient_pcFree spC s toBuf isCreationPtr) h0
  refine cpsTripleWithin_weaken (fun h hp => ?_) (fun _ hq => by xperm_hyp hq) hF
  -- pre: walkFrame ** ambient ** common ** regs ** s5s6
  -- target: walkFrame ** ambient ** rest ** x0 ** regs ** s5s6
  -- common = temps ** x0 ** x1 ** bytes; rest = temps ** x1 ** bytes (no x0)
  simp only [extractWalkInitCommon, walkInitRest] at hp ⊢
  xperm_hyp hp

/-- Short AfterSave post with concrete short walk cursor/end. -/
def frontAfterSavePostShort (spC : Word) (s : ExtractSaved)
    (txBase lenW toBuf isCreationPtr : Word)
    (txBytes : List (BitVec 8)) : Assertion :=
  walkFrameAmbient spC s toBuf isCreationPtr **
    extractAfterSavePost txBase lenW
      (teerTxTypeDispatch txBytes).2.1 (teerTxTypeDispatch txBytes).2.2
      (shortWalkCursor txBase (teerTxTypeDispatch txBytes).2.2.toNat)
      (shortWalkEnd txBase (lenW - (teerTxTypeDispatch txBytes).2.2)
        (teerTxTypeDispatch txBytes).2.2.toNat)
      txBytes

set_option maxRecDepth 8000 in
/-- Short path: WalkInitJalPc → AfterSaveCursor with concrete cursor/end (no hdrop). -/
theorem extractWalkInitCall_short_toAfterSave_owned
    (spC : Word) (s : ExtractSaved)
    (txBase lenW toBuf isCreationPtr : Word)
    (txBytes : List (BitVec 8))
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
    cpsTripleWithin ((1 + 15) + (1 + (1 + 1)))
      WalkInitJalPc AfterSaveCursor extractLinkedCode
      (frontTypeLoadPost spC s txBase lenW toBuf isCreationPtr txBytes)
      (frontAfterSavePost spC s txBase lenW toBuf isCreationPtr txBytes) := by
  set inner := (teerTxTypeDispatch txBytes).2.2
  set listOff := inner.toNat
  set listLen := lenW - inner
  have hCall := extractWalkInitCall_short_fromFrontTypeLoad_owned spC s
    txBase lenW toBuf isCreationPtr txBytes
    hsalign hoff hover hvalid hlen h_ge h_hi h_exact
  have hSave := extractWalkInitBneSave_owned spC s
    txBase lenW toBuf isCreationPtr
    (shortWalkCursor txBase listOff)
    (shortWalkEnd txBase listLen listOff)
    txBytes
  -- reshape ShortOkRegs = x10/x11/x12 concrete for BneSave pre
  have hCall' : cpsTripleWithin (1 + 15) WalkInitJalPc LinkWalkInit extractLinkedCode
      (frontTypeLoadPost spC s txBase lenW toBuf isCreationPtr txBytes)
      (walkFrameAmbient spC s toBuf isCreationPtr **
        walkInitAmbient txBase lenW
          (teerTxTypeDispatch txBytes).2.1 inner **
        extractWalkInitCommon txBase txBytes **
        ((.x10 ↦ᵣ shortWalkCursor txBase listOff) **
          (.x11 ↦ᵣ shortWalkEnd txBase listLen listOff) **
          (.x12 ↦ᵣ (0 : Word))) **
        regOwn .x21 ** regOwn .x22) := by
    refine cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => by
      simp only [extractWalkInitShortOkRegs, shortWalkCursor, shortWalkEnd,
        listOff, listLen, inner] at hq ⊢
      xperm_hyp hq) hCall
  have hseq := cpsTripleWithin_seq_same_cr hCall' hSave
  -- keep concrete Short post available; also export ∃ form for existing consumers
  exact cpsTripleWithin_weaken (fun _ hp => hp) (fun h hq => by
    simp only [frontAfterSavePostShort, shortWalkCursor, shortWalkEnd,
      listOff, listLen, inner] at hq
    -- Short → ∃ frontAfterSavePost
    refine ⟨shortWalkCursor txBase listOff,
      shortWalkEnd txBase listLen listOff, hq⟩) hseq

set_option maxRecDepth 8000 in
/-- E → AfterSaveCursor short path (concrete internally; ∃ post for consumers). -/
theorem extractFrontToAfterSave_short
    (sp0 spC : Word) (s : ExtractSaved)
    (txBase lenW toBuf isCreationPtr : Word)
    (old5 old6 old7 old14 old15 old16 : Word)
    (txBytes : List (BitVec 8))
    (hspC : spC = sp0 + signExtend12 (-80 : BitVec 12))
    (htalign : toBuf.toNat % 8 = 0)
    (htover : toBuf.toNat + 16 < 2 ^ 64)
    (htvalid : isValidMemAccess (toBuf + (16 : Word)) = true)
    (hlen : lenW = BitVec.ofNat 64 txBytes.length)
    (hsuccess : (teerTxTypeDispatch txBytes).1 = (0 : Word))
    (halign : txBase.toNat % 8 = 0)
    (hover : txBase.toNat + txBytes.length < 2 ^ 64)
    (hvalid0 : isValidByteAccess (txBase + BitVec.ofNat 64 0) = true)
    (hoff : (teerTxTypeDispatch txBytes).2.2.toNat < txBytes.length)
    (hinover : txBase.toNat + (teerTxTypeDispatch txBytes).2.2.toNat < 2 ^ 64)
    (hinvalid : isValidByteAccess
      (txBase + BitVec.ofNat 64 (teerTxTypeDispatch txBytes).2.2.toNat) = true)
    (hlistLen_ne : (lenW - (teerTxTypeDispatch txBytes).2.2) ≠ (0 : Word))
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
    cpsTripleWithin
      (((14 + 4) + ((6 + (1 + nTypeSteps) + 1) + 8)) +
        ((1 + 15) + (1 + (1 + 1))))
      E AfterSaveCursor extractLinkedCode
      ((.x2 ↦ᵣ sp0) ** regsAt extractFrame (extractSavedVals s) **
        frameSlotsOwn extractFrame spC ** extractSpareSlot spC **
        prologueAbiRest txBase lenW toBuf isCreationPtr
          old5 old6 old7 old14 old15 old16 **
        extractToBufOwn toBuf ** memOwn isCreationPtr **
        frontExtraAmbient txBase txBytes)
      (frontAfterSavePost spC s txBase lenW toBuf isCreationPtr txBytes) := by
  have hF := extractFrontThenTypeLoad sp0 spC s txBase lenW toBuf isCreationPtr
    old5 old6 old7 old14 old15 old16 txBytes
    hspC htalign htover htvalid hlen hsuccess halign hover hvalid0
  have hW := extractWalkInitCall_short_toAfterSave_owned spC s
    txBase lenW toBuf isCreationPtr txBytes
    halign hoff hinover hinvalid hlistLen_ne h_ge h_hi h_exact
  exact cpsTripleWithin_seq_same_cr hF hW

set_option maxRecDepth 8000 in
/-- Short path keeping concrete `frontAfterSavePostShort` (no ∃). -/
theorem extractWalkInitCall_short_toAfterSave_concrete
    (spC : Word) (s : ExtractSaved)
    (txBase lenW toBuf isCreationPtr : Word)
    (txBytes : List (BitVec 8))
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
    cpsTripleWithin ((1 + 15) + (1 + (1 + 1)))
      WalkInitJalPc AfterSaveCursor extractLinkedCode
      (frontTypeLoadPost spC s txBase lenW toBuf isCreationPtr txBytes)
      (frontAfterSavePostShort spC s txBase lenW toBuf isCreationPtr txBytes) := by
  set inner := (teerTxTypeDispatch txBytes).2.2
  set listOff := inner.toNat
  set listLen := lenW - inner
  have hCall := extractWalkInitCall_short_fromFrontTypeLoad_owned spC s
    txBase lenW toBuf isCreationPtr txBytes
    hsalign hoff hover hvalid hlen h_ge h_hi h_exact
  have hSave := extractWalkInitBneSave_owned spC s
    txBase lenW toBuf isCreationPtr
    (shortWalkCursor txBase listOff)
    (shortWalkEnd txBase listLen listOff)
    txBytes
  have hCall' : cpsTripleWithin (1 + 15) WalkInitJalPc LinkWalkInit extractLinkedCode
      (frontTypeLoadPost spC s txBase lenW toBuf isCreationPtr txBytes)
      (walkFrameAmbient spC s toBuf isCreationPtr **
        walkInitAmbient txBase lenW
          (teerTxTypeDispatch txBytes).2.1 inner **
        extractWalkInitCommon txBase txBytes **
        ((.x10 ↦ᵣ shortWalkCursor txBase listOff) **
          (.x11 ↦ᵣ shortWalkEnd txBase listLen listOff) **
          (.x12 ↦ᵣ (0 : Word))) **
        regOwn .x21 ** regOwn .x22) := by
    refine cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => by
      simp only [extractWalkInitShortOkRegs, shortWalkCursor, shortWalkEnd,
        listOff, listLen, inner] at hq ⊢
      xperm_hyp hq) hCall
  have hseq := cpsTripleWithin_seq_same_cr hCall' hSave
  exact cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => by
    simp only [frontAfterSavePostShort, shortWalkCursor, shortWalkEnd,
      listOff, listLen, inner] at hq ⊢
    xperm_hyp hq) hseq

#print axioms extractWalkInitCall_fromFrontTypeLoad_owned
#print axioms extractWalkInitOkNested_owned
#print axioms extractWalkInitOkFail_toAfterSave_owned
#print axioms extractWalkInitCall_toAfterSave_owned
#print axioms extractFrontToAfterSave
#print axioms extractWalkInitCall_short_fromFrontTypeLoad_owned
#print axioms extractWalkInitBneSave_owned
#print axioms extractWalkInitCall_short_toAfterSave_owned
#print axioms extractWalkInitCall_short_toAfterSave_concrete

set_option maxRecDepth 8000 in
/-- E → AfterSave short path with concrete `frontAfterSavePostShort` (no ∃). -/
theorem extractFrontToAfterSave_short_concrete
    (sp0 spC : Word) (s : ExtractSaved)
    (txBase lenW toBuf isCreationPtr : Word)
    (old5 old6 old7 old14 old15 old16 : Word)
    (txBytes : List (BitVec 8))
    (hspC : spC = sp0 + signExtend12 (-80 : BitVec 12))
    (htalign : toBuf.toNat % 8 = 0)
    (htover : toBuf.toNat + 16 < 2 ^ 64)
    (htvalid : isValidMemAccess (toBuf + (16 : Word)) = true)
    (hlen : lenW = BitVec.ofNat 64 txBytes.length)
    (hsuccess : (teerTxTypeDispatch txBytes).1 = (0 : Word))
    (halign : txBase.toNat % 8 = 0)
    (hover : txBase.toNat + txBytes.length < 2 ^ 64)
    (hvalid0 : isValidByteAccess (txBase + BitVec.ofNat 64 0) = true)
    (hoff : (teerTxTypeDispatch txBytes).2.2.toNat < txBytes.length)
    (hinover : txBase.toNat + (teerTxTypeDispatch txBytes).2.2.toNat < 2 ^ 64)
    (hinvalid : isValidByteAccess
      (txBase + BitVec.ofNat 64 (teerTxTypeDispatch txBytes).2.2.toNat) = true)
    (hlistLen_ne : (lenW - (teerTxTypeDispatch txBytes).2.2) ≠ (0 : Word))
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
    cpsTripleWithin
      (((14 + 4) + ((6 + (1 + nTypeSteps) + 1) + 8)) +
        ((1 + 15) + (1 + (1 + 1))))
      E AfterSaveCursor extractLinkedCode
      ((.x2 ↦ᵣ sp0) ** regsAt extractFrame (extractSavedVals s) **
        frameSlotsOwn extractFrame spC ** extractSpareSlot spC **
        prologueAbiRest txBase lenW toBuf isCreationPtr
          old5 old6 old7 old14 old15 old16 **
        extractToBufOwn toBuf ** memOwn isCreationPtr **
        frontExtraAmbient txBase txBytes)
      (frontAfterSavePostShort spC s txBase lenW toBuf isCreationPtr txBytes) := by
  have hF := extractFrontThenTypeLoad sp0 spC s txBase lenW toBuf isCreationPtr
    old5 old6 old7 old14 old15 old16 txBytes
    hspC htalign htover htvalid hlen hsuccess halign hover hvalid0
  have hW := extractWalkInitCall_short_toAfterSave_concrete spC s
    txBase lenW toBuf isCreationPtr txBytes
    halign hoff hinover hinvalid hlistLen_ne h_ge h_hi h_exact
  exact cpsTripleWithin_seq_same_cr hF hW

#print axioms extractFrontToAfterSave_short
#print axioms extractFrontToAfterSave_short_concrete

end EvmAsm.Codegen.TxExtractToAddressSpec
