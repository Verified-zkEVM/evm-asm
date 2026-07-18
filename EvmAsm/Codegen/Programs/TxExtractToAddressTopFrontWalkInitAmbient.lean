/-
  Ambient dual: short walk_init Front → AfterSave under regionBase/loadPtr.
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Codegen.Programs.TxExtractToAddressTopFrontWalkInit
import EvmAsm.Codegen.Programs.TxExtractToAddressTopFrontMid
import EvmAsm.Codegen.Programs.TxExtractToAddressTopFrontJoin
import EvmAsm.Codegen.Programs.TxExtractToAddressTopWalkInitOk
import EvmAsm.Codegen.Programs.TxExtractToAddressTopWalkInitShort
import EvmAsm.Codegen.Programs.TxExtractToAddressTopWalkInitShortAmbient
import EvmAsm.Codegen.Programs.TxExtractToAddressTopTypeBranch
import EvmAsm.Codegen.Programs.TxExtractToAddressTopMidOwned
import EvmAsm.Codegen.Programs.TxExtractToAddressWalkInit
import EvmAsm.Codegen.Programs.TxExtractToAddressWalkNext
import EvmAsm.Codegen.Programs.TxTypeDispatchAmbient
import EvmAsm.Codegen.Programs.TxTypeDispatchSpec
import EvmAsm.Codegen.Programs.TxIntrinsicStateGasSpec

namespace EvmAsm.Codegen.TxExtractToAddressSpec

open EvmAsm.Rv64
open EvmAsm.Codegen
open EvmAsm.Codegen.TxTypeDispatchSpec
open EvmAsm.Codegen.TxIntrinsicStateGasSpec (extractToBufOwn)

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

/-- Ambient frontTypeLoadPost: s0=loadPtr, full blob region. -/
def frontTypeLoadPostAmbient (spC : Word) (s : ExtractSaved)
    (regionBase loadPtr lenW toBuf isCreationPtr : Word)
    (bs : List (BitVec 8)) (off len : Nat) : Assertion :=
  typeMidAmbient spC s toBuf isCreationPtr **
    (.x1 ↦ᵣ LinkType) ** (.x0 ↦ᵣ (0 : Word)) **
    (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
    (.x5 ↦ᵣ TeaInnerAddr) **
    (.x10 ↦ᵣ (loadPtr + (teerTxTypeDispatch (txSlice bs off len)).2.2)) **
    (.x11 ↦ᵣ (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) **
    (.x20 ↦ᵣ (teerTxTypeDispatch (txSlice bs off len)).2.1) **
    (.x30 ↦ᵣ (teerTxTypeDispatch (txSlice bs off len)).2.2) **
    bytesRegion regionBase bs **
    (TeaTypeAddr ↦ₘ (teerTxTypeDispatch (txSlice bs off len)).2.1) **
    (TeaInnerAddr ↦ₘ (teerTxTypeDispatch (txSlice bs off len)).2.2) **
    regOwn .x6 ** regOwn .x7 **
    regOwn .x12 ** regOwn .x13 **
    regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
    regOwn .x28 ** regOwn .x29 ** regOwn .x31

/-- AfterSave post ambient: loadPtr in walkInitAmbient, regionBase blob. -/
def extractAfterSavePostAmbient (loadPtr regionBase lenW typeW innerW
    cursor endPtr : Word) (bs : List (BitVec 8)) : Assertion :=
  walkInitAmbient loadPtr lenW typeW innerW **
    walkInitRest regionBase bs **
      (.x0 ↦ᵣ (0 : Word)) **
      (.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ (0 : Word)) **
      (.x21 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr)

/-- Short AfterSave post ambient with concrete cursor/end at abs listOff. -/
def frontAfterSavePostShortAmbient (spC : Word) (s : ExtractSaved)
    (regionBase loadPtr lenW toBuf isCreationPtr : Word)
    (bs : List (BitVec 8)) (off len : Nat) : Assertion :=
  walkFrameAmbient spC s toBuf isCreationPtr **
    extractAfterSavePostAmbient loadPtr regionBase lenW
      (teerTxTypeDispatch (txSlice bs off len)).2.1
      (teerTxTypeDispatch (txSlice bs off len)).2.2
      (shortWalkCursor regionBase
        (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat))
      (shortWalkEnd regionBase (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)
        (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat))
      bs

set_option maxRecDepth 8000 in
/-- BNE not-taken framed with split loadPtr ambient / regionBase rest. -/
theorem extractWalkInitBneOk_framed_ambient
    (loadPtr regionBase lenW typeW innerW cursor endPtr : Word)
    (bs : List (BitVec 8)) :
    cpsTripleWithin 1 LinkWalkInit AfterWalkInitOk extractLinkedCode
      (walkInitAmbient loadPtr lenW typeW innerW **
        walkInitRest regionBase bs **
          (.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) **
          (.x12 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)))
      (walkInitAmbient loadPtr lenW typeW innerW **
        walkInitRest regionBase bs **
          (.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) **
          (.x12 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) := by
  have h0 := extractWalkInitBneOk
  have hF := cpsTripleWithin_frameR
    (walkInitAmbient loadPtr lenW typeW innerW **
      walkInitRest regionBase bs **
        (.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr))
    (by pcf) h0
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hF

set_option maxRecDepth 8000 in
/-- Save cursor framed with split loadPtr / regionBase. -/
theorem extractSaveCursor_framed_ambient
    (loadPtr regionBase lenW typeW innerW cursor endPtr : Word)
    (bs : List (BitVec 8)) :
    cpsTripleWithin (1 + 1) AfterWalkInitOk AfterSaveCursor extractLinkedCode
      (walkInitAmbient loadPtr lenW typeW innerW **
        walkInitRest regionBase bs **
          (.x0 ↦ᵣ (0 : Word)) **
          (.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ (0 : Word)) **
          regOwn .x21 ** regOwn .x22)
      (walkInitAmbient loadPtr lenW typeW innerW **
        walkInitRest regionBase bs **
          (.x0 ↦ᵣ (0 : Word)) **
          (.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ (0 : Word)) **
          (.x21 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr)) := by
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ h => h)
    (cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x22)
      (P := walkInitAmbient loadPtr lenW typeW innerW **
        walkInitRest regionBase bs **
          (.x0 ↦ᵣ (0 : Word)) **
          (.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ (0 : Word)) **
          regOwn .x21)
      (fun s6Old => ?_))
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ h => h)
    (cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x21)
      (P := walkInitAmbient loadPtr lenW typeW innerW **
        walkInitRest regionBase bs **
          (.x0 ↦ᵣ (0 : Word)) **
          (.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ (0 : Word)) **
          (.x22 ↦ᵣ s6Old))
      (fun s5Old => ?_))
  have hs := extractSaveCursor cursor endPtr s5Old s6Old
  have hF := cpsTripleWithin_frameR
    (walkInitAmbient loadPtr lenW typeW innerW **
      walkInitRest regionBase bs **
        (.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (0 : Word)))
    (by pcf) hs
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hF

set_option maxRecDepth 8000 in
/-- BNE+save ambient split bases. -/
theorem extractWalkInitBneSave_ambient
    (loadPtr regionBase lenW typeW innerW cursor endPtr : Word)
    (bs : List (BitVec 8)) :
    cpsTripleWithin (1 + (1 + 1)) LinkWalkInit AfterSaveCursor extractLinkedCode
      (walkInitAmbient loadPtr lenW typeW innerW **
        walkInitRest regionBase bs **
          (.x0 ↦ᵣ (0 : Word)) **
          (.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ (0 : Word)) **
          regOwn .x21 ** regOwn .x22)
      (extractAfterSavePostAmbient loadPtr regionBase lenW typeW innerW
        cursor endPtr bs) := by
  have hbne := extractWalkInitBneOk_framed_ambient
    loadPtr regionBase lenW typeW innerW cursor endPtr bs
  have hbne' : cpsTripleWithin 1 LinkWalkInit AfterWalkInitOk extractLinkedCode
      (walkInitAmbient loadPtr lenW typeW innerW **
        walkInitRest regionBase bs **
          (.x0 ↦ᵣ (0 : Word)) **
          (.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ (0 : Word)) **
          regOwn .x21 ** regOwn .x22)
      (walkInitAmbient loadPtr lenW typeW innerW **
        walkInitRest regionBase bs **
          (.x0 ↦ᵣ (0 : Word)) **
          (.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ (0 : Word)) **
          regOwn .x21 ** regOwn .x22) := by
    have hF := cpsTripleWithin_frameR (regOwn .x21 ** regOwn .x22) (by pcf) hbne
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hF
  have hsave := extractSaveCursor_framed_ambient
    loadPtr regionBase lenW typeW innerW cursor endPtr bs
  have hseq := cpsTripleWithin_seq_same_cr hbne' hsave
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by
      simp only [extractAfterSavePostAmbient] at hq ⊢
      xperm_hyp hq) hseq

set_option maxRecDepth 8000 in
/-- BNE+save under walkFrame ambient (owned front). -/
theorem extractWalkInitBneSave_owned_ambient
    (spC : Word) (s : ExtractSaved)
    (loadPtr regionBase lenW toBuf isCreationPtr cursor endPtr : Word)
    (bs : List (BitVec 8)) (off len : Nat) :
    cpsTripleWithin (1 + (1 + 1)) LinkWalkInit AfterSaveCursor extractLinkedCode
      (walkFrameAmbient spC s toBuf isCreationPtr **
        walkInitAmbient loadPtr lenW
          (teerTxTypeDispatch (txSlice bs off len)).2.1
          (teerTxTypeDispatch (txSlice bs off len)).2.2 **
        extractWalkInitCommon regionBase bs **
        ((.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ (0 : Word))) **
        regOwn .x21 ** regOwn .x22)
      (walkFrameAmbient spC s toBuf isCreationPtr **
        extractAfterSavePostAmbient loadPtr regionBase lenW
          (teerTxTypeDispatch (txSlice bs off len)).2.1
          (teerTxTypeDispatch (txSlice bs off len)).2.2
          cursor endPtr bs) := by
  have h0 := extractWalkInitBneSave_ambient loadPtr regionBase lenW
    (teerTxTypeDispatch (txSlice bs off len)).2.1
    (teerTxTypeDispatch (txSlice bs off len)).2.2
    cursor endPtr bs
  have hF := cpsTripleWithin_frameR
    (walkFrameAmbient spC s toBuf isCreationPtr)
    (by unfold walkFrameAmbient extractToBufOwn; pcf) h0
  refine cpsTripleWithin_weaken (fun h hp => ?_) (fun _ hq => by xperm_hyp hq) hF
  simp only [extractWalkInitCommon, walkInitRest] at hp ⊢
  xperm_hyp hp

set_option maxRecDepth 8000 in
/-- WalkInitJalPc → LinkWalkInit under frontTypeLoadPostAmbient. -/
theorem extractWalkInitCall_short_fromFrontTypeLoad_owned_ambient
    (spC : Word) (s : ExtractSaved)
    (regionBase loadPtr lenW toBuf isCreationPtr : Word)
    (bs : List (BitVec 8)) (off len : Nat)
    (hptr : loadPtr = regionBase + BitVec.ofNat 64 off)
    (hsalign : regionBase.toNat % 8 = 0)
    (_hbound : off + len ≤ bs.length)
    (hoff : ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat < bs.length)
    (hover : regionBase.toNat +
        ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat < 2 ^ 64)
    (hvalid : isValidByteAccess
      (regionBase + BitVec.ofNat 64
        (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)) = true)
    (hspan : regionBase.toNat +
        (off + (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat) < 2 ^ 64)
    (hlen : (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2) ≠ (0 : Word))
    (h_ge : ¬ BitVec.ult
        ((bs[ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat]'hoff
          ).zeroExtend 64)
        (0xc0 : Word) = true)
    (h_hi : BitVec.ult
        ((bs[ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat]'hoff
          ).zeroExtend 64)
        (0xf8 : Word) = true)
    (h_exact : (regionBase + BitVec.ofNat 64
          (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)) +
        (((bs[ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat]'hoff
            ).zeroExtend 64 - (0xc0 : Word)) + signExtend12 (1 : BitVec 12)) =
      (regionBase + BitVec.ofNat 64
          (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) :
    cpsTripleWithin (1 + 15) WalkInitJalPc LinkWalkInit extractLinkedCode
      (frontTypeLoadPostAmbient spC s regionBase loadPtr lenW toBuf isCreationPtr
        bs off len)
      (walkFrameAmbient spC s toBuf isCreationPtr **
        walkInitAmbient loadPtr lenW
          (teerTxTypeDispatch (txSlice bs off len)).2.1
          (teerTxTypeDispatch (txSlice bs off len)).2.2 **
        extractWalkInitCommon regionBase bs **
        extractWalkInitShortOkRegs regionBase
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)
          (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat) **
        regOwn .x21 ** regOwn .x22) := by
  have h0 := extractWalkInitCall_short_ok_framed_s5s6_ambient
    regionBase loadPtr lenW bs off len LinkType hptr hsalign _hbound
    hoff hover hvalid hspan hlen h_ge h_hi h_exact
  have hF := cpsTripleWithin_frameR
    (walkFrameAmbient spC s toBuf isCreationPtr)
    (by unfold walkFrameAmbient extractToBufOwn; pcf) h0
  refine cpsTripleWithin_weaken (fun h hp => ?_) (fun _ hq => by xperm_hyp hq) hF
  have hp1 :
      (walkFrameAmbient spC s toBuf isCreationPtr **
        ((.x1 ↦ᵣ LinkType) ** (.x0 ↦ᵣ (0 : Word)) **
          (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
          (.x5 ↦ᵣ TeaInnerAddr) **
          (.x10 ↦ᵣ (loadPtr + (teerTxTypeDispatch (txSlice bs off len)).2.2)) **
          (.x11 ↦ᵣ (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) **
          (.x20 ↦ᵣ (teerTxTypeDispatch (txSlice bs off len)).2.1) **
          (.x30 ↦ᵣ (teerTxTypeDispatch (txSlice bs off len)).2.2) **
          bytesRegion regionBase bs **
          (TeaTypeAddr ↦ₘ (teerTxTypeDispatch (txSlice bs off len)).2.1) **
          (TeaInnerAddr ↦ₘ (teerTxTypeDispatch (txSlice bs off len)).2.2) **
          regOwn .x6 ** regOwn .x7 **
          regOwn .x12 ** regOwn .x13 **
          regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x31 **
          (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6))) h := by
    simp only [frontTypeLoadPostAmbient, typeMidAmbient, walkFrameAmbient,
      extractToBufOwn] at hp ⊢
    xperm_hyp hp
  have hnest :
      ((walkFrameAmbient spC s toBuf isCreationPtr **
          ((.x1 ↦ᵣ LinkType) ** (.x0 ↦ᵣ (0 : Word)) **
            (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
            (.x5 ↦ᵣ TeaInnerAddr) **
            (.x10 ↦ᵣ (loadPtr + (teerTxTypeDispatch (txSlice bs off len)).2.2)) **
            (.x11 ↦ᵣ (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) **
            (.x20 ↦ᵣ (teerTxTypeDispatch (txSlice bs off len)).2.1) **
            (.x30 ↦ᵣ (teerTxTypeDispatch (txSlice bs off len)).2.2) **
            bytesRegion regionBase bs **
            (TeaTypeAddr ↦ₘ (teerTxTypeDispatch (txSlice bs off len)).2.1) **
            (TeaInnerAddr ↦ₘ (teerTxTypeDispatch (txSlice bs off len)).2.2) **
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
/-- Short ambient: WalkInitJalPc → AfterSaveCursor concrete cursor/end. -/
theorem extractWalkInitCall_short_toAfterSave_concrete_ambient
    (spC : Word) (s : ExtractSaved)
    (regionBase loadPtr lenW toBuf isCreationPtr : Word)
    (bs : List (BitVec 8)) (off len : Nat)
    (hptr : loadPtr = regionBase + BitVec.ofNat 64 off)
    (hsalign : regionBase.toNat % 8 = 0)
    (_hbound : off + len ≤ bs.length)
    (hoff : ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat < bs.length)
    (hover : regionBase.toNat +
        ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat < 2 ^ 64)
    (hvalid : isValidByteAccess
      (regionBase + BitVec.ofNat 64
        (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)) = true)
    (hspan : regionBase.toNat +
        (off + (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat) < 2 ^ 64)
    (hlen : (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2) ≠ (0 : Word))
    (h_ge : ¬ BitVec.ult
        ((bs[ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat]'hoff
          ).zeroExtend 64)
        (0xc0 : Word) = true)
    (h_hi : BitVec.ult
        ((bs[ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat]'hoff
          ).zeroExtend 64)
        (0xf8 : Word) = true)
    (h_exact : (regionBase + BitVec.ofNat 64
          (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)) +
        (((bs[ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat]'hoff
            ).zeroExtend 64 - (0xc0 : Word)) + signExtend12 (1 : BitVec 12)) =
      (regionBase + BitVec.ofNat 64
          (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) :
    cpsTripleWithin ((1 + 15) + (1 + (1 + 1)))
      WalkInitJalPc AfterSaveCursor extractLinkedCode
      (frontTypeLoadPostAmbient spC s regionBase loadPtr lenW toBuf isCreationPtr
        bs off len)
      (frontAfterSavePostShortAmbient spC s regionBase loadPtr lenW toBuf
        isCreationPtr bs off len) := by
  set inner := (teerTxTypeDispatch (txSlice bs off len)).2.2
  set listOff := ambientAbsOff off inner.toNat
  set listLen := lenW - inner
  have hCall := extractWalkInitCall_short_fromFrontTypeLoad_owned_ambient
    spC s regionBase loadPtr lenW toBuf isCreationPtr bs off len
    hptr hsalign _hbound hoff hover hvalid hspan hlen h_ge h_hi h_exact
  have hSave := extractWalkInitBneSave_owned_ambient spC s
    loadPtr regionBase lenW toBuf isCreationPtr
    (shortWalkCursor regionBase listOff)
    (shortWalkEnd regionBase listLen listOff)
    bs off len
  have hCall' : cpsTripleWithin (1 + 15) WalkInitJalPc LinkWalkInit extractLinkedCode
      (frontTypeLoadPostAmbient spC s regionBase loadPtr lenW toBuf isCreationPtr
        bs off len)
      (walkFrameAmbient spC s toBuf isCreationPtr **
        walkInitAmbient loadPtr lenW
          (teerTxTypeDispatch (txSlice bs off len)).2.1 inner **
        extractWalkInitCommon regionBase bs **
        ((.x10 ↦ᵣ shortWalkCursor regionBase listOff) **
          (.x11 ↦ᵣ shortWalkEnd regionBase listLen listOff) **
          (.x12 ↦ᵣ (0 : Word))) **
        regOwn .x21 ** regOwn .x22) := by
    refine cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => by
      simp only [extractWalkInitShortOkRegs, shortWalkCursor, shortWalkEnd,
        listOff, listLen, inner] at hq ⊢
      xperm_hyp hq) hCall
  have hseq := cpsTripleWithin_seq_same_cr hCall' hSave
  exact cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => by
    simp only [frontAfterSavePostShortAmbient, extractAfterSavePostAmbient,
      shortWalkCursor, shortWalkEnd, listOff, listLen, inner] at hq ⊢
    xperm_hyp hq) hseq

/-- Split-base AfterSave frame: x8=loadPtr, bytesRegion regionBase/bs. -/
def afterSaveFrameTyAmbient (loadPtr regionBase lenW typeW innerW
    cursor endPtr : Word) (bs : List (BitVec 8)) : Assertion :=
  (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
    (TeaTypeAddr ↦ₘ typeW) ** (TeaInnerAddr ↦ₘ innerW) **
    regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
    regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
    regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkWalkInit) **
    bytesRegion regionBase bs **
    (.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ (0 : Word)) **
    (.x21 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr)

/-- extractAfterSavePostAmbient → afterSaveFrameTyAmbient ** x20 ** regOwn x5 ** x0. -/
theorem afterSave_to_midJoinCore_ambient
    (loadPtr regionBase lenW typeW innerW cursor endPtr : Word)
    (bs : List (BitVec 8)) :
    ∀ h, extractAfterSavePostAmbient loadPtr regionBase lenW typeW innerW
        cursor endPtr bs h →
      (afterSaveFrameTyAmbient loadPtr regionBase lenW typeW innerW
          cursor endPtr bs **
        (.x20 ↦ᵣ typeW) ** regOwn .x5 ** (.x0 ↦ᵣ (0 : Word))) h := by
  intro h hp
  simp only [extractAfterSavePostAmbient, walkInitAmbient, walkInitRest,
    afterSaveFrameTyAmbient] at hp ⊢
  xperm_hyp hp

/-- Concrete short AfterSave ambient → MidJoin pre (split bases). -/
theorem frontAfterSavePostShortAmbient_to_midJoinPre
    (spC : Word) (s : ExtractSaved)
    (regionBase loadPtr lenW toBuf isCreationPtr : Word)
    (bs : List (BitVec 8)) (off len : Nat) :
    ∀ h, frontAfterSavePostShortAmbient spC s regionBase loadPtr lenW toBuf
        isCreationPtr bs off len h →
      (afterSaveFrameTyAmbient loadPtr regionBase lenW
          (teerTxTypeDispatch (txSlice bs off len)).2.1
          (teerTxTypeDispatch (txSlice bs off len)).2.2
          (shortWalkCursor regionBase
            (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat))
          (shortWalkEnd regionBase
            (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)
            (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat))
          bs **
        (.x20 ↦ᵣ (teerTxTypeDispatch (txSlice bs off len)).2.1) **
        regOwn .x5 ** (.x0 ↦ᵣ (0 : Word)) **
        midOwned spC s toBuf isCreationPtr s.s7) h := by
  intro h hp
  simp only [frontAfterSavePostShortAmbient] at hp
  obtain ⟨h1, h2, hd, hu, hW, hAS⟩ := hp
  have hM := walkFrame_to_midOwned spC s toBuf isCreationPtr h1 hW
  have hC := afterSave_to_midJoinCore_ambient loadPtr regionBase lenW
    (teerTxTypeDispatch (txSlice bs off len)).2.1
    (teerTxTypeDispatch (txSlice bs off len)).2.2
    (shortWalkCursor regionBase
      (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat))
    (shortWalkEnd regionBase
      (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)
      (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat))
    bs h2 hAS
  have hnest :
      ((afterSaveFrameTyAmbient loadPtr regionBase lenW
          (teerTxTypeDispatch (txSlice bs off len)).2.1
          (teerTxTypeDispatch (txSlice bs off len)).2.2
          (shortWalkCursor regionBase
            (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat))
          (shortWalkEnd regionBase
            (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)
            (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat))
          bs **
        (.x20 ↦ᵣ (teerTxTypeDispatch (txSlice bs off len)).2.1) **
        regOwn .x5 ** (.x0 ↦ᵣ (0 : Word))) **
      midOwned spC s toBuf isCreationPtr s.s7) h :=
    ⟨h2, h1, hd.symm,
      by rw [PartialState.union_comm_of_disjoint hd.symm, hu],
      hC, hM⟩
  xperm_hyp hnest

#print axioms extractWalkInitBneSave_ambient
#print axioms extractWalkInitCall_short_fromFrontTypeLoad_owned_ambient
#print axioms extractWalkInitCall_short_toAfterSave_concrete_ambient
#print axioms frontAfterSavePostShortAmbient_to_midJoinPre

end EvmAsm.Codegen.TxExtractToAddressSpec
