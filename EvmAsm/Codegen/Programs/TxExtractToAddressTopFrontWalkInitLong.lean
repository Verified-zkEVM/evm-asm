/-
  Front typeLoad → long walk_init AfterSave with concrete longWalkCursor/End.
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.SAsm.AbiFrame
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Codegen.Programs.TxExtractToAddressTopFrontWalkInit
import EvmAsm.Codegen.Programs.TxExtractToAddressTopWalkInitLong
import EvmAsm.Codegen.Programs.TxExtractToAddressWalkInit
import EvmAsm.Codegen.Programs.TxIntrinsicStateGasSpec
import EvmAsm.Codegen.Programs.TxTypeDispatchSpec

namespace EvmAsm.Codegen.TxExtractToAddressSpec

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
open EvmAsm.Codegen.TxIntrinsicStateGasSpec (extractToBufOwn nTypeSteps)
open EvmAsm.Codegen.TxTypeDispatchSpec (teerTxTypeDispatch)
open EvmAsm.EL.RLP

private theorem regIs_imp_regOwn (r : Reg) (v : Word) :
    ∀ h, (r ↦ᵣ v) h → regOwn r h :=
  fun _ hx => ⟨v, hx⟩

private theorem walkFrameAmbient_pcFree' (spC : Word) (s : ExtractSaved)
    (toBuf isCreationPtr : Word) :
    (walkFrameAmbient spC s toBuf isCreationPtr).pcFree := by
  unfold walkFrameAmbient extractToBufOwn
  repeat first
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

/-- Long AfterSave post with concrete long walk cursor/end. -/
def frontAfterSavePostLong (spC : Word) (s : ExtractSaved)
    (txBase lenW toBuf isCreationPtr : Word)
    (txBytes : List (BitVec 8))
    (hoff : (teerTxTypeDispatch txBytes).2.2.toNat < txBytes.length) : Assertion :=
  walkFrameAmbient spC s toBuf isCreationPtr **
    extractAfterSavePost txBase lenW
      (teerTxTypeDispatch txBytes).2.1 (teerTxTypeDispatch txBytes).2.2
      (longWalkCursor txBase txBytes
        (teerTxTypeDispatch txBytes).2.2.toNat hoff)
      (longWalkEnd txBase (lenW - (teerTxTypeDispatch txBytes).2.2)
        (teerTxTypeDispatch txBytes).2.2.toNat)
      txBytes

set_option maxRecDepth 8000 in
/-- WalkInitJalPc → LinkWalkInit long path under frontTypeLoadPost ambient. -/
theorem extractWalkInitCall_long_fromFrontTypeLoad_owned
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
    (h_ge_f8 : ¬ BitVec.ult
        ((txBytes[(teerTxTypeDispatch txBytes).2.2.toNat]'hoff).zeroExtend 64)
        (0xf8 : Word) = true)
    (hllen : (teerTxTypeDispatch txBytes).2.2.toNat + 1 +
      ((txBytes[(teerTxTypeDispatch txBytes).2.2.toNat]'hoff).zeroExtend 64 -
        (0xf7 : Word)).toNat ≤ txBytes.length)
    (hlover : txBase.toNat + ((teerTxTypeDispatch txBytes).2.2.toNat + 1 +
      ((txBytes[(teerTxTypeDispatch txBytes).2.2.toNat]'hoff).zeroExtend 64 -
        (0xf7 : Word)).toNat) ≤ 2 ^ 64)
    (hlvalid : ∀ k, k < ((txBytes[(teerTxTypeDispatch txBytes).2.2.toNat]'hoff).zeroExtend 64 -
        (0xf7 : Word)).toNat →
      isValidByteAccess (txBase + BitVec.ofNat 64
        ((teerTxTypeDispatch txBytes).2.2.toNat + 1 + k)) = true)
    (hoff1 : (teerTxTypeDispatch txBytes).2.2.toNat + 1 < txBytes.length)
    (h_fits : ¬ BitVec.ult
        ((txBase + BitVec.ofNat 64 (teerTxTypeDispatch txBytes).2.2.toNat) +
          (lenW - (teerTxTypeDispatch txBytes).2.2))
        ((txBase + BitVec.ofNat 64 (teerTxTypeDispatch txBytes).2.2.toNat) +
          (((txBytes[(teerTxTypeDispatch txBytes).2.2.toNat]'hoff).zeroExtend 64 -
            (0xf7 : Word)) + signExtend12 (1 : BitVec 12))) = true)
    (h_llz : (txBytes[(teerTxTypeDispatch txBytes).2.2.toNat + 1]'hoff1).zeroExtend 64 ≠
      (0 : Word))
    (h_min : ¬ BitVec.ult (BitVec.ofNat 64 (Nat.fromBytesBE
        ((txBytes.drop ((teerTxTypeDispatch txBytes).2.2.toNat + 1)).take
          ((txBytes[(teerTxTypeDispatch txBytes).2.2.toNat]'hoff).zeroExtend 64 -
            (0xf7 : Word)).toNat))) (56 : Word) = true)
    (h_match : ((txBase + BitVec.ofNat 64 (teerTxTypeDispatch txBytes).2.2.toNat) +
          (((txBytes[(teerTxTypeDispatch txBytes).2.2.toNat]'hoff).zeroExtend 64 -
            (0xf7 : Word)) + signExtend12 (1 : BitVec 12))) +
        BitVec.ofNat 64 (Nat.fromBytesBE
          ((txBytes.drop ((teerTxTypeDispatch txBytes).2.2.toNat + 1)).take
            ((txBytes[(teerTxTypeDispatch txBytes).2.2.toNat]'hoff).zeroExtend 64 -
              (0xf7 : Word)).toNat))
      = (txBase + BitVec.ofNat 64 (teerTxTypeDispatch txBytes).2.2.toNat) +
          (lenW - (teerTxTypeDispatch txBytes).2.2)) :
    cpsTripleWithin
      (1 + (7 * ((txBytes[(teerTxTypeDispatch txBytes).2.2.toNat]'hoff).zeroExtend 64 -
        (0xf7 : Word)).toNat + 25))
      WalkInitJalPc LinkWalkInit extractLinkedCode
      (frontTypeLoadPost spC s txBase lenW toBuf isCreationPtr txBytes)
      (walkFrameAmbient spC s toBuf isCreationPtr **
        walkInitAmbient txBase lenW
          (teerTxTypeDispatch txBytes).2.1 (teerTxTypeDispatch txBytes).2.2 **
        extractWalkInitCommon txBase txBytes **
        extractWalkInitLongOkRegs txBase (lenW - (teerTxTypeDispatch txBytes).2.2)
          txBytes (teerTxTypeDispatch txBytes).2.2.toNat hoff **
        regOwn .x21 ** regOwn .x22) := by
  have h0 := extractWalkInitCall_long_ok_framed_s5s6 txBase lenW txBytes LinkType
    hsalign hoff hover hvalid hlen h_ge h_ge_f8 hllen hlover hlvalid hoff1
    h_fits h_llz h_min h_match
  have hF := cpsTripleWithin_frameR
    (walkFrameAmbient spC s toBuf isCreationPtr)
    (walkFrameAmbient_pcFree' spC s toBuf isCreationPtr) h0
  refine cpsTripleWithin_weaken (fun h hp => ?_) (fun _ hq => by xperm_hyp hq) hF
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
/-- Long path keeping concrete `frontAfterSavePostLong` (no ∃). -/
theorem extractWalkInitCall_long_toAfterSave_concrete
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
    (h_ge_f8 : ¬ BitVec.ult
        ((txBytes[(teerTxTypeDispatch txBytes).2.2.toNat]'hoff).zeroExtend 64)
        (0xf8 : Word) = true)
    (hllen : (teerTxTypeDispatch txBytes).2.2.toNat + 1 +
      ((txBytes[(teerTxTypeDispatch txBytes).2.2.toNat]'hoff).zeroExtend 64 -
        (0xf7 : Word)).toNat ≤ txBytes.length)
    (hlover : txBase.toNat + ((teerTxTypeDispatch txBytes).2.2.toNat + 1 +
      ((txBytes[(teerTxTypeDispatch txBytes).2.2.toNat]'hoff).zeroExtend 64 -
        (0xf7 : Word)).toNat) ≤ 2 ^ 64)
    (hlvalid : ∀ k, k < ((txBytes[(teerTxTypeDispatch txBytes).2.2.toNat]'hoff).zeroExtend 64 -
        (0xf7 : Word)).toNat →
      isValidByteAccess (txBase + BitVec.ofNat 64
        ((teerTxTypeDispatch txBytes).2.2.toNat + 1 + k)) = true)
    (hoff1 : (teerTxTypeDispatch txBytes).2.2.toNat + 1 < txBytes.length)
    (h_fits : ¬ BitVec.ult
        ((txBase + BitVec.ofNat 64 (teerTxTypeDispatch txBytes).2.2.toNat) +
          (lenW - (teerTxTypeDispatch txBytes).2.2))
        ((txBase + BitVec.ofNat 64 (teerTxTypeDispatch txBytes).2.2.toNat) +
          (((txBytes[(teerTxTypeDispatch txBytes).2.2.toNat]'hoff).zeroExtend 64 -
            (0xf7 : Word)) + signExtend12 (1 : BitVec 12))) = true)
    (h_llz : (txBytes[(teerTxTypeDispatch txBytes).2.2.toNat + 1]'hoff1).zeroExtend 64 ≠
      (0 : Word))
    (h_min : ¬ BitVec.ult (BitVec.ofNat 64 (Nat.fromBytesBE
        ((txBytes.drop ((teerTxTypeDispatch txBytes).2.2.toNat + 1)).take
          ((txBytes[(teerTxTypeDispatch txBytes).2.2.toNat]'hoff).zeroExtend 64 -
            (0xf7 : Word)).toNat))) (56 : Word) = true)
    (h_match : ((txBase + BitVec.ofNat 64 (teerTxTypeDispatch txBytes).2.2.toNat) +
          (((txBytes[(teerTxTypeDispatch txBytes).2.2.toNat]'hoff).zeroExtend 64 -
            (0xf7 : Word)) + signExtend12 (1 : BitVec 12))) +
        BitVec.ofNat 64 (Nat.fromBytesBE
          ((txBytes.drop ((teerTxTypeDispatch txBytes).2.2.toNat + 1)).take
            ((txBytes[(teerTxTypeDispatch txBytes).2.2.toNat]'hoff).zeroExtend 64 -
              (0xf7 : Word)).toNat))
      = (txBase + BitVec.ofNat 64 (teerTxTypeDispatch txBytes).2.2.toNat) +
          (lenW - (teerTxTypeDispatch txBytes).2.2)) :
    cpsTripleWithin
      ((1 + (7 * ((txBytes[(teerTxTypeDispatch txBytes).2.2.toNat]'hoff).zeroExtend 64 -
          (0xf7 : Word)).toNat + 25)) + (1 + (1 + 1)))
      WalkInitJalPc AfterSaveCursor extractLinkedCode
      (frontTypeLoadPost spC s txBase lenW toBuf isCreationPtr txBytes)
      (frontAfterSavePostLong spC s txBase lenW toBuf isCreationPtr txBytes hoff) := by
  set inner := (teerTxTypeDispatch txBytes).2.2
  set listOff := inner.toNat
  set listLen := lenW - inner
  have hCall := extractWalkInitCall_long_fromFrontTypeLoad_owned spC s
    txBase lenW toBuf isCreationPtr txBytes
    hsalign hoff hover hvalid hlen h_ge h_ge_f8 hllen hlover hlvalid hoff1
    h_fits h_llz h_min h_match
  have hSave := extractWalkInitBneSave_owned spC s
    txBase lenW toBuf isCreationPtr
    (longWalkCursor txBase txBytes listOff hoff)
    (longWalkEnd txBase listLen listOff)
    txBytes
  have hCall' : cpsTripleWithin
      (1 + (7 * ((txBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat + 25))
      WalkInitJalPc LinkWalkInit extractLinkedCode
      (frontTypeLoadPost spC s txBase lenW toBuf isCreationPtr txBytes)
      (walkFrameAmbient spC s toBuf isCreationPtr **
        walkInitAmbient txBase lenW
          (teerTxTypeDispatch txBytes).2.1 inner **
        extractWalkInitCommon txBase txBytes **
        ((.x10 ↦ᵣ longWalkCursor txBase txBytes listOff hoff) **
          (.x11 ↦ᵣ longWalkEnd txBase listLen listOff) **
          (.x12 ↦ᵣ (0 : Word))) **
        regOwn .x21 ** regOwn .x22) := by
    refine cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => by
      simp only [extractWalkInitLongOkRegs, longWalkCursor, longWalkEnd,
        listOff, listLen, inner] at hq ⊢
      xperm_hyp hq) hCall
  have hseq := cpsTripleWithin_seq_same_cr hCall' hSave
  exact cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => by
    simp only [frontAfterSavePostLong, longWalkCursor, longWalkEnd,
      listOff, listLen, inner] at hq ⊢
    xperm_hyp hq) hseq

set_option maxRecDepth 8000 in
/-- E → AfterSave long path with concrete `frontAfterSavePostLong` (no ∃). -/
theorem extractFrontToAfterSave_long_concrete
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
    (h_ge_f8 : ¬ BitVec.ult
        ((txBytes[(teerTxTypeDispatch txBytes).2.2.toNat]'hoff).zeroExtend 64)
        (0xf8 : Word) = true)
    (hllen : (teerTxTypeDispatch txBytes).2.2.toNat + 1 +
      ((txBytes[(teerTxTypeDispatch txBytes).2.2.toNat]'hoff).zeroExtend 64 -
        (0xf7 : Word)).toNat ≤ txBytes.length)
    (hlover : txBase.toNat + ((teerTxTypeDispatch txBytes).2.2.toNat + 1 +
      ((txBytes[(teerTxTypeDispatch txBytes).2.2.toNat]'hoff).zeroExtend 64 -
        (0xf7 : Word)).toNat) ≤ 2 ^ 64)
    (hlvalid : ∀ k, k < ((txBytes[(teerTxTypeDispatch txBytes).2.2.toNat]'hoff).zeroExtend 64 -
        (0xf7 : Word)).toNat →
      isValidByteAccess (txBase + BitVec.ofNat 64
        ((teerTxTypeDispatch txBytes).2.2.toNat + 1 + k)) = true)
    (hoff1 : (teerTxTypeDispatch txBytes).2.2.toNat + 1 < txBytes.length)
    (h_fits : ¬ BitVec.ult
        ((txBase + BitVec.ofNat 64 (teerTxTypeDispatch txBytes).2.2.toNat) +
          (lenW - (teerTxTypeDispatch txBytes).2.2))
        ((txBase + BitVec.ofNat 64 (teerTxTypeDispatch txBytes).2.2.toNat) +
          (((txBytes[(teerTxTypeDispatch txBytes).2.2.toNat]'hoff).zeroExtend 64 -
            (0xf7 : Word)) + signExtend12 (1 : BitVec 12))) = true)
    (h_llz : (txBytes[(teerTxTypeDispatch txBytes).2.2.toNat + 1]'hoff1).zeroExtend 64 ≠
      (0 : Word))
    (h_min : ¬ BitVec.ult (BitVec.ofNat 64 (Nat.fromBytesBE
        ((txBytes.drop ((teerTxTypeDispatch txBytes).2.2.toNat + 1)).take
          ((txBytes[(teerTxTypeDispatch txBytes).2.2.toNat]'hoff).zeroExtend 64 -
            (0xf7 : Word)).toNat))) (56 : Word) = true)
    (h_match : ((txBase + BitVec.ofNat 64 (teerTxTypeDispatch txBytes).2.2.toNat) +
          (((txBytes[(teerTxTypeDispatch txBytes).2.2.toNat]'hoff).zeroExtend 64 -
            (0xf7 : Word)) + signExtend12 (1 : BitVec 12))) +
        BitVec.ofNat 64 (Nat.fromBytesBE
          ((txBytes.drop ((teerTxTypeDispatch txBytes).2.2.toNat + 1)).take
            ((txBytes[(teerTxTypeDispatch txBytes).2.2.toNat]'hoff).zeroExtend 64 -
              (0xf7 : Word)).toNat))
      = (txBase + BitVec.ofNat 64 (teerTxTypeDispatch txBytes).2.2.toNat) +
          (lenW - (teerTxTypeDispatch txBytes).2.2)) :
    cpsTripleWithin
      (((14 + 4) + ((6 + (1 + nTypeSteps) + 1) + 8)) +
        ((1 + (7 * ((txBytes[(teerTxTypeDispatch txBytes).2.2.toNat]'hoff).zeroExtend 64 -
            (0xf7 : Word)).toNat + 25)) + (1 + (1 + 1))))
      E AfterSaveCursor extractLinkedCode
      ((.x2 ↦ᵣ sp0) ** regsAt extractFrame (extractSavedVals s) **
        frameSlotsOwn extractFrame spC ** extractSpareSlot spC **
        prologueAbiRest txBase lenW toBuf isCreationPtr
          old5 old6 old7 old14 old15 old16 **
        extractToBufOwn toBuf ** memOwn isCreationPtr **
        frontExtraAmbient txBase txBytes)
      (frontAfterSavePostLong spC s txBase lenW toBuf isCreationPtr txBytes hoff) := by
  have hF := extractFrontThenTypeLoad sp0 spC s txBase lenW toBuf isCreationPtr
    old5 old6 old7 old14 old15 old16 txBytes
    hspC htalign htover htvalid hlen hsuccess halign hover hvalid0
  have hW := extractWalkInitCall_long_toAfterSave_concrete spC s
    txBase lenW toBuf isCreationPtr txBytes
    halign hoff hinover hinvalid hlistLen_ne h_ge h_ge_f8 hllen hlover hlvalid hoff1
    h_fits h_llz h_min h_match
  exact cpsTripleWithin_seq_same_cr hF hW

#print axioms extractWalkInitCall_long_fromFrontTypeLoad_owned
#print axioms extractWalkInitCall_long_toAfterSave_concrete
#print axioms extractFrontToAfterSave_long_concrete

end EvmAsm.Codegen.TxExtractToAddressSpec
