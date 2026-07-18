/-
  Ambient dual: long walk_init Front → AfterSave under regionBase/loadPtr.
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.SAsm.AbiFrame
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Codegen.Programs.TxExtractToAddressTopFrontWalkInit
import EvmAsm.Codegen.Programs.TxExtractToAddressTopFrontWalkInitAmbient
import EvmAsm.Codegen.Programs.TxExtractToAddressTopFrontMidAmbient
import EvmAsm.Codegen.Programs.TxExtractToAddressTopFrontJoin
import EvmAsm.Codegen.Programs.TxExtractToAddressTopMidOwned
import EvmAsm.Codegen.Programs.TxExtractToAddressTopWalkInitLongAmbient
import EvmAsm.Codegen.Programs.TxExtractToAddressWalkInit
import EvmAsm.Codegen.Programs.TxTypeDispatchAmbient
import EvmAsm.Codegen.Programs.TxTypeDispatchSpec
import EvmAsm.Codegen.Programs.TxIntrinsicStateGasSpec

namespace EvmAsm.Codegen.TxExtractToAddressSpec

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
open EvmAsm.Codegen.TxTypeDispatchSpec
open EvmAsm.Codegen.TxIntrinsicStateGasSpec (extractToBufOwn nTypeSteps)
open EvmAsm.EL.RLP

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

/-- Long AfterSave post ambient with concrete long cursor/end at abs listOff. -/
def frontAfterSavePostLongAmbient (spC : Word) (s : ExtractSaved)
    (regionBase loadPtr lenW toBuf isCreationPtr : Word)
    (bs : List (BitVec 8)) (off len : Nat)
    (hoff : ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat <
      bs.length) : Assertion :=
  walkFrameAmbient spC s toBuf isCreationPtr **
    extractAfterSavePostAmbient loadPtr regionBase lenW
      (teerTxTypeDispatch (txSlice bs off len)).2.1
      (teerTxTypeDispatch (txSlice bs off len)).2.2
      (longWalkCursorAmbient regionBase bs
        (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat) hoff)
      (longWalkEndAmbient regionBase (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)
        (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat))
      bs

set_option maxRecDepth 8000 in
/-- WalkInitJalPc → LinkWalkInit long path under frontTypeLoadPostAmbient. -/
theorem extractWalkInitCall_long_fromFrontTypeLoad_owned_ambient
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
    (h_ge_f8 : ¬ BitVec.ult
        ((bs[ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat]'hoff
          ).zeroExtend 64)
        (0xf8 : Word) = true)
    (hllen : ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat + 1 +
      ((bs[ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat]'hoff
          ).zeroExtend 64 - (0xf7 : Word)).toNat ≤ bs.length)
    (hlover : regionBase.toNat +
        (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat + 1 +
          ((bs[ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat]'hoff
              ).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64)
    (hlvalid : ∀ k, k <
        ((bs[ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat]'hoff
            ).zeroExtend 64 - (0xf7 : Word)).toNat →
      isValidByteAccess (regionBase + BitVec.ofNat 64
        (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat + 1 + k)) = true)
    (hoff1 : ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat + 1 <
      bs.length)
    (h_fits : ¬ BitVec.ult
        ((regionBase + BitVec.ofNat 64
            (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2))
        ((regionBase + BitVec.ofNat 64
            (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)) +
          (((bs[ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat]'hoff
              ).zeroExtend 64 - (0xf7 : Word)) + signExtend12 (1 : BitVec 12))) = true)
    (h_llz : (bs[ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat + 1]'hoff1
        ).zeroExtend 64 ≠ (0 : Word))
    (h_min : ¬ BitVec.ult (BitVec.ofNat 64 (Nat.fromBytesBE
        ((bs.drop (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat + 1)).take
          ((bs[ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat]'hoff
              ).zeroExtend 64 - (0xf7 : Word)).toNat))) (56 : Word) = true)
    (h_match : ((regionBase + BitVec.ofNat 64
            (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)) +
          (((bs[ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat]'hoff
              ).zeroExtend 64 - (0xf7 : Word)) + signExtend12 (1 : BitVec 12))) +
        BitVec.ofNat 64 (Nat.fromBytesBE
          ((bs.drop (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat + 1)).take
            ((bs[ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat]'hoff
                ).zeroExtend 64 - (0xf7 : Word)).toNat))
      = (regionBase + BitVec.ofNat 64
            (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) :
    cpsTripleWithin
      (1 + (7 * ((bs[ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat]'hoff
          ).zeroExtend 64 - (0xf7 : Word)).toNat + 25))
      WalkInitJalPc LinkWalkInit extractLinkedCode
      (frontTypeLoadPostAmbient spC s regionBase loadPtr lenW toBuf isCreationPtr
        bs off len)
      (walkFrameAmbient spC s toBuf isCreationPtr **
        walkInitAmbient loadPtr lenW
          (teerTxTypeDispatch (txSlice bs off len)).2.1
          (teerTxTypeDispatch (txSlice bs off len)).2.2 **
        extractWalkInitCommon regionBase bs **
        extractWalkInitLongOkRegs regionBase
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)
          bs (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat) hoff **
        regOwn .x21 ** regOwn .x22) := by
  have h0 := extractWalkInitCall_long_ok_framed_s5s6_ambient
    regionBase loadPtr lenW bs off len LinkType hptr hsalign _hbound
    hoff hover hvalid hspan hlen h_ge h_ge_f8 hllen hlover hlvalid hoff1
    h_fits h_llz h_min h_match
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
/-- Long ambient: WalkInitJalPc → AfterSaveCursor concrete cursor/end. -/
theorem extractWalkInitCall_long_toAfterSave_concrete_ambient
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
    (h_ge_f8 : ¬ BitVec.ult
        ((bs[ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat]'hoff
          ).zeroExtend 64)
        (0xf8 : Word) = true)
    (hllen : ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat + 1 +
      ((bs[ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat]'hoff
          ).zeroExtend 64 - (0xf7 : Word)).toNat ≤ bs.length)
    (hlover : regionBase.toNat +
        (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat + 1 +
          ((bs[ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat]'hoff
              ).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64)
    (hlvalid : ∀ k, k <
        ((bs[ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat]'hoff
            ).zeroExtend 64 - (0xf7 : Word)).toNat →
      isValidByteAccess (regionBase + BitVec.ofNat 64
        (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat + 1 + k)) = true)
    (hoff1 : ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat + 1 <
      bs.length)
    (h_fits : ¬ BitVec.ult
        ((regionBase + BitVec.ofNat 64
            (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2))
        ((regionBase + BitVec.ofNat 64
            (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)) +
          (((bs[ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat]'hoff
              ).zeroExtend 64 - (0xf7 : Word)) + signExtend12 (1 : BitVec 12))) = true)
    (h_llz : (bs[ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat + 1]'hoff1
        ).zeroExtend 64 ≠ (0 : Word))
    (h_min : ¬ BitVec.ult (BitVec.ofNat 64 (Nat.fromBytesBE
        ((bs.drop (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat + 1)).take
          ((bs[ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat]'hoff
              ).zeroExtend 64 - (0xf7 : Word)).toNat))) (56 : Word) = true)
    (h_match : ((regionBase + BitVec.ofNat 64
            (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)) +
          (((bs[ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat]'hoff
              ).zeroExtend 64 - (0xf7 : Word)) + signExtend12 (1 : BitVec 12))) +
        BitVec.ofNat 64 (Nat.fromBytesBE
          ((bs.drop (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat + 1)).take
            ((bs[ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat]'hoff
                ).zeroExtend 64 - (0xf7 : Word)).toNat))
      = (regionBase + BitVec.ofNat 64
            (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) :
    cpsTripleWithin
      ((1 + (7 * ((bs[ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat]'hoff
          ).zeroExtend 64 - (0xf7 : Word)).toNat + 25)) + (1 + (1 + 1)))
      WalkInitJalPc AfterSaveCursor extractLinkedCode
      (frontTypeLoadPostAmbient spC s regionBase loadPtr lenW toBuf isCreationPtr
        bs off len)
      (frontAfterSavePostLongAmbient spC s regionBase loadPtr lenW toBuf
        isCreationPtr bs off len hoff) := by
  set inner := (teerTxTypeDispatch (txSlice bs off len)).2.2
  set listOff := ambientAbsOff off inner.toNat
  set listLen := lenW - inner
  have hCall := extractWalkInitCall_long_fromFrontTypeLoad_owned_ambient
    spC s regionBase loadPtr lenW toBuf isCreationPtr bs off len
    hptr hsalign _hbound hoff hover hvalid hspan hlen h_ge h_ge_f8 hllen hlover hlvalid
    hoff1 h_fits h_llz h_min h_match
  have hSave := extractWalkInitBneSave_owned_ambient spC s
    loadPtr regionBase lenW toBuf isCreationPtr
    (longWalkCursorAmbient regionBase bs listOff hoff)
    (longWalkEndAmbient regionBase listLen listOff)
    bs off len
  have hCall' : cpsTripleWithin
      (1 + (7 * ((bs[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat + 25))
      WalkInitJalPc LinkWalkInit extractLinkedCode
      (frontTypeLoadPostAmbient spC s regionBase loadPtr lenW toBuf isCreationPtr
        bs off len)
      (walkFrameAmbient spC s toBuf isCreationPtr **
        walkInitAmbient loadPtr lenW
          (teerTxTypeDispatch (txSlice bs off len)).2.1 inner **
        extractWalkInitCommon regionBase bs **
        ((.x10 ↦ᵣ longWalkCursorAmbient regionBase bs listOff hoff) **
          (.x11 ↦ᵣ longWalkEndAmbient regionBase listLen listOff) **
          (.x12 ↦ᵣ (0 : Word))) **
        regOwn .x21 ** regOwn .x22) := by
    refine cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => by
      simp only [extractWalkInitLongOkRegs, longWalkCursorAmbient, longWalkEndAmbient,
        listOff, listLen, inner] at hq ⊢
      xperm_hyp hq) hCall
  have hseq := cpsTripleWithin_seq_same_cr hCall' hSave
  exact cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => by
    simp only [frontAfterSavePostLongAmbient, extractAfterSavePostAmbient,
      longWalkCursorAmbient, longWalkEndAmbient, listOff, listLen, inner] at hq ⊢
    xperm_hyp hq) hseq

set_option maxRecDepth 8000 in
/-- E → AfterSave long ambient concrete. -/
theorem extractFrontToAfterSave_long_concrete_ambient
    (sp0 spC : Word) (s : ExtractSaved)
    (regionBase loadPtr lenW toBuf isCreationPtr : Word)
    (old5 old6 old7 old14 old15 old16 : Word)
    (bs : List (BitVec 8)) (off len : Nat)
    (hspC : spC = sp0 + signExtend12 (-80 : BitVec 12))
    (hptr : loadPtr = regionBase + BitVec.ofNat 64 off)
    (htalign : toBuf.toNat % 8 = 0)
    (htover : toBuf.toNat + 16 < 2 ^ 64)
    (htvalid : isValidMemAccess (toBuf + (16 : Word)) = true)
    (hlen : lenW = BitVec.ofNat 64 len)
    (hsuccess : (teerTxTypeDispatch (txSlice bs off len)).1 = (0 : Word))
    (halign : regionBase.toNat % 8 = 0)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hbound : off + len ≤ bs.length)
    (hvalid0 : isValidByteAccess (regionBase + BitVec.ofNat 64 off) = true)
    (hoff : ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat <
        bs.length)
    (hinover : regionBase.toNat +
        ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat < 2 ^ 64)
    (hinvalid : isValidByteAccess
      (regionBase + BitVec.ofNat 64
        (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)) = true)
    (hspan : regionBase.toNat +
        (off + (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat) < 2 ^ 64)
    (hlistLen_ne : (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2) ≠ (0 : Word))
    (h_ge : ¬ BitVec.ult
        ((bs[ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat]'hoff
          ).zeroExtend 64)
        (0xc0 : Word) = true)
    (h_ge_f8 : ¬ BitVec.ult
        ((bs[ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat]'hoff
          ).zeroExtend 64)
        (0xf8 : Word) = true)
    (hllen : ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat + 1 +
      ((bs[ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat]'hoff
          ).zeroExtend 64 - (0xf7 : Word)).toNat ≤ bs.length)
    (hlover : regionBase.toNat +
        (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat + 1 +
          ((bs[ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat]'hoff
              ).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64)
    (hlvalid : ∀ k, k <
        ((bs[ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat]'hoff
            ).zeroExtend 64 - (0xf7 : Word)).toNat →
      isValidByteAccess (regionBase + BitVec.ofNat 64
        (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat + 1 + k)) = true)
    (hoff1 : ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat + 1 <
      bs.length)
    (h_fits : ¬ BitVec.ult
        ((regionBase + BitVec.ofNat 64
            (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2))
        ((regionBase + BitVec.ofNat 64
            (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)) +
          (((bs[ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat]'hoff
              ).zeroExtend 64 - (0xf7 : Word)) + signExtend12 (1 : BitVec 12))) = true)
    (h_llz : (bs[ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat + 1]'hoff1
        ).zeroExtend 64 ≠ (0 : Word))
    (h_min : ¬ BitVec.ult (BitVec.ofNat 64 (Nat.fromBytesBE
        ((bs.drop (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat + 1)).take
          ((bs[ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat]'hoff
              ).zeroExtend 64 - (0xf7 : Word)).toNat))) (56 : Word) = true)
    (h_match : ((regionBase + BitVec.ofNat 64
            (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)) +
          (((bs[ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat]'hoff
              ).zeroExtend 64 - (0xf7 : Word)) + signExtend12 (1 : BitVec 12))) +
        BitVec.ofNat 64 (Nat.fromBytesBE
          ((bs.drop (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat + 1)).take
            ((bs[ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat]'hoff
                ).zeroExtend 64 - (0xf7 : Word)).toNat))
      = (regionBase + BitVec.ofNat 64
            (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) :
    cpsTripleWithin
      (((14 + 4) + ((6 + (1 + nTypeSteps) + 1) + 8)) +
        ((1 + (7 * ((bs[ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat]'hoff
            ).zeroExtend 64 - (0xf7 : Word)).toNat + 25)) + (1 + (1 + 1))))
      E AfterSaveCursor extractLinkedCode
      ((.x2 ↦ᵣ sp0) ** regsAt extractFrame (extractSavedVals s) **
        frameSlotsOwn extractFrame spC ** extractSpareSlot spC **
        prologueAbiRest loadPtr lenW toBuf isCreationPtr
          old5 old6 old7 old14 old15 old16 **
        extractToBufOwn toBuf ** memOwn isCreationPtr **
        frontExtraAmbientAmb regionBase bs)
      (frontAfterSavePostLongAmbient spC s regionBase loadPtr lenW toBuf isCreationPtr
        bs off len hoff) := by
  have hF := extractFrontThenTypeLoadAmbient sp0 spC s regionBase loadPtr lenW
    toBuf isCreationPtr old5 old6 old7 old14 old15 old16 bs off len
    hspC hptr htalign htover htvalid hlen hsuccess halign hover hbound hvalid0
  have hW := extractWalkInitCall_long_toAfterSave_concrete_ambient spC s
    regionBase loadPtr lenW toBuf isCreationPtr bs off len
    hptr halign hbound hoff hinover hinvalid hspan hlistLen_ne h_ge h_ge_f8 hllen hlover
    hlvalid hoff1 h_fits h_llz h_min h_match
  exact cpsTripleWithin_seq_same_cr hF hW

/-- Concrete long AfterSave ambient → MidJoin pre (split bases). -/
theorem frontAfterSavePostLongAmbient_to_midJoinPre
    (spC : Word) (s : ExtractSaved)
    (regionBase loadPtr lenW toBuf isCreationPtr : Word)
    (bs : List (BitVec 8)) (off len : Nat)
    (hoff : ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat <
      bs.length) :
    ∀ h, frontAfterSavePostLongAmbient spC s regionBase loadPtr lenW toBuf
        isCreationPtr bs off len hoff h →
      (afterSaveFrameTyAmbient loadPtr regionBase lenW
          (teerTxTypeDispatch (txSlice bs off len)).2.1
          (teerTxTypeDispatch (txSlice bs off len)).2.2
          (longWalkCursorAmbient regionBase bs
            (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat) hoff)
          (longWalkEndAmbient regionBase
            (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)
            (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat))
          bs **
        (.x20 ↦ᵣ (teerTxTypeDispatch (txSlice bs off len)).2.1) **
        regOwn .x5 ** (.x0 ↦ᵣ (0 : Word)) **
        midOwned spC s toBuf isCreationPtr s.s7) h := by
  intro h hp
  simp only [frontAfterSavePostLongAmbient] at hp
  obtain ⟨h1, h2, hd, hu, hW, hAS⟩ := hp
  have hM := walkFrame_to_midOwned spC s toBuf isCreationPtr h1 hW
  have hC := afterSave_to_midJoinCore_ambient loadPtr regionBase lenW
    (teerTxTypeDispatch (txSlice bs off len)).2.1
    (teerTxTypeDispatch (txSlice bs off len)).2.2
    (longWalkCursorAmbient regionBase bs
      (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat) hoff)
    (longWalkEndAmbient regionBase
      (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)
      (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat))
    bs h2 hAS
  have hnest :
      ((afterSaveFrameTyAmbient loadPtr regionBase lenW
          (teerTxTypeDispatch (txSlice bs off len)).2.1
          (teerTxTypeDispatch (txSlice bs off len)).2.2
          (longWalkCursorAmbient regionBase bs
            (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat) hoff)
          (longWalkEndAmbient regionBase
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

#print axioms extractWalkInitCall_long_fromFrontTypeLoad_owned_ambient
#print axioms extractWalkInitCall_long_toAfterSave_concrete_ambient
#print axioms extractFrontToAfterSave_long_concrete_ambient
#print axioms frontAfterSavePostLongAmbient_to_midJoinPre

end EvmAsm.Codegen.TxExtractToAddressSpec
