/-
  Ambient dual: front + typeThenLoad under regionBase/loadPtr.
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.SAsm.AbiFrame
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Codegen.Programs.TxExtractToAddressTopFront
import EvmAsm.Codegen.Programs.TxExtractToAddressTopFrontMid
import EvmAsm.Codegen.Programs.TxExtractToAddressTypeThenLoadAmbient
import EvmAsm.Codegen.Programs.TxExtractToAddressTopFrontWalkInitAmbient
import EvmAsm.Codegen.Programs.TxTypeDispatchAmbient
import EvmAsm.Codegen.Programs.TxIntrinsicStateGasSpec
import EvmAsm.Codegen.Programs.TxTypeDispatchSpec

namespace EvmAsm.Codegen.TxExtractToAddressSpec

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
open EvmAsm.Codegen.TxIntrinsicStateGasSpec
  (nTypeSteps extractToBufOwn teaScratchOwn)
open EvmAsm.Codegen.TxTypeDispatchSpec (txSlice teerTxTypeDispatch ambientAbsOff)

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

def frontExtraAmbientAmb (regionBase : Word) (bs : List (BitVec 8)) : Assertion :=
  bytesRegion regionBase bs ** teaScratchOwn

private theorem frontExtraAmbientAmb_pcFree (regionBase : Word) (bs : List (BitVec 8)) :
    (frontExtraAmbientAmb regionBase bs).pcFree := by
  unfold frontExtraAmbientAmb; pcf

private theorem preZero_to_owns_amb (toBuf isCreationPtr : Word) :
    ∀ h, preZeroPost toBuf isCreationPtr h →
      (extractToBufOwn toBuf ** memOwn isCreationPtr) h := by
  intro h hp
  simp only [preZeroPost, extractToBufOwn] at hp ⊢
  have hq :
      ((toBuf ↦ₘ (0 : Word)) **
        (((toBuf + 8) ↦ₘ (0 : Word)) **
          (memOwn (toBuf + 16) ** (isCreationPtr ↦ₘ (0 : Word))))) h := by
    xperm_hyp hp
  have hq2 :
      (memOwn toBuf ** memOwn (toBuf + 8) ** memOwn (toBuf + 16) **
        memOwn isCreationPtr) h :=
    (sepConj_mono (memIs_implies_memOwn (v := (0 : Word)))
      (sepConj_mono (memIs_implies_memOwn (v := (0 : Word)))
        (sepConj_mono (fun _ x => x)
          (memIs_implies_memOwn (v := (0 : Word)))))) h hq
  xperm_hyp hq2

private theorem regIs_imp_regOwn_amb (r : Reg) (v : Word) :
    ∀ h, (r ↦ᵣ v) h → regOwn r h := fun _ hx => ⟨v, hx⟩

set_option maxRecDepth 8000 in
/-- Front frames ambient blob (regionBase/bs). ABI uses loadPtr as a0/s0. -/
theorem extractFront_extra_ambient
    (sp0 spC : Word) (s : ExtractSaved)
    (regionBase loadPtr lenW toBuf isCreationPtr : Word)
    (old5 old6 old7 old14 old15 old16 : Word)
    (bs : List (BitVec 8))
    (hspC : spC = sp0 + signExtend12 (-80 : BitVec 12))
    (halign : toBuf.toNat % 8 = 0)
    (hover : toBuf.toNat + 16 < 2 ^ 64)
    (hvalid16 : isValidMemAccess (toBuf + (16 : Word)) = true) :
    cpsTripleWithin (14 + 4) E AfterPreZero extractLinkedCode
      ((.x2 ↦ᵣ sp0) ** regsAt extractFrame (extractSavedVals s) **
        frameSlotsOwn extractFrame spC ** extractSpareSlot spC **
        prologueAbiRest loadPtr lenW toBuf isCreationPtr
          old5 old6 old7 old14 old15 old16 **
        extractToBufOwn toBuf ** memOwn isCreationPtr **
        frontExtraAmbientAmb regionBase bs)
      (prologuePost spC s loadPtr lenW toBuf isCreationPtr
        old5 old6 old7 old14 old15 old16 **
        preZeroPost toBuf isCreationPtr **
        frontExtraAmbientAmb regionBase bs) := by
  have h0 := extractFront sp0 spC s loadPtr lenW toBuf isCreationPtr
    old5 old6 old7 old14 old15 old16 hspC halign hover hvalid16
  have hF := cpsTripleWithin_frameR
    (frontExtraAmbientAmb regionBase bs)
    (frontExtraAmbientAmb_pcFree regionBase bs) h0
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hF

set_option maxRecDepth 8000 in
/-- typeThenLoad ambient under typeMidAmbient after front post reshape. -/
theorem extractTypeThenLoad_mid_ambient
    (spC : Word) (s : ExtractSaved)
    (regionBase loadPtr lenW toBuf isCreationPtr : Word)
    (old5 old6 old7 old14 old15 old16 : Word)
    (bs : List (BitVec 8)) (off len : Nat)
    (hptr : loadPtr = regionBase + BitVec.ofNat 64 off)
    (hlen : lenW = BitVec.ofNat 64 len)
    (hsuccess : (teerTxTypeDispatch (txSlice bs off len)).1 = (0 : Word))
    (halign : regionBase.toNat % 8 = 0)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hbound : off + len ≤ bs.length)
    (hvalid0 : isValidByteAccess (regionBase + BitVec.ofNat 64 off) = true) :
    cpsTripleWithin ((6 + (1 + nTypeSteps) + 1) + 8)
      AfterPreZero WalkInitJalPc extractLinkedCode
      (prologuePost spC s loadPtr lenW toBuf isCreationPtr
        old5 old6 old7 old14 old15 old16 **
        preZeroPost toBuf isCreationPtr **
        frontExtraAmbientAmb regionBase bs)
      (frontTypeLoadPostAmbient spC s regionBase loadPtr lenW toBuf isCreationPtr
        bs off len) := by
  have ht := extractTypeThenLoadAmbient regionBase loadPtr lenW bs off len
    s.ra loadPtr lenW toBuf isCreationPtr s.s4
    hptr hlen hsuccess halign hover hbound hvalid0
  have htF := cpsTripleWithin_frameR
    (typeMidAmbient spC s toBuf isCreationPtr)
    (by unfold typeMidAmbient extractToBufOwn; pcf) ht
  refine cpsTripleWithin_weaken (fun h hp => ?_) (fun _ hq => by
      simp only [frontTypeLoadPostAmbient] at hq ⊢
      xperm_hyp hq) htF
  have hp1 :
      (prologuePost spC s loadPtr lenW toBuf isCreationPtr
        old5 old6 old7 old14 old15 old16 **
        (extractToBufOwn toBuf ** memOwn isCreationPtr) **
        frontExtraAmbientAmb regionBase bs) h := by
    obtain ⟨hA, hB, hd, hu, hPro, hRest⟩ := hp
    obtain ⟨hB1, hB2, hd2, hu2, hPZ, hEx⟩ := hRest
    exact ⟨hA, hB, hd, hu, hPro, hB1, hB2, hd2, hu2,
      preZero_to_owns_amb toBuf isCreationPtr hB1 hPZ, hEx⟩
  have hnest :
      (((.x1 ↦ᵣ s.ra) ** (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
          (.x10 ↦ᵣ loadPtr) ** (.x11 ↦ᵣ lenW) **
          (.x12 ↦ᵣ toBuf) ** (.x13 ↦ᵣ isCreationPtr) **
          (.x20 ↦ᵣ s.s4) **
          bytesRegion regionBase bs ** teaScratchOwn **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          (.x0 ↦ᵣ (0 : Word)) **
          typeMidAmbient spC s toBuf isCreationPtr) **
        (.x5 ↦ᵣ old5) ** (.x6 ↦ᵣ old6) ** (.x7 ↦ᵣ old7) **
        (.x14 ↦ᵣ old14) ** (.x15 ↦ᵣ old15) ** (.x16 ↦ᵣ old16)) h := by
    simp only [prologuePost, prologueAbiRest, frontExtraAmbientAmb, teaScratchOwn,
      typeMidAmbient, extractToBufOwn] at hp1 ⊢
    xperm_hyp hp1
  have mtemps :=
    sepConj_mono (fun _ x => x)
      (sepConj_mono (regIs_imp_regOwn_amb .x5 old5)
        (sepConj_mono (regIs_imp_regOwn_amb .x6 old6)
          (sepConj_mono (regIs_imp_regOwn_amb .x7 old7)
            (sepConj_mono (regIs_imp_regOwn_amb .x14 old14)
              (sepConj_mono (regIs_imp_regOwn_amb .x15 old15)
                (regIs_imp_regOwn_amb .x16 old16)))))) h hnest
  simp only [typeMidAmbient, extractToBufOwn, teaScratchOwn] at mtemps ⊢
  xperm_hyp mtemps

set_option maxRecDepth 8000 in
/-- E → WalkInitJalPc ambient. -/
theorem extractFrontThenTypeLoadAmbient
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
    (hvalid0 : isValidByteAccess (regionBase + BitVec.ofNat 64 off) = true) :
    cpsTripleWithin
      ((14 + 4) + ((6 + (1 + nTypeSteps) + 1) + 8))
      E WalkInitJalPc extractLinkedCode
      ((.x2 ↦ᵣ sp0) ** regsAt extractFrame (extractSavedVals s) **
        frameSlotsOwn extractFrame spC ** extractSpareSlot spC **
        prologueAbiRest loadPtr lenW toBuf isCreationPtr
          old5 old6 old7 old14 old15 old16 **
        extractToBufOwn toBuf ** memOwn isCreationPtr **
        frontExtraAmbientAmb regionBase bs)
      (frontTypeLoadPostAmbient spC s regionBase loadPtr lenW toBuf isCreationPtr
        bs off len) := by
  have hF := extractFront_extra_ambient sp0 spC s regionBase loadPtr lenW
    toBuf isCreationPtr old5 old6 old7 old14 old15 old16 bs
    hspC htalign htover htvalid
  have hT := extractTypeThenLoad_mid_ambient spC s regionBase loadPtr lenW
    toBuf isCreationPtr old5 old6 old7 old14 old15 old16 bs off len
    hptr hlen hsuccess halign hover hbound hvalid0
  exact cpsTripleWithin_seq_same_cr hF hT

set_option maxRecDepth 8000 in
/-- E → AfterSave short ambient concrete. -/
theorem extractFrontToAfterSave_short_concrete_ambient
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
    cpsTripleWithin
      (((14 + 4) + ((6 + (1 + nTypeSteps) + 1) + 8)) +
        ((1 + 15) + (1 + (1 + 1))))
      E AfterSaveCursor extractLinkedCode
      ((.x2 ↦ᵣ sp0) ** regsAt extractFrame (extractSavedVals s) **
        frameSlotsOwn extractFrame spC ** extractSpareSlot spC **
        prologueAbiRest loadPtr lenW toBuf isCreationPtr
          old5 old6 old7 old14 old15 old16 **
        extractToBufOwn toBuf ** memOwn isCreationPtr **
        frontExtraAmbientAmb regionBase bs)
      (frontAfterSavePostShortAmbient spC s regionBase loadPtr lenW toBuf isCreationPtr
        bs off len) := by
  have hF := extractFrontThenTypeLoadAmbient sp0 spC s regionBase loadPtr lenW
    toBuf isCreationPtr old5 old6 old7 old14 old15 old16 bs off len
    hspC hptr htalign htover htvalid hlen hsuccess halign hover hbound hvalid0
  have hW := extractWalkInitCall_short_toAfterSave_concrete_ambient spC s
    regionBase loadPtr lenW toBuf isCreationPtr bs off len
    hptr halign hbound hoff hinover hinvalid hspan hlistLen_ne h_ge h_hi h_exact
  exact cpsTripleWithin_seq_same_cr hF hW

#print axioms extractFront_extra_ambient
#print axioms extractTypeThenLoad_mid_ambient
#print axioms extractFrontThenTypeLoadAmbient
#print axioms extractFrontToAfterSave_short_concrete_ambient

end EvmAsm.Codegen.TxExtractToAddressSpec
