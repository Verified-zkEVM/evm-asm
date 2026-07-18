/-
  Front + typeThenLoad under mid ambient: E → WalkInitJalPc.
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.SAsm.AbiFrame
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Codegen.Programs.TxExtractToAddressTopFront
import EvmAsm.Codegen.Programs.TxExtractToAddressTopTypeLoad
import EvmAsm.Codegen.Programs.TxExtractToAddressTopMidOwned
import EvmAsm.Codegen.Programs.TxIntrinsicStateGasSpec
import EvmAsm.Codegen.Programs.TxTypeDispatchSpec

namespace EvmAsm.Codegen.TxExtractToAddressSpec

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
open EvmAsm.Codegen.TxIntrinsicStateGasSpec
  (extractToBufOwn teaScratchOwn nExtractStackDwords nTypeSteps)
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
      | exact pcFree_teaScratchOwn
      | exact midOwned_pcFree _ _ _ _ _)

/-- RO blob + tea cells framed across front. -/
def frontExtraAmbient (txBase : Word) (txBytes : List (BitVec 8)) : Assertion :=
  bytesRegion txBase txBytes ** teaScratchOwn

private theorem frontExtraAmbient_pcFree (txBase : Word)
    (txBytes : List (BitVec 8)) :
    (frontExtraAmbient txBase txBytes).pcFree := by
  unfold frontExtraAmbient; pcf

/-- preZero concrete zeros → extractToBufOwn + memOwn isCreation. -/
private theorem preZero_to_owns (toBuf isCreationPtr : Word) :
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

private theorem regIs_imp_regOwn (r : Reg) (v : Word) :
    ∀ h, (r ↦ᵣ v) h → regOwn r h :=
  fun _ hx => ⟨v, hx⟩

set_option maxRecDepth 8000 in
/-- extractFront + bytes/tea ambient. -/
theorem extractFront_extra
    (sp0 spC : Word) (s : ExtractSaved)
    (txBase txLenW toBuf isCreationPtr : Word)
    (old5 old6 old7 old14 old15 old16 : Word)
    (txBytes : List (BitVec 8))
    (hspC : spC = sp0 + signExtend12 (-80 : BitVec 12))
    (halign : toBuf.toNat % 8 = 0)
    (hover : toBuf.toNat + 16 < 2 ^ 64)
    (hvalid16 : isValidMemAccess (toBuf + (16 : Word)) = true) :
    cpsTripleWithin (14 + 4) E AfterPreZero extractLinkedCode
      ((.x2 ↦ᵣ sp0) ** regsAt extractFrame (extractSavedVals s) **
        frameSlotsOwn extractFrame spC ** extractSpareSlot spC **
        prologueAbiRest txBase txLenW toBuf isCreationPtr
          old5 old6 old7 old14 old15 old16 **
        extractToBufOwn toBuf ** memOwn isCreationPtr **
        frontExtraAmbient txBase txBytes)
      (prologuePost spC s txBase txLenW toBuf isCreationPtr
        old5 old6 old7 old14 old15 old16 **
        preZeroPost toBuf isCreationPtr **
        frontExtraAmbient txBase txBytes) := by
  have h0 := extractFront sp0 spC s txBase txLenW toBuf isCreationPtr
    old5 old6 old7 old14 old15 old16 hspC halign hover hvalid16
  have hF := cpsTripleWithin_frameR
    (frontExtraAmbient txBase txBytes)
    (frontExtraAmbient_pcFree txBase txBytes) h0
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hF

/-- Stack + s-regs + toBuf owns framed across typeThenLoad. -/
def typeMidAmbient (spC : Word) (s : ExtractSaved)
    (toBuf isCreationPtr : Word) : Assertion :=
  (.x2 ↦ᵣ spC) **
    frameSlotsSaved extractFrame spC (extractSavedVals s) **
    extractSpareSlot spC **
    (.x18 ↦ᵣ toBuf) ** (.x19 ↦ᵣ isCreationPtr) **
    (Reg.x23 ↦ᵣ s.s7) **
    (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) **
    extractToBufOwn toBuf ** memOwn isCreationPtr

private theorem typeMidAmbient_pcFree (spC : Word) (s : ExtractSaved)
    (toBuf isCreationPtr : Word) :
    (typeMidAmbient spC s toBuf isCreationPtr).pcFree := by
  unfold typeMidAmbient extractToBufOwn; pcf

/-- Post at WalkInitJalPc: typeLoad result + typeMidAmbient. -/
def frontTypeLoadPost (spC : Word) (s : ExtractSaved)
    (txBase lenW toBuf isCreationPtr : Word)
    (txBytes : List (BitVec 8)) : Assertion :=
  typeMidAmbient spC s toBuf isCreationPtr **
    (.x1 ↦ᵣ LinkType) ** (.x0 ↦ᵣ (0 : Word)) **
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
    regOwn .x28 ** regOwn .x29 ** regOwn .x31

set_option maxRecDepth 8000 in
/-- typeThenLoad under typeMidAmbient after front post reshape. -/
theorem extractTypeThenLoad_mid
    (spC : Word) (s : ExtractSaved)
    (txBase lenW toBuf isCreationPtr : Word)
    (old5 old6 old7 old14 old15 old16 : Word)
    (txBytes : List (BitVec 8))
    (hlen : lenW = BitVec.ofNat 64 txBytes.length)
    (hsuccess : (teerTxTypeDispatch txBytes).1 = (0 : Word))
    (halign : txBase.toNat % 8 = 0)
    (hover : txBase.toNat + txBytes.length < 2 ^ 64)
    (hvalid0 : isValidByteAccess (txBase + BitVec.ofNat 64 0) = true) :
    cpsTripleWithin ((6 + (1 + nTypeSteps) + 1) + 8)
      AfterPreZero WalkInitJalPc extractLinkedCode
      (prologuePost spC s txBase lenW toBuf isCreationPtr
        old5 old6 old7 old14 old15 old16 **
        preZeroPost toBuf isCreationPtr **
        frontExtraAmbient txBase txBytes)
      (frontTypeLoadPost spC s txBase lenW toBuf isCreationPtr txBytes) := by
  have ht := extractTypeThenLoad txBase lenW txBytes s.ra
    txBase lenW toBuf isCreationPtr s.s4
    hlen hsuccess halign hover hvalid0
  have htF := cpsTripleWithin_frameR
    (typeMidAmbient spC s toBuf isCreationPtr)
    (typeMidAmbient_pcFree spC s toBuf isCreationPtr) ht
  refine cpsTripleWithin_weaken (fun h hp => ?_) (fun _ hq => by
      simp only [frontTypeLoadPost] at hq ⊢
      xperm_hyp hq) htF
  -- Convert prologue ** preZero ** extra → typeThenLoadPre ** typeMidAmbient
  have hp1 :
      (prologuePost spC s txBase lenW toBuf isCreationPtr
        old5 old6 old7 old14 old15 old16 **
        (extractToBufOwn toBuf ** memOwn isCreationPtr) **
        frontExtraAmbient txBase txBytes) h := by
    obtain ⟨hA, hB, hd, hu, hPro, hRest⟩ := hp
    obtain ⟨hB1, hB2, hd2, hu2, hPZ, hEx⟩ := hRest
    exact ⟨hA, hB, hd, hu, hPro, hB1, hB2, hd2, hu2,
      preZero_to_owns toBuf isCreationPtr hB1 hPZ, hEx⟩
  -- Right-assoc: core ** x5 ** x6 ** x7 ** x14 ** x15 ** x16
  have hnest :
      (((.x1 ↦ᵣ s.ra) ** (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
          (.x10 ↦ᵣ txBase) ** (.x11 ↦ᵣ lenW) **
          (.x12 ↦ᵣ toBuf) ** (.x13 ↦ᵣ isCreationPtr) **
          (.x20 ↦ᵣ s.s4) **
          bytesRegion txBase txBytes ** teaScratchOwn **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          (.x0 ↦ᵣ (0 : Word)) **
          typeMidAmbient spC s toBuf isCreationPtr) **
        (.x5 ↦ᵣ old5) ** (.x6 ↦ᵣ old6) ** (.x7 ↦ᵣ old7) **
        (.x14 ↦ᵣ old14) ** (.x15 ↦ᵣ old15) ** (.x16 ↦ᵣ old16)) h := by
    simp only [prologuePost, prologueAbiRest, frontExtraAmbient, teaScratchOwn,
      typeMidAmbient, extractToBufOwn] at hp1 ⊢
    xperm_hyp hp1
  -- ** is right-assoc: A ** B ** C = A ** (B ** C)
  have mtemps :=
    sepConj_mono (fun _ x => x)
      (sepConj_mono (regIs_imp_regOwn .x5 old5)
        (sepConj_mono (regIs_imp_regOwn .x6 old6)
          (sepConj_mono (regIs_imp_regOwn .x7 old7)
            (sepConj_mono (regIs_imp_regOwn .x14 old14)
              (sepConj_mono (regIs_imp_regOwn .x15 old15)
                (regIs_imp_regOwn .x16 old16)))))) h hnest
  simp only [typeMidAmbient, extractToBufOwn, teaScratchOwn] at mtemps ⊢
  xperm_hyp mtemps

set_option maxRecDepth 8000 in
/-- E → WalkInitJalPc: front + typeThenLoad under ambient. -/
theorem extractFrontThenTypeLoad
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
    (hvalid0 : isValidByteAccess (txBase + BitVec.ofNat 64 0) = true) :
    cpsTripleWithin
      ((14 + 4) + ((6 + (1 + nTypeSteps) + 1) + 8))
      E WalkInitJalPc extractLinkedCode
      ((.x2 ↦ᵣ sp0) ** regsAt extractFrame (extractSavedVals s) **
        frameSlotsOwn extractFrame spC ** extractSpareSlot spC **
        prologueAbiRest txBase lenW toBuf isCreationPtr
          old5 old6 old7 old14 old15 old16 **
        extractToBufOwn toBuf ** memOwn isCreationPtr **
        frontExtraAmbient txBase txBytes)
      (frontTypeLoadPost spC s txBase lenW toBuf isCreationPtr txBytes) := by
  have hF := extractFront_extra sp0 spC s txBase lenW toBuf isCreationPtr
    old5 old6 old7 old14 old15 old16 txBytes hspC htalign htover htvalid
  have hT := extractTypeThenLoad_mid spC s txBase lenW toBuf isCreationPtr
    old5 old6 old7 old14 old15 old16 txBytes hlen hsuccess halign hover hvalid0
  exact cpsTripleWithin_seq_same_cr hF hT

#print axioms extractFront_extra
#print axioms extractTypeThenLoad_mid
#print axioms extractFrontThenTypeLoad

end EvmAsm.Codegen.TxExtractToAddressSpec
