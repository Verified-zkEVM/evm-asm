/-
  Frame stack + toBuf/isCreation through type234 end → HaveField creation → ret.
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.SAsm.AbiFrame
import EvmAsm.Rv64.SAsm.MeasureLoop
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Codegen.Programs.TxExtractToAddressTopWalkNextRest
import EvmAsm.Codegen.Programs.TxExtractToAddressTopJoin
import EvmAsm.Codegen.Programs.TxIntrinsicStateGasSpec

namespace EvmAsm.Codegen.TxExtractToAddressSpec

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Rv64.RLP
open EvmAsm.Codegen
open EvmAsm.Codegen.TxIntrinsicStateGasSpec
  (extractToBufOwn nExtractStackDwords)

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
      | exact bytesRegion_pcFree _ _)

/-- Owned across mid walks / HaveField (not in wn*Stable). -/
def midOwned (spC : Word) (s : ExtractSaved)
    (toBuf isCreationPtr s7 : Word) : Assertion :=
  joinStackAmbient spC s **
    (.x18 ↦ᵣ toBuf) ** (.x19 ↦ᵣ isCreationPtr) **
    extractToBufOwn toBuf ** memOwn isCreationPtr **
    (Reg.x23 ↦ᵣ s7)

theorem midOwned_pcFree (spC : Word) (s : ExtractSaved)
    (toBuf isCreationPtr s7 : Word) :
    (midOwned spC s toBuf isCreationPtr s7).pcFree := by
  unfold midOwned joinStackAmbient extractToBufOwn; pcf

/-- Temps framed across creation (not clobbered). -/
def creExtraTemps : Assertion :=
  regOwn .x6 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30

theorem creExtraTemps_pcFree : creExtraTemps.pcFree := by
  unfold creExtraTemps; pcf

set_option maxRecDepth 8000 in
/-- type234 SUB+JAL HaveField with stack/toBuf/isCreation framed. -/
theorem extractType234ToHaveField_owned
    (spC : Word) (s : ExtractSaved)
    (txBase lenW typeW innerW endPtr next len toBuf isCreationPtr s7 : Word)
    (txBytes : List (BitVec 8)) (srcOff5 : Nat) :
    cpsTripleWithin (1 + 1) AfterWalkNext5Bne HaveField extractLinkedCode
      (wn5OkConcrete txBase lenW typeW innerW endPtr next len txBytes srcOff5 **
        midOwned spC s toBuf isCreationPtr s7)
      (wn5Stable txBase lenW typeW innerW endPtr
          (txBase + BitVec.ofNat 64 srcOff5) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkWalkNext5) **
        bytesRegion txBase txBytes **
        (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
        (.x31 ↦ᵣ (next - len)) **
        midOwned spC s toBuf isCreationPtr s7) := by
  have h := extractType234ToHaveField_framed txBase lenW typeW innerW endPtr
    next len txBytes srcOff5
  have hF := cpsTripleWithin_frameR
    (midOwned spC s toBuf isCreationPtr s7) (midOwned_pcFree _ _ _ _ _) h
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hF

/-- Reshape ToHaveField post (len=0) → creation pre + extra temps.
    Shape: `Pcore ** regOwn x7 ** regOwn x5` (right-assoc for of_forall2). -/
private theorem toHaveField_owned_post_to_creationPre
    (spC : Word) (s : ExtractSaved)
    (txBase lenW typeW innerW endPtr next toBuf isCreationPtr s7 : Word)
    (txBytes : List (BitVec 8)) (srcOff5 : Nat) :
    ∀ h,
      (wn5Stable txBase lenW typeW innerW endPtr
          (txBase + BitVec.ofNat 64 srcOff5) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkWalkNext5) **
        bytesRegion txBase txBytes **
        (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (0 : Word)) **
        (.x31 ↦ᵣ (next - (0 : Word))) **
        midOwned spC s toBuf isCreationPtr s7) h →
      (haveFieldCreAmbient txBase lenW typeW innerW toBuf
          (txBase + BitVec.ofNat 64 srcOff5) endPtr next txBytes **
        joinStackAmbient spC s **
        (.x1 ↦ᵣ LinkWalkNext5) ** (Reg.x23 ↦ᵣ s7) **
        (.x12 ↦ᵣ (0 : Word)) **
        (.x19 ↦ᵣ isCreationPtr) ** (.x10 ↦ᵣ next) **
        (.x0 ↦ᵣ (0 : Word)) ** memOwn isCreationPtr **
        creExtraTemps ** regOwn .x7 ** regOwn .x5) h := by
  intro h hp
  simp only [wn5Stable, midOwned, joinStackAmbient, haveFieldCreAmbient,
    extractToBufOwn, creExtraTemps] at hp ⊢
  xperm_hyp hp

set_option maxRecDepth 8000 in
/-- type234 end (len=0) → creation → ret under midOwned. -/
theorem extractType234HaveFieldCreation_then_epi
    (sp0 spC : Word) (s : ExtractSaved)
    (txBase lenW typeW innerW endPtr next toBuf isCreationPtr s7 : Word)
    (txBytes : List (BitVec 8)) (srcOff5 : Nat)
    (hspC : spC = sp0 + signExtend12 (-80 : BitVec 12))
    (hret : s.ra &&& ~~~(1 : Word) = s.ra) :
    cpsTripleWithin
      ((1 + 1) + ((1 + (1 + (1 + (1 + (1 + 1))))) + 11))
      AfterWalkNext5Bne s.ra extractLinkedCode
      (wn5OkConcrete txBase lenW typeW innerW endPtr next (0 : Word)
          txBytes srcOff5 **
        midOwned spC s toBuf isCreationPtr s7)
      ((.x1 ↦ᵣ s.ra) ** (.x2 ↦ᵣ sp0) **
        stackFree sp0 nExtractStackDwords **
        (.x10 ↦ᵣ (0 : Word)) **
        bytesRegion txBase txBytes **
        extractToBufOwn toBuf **
        (isCreationPtr ↦ₘ (1 : Word)) **
        (TeaTypeAddr ↦ₘ typeW) ** (TeaInnerAddr ↦ₘ innerW) **
        (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
        (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) **
        (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) **
        (Reg.x23 ↦ᵣ s.s7) **
        (.x5 ↦ᵣ (1 : Word)) ** (.x7 ↦ᵣ (0 : Word)) **
        (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (0 : Word)) **
        (.x0 ↦ᵣ (0 : Word)) **
        regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
        (.x31 ↦ᵣ (next - (0 : Word))) **
        creExtraTemps) := by
  let cursor := txBase + BitVec.ofNat 64 srcOff5
  have hTo := extractType234ToHaveField_owned spC s txBase lenW typeW innerW
    endPtr next (0 : Word) toBuf isCreationPtr s7 txBytes srcOff5
  have hTo2 :
      cpsTripleWithin (1 + 1) AfterWalkNext5Bne HaveField extractLinkedCode
        (wn5OkConcrete txBase lenW typeW innerW endPtr next (0 : Word)
            txBytes srcOff5 **
          midOwned spC s toBuf isCreationPtr s7)
        (haveFieldCreAmbient txBase lenW typeW innerW toBuf cursor endPtr next
            txBytes **
          joinStackAmbient spC s **
          (.x1 ↦ᵣ LinkWalkNext5) ** (Reg.x23 ↦ᵣ s7) **
          (.x12 ↦ᵣ (0 : Word)) **
          (.x19 ↦ᵣ isCreationPtr) ** (.x10 ↦ᵣ next) **
          (.x0 ↦ᵣ (0 : Word)) ** memOwn isCreationPtr **
          creExtraTemps ** regOwn .x7 ** regOwn .x5) := by
    refine cpsTripleWithin_weaken (fun _ hp => hp)
      (fun h hq => by
        have hq1 :
            (wn5Stable txBase lenW typeW innerW endPtr cursor **
              regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
              regOwn .x29 ** regOwn .x30 **
              (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkWalkNext5) **
              bytesRegion txBase txBytes **
              (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (0 : Word)) **
              (.x31 ↦ᵣ (next - (0 : Word))) **
              midOwned spC s toBuf isCreationPtr s7) h := by
          simpa [cursor] using hq
        exact toHaveField_owned_post_to_creationPre spC s txBase lenW typeW
          innerW endPtr next toBuf isCreationPtr s7 txBytes srcOff5 _ hq1) hTo
  have hCre :
      cpsTripleWithin ((1 + (1 + (1 + (1 + (1 + 1))))) + 11)
        HaveField s.ra extractLinkedCode
        (haveFieldCreAmbient txBase lenW typeW innerW toBuf cursor endPtr next
            txBytes **
          joinStackAmbient spC s **
          (.x1 ↦ᵣ LinkWalkNext5) ** (Reg.x23 ↦ᵣ s7) **
          (.x12 ↦ᵣ (0 : Word)) **
          (.x19 ↦ᵣ isCreationPtr) ** (.x10 ↦ᵣ next) **
          (.x0 ↦ᵣ (0 : Word)) ** memOwn isCreationPtr **
          creExtraTemps ** regOwn .x7 ** regOwn .x5)
        ((.x1 ↦ᵣ s.ra) ** (.x2 ↦ᵣ sp0) **
          stackFree sp0 nExtractStackDwords **
          (.x10 ↦ᵣ (0 : Word)) **
          bytesRegion txBase txBytes **
          extractToBufOwn toBuf **
          (isCreationPtr ↦ₘ (1 : Word)) **
          (TeaTypeAddr ↦ₘ typeW) ** (TeaInnerAddr ↦ₘ innerW) **
          (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
          (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) **
          (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) **
          (Reg.x23 ↦ᵣ s.s7) **
          (.x5 ↦ᵣ (1 : Word)) ** (.x7 ↦ᵣ (0 : Word)) **
          (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (0 : Word)) **
          (.x0 ↦ᵣ (0 : Word)) **
          regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
          (.x31 ↦ᵣ (next - (0 : Word))) **
          creExtraTemps) := by
    let Pcore : Assertion :=
      haveFieldCreAmbient txBase lenW typeW innerW toBuf cursor endPtr next
          txBytes **
        joinStackAmbient spC s **
        (.x1 ↦ᵣ LinkWalkNext5) ** (Reg.x23 ↦ᵣ s7) **
        (.x12 ↦ᵣ (0 : Word)) **
        (.x19 ↦ᵣ isCreationPtr) ** (.x10 ↦ᵣ next) **
        (.x0 ↦ᵣ (0 : Word)) ** memOwn isCreationPtr **
        creExtraTemps
    -- of_forall2 shape first (TopT1 pattern), then reassoc to flat.
    have htemps :
        cpsTripleWithin ((1 + (1 + (1 + (1 + (1 + 1))))) + 11)
          HaveField s.ra extractLinkedCode
          (Pcore ** regOwn .x7 ** regOwn .x5)
          ((.x1 ↦ᵣ s.ra) ** (.x2 ↦ᵣ sp0) **
            stackFree sp0 nExtractStackDwords **
            (.x10 ↦ᵣ (0 : Word)) **
            bytesRegion txBase txBytes **
            extractToBufOwn toBuf **
            (isCreationPtr ↦ₘ (1 : Word)) **
            (TeaTypeAddr ↦ₘ typeW) ** (TeaInnerAddr ↦ₘ innerW) **
            (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
            (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) **
            (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) **
            (Reg.x23 ↦ᵣ s.s7) **
            (.x5 ↦ᵣ (1 : Word)) ** (.x7 ↦ᵣ (0 : Word)) **
            (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (0 : Word)) **
            (.x0 ↦ᵣ (0 : Word)) **
            regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
            (.x31 ↦ᵣ (next - (0 : Word))) **
            creExtraTemps) := by
      refine cpsTripleWithin_of_forall_regIs_to_regOwn2 (r1 := .x7) (r2 := .x5)
        (P := Pcore) (fun t2Old t0Old => ?_)
      have h := extractHaveFieldCreation_then_epi sp0 spC s txBase lenW typeW
        innerW toBuf cursor endPtr next isCreationPtr t2Old t0Old next
        LinkWalkNext5 s7 txBytes hspC hret
      have hF := cpsTripleWithin_frameR creExtraTemps creExtraTemps_pcFree h
      exact cpsTripleWithin_weaken (fun _ hp => by
        dsimp only [Pcore, creExtraTemps] at hp ⊢
        xperm_hyp hp) (fun _ hq => by
        dsimp only [creExtraTemps] at hq ⊢
        xperm_hyp hq) hF
    exact cpsTripleWithin_weaken (fun _ hp => by
      dsimp only [Pcore, creExtraTemps] at hp ⊢
      xperm_hyp hp) (fun _ hq => hq) htemps
  exact cpsTripleWithin_seq_same_cr hTo2 hCre

set_option maxRecDepth 8000 in
/-- type234 end (len=20) → copy → ret under midOwned + content dwords.
    Content field dwords are ambient (leaf models them as memIs).
    `old16` is peeled from extractToBufOwn's third memOwn. -/
theorem extractType234HaveFieldCopy_then_epi
    (sp0 spC : Word) (s : ExtractSaved)
    (txBase lenW typeW innerW endPtr next toBuf isCreationPtr s7 : Word)
    (txBytes : List (BitVec 8)) (srcOff5 : Nat)
    (w0 w1 w2 : Word)
    (hspC : spC = sp0 + signExtend12 (-80 : BitVec 12))
    (hret : s.ra &&& ~~~(1 : Word) = s.ra)
    (hcalign : (next - (20 : Word)).toNat % 8 = 0)
    (hcover : (next - (20 : Word)).toNat + 16 < 2 ^ 64)
    (hcvalid : isValidMemAccess ((next - (20 : Word)) + (16 : Word)) = true)
    (htalign : toBuf.toNat % 8 = 0)
    (htover : toBuf.toNat + 16 < 2 ^ 64)
    (htvalid : isValidMemAccess (toBuf + (16 : Word)) = true) :
    cpsTripleWithin
      ((1 + 1) +
        ((1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + 1)))))))))))) + 11))
      AfterWalkNext5Bne s.ra extractLinkedCode
      (wn5OkConcrete txBase lenW typeW innerW endPtr next (20 : Word)
          txBytes srcOff5 **
        midOwned spC s toBuf isCreationPtr s7 **
        ((next - (20 : Word)) ↦ₘ w0) **
        ((next - (20 : Word) + 8) ↦ₘ w1) **
        ((next - (20 : Word) + 16) ↦ₘ w2))
      ((.x1 ↦ᵣ s.ra) ** (.x2 ↦ᵣ sp0) **
        stackFree sp0 nExtractStackDwords **
        (.x10 ↦ᵣ (0 : Word)) **
        bytesRegion txBase txBytes **
        extractToBufOwn toBuf **
        (isCreationPtr ↦ₘ (0 : Word)) **
        (TeaTypeAddr ↦ₘ typeW) ** (TeaInnerAddr ↦ₘ innerW) **
        ((next - (20 : Word)) ↦ₘ w0) **
        ((next - (20 : Word) + 8) ↦ₘ w1) **
        ((next - (20 : Word) + 16) ↦ₘ w2) **
        (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
        (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) **
        (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) **
        (Reg.x23 ↦ᵣ s.s7) **
        (.x5 ↦ᵣ (extractWord32 w2
            (byteOffset ((next - (20 : Word)) + 16) / 4)).zeroExtend 64) **
        (.x6 ↦ᵣ (20 : Word)) ** (.x7 ↦ᵣ (20 : Word)) **
        (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (20 : Word)) **
        (.x31 ↦ᵣ (next - (20 : Word))) **
        (.x0 ↦ᵣ (0 : Word)) **
        regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30) := by
  let cursor := txBase + BitVec.ofNat 64 srcOff5
  let contentPtr := next - (20 : Word)
  have hTo := extractType234ToHaveField_owned spC s txBase lenW typeW innerW
    endPtr next (20 : Word) toBuf isCreationPtr s7 txBytes srcOff5
  have hToF := cpsTripleWithin_frameR
    ((contentPtr ↦ₘ w0) ** ((contentPtr + 8) ↦ₘ w1) ** ((contentPtr + 16) ↦ₘ w2))
    (by
      apply pcFree_sepConj
      · exact pcFree_memIs
      · apply pcFree_sepConj
        · exact pcFree_memIs
        · exact pcFree_memIs) hTo
  -- Peel toBuf+16 from extractToBufOwn via of_forall after reshape;
  -- peel temps x7/x6/x5; a0 stays next (concrete from walk).
  have hCopy :
      cpsTripleWithin
        ((1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + 1)))))))))))) + 11)
        HaveField s.ra extractLinkedCode
        (wn5Stable txBase lenW typeW innerW endPtr cursor **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkWalkNext5) **
          bytesRegion txBase txBytes **
          (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (20 : Word)) **
          (.x31 ↦ᵣ contentPtr) **
          midOwned spC s toBuf isCreationPtr s7 **
          (contentPtr ↦ₘ w0) ** ((contentPtr + 8) ↦ₘ w1) ** ((contentPtr + 16) ↦ₘ w2))
        ((.x1 ↦ᵣ s.ra) ** (.x2 ↦ᵣ sp0) **
          stackFree sp0 nExtractStackDwords **
          (.x10 ↦ᵣ (0 : Word)) **
          bytesRegion txBase txBytes **
          extractToBufOwn toBuf **
          (isCreationPtr ↦ₘ (0 : Word)) **
          (TeaTypeAddr ↦ₘ typeW) ** (TeaInnerAddr ↦ₘ innerW) **
          (contentPtr ↦ₘ w0) ** ((contentPtr + 8) ↦ₘ w1) ** ((contentPtr + 16) ↦ₘ w2) **
          (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
          (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) **
          (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) **
          (Reg.x23 ↦ᵣ s.s7) **
          (.x5 ↦ᵣ (extractWord32 w2 (byteOffset (contentPtr + 16) / 4)).zeroExtend 64) **
          (.x6 ↦ᵣ (20 : Word)) ** (.x7 ↦ᵣ (20 : Word)) **
          (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (20 : Word)) **
          (.x31 ↦ᵣ contentPtr) **
          (.x0 ↦ᵣ (0 : Word)) **
          regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30) := by
    let Pcore : Assertion :=
      haveFieldCopyAmbient txBase lenW typeW innerW endPtr cursor txBytes **
        joinStackAmbient spC s **
        (.x1 ↦ᵣ LinkWalkNext5) ** (Reg.x23 ↦ᵣ s7) **
        (.x12 ↦ᵣ (20 : Word)) **
        (.x31 ↦ᵣ contentPtr) **
        (.x18 ↦ᵣ toBuf) ** (.x19 ↦ᵣ isCreationPtr) **
        (.x10 ↦ᵣ next) ** (.x0 ↦ᵣ (0 : Word)) **
        (contentPtr ↦ₘ w0) ** ((contentPtr + 8) ↦ₘ w1) ** ((contentPtr + 16) ↦ₘ w2) **
        memOwn toBuf ** memOwn (toBuf + 8) ** memOwn isCreationPtr **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30
    -- Peel old16 from memOwn (toBuf+16), then temps x7/x6/x5 (a0=next concrete).
    have htemps :
        cpsTripleWithin
          ((1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + 1)))))))))))) + 11)
          HaveField s.ra extractLinkedCode
          (Pcore ** memOwn (toBuf + 16) ** regOwn .x7 ** regOwn .x6 ** regOwn .x5)
          ((.x1 ↦ᵣ s.ra) ** (.x2 ↦ᵣ sp0) **
            stackFree sp0 nExtractStackDwords **
            (.x10 ↦ᵣ (0 : Word)) **
            bytesRegion txBase txBytes **
            extractToBufOwn toBuf **
            (isCreationPtr ↦ₘ (0 : Word)) **
            (TeaTypeAddr ↦ₘ typeW) ** (TeaInnerAddr ↦ₘ innerW) **
            (contentPtr ↦ₘ w0) ** ((contentPtr + 8) ↦ₘ w1) ** ((contentPtr + 16) ↦ₘ w2) **
            (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
            (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) **
            (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) **
            (Reg.x23 ↦ᵣ s.s7) **
            (.x5 ↦ᵣ (extractWord32 w2 (byteOffset (contentPtr + 16) / 4)).zeroExtend 64) **
            (.x6 ↦ᵣ (20 : Word)) ** (.x7 ↦ᵣ (20 : Word)) **
            (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (20 : Word)) **
            (.x31 ↦ᵣ contentPtr) **
            (.x0 ↦ᵣ (0 : Word)) **
            regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
            regOwn .x28 ** regOwn .x29 ** regOwn .x30) := by
      refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => hq)
        (cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x5)
          (P := Pcore ** memOwn (toBuf + 16) ** regOwn .x7 ** regOwn .x6)
          (fun t0Old => ?_))
      refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => hq)
        (cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x6)
          (P := Pcore ** memOwn (toBuf + 16) ** regOwn .x7 ** (.x5 ↦ᵣ t0Old))
          (fun t1Old => ?_))
      refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => hq)
        (cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x7)
          (P := Pcore ** memOwn (toBuf + 16) ** (.x6 ↦ᵣ t1Old) ** (.x5 ↦ᵣ t0Old))
          (fun t2Old => ?_))
      refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => hq)
        (cpsTripleWithin_of_forall_memIs_to_memOwn (a := toBuf + 16)
          (P := Pcore ** (.x7 ↦ᵣ t2Old) ** (.x6 ↦ᵣ t1Old) ** (.x5 ↦ᵣ t0Old))
          (fun old16' => ?_))
      have h := extractHaveFieldCopy_then_epi sp0 spC s txBase lenW typeW
        innerW endPtr cursor contentPtr toBuf isCreationPtr
        t2Old t1Old t0Old next w0 w1 w2 old16' LinkWalkNext5 s7 txBytes
        hspC hret hcalign hcover hcvalid htalign htover htvalid
      have hF := cpsTripleWithin_frameR
        (regOwn .x28 ** regOwn .x29 ** regOwn .x30)
        (by
          apply pcFree_sepConj
          · exact pcFree_regOwn
          · apply pcFree_sepConj
            · exact pcFree_regOwn
            · exact pcFree_regOwn) h
      exact cpsTripleWithin_weaken (fun _ hp => by
        dsimp only [Pcore] at hp ⊢
        xperm_hyp hp) (fun _ hq => by
        dsimp only [extractToBufOwn] at hq ⊢
        xperm_hyp hq) hF
    exact cpsTripleWithin_weaken (fun _ hp => by
      dsimp only [Pcore, midOwned, joinStackAmbient, haveFieldCopyAmbient,
        extractToBufOwn, wn5Stable] at hp ⊢
      xperm_hyp hp) (fun _ hq => hq) htemps
  have hTo2 :
      cpsTripleWithin (1 + 1) AfterWalkNext5Bne HaveField extractLinkedCode
        (wn5OkConcrete txBase lenW typeW innerW endPtr next (20 : Word)
            txBytes srcOff5 **
          midOwned spC s toBuf isCreationPtr s7 **
          (contentPtr ↦ₘ w0) ** ((contentPtr + 8) ↦ₘ w1) ** ((contentPtr + 16) ↦ₘ w2))
        (wn5Stable txBase lenW typeW innerW endPtr cursor **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkWalkNext5) **
          bytesRegion txBase txBytes **
          (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (20 : Word)) **
          (.x31 ↦ᵣ contentPtr) **
          midOwned spC s toBuf isCreationPtr s7 **
          (contentPtr ↦ₘ w0) ** ((contentPtr + 8) ↦ₘ w1) ** ((contentPtr + 16) ↦ₘ w2)) := by
    refine cpsTripleWithin_weaken (fun _ hp => by
      dsimp only [contentPtr] at hp ⊢; xperm_hyp hp) (fun _ hq => by
      dsimp only [contentPtr, cursor] at hq ⊢; xperm_hyp hq) hToF
  exact cpsTripleWithin_seq_same_cr hTo2 hCopy

set_option maxRecDepth 8000 in
/-- wn5 prep under midOwned. -/
theorem extractWalkNext5Prep_owned
    (spC : Word) (s : ExtractSaved)
    (txBase lenW typeW innerW endPtr next len toBuf isCreationPtr s7 : Word)
    (txBytes : List (BitVec 8)) (srcOff0 : Nat) :
    cpsTripleWithin (1 + (1 + 1)) AfterWalkNext4Bne WalkNext5JalPc extractLinkedCode
      (wn4OkConcrete txBase lenW typeW innerW endPtr next len txBytes srcOff0 **
        midOwned spC s toBuf isCreationPtr s7)
      (wn5Stable txBase lenW typeW innerW endPtr next **
        (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ len) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ LinkWalkNext4) ** bytesRegion txBase txBytes **
        midOwned spC s toBuf isCreationPtr s7) := by
  have h := extractWalkNext5Prep_framed txBase lenW typeW innerW endPtr next len
    txBytes srcOff0
  have hF := cpsTripleWithin_frameR
    (midOwned spC s toBuf isCreationPtr s7) (midOwned_pcFree _ _ _ _ _) h
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hF

set_option maxRecDepth 8000 in
/-- wn5 call under midOwned. -/
theorem extractWalkNext5Call_owned
    (spC : Word) (s : ExtractSaved)
    (txBase lenW typeW innerW endPtr toBuf isCreationPtr s7 : Word)
    (txBytes : List (BitVec 8)) (srcOff : Nat)
    (hsalign : txBase.toNat % 8 = 0)
    (hoff : srcOff < txBytes.length)
    (hover : txBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (txBase + BitVec.ofNat 64 srcOff) = true)
    (hss : ¬ BitVec.ult ((txBytes[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((txBytes[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        srcOff + 1 < txBytes.length ∧ txBase.toNat + (srcOff + 1) < 2 ^ 64 ∧
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff + 1)) = true)
    (hls : ¬ BitVec.ult ((txBytes[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((txBytes[srcOff]'hoff).zeroExtend 64) (0xc0 : Word) = true →
        srcOff + 1 + ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ txBytes.length ∧
        txBase.toNat + (srcOff + 1 +
          ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff + 1 + k)) = true)
    (hll : ¬ BitVec.ult ((txBytes[srcOff]'hoff).zeroExtend 64) (0xf8 : Word) = true →
        srcOff + 1 + ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ txBytes.length ∧
        txBase.toNat + (srcOff + 1 +
          ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff + 1 + k)) = true) :
    cpsTripleWithin (1 + 87) WalkNext5JalPc LinkWalkNext5 extractLinkedCode
      (wn5Stable txBase lenW typeW innerW endPtr
          (txBase + BitVec.ofNat 64 srcOff) **
        (.x10 ↦ᵣ (txBase + BitVec.ofNat 64 srcOff)) **
        (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ LinkWalkNext4) ** bytesRegion txBase txBytes **
        midOwned spC s toBuf isCreationPtr s7)
      (wn5Stable txBase lenW typeW innerW endPtr
          (txBase + BitVec.ofNat 64 srcOff) **
        wn5Common txBase txBytes **
        wn0OkFail txBase endPtr txBytes srcOff **
        midOwned spC s toBuf isCreationPtr s7) := by
  have h := extractWalkNext5Call_type234 txBase lenW typeW innerW endPtr
    txBytes srcOff hsalign hoff hover hvalid hss hls hll
  have hF := cpsTripleWithin_frameR
    (midOwned spC s toBuf isCreationPtr s7) (midOwned_pcFree _ _ _ _ _) h
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hF

set_option maxRecDepth 8000 in
/-- wn5 OK exists_pre→BNE under midOwned. -/
theorem extractWalkNext5OkNested_owned
    (spC : Word) (s : ExtractSaved)
    (txBase lenW typeW innerW endPtr toBuf isCreationPtr s7 : Word)
    (txBytes : List (BitVec 8)) (srcOff : Nat) :
    cpsTripleWithin 1 LinkWalkNext5 AfterWalkNext5Bne extractLinkedCode
      (wn5Stable txBase lenW typeW innerW endPtr
          (txBase + BitVec.ofNat 64 srcOff) **
        wn5Common txBase txBytes **
        rlpWalkNextOk (txBase + BitVec.ofNat 64 srcOff) endPtr txBytes srcOff **
        midOwned spC s toBuf isCreationPtr s7)
      (fun h => ∃ next len : Word,
        (wn5OkConcrete txBase lenW typeW innerW endPtr next len
          txBytes srcOff **
          midOwned spC s toBuf isCreationPtr s7) h) := by
  have h := extractWalkNext5OkNested_bne txBase lenW typeW innerW endPtr
    txBytes srcOff
  have hF := cpsTripleWithin_frameR
    (midOwned spC s toBuf isCreationPtr s7) (midOwned_pcFree _ _ _ _ _) h
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun h hq => by
      obtain ⟨h1, h2, hd, hu, hEx, hM⟩ := hq
      obtain ⟨next, len, hOk⟩ := hEx
      exact ⟨next, len, h1, h2, hd, hu, hOk, hM⟩) hF


set_option maxRecDepth 8000 in
/-- type234 AfterSave → WalkNext0 under midOwned. -/
theorem extractType234ToWalkNext0_owned
    (spC : Word) (s : ExtractSaved)
    (txBase lenW typeW innerW cursor endPtr toBuf isCreationPtr s7 : Word)
    (txBytes : List (BitVec 8))
    (hne0 : typeW ≠ 0) (hne1 : typeW ≠ 1) :
    cpsTripleWithin ((1 + (1 + (1 + 1))) + (1 + 1))
      AfterSaveCursor WalkNext0JalPc extractLinkedCode
      (afterSaveFrameTy txBase lenW typeW innerW cursor endPtr txBytes **
        (.x20 ↦ᵣ typeW) ** regOwn .x5 ** (.x0 ↦ᵣ (0 : Word)) **
        midOwned spC s toBuf isCreationPtr s7)
      (type234StartFrame txBase lenW typeW innerW cursor endPtr txBytes **
        midOwned spC s toBuf isCreationPtr s7) := by
  have h := extractType234ToWalkNext0 txBase lenW typeW innerW cursor endPtr
    txBytes hne0 hne1
  have hF := cpsTripleWithin_frameR
    (midOwned spC s toBuf isCreationPtr s7) (midOwned_pcFree _ _ _ _ _) h
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hF

set_option maxRecDepth 8000 in
/-- wn0 call under midOwned. -/
theorem extractWalkNext0Call_owned
    (spC : Word) (s : ExtractSaved)
    (txBase lenW typeW innerW endPtr toBuf isCreationPtr s7 : Word)
    (txBytes : List (BitVec 8)) (srcOff : Nat)
    (hsalign : txBase.toNat % 8 = 0)
    (hoff : srcOff < txBytes.length)
    (hover : txBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (txBase + BitVec.ofNat 64 srcOff) = true)
    (hss : ¬ BitVec.ult ((txBytes[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((txBytes[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        srcOff + 1 < txBytes.length ∧ txBase.toNat + (srcOff + 1) < 2 ^ 64 ∧
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff + 1)) = true)
    (hls : ¬ BitVec.ult ((txBytes[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((txBytes[srcOff]'hoff).zeroExtend 64) (0xc0 : Word) = true →
        srcOff + 1 + ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ txBytes.length ∧
        txBase.toNat + (srcOff + 1 +
          ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff + 1 + k)) = true)
    (hll : ¬ BitVec.ult ((txBytes[srcOff]'hoff).zeroExtend 64) (0xf8 : Word) = true →
        srcOff + 1 + ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ txBytes.length ∧
        txBase.toNat + (srcOff + 1 +
          ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff + 1 + k)) = true) :
    cpsTripleWithin (1 + 87) WalkNext0JalPc LinkWalkNext0 extractLinkedCode
      (type234StartFrame txBase lenW typeW innerW
          (txBase + BitVec.ofNat 64 srcOff) endPtr txBytes **
        midOwned spC s toBuf isCreationPtr s7)
      (wn0Stable txBase lenW typeW innerW endPtr
          (txBase + BitVec.ofNat 64 srcOff) **
        wn0Common txBase txBytes **
        wn0OkFail txBase endPtr txBytes srcOff **
        midOwned spC s toBuf isCreationPtr s7) := by
  have h := extractWalkNext0Call_type234 txBase lenW typeW innerW endPtr
    txBytes srcOff hsalign hoff hover hvalid hss hls hll
  have hF := cpsTripleWithin_frameR
    (midOwned spC s toBuf isCreationPtr s7) (midOwned_pcFree _ _ _ _ _) h
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hF

set_option maxRecDepth 8000 in
/-- wn0 OK exists_pre→BNE under midOwned. -/
theorem extractWalkNext0OkNested_owned
    (spC : Word) (s : ExtractSaved)
    (txBase lenW typeW innerW endPtr toBuf isCreationPtr s7 : Word)
    (txBytes : List (BitVec 8)) (srcOff : Nat) :
    cpsTripleWithin 1 LinkWalkNext0 AfterWalkNext0Bne extractLinkedCode
      (wn0Stable txBase lenW typeW innerW endPtr
          (txBase + BitVec.ofNat 64 srcOff) **
        wn0Common txBase txBytes **
        rlpWalkNextOk (txBase + BitVec.ofNat 64 srcOff) endPtr txBytes srcOff **
        midOwned spC s toBuf isCreationPtr s7)
      (fun h => ∃ next len : Word,
        (wn0OkConcrete txBase lenW typeW innerW endPtr next len
          txBytes srcOff **
          midOwned spC s toBuf isCreationPtr s7) h) := by
  have h := extractWalkNext0OkNested_bne txBase lenW typeW innerW endPtr
    txBytes srcOff
  have hF := cpsTripleWithin_frameR
    (midOwned spC s toBuf isCreationPtr s7) (midOwned_pcFree _ _ _ _ _) h
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun h hq => by
      obtain ⟨h1, h2, hd, hu, hEx, hM⟩ := hq
      obtain ⟨next, len, hOk⟩ := hEx
      exact ⟨next, len, h1, h2, hd, hu, hOk, hM⟩) hF

/-- wn1 prep under midOwned. -/
theorem extractWalkNext1Prep_owned
    (spC : Word) (s : ExtractSaved)
    (txBase lenW typeW innerW endPtr next len toBuf isCreationPtr s7 : Word)
    (txBytes : List (BitVec 8)) (srcOff0 : Nat) :
    cpsTripleWithin (1 + (1 + 1)) AfterWalkNext0Bne WalkNext1JalPc extractLinkedCode
      (wn0OkConcrete txBase lenW typeW innerW endPtr next len txBytes srcOff0 **
        midOwned spC s toBuf isCreationPtr s7)
      (wn1Stable txBase lenW typeW innerW endPtr next **
        (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ len) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ LinkWalkNext0) ** bytesRegion txBase txBytes **
        midOwned spC s toBuf isCreationPtr s7) := by
  have h := extractWalkNext1Prep_framed txBase lenW typeW innerW endPtr next len
    txBytes srcOff0
  have hF := cpsTripleWithin_frameR
    (midOwned spC s toBuf isCreationPtr s7) (midOwned_pcFree _ _ _ _ _) h
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hF

set_option maxRecDepth 8000 in
/-- wn1 call under midOwned. -/
theorem extractWalkNext1Call_owned
    (spC : Word) (s : ExtractSaved)
    (txBase lenW typeW innerW endPtr toBuf isCreationPtr s7 : Word)
    (txBytes : List (BitVec 8)) (srcOff : Nat)
    (hsalign : txBase.toNat % 8 = 0)
    (hoff : srcOff < txBytes.length)
    (hover : txBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (txBase + BitVec.ofNat 64 srcOff) = true)
    (hss : ¬ BitVec.ult ((txBytes[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((txBytes[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        srcOff + 1 < txBytes.length ∧ txBase.toNat + (srcOff + 1) < 2 ^ 64 ∧
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff + 1)) = true)
    (hls : ¬ BitVec.ult ((txBytes[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((txBytes[srcOff]'hoff).zeroExtend 64) (0xc0 : Word) = true →
        srcOff + 1 + ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ txBytes.length ∧
        txBase.toNat + (srcOff + 1 +
          ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff + 1 + k)) = true)
    (hll : ¬ BitVec.ult ((txBytes[srcOff]'hoff).zeroExtend 64) (0xf8 : Word) = true →
        srcOff + 1 + ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ txBytes.length ∧
        txBase.toNat + (srcOff + 1 +
          ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff + 1 + k)) = true) :
    cpsTripleWithin (1 + 87) WalkNext1JalPc LinkWalkNext1 extractLinkedCode
      (wn1Stable txBase lenW typeW innerW endPtr
          (txBase + BitVec.ofNat 64 srcOff) **
        (.x10 ↦ᵣ (txBase + BitVec.ofNat 64 srcOff)) **
        (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ LinkWalkNext0) ** bytesRegion txBase txBytes **
        midOwned spC s toBuf isCreationPtr s7)
      (wn1Stable txBase lenW typeW innerW endPtr
          (txBase + BitVec.ofNat 64 srcOff) **
        wn1Common txBase txBytes **
        wn0OkFail txBase endPtr txBytes srcOff **
        midOwned spC s toBuf isCreationPtr s7) := by
  have h := extractWalkNext1Call_type234 txBase lenW typeW innerW endPtr
    txBytes srcOff hsalign hoff hover hvalid hss hls hll
  have hF := cpsTripleWithin_frameR
    (midOwned spC s toBuf isCreationPtr s7) (midOwned_pcFree _ _ _ _ _) h
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hF

set_option maxRecDepth 8000 in
/-- wn1 OK exists_pre→BNE under midOwned. -/
theorem extractWalkNext1OkNested_owned
    (spC : Word) (s : ExtractSaved)
    (txBase lenW typeW innerW endPtr toBuf isCreationPtr s7 : Word)
    (txBytes : List (BitVec 8)) (srcOff : Nat) :
    cpsTripleWithin 1 LinkWalkNext1 AfterWalkNext1Bne extractLinkedCode
      (wn1Stable txBase lenW typeW innerW endPtr
          (txBase + BitVec.ofNat 64 srcOff) **
        wn1Common txBase txBytes **
        rlpWalkNextOk (txBase + BitVec.ofNat 64 srcOff) endPtr txBytes srcOff **
        midOwned spC s toBuf isCreationPtr s7)
      (fun h => ∃ next len : Word,
        (wn1OkConcrete txBase lenW typeW innerW endPtr next len
          txBytes srcOff **
          midOwned spC s toBuf isCreationPtr s7) h) := by
  have h := extractWalkNext1OkNested_bne txBase lenW typeW innerW endPtr
    txBytes srcOff
  have hF := cpsTripleWithin_frameR
    (midOwned spC s toBuf isCreationPtr s7) (midOwned_pcFree _ _ _ _ _) h
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun h hq => by
      obtain ⟨h1, h2, hd, hu, hEx, hM⟩ := hq
      obtain ⟨next, len, hOk⟩ := hEx
      exact ⟨next, len, h1, h2, hd, hu, hOk, hM⟩) hF


set_option maxRecDepth 8000 in
/-- wn2 prep under midOwned. -/
theorem extractWalkNext2Prep_owned
    (spC : Word) (s : ExtractSaved)
    (txBase lenW typeW innerW endPtr next len toBuf isCreationPtr s7 : Word)
    (txBytes : List (BitVec 8)) (srcOff0 : Nat) :
    cpsTripleWithin (1 + (1 + 1)) AfterWalkNext1Bne WalkNext2JalPc extractLinkedCode
      (wn1OkConcrete txBase lenW typeW innerW endPtr next len txBytes srcOff0 **
        midOwned spC s toBuf isCreationPtr s7)
      (wn2Stable txBase lenW typeW innerW endPtr next **
        (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ len) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ LinkWalkNext1) ** bytesRegion txBase txBytes **
        midOwned spC s toBuf isCreationPtr s7) := by
  have h := extractWalkNext2Prep_framed txBase lenW typeW innerW endPtr next len
    txBytes srcOff0
  have hF := cpsTripleWithin_frameR
    (midOwned spC s toBuf isCreationPtr s7) (midOwned_pcFree _ _ _ _ _) h
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hF

set_option maxRecDepth 8000 in
/-- wn2 call under midOwned. -/
theorem extractWalkNext2Call_owned
    (spC : Word) (s : ExtractSaved)
    (txBase lenW typeW innerW endPtr toBuf isCreationPtr s7 : Word)
    (txBytes : List (BitVec 8)) (srcOff : Nat)
    (hsalign : txBase.toNat % 8 = 0)
    (hoff : srcOff < txBytes.length)
    (hover : txBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (txBase + BitVec.ofNat 64 srcOff) = true)
    (hss : ¬ BitVec.ult ((txBytes[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((txBytes[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        srcOff + 1 < txBytes.length ∧ txBase.toNat + (srcOff + 1) < 2 ^ 64 ∧
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff + 1)) = true)
    (hls : ¬ BitVec.ult ((txBytes[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((txBytes[srcOff]'hoff).zeroExtend 64) (0xc0 : Word) = true →
        srcOff + 1 + ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ txBytes.length ∧
        txBase.toNat + (srcOff + 1 +
          ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff + 1 + k)) = true)
    (hll : ¬ BitVec.ult ((txBytes[srcOff]'hoff).zeroExtend 64) (0xf8 : Word) = true →
        srcOff + 1 + ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ txBytes.length ∧
        txBase.toNat + (srcOff + 1 +
          ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff + 1 + k)) = true) :
    cpsTripleWithin (1 + 87) WalkNext2JalPc LinkWalkNext2 extractLinkedCode
      (wn2Stable txBase lenW typeW innerW endPtr
          (txBase + BitVec.ofNat 64 srcOff) **
        (.x10 ↦ᵣ (txBase + BitVec.ofNat 64 srcOff)) **
        (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ LinkWalkNext1) ** bytesRegion txBase txBytes **
        midOwned spC s toBuf isCreationPtr s7)
      (wn2Stable txBase lenW typeW innerW endPtr
          (txBase + BitVec.ofNat 64 srcOff) **
        wn2Common txBase txBytes **
        wn0OkFail txBase endPtr txBytes srcOff **
        midOwned spC s toBuf isCreationPtr s7) := by
  have h := extractWalkNext2Call_type234 txBase lenW typeW innerW endPtr
    txBytes srcOff hsalign hoff hover hvalid hss hls hll
  have hF := cpsTripleWithin_frameR
    (midOwned spC s toBuf isCreationPtr s7) (midOwned_pcFree _ _ _ _ _) h
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hF

set_option maxRecDepth 8000 in
/-- wn2 OK exists_pre→BNE under midOwned. -/
theorem extractWalkNext2OkNested_owned
    (spC : Word) (s : ExtractSaved)
    (txBase lenW typeW innerW endPtr toBuf isCreationPtr s7 : Word)
    (txBytes : List (BitVec 8)) (srcOff : Nat) :
    cpsTripleWithin 1 LinkWalkNext2 AfterWalkNext2Bne extractLinkedCode
      (wn2Stable txBase lenW typeW innerW endPtr
          (txBase + BitVec.ofNat 64 srcOff) **
        wn2Common txBase txBytes **
        rlpWalkNextOk (txBase + BitVec.ofNat 64 srcOff) endPtr txBytes srcOff **
        midOwned spC s toBuf isCreationPtr s7)
      (fun h => ∃ next len : Word,
        (wn2OkConcrete txBase lenW typeW innerW endPtr next len
          txBytes srcOff **
          midOwned spC s toBuf isCreationPtr s7) h) := by
  have h := extractWalkNext2OkNested_bne txBase lenW typeW innerW endPtr
    txBytes srcOff
  have hF := cpsTripleWithin_frameR
    (midOwned spC s toBuf isCreationPtr s7) (midOwned_pcFree _ _ _ _ _) h
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun h hq => by
      obtain ⟨h1, h2, hd, hu, hEx, hM⟩ := hq
      obtain ⟨next, len, hOk⟩ := hEx
      exact ⟨next, len, h1, h2, hd, hu, hOk, hM⟩) hF


set_option maxRecDepth 8000 in
/-- wn3 prep under midOwned. -/
theorem extractWalkNext3Prep_owned
    (spC : Word) (s : ExtractSaved)
    (txBase lenW typeW innerW endPtr next len toBuf isCreationPtr s7 : Word)
    (txBytes : List (BitVec 8)) (srcOff0 : Nat) :
    cpsTripleWithin (1 + (1 + 1)) AfterWalkNext2Bne WalkNext3JalPc extractLinkedCode
      (wn2OkConcrete txBase lenW typeW innerW endPtr next len txBytes srcOff0 **
        midOwned spC s toBuf isCreationPtr s7)
      (wn3Stable txBase lenW typeW innerW endPtr next **
        (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ len) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ LinkWalkNext2) ** bytesRegion txBase txBytes **
        midOwned spC s toBuf isCreationPtr s7) := by
  have h := extractWalkNext3Prep_framed txBase lenW typeW innerW endPtr next len
    txBytes srcOff0
  have hF := cpsTripleWithin_frameR
    (midOwned spC s toBuf isCreationPtr s7) (midOwned_pcFree _ _ _ _ _) h
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hF

set_option maxRecDepth 8000 in
/-- wn3 call under midOwned. -/
theorem extractWalkNext3Call_owned
    (spC : Word) (s : ExtractSaved)
    (txBase lenW typeW innerW endPtr toBuf isCreationPtr s7 : Word)
    (txBytes : List (BitVec 8)) (srcOff : Nat)
    (hsalign : txBase.toNat % 8 = 0)
    (hoff : srcOff < txBytes.length)
    (hover : txBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (txBase + BitVec.ofNat 64 srcOff) = true)
    (hss : ¬ BitVec.ult ((txBytes[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((txBytes[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        srcOff + 1 < txBytes.length ∧ txBase.toNat + (srcOff + 1) < 2 ^ 64 ∧
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff + 1)) = true)
    (hls : ¬ BitVec.ult ((txBytes[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((txBytes[srcOff]'hoff).zeroExtend 64) (0xc0 : Word) = true →
        srcOff + 1 + ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ txBytes.length ∧
        txBase.toNat + (srcOff + 1 +
          ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff + 1 + k)) = true)
    (hll : ¬ BitVec.ult ((txBytes[srcOff]'hoff).zeroExtend 64) (0xf8 : Word) = true →
        srcOff + 1 + ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ txBytes.length ∧
        txBase.toNat + (srcOff + 1 +
          ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff + 1 + k)) = true) :
    cpsTripleWithin (1 + 87) WalkNext3JalPc LinkWalkNext3 extractLinkedCode
      (wn3Stable txBase lenW typeW innerW endPtr
          (txBase + BitVec.ofNat 64 srcOff) **
        (.x10 ↦ᵣ (txBase + BitVec.ofNat 64 srcOff)) **
        (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ LinkWalkNext2) ** bytesRegion txBase txBytes **
        midOwned spC s toBuf isCreationPtr s7)
      (wn3Stable txBase lenW typeW innerW endPtr
          (txBase + BitVec.ofNat 64 srcOff) **
        wn3Common txBase txBytes **
        wn0OkFail txBase endPtr txBytes srcOff **
        midOwned spC s toBuf isCreationPtr s7) := by
  have h := extractWalkNext3Call_type234 txBase lenW typeW innerW endPtr
    txBytes srcOff hsalign hoff hover hvalid hss hls hll
  have hF := cpsTripleWithin_frameR
    (midOwned spC s toBuf isCreationPtr s7) (midOwned_pcFree _ _ _ _ _) h
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hF

set_option maxRecDepth 8000 in
/-- wn3 OK exists_pre→BNE under midOwned. -/
theorem extractWalkNext3OkNested_owned
    (spC : Word) (s : ExtractSaved)
    (txBase lenW typeW innerW endPtr toBuf isCreationPtr s7 : Word)
    (txBytes : List (BitVec 8)) (srcOff : Nat) :
    cpsTripleWithin 1 LinkWalkNext3 AfterWalkNext3Bne extractLinkedCode
      (wn3Stable txBase lenW typeW innerW endPtr
          (txBase + BitVec.ofNat 64 srcOff) **
        wn3Common txBase txBytes **
        rlpWalkNextOk (txBase + BitVec.ofNat 64 srcOff) endPtr txBytes srcOff **
        midOwned spC s toBuf isCreationPtr s7)
      (fun h => ∃ next len : Word,
        (wn3OkConcrete txBase lenW typeW innerW endPtr next len
          txBytes srcOff **
          midOwned spC s toBuf isCreationPtr s7) h) := by
  have h := extractWalkNext3OkNested_bne txBase lenW typeW innerW endPtr
    txBytes srcOff
  have hF := cpsTripleWithin_frameR
    (midOwned spC s toBuf isCreationPtr s7) (midOwned_pcFree _ _ _ _ _) h
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun h hq => by
      obtain ⟨h1, h2, hd, hu, hEx, hM⟩ := hq
      obtain ⟨next, len, hOk⟩ := hEx
      exact ⟨next, len, h1, h2, hd, hu, hOk, hM⟩) hF


set_option maxRecDepth 8000 in
/-- wn4 prep under midOwned. -/
theorem extractWalkNext4Prep_owned
    (spC : Word) (s : ExtractSaved)
    (txBase lenW typeW innerW endPtr next len toBuf isCreationPtr s7 : Word)
    (txBytes : List (BitVec 8)) (srcOff0 : Nat) :
    cpsTripleWithin (1 + (1 + 1)) AfterWalkNext3Bne WalkNext4JalPc extractLinkedCode
      (wn3OkConcrete txBase lenW typeW innerW endPtr next len txBytes srcOff0 **
        midOwned spC s toBuf isCreationPtr s7)
      (wn4Stable txBase lenW typeW innerW endPtr next **
        (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ len) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ LinkWalkNext3) ** bytesRegion txBase txBytes **
        midOwned spC s toBuf isCreationPtr s7) := by
  have h := extractWalkNext4Prep_framed txBase lenW typeW innerW endPtr next len
    txBytes srcOff0
  have hF := cpsTripleWithin_frameR
    (midOwned spC s toBuf isCreationPtr s7) (midOwned_pcFree _ _ _ _ _) h
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hF

set_option maxRecDepth 8000 in
/-- wn4 call under midOwned. -/
theorem extractWalkNext4Call_owned
    (spC : Word) (s : ExtractSaved)
    (txBase lenW typeW innerW endPtr toBuf isCreationPtr s7 : Word)
    (txBytes : List (BitVec 8)) (srcOff : Nat)
    (hsalign : txBase.toNat % 8 = 0)
    (hoff : srcOff < txBytes.length)
    (hover : txBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (txBase + BitVec.ofNat 64 srcOff) = true)
    (hss : ¬ BitVec.ult ((txBytes[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((txBytes[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        srcOff + 1 < txBytes.length ∧ txBase.toNat + (srcOff + 1) < 2 ^ 64 ∧
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff + 1)) = true)
    (hls : ¬ BitVec.ult ((txBytes[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((txBytes[srcOff]'hoff).zeroExtend 64) (0xc0 : Word) = true →
        srcOff + 1 + ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ txBytes.length ∧
        txBase.toNat + (srcOff + 1 +
          ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff + 1 + k)) = true)
    (hll : ¬ BitVec.ult ((txBytes[srcOff]'hoff).zeroExtend 64) (0xf8 : Word) = true →
        srcOff + 1 + ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ txBytes.length ∧
        txBase.toNat + (srcOff + 1 +
          ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((txBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (txBase + BitVec.ofNat 64 (srcOff + 1 + k)) = true) :
    cpsTripleWithin (1 + 87) WalkNext4JalPc LinkWalkNext4 extractLinkedCode
      (wn4Stable txBase lenW typeW innerW endPtr
          (txBase + BitVec.ofNat 64 srcOff) **
        (.x10 ↦ᵣ (txBase + BitVec.ofNat 64 srcOff)) **
        (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ LinkWalkNext3) ** bytesRegion txBase txBytes **
        midOwned spC s toBuf isCreationPtr s7)
      (wn4Stable txBase lenW typeW innerW endPtr
          (txBase + BitVec.ofNat 64 srcOff) **
        wn4Common txBase txBytes **
        wn0OkFail txBase endPtr txBytes srcOff **
        midOwned spC s toBuf isCreationPtr s7) := by
  have h := extractWalkNext4Call_type234 txBase lenW typeW innerW endPtr
    txBytes srcOff hsalign hoff hover hvalid hss hls hll
  have hF := cpsTripleWithin_frameR
    (midOwned spC s toBuf isCreationPtr s7) (midOwned_pcFree _ _ _ _ _) h
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hF

set_option maxRecDepth 8000 in
/-- wn4 OK exists_pre→BNE under midOwned. -/
theorem extractWalkNext4OkNested_owned
    (spC : Word) (s : ExtractSaved)
    (txBase lenW typeW innerW endPtr toBuf isCreationPtr s7 : Word)
    (txBytes : List (BitVec 8)) (srcOff : Nat) :
    cpsTripleWithin 1 LinkWalkNext4 AfterWalkNext4Bne extractLinkedCode
      (wn4Stable txBase lenW typeW innerW endPtr
          (txBase + BitVec.ofNat 64 srcOff) **
        wn4Common txBase txBytes **
        rlpWalkNextOk (txBase + BitVec.ofNat 64 srcOff) endPtr txBytes srcOff **
        midOwned spC s toBuf isCreationPtr s7)
      (fun h => ∃ next len : Word,
        (wn4OkConcrete txBase lenW typeW innerW endPtr next len
          txBytes srcOff **
          midOwned spC s toBuf isCreationPtr s7) h) := by
  have h := extractWalkNext4OkNested_bne txBase lenW typeW innerW endPtr
    txBytes srcOff
  have hF := cpsTripleWithin_frameR
    (midOwned spC s toBuf isCreationPtr s7) (midOwned_pcFree _ _ _ _ _) h
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun h hq => by
      obtain ⟨h1, h2, hd, hu, hEx, hM⟩ := hq
      obtain ⟨next, len, hOk⟩ := hEx
      exact ⟨next, len, h1, h2, hd, hu, hOk, hM⟩) hF

#print axioms extractType234ToWalkNext0_owned
#print axioms extractWalkNext0Call_owned
#print axioms extractWalkNext0OkNested_owned
#print axioms extractWalkNext1Prep_owned
#print axioms extractWalkNext1Call_owned
#print axioms extractWalkNext1OkNested_owned
#print axioms extractWalkNext2Prep_owned
#print axioms extractWalkNext2Call_owned
#print axioms extractWalkNext2OkNested_owned
#print axioms extractWalkNext3Prep_owned
#print axioms extractWalkNext3Call_owned
#print axioms extractWalkNext3OkNested_owned
#print axioms extractWalkNext4Prep_owned
#print axioms extractWalkNext4Call_owned
#print axioms extractWalkNext4OkNested_owned
set_option maxRecDepth 8000 in
/-- type-branch type234 under midOwned. -/
theorem extractTypeBranchType234_owned
    (spC : Word) (s : ExtractSaved)
    (txBase lenW typeW innerW cursor endPtr toBuf isCreationPtr s7 : Word)
    (txBytes : List (BitVec 8))
    (hne0 : typeW ≠ 0) (hne1 : typeW ≠ 1) :
    cpsTripleWithin (1 + (1 + (1 + 1))) AfterSaveCursor Type234Start extractLinkedCode
      (afterSaveFrameTy txBase lenW typeW innerW cursor endPtr txBytes **
        (.x20 ↦ᵣ typeW) ** regOwn .x5 ** (.x0 ↦ᵣ (0 : Word)) **
        midOwned spC s toBuf isCreationPtr s7)
      (afterSaveFrameTy txBase lenW typeW innerW cursor endPtr txBytes **
        (.x20 ↦ᵣ typeW) ** (.x5 ↦ᵣ (1 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        midOwned spC s toBuf isCreationPtr s7) := by
  have h := extractTypeBranchType234_framed txBase lenW typeW innerW cursor endPtr
    txBytes hne0 hne1
  have hF := cpsTripleWithin_frameR
    (midOwned spC s toBuf isCreationPtr s7) (midOwned_pcFree _ _ _ _ _) h
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hF

set_option maxRecDepth 8000 in
/-- type-branch legacy under midOwned. -/
theorem extractTypeBranchLegacy_owned
    (spC : Word) (s : ExtractSaved)
    (txBase lenW innerW cursor endPtr toBuf isCreationPtr s7 : Word)
    (txBytes : List (BitVec 8)) :
    cpsTripleWithin (1 + 1) AfterSaveCursor LegacyStart extractLinkedCode
      (afterSaveFrame txBase lenW innerW cursor endPtr txBytes **
        (.x20 ↦ᵣ (0 : Word)) ** regOwn .x5 ** (.x0 ↦ᵣ (0 : Word)) **
        midOwned spC s toBuf isCreationPtr s7)
      (afterSaveFrame txBase lenW innerW cursor endPtr txBytes **
        (.x20 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        midOwned spC s toBuf isCreationPtr s7) := by
  have h := extractTypeBranchLegacy_framed txBase lenW innerW cursor endPtr txBytes
  have hF := cpsTripleWithin_frameR
    (midOwned spC s toBuf isCreationPtr s7) (midOwned_pcFree _ _ _ _ _) h
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hF

set_option maxRecDepth 8000 in
/-- type-branch t1 under midOwned. -/
theorem extractTypeBranchT1_owned
    (spC : Word) (s : ExtractSaved)
    (txBase lenW innerW cursor endPtr toBuf isCreationPtr s7 : Word)
    (txBytes : List (BitVec 8)) :
    cpsTripleWithin (1 + (1 + (1 + 1))) AfterSaveCursor T1Start extractLinkedCode
      (afterSaveFrameTy txBase lenW (1 : Word) innerW cursor endPtr txBytes **
        (.x20 ↦ᵣ (1 : Word)) ** regOwn .x5 ** (.x0 ↦ᵣ (0 : Word)) **
        midOwned spC s toBuf isCreationPtr s7)
      (afterSaveFrameTy txBase lenW (1 : Word) innerW cursor endPtr txBytes **
        (.x20 ↦ᵣ (1 : Word)) ** (.x5 ↦ᵣ (1 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        midOwned spC s toBuf isCreationPtr s7) := by
  have h := extractTypeBranchT1_framed txBase lenW innerW cursor endPtr txBytes
  have hF := cpsTripleWithin_frameR
    (midOwned spC s toBuf isCreationPtr s7) (midOwned_pcFree _ _ _ _ _) h
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hF

#print axioms extractType234ToHaveField_owned
#print axioms extractType234HaveFieldCreation_then_epi
#print axioms extractType234HaveFieldCopy_then_epi
#print axioms extractWalkNext5Prep_owned
#print axioms extractWalkNext5Call_owned
#print axioms extractWalkNext5OkNested_owned
#print axioms extractTypeBranchType234_owned
#print axioms extractTypeBranchLegacy_owned
#print axioms extractTypeBranchT1_owned

end EvmAsm.Codegen.TxExtractToAddressSpec
