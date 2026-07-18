/-
  Extract mid: HaveField creation/copy under join ambient → EpiRestore.
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Codegen.Programs.TxExtractToAddressHaveFieldBody
import EvmAsm.Codegen.Programs.TxExtractToAddressTopTypeBranch
import EvmAsm.Codegen.Programs.TxIntrinsicStateGasSpec

namespace EvmAsm.Codegen.TxExtractToAddressSpec

open EvmAsm.Rv64
open EvmAsm.Codegen
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

/-- Ambient preserved across HaveField creation (no leaf atoms). -/
def haveFieldCreAmbient (txBase lenW typeW innerW toBuf contentPtr endPtr
    next : Word) (txBytes : List (BitVec 8)) : Assertion :=
  (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
    (TeaTypeAddr ↦ₘ typeW) ** (TeaInnerAddr ↦ₘ innerW) **
    (.x18 ↦ᵣ toBuf) **
    regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
    (.x20 ↦ᵣ typeW) **
    (.x21 ↦ᵣ contentPtr) ** (.x22 ↦ᵣ endPtr) **
    (.x11 ↦ᵣ (0 : Word)) **
    (.x31 ↦ᵣ (next - (0 : Word))) **
    bytesRegion txBase txBytes **
    extractToBufOwn toBuf

private theorem haveFieldCreAmbient_pcFree
    (txBase lenW typeW innerW toBuf contentPtr endPtr next : Word)
    (txBytes : List (BitVec 8)) :
    (haveFieldCreAmbient txBase lenW typeW innerW toBuf contentPtr endPtr
      next txBytes).pcFree := by
  unfold haveFieldCreAmbient extractToBufOwn; pcf

set_option maxRecDepth 8000 in
/-- Creation path under join ambient (len=0). -/
theorem extractHaveFieldCreation_framed
    (txBase lenW typeW innerW toBuf contentPtr endPtr next
      isCreationPtr t2Old t0Old a0Old : Word)
    (txBytes : List (BitVec 8)) :
    cpsTripleWithin (1 + (1 + (1 + (1 + (1 + 1))))) HaveField EpiRestore
      extractLinkedCode
      (haveFieldCreAmbient txBase lenW typeW innerW toBuf contentPtr endPtr
          next txBytes **
        (.x12 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ t2Old) **
        (.x19 ↦ᵣ isCreationPtr) ** (.x5 ↦ᵣ t0Old) ** (.x10 ↦ᵣ a0Old) **
        (.x0 ↦ᵣ (0 : Word)) ** memOwn isCreationPtr)
      (haveFieldCreAmbient txBase lenW typeW innerW toBuf contentPtr endPtr
          next txBytes **
        (.x12 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ (0 : Word)) **
        (.x19 ↦ᵣ isCreationPtr) ** (.x5 ↦ᵣ (1 : Word)) ** (.x10 ↦ᵣ (0 : Word)) **
        (.x0 ↦ᵣ (0 : Word)) ** (isCreationPtr ↦ₘ (1 : Word))) := by
  have h := extractHaveFieldCreation isCreationPtr t2Old t0Old a0Old
  have hF := cpsTripleWithin_frameR
    (haveFieldCreAmbient txBase lenW typeW innerW toBuf contentPtr endPtr
      next txBytes)
    (haveFieldCreAmbient_pcFree _ _ _ _ _ _ _ _ _) h
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hF

/-- Ambient for 20B copy (toBuf owned by leaf as memOwn cells). -/
def haveFieldCopyAmbient (txBase lenW typeW innerW endPtr
    cursor : Word) (txBytes : List (BitVec 8)) : Assertion :=
  (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
    (TeaTypeAddr ↦ₘ typeW) ** (TeaInnerAddr ↦ₘ innerW) **
    regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
    (.x20 ↦ᵣ typeW) **
    (.x21 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr) **
    (.x11 ↦ᵣ (0 : Word)) **
    bytesRegion txBase txBytes

private theorem haveFieldCopyAmbient_pcFree
    (txBase lenW typeW innerW endPtr cursor : Word)
    (txBytes : List (BitVec 8)) :
    (haveFieldCopyAmbient txBase lenW typeW innerW endPtr cursor
      txBytes).pcFree := by
  unfold haveFieldCopyAmbient; pcf

set_option maxRecDepth 8000 in
/-- 20B copy path under join ambient (len=20). -/
theorem extractHaveFieldCopy_framed
    (txBase lenW typeW innerW endPtr cursor contentPtr toBuf isCreationPtr
      t2Old t1Old t0Old a0Old w0 w1 w2 old16 : Word)
    (txBytes : List (BitVec 8))
    (hcalign : contentPtr.toNat % 8 = 0)
    (hcover : contentPtr.toNat + 16 < 2 ^ 64)
    (hcvalid : isValidMemAccess (contentPtr + (16 : Word)) = true)
    (htalign : toBuf.toNat % 8 = 0)
    (htover : toBuf.toNat + 16 < 2 ^ 64)
    (htvalid : isValidMemAccess (toBuf + (16 : Word)) = true) :
    cpsTripleWithin
      (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + 1))))))))))))
      HaveField EpiRestore extractLinkedCode
      (haveFieldCopyAmbient txBase lenW typeW innerW endPtr cursor txBytes **
        (.x12 ↦ᵣ (20 : Word)) ** (.x7 ↦ᵣ t2Old) ** (.x6 ↦ᵣ t1Old) **
        (.x31 ↦ᵣ contentPtr) ** (.x18 ↦ᵣ toBuf) ** (.x19 ↦ᵣ isCreationPtr) **
        (.x5 ↦ᵣ t0Old) ** (.x10 ↦ᵣ a0Old) ** (.x0 ↦ᵣ (0 : Word)) **
        (contentPtr ↦ₘ w0) ** ((contentPtr + 8) ↦ₘ w1) ** ((contentPtr + 16) ↦ₘ w2) **
        memOwn toBuf ** memOwn (toBuf + 8) ** ((toBuf + 16) ↦ₘ old16) **
        memOwn isCreationPtr)
      (haveFieldCopyAmbient txBase lenW typeW innerW endPtr cursor txBytes **
        (.x12 ↦ᵣ (20 : Word)) ** (.x7 ↦ᵣ (20 : Word)) ** (.x6 ↦ᵣ (20 : Word)) **
        (.x31 ↦ᵣ contentPtr) ** (.x18 ↦ᵣ toBuf) ** (.x19 ↦ᵣ isCreationPtr) **
        (.x5 ↦ᵣ (extractWord32 w2 (byteOffset (contentPtr + 16) / 4)).zeroExtend 64) **
        (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        (contentPtr ↦ₘ w0) ** ((contentPtr + 8) ↦ₘ w1) ** ((contentPtr + 16) ↦ₘ w2) **
        (toBuf ↦ₘ w0) ** ((toBuf + 8) ↦ₘ w1) **
        ((toBuf + 16) ↦ₘ replaceWord32 old16 ((byteOffset (toBuf + 16)) / 4)
          (((extractWord32 w2 (byteOffset (contentPtr + 16) / 4)).zeroExtend 64).truncate 32)) **
        (isCreationPtr ↦ₘ (0 : Word))) := by
  have h := extractHaveFieldCopy contentPtr toBuf isCreationPtr t2Old t1Old t0Old
    a0Old w0 w1 w2 old16 hcalign hcover hcvalid htalign htover htvalid
  have hF := cpsTripleWithin_frameR
    (haveFieldCopyAmbient txBase lenW typeW innerW endPtr cursor txBytes)
    (haveFieldCopyAmbient_pcFree _ _ _ _ _ _ _) h
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hF

#print axioms extractHaveFieldCreation_framed
#print axioms extractHaveFieldCopy_framed

end EvmAsm.Codegen.TxExtractToAddressSpec
