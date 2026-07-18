/-
  Ambient dual of TopLegacy frames (split loadPtr / regionBase).
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Codegen.Programs.TxExtractToAddressLegacyWalk
import EvmAsm.Codegen.Programs.TxExtractToAddressTopLegacy
import EvmAsm.Codegen.Programs.TxExtractToAddressTopFrontWalkInitAmbient
import EvmAsm.Codegen.Programs.TxExtractToAddressTypeBranch
import EvmAsm.Codegen.Programs.TxExtractToAddressTopTypeBranch
import EvmAsm.Codegen.Programs.TxExtractToAddressTopMidOwned
import EvmAsm.Codegen.Programs.TxIntrinsicStateGasSpec

namespace EvmAsm.Codegen.TxExtractToAddressSpec

open EvmAsm.Rv64
open EvmAsm.Rv64.RLP
open EvmAsm.Codegen
open EvmAsm.Codegen.TxIntrinsicStateGasSpec
  (extractToBufOwn nExtractStackDwords)

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

/-- Legacy start frame ambient (type=0 after branch). -/
def legacyStartFrameAmbient (loadPtr regionBase lenW innerW cursor endPtr : Word)
    (bs : List (BitVec 8)) : Assertion :=
  afterSaveFrameTyAmbient loadPtr regionBase lenW (0 : Word) innerW
      cursor endPtr bs **
    (.x20 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))

/-- Stable ambient for legacy walks: x8=loadPtr; s5/s6 hold cursor/end. -/
def legStableAmbient (loadPtr lenW innerW endPtr cursor : Word) : Assertion :=
  (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
    (TeaTypeAddr ↦ₘ (0 : Word)) ** (TeaInnerAddr ↦ₘ innerW) **
    regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
    (.x20 ↦ᵣ (0 : Word)) **
    (.x21 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr)

theorem legStableAmbient_pcFree (loadPtr lenW innerW endPtr cursor : Word) :
    (legStableAmbient loadPtr lenW innerW endPtr cursor).pcFree := by
  unfold legStableAmbient; pcf

def leg0CommonAmbient (regionBase : Word) (bs : List (BitVec 8)) : Assertion :=
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
    regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkLegacyWalk0) **
    bytesRegion regionBase bs

def leg1CommonAmbient (regionBase : Word) (bs : List (BitVec 8)) : Assertion :=
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
    regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkLegacyWalk1) **
    bytesRegion regionBase bs

def leg2CommonAmbient (regionBase : Word) (bs : List (BitVec 8)) : Assertion :=
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
    regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkLegacyWalk2) **
    bytesRegion regionBase bs

def leg3CommonAmbient (regionBase : Word) (bs : List (BitVec 8)) : Assertion :=
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
    regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkLegacyWalk3) **
    bytesRegion regionBase bs

def leg0OkRegsAmbient (loadPtr regionBase lenW innerW endPtr next len : Word)
    (bs : List (BitVec 8)) (absOff : Nat) : Assertion :=
  legStableAmbient loadPtr lenW innerW endPtr
      (regionBase + BitVec.ofNat 64 absOff) **
    leg0CommonAmbient regionBase bs **
    (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len)

def leg0OkConcreteAmbient (loadPtr regionBase lenW innerW endPtr next len : Word)
    (bs : List (BitVec 8)) (absOff : Nat) : Assertion :=
  leg0OkRegsAmbient loadPtr regionBase lenW innerW endPtr next len bs absOff **
    ⌜rlpItemDecode bs absOff (regionBase + BitVec.ofNat 64 absOff)
      endPtr next len⌝

def leg1OkRegsAmbient (loadPtr regionBase lenW innerW endPtr next len : Word)
    (bs : List (BitVec 8)) (absOff : Nat) : Assertion :=
  legStableAmbient loadPtr lenW innerW endPtr
      (regionBase + BitVec.ofNat 64 absOff) **
    leg1CommonAmbient regionBase bs **
    (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len)

def leg1OkConcreteAmbient (loadPtr regionBase lenW innerW endPtr next len : Word)
    (bs : List (BitVec 8)) (absOff : Nat) : Assertion :=
  leg1OkRegsAmbient loadPtr regionBase lenW innerW endPtr next len bs absOff **
    ⌜rlpItemDecode bs absOff (regionBase + BitVec.ofNat 64 absOff)
      endPtr next len⌝

def leg2OkRegsAmbient (loadPtr regionBase lenW innerW endPtr next len : Word)
    (bs : List (BitVec 8)) (absOff : Nat) : Assertion :=
  legStableAmbient loadPtr lenW innerW endPtr
      (regionBase + BitVec.ofNat 64 absOff) **
    leg2CommonAmbient regionBase bs **
    (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len)

def leg2OkConcreteAmbient (loadPtr regionBase lenW innerW endPtr next len : Word)
    (bs : List (BitVec 8)) (absOff : Nat) : Assertion :=
  leg2OkRegsAmbient loadPtr regionBase lenW innerW endPtr next len bs absOff **
    ⌜rlpItemDecode bs absOff (regionBase + BitVec.ofNat 64 absOff)
      endPtr next len⌝

def leg3OkRegsAmbient (loadPtr regionBase lenW innerW endPtr next len : Word)
    (bs : List (BitVec 8)) (absOff : Nat) : Assertion :=
  legStableAmbient loadPtr lenW innerW endPtr
      (regionBase + BitVec.ofNat 64 absOff) **
    leg3CommonAmbient regionBase bs **
    (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len)

def leg3OkConcreteAmbient (loadPtr regionBase lenW innerW endPtr next len : Word)
    (bs : List (BitVec 8)) (absOff : Nat) : Assertion :=
  leg3OkRegsAmbient loadPtr regionBase lenW innerW endPtr next len bs absOff **
    ⌜rlpItemDecode bs absOff (regionBase + BitVec.ofNat 64 absOff)
      endPtr next len⌝

set_option maxRecDepth 8000 in
theorem extractTypeBranchLegacy_framed_ambient
    (loadPtr regionBase lenW innerW cursor endPtr : Word)
    (bs : List (BitVec 8)) :
    cpsTripleWithin (1 + 1) AfterSaveCursor LegacyStart extractLinkedCode
      (afterSaveFrameTyAmbient loadPtr regionBase lenW (0 : Word) innerW
          cursor endPtr bs **
        (.x20 ↦ᵣ (0 : Word)) ** regOwn .x5 ** (.x0 ↦ᵣ (0 : Word)))
      (afterSaveFrameTyAmbient loadPtr regionBase lenW (0 : Word) innerW
          cursor endPtr bs **
        (.x20 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) := by
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ h => h)
    (cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x5)
      (P := afterSaveFrameTyAmbient loadPtr regionBase lenW (0 : Word) innerW
          cursor endPtr bs **
        (.x20 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)))
      (fun t0Old => ?_))
  have h := extractTypeBranchLegacy t0Old
  have hF := cpsTripleWithin_frameR
    (afterSaveFrameTyAmbient loadPtr regionBase lenW (0 : Word) innerW
      cursor endPtr bs)
    (by unfold afterSaveFrameTyAmbient; pcf) h
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hF

set_option maxRecDepth 8000 in
theorem extractLegacyLoadArgs_framed_ambient
    (loadPtr regionBase lenW innerW cursor endPtr : Word)
    (bs : List (BitVec 8)) :
    cpsTripleWithin (1 + 1) LegacyStart LegacyWalk0JalPc extractLinkedCode
      (legacyStartFrameAmbient loadPtr regionBase lenW innerW cursor endPtr bs)
      (legacyStartFrameAmbient loadPtr regionBase lenW innerW cursor endPtr bs) := by
  have h := extractLegacyLoadArgs cursor endPtr cursor endPtr
  have hF := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
      (TeaTypeAddr ↦ₘ (0 : Word)) ** (TeaInnerAddr ↦ₘ innerW) **
      regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
      regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
      regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkWalkInit) **
      bytesRegion regionBase bs **
      (.x12 ↦ᵣ (0 : Word)) **
      (.x20 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)))
    (by pcf) h
  refine cpsTripleWithin_weaken (fun _ hp => by
    simp only [legacyStartFrameAmbient, afterSaveFrameTyAmbient] at hp ⊢
    xperm_hyp hp) (fun _ hq => by
    simp only [legacyStartFrameAmbient, afterSaveFrameTyAmbient] at hq ⊢
    xperm_hyp hq) hF

#print axioms extractTypeBranchLegacy_framed_ambient
#print axioms extractLegacyLoadArgs_framed_ambient

end EvmAsm.Codegen.TxExtractToAddressSpec
