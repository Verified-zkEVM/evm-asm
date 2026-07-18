/-
  Ambient dual of TopT1 frames (split loadPtr / regionBase).
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Codegen.Programs.TxExtractToAddressT1Walk
import EvmAsm.Codegen.Programs.TxExtractToAddressTopT1
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

/-- T1 start frame ambient (type=0 after branch). -/
def t1StartFrameAmbient (loadPtr regionBase lenW innerW cursor endPtr : Word)
    (bs : List (BitVec 8)) : Assertion :=
  afterSaveFrameTyAmbient loadPtr regionBase lenW (1 : Word) innerW
      cursor endPtr bs **
    (.x20 ↦ᵣ (1 : Word)) ** (.x5 ↦ᵣ (1 : Word)) ** (.x0 ↦ᵣ (0 : Word))

/-- Stable ambient for t1 walks: x8=loadPtr; s5/s6 hold cursor/end. -/
def t1StableAmbient (loadPtr lenW innerW endPtr cursor : Word) : Assertion :=
  (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
    (TeaTypeAddr ↦ₘ (1 : Word)) ** (TeaInnerAddr ↦ₘ innerW) **
    regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
    (.x20 ↦ᵣ (1 : Word)) **
    (.x21 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr)

theorem t1StableAmbient_pcFree (loadPtr lenW innerW endPtr cursor : Word) :
    (t1StableAmbient loadPtr lenW innerW endPtr cursor).pcFree := by
  unfold t1StableAmbient; pcf

def t10CommonAmbient (regionBase : Word) (bs : List (BitVec 8)) : Assertion :=
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
    regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkT1Walk0) **
    bytesRegion regionBase bs

def t11CommonAmbient (regionBase : Word) (bs : List (BitVec 8)) : Assertion :=
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
    regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkT1Walk1) **
    bytesRegion regionBase bs

def t12CommonAmbient (regionBase : Word) (bs : List (BitVec 8)) : Assertion :=
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
    regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkT1Walk2) **
    bytesRegion regionBase bs

def t13CommonAmbient (regionBase : Word) (bs : List (BitVec 8)) : Assertion :=
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
    regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkT1Walk3) **
    bytesRegion regionBase bs

def t10OkRegsAmbient (loadPtr regionBase lenW innerW endPtr next len : Word)
    (bs : List (BitVec 8)) (absOff : Nat) : Assertion :=
  t1StableAmbient loadPtr lenW innerW endPtr
      (regionBase + BitVec.ofNat 64 absOff) **
    t10CommonAmbient regionBase bs **
    (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len)

def t10OkConcreteAmbient (loadPtr regionBase lenW innerW endPtr next len : Word)
    (bs : List (BitVec 8)) (absOff : Nat) : Assertion :=
  t10OkRegsAmbient loadPtr regionBase lenW innerW endPtr next len bs absOff **
    ⌜rlpItemDecode bs absOff (regionBase + BitVec.ofNat 64 absOff)
      endPtr next len⌝

def t11OkRegsAmbient (loadPtr regionBase lenW innerW endPtr next len : Word)
    (bs : List (BitVec 8)) (absOff : Nat) : Assertion :=
  t1StableAmbient loadPtr lenW innerW endPtr
      (regionBase + BitVec.ofNat 64 absOff) **
    t11CommonAmbient regionBase bs **
    (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len)

def t11OkConcreteAmbient (loadPtr regionBase lenW innerW endPtr next len : Word)
    (bs : List (BitVec 8)) (absOff : Nat) : Assertion :=
  t11OkRegsAmbient loadPtr regionBase lenW innerW endPtr next len bs absOff **
    ⌜rlpItemDecode bs absOff (regionBase + BitVec.ofNat 64 absOff)
      endPtr next len⌝

def t12OkRegsAmbient (loadPtr regionBase lenW innerW endPtr next len : Word)
    (bs : List (BitVec 8)) (absOff : Nat) : Assertion :=
  t1StableAmbient loadPtr lenW innerW endPtr
      (regionBase + BitVec.ofNat 64 absOff) **
    t12CommonAmbient regionBase bs **
    (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len)

def t12OkConcreteAmbient (loadPtr regionBase lenW innerW endPtr next len : Word)
    (bs : List (BitVec 8)) (absOff : Nat) : Assertion :=
  t12OkRegsAmbient loadPtr regionBase lenW innerW endPtr next len bs absOff **
    ⌜rlpItemDecode bs absOff (regionBase + BitVec.ofNat 64 absOff)
      endPtr next len⌝

def t13OkRegsAmbient (loadPtr regionBase lenW innerW endPtr next len : Word)
    (bs : List (BitVec 8)) (absOff : Nat) : Assertion :=
  t1StableAmbient loadPtr lenW innerW endPtr
      (regionBase + BitVec.ofNat 64 absOff) **
    t13CommonAmbient regionBase bs **
    (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len)

def t13OkConcreteAmbient (loadPtr regionBase lenW innerW endPtr next len : Word)
    (bs : List (BitVec 8)) (absOff : Nat) : Assertion :=
  t13OkRegsAmbient loadPtr regionBase lenW innerW endPtr next len bs absOff **
    ⌜rlpItemDecode bs absOff (regionBase + BitVec.ofNat 64 absOff)
      endPtr next len⌝


def t14CommonAmbient (regionBase : Word) (bs : List (BitVec 8)) : Assertion :=
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
    regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkT1Walk4) **
    bytesRegion regionBase bs

def t14OkRegsAmbient (loadPtr regionBase lenW innerW endPtr next len : Word)
    (bs : List (BitVec 8)) (absOff : Nat) : Assertion :=
  t1StableAmbient loadPtr lenW innerW endPtr
      (regionBase + BitVec.ofNat 64 absOff) **
    t14CommonAmbient regionBase bs **
    (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len)

def t14OkConcreteAmbient (loadPtr regionBase lenW innerW endPtr next len : Word)
    (bs : List (BitVec 8)) (absOff : Nat) : Assertion :=
  t14OkRegsAmbient loadPtr regionBase lenW innerW endPtr next len bs absOff **
    ⌜rlpItemDecode bs absOff (regionBase + BitVec.ofNat 64 absOff)
      endPtr next len⌝

set_option maxRecDepth 8000 in
theorem extractTypeBranchT1_framed_ambient
    (loadPtr regionBase lenW innerW cursor endPtr : Word)
    (bs : List (BitVec 8)) :
    cpsTripleWithin (1 + (1 + (1 + 1))) AfterSaveCursor T1Start extractLinkedCode
      (afterSaveFrameTyAmbient loadPtr regionBase lenW (1 : Word) innerW
          cursor endPtr bs **
        (.x20 ↦ᵣ (1 : Word)) ** regOwn .x5 ** (.x0 ↦ᵣ (0 : Word)))
      (afterSaveFrameTyAmbient loadPtr regionBase lenW (1 : Word) innerW
          cursor endPtr bs **
        (.x20 ↦ᵣ (1 : Word)) ** (.x5 ↦ᵣ (1 : Word)) ** (.x0 ↦ᵣ (0 : Word))) := by
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ h => h)
    (cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x5)
      (P := afterSaveFrameTyAmbient loadPtr regionBase lenW (1 : Word) innerW
          cursor endPtr bs **
        (.x20 ↦ᵣ (1 : Word)) ** (.x0 ↦ᵣ (0 : Word)))
      (fun t0Old => ?_))
  have h := extractTypeBranchT1 t0Old
  have hF := cpsTripleWithin_frameR
    (afterSaveFrameTyAmbient loadPtr regionBase lenW (1 : Word) innerW
      cursor endPtr bs)
    (by unfold afterSaveFrameTyAmbient; pcf) h
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hF

set_option maxRecDepth 8000 in
theorem extractT1LoadArgs_framed_ambient
    (loadPtr regionBase lenW innerW cursor endPtr : Word)
    (bs : List (BitVec 8)) :
    cpsTripleWithin (1 + 1) T1Start T1Walk0JalPc extractLinkedCode
      (t1StartFrameAmbient loadPtr regionBase lenW innerW cursor endPtr bs)
      (t1StartFrameAmbient loadPtr regionBase lenW innerW cursor endPtr bs) := by
  have h := extractT1LoadArgs cursor endPtr cursor endPtr
  have hF := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
      (TeaTypeAddr ↦ₘ (1 : Word)) ** (TeaInnerAddr ↦ₘ innerW) **
      regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
      regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
      regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkWalkInit) **
      bytesRegion regionBase bs **
      (.x12 ↦ᵣ (0 : Word)) **
      (.x20 ↦ᵣ (1 : Word)) ** (.x5 ↦ᵣ (1 : Word)) ** (.x0 ↦ᵣ (0 : Word)))
    (by pcf) h
  refine cpsTripleWithin_weaken (fun _ hp => by
    simp only [t1StartFrameAmbient, afterSaveFrameTyAmbient] at hp ⊢
    xperm_hyp hp) (fun _ hq => by
    simp only [t1StartFrameAmbient, afterSaveFrameTyAmbient] at hq ⊢
    xperm_hyp hq) hF

#print axioms extractTypeBranchT1_framed_ambient
#print axioms extractT1LoadArgs_framed_ambient

end EvmAsm.Codegen.TxExtractToAddressSpec
