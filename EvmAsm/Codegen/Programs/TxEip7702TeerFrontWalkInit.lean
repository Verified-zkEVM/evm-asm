/-
  Teer front short walk_init under applied prest.
  AtWalkInit → AfterWalkInitSave (E→AfterWalkInitSave compose).
-/

import EvmAsm.Codegen.Programs.TxEip7702TeerFrontType4
import EvmAsm.Codegen.Programs.TxEip7702TeerWalkInit
import EvmAsm.Codegen.Programs.TxTypeDispatchAmbient
import EvmAsm.Codegen.Programs.TxIntrinsicStateGasSpec
import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SAsm.MeasureLoop
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.SAsm.AbiFrameCall
import EvmAsm.Rv64.Tactics.XSimp

namespace EvmAsm.Codegen.TxEip7702TeerSpec

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
open EvmAsm.Codegen.BlockVerdictTxStateGasArraySpec
open EvmAsm.Codegen.TxTypeDispatchSpec
  (teerTxTypeDispatch txSlice ambientAbsOff loadPtr_add_rel_eq)
open EvmAsm.Codegen.TxIntrinsicStateGasSpec (nTypeSteps)

private abbrev nFrontToWalkInit : Nat :=
  (34 + (6 + (1 + nTypeSteps) + 1)) + (5 + 7)

private abbrev nWalkInitShort : Nat := 1 + 15 + 1 + 2

/-- Ambient through walk_init (no x24/x25 — body saves s8/s9). -/
def teerWalkInitAmbient
    (spC loadPtr lenW balPtr balLenW chainIdW
      s7 s11 spVal : Word)
    (balBytes : List (BitVec 8)) (s : TeerSaved)
    (innerVal : Word) : Assertion :=
  (.x2 ↦ᵣ spC) **
  (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
  (.x18 ↦ᵣ balPtr) ** (.x19 ↦ᵣ balLenW) ** (.x20 ↦ᵣ chainIdW) **
  (.x21 ↦ᵣ loadPtr + innerVal) ** (.x22 ↦ᵣ lenW - innerVal) **
  (.x23 ↦ᵣ s7) **
  (.x26 ↦ᵣ (0 : Word)) **
  (.x27 ↦ᵣ s11) **
  frameSlotsSaved teerFrame spC (teerSavedVals s) **
  (TypeAddr ↦ₘ (4 : Word)) ** (InnerOffAddr ↦ₘ innerVal) **
  regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
  stackFree spVal 6 **
  bytesRegion balPtr balBytes **
  teerScratchWithoutTypeOwn

private theorem pcFree_teerWalkInitAmbient
    (spC loadPtr lenW balPtr balLenW chainIdW
      s7 s11 spVal : Word)
    (balBytes : List (BitVec 8)) (s : TeerSaved)
    (innerVal : Word) :
    (teerWalkInitAmbient spC loadPtr lenW balPtr balLenW chainIdW
      s7 s11 spVal balBytes s innerVal).pcFree := by
  unfold teerWalkInitAmbient; pcf

/-- Core walk_init prest atoms excl temps lifted to regOwn. -/
def teerWalkInitBodyCore
    (listBase listLen : Word) (bs : List (BitVec 8)) (listOff : Nat)
    (old1 v24 v25 t0 t1 t2 : Word) : Assertion :=
  (.x1 ↦ᵣ old1) ** (.x24 ↦ᵣ v24) ** (.x25 ↦ᵣ v25) **
  (.x10 ↦ᵣ (listBase + BitVec.ofNat 64 listOff)) ** (.x11 ↦ᵣ listLen) **
  (.x5 ↦ᵣ t0) ** (.x6 ↦ᵣ t1) ** (.x7 ↦ᵣ t2) **
  (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs

/-- Short walk_init post: cursors + s8/s9; all temps regOwn. -/
def teerWalkInitBodyPost
    (listBase listLen : Word) (bs : List (BitVec 8)) (listOff : Nat) : Assertion :=
  (.x1 ↦ᵣ LinkWalkInit) **
    (.x10 ↦ᵣ (listBase + BitVec.ofNat 64 listOff + signExtend12 (1 : BitVec 12))) **
    (.x11 ↦ᵣ (listBase + BitVec.ofNat 64 listOff + listLen)) **
    (.x12 ↦ᵣ (0 : Word)) **
    (.x24 ↦ᵣ (listBase + BitVec.ofNat 64 listOff + signExtend12 (1 : BitVec 12))) **
    (.x25 ↦ᵣ (listBase + BitVec.ofNat 64 listOff + listLen)) **
    regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
    regOwn .x30 ** regOwn .x31 **
    (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs

set_option maxRecDepth 8000 in
/-- Short walk_init with regOwn temps x12/x28/x29/x30/x31. -/
theorem teerWalkInitShortSuccess_ownTemps
    (listBase listLen t0 t1 t2 : Word)
    (bs : List (BitVec 8)) (listOff : Nat) (old1 v24 v25 : Word)
    (hsalign : listBase.toNat % 8 = 0)
    (hoff : listOff < bs.length)
    (hover : listBase.toNat + listOff < 2 ^ 64)
    (hvalid : isValidByteAccess (listBase + BitVec.ofNat 64 listOff) = true)
    (hlen : listLen ≠ (0 : Word))
    (h_ge : ¬ BitVec.ult ((bs[listOff]'hoff).zeroExtend 64) (0xc0 : Word) = true)
    (h_hi : BitVec.ult ((bs[listOff]'hoff).zeroExtend 64) (0xf8 : Word) = true)
    (h_exact : (listBase + BitVec.ofNat 64 listOff) +
        (((bs[listOff]'hoff).zeroExtend 64 - (0xc0 : Word)) +
          signExtend12 (1 : BitVec 12)) =
      (listBase + BitVec.ofNat 64 listOff) + listLen) :
    cpsTripleWithin nWalkInitShort AtWalkInit AfterWalkInitSave teerLinkedEarly
      (teerWalkInitBodyCore listBase listLen bs listOff old1 v24 v25 t0 t1 t2 **
        regOwn .x12 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
      (teerWalkInitBodyPost listBase listLen bs listOff) := by
  have hcore (a2 t3 t4 t5 t6 : Word) :
      cpsTripleWithin nWalkInitShort AtWalkInit AfterWalkInitSave teerLinkedEarly
        ((.x1 ↦ᵣ old1) ** (.x24 ↦ᵣ v24) ** (.x25 ↦ᵣ v25) **
          teerWalkInitPrest listBase listLen a2 t0 t1 t2 t3 t4 t5 t6 bs listOff)
        (teerWalkInitBodyPost listBase listLen bs listOff) := by
    have h0 := teerWalkInitShortSuccess listBase listLen a2 t0 t1 t2 t3 t4 t5 t6
      bs listOff old1 v24 v25 hsalign hoff hover hvalid hlen h_ge h_hi h_exact
    refine cpsTripleWithin_weaken (fun _ hp => hp) (fun s hq => ?_) h0
    -- Post: mono x30/x31 regIs→regOwn into BodyPost
    unfold teerWalkInitBodyPost
    have hq1 :
        ((.x30 ↦ᵣ t5) ** (.x31 ↦ᵣ t6) **
          ((.x1 ↦ᵣ LinkWalkInit) **
            (.x10 ↦ᵣ (listBase + BitVec.ofNat 64 listOff + signExtend12 1)) **
            (.x11 ↦ᵣ (listBase + BitVec.ofNat 64 listOff + listLen)) **
            (.x12 ↦ᵣ (0 : Word)) **
            (.x24 ↦ᵣ (listBase + BitVec.ofNat 64 listOff + signExtend12 1)) **
            (.x25 ↦ᵣ (listBase + BitVec.ofNat 64 listOff + listLen)) **
            regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
            regOwn .x29 ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs)) s := by
      xperm_hyp hq
    have hq2 :=
      (sepConj_mono (regIs_implies_regOwn .x30)
        (sepConj_mono (regIs_implies_regOwn .x31) (fun _ h => h))) s hq1
    xperm_hyp hq2
  -- Align prest to BodyCore ** concrete temps
  have hcore' (a2 t3 t4 t5 t6 : Word) :
      cpsTripleWithin nWalkInitShort AtWalkInit AfterWalkInitSave teerLinkedEarly
        (teerWalkInitBodyCore listBase listLen bs listOff old1 v24 v25 t0 t1 t2 **
          (.x12 ↦ᵣ a2) ** (.x28 ↦ᵣ t3) ** (.x29 ↦ᵣ t4) **
          (.x30 ↦ᵣ t5) ** (.x31 ↦ᵣ t6))
        (teerWalkInitBodyPost listBase listLen bs listOff) := by
    refine cpsTripleWithin_weaken (fun s hp => ?_) (fun _ hq => hq)
      (hcore a2 t3 t4 t5 t6)
    unfold teerWalkInitBodyCore at hp
    unfold teerWalkInitPrest
    xperm_hyp hp
  -- Lift x30,x31
  have h3031 (a2 t3 t4 : Word) :
      cpsTripleWithin nWalkInitShort AtWalkInit AfterWalkInitSave teerLinkedEarly
        (teerWalkInitBodyCore listBase listLen bs listOff old1 v24 v25 t0 t1 t2 **
          (.x12 ↦ᵣ a2) ** (.x28 ↦ᵣ t3) ** (.x29 ↦ᵣ t4) **
          regOwn .x30 ** regOwn .x31)
        (teerWalkInitBodyPost listBase listLen bs listOff) := by
    have h := cpsTripleWithin_of_forall_regIs_to_regOwn2
      (r1 := .x30) (r2 := .x31)
      (P := teerWalkInitBodyCore listBase listLen bs listOff old1 v24 v25 t0 t1 t2 **
        (.x12 ↦ᵣ a2) ** (.x28 ↦ᵣ t3) ** (.x29 ↦ᵣ t4))
      (fun t5 t6 =>
        cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
          (fun _ hq => hq) (hcore' a2 t3 t4 t5 t6))
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => hq) h
  -- Lift x28,x29
  have h2829 (a2 : Word) :
      cpsTripleWithin nWalkInitShort AtWalkInit AfterWalkInitSave teerLinkedEarly
        (teerWalkInitBodyCore listBase listLen bs listOff old1 v24 v25 t0 t1 t2 **
          (.x12 ↦ᵣ a2) **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
        (teerWalkInitBodyPost listBase listLen bs listOff) := by
    have h := cpsTripleWithin_of_forall_regIs_to_regOwn2
      (r1 := .x28) (r2 := .x29)
      (P := teerWalkInitBodyCore listBase listLen bs listOff old1 v24 v25 t0 t1 t2 **
        (.x12 ↦ᵣ a2) ** regOwn .x30 ** regOwn .x31)
      (fun t3 t4 =>
        cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
          (fun _ hq => hq) (h3031 a2 t3 t4))
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => hq) h
  -- Lift x12
  have h := cpsTripleWithin_of_forall_regIs_to_regOwn
    (r := .x12)
    (P := teerWalkInitBodyCore listBase listLen bs listOff old1 v24 v25 t0 t1 t2 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
    (fun a2 =>
      cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
        (fun _ hq => hq) (h2829 a2))
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => hq) h

/-- Focus = ownTemps prest (listBase=regionBase). -/
def teerWalkInitFocus
    (listBase listLen : Word) (bs : List (BitVec 8)) (listOff : Nat)
    (old1 v24 v25 t0 t1 t2 : Word) : Assertion :=
  teerWalkInitBodyCore listBase listLen bs listOff old1 v24 v25 t0 t1 t2 **
    regOwn .x12 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31

/-- Type4-applied AtWalkInit post → walk_init focus ** ambient. -/
theorem teerAtWalkInitFlat_to_walkInitPre
    (spC loadPtr lenW balPtr balLenW chainIdW
      s7 s8 s9 s11 spVal regionBase : Word)
    (bs balBytes : List (BitVec 8)) (s : TeerSaved)
    (innerVal : Word)
    (listOff : Nat)
    (ha0 : loadPtr + innerVal = regionBase + BitVec.ofNat 64 listOff) :
    ∀ h,
      ((.x2 ↦ᵣ spC) **
        (.x1 ↦ᵣ LinkType) **
        (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
        (.x18 ↦ᵣ balPtr) ** (.x19 ↦ᵣ balLenW) ** (.x20 ↦ᵣ chainIdW) **
        (.x21 ↦ᵣ loadPtr + innerVal) ** (.x22 ↦ᵣ lenW - innerVal) **
        (.x23 ↦ᵣ s7) ** (.x24 ↦ᵣ s8) ** (.x25 ↦ᵣ s9) **
        (.x26 ↦ᵣ (0 : Word)) **
        (.x27 ↦ᵣ s11) **
        frameSlotsSaved teerFrame spC (teerSavedVals s) **
        (.x5 ↦ᵣ InnerOffAddr) ** (.x6 ↦ᵣ innerVal) ** (.x7 ↦ᵣ (4 : Word)) **
        (.x10 ↦ᵣ loadPtr + innerVal) ** (.x11 ↦ᵣ lenW - innerVal) **
        (.x0 ↦ᵣ (0 : Word)) **
        (TypeAddr ↦ₘ (4 : Word)) ** (InnerOffAddr ↦ₘ innerVal) **
        regOwn .x12 ** regOwn .x13 ** regOwn .x14 ** regOwn .x15 **
        regOwn .x16 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        stackFree spVal 6 **
        bytesRegion regionBase bs ** bytesRegion balPtr balBytes **
        teerScratchWithoutTypeOwn) h →
      (teerWalkInitFocus regionBase (lenW - innerVal) bs listOff
          LinkType s8 s9 InnerOffAddr innerVal (4 : Word) **
        teerWalkInitAmbient spC loadPtr lenW balPtr balLenW chainIdW
          s7 s11 spVal balBytes s innerVal) h := by
  intro _ hp
  unfold teerWalkInitFocus teerWalkInitBodyCore teerWalkInitAmbient
  -- rewrite a0 via ha0 (focus wants regionBase+listOff)
  simp only [ha0] at hp ⊢
  xperm_hyp hp

/-- Nested post = (BodyPost ** ambient). -/
def teerWalkInitPostNested
    (spC loadPtr lenW balPtr balLenW chainIdW
      s7 s11 spVal regionBase : Word)
    (bs balBytes : List (BitVec 8)) (s : TeerSaved)
    (innerVal : Word) (listOff : Nat) : Assertion :=
  (teerWalkInitBodyPost regionBase (lenW - innerVal) bs listOff **
    teerWalkInitAmbient spC loadPtr lenW balPtr balLenW chainIdW
      s7 s11 spVal balBytes s innerVal)

set_option maxRecDepth 8000 in
/-- E → AfterWalkInitSave under applied prest (short outer list). -/
theorem teerWalkInitShort_applied_nested
    (ret spVal spC loadPtr lenW balPtr balLenW chainIdW baiW : Word)
    (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : Word)
    (regionBase : Word) (bs balBytes : List (BitVec 8)) (off len : Nat)
    (hspC : spC = spVal + signExtend12 (-160 : BitVec 12))
    (hnez : balPtr ≠ (0 : Word))
    (hptr : loadPtr = regionBase + BitVec.ofNat 64 off)
    (hlenW : lenW = BitVec.ofNat 64 len)
    (hsuccess : (teerTxTypeDispatch (txSlice bs off len)).1 = (0 : Word))
    (htype4 : (teerTxTypeDispatch (txSlice bs off len)).2.1 = (4 : Word))
    (halign : regionBase.toNat % 8 = 0)
    (hbound : off + len ≤ bs.length)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hvalid0 : isValidByteAccess (regionBase + BitVec.ofNat 64 off) = true)
    -- short walk_init guards on abs list head
    (listOff : Nat)
    (ha0 : loadPtr + (teerTxTypeDispatch (txSlice bs off len)).2.2 =
      regionBase + BitVec.ofNat 64 listOff)
    (hoff : listOff < bs.length)
    (hoverL : regionBase.toNat + listOff < 2 ^ 64)
    (hvalidL : isValidByteAccess (regionBase + BitVec.ofNat 64 listOff) = true)
    (hlenL : lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2 ≠ (0 : Word))
    (h_ge : ¬ BitVec.ult ((bs[listOff]'hoff).zeroExtend 64) (0xc0 : Word) = true)
    (h_hi : BitVec.ult ((bs[listOff]'hoff).zeroExtend 64) (0xf8 : Word) = true)
    (h_exact : (regionBase + BitVec.ofNat 64 listOff) +
        (((bs[listOff]'hoff).zeroExtend 64 - (0xc0 : Word)) +
          signExtend12 (1 : BitVec 12)) =
      (regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) :
    let s : TeerSaved :=
      { ra := ret, s0 := s0, s1 := s1, s2 := s2, s3 := s3, s4 := s4
        s5 := s5, s6 := s6, s7 := s7, s8 := s8, s9 := s9
        s10 := s10, s11 := s11, a5 := baiW }
    let innerVal := (teerTxTypeDispatch (txSlice bs off len)).2.2
    cpsTripleWithin (nFrontToWalkInit + nWalkInitShort)
      E AfterWalkInitSave teerLinkedEarly
      ((.x1 ↦ᵣ ret) ** (.x2 ↦ᵣ spVal) **
        stackFree spVal nTeerStackDwords **
        (.x8 ↦ᵣ s0) ** (.x9 ↦ᵣ s1) **
        (.x18 ↦ᵣ s2) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) **
        (.x21 ↦ᵣ s5) ** (.x22 ↦ᵣ s6) ** (.x23 ↦ᵣ s7) **
        (.x24 ↦ᵣ s8) ** (.x25 ↦ᵣ s9) ** (.x26 ↦ᵣ s10) **
        (.x27 ↦ᵣ s11) **
        (.x10 ↦ᵣ loadPtr) ** (.x11 ↦ᵣ lenW) **
        (.x12 ↦ᵣ balPtr) ** (.x13 ↦ᵣ balLenW) **
        (.x14 ↦ᵣ chainIdW) ** (.x15 ↦ᵣ baiW) **
        bytesRegion regionBase bs ** bytesRegion balPtr balBytes **
        teerScratchOwn **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x16 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
        regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)))
      (teerWalkInitPostNested spC loadPtr lenW balPtr balLenW chainIdW
        s7 s11 spVal regionBase bs balBytes s innerVal listOff) := by
  intro s innerVal
  have hty := teerType4ThenInner_applied ret spVal spC loadPtr lenW
    balPtr balLenW chainIdW baiW s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    regionBase bs balBytes off len hspC hnez hptr hlenW hsuccess htype4
    halign hbound hover hvalid0
  have hwi := teerWalkInitShortSuccess_ownTemps regionBase
    (lenW - innerVal) InnerOffAddr innerVal (4 : Word) bs listOff
    LinkType s8 s9
    (by simpa using halign) hoff hoverL hvalidL hlenL h_ge h_hi h_exact
  have hwiF := cpsTripleWithin_frameR
    (teerWalkInitAmbient spC loadPtr lenW balPtr balLenW chainIdW
      s7 s11 spVal balBytes s innerVal)
    (by exact pcFree_teerWalkInitAmbient _ _ _ _ _ _ _ _ _ _ _ _) hwi
  have hwiF' :
      cpsTripleWithin nWalkInitShort AtWalkInit AfterWalkInitSave teerLinkedEarly
        (teerWalkInitFocus regionBase (lenW - innerVal) bs listOff
            LinkType s8 s9 InnerOffAddr innerVal (4 : Word) **
          teerWalkInitAmbient spC loadPtr lenW balPtr balLenW chainIdW
            s7 s11 spVal balBytes s innerVal)
        (teerWalkInitPostNested spC loadPtr lenW balPtr balLenW chainIdW
          s7 s11 spVal regionBase bs balBytes s innerVal listOff) := by
    exact cpsTripleWithin_weaken
      (fun _ hp => by
        unfold teerWalkInitFocus at hp
        xperm_hyp hp)
      (fun _ hq => by
        unfold teerWalkInitPostNested
        exact hq)
      hwiF
  have hsc := teerAtWalkInitFlat_to_walkInitPre spC loadPtr lenW balPtr
    balLenW chainIdW s7 s8 s9 s11 spVal regionBase bs balBytes s
    innerVal listOff ha0
  have hseq := cpsTripleWithin_seq_perm_same_cr hsc hty hwiF'
  exact cpsTripleWithin_mono_nSteps
    (by decide : nFrontToWalkInit + nWalkInitShort ≤ nFrontToWalkInit + nWalkInitShort)
    hseq

set_option maxRecDepth 8000 in
/-- Flatten nested → applied-style AfterWalkInitSave post. -/
theorem teerWalkInitShort_applied
    (ret spVal spC loadPtr lenW balPtr balLenW chainIdW baiW : Word)
    (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : Word)
    (regionBase : Word) (bs balBytes : List (BitVec 8)) (off len : Nat)
    (hspC : spC = spVal + signExtend12 (-160 : BitVec 12))
    (hnez : balPtr ≠ (0 : Word))
    (hptr : loadPtr = regionBase + BitVec.ofNat 64 off)
    (hlenW : lenW = BitVec.ofNat 64 len)
    (hsuccess : (teerTxTypeDispatch (txSlice bs off len)).1 = (0 : Word))
    (htype4 : (teerTxTypeDispatch (txSlice bs off len)).2.1 = (4 : Word))
    (halign : regionBase.toNat % 8 = 0)
    (hbound : off + len ≤ bs.length)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hvalid0 : isValidByteAccess (regionBase + BitVec.ofNat 64 off) = true)
    (listOff : Nat)
    (ha0 : loadPtr + (teerTxTypeDispatch (txSlice bs off len)).2.2 =
      regionBase + BitVec.ofNat 64 listOff)
    (hoff : listOff < bs.length)
    (hoverL : regionBase.toNat + listOff < 2 ^ 64)
    (hvalidL : isValidByteAccess (regionBase + BitVec.ofNat 64 listOff) = true)
    (hlenL : lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2 ≠ (0 : Word))
    (h_ge : ¬ BitVec.ult ((bs[listOff]'hoff).zeroExtend 64) (0xc0 : Word) = true)
    (h_hi : BitVec.ult ((bs[listOff]'hoff).zeroExtend 64) (0xf8 : Word) = true)
    (h_exact : (regionBase + BitVec.ofNat 64 listOff) +
        (((bs[listOff]'hoff).zeroExtend 64 - (0xc0 : Word)) +
          signExtend12 (1 : BitVec 12)) =
      (regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) :
    let s : TeerSaved :=
      { ra := ret, s0 := s0, s1 := s1, s2 := s2, s3 := s3, s4 := s4
        s5 := s5, s6 := s6, s7 := s7, s8 := s8, s9 := s9
        s10 := s10, s11 := s11, a5 := baiW }
    let innerVal := (teerTxTypeDispatch (txSlice bs off len)).2.2
    let cur := (regionBase + BitVec.ofNat 64 listOff) + signExtend12 (1 : BitVec 12)
    let endW := (regionBase + BitVec.ofNat 64 listOff) + (lenW - innerVal)
    cpsTripleWithin (nFrontToWalkInit + nWalkInitShort)
      E AfterWalkInitSave teerLinkedEarly
      ((.x1 ↦ᵣ ret) ** (.x2 ↦ᵣ spVal) **
        stackFree spVal nTeerStackDwords **
        (.x8 ↦ᵣ s0) ** (.x9 ↦ᵣ s1) **
        (.x18 ↦ᵣ s2) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) **
        (.x21 ↦ᵣ s5) ** (.x22 ↦ᵣ s6) ** (.x23 ↦ᵣ s7) **
        (.x24 ↦ᵣ s8) ** (.x25 ↦ᵣ s9) ** (.x26 ↦ᵣ s10) **
        (.x27 ↦ᵣ s11) **
        (.x10 ↦ᵣ loadPtr) ** (.x11 ↦ᵣ lenW) **
        (.x12 ↦ᵣ balPtr) ** (.x13 ↦ᵣ balLenW) **
        (.x14 ↦ᵣ chainIdW) ** (.x15 ↦ᵣ baiW) **
        bytesRegion regionBase bs ** bytesRegion balPtr balBytes **
        teerScratchOwn **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x16 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
        regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)))
      ((.x2 ↦ᵣ spC) **
        (.x1 ↦ᵣ LinkWalkInit) **
        (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
        (.x18 ↦ᵣ balPtr) ** (.x19 ↦ᵣ balLenW) ** (.x20 ↦ᵣ chainIdW) **
        (.x21 ↦ᵣ loadPtr + innerVal) ** (.x22 ↦ᵣ lenW - innerVal) **
        (.x23 ↦ᵣ s7) **
        (.x10 ↦ᵣ cur) ** (.x11 ↦ᵣ endW) **
        (.x12 ↦ᵣ (0 : Word)) ** (.x24 ↦ᵣ cur) ** (.x25 ↦ᵣ endW) **
        (.x26 ↦ᵣ (0 : Word)) **
        (.x27 ↦ᵣ s11) **
        frameSlotsSaved teerFrame spC (teerSavedVals s) **
        (.x0 ↦ᵣ (0 : Word)) **
        (TypeAddr ↦ₘ (4 : Word)) ** (InnerOffAddr ↦ₘ innerVal) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        stackFree spVal 6 **
        bytesRegion regionBase bs ** bytesRegion balPtr balBytes **
        teerScratchWithoutTypeOwn) := by
  intro s innerVal cur endW
  have h0 := teerWalkInitShort_applied_nested ret spVal spC loadPtr lenW
    balPtr balLenW chainIdW baiW s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    regionBase bs balBytes off len hspC hnez hptr hlenW hsuccess htype4
    halign hbound hover hvalid0 listOff ha0 hoff hoverL hvalidL hlenL
    h_ge h_hi h_exact
  exact cpsTripleWithin_weaken (fun _ hp => hp)
    (fun _ hq => by
      unfold teerWalkInitPostNested teerWalkInitBodyPost teerWalkInitAmbient at hq
      xperm_hyp hq) h0

#print axioms teerWalkInitShortSuccess_ownTemps
#print axioms teerWalkInitShort_applied_nested
#print axioms teerWalkInitShort_applied

end EvmAsm.Codegen.TxEip7702TeerSpec
