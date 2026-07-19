/-
  Teer front first walk_next cycle under applied prest.
  E → AfterWalkNext0Save via WalkInit applied + CycleOk.
-/

import EvmAsm.Codegen.Programs.TxEip7702TeerFrontWalkInit
import EvmAsm.Codegen.Programs.TxEip7702TeerWalkNext0
import EvmAsm.Codegen.Programs.TxTypeDispatchAmbient
import EvmAsm.Codegen.Programs.TxIntrinsicStateGasSpec
import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SAsm.MeasureLoop
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.SAsm.AbiFrameCall
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.RLP.WalkNext

namespace EvmAsm.Codegen.TxEip7702TeerSpec

open EvmAsm.Rv64
open EvmAsm.Rv64.RLP
open EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
open EvmAsm.Codegen.BlockVerdictTxStateGasArraySpec
open EvmAsm.Codegen.TxTypeDispatchSpec
  (teerTxTypeDispatch txSlice ambientAbsOff loadPtr_add_rel_eq)
open EvmAsm.Codegen.TxIntrinsicStateGasSpec (nTypeSteps)

private abbrev nFrontToWalkInit : Nat :=
  (34 + (6 + (1 + nTypeSteps) + 1)) + (5 + 7)

private abbrev nWalkInitShort : Nat := 1 + 15 + 1 + 2

private abbrev nFrontToWalkInitSave : Nat :=
  nFrontToWalkInit + nWalkInitShort

private abbrev nWalkNext0Cycle : Nat := 2 + (1 + 87) + 1 + 1

private abbrev nFrontToWalkNext0Save : Nat :=
  nFrontToWalkInitSave + nWalkNext0Cycle

/-- CycleOk prest core (concrete a0/a1/a2; temps lifted separately). -/
def teerWalkNext0BodyCore
    (listBase : Word) (bs : List (BitVec 8))
    (old1 v24 v25 a0Old a1Old a2Old : Word) : Assertion :=
  (.x1 ↦ᵣ old1) ** (.x24 ↦ᵣ v24) ** (.x25 ↦ᵣ v25) **
    (.x10 ↦ᵣ a0Old) ** (.x11 ↦ᵣ a1Old) ** (.x12 ↦ᵣ a2Old) **
    (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs

/-- CycleOk post body (exists stripped). -/
def teerWalkNext0BodyPost
    (listBase endPtr next len : Word) (bs : List (BitVec 8))
    (srcOff : Nat) : Assertion :=
  (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
    (.x24 ↦ᵣ next) ** (.x25 ↦ᵣ endPtr) **
    (.x0 ↦ᵣ (0 : Word)) **
    regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
    regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkWalkNext0) **
    bytesRegion listBase bs **
    ⌜rlpItemDecode bs srcOff (listBase + BitVec.ofNat 64 srcOff) endPtr next len⌝

set_option maxRecDepth 8000 in
/-- CycleOk with regOwn temps x5–7,x28–31. -/
theorem teerWalkNext0CycleOk_ownTemps
    (listBase endPtr : Word) (bs : List (BitVec 8)) (srcOff : Nat)
    (old1 v24 v25 a0Old a1Old a2Old : Word)
    (hsalign : listBase.toNat % 8 = 0)
    (hoff : srcOff < bs.length)
    (hover : listBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (listBase + BitVec.ofNat 64 srcOff) = true)
    (hss : ¬ BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        srcOff + 1 < bs.length ∧ listBase.toNat + (srcOff + 1) < 2 ^ 64 ∧
          isValidByteAccess (listBase + BitVec.ofNat 64 (srcOff + 1)) = true)
    (hls : ¬ BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xc0 : Word) = true →
        srcOff + 1 + ((bs[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        listBase.toNat + (srcOff + 1 +
          ((bs[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (listBase + BitVec.ofNat 64 (srcOff + 1 + k)) = true)
    (hll : ¬ BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xf8 : Word) = true →
        srcOff + 1 + ((bs[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        listBase.toNat + (srcOff + 1 +
          ((bs[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (listBase + BitVec.ofNat 64 (srcOff + 1 + k)) = true)
    (hdec : ∃ next len : Word,
      rlpItemDecode bs srcOff (listBase + BitVec.ofNat 64 srcOff)
        endPtr next len)
    (hinb : BitVec.ult (listBase + BitVec.ofNat 64 srcOff) endPtr = true)
    (hcur : v24 = listBase + BitVec.ofNat 64 srcOff)
    (hend : v25 = endPtr) :
    cpsTripleWithin nWalkNext0Cycle AfterWalkInitSave AfterWalkNext0Save
      teerLinkedEarly
      (teerWalkNext0BodyCore listBase bs old1 v24 v25 a0Old a1Old a2Old **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
      (fun h => ∃ next len : Word,
        (teerWalkNext0BodyPost listBase endPtr next len bs srcOff) h) := by
  have hcore (t0 t1 t2 t3 t4 t5 t6 : Word) :
      cpsTripleWithin nWalkNext0Cycle AfterWalkInitSave AfterWalkNext0Save
        teerLinkedEarly
        (teerWalkNext0BodyCore listBase bs old1 v24 v25 a0Old a1Old a2Old **
          (.x5 ↦ᵣ t0) ** (.x6 ↦ᵣ t1) ** (.x7 ↦ᵣ t2) **
          (.x28 ↦ᵣ t3) ** (.x29 ↦ᵣ t4) ** (.x30 ↦ᵣ t5) ** (.x31 ↦ᵣ t6))
        (fun h => ∃ next len : Word,
          (teerWalkNext0BodyPost listBase endPtr next len bs srcOff) h) := by
    have h0 := teerWalkNext0CycleOk listBase endPtr a2Old t0 t1 t2 t3 t4 t5 t6
      bs srcOff old1 v24 v25 a0Old a1Old
      hsalign hoff hover hvalid hss hls hll hdec hinb hcur hend
    refine cpsTripleWithin_weaken (fun s hp => ?_) (fun h hq => by
      obtain ⟨next, len, hq'⟩ := hq
      exact ⟨next, len, by
        unfold teerWalkNext0BodyPost
        exact hq'⟩) h0
    unfold teerWalkNext0BodyCore at hp
    xperm_hyp hp
  -- Lift x30,x31
  have h3031 (t0 t1 t2 t3 t4 : Word) :
      cpsTripleWithin nWalkNext0Cycle AfterWalkInitSave AfterWalkNext0Save
        teerLinkedEarly
        (teerWalkNext0BodyCore listBase bs old1 v24 v25 a0Old a1Old a2Old **
          (.x5 ↦ᵣ t0) ** (.x6 ↦ᵣ t1) ** (.x7 ↦ᵣ t2) **
          (.x28 ↦ᵣ t3) ** (.x29 ↦ᵣ t4) **
          regOwn .x30 ** regOwn .x31)
        (fun h => ∃ next len : Word,
          (teerWalkNext0BodyPost listBase endPtr next len bs srcOff) h) := by
    have h := cpsTripleWithin_of_forall_regIs_to_regOwn2
      (r1 := .x30) (r2 := .x31)
      (P := teerWalkNext0BodyCore listBase bs old1 v24 v25 a0Old a1Old a2Old **
        (.x5 ↦ᵣ t0) ** (.x6 ↦ᵣ t1) ** (.x7 ↦ᵣ t2) **
        (.x28 ↦ᵣ t3) ** (.x29 ↦ᵣ t4))
      (fun t5 t6 =>
        cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
          (fun _ hq => hq) (hcore t0 t1 t2 t3 t4 t5 t6))
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => hq) h
  -- Lift x28,x29
  have h2829 (t0 t1 t2 : Word) :
      cpsTripleWithin nWalkNext0Cycle AfterWalkInitSave AfterWalkNext0Save
        teerLinkedEarly
        (teerWalkNext0BodyCore listBase bs old1 v24 v25 a0Old a1Old a2Old **
          (.x5 ↦ᵣ t0) ** (.x6 ↦ᵣ t1) ** (.x7 ↦ᵣ t2) **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
        (fun h => ∃ next len : Word,
          (teerWalkNext0BodyPost listBase endPtr next len bs srcOff) h) := by
    have h := cpsTripleWithin_of_forall_regIs_to_regOwn2
      (r1 := .x28) (r2 := .x29)
      (P := teerWalkNext0BodyCore listBase bs old1 v24 v25 a0Old a1Old a2Old **
        (.x5 ↦ᵣ t0) ** (.x6 ↦ᵣ t1) ** (.x7 ↦ᵣ t2) **
        regOwn .x30 ** regOwn .x31)
      (fun t3 t4 =>
        cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
          (fun _ hq => hq) (h3031 t0 t1 t2 t3 t4))
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => hq) h
  -- Lift x5,x6 then x7
  have h56 (t2 : Word) :
      cpsTripleWithin nWalkNext0Cycle AfterWalkInitSave AfterWalkNext0Save
        teerLinkedEarly
        (teerWalkNext0BodyCore listBase bs old1 v24 v25 a0Old a1Old a2Old **
          regOwn .x5 ** regOwn .x6 ** (.x7 ↦ᵣ t2) **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
        (fun h => ∃ next len : Word,
          (teerWalkNext0BodyPost listBase endPtr next len bs srcOff) h) := by
    have h := cpsTripleWithin_of_forall_regIs_to_regOwn2
      (r1 := .x5) (r2 := .x6)
      (P := teerWalkNext0BodyCore listBase bs old1 v24 v25 a0Old a1Old a2Old **
        (.x7 ↦ᵣ t2) **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
      (fun t0 t1 =>
        cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
          (fun _ hq => hq) (h2829 t0 t1 t2))
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => hq) h
  have h := cpsTripleWithin_of_forall_regIs_to_regOwn
    (r := .x7)
    (P := teerWalkNext0BodyCore listBase bs old1 v24 v25 a0Old a1Old a2Old **
      regOwn .x5 ** regOwn .x6 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
    (fun t2 =>
      cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
        (fun _ hq => hq) (h56 t2))
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => hq) h

/-- Ambient through wn0 (no focus cycle regs x1/x10-12/x24-25/x0/temps/blob). -/
def teerWalkNext0Ambient
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

private theorem pcFree_teerWalkNext0Ambient
    (spC loadPtr lenW balPtr balLenW chainIdW
      s7 s11 spVal : Word)
    (balBytes : List (BitVec 8)) (s : TeerSaved)
    (innerVal : Word) :
    (teerWalkNext0Ambient spC loadPtr lenW balPtr balLenW chainIdW
      s7 s11 spVal balBytes s innerVal).pcFree := by
  unfold teerWalkNext0Ambient; pcf

/-- Focus = CycleOk ownTemps prest. -/
def teerWalkNext0Focus
    (listBase : Word) (bs : List (BitVec 8))
    (old1 v24 v25 a0Old a1Old a2Old : Word) : Assertion :=
  teerWalkNext0BodyCore listBase bs old1 v24 v25 a0Old a1Old a2Old **
    regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
    regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31

/-- AfterWalkInitSave flat → CycleOk focus ** ambient. -/
theorem teerAfterWalkInitSaveFlat_to_wn0Pre
    (spC loadPtr lenW balPtr balLenW chainIdW
      s7 s11 spVal regionBase : Word)
    (bs balBytes : List (BitVec 8)) (s : TeerSaved)
    (innerVal : Word) (listOff srcOff : Nat)
    (_hcur : (regionBase + BitVec.ofNat 64 listOff) + signExtend12 (1 : BitVec 12) =
      regionBase + BitVec.ofNat 64 srcOff) :
    let cur := (regionBase + BitVec.ofNat 64 listOff) + signExtend12 (1 : BitVec 12)
    let endW := (regionBase + BitVec.ofNat 64 listOff) + (lenW - innerVal)
    ∀ h,
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
        teerScratchWithoutTypeOwn) h →
      (teerWalkNext0Focus regionBase bs
          LinkWalkInit cur endW cur endW (0 : Word) **
        teerWalkNext0Ambient spC loadPtr lenW balPtr balLenW chainIdW
          s7 s11 spVal balBytes s innerVal) h := by
  intro cur endW _ hp
  unfold teerWalkNext0Focus teerWalkNext0BodyCore teerWalkNext0Ambient
  xperm_hyp hp

/-- Nested post after wn0: ∃ next len. BodyPost ** ambient. -/
def teerWalkNext0PostNested
    (spC loadPtr lenW balPtr balLenW chainIdW
      s7 s11 spVal regionBase endW : Word)
    (bs balBytes : List (BitVec 8)) (s : TeerSaved)
    (innerVal : Word) (srcOff : Nat) : Assertion :=
  fun h => ∃ next len : Word,
    (teerWalkNext0BodyPost regionBase endW next len bs srcOff **
      teerWalkNext0Ambient spC loadPtr lenW balPtr balLenW chainIdW
        s7 s11 spVal balBytes s innerVal) h

set_option maxRecDepth 8000 in
/-- E → AfterWalkNext0Save under applied (short outer list + first item decode). -/
theorem teerWalkNext0_applied_nested
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
    (hoffL : listOff < bs.length)
    (hoverL : regionBase.toNat + listOff < 2 ^ 64)
    (hvalidL : isValidByteAccess (regionBase + BitVec.ofNat 64 listOff) = true)
    (hlenL : lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2 ≠ (0 : Word))
    (h_ge : ¬ BitVec.ult ((bs[listOff]'hoffL).zeroExtend 64) (0xc0 : Word) = true)
    (h_hi : BitVec.ult ((bs[listOff]'hoffL).zeroExtend 64) (0xf8 : Word) = true)
    (h_exact : (regionBase + BitVec.ofNat 64 listOff) +
        (((bs[listOff]'hoffL).zeroExtend 64 - (0xc0 : Word)) +
          signExtend12 (1 : BitVec 12)) =
      (regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2))
    -- first walk_next item at srcOff (payload start after short list head)
    (srcOff : Nat)
    (hcur : (regionBase + BitVec.ofNat 64 listOff) + signExtend12 (1 : BitVec 12) =
      regionBase + BitVec.ofNat 64 srcOff)
    (hoff : srcOff < bs.length)
    (hoverI : regionBase.toNat + srcOff < 2 ^ 64)
    (hvalidI : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOff) = true)
    (hss : ¬ BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        srcOff + 1 < bs.length ∧ regionBase.toNat + (srcOff + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff + 1)) = true)
    (hls : ¬ BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xc0 : Word) = true →
        srcOff + 1 + ((bs[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff + 1 +
          ((bs[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff + 1 + k)) = true)
    (hll : ¬ BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xf8 : Word) = true →
        srcOff + 1 + ((bs[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff + 1 +
          ((bs[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff + 1 + k)) = true)
    (hdec : ∃ next len0 : Word,
      rlpItemDecode bs srcOff (regionBase + BitVec.ofNat 64 srcOff)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next len0)
    (hinb : BitVec.ult (regionBase + BitVec.ofNat 64 srcOff)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true) :
    let s : TeerSaved :=
      { ra := ret, s0 := s0, s1 := s1, s2 := s2, s3 := s3, s4 := s4
        s5 := s5, s6 := s6, s7 := s7, s8 := s8, s9 := s9
        s10 := s10, s11 := s11, a5 := baiW }
    let innerVal := (teerTxTypeDispatch (txSlice bs off len)).2.2
    let endW := (regionBase + BitVec.ofNat 64 listOff) + (lenW - innerVal)
    cpsTripleWithin nFrontToWalkNext0Save
      E AfterWalkNext0Save teerLinkedEarly
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
      (teerWalkNext0PostNested spC loadPtr lenW balPtr balLenW chainIdW
        s7 s11 spVal regionBase endW bs balBytes s innerVal srcOff) := by
  intro s innerVal endW
  have hwi := teerWalkInitShort_applied ret spVal spC loadPtr lenW
    balPtr balLenW chainIdW baiW s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    regionBase bs balBytes off len hspC hnez hptr hlenW hsuccess htype4
    halign hbound hover hvalid0 listOff ha0 hoffL hoverL hvalidL hlenL
    h_ge h_hi h_exact
  have hcy := teerWalkNext0CycleOk_ownTemps regionBase endW bs srcOff
    LinkWalkInit
    ((regionBase + BitVec.ofNat 64 listOff) + signExtend12 (1 : BitVec 12))
    endW
    ((regionBase + BitVec.ofNat 64 listOff) + signExtend12 (1 : BitVec 12))
    endW
    (0 : Word)
    (by simpa using halign) hoff hoverI hvalidI hss hls hll hdec hinb
    hcur rfl
  have hcyF := cpsTripleWithin_frameR
    (teerWalkNext0Ambient spC loadPtr lenW balPtr balLenW chainIdW
      s7 s11 spVal balBytes s innerVal)
    (by exact pcFree_teerWalkNext0Ambient _ _ _ _ _ _ _ _ _ _ _ _) hcy
  have hcyF' :
      cpsTripleWithin nWalkNext0Cycle AfterWalkInitSave AfterWalkNext0Save
        teerLinkedEarly
        (teerWalkNext0Focus regionBase bs
            LinkWalkInit
            ((regionBase + BitVec.ofNat 64 listOff) + signExtend12 (1 : BitVec 12))
            endW
            ((regionBase + BitVec.ofNat 64 listOff) + signExtend12 (1 : BitVec 12))
            endW (0 : Word) **
          teerWalkNext0Ambient spC loadPtr lenW balPtr balLenW chainIdW
            s7 s11 spVal balBytes s innerVal)
        (teerWalkNext0PostNested spC loadPtr lenW balPtr balLenW chainIdW
          s7 s11 spVal regionBase endW bs balBytes s innerVal srcOff) := by
    refine cpsTripleWithin_weaken
      (fun _ hp => by
        unfold teerWalkNext0Focus at hp
        xperm_hyp hp)
      (fun h hq => by
        unfold teerWalkNext0PostNested
        -- frameR: (∃ body) ** ambient
        obtain ⟨h1, h2, hd, hu, hEx, hA⟩ := hq
        obtain ⟨next, len0, hB⟩ := hEx
        exact ⟨next, len0, h1, h2, hd, hu, hB, hA⟩)
      hcyF
  have hsc := teerAfterWalkInitSaveFlat_to_wn0Pre spC loadPtr lenW balPtr
    balLenW chainIdW s7 s11 spVal regionBase bs balBytes s innerVal
    listOff srcOff hcur
  have hseq := cpsTripleWithin_seq_perm_same_cr hsc hwi hcyF'
  exact cpsTripleWithin_mono_nSteps
    (by decide : nFrontToWalkInitSave + nWalkNext0Cycle ≤ nFrontToWalkNext0Save)
    hseq

set_option maxRecDepth 8000 in
/-- Flatten nested → applied-style AfterWalkNext0Save post (exists next/len). -/
theorem teerWalkNext0_applied
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
    (hoffL : listOff < bs.length)
    (hoverL : regionBase.toNat + listOff < 2 ^ 64)
    (hvalidL : isValidByteAccess (regionBase + BitVec.ofNat 64 listOff) = true)
    (hlenL : lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2 ≠ (0 : Word))
    (h_ge : ¬ BitVec.ult ((bs[listOff]'hoffL).zeroExtend 64) (0xc0 : Word) = true)
    (h_hi : BitVec.ult ((bs[listOff]'hoffL).zeroExtend 64) (0xf8 : Word) = true)
    (h_exact : (regionBase + BitVec.ofNat 64 listOff) +
        (((bs[listOff]'hoffL).zeroExtend 64 - (0xc0 : Word)) +
          signExtend12 (1 : BitVec 12)) =
      (regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2))
    (srcOff : Nat)
    (hcur : (regionBase + BitVec.ofNat 64 listOff) + signExtend12 (1 : BitVec 12) =
      regionBase + BitVec.ofNat 64 srcOff)
    (hoff : srcOff < bs.length)
    (hoverI : regionBase.toNat + srcOff < 2 ^ 64)
    (hvalidI : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOff) = true)
    (hss : ¬ BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        srcOff + 1 < bs.length ∧ regionBase.toNat + (srcOff + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff + 1)) = true)
    (hls : ¬ BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xc0 : Word) = true →
        srcOff + 1 + ((bs[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff + 1 +
          ((bs[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff + 1 + k)) = true)
    (hll : ¬ BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xf8 : Word) = true →
        srcOff + 1 + ((bs[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff + 1 +
          ((bs[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff + 1 + k)) = true)
    (hdec : ∃ next len0 : Word,
      rlpItemDecode bs srcOff (regionBase + BitVec.ofNat 64 srcOff)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next len0)
    (hinb : BitVec.ult (regionBase + BitVec.ofNat 64 srcOff)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true) :
    let s : TeerSaved :=
      { ra := ret, s0 := s0, s1 := s1, s2 := s2, s3 := s3, s4 := s4
        s5 := s5, s6 := s6, s7 := s7, s8 := s8, s9 := s9
        s10 := s10, s11 := s11, a5 := baiW }
    let innerVal := (teerTxTypeDispatch (txSlice bs off len)).2.2
    let endW := (regionBase + BitVec.ofNat 64 listOff) + (lenW - innerVal)
    cpsTripleWithin nFrontToWalkNext0Save
      E AfterWalkNext0Save teerLinkedEarly
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
      (fun h => ∃ next len0 : Word,
        ((.x2 ↦ᵣ spC) **
          (.x1 ↦ᵣ LinkWalkNext0) **
          (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
          (.x18 ↦ᵣ balPtr) ** (.x19 ↦ᵣ balLenW) ** (.x20 ↦ᵣ chainIdW) **
          (.x21 ↦ᵣ loadPtr + innerVal) ** (.x22 ↦ᵣ lenW - innerVal) **
          (.x23 ↦ᵣ s7) **
          (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len0) **
          (.x24 ↦ᵣ next) ** (.x25 ↦ᵣ endW) **
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
          teerScratchWithoutTypeOwn **
          ⌜rlpItemDecode bs srcOff (regionBase + BitVec.ofNat 64 srcOff)
            endW next len0⌝) h) := by
  intro s innerVal endW
  have h0 := teerWalkNext0_applied_nested ret spVal spC loadPtr lenW
    balPtr balLenW chainIdW baiW s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    regionBase bs balBytes off len hspC hnez hptr hlenW hsuccess htype4
    halign hbound hover hvalid0 listOff ha0 hoffL hoverL hvalidL hlenL
    h_ge h_hi h_exact srcOff hcur hoff hoverI hvalidI hss hls hll hdec hinb
  exact cpsTripleWithin_weaken (fun _ hp => hp)
    (fun h hq => by
      unfold teerWalkNext0PostNested teerWalkNext0BodyPost teerWalkNext0Ambient at hq
      obtain ⟨next, len0, hq'⟩ := hq
      refine ⟨next, len0, ?_⟩
      xperm_hyp hq') h0

#print axioms teerWalkNext0CycleOk_ownTemps
#print axioms teerWalkNext0_applied_nested
#print axioms teerWalkNext0_applied

end EvmAsm.Codegen.TxEip7702TeerSpec
