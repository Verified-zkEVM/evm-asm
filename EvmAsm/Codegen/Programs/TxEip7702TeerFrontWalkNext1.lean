/-
  Teer front walk_next cycle 1 under applied prest.
  E → AfterWalkNext1Save via FrontWalkNext0 + Cycle1.
-/

import EvmAsm.Codegen.Programs.TxEip7702TeerFrontWalkNext0
import EvmAsm.Codegen.Programs.TxEip7702TeerWalkNextSkip
import EvmAsm.Codegen.Programs.TxTypeDispatchAmbient
import EvmAsm.Codegen.Programs.TxIntrinsicStateGasSpec
import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SAsm.MeasureLoop
import EvmAsm.Rv64.SAsm.StmtSoundCall
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

private abbrev nWalkNextCycle : Nat := 2 + (1 + 87) + 1 + 1

private abbrev nFrontToWalkNext0Save : Nat :=
  ((34 + (6 + (1 + nTypeSteps) + 1)) + (5 + 7)) + (1 + 15 + 1 + 2) + nWalkNextCycle

private abbrev nFrontToWalkNext1Save : Nat := nFrontToWalkNext0Save + nWalkNextCycle

def teerWalkNextSkipBodyPost
    (listBase endPtr next len : Word) (bs : List (BitVec 8))
    (srcOff : Nat) (linkPc : Word) : Assertion :=
  (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
    (.x24 ↦ᵣ next) ** (.x25 ↦ᵣ endPtr) **
    (.x0 ↦ᵣ (0 : Word)) **
    regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
    regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ linkPc) **
    bytesRegion listBase bs **
    ⌜rlpItemDecode bs srcOff (listBase + BitVec.ofNat 64 srcOff) endPtr next len⌝

set_option maxRecDepth 8000 in
/-- Cycle1 CycleOk with regOwn temps x5–7,x28–31. -/
theorem teerWalkNext1CycleOk_ownTemps
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
    cpsTripleWithin nWalkNextCycle AfterWalkNext0Save AfterWalkNext1Save
      teerLinkedEarly
      (teerWalkNext0BodyCore listBase bs old1 v24 v25 a0Old a1Old a2Old **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
      (fun h => ∃ next len : Word,
        (teerWalkNextSkipBodyPost listBase endPtr next len bs srcOff LinkWalkNext1) h) := by
  have hcore (t0 t1 t2 t3 t4 t5 t6 : Word) :
      cpsTripleWithin nWalkNextCycle AfterWalkNext0Save AfterWalkNext1Save
        teerLinkedEarly
        (teerWalkNext0BodyCore listBase bs old1 v24 v25 a0Old a1Old a2Old **
          (.x5 ↦ᵣ t0) ** (.x6 ↦ᵣ t1) ** (.x7 ↦ᵣ t2) **
          (.x28 ↦ᵣ t3) ** (.x29 ↦ᵣ t4) ** (.x30 ↦ᵣ t5) ** (.x31 ↦ᵣ t6))
        (fun h => ∃ next len : Word,
          (teerWalkNextSkipBodyPost listBase endPtr next len bs srcOff LinkWalkNext1) h) := by
    have h0 := teerWalkNext1CycleOk listBase endPtr a2Old t0 t1 t2 t3 t4 t5 t6
      bs srcOff old1 v24 v25 a0Old a1Old
      hsalign hoff hover hvalid hss hls hll hdec hinb hcur hend
    refine cpsTripleWithin_weaken (fun s hp => ?_) (fun h hq => by
      obtain ⟨next, len, hq'⟩ := hq
      exact ⟨next, len, by
        unfold teerWalkNextSkipBodyPost
        exact hq'⟩) h0
    unfold teerWalkNext0BodyCore at hp
    xperm_hyp hp
  -- Lift x30,x31
  have h3031 (t0 t1 t2 t3 t4 : Word) :
      cpsTripleWithin nWalkNextCycle AfterWalkNext0Save AfterWalkNext1Save
        teerLinkedEarly
        (teerWalkNext0BodyCore listBase bs old1 v24 v25 a0Old a1Old a2Old **
          (.x5 ↦ᵣ t0) ** (.x6 ↦ᵣ t1) ** (.x7 ↦ᵣ t2) **
          (.x28 ↦ᵣ t3) ** (.x29 ↦ᵣ t4) **
          regOwn .x30 ** regOwn .x31)
        (fun h => ∃ next len : Word,
          (teerWalkNextSkipBodyPost listBase endPtr next len bs srcOff LinkWalkNext1) h) := by
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
      cpsTripleWithin nWalkNextCycle AfterWalkNext0Save AfterWalkNext1Save
        teerLinkedEarly
        (teerWalkNext0BodyCore listBase bs old1 v24 v25 a0Old a1Old a2Old **
          (.x5 ↦ᵣ t0) ** (.x6 ↦ᵣ t1) ** (.x7 ↦ᵣ t2) **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
        (fun h => ∃ next len : Word,
          (teerWalkNextSkipBodyPost listBase endPtr next len bs srcOff LinkWalkNext1) h) := by
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
      cpsTripleWithin nWalkNextCycle AfterWalkNext0Save AfterWalkNext1Save
        teerLinkedEarly
        (teerWalkNext0BodyCore listBase bs old1 v24 v25 a0Old a1Old a2Old **
          regOwn .x5 ** regOwn .x6 ** (.x7 ↦ᵣ t2) **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
        (fun h => ∃ next len : Word,
          (teerWalkNextSkipBodyPost listBase endPtr next len bs srcOff LinkWalkNext1) h) := by
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


abbrev teerWalkNextSkipAmbient := teerWalkNext0Ambient
abbrev teerWalkNextSkipFocus := teerWalkNext0Focus

private theorem pcFree_teerWalkNextSkipAmbient
    (spC loadPtr lenW balPtr balLenW chainIdW
      s7 s11 spVal : Word)
    (balBytes : List (BitVec 8)) (s : TeerSaved)
    (innerVal : Word) :
    (teerWalkNextSkipAmbient spC loadPtr lenW balPtr balLenW chainIdW
      s7 s11 spVal balBytes s innerVal).pcFree := by
  unfold teerWalkNextSkipAmbient teerWalkNext0Ambient; pcf

/-- Rest of AfterWalkNext0Save flat without the trailing pure decode. -/
def teerWalkNext0FlatRest
    (spC loadPtr lenW balPtr balLenW chainIdW
      s7 s11 spVal regionBase endW : Word)
    (bs balBytes : List (BitVec 8)) (s : TeerSaved)
    (innerVal next0 len0 : Word) : Assertion :=
  (.x2 ↦ᵣ spC) **
    (.x1 ↦ᵣ LinkWalkNext0) **
    (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
    (.x18 ↦ᵣ balPtr) ** (.x19 ↦ᵣ balLenW) ** (.x20 ↦ᵣ chainIdW) **
    (.x21 ↦ᵣ loadPtr + innerVal) ** (.x22 ↦ᵣ lenW - innerVal) **
    (.x23 ↦ᵣ s7) **
    (.x10 ↦ᵣ next0) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len0) **
    (.x24 ↦ᵣ next0) ** (.x25 ↦ᵣ endW) **
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
    teerScratchWithoutTypeOwn

/-- Rest → cycle1 focus ** ambient. -/
theorem teerWalkNext0FlatRest_to_wn1Pre
    (spC loadPtr lenW balPtr balLenW chainIdW
      s7 s11 spVal regionBase endW : Word)
    (bs balBytes : List (BitVec 8)) (s : TeerSaved)
    (innerVal next0 len0 : Word) :
    ∀ h,
      (teerWalkNext0FlatRest spC loadPtr lenW balPtr balLenW chainIdW
          s7 s11 spVal regionBase endW bs balBytes s innerVal next0 len0) h →
      (teerWalkNextSkipFocus regionBase bs
          LinkWalkNext0 next0 endW next0 (0 : Word) len0 **
        teerWalkNextSkipAmbient spC loadPtr lenW balPtr balLenW chainIdW
          s7 s11 spVal balBytes s innerVal) h := by
  intro h hp
  unfold teerWalkNext0FlatRest at hp
  unfold teerWalkNextSkipFocus teerWalkNext0Focus teerWalkNext0BodyCore
    teerWalkNextSkipAmbient teerWalkNext0Ambient
  xperm_hyp hp

def teerWalkNext1PostNested
    (spC loadPtr lenW balPtr balLenW chainIdW
      s7 s11 spVal regionBase endW : Word)
    (bs balBytes : List (BitVec 8)) (s : TeerSaved)
    (innerVal : Word) (srcOff1 : Nat) : Assertion :=
  fun h => ∃ next len : Word,
    (teerWalkNextSkipBodyPost regionBase endW next len bs srcOff1 LinkWalkNext1 **
      teerWalkNextSkipAmbient spC loadPtr lenW balPtr balLenW chainIdW
        s7 s11 spVal balBytes s innerVal) h

set_option maxRecDepth 8000 in
theorem teerWalkNext1_applied_nested
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
    (srcOff0 : Nat)
    (hcur0 : (regionBase + BitVec.ofNat 64 listOff) + signExtend12 (1 : BitVec 12) =
      regionBase + BitVec.ofNat 64 srcOff0)
    (hoff0 : srcOff0 < bs.length)
    (hover0 : regionBase.toNat + srcOff0 < 2 ^ 64)
    (hvalid0I : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOff0) = true)
    (hss0 : ¬ BitVec.ult ((bs[srcOff0]'hoff0).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff0]'hoff0).zeroExtend 64) (0xb8 : Word) = true →
        srcOff0 + 1 < bs.length ∧ regionBase.toNat + (srcOff0 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff0 + 1)) = true)
    (hls0 : ¬ BitVec.ult ((bs[srcOff0]'hoff0).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff0]'hoff0).zeroExtend 64) (0xc0 : Word) = true →
        srcOff0 + 1 + ((bs[srcOff0]'hoff0).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff0 + 1 +
          ((bs[srcOff0]'hoff0).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff0]'hoff0).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff0 + 1 + k)) = true)
    (hll0 : ¬ BitVec.ult ((bs[srcOff0]'hoff0).zeroExtend 64) (0xf8 : Word) = true →
        srcOff0 + 1 + ((bs[srcOff0]'hoff0).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff0 + 1 +
          ((bs[srcOff0]'hoff0).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff0]'hoff0).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff0 + 1 + k)) = true)
    (hdec0 : ∃ next len0 : Word,
      rlpItemDecode bs srcOff0 (regionBase + BitVec.ofNat 64 srcOff0)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next len0)
    (hinb0 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOff0)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (srcOff1 : Nat)
    (hoff1 : srcOff1 < bs.length)
    (hover1 : regionBase.toNat + srcOff1 < 2 ^ 64)
    (hvalid1 : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOff1) = true)
    (hss1 : ¬ BitVec.ult ((bs[srcOff1]'hoff1).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff1]'hoff1).zeroExtend 64) (0xb8 : Word) = true →
        srcOff1 + 1 < bs.length ∧ regionBase.toNat + (srcOff1 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff1 + 1)) = true)
    (hls1 : ¬ BitVec.ult ((bs[srcOff1]'hoff1).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff1]'hoff1).zeroExtend 64) (0xc0 : Word) = true →
        srcOff1 + 1 + ((bs[srcOff1]'hoff1).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff1 + 1 +
          ((bs[srcOff1]'hoff1).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff1]'hoff1).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff1 + 1 + k)) = true)
    (hll1 : ¬ BitVec.ult ((bs[srcOff1]'hoff1).zeroExtend 64) (0xf8 : Word) = true →
        srcOff1 + 1 + ((bs[srcOff1]'hoff1).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff1 + 1 +
          ((bs[srcOff1]'hoff1).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff1]'hoff1).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff1 + 1 + k)) = true)
    (hdec1 : ∃ next len1 : Word,
      rlpItemDecode bs srcOff1 (regionBase + BitVec.ofNat 64 srcOff1)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next len1)
    (hinb1 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOff1)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridge : ∀ next0 len0 : Word,
      rlpItemDecode bs srcOff0 (regionBase + BitVec.ofNat 64 srcOff0)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next0 len0 →
      next0 = regionBase + BitVec.ofNat 64 srcOff1) :
    let s : TeerSaved :=
      { ra := ret, s0 := s0, s1 := s1, s2 := s2, s3 := s3, s4 := s4
        s5 := s5, s6 := s6, s7 := s7, s8 := s8, s9 := s9
        s10 := s10, s11 := s11, a5 := baiW }
    let innerVal := (teerTxTypeDispatch (txSlice bs off len)).2.2
    let endW := (regionBase + BitVec.ofNat 64 listOff) + (lenW - innerVal)
    cpsTripleWithin nFrontToWalkNext1Save
      E AfterWalkNext1Save teerLinkedEarly
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
      (teerWalkNext1PostNested spC loadPtr lenW balPtr balLenW chainIdW
        s7 s11 spVal regionBase endW bs balBytes s innerVal srcOff1) := by
  intro s innerVal endW
  have hwn0 := teerWalkNext0_applied ret spVal spC loadPtr lenW
    balPtr balLenW chainIdW baiW s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    regionBase bs balBytes off len hspC hnez hptr hlenW hsuccess htype4
    halign hbound hover hvalid0 listOff ha0 hoffL hoverL hvalidL hlenL
    h_ge h_hi h_exact srcOff0 hcur0 hoff0 hover0 hvalid0I hss0 hls0 hll0 hdec0 hinb0
  let Flat (p : Word × Word) : Assertion :=
    teerWalkNext0FlatRest spC loadPtr lenW balPtr balLenW chainIdW
      s7 s11 spVal regionBase endW bs balBytes s innerVal p.1 p.2 **
    ⌜rlpItemDecode bs srcOff0 (regionBase + BitVec.ofNat 64 srcOff0)
      endW p.1 p.2⌝
  have hwn0E :
      cpsTripleWithin nFrontToWalkNext0Save E AfterWalkNext0Save teerLinkedEarly
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
        (fun h => ∃ p : Word × Word, Flat p h) := by
    refine cpsTripleWithin_weaken (fun _ hp => hp) (fun h hq => ?_) hwn0
    obtain ⟨next0, len0, hq'⟩ := hq
    refine ⟨(next0, len0), ?_⟩
    -- wn0 flat post → Flat (rest ** pure)
    dsimp only [Flat, teerWalkNext0FlatRest]
    xperm_hyp hq'
  have hstep (p : Word × Word) :
      cpsTripleWithin nWalkNextCycle AfterWalkNext0Save AfterWalkNext1Save
        teerLinkedEarly (Flat p)
        (teerWalkNext1PostNested spC loadPtr lenW balPtr balLenW chainIdW
          s7 s11 spVal regionBase endW bs balBytes s innerVal srcOff1) := by
    dsimp only [Flat]
    -- prest = Rest ** pure; pure_pre wants pure ** H
    have hswap :
        cpsTripleWithin nWalkNextCycle AfterWalkNext0Save AfterWalkNext1Save
          teerLinkedEarly
          (⌜rlpItemDecode bs srcOff0 (regionBase + BitVec.ofNat 64 srcOff0)
              endW p.1 p.2⌝ **
            teerWalkNext0FlatRest spC loadPtr lenW balPtr balLenW chainIdW
              s7 s11 spVal regionBase endW bs balBytes s innerVal p.1 p.2)
          (teerWalkNext1PostNested spC loadPtr lenW balPtr balLenW chainIdW
            s7 s11 spVal regionBase endW bs balBytes s innerVal srcOff1) := by
      refine cpsTripleWithin_pure_pre (fun hpure => ?_)
      have hcur1 : p.1 = regionBase + BitVec.ofNat 64 srcOff1 :=
        hbridge p.1 p.2 (by simpa [endW, innerVal] using hpure)
      have hcy := teerWalkNext1CycleOk_ownTemps regionBase endW bs srcOff1
        LinkWalkNext0 p.1 endW p.1 (0 : Word) p.2
        (by simpa using halign) hoff1 hover1 hvalid1 hss1 hls1 hll1 hdec1 hinb1
        hcur1 rfl
      have hcyF := cpsTripleWithin_frameR
        (teerWalkNextSkipAmbient spC loadPtr lenW balPtr balLenW chainIdW
          s7 s11 spVal balBytes s innerVal)
        (by exact pcFree_teerWalkNextSkipAmbient _ _ _ _ _ _ _ _ _ _ _ _) hcy
      have hcyF' :
          cpsTripleWithin nWalkNextCycle AfterWalkNext0Save AfterWalkNext1Save
            teerLinkedEarly
            (teerWalkNextSkipFocus regionBase bs
                LinkWalkNext0 p.1 endW p.1 (0 : Word) p.2 **
              teerWalkNextSkipAmbient spC loadPtr lenW balPtr balLenW chainIdW
                s7 s11 spVal balBytes s innerVal)
            (teerWalkNext1PostNested spC loadPtr lenW balPtr balLenW chainIdW
              s7 s11 spVal regionBase endW bs balBytes s innerVal srcOff1) := by
        refine cpsTripleWithin_weaken
          (fun _ hp => by
            unfold teerWalkNextSkipFocus teerWalkNext0Focus at hp
            xperm_hyp hp)
          (fun h hq => by
            unfold teerWalkNext1PostNested
            obtain ⟨h1, h2, hd, hu, hEx, hA⟩ := hq
            obtain ⟨next, len1, hB⟩ := hEx
            exact ⟨next, len1, h1, h2, hd, hu, hB, hA⟩)
          hcyF
      exact cpsTripleWithin_weaken
        (teerWalkNext0FlatRest_to_wn1Pre spC loadPtr lenW balPtr balLenW chainIdW
          s7 s11 spVal regionBase endW bs balBytes s innerVal p.1 p.2)
        (fun _ hq => hq) hcyF'
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => hq) hswap
  have hseq := cpsTripleWithin_seq_exists_same_cr hwn0E hstep
  exact cpsTripleWithin_mono_nSteps
    (by decide : nFrontToWalkNext0Save + nWalkNextCycle ≤ nFrontToWalkNext1Save)
    hseq

set_option maxRecDepth 8000 in
/-- Flatten nested → applied-style AfterWalkNext1Save post. -/
theorem teerWalkNext1_applied
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
    (srcOff0 : Nat)
    (hcur0 : (regionBase + BitVec.ofNat 64 listOff) + signExtend12 (1 : BitVec 12) =
      regionBase + BitVec.ofNat 64 srcOff0)
    (hoff0 : srcOff0 < bs.length)
    (hover0 : regionBase.toNat + srcOff0 < 2 ^ 64)
    (hvalid0I : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOff0) = true)
    (hss0 : ¬ BitVec.ult ((bs[srcOff0]'hoff0).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff0]'hoff0).zeroExtend 64) (0xb8 : Word) = true →
        srcOff0 + 1 < bs.length ∧ regionBase.toNat + (srcOff0 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff0 + 1)) = true)
    (hls0 : ¬ BitVec.ult ((bs[srcOff0]'hoff0).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff0]'hoff0).zeroExtend 64) (0xc0 : Word) = true →
        srcOff0 + 1 + ((bs[srcOff0]'hoff0).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff0 + 1 +
          ((bs[srcOff0]'hoff0).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff0]'hoff0).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff0 + 1 + k)) = true)
    (hll0 : ¬ BitVec.ult ((bs[srcOff0]'hoff0).zeroExtend 64) (0xf8 : Word) = true →
        srcOff0 + 1 + ((bs[srcOff0]'hoff0).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff0 + 1 +
          ((bs[srcOff0]'hoff0).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff0]'hoff0).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff0 + 1 + k)) = true)
    (hdec0 : ∃ next len0 : Word,
      rlpItemDecode bs srcOff0 (regionBase + BitVec.ofNat 64 srcOff0)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next len0)
    (hinb0 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOff0)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (srcOff1 : Nat)
    (hoff1 : srcOff1 < bs.length)
    (hover1 : regionBase.toNat + srcOff1 < 2 ^ 64)
    (hvalid1 : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOff1) = true)
    (hss1 : ¬ BitVec.ult ((bs[srcOff1]'hoff1).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff1]'hoff1).zeroExtend 64) (0xb8 : Word) = true →
        srcOff1 + 1 < bs.length ∧ regionBase.toNat + (srcOff1 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff1 + 1)) = true)
    (hls1 : ¬ BitVec.ult ((bs[srcOff1]'hoff1).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff1]'hoff1).zeroExtend 64) (0xc0 : Word) = true →
        srcOff1 + 1 + ((bs[srcOff1]'hoff1).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff1 + 1 +
          ((bs[srcOff1]'hoff1).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff1]'hoff1).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff1 + 1 + k)) = true)
    (hll1 : ¬ BitVec.ult ((bs[srcOff1]'hoff1).zeroExtend 64) (0xf8 : Word) = true →
        srcOff1 + 1 + ((bs[srcOff1]'hoff1).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff1 + 1 +
          ((bs[srcOff1]'hoff1).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff1]'hoff1).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff1 + 1 + k)) = true)
    (hdec1 : ∃ next len1 : Word,
      rlpItemDecode bs srcOff1 (regionBase + BitVec.ofNat 64 srcOff1)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next len1)
    (hinb1 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOff1)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridge : ∀ next0 len0 : Word,
      rlpItemDecode bs srcOff0 (regionBase + BitVec.ofNat 64 srcOff0)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next0 len0 →
      next0 = regionBase + BitVec.ofNat 64 srcOff1) :
    let s : TeerSaved :=
      { ra := ret, s0 := s0, s1 := s1, s2 := s2, s3 := s3, s4 := s4
        s5 := s5, s6 := s6, s7 := s7, s8 := s8, s9 := s9
        s10 := s10, s11 := s11, a5 := baiW }
    let innerVal := (teerTxTypeDispatch (txSlice bs off len)).2.2
    let endW := (regionBase + BitVec.ofNat 64 listOff) + (lenW - innerVal)
    cpsTripleWithin nFrontToWalkNext1Save
      E AfterWalkNext1Save teerLinkedEarly
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
      (fun h => ∃ next len1 : Word,
        ((.x2 ↦ᵣ spC) **
          (.x1 ↦ᵣ LinkWalkNext1) **
          (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
          (.x18 ↦ᵣ balPtr) ** (.x19 ↦ᵣ balLenW) ** (.x20 ↦ᵣ chainIdW) **
          (.x21 ↦ᵣ loadPtr + innerVal) ** (.x22 ↦ᵣ lenW - innerVal) **
          (.x23 ↦ᵣ s7) **
          (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len1) **
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
          ⌜rlpItemDecode bs srcOff1 (regionBase + BitVec.ofNat 64 srcOff1)
            endW next len1⌝) h) := by
  intro s innerVal endW
  have h0 := teerWalkNext1_applied_nested ret spVal spC loadPtr lenW
    balPtr balLenW chainIdW baiW s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    regionBase bs balBytes off len hspC hnez hptr hlenW hsuccess htype4
    halign hbound hover hvalid0 listOff ha0 hoffL hoverL hvalidL hlenL
    h_ge h_hi h_exact srcOff0 hcur0 hoff0 hover0 hvalid0I hss0 hls0 hll0 hdec0 hinb0
    srcOff1 hoff1 hover1 hvalid1 hss1 hls1 hll1 hdec1 hinb1 hbridge
  exact cpsTripleWithin_weaken (fun _ hp => hp)
    (fun h hq => by
      unfold teerWalkNext1PostNested teerWalkNextSkipBodyPost
        teerWalkNextSkipAmbient teerWalkNext0Ambient at hq
      obtain ⟨next, len1, hq'⟩ := hq
      refine ⟨next, len1, ?_⟩
      xperm_hyp hq') h0

#print axioms teerWalkNext1CycleOk_ownTemps
#print axioms teerWalkNext0FlatRest_to_wn1Pre
#print axioms teerWalkNext1_applied_nested
#print axioms teerWalkNext1_applied

end EvmAsm.Codegen.TxEip7702TeerSpec
