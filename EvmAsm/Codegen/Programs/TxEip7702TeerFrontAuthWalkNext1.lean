/-
  Teer front auth walk_next cycle 1 under applied prest.
  E → AfterAuthWalkNext1Save via FrontAuthWalkNext0 + Cycle1.
-/

import EvmAsm.Codegen.Programs.TxEip7702TeerFrontAuthWalkNext0
import EvmAsm.Codegen.Programs.TxEip7702TeerAuthWalkNextSkip
import EvmAsm.Codegen.Programs.TxTypeDispatchAmbient
import EvmAsm.Codegen.Programs.TxIntrinsicStateGasSpec
import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SAsm.MeasureLoop
import EvmAsm.Rv64.SAsm.StmtSoundCall
import EvmAsm.Rv64.SAsm.RwSubwindow
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
private abbrev nWalkNext5CycleOnly : Nat := 2 + (1 + 87) + 1
private abbrev nValueNonzeroCyclePub : Nat := 2 + (1 + 87) + 1 + 4
private abbrev nWalkInit2Short : Nat := 1 + 15 + 1 + 2
private abbrev nInnerSetup2 : Nat := 7
private abbrev nWalkInit2FromValue : Nat := nInnerSetup2 + nWalkInit2Short
private abbrev nFrontToWalkNext5Bne : Nat :=
  ((34 + (6 + (1 + nTypeSteps) + 1)) + (5 + 7)) + (1 + 15 + 1 + 2) +
    nWalkNextCycle * 5 + nWalkNext5CycleOnly
private abbrev nFrontToRecipientSave : Nat := nFrontToWalkNext5Bne + 8
private abbrev nFrontToValueNonzero : Nat := nFrontToRecipientSave + nValueNonzeroCyclePub
private abbrev nFrontToWalkInit2Save : Nat := nFrontToValueNonzero + nWalkInit2FromValue
private abbrev nAuthWalkNextCycle : Nat := 2 + (1 + 87) + 1 + 1
private abbrev nFrontToAuthWalkNext0SavePub : Nat :=
  nFrontToWalkInit2Save + nAuthWalkNextCycle
private abbrev nFrontToAuthWalkNext1Save : Nat :=
  nFrontToAuthWalkNext0SavePub + nAuthWalkNextCycle

local macro "pcf" : tactic => `(tactic|
  repeat first
    | apply pcFree_sepConj
    | exact pcFree_regIs
    | exact pcFree_regOwn
    | exact pcFree_memIs
    | exact pcFree_memOwn
    | exact pcFree_emp
    | exact pcFree_pure
    | exact bytesRegion_pcFree _ _
    | exact frameSlotsSaved_pcFree _ _ _)

/-- Auth skip body post with parametric link (cycles with Save s5). -/
def teerAuthWalkNextSkipBodyPost
    (listBase endPtr next len : Word) (bs : List (BitVec 8))
    (srcOff : Nat) (linkPc : Word) : Assertion :=
  (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
    (.x21 ↦ᵣ next) ** (.x22 ↦ᵣ endPtr) **
    (.x0 ↦ᵣ (0 : Word)) **
    regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
    regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ linkPc) **
    bytesRegion listBase bs **
    ⌜rlpItemDecode bs srcOff (listBase + BitVec.ofNat 64 srcOff) endPtr next len⌝

set_option maxRecDepth 8000 in
/-- Cycle1 CycleOk with regOwn temps x5–7,x28–31. -/
theorem teerAuthWalkNext1CycleOk_ownTemps
    (listBase endPtr : Word) (bs : List (BitVec 8)) (srcOff : Nat)
    (old1 v21 v22 a0Old a1Old a2Old : Word)
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
    (hcur : v21 = listBase + BitVec.ofNat 64 srcOff)
    (hend : v22 = endPtr) :
    cpsTripleWithin nAuthWalkNextCycle AfterAuthWalkNext0Save AfterAuthWalkNext1Save
      teerLinkedEarly
      (teerAuthWalkNext0BodyCore listBase bs old1 v21 v22 a0Old a1Old a2Old **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
      (fun h => ∃ next len : Word,
        (teerAuthWalkNextSkipBodyPost listBase endPtr next len bs srcOff
          LinkAuthWalkNext1) h) := by
  have hcore (t0 t1 t2 t3 t4 t5 t6 : Word) :
      cpsTripleWithin nAuthWalkNextCycle AfterAuthWalkNext0Save AfterAuthWalkNext1Save
        teerLinkedEarly
        (teerAuthWalkNext0BodyCore listBase bs old1 v21 v22 a0Old a1Old a2Old **
          (.x5 ↦ᵣ t0) ** (.x6 ↦ᵣ t1) ** (.x7 ↦ᵣ t2) **
          (.x28 ↦ᵣ t3) ** (.x29 ↦ᵣ t4) ** (.x30 ↦ᵣ t5) ** (.x31 ↦ᵣ t6))
        (fun h => ∃ next len : Word,
          (teerAuthWalkNextSkipBodyPost listBase endPtr next len bs srcOff
            LinkAuthWalkNext1) h) := by
    have h0 := teerAuthWalkNext1CycleOk listBase endPtr a2Old t0 t1 t2 t3 t4 t5 t6
      bs srcOff old1 v21 v22 a0Old a1Old
      hsalign hoff hover hvalid hss hls hll hdec hinb hcur hend
    refine cpsTripleWithin_weaken (fun s hp => ?_) (fun h hq => by
      obtain ⟨next, len, hq'⟩ := hq
      exact ⟨next, len, by
        unfold teerAuthWalkNextSkipBodyPost
        exact hq'⟩) h0
    unfold teerAuthWalkNext0BodyCore at hp
    xperm_hyp hp
  have h3031 (t0 t1 t2 t3 t4 : Word) :
      cpsTripleWithin nAuthWalkNextCycle AfterAuthWalkNext0Save AfterAuthWalkNext1Save
        teerLinkedEarly
        (teerAuthWalkNext0BodyCore listBase bs old1 v21 v22 a0Old a1Old a2Old **
          (.x5 ↦ᵣ t0) ** (.x6 ↦ᵣ t1) ** (.x7 ↦ᵣ t2) **
          (.x28 ↦ᵣ t3) ** (.x29 ↦ᵣ t4) **
          regOwn .x30 ** regOwn .x31)
        (fun h => ∃ next len : Word,
          (teerAuthWalkNextSkipBodyPost listBase endPtr next len bs srcOff
            LinkAuthWalkNext1) h) := by
    have h := cpsTripleWithin_of_forall_regIs_to_regOwn2
      (r1 := .x30) (r2 := .x31)
      (P := teerAuthWalkNext0BodyCore listBase bs old1 v21 v22 a0Old a1Old a2Old **
        (.x5 ↦ᵣ t0) ** (.x6 ↦ᵣ t1) ** (.x7 ↦ᵣ t2) **
        (.x28 ↦ᵣ t3) ** (.x29 ↦ᵣ t4))
      (fun t5 t6 =>
        cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
          (fun _ hq => hq) (hcore t0 t1 t2 t3 t4 t5 t6))
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => hq) h
  have h2829 (t0 t1 t2 : Word) :
      cpsTripleWithin nAuthWalkNextCycle AfterAuthWalkNext0Save AfterAuthWalkNext1Save
        teerLinkedEarly
        (teerAuthWalkNext0BodyCore listBase bs old1 v21 v22 a0Old a1Old a2Old **
          (.x5 ↦ᵣ t0) ** (.x6 ↦ᵣ t1) ** (.x7 ↦ᵣ t2) **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
        (fun h => ∃ next len : Word,
          (teerAuthWalkNextSkipBodyPost listBase endPtr next len bs srcOff
            LinkAuthWalkNext1) h) := by
    have h := cpsTripleWithin_of_forall_regIs_to_regOwn2
      (r1 := .x28) (r2 := .x29)
      (P := teerAuthWalkNext0BodyCore listBase bs old1 v21 v22 a0Old a1Old a2Old **
        (.x5 ↦ᵣ t0) ** (.x6 ↦ᵣ t1) ** (.x7 ↦ᵣ t2) **
        regOwn .x30 ** regOwn .x31)
      (fun t3 t4 =>
        cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
          (fun _ hq => hq) (h3031 t0 t1 t2 t3 t4))
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => hq) h
  have h56 (t2 : Word) :
      cpsTripleWithin nAuthWalkNextCycle AfterAuthWalkNext0Save AfterAuthWalkNext1Save
        teerLinkedEarly
        (teerAuthWalkNext0BodyCore listBase bs old1 v21 v22 a0Old a1Old a2Old **
          regOwn .x5 ** regOwn .x6 ** (.x7 ↦ᵣ t2) **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
        (fun h => ∃ next len : Word,
          (teerAuthWalkNextSkipBodyPost listBase endPtr next len bs srcOff
            LinkAuthWalkNext1) h) := by
    have h := cpsTripleWithin_of_forall_regIs_to_regOwn2
      (r1 := .x5) (r2 := .x6)
      (P := teerAuthWalkNext0BodyCore listBase bs old1 v21 v22 a0Old a1Old a2Old **
        (.x7 ↦ᵣ t2) **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
      (fun t0 t1 =>
        cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
          (fun _ hq => hq) (h2829 t0 t1 t2))
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => hq) h
  have h := cpsTripleWithin_of_forall_regIs_to_regOwn
    (r := .x7)
    (P := teerAuthWalkNext0BodyCore listBase bs old1 v21 v22 a0Old a1Old a2Old **
      regOwn .x5 ** regOwn .x6 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
    (fun t2 =>
      cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
        (fun _ hq => hq) (h56 t2))
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => hq) h

abbrev teerAuthWalkNextSkipAmbient := teerAuthWalkNext0Ambient
abbrev teerAuthWalkNextSkipFocus := teerAuthWalkNext0Focus

private theorem pcFree_teerAuthWalkNextSkipAmbient
    (spC loadPtr lenW balPtr balLenW chainIdW
      s7 s11 spVal cursorV endWV : Word)
    (balBytes : List (BitVec 8)) (s : TeerSaved)
    (innerVal : Word) :
    (teerAuthWalkNextSkipAmbient spC loadPtr lenW balPtr balLenW chainIdW
      s7 s11 spVal cursorV endWV balBytes s innerVal).pcFree := by
  unfold teerAuthWalkNextSkipAmbient teerAuthWalkNext0Ambient; pcf

/-- Rest of AfterAuthWalkNext0Save flat without trailing pure. -/
def teerAuthWalkNext0FlatRest
    (spC loadPtr lenW balPtr balLenW chainIdW
      s7 s11 spVal regionBase endL cursorV endWV : Word)
    (bs balBytes : List (BitVec 8)) (s : TeerSaved)
    (innerVal next0 len0 : Word) : Assertion :=
  (.x2 ↦ᵣ spC) **
    (.x1 ↦ᵣ LinkAuthWalkNext0) **
    (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
    (.x18 ↦ᵣ balPtr) ** (.x19 ↦ᵣ balLenW) ** (.x20 ↦ᵣ chainIdW) **
    (.x21 ↦ᵣ next0) ** (.x22 ↦ᵣ endL) **
    (.x23 ↦ᵣ s7) **
    (.x10 ↦ᵣ next0) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len0) **
    (.x24 ↦ᵣ cursorV) ** (.x25 ↦ᵣ endWV) **
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
    memOwn RecipientPtrAddr ** memOwn RecipientLenAddr **
    memOwn ValueNonzeroAddr **
    teerScratchWithoutVnzOwn

theorem teerAuthWalkNext0FlatRest_to_awn1Pre
    (spC loadPtr lenW balPtr balLenW chainIdW
      s7 s11 spVal regionBase endL cursorV endWV : Word)
    (bs balBytes : List (BitVec 8)) (s : TeerSaved)
    (innerVal next0 len0 : Word) :
    ∀ h,
      (teerAuthWalkNext0FlatRest spC loadPtr lenW balPtr balLenW chainIdW
          s7 s11 spVal regionBase endL cursorV endWV bs balBytes s
          innerVal next0 len0) h →
      (teerAuthWalkNextSkipFocus regionBase bs
          LinkAuthWalkNext0 next0 endL next0 (0 : Word) len0 **
        teerAuthWalkNextSkipAmbient spC loadPtr lenW balPtr balLenW chainIdW
          s7 s11 spVal cursorV endWV balBytes s innerVal) h := by
  intro h hp
  unfold teerAuthWalkNext0FlatRest at hp
  unfold teerAuthWalkNextSkipFocus teerAuthWalkNext0Focus teerAuthWalkNext0BodyCore
    teerAuthWalkNextSkipAmbient teerAuthWalkNext0Ambient
  xperm_hyp hp

def teerAuthWalkNext1PostNested
    (spC loadPtr lenW balPtr balLenW chainIdW
      s7 s11 spVal regionBase endL cursorV endWV : Word)
    (bs balBytes : List (BitVec 8)) (s : TeerSaved)
    (innerVal : Word) (srcOffA1 : Nat) : Assertion :=
  fun h => ∃ next len : Word,
    (teerAuthWalkNextSkipBodyPost regionBase endL next len bs srcOffA1
        LinkAuthWalkNext1 **
      teerAuthWalkNextSkipAmbient spC loadPtr lenW balPtr balLenW chainIdW
        s7 s11 spVal cursorV endWV balBytes s innerVal) h

set_option maxRecDepth 8000 in
theorem teerAuthWalkNext1_applied_nested
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
    (srcOff2 : Nat)
    (hoff2 : srcOff2 < bs.length)
    (hover2 : regionBase.toNat + srcOff2 < 2 ^ 64)
    (hvalid2 : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOff2) = true)
    (hss2 : ¬ BitVec.ult ((bs[srcOff2]'hoff2).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff2]'hoff2).zeroExtend 64) (0xb8 : Word) = true →
        srcOff2 + 1 < bs.length ∧ regionBase.toNat + (srcOff2 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff2 + 1)) = true)
    (hls2 : ¬ BitVec.ult ((bs[srcOff2]'hoff2).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff2]'hoff2).zeroExtend 64) (0xc0 : Word) = true →
        srcOff2 + 1 + ((bs[srcOff2]'hoff2).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff2 + 1 +
          ((bs[srcOff2]'hoff2).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff2]'hoff2).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff2 + 1 + k)) = true)
    (hll2 : ¬ BitVec.ult ((bs[srcOff2]'hoff2).zeroExtend 64) (0xf8 : Word) = true →
        srcOff2 + 1 + ((bs[srcOff2]'hoff2).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff2 + 1 +
          ((bs[srcOff2]'hoff2).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff2]'hoff2).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff2 + 1 + k)) = true)
    (hdec2 : ∃ next len2 : Word,
      rlpItemDecode bs srcOff2 (regionBase + BitVec.ofNat 64 srcOff2)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next len2)
    (hinb2 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOff2)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (srcOff3 : Nat)
    (hoff3 : srcOff3 < bs.length)
    (hover3 : regionBase.toNat + srcOff3 < 2 ^ 64)
    (hvalid3 : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOff3) = true)
    (hss3 : ¬ BitVec.ult ((bs[srcOff3]'hoff3).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff3]'hoff3).zeroExtend 64) (0xb8 : Word) = true →
        srcOff3 + 1 < bs.length ∧ regionBase.toNat + (srcOff3 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff3 + 1)) = true)
    (hls3 : ¬ BitVec.ult ((bs[srcOff3]'hoff3).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff3]'hoff3).zeroExtend 64) (0xc0 : Word) = true →
        srcOff3 + 1 + ((bs[srcOff3]'hoff3).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff3 + 1 +
          ((bs[srcOff3]'hoff3).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff3]'hoff3).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff3 + 1 + k)) = true)
    (hll3 : ¬ BitVec.ult ((bs[srcOff3]'hoff3).zeroExtend 64) (0xf8 : Word) = true →
        srcOff3 + 1 + ((bs[srcOff3]'hoff3).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff3 + 1 +
          ((bs[srcOff3]'hoff3).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff3]'hoff3).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff3 + 1 + k)) = true)
    (hdec3 : ∃ next len3 : Word,
      rlpItemDecode bs srcOff3 (regionBase + BitVec.ofNat 64 srcOff3)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next len3)
    (hinb3 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOff3)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (srcOff4 : Nat)
    (hoff4 : srcOff4 < bs.length)
    (hover4 : regionBase.toNat + srcOff4 < 2 ^ 64)
    (hvalid4 : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOff4) = true)
    (hss4 : ¬ BitVec.ult ((bs[srcOff4]'hoff4).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff4]'hoff4).zeroExtend 64) (0xb8 : Word) = true →
        srcOff4 + 1 < bs.length ∧ regionBase.toNat + (srcOff4 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff4 + 1)) = true)
    (hls4 : ¬ BitVec.ult ((bs[srcOff4]'hoff4).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff4]'hoff4).zeroExtend 64) (0xc0 : Word) = true →
        srcOff4 + 1 + ((bs[srcOff4]'hoff4).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff4 + 1 +
          ((bs[srcOff4]'hoff4).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff4]'hoff4).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff4 + 1 + k)) = true)
    (hll4 : ¬ BitVec.ult ((bs[srcOff4]'hoff4).zeroExtend 64) (0xf8 : Word) = true →
        srcOff4 + 1 + ((bs[srcOff4]'hoff4).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff4 + 1 +
          ((bs[srcOff4]'hoff4).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff4]'hoff4).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff4 + 1 + k)) = true)
    (hdec4 : ∃ next len4 : Word,
      rlpItemDecode bs srcOff4 (regionBase + BitVec.ofNat 64 srcOff4)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next len4)
    (hinb4 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOff4)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (srcOff5 : Nat)
    (hoff5 : srcOff5 < bs.length)
    (hover5 : regionBase.toNat + srcOff5 < 2 ^ 64)
    (hvalid5 : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOff5) = true)
    (hss5 : ¬ BitVec.ult ((bs[srcOff5]'hoff5).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff5]'hoff5).zeroExtend 64) (0xb8 : Word) = true →
        srcOff5 + 1 < bs.length ∧ regionBase.toNat + (srcOff5 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff5 + 1)) = true)
    (hls5 : ¬ BitVec.ult ((bs[srcOff5]'hoff5).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff5]'hoff5).zeroExtend 64) (0xc0 : Word) = true →
        srcOff5 + 1 + ((bs[srcOff5]'hoff5).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff5 + 1 +
          ((bs[srcOff5]'hoff5).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff5]'hoff5).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff5 + 1 + k)) = true)
    (hll5 : ¬ BitVec.ult ((bs[srcOff5]'hoff5).zeroExtend 64) (0xf8 : Word) = true →
        srcOff5 + 1 + ((bs[srcOff5]'hoff5).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff5 + 1 +
          ((bs[srcOff5]'hoff5).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff5]'hoff5).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff5 + 1 + k)) = true)
    (hdec5 : ∃ next len5 : Word,
      rlpItemDecode bs srcOff5 (regionBase + BitVec.ofNat 64 srcOff5)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next len5)
    (hinb5 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOff5)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridge : ∀ next0 len0 : Word,
      rlpItemDecode bs srcOff0 (regionBase + BitVec.ofNat 64 srcOff0)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next0 len0 →
      next0 = regionBase + BitVec.ofNat 64 srcOff1)
    (hbridge1 : ∀ next1 len1 : Word,
      rlpItemDecode bs srcOff1 (regionBase + BitVec.ofNat 64 srcOff1)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next1 len1 →
      next1 = regionBase + BitVec.ofNat 64 srcOff2)
    (hbridge2 : ∀ next2 len2 : Word,
      rlpItemDecode bs srcOff2 (regionBase + BitVec.ofNat 64 srcOff2)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next2 len2 →
      next2 = regionBase + BitVec.ofNat 64 srcOff3)
    (hbridge3 : ∀ next3 len3 : Word,
      rlpItemDecode bs srcOff3 (regionBase + BitVec.ofNat 64 srcOff3)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next3 len3 →
      next3 = regionBase + BitVec.ofNat 64 srcOff4)
    (hbridge4 : ∀ next4 len4 : Word,
      rlpItemDecode bs srcOff4 (regionBase + BitVec.ofNat 64 srcOff4)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next4 len4 →
      next4 = regionBase + BitVec.ofNat 64 srcOff5)
    (srcOffV : Nat)
    (hoffV : srcOffV < bs.length)
    (hoverV : regionBase.toNat + srcOffV < 2 ^ 64)
    (hvalidV : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOffV) = true)
    (hssV : ¬ BitVec.ult ((bs[srcOffV]'hoffV).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffV]'hoffV).zeroExtend 64) (0xb8 : Word) = true →
        srcOffV + 1 < bs.length ∧ regionBase.toNat + (srcOffV + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffV + 1)) = true)
    (hlsV : ¬ BitVec.ult ((bs[srcOffV]'hoffV).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffV]'hoffV).zeroExtend 64) (0xc0 : Word) = true →
        srcOffV + 1 + ((bs[srcOffV]'hoffV).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffV + 1 +
          ((bs[srcOffV]'hoffV).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffV]'hoffV).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffV + 1 + k)) = true)
    (hllV : ¬ BitVec.ult ((bs[srcOffV]'hoffV).zeroExtend 64) (0xf8 : Word) = true →
        srcOffV + 1 + ((bs[srcOffV]'hoffV).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffV + 1 +
          ((bs[srcOffV]'hoffV).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffV]'hoffV).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffV + 1 + k)) = true)
    (hdecV : ∃ next lenV : Word,
      rlpItemDecode bs srcOffV (regionBase + BitVec.ofNat 64 srcOffV)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenV)
    (hinbV : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffV)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridge5 : ∀ next5 len5 : Word,
      rlpItemDecode bs srcOff5 (regionBase + BitVec.ofNat 64 srcOff5)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next5 len5 →
      next5 = regionBase + BitVec.ofNat 64 srcOffV) 
    -- auth walk_next0 item
    (srcOffA : Nat)
    (hcurA : (regionBase + BitVec.ofNat 64 listOff) + signExtend12 (1 : BitVec 12) =
      regionBase + BitVec.ofNat 64 srcOffA)
    (hoffA : srcOffA < bs.length)
    (hoverA : regionBase.toNat + srcOffA < 2 ^ 64)
    (hvalidA : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOffA) = true)
    (hssA : ¬ BitVec.ult ((bs[srcOffA]'hoffA).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffA]'hoffA).zeroExtend 64) (0xb8 : Word) = true →
        srcOffA + 1 < bs.length ∧ regionBase.toNat + (srcOffA + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA + 1)) = true)
    (hlsA : ¬ BitVec.ult ((bs[srcOffA]'hoffA).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffA]'hoffA).zeroExtend 64) (0xc0 : Word) = true →
        srcOffA + 1 + ((bs[srcOffA]'hoffA).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA + 1 +
          ((bs[srcOffA]'hoffA).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA]'hoffA).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA + 1 + k)) = true)
    (hllA : ¬ BitVec.ult ((bs[srcOffA]'hoffA).zeroExtend 64) (0xf8 : Word) = true →
        srcOffA + 1 + ((bs[srcOffA]'hoffA).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA + 1 +
          ((bs[srcOffA]'hoffA).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA]'hoffA).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA + 1 + k)) = true)
    (hdecA : ∃ next lenA : Word,
      rlpItemDecode bs srcOffA (regionBase + BitVec.ofNat 64 srcOffA)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenA)
    (hinbA : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffA)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (srcOffA1 : Nat)
    (hoffA1 : srcOffA1 < bs.length)
    (hoverA1 : regionBase.toNat + srcOffA1 < 2 ^ 64)
    (hvalidA1 : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOffA1) = true)
    (hssA1 : ¬ BitVec.ult ((bs[srcOffA1]'hoffA1).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffA1]'hoffA1).zeroExtend 64) (0xb8 : Word) = true →
        srcOffA1 + 1 < bs.length ∧ regionBase.toNat + (srcOffA1 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA1 + 1)) = true)
    (hlsA1 : ¬ BitVec.ult ((bs[srcOffA1]'hoffA1).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffA1]'hoffA1).zeroExtend 64) (0xc0 : Word) = true →
        srcOffA1 + 1 + ((bs[srcOffA1]'hoffA1).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA1 + 1 +
          ((bs[srcOffA1]'hoffA1).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA1]'hoffA1).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA1 + 1 + k)) = true)
    (hllA1 : ¬ BitVec.ult ((bs[srcOffA1]'hoffA1).zeroExtend 64) (0xf8 : Word) = true →
        srcOffA1 + 1 + ((bs[srcOffA1]'hoffA1).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA1 + 1 +
          ((bs[srcOffA1]'hoffA1).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA1]'hoffA1).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA1 + 1 + k)) = true)
    (hdecA1 : ∃ next lenA1 : Word,
      rlpItemDecode bs srcOffA1 (regionBase + BitVec.ofNat 64 srcOffA1)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenA1)
    (hinbA1 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffA1)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridgeA : ∀ nextA lenA : Word,
      rlpItemDecode bs srcOffA (regionBase + BitVec.ofNat 64 srcOffA)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) nextA lenA →
      nextA = regionBase + BitVec.ofNat 64 srcOffA1) :
    let s : TeerSaved :=
      { ra := ret, s0 := s0, s1 := s1, s2 := s2, s3 := s3, s4 := s4
        s5 := s5, s6 := s6, s7 := s7, s8 := s8, s9 := s9
        s10 := s10, s11 := s11, a5 := baiW }
    let innerVal := (teerTxTypeDispatch (txSlice bs off len)).2.2
    let listLen := lenW - innerVal
    let endL := (regionBase + BitVec.ofNat 64 listOff) + listLen
    let endW := endL
    let cursorV := regionBase + BitVec.ofNat 64 srcOffV
    cpsTripleWithin nFrontToAuthWalkNext1Save
      E AfterAuthWalkNext1Save teerLinkedEarly
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
      (teerAuthWalkNext1PostNested spC loadPtr lenW balPtr balLenW chainIdW
        s7 s11 spVal regionBase endL cursorV endW bs balBytes s innerVal
        srcOffA1) := by
  intro s innerVal listLen endL endW cursorV
  have hwn0 := teerAuthWalkNext0_applied ret spVal spC loadPtr lenW
    balPtr balLenW chainIdW baiW s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    regionBase bs balBytes off len hspC hnez hptr hlenW hsuccess htype4
    halign hbound hover hvalid0 listOff ha0 hoffL hoverL hvalidL hlenL
    h_ge h_hi h_exact srcOff0 hcur0 hoff0 hover0 hvalid0I hss0 hls0 hll0 hdec0 hinb0
    srcOff1 hoff1 hover1 hvalid1 hss1 hls1 hll1 hdec1 hinb1
    srcOff2 hoff2 hover2 hvalid2 hss2 hls2 hll2 hdec2 hinb2
    srcOff3 hoff3 hover3 hvalid3 hss3 hls3 hll3 hdec3 hinb3
    srcOff4 hoff4 hover4 hvalid4 hss4 hls4 hll4 hdec4 hinb4
    srcOff5 hoff5 hover5 hvalid5 hss5 hls5 hll5 hdec5 hinb5
    hbridge hbridge1 hbridge2 hbridge3 hbridge4
    srcOffV hoffV hoverV hvalidV hssV hlsV hllV hdecV hinbV hbridge5
    srcOffA hcurA hoffA hoverA hvalidA hssA hlsA hllA hdecA hinbA
  let Flat (p : Word × Word) : Assertion :=
    teerAuthWalkNext0FlatRest spC loadPtr lenW balPtr balLenW chainIdW
      s7 s11 spVal regionBase endL cursorV endW bs balBytes s
      innerVal p.1 p.2 **
    ⌜rlpItemDecode bs srcOffA (regionBase + BitVec.ofNat 64 srcOffA)
      endL p.1 p.2⌝
  have hwn0E :
      cpsTripleWithin nFrontToAuthWalkNext0SavePub E AfterAuthWalkNext0Save
        teerLinkedEarly
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
    dsimp only [Flat, teerAuthWalkNext0FlatRest]
    xperm_hyp hq'
  have hstep (p : Word × Word) :
      cpsTripleWithin nAuthWalkNextCycle AfterAuthWalkNext0Save AfterAuthWalkNext1Save
        teerLinkedEarly (Flat p)
        (teerAuthWalkNext1PostNested spC loadPtr lenW balPtr balLenW chainIdW
          s7 s11 spVal regionBase endL cursorV endW bs balBytes s innerVal
          srcOffA1) := by
    dsimp only [Flat]
    have hswap :
        cpsTripleWithin nAuthWalkNextCycle AfterAuthWalkNext0Save AfterAuthWalkNext1Save
          teerLinkedEarly
          (⌜rlpItemDecode bs srcOffA (regionBase + BitVec.ofNat 64 srcOffA)
              endL p.1 p.2⌝ **
            teerAuthWalkNext0FlatRest spC loadPtr lenW balPtr balLenW chainIdW
              s7 s11 spVal regionBase endL cursorV endW bs balBytes s
              innerVal p.1 p.2)
          (teerAuthWalkNext1PostNested spC loadPtr lenW balPtr balLenW chainIdW
            s7 s11 spVal regionBase endL cursorV endW bs balBytes s innerVal
            srcOffA1) := by
      refine cpsTripleWithin_pure_pre (fun hpure => ?_)
      have hcur1 : p.1 = regionBase + BitVec.ofNat 64 srcOffA1 :=
        hbridgeA p.1 p.2 (by simpa [endL, innerVal, listLen] using hpure)
      have hcy := teerAuthWalkNext1CycleOk_ownTemps regionBase endL bs srcOffA1
        LinkAuthWalkNext0 p.1 endL p.1 (0 : Word) p.2
        (by simpa using halign) hoffA1 hoverA1 hvalidA1 hssA1 hlsA1 hllA1
        hdecA1 hinbA1 hcur1 rfl
      have hcyF := cpsTripleWithin_frameR
        (teerAuthWalkNextSkipAmbient spC loadPtr lenW balPtr balLenW chainIdW
          s7 s11 spVal cursorV endW balBytes s innerVal)
        (by exact pcFree_teerAuthWalkNextSkipAmbient _ _ _ _ _ _ _ _ _ _ _ _ _ _) hcy
      have hcyF' :
          cpsTripleWithin nAuthWalkNextCycle AfterAuthWalkNext0Save
            AfterAuthWalkNext1Save teerLinkedEarly
            (teerAuthWalkNextSkipFocus regionBase bs
                LinkAuthWalkNext0 p.1 endL p.1 (0 : Word) p.2 **
              teerAuthWalkNextSkipAmbient spC loadPtr lenW balPtr balLenW chainIdW
                s7 s11 spVal cursorV endW balBytes s innerVal)
            (teerAuthWalkNext1PostNested spC loadPtr lenW balPtr balLenW chainIdW
              s7 s11 spVal regionBase endL cursorV endW bs balBytes s innerVal
              srcOffA1) := by
        refine cpsTripleWithin_weaken
          (fun _ hp => by
            unfold teerAuthWalkNextSkipFocus teerAuthWalkNext0Focus at hp
            xperm_hyp hp)
          (fun h hq => by
            unfold teerAuthWalkNext1PostNested
            obtain ⟨h1, h2, hd, hu, hEx, hA⟩ := hq
            obtain ⟨next, len1, hB⟩ := hEx
            exact ⟨next, len1, h1, h2, hd, hu, hB, hA⟩)
          hcyF
      exact cpsTripleWithin_weaken
        (teerAuthWalkNext0FlatRest_to_awn1Pre spC loadPtr lenW balPtr balLenW
          chainIdW s7 s11 spVal regionBase endL cursorV endW bs balBytes s
          innerVal p.1 p.2)
        (fun _ hq => hq) hcyF'
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => hq) hswap
  have hseq := cpsTripleWithin_seq_exists_same_cr hwn0E hstep
  exact cpsTripleWithin_mono_nSteps
    (by decide :
      nFrontToAuthWalkNext0SavePub + nAuthWalkNextCycle ≤ nFrontToAuthWalkNext1Save)
    hseq

set_option maxRecDepth 8000 in
/-- Flatten nested → applied-style AfterAuthWalkNext1Save post. -/
theorem teerAuthWalkNext1_applied
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
    (srcOff2 : Nat)
    (hoff2 : srcOff2 < bs.length)
    (hover2 : regionBase.toNat + srcOff2 < 2 ^ 64)
    (hvalid2 : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOff2) = true)
    (hss2 : ¬ BitVec.ult ((bs[srcOff2]'hoff2).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff2]'hoff2).zeroExtend 64) (0xb8 : Word) = true →
        srcOff2 + 1 < bs.length ∧ regionBase.toNat + (srcOff2 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff2 + 1)) = true)
    (hls2 : ¬ BitVec.ult ((bs[srcOff2]'hoff2).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff2]'hoff2).zeroExtend 64) (0xc0 : Word) = true →
        srcOff2 + 1 + ((bs[srcOff2]'hoff2).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff2 + 1 +
          ((bs[srcOff2]'hoff2).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff2]'hoff2).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff2 + 1 + k)) = true)
    (hll2 : ¬ BitVec.ult ((bs[srcOff2]'hoff2).zeroExtend 64) (0xf8 : Word) = true →
        srcOff2 + 1 + ((bs[srcOff2]'hoff2).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff2 + 1 +
          ((bs[srcOff2]'hoff2).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff2]'hoff2).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff2 + 1 + k)) = true)
    (hdec2 : ∃ next len2 : Word,
      rlpItemDecode bs srcOff2 (regionBase + BitVec.ofNat 64 srcOff2)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next len2)
    (hinb2 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOff2)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (srcOff3 : Nat)
    (hoff3 : srcOff3 < bs.length)
    (hover3 : regionBase.toNat + srcOff3 < 2 ^ 64)
    (hvalid3 : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOff3) = true)
    (hss3 : ¬ BitVec.ult ((bs[srcOff3]'hoff3).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff3]'hoff3).zeroExtend 64) (0xb8 : Word) = true →
        srcOff3 + 1 < bs.length ∧ regionBase.toNat + (srcOff3 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff3 + 1)) = true)
    (hls3 : ¬ BitVec.ult ((bs[srcOff3]'hoff3).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff3]'hoff3).zeroExtend 64) (0xc0 : Word) = true →
        srcOff3 + 1 + ((bs[srcOff3]'hoff3).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff3 + 1 +
          ((bs[srcOff3]'hoff3).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff3]'hoff3).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff3 + 1 + k)) = true)
    (hll3 : ¬ BitVec.ult ((bs[srcOff3]'hoff3).zeroExtend 64) (0xf8 : Word) = true →
        srcOff3 + 1 + ((bs[srcOff3]'hoff3).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff3 + 1 +
          ((bs[srcOff3]'hoff3).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff3]'hoff3).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff3 + 1 + k)) = true)
    (hdec3 : ∃ next len3 : Word,
      rlpItemDecode bs srcOff3 (regionBase + BitVec.ofNat 64 srcOff3)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next len3)
    (hinb3 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOff3)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (srcOff4 : Nat)
    (hoff4 : srcOff4 < bs.length)
    (hover4 : regionBase.toNat + srcOff4 < 2 ^ 64)
    (hvalid4 : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOff4) = true)
    (hss4 : ¬ BitVec.ult ((bs[srcOff4]'hoff4).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff4]'hoff4).zeroExtend 64) (0xb8 : Word) = true →
        srcOff4 + 1 < bs.length ∧ regionBase.toNat + (srcOff4 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff4 + 1)) = true)
    (hls4 : ¬ BitVec.ult ((bs[srcOff4]'hoff4).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff4]'hoff4).zeroExtend 64) (0xc0 : Word) = true →
        srcOff4 + 1 + ((bs[srcOff4]'hoff4).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff4 + 1 +
          ((bs[srcOff4]'hoff4).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff4]'hoff4).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff4 + 1 + k)) = true)
    (hll4 : ¬ BitVec.ult ((bs[srcOff4]'hoff4).zeroExtend 64) (0xf8 : Word) = true →
        srcOff4 + 1 + ((bs[srcOff4]'hoff4).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff4 + 1 +
          ((bs[srcOff4]'hoff4).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff4]'hoff4).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff4 + 1 + k)) = true)
    (hdec4 : ∃ next len4 : Word,
      rlpItemDecode bs srcOff4 (regionBase + BitVec.ofNat 64 srcOff4)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next len4)
    (hinb4 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOff4)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (srcOff5 : Nat)
    (hoff5 : srcOff5 < bs.length)
    (hover5 : regionBase.toNat + srcOff5 < 2 ^ 64)
    (hvalid5 : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOff5) = true)
    (hss5 : ¬ BitVec.ult ((bs[srcOff5]'hoff5).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff5]'hoff5).zeroExtend 64) (0xb8 : Word) = true →
        srcOff5 + 1 < bs.length ∧ regionBase.toNat + (srcOff5 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff5 + 1)) = true)
    (hls5 : ¬ BitVec.ult ((bs[srcOff5]'hoff5).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff5]'hoff5).zeroExtend 64) (0xc0 : Word) = true →
        srcOff5 + 1 + ((bs[srcOff5]'hoff5).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff5 + 1 +
          ((bs[srcOff5]'hoff5).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff5]'hoff5).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff5 + 1 + k)) = true)
    (hll5 : ¬ BitVec.ult ((bs[srcOff5]'hoff5).zeroExtend 64) (0xf8 : Word) = true →
        srcOff5 + 1 + ((bs[srcOff5]'hoff5).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff5 + 1 +
          ((bs[srcOff5]'hoff5).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff5]'hoff5).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff5 + 1 + k)) = true)
    (hdec5 : ∃ next len5 : Word,
      rlpItemDecode bs srcOff5 (regionBase + BitVec.ofNat 64 srcOff5)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next len5)
    (hinb5 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOff5)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridge : ∀ next0 len0 : Word,
      rlpItemDecode bs srcOff0 (regionBase + BitVec.ofNat 64 srcOff0)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next0 len0 →
      next0 = regionBase + BitVec.ofNat 64 srcOff1)
    (hbridge1 : ∀ next1 len1 : Word,
      rlpItemDecode bs srcOff1 (regionBase + BitVec.ofNat 64 srcOff1)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next1 len1 →
      next1 = regionBase + BitVec.ofNat 64 srcOff2)
    (hbridge2 : ∀ next2 len2 : Word,
      rlpItemDecode bs srcOff2 (regionBase + BitVec.ofNat 64 srcOff2)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next2 len2 →
      next2 = regionBase + BitVec.ofNat 64 srcOff3)
    (hbridge3 : ∀ next3 len3 : Word,
      rlpItemDecode bs srcOff3 (regionBase + BitVec.ofNat 64 srcOff3)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next3 len3 →
      next3 = regionBase + BitVec.ofNat 64 srcOff4)
    (hbridge4 : ∀ next4 len4 : Word,
      rlpItemDecode bs srcOff4 (regionBase + BitVec.ofNat 64 srcOff4)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next4 len4 →
      next4 = regionBase + BitVec.ofNat 64 srcOff5)
    (srcOffV : Nat)
    (hoffV : srcOffV < bs.length)
    (hoverV : regionBase.toNat + srcOffV < 2 ^ 64)
    (hvalidV : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOffV) = true)
    (hssV : ¬ BitVec.ult ((bs[srcOffV]'hoffV).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffV]'hoffV).zeroExtend 64) (0xb8 : Word) = true →
        srcOffV + 1 < bs.length ∧ regionBase.toNat + (srcOffV + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffV + 1)) = true)
    (hlsV : ¬ BitVec.ult ((bs[srcOffV]'hoffV).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffV]'hoffV).zeroExtend 64) (0xc0 : Word) = true →
        srcOffV + 1 + ((bs[srcOffV]'hoffV).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffV + 1 +
          ((bs[srcOffV]'hoffV).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffV]'hoffV).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffV + 1 + k)) = true)
    (hllV : ¬ BitVec.ult ((bs[srcOffV]'hoffV).zeroExtend 64) (0xf8 : Word) = true →
        srcOffV + 1 + ((bs[srcOffV]'hoffV).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffV + 1 +
          ((bs[srcOffV]'hoffV).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffV]'hoffV).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffV + 1 + k)) = true)
    (hdecV : ∃ next lenV : Word,
      rlpItemDecode bs srcOffV (regionBase + BitVec.ofNat 64 srcOffV)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenV)
    (hinbV : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffV)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridge5 : ∀ next5 len5 : Word,
      rlpItemDecode bs srcOff5 (regionBase + BitVec.ofNat 64 srcOff5)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next5 len5 →
      next5 = regionBase + BitVec.ofNat 64 srcOffV) 
    -- auth walk_next0 item
    (srcOffA : Nat)
    (hcurA : (regionBase + BitVec.ofNat 64 listOff) + signExtend12 (1 : BitVec 12) =
      regionBase + BitVec.ofNat 64 srcOffA)
    (hoffA : srcOffA < bs.length)
    (hoverA : regionBase.toNat + srcOffA < 2 ^ 64)
    (hvalidA : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOffA) = true)
    (hssA : ¬ BitVec.ult ((bs[srcOffA]'hoffA).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffA]'hoffA).zeroExtend 64) (0xb8 : Word) = true →
        srcOffA + 1 < bs.length ∧ regionBase.toNat + (srcOffA + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA + 1)) = true)
    (hlsA : ¬ BitVec.ult ((bs[srcOffA]'hoffA).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffA]'hoffA).zeroExtend 64) (0xc0 : Word) = true →
        srcOffA + 1 + ((bs[srcOffA]'hoffA).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA + 1 +
          ((bs[srcOffA]'hoffA).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA]'hoffA).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA + 1 + k)) = true)
    (hllA : ¬ BitVec.ult ((bs[srcOffA]'hoffA).zeroExtend 64) (0xf8 : Word) = true →
        srcOffA + 1 + ((bs[srcOffA]'hoffA).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA + 1 +
          ((bs[srcOffA]'hoffA).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA]'hoffA).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA + 1 + k)) = true)
    (hdecA : ∃ next lenA : Word,
      rlpItemDecode bs srcOffA (regionBase + BitVec.ofNat 64 srcOffA)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenA)
    (hinbA : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffA)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (srcOffA1 : Nat)
    (hoffA1 : srcOffA1 < bs.length)
    (hoverA1 : regionBase.toNat + srcOffA1 < 2 ^ 64)
    (hvalidA1 : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOffA1) = true)
    (hssA1 : ¬ BitVec.ult ((bs[srcOffA1]'hoffA1).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffA1]'hoffA1).zeroExtend 64) (0xb8 : Word) = true →
        srcOffA1 + 1 < bs.length ∧ regionBase.toNat + (srcOffA1 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA1 + 1)) = true)
    (hlsA1 : ¬ BitVec.ult ((bs[srcOffA1]'hoffA1).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffA1]'hoffA1).zeroExtend 64) (0xc0 : Word) = true →
        srcOffA1 + 1 + ((bs[srcOffA1]'hoffA1).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA1 + 1 +
          ((bs[srcOffA1]'hoffA1).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA1]'hoffA1).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA1 + 1 + k)) = true)
    (hllA1 : ¬ BitVec.ult ((bs[srcOffA1]'hoffA1).zeroExtend 64) (0xf8 : Word) = true →
        srcOffA1 + 1 + ((bs[srcOffA1]'hoffA1).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA1 + 1 +
          ((bs[srcOffA1]'hoffA1).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA1]'hoffA1).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA1 + 1 + k)) = true)
    (hdecA1 : ∃ next lenA1 : Word,
      rlpItemDecode bs srcOffA1 (regionBase + BitVec.ofNat 64 srcOffA1)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenA1)
    (hinbA1 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffA1)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridgeA : ∀ nextA lenA : Word,
      rlpItemDecode bs srcOffA (regionBase + BitVec.ofNat 64 srcOffA)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) nextA lenA →
      nextA = regionBase + BitVec.ofNat 64 srcOffA1) :
    let s : TeerSaved :=
      { ra := ret, s0 := s0, s1 := s1, s2 := s2, s3 := s3, s4 := s4
        s5 := s5, s6 := s6, s7 := s7, s8 := s8, s9 := s9
        s10 := s10, s11 := s11, a5 := baiW }
    let innerVal := (teerTxTypeDispatch (txSlice bs off len)).2.2
    let listLen := lenW - innerVal
    let endL := (regionBase + BitVec.ofNat 64 listOff) + listLen
    let endW := endL
    let cursorV := regionBase + BitVec.ofNat 64 srcOffV
    cpsTripleWithin nFrontToAuthWalkNext1Save
      E AfterAuthWalkNext1Save teerLinkedEarly
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
          (.x1 ↦ᵣ LinkAuthWalkNext1) **
          (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
          (.x18 ↦ᵣ balPtr) ** (.x19 ↦ᵣ balLenW) ** (.x20 ↦ᵣ chainIdW) **
          (.x21 ↦ᵣ next) ** (.x22 ↦ᵣ endL) **
          (.x23 ↦ᵣ s7) **
          (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len1) **
          (.x24 ↦ᵣ cursorV) ** (.x25 ↦ᵣ endW) **
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
          memOwn RecipientPtrAddr ** memOwn RecipientLenAddr **
          memOwn ValueNonzeroAddr **
          teerScratchWithoutVnzOwn **
          ⌜rlpItemDecode bs srcOffA1 (regionBase + BitVec.ofNat 64 srcOffA1)
            endL next len1⌝) h) := by
  intro s innerVal listLen endL endW cursorV
  have h0 := teerAuthWalkNext1_applied_nested ret spVal spC loadPtr lenW
    balPtr balLenW chainIdW baiW s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    regionBase bs balBytes off len hspC hnez hptr hlenW hsuccess htype4
    halign hbound hover hvalid0 listOff ha0 hoffL hoverL hvalidL hlenL
    h_ge h_hi h_exact srcOff0 hcur0 hoff0 hover0 hvalid0I hss0 hls0 hll0 hdec0 hinb0
    srcOff1 hoff1 hover1 hvalid1 hss1 hls1 hll1 hdec1 hinb1
    srcOff2 hoff2 hover2 hvalid2 hss2 hls2 hll2 hdec2 hinb2
    srcOff3 hoff3 hover3 hvalid3 hss3 hls3 hll3 hdec3 hinb3
    srcOff4 hoff4 hover4 hvalid4 hss4 hls4 hll4 hdec4 hinb4
    srcOff5 hoff5 hover5 hvalid5 hss5 hls5 hll5 hdec5 hinb5
    hbridge hbridge1 hbridge2 hbridge3 hbridge4
    srcOffV hoffV hoverV hvalidV hssV hlsV hllV hdecV hinbV hbridge5
    srcOffA hcurA hoffA hoverA hvalidA hssA hlsA hllA hdecA hinbA
    srcOffA1 hoffA1 hoverA1 hvalidA1 hssA1 hlsA1 hllA1 hdecA1 hinbA1 hbridgeA
  exact cpsTripleWithin_weaken (fun _ hp => hp)
    (fun h hq => by
      unfold teerAuthWalkNext1PostNested teerAuthWalkNextSkipBodyPost
        teerAuthWalkNextSkipAmbient teerAuthWalkNext0Ambient at hq
      obtain ⟨next, len1, hq'⟩ := hq
      refine ⟨next, len1, ?_⟩
      xperm_hyp hq') h0

#print axioms teerAuthWalkNext1CycleOk_ownTemps
#print axioms teerAuthWalkNext1_applied_nested
#print axioms teerAuthWalkNext1_applied


abbrev teerAuthWalkNextSkipAmbientIs := teerAuthWalkNext0AmbientIs

theorem pcFree_teerAuthWalkNextSkipAmbientIs
    (spC loadPtr lenW balPtr balLenW chainIdW
      s7 s11 spVal cursorV endWV : Word)
    (balBytes : List (BitVec 8)) (s : TeerSaved)
    (innerVal : Word) :
    (teerAuthWalkNextSkipAmbientIs spC loadPtr lenW balPtr balLenW chainIdW
      s7 s11 spVal cursorV endWV balBytes s innerVal).pcFree := by
  unfold teerAuthWalkNextSkipAmbientIs teerAuthWalkNext0AmbientIs
    teerScratchZeroIs teerScratchRestWithoutVnzOwn; pcf

/-- Rest of AfterAuthWalkNext0Save flat without trailing pure. -/
def teerAuthWalkNext0FlatRestIs
    (spC loadPtr lenW balPtr balLenW chainIdW
      s7 s11 spVal regionBase endL cursorV endWV : Word)
    (bs balBytes : List (BitVec 8)) (s : TeerSaved)
    (innerVal next0 len0 : Word) : Assertion :=
  (.x2 ↦ᵣ spC) **
    (.x1 ↦ᵣ LinkAuthWalkNext0) **
    (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
    (.x18 ↦ᵣ balPtr) ** (.x19 ↦ᵣ balLenW) ** (.x20 ↦ᵣ chainIdW) **
    (.x21 ↦ᵣ next0) ** (.x22 ↦ᵣ endL) **
    (.x23 ↦ᵣ s7) **
    (.x10 ↦ᵣ next0) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len0) **
    (.x24 ↦ᵣ cursorV) ** (.x25 ↦ᵣ endWV) **
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
    memOwn RecipientPtrAddr ** memOwn RecipientLenAddr **
    memOwn ValueNonzeroAddr **
    teerScratchZeroIs ** teerScratchRestWithoutVnzOwn

theorem teerAuthWalkNext0FlatRestIs_to_awn1Pre
    (spC loadPtr lenW balPtr balLenW chainIdW
      s7 s11 spVal regionBase endL cursorV endWV : Word)
    (bs balBytes : List (BitVec 8)) (s : TeerSaved)
    (innerVal next0 len0 : Word) :
    ∀ h,
      (teerAuthWalkNext0FlatRestIs spC loadPtr lenW balPtr balLenW chainIdW
          s7 s11 spVal regionBase endL cursorV endWV bs balBytes s
          innerVal next0 len0) h →
      (teerAuthWalkNextSkipFocus regionBase bs
          LinkAuthWalkNext0 next0 endL next0 (0 : Word) len0 **
        teerAuthWalkNextSkipAmbientIs spC loadPtr lenW balPtr balLenW chainIdW
          s7 s11 spVal cursorV endWV balBytes s innerVal) h := by
  intro h hp
  unfold teerAuthWalkNext0FlatRestIs at hp
  unfold teerAuthWalkNextSkipFocus teerAuthWalkNext0Focus teerAuthWalkNext0BodyCore
    teerAuthWalkNextSkipAmbientIs teerAuthWalkNext0AmbientIs
  xperm_hyp hp

def teerAuthWalkNext1PostNestedIs
    (spC loadPtr lenW balPtr balLenW chainIdW
      s7 s11 spVal regionBase endL cursorV endWV : Word)
    (bs balBytes : List (BitVec 8)) (s : TeerSaved)
    (innerVal : Word) (srcOffA1 : Nat) : Assertion :=
  fun h => ∃ next len : Word,
    (teerAuthWalkNextSkipBodyPost regionBase endL next len bs srcOffA1
        LinkAuthWalkNext1 **
      teerAuthWalkNextSkipAmbientIs spC loadPtr lenW balPtr balLenW chainIdW
        s7 s11 spVal cursorV endWV balBytes s innerVal) h

set_option maxRecDepth 8000 in
theorem teerAuthWalkNext1_applied_nested_is
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
    (srcOff2 : Nat)
    (hoff2 : srcOff2 < bs.length)
    (hover2 : regionBase.toNat + srcOff2 < 2 ^ 64)
    (hvalid2 : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOff2) = true)
    (hss2 : ¬ BitVec.ult ((bs[srcOff2]'hoff2).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff2]'hoff2).zeroExtend 64) (0xb8 : Word) = true →
        srcOff2 + 1 < bs.length ∧ regionBase.toNat + (srcOff2 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff2 + 1)) = true)
    (hls2 : ¬ BitVec.ult ((bs[srcOff2]'hoff2).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff2]'hoff2).zeroExtend 64) (0xc0 : Word) = true →
        srcOff2 + 1 + ((bs[srcOff2]'hoff2).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff2 + 1 +
          ((bs[srcOff2]'hoff2).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff2]'hoff2).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff2 + 1 + k)) = true)
    (hll2 : ¬ BitVec.ult ((bs[srcOff2]'hoff2).zeroExtend 64) (0xf8 : Word) = true →
        srcOff2 + 1 + ((bs[srcOff2]'hoff2).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff2 + 1 +
          ((bs[srcOff2]'hoff2).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff2]'hoff2).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff2 + 1 + k)) = true)
    (hdec2 : ∃ next len2 : Word,
      rlpItemDecode bs srcOff2 (regionBase + BitVec.ofNat 64 srcOff2)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next len2)
    (hinb2 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOff2)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (srcOff3 : Nat)
    (hoff3 : srcOff3 < bs.length)
    (hover3 : regionBase.toNat + srcOff3 < 2 ^ 64)
    (hvalid3 : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOff3) = true)
    (hss3 : ¬ BitVec.ult ((bs[srcOff3]'hoff3).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff3]'hoff3).zeroExtend 64) (0xb8 : Word) = true →
        srcOff3 + 1 < bs.length ∧ regionBase.toNat + (srcOff3 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff3 + 1)) = true)
    (hls3 : ¬ BitVec.ult ((bs[srcOff3]'hoff3).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff3]'hoff3).zeroExtend 64) (0xc0 : Word) = true →
        srcOff3 + 1 + ((bs[srcOff3]'hoff3).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff3 + 1 +
          ((bs[srcOff3]'hoff3).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff3]'hoff3).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff3 + 1 + k)) = true)
    (hll3 : ¬ BitVec.ult ((bs[srcOff3]'hoff3).zeroExtend 64) (0xf8 : Word) = true →
        srcOff3 + 1 + ((bs[srcOff3]'hoff3).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff3 + 1 +
          ((bs[srcOff3]'hoff3).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff3]'hoff3).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff3 + 1 + k)) = true)
    (hdec3 : ∃ next len3 : Word,
      rlpItemDecode bs srcOff3 (regionBase + BitVec.ofNat 64 srcOff3)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next len3)
    (hinb3 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOff3)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (srcOff4 : Nat)
    (hoff4 : srcOff4 < bs.length)
    (hover4 : regionBase.toNat + srcOff4 < 2 ^ 64)
    (hvalid4 : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOff4) = true)
    (hss4 : ¬ BitVec.ult ((bs[srcOff4]'hoff4).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff4]'hoff4).zeroExtend 64) (0xb8 : Word) = true →
        srcOff4 + 1 < bs.length ∧ regionBase.toNat + (srcOff4 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff4 + 1)) = true)
    (hls4 : ¬ BitVec.ult ((bs[srcOff4]'hoff4).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff4]'hoff4).zeroExtend 64) (0xc0 : Word) = true →
        srcOff4 + 1 + ((bs[srcOff4]'hoff4).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff4 + 1 +
          ((bs[srcOff4]'hoff4).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff4]'hoff4).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff4 + 1 + k)) = true)
    (hll4 : ¬ BitVec.ult ((bs[srcOff4]'hoff4).zeroExtend 64) (0xf8 : Word) = true →
        srcOff4 + 1 + ((bs[srcOff4]'hoff4).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff4 + 1 +
          ((bs[srcOff4]'hoff4).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff4]'hoff4).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff4 + 1 + k)) = true)
    (hdec4 : ∃ next len4 : Word,
      rlpItemDecode bs srcOff4 (regionBase + BitVec.ofNat 64 srcOff4)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next len4)
    (hinb4 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOff4)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (srcOff5 : Nat)
    (hoff5 : srcOff5 < bs.length)
    (hover5 : regionBase.toNat + srcOff5 < 2 ^ 64)
    (hvalid5 : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOff5) = true)
    (hss5 : ¬ BitVec.ult ((bs[srcOff5]'hoff5).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff5]'hoff5).zeroExtend 64) (0xb8 : Word) = true →
        srcOff5 + 1 < bs.length ∧ regionBase.toNat + (srcOff5 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff5 + 1)) = true)
    (hls5 : ¬ BitVec.ult ((bs[srcOff5]'hoff5).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff5]'hoff5).zeroExtend 64) (0xc0 : Word) = true →
        srcOff5 + 1 + ((bs[srcOff5]'hoff5).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff5 + 1 +
          ((bs[srcOff5]'hoff5).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff5]'hoff5).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff5 + 1 + k)) = true)
    (hll5 : ¬ BitVec.ult ((bs[srcOff5]'hoff5).zeroExtend 64) (0xf8 : Word) = true →
        srcOff5 + 1 + ((bs[srcOff5]'hoff5).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff5 + 1 +
          ((bs[srcOff5]'hoff5).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff5]'hoff5).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff5 + 1 + k)) = true)
    (hdec5 : ∃ next len5 : Word,
      rlpItemDecode bs srcOff5 (regionBase + BitVec.ofNat 64 srcOff5)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next len5)
    (hinb5 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOff5)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridge : ∀ next0 len0 : Word,
      rlpItemDecode bs srcOff0 (regionBase + BitVec.ofNat 64 srcOff0)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next0 len0 →
      next0 = regionBase + BitVec.ofNat 64 srcOff1)
    (hbridge1 : ∀ next1 len1 : Word,
      rlpItemDecode bs srcOff1 (regionBase + BitVec.ofNat 64 srcOff1)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next1 len1 →
      next1 = regionBase + BitVec.ofNat 64 srcOff2)
    (hbridge2 : ∀ next2 len2 : Word,
      rlpItemDecode bs srcOff2 (regionBase + BitVec.ofNat 64 srcOff2)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next2 len2 →
      next2 = regionBase + BitVec.ofNat 64 srcOff3)
    (hbridge3 : ∀ next3 len3 : Word,
      rlpItemDecode bs srcOff3 (regionBase + BitVec.ofNat 64 srcOff3)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next3 len3 →
      next3 = regionBase + BitVec.ofNat 64 srcOff4)
    (hbridge4 : ∀ next4 len4 : Word,
      rlpItemDecode bs srcOff4 (regionBase + BitVec.ofNat 64 srcOff4)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next4 len4 →
      next4 = regionBase + BitVec.ofNat 64 srcOff5)
    (srcOffV : Nat)
    (hoffV : srcOffV < bs.length)
    (hoverV : regionBase.toNat + srcOffV < 2 ^ 64)
    (hvalidV : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOffV) = true)
    (hssV : ¬ BitVec.ult ((bs[srcOffV]'hoffV).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffV]'hoffV).zeroExtend 64) (0xb8 : Word) = true →
        srcOffV + 1 < bs.length ∧ regionBase.toNat + (srcOffV + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffV + 1)) = true)
    (hlsV : ¬ BitVec.ult ((bs[srcOffV]'hoffV).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffV]'hoffV).zeroExtend 64) (0xc0 : Word) = true →
        srcOffV + 1 + ((bs[srcOffV]'hoffV).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffV + 1 +
          ((bs[srcOffV]'hoffV).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffV]'hoffV).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffV + 1 + k)) = true)
    (hllV : ¬ BitVec.ult ((bs[srcOffV]'hoffV).zeroExtend 64) (0xf8 : Word) = true →
        srcOffV + 1 + ((bs[srcOffV]'hoffV).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffV + 1 +
          ((bs[srcOffV]'hoffV).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffV]'hoffV).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffV + 1 + k)) = true)
    (hdecV : ∃ next lenV : Word,
      rlpItemDecode bs srcOffV (regionBase + BitVec.ofNat 64 srcOffV)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenV)
    (hinbV : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffV)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridge5 : ∀ next5 len5 : Word,
      rlpItemDecode bs srcOff5 (regionBase + BitVec.ofNat 64 srcOff5)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next5 len5 →
      next5 = regionBase + BitVec.ofNat 64 srcOffV) 
    -- auth walk_next0 item
    (srcOffA : Nat)
    (hcurA : (regionBase + BitVec.ofNat 64 listOff) + signExtend12 (1 : BitVec 12) =
      regionBase + BitVec.ofNat 64 srcOffA)
    (hoffA : srcOffA < bs.length)
    (hoverA : regionBase.toNat + srcOffA < 2 ^ 64)
    (hvalidA : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOffA) = true)
    (hssA : ¬ BitVec.ult ((bs[srcOffA]'hoffA).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffA]'hoffA).zeroExtend 64) (0xb8 : Word) = true →
        srcOffA + 1 < bs.length ∧ regionBase.toNat + (srcOffA + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA + 1)) = true)
    (hlsA : ¬ BitVec.ult ((bs[srcOffA]'hoffA).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffA]'hoffA).zeroExtend 64) (0xc0 : Word) = true →
        srcOffA + 1 + ((bs[srcOffA]'hoffA).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA + 1 +
          ((bs[srcOffA]'hoffA).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA]'hoffA).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA + 1 + k)) = true)
    (hllA : ¬ BitVec.ult ((bs[srcOffA]'hoffA).zeroExtend 64) (0xf8 : Word) = true →
        srcOffA + 1 + ((bs[srcOffA]'hoffA).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA + 1 +
          ((bs[srcOffA]'hoffA).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA]'hoffA).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA + 1 + k)) = true)
    (hdecA : ∃ next lenA : Word,
      rlpItemDecode bs srcOffA (regionBase + BitVec.ofNat 64 srcOffA)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenA)
    (hinbA : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffA)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (srcOffA1 : Nat)
    (hoffA1 : srcOffA1 < bs.length)
    (hoverA1 : regionBase.toNat + srcOffA1 < 2 ^ 64)
    (hvalidA1 : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOffA1) = true)
    (hssA1 : ¬ BitVec.ult ((bs[srcOffA1]'hoffA1).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffA1]'hoffA1).zeroExtend 64) (0xb8 : Word) = true →
        srcOffA1 + 1 < bs.length ∧ regionBase.toNat + (srcOffA1 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA1 + 1)) = true)
    (hlsA1 : ¬ BitVec.ult ((bs[srcOffA1]'hoffA1).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffA1]'hoffA1).zeroExtend 64) (0xc0 : Word) = true →
        srcOffA1 + 1 + ((bs[srcOffA1]'hoffA1).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA1 + 1 +
          ((bs[srcOffA1]'hoffA1).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA1]'hoffA1).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA1 + 1 + k)) = true)
    (hllA1 : ¬ BitVec.ult ((bs[srcOffA1]'hoffA1).zeroExtend 64) (0xf8 : Word) = true →
        srcOffA1 + 1 + ((bs[srcOffA1]'hoffA1).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA1 + 1 +
          ((bs[srcOffA1]'hoffA1).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA1]'hoffA1).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA1 + 1 + k)) = true)
    (hdecA1 : ∃ next lenA1 : Word,
      rlpItemDecode bs srcOffA1 (regionBase + BitVec.ofNat 64 srcOffA1)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenA1)
    (hinbA1 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffA1)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridgeA : ∀ nextA lenA : Word,
      rlpItemDecode bs srcOffA (regionBase + BitVec.ofNat 64 srcOffA)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) nextA lenA →
      nextA = regionBase + BitVec.ofNat 64 srcOffA1) :
    let s : TeerSaved :=
      { ra := ret, s0 := s0, s1 := s1, s2 := s2, s3 := s3, s4 := s4
        s5 := s5, s6 := s6, s7 := s7, s8 := s8, s9 := s9
        s10 := s10, s11 := s11, a5 := baiW }
    let innerVal := (teerTxTypeDispatch (txSlice bs off len)).2.2
    let listLen := lenW - innerVal
    let endL := (regionBase + BitVec.ofNat 64 listOff) + listLen
    let endW := endL
    let cursorV := regionBase + BitVec.ofNat 64 srcOffV
    cpsTripleWithin nFrontToAuthWalkNext1Save
      E AfterAuthWalkNext1Save teerLinkedEarly
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
      (teerAuthWalkNext1PostNestedIs spC loadPtr lenW balPtr balLenW chainIdW
        s7 s11 spVal regionBase endL cursorV endW bs balBytes s innerVal
        srcOffA1) := by
  intro s innerVal listLen endL endW cursorV
  have hwn0 := teerAuthWalkNext0_applied_is ret spVal spC loadPtr lenW
    balPtr balLenW chainIdW baiW s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    regionBase bs balBytes off len hspC hnez hptr hlenW hsuccess htype4
    halign hbound hover hvalid0 listOff ha0 hoffL hoverL hvalidL hlenL
    h_ge h_hi h_exact srcOff0 hcur0 hoff0 hover0 hvalid0I hss0 hls0 hll0 hdec0 hinb0
    srcOff1 hoff1 hover1 hvalid1 hss1 hls1 hll1 hdec1 hinb1
    srcOff2 hoff2 hover2 hvalid2 hss2 hls2 hll2 hdec2 hinb2
    srcOff3 hoff3 hover3 hvalid3 hss3 hls3 hll3 hdec3 hinb3
    srcOff4 hoff4 hover4 hvalid4 hss4 hls4 hll4 hdec4 hinb4
    srcOff5 hoff5 hover5 hvalid5 hss5 hls5 hll5 hdec5 hinb5
    hbridge hbridge1 hbridge2 hbridge3 hbridge4
    srcOffV hoffV hoverV hvalidV hssV hlsV hllV hdecV hinbV hbridge5
    srcOffA hcurA hoffA hoverA hvalidA hssA hlsA hllA hdecA hinbA
  let Flat (p : Word × Word) : Assertion :=
    teerAuthWalkNext0FlatRestIs spC loadPtr lenW balPtr balLenW chainIdW
      s7 s11 spVal regionBase endL cursorV endW bs balBytes s
      innerVal p.1 p.2 **
    ⌜rlpItemDecode bs srcOffA (regionBase + BitVec.ofNat 64 srcOffA)
      endL p.1 p.2⌝
  have hwn0E :
      cpsTripleWithin nFrontToAuthWalkNext0SavePub E AfterAuthWalkNext0Save
        teerLinkedEarly
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
    dsimp only [Flat, teerAuthWalkNext0FlatRestIs]
    xperm_hyp hq'
  have hstep (p : Word × Word) :
      cpsTripleWithin nAuthWalkNextCycle AfterAuthWalkNext0Save AfterAuthWalkNext1Save
        teerLinkedEarly (Flat p)
        (teerAuthWalkNext1PostNestedIs spC loadPtr lenW balPtr balLenW chainIdW
          s7 s11 spVal regionBase endL cursorV endW bs balBytes s innerVal
          srcOffA1) := by
    dsimp only [Flat]
    have hswap :
        cpsTripleWithin nAuthWalkNextCycle AfterAuthWalkNext0Save AfterAuthWalkNext1Save
          teerLinkedEarly
          (⌜rlpItemDecode bs srcOffA (regionBase + BitVec.ofNat 64 srcOffA)
              endL p.1 p.2⌝ **
            teerAuthWalkNext0FlatRestIs spC loadPtr lenW balPtr balLenW chainIdW
              s7 s11 spVal regionBase endL cursorV endW bs balBytes s
              innerVal p.1 p.2)
          (teerAuthWalkNext1PostNestedIs spC loadPtr lenW balPtr balLenW chainIdW
            s7 s11 spVal regionBase endL cursorV endW bs balBytes s innerVal
            srcOffA1) := by
      refine cpsTripleWithin_pure_pre (fun hpure => ?_)
      have hcur1 : p.1 = regionBase + BitVec.ofNat 64 srcOffA1 :=
        hbridgeA p.1 p.2 (by simpa [endL, innerVal, listLen] using hpure)
      have hcy := teerAuthWalkNext1CycleOk_ownTemps regionBase endL bs srcOffA1
        LinkAuthWalkNext0 p.1 endL p.1 (0 : Word) p.2
        (by simpa using halign) hoffA1 hoverA1 hvalidA1 hssA1 hlsA1 hllA1
        hdecA1 hinbA1 hcur1 rfl
      have hcyF := cpsTripleWithin_frameR
        (teerAuthWalkNextSkipAmbientIs spC loadPtr lenW balPtr balLenW chainIdW
          s7 s11 spVal cursorV endW balBytes s innerVal)
        (by exact pcFree_teerAuthWalkNextSkipAmbientIs _ _ _ _ _ _ _ _ _ _ _ _ _ _) hcy
      have hcyF' :
          cpsTripleWithin nAuthWalkNextCycle AfterAuthWalkNext0Save
            AfterAuthWalkNext1Save teerLinkedEarly
            (teerAuthWalkNextSkipFocus regionBase bs
                LinkAuthWalkNext0 p.1 endL p.1 (0 : Word) p.2 **
              teerAuthWalkNextSkipAmbientIs spC loadPtr lenW balPtr balLenW chainIdW
                s7 s11 spVal cursorV endW balBytes s innerVal)
            (teerAuthWalkNext1PostNestedIs spC loadPtr lenW balPtr balLenW chainIdW
              s7 s11 spVal regionBase endL cursorV endW bs balBytes s innerVal
              srcOffA1) := by
        refine cpsTripleWithin_weaken
          (fun _ hp => by
            unfold teerAuthWalkNextSkipFocus teerAuthWalkNext0Focus at hp
            xperm_hyp hp)
          (fun h hq => by
            unfold teerAuthWalkNext1PostNestedIs
            obtain ⟨h1, h2, hd, hu, hEx, hA⟩ := hq
            obtain ⟨next, len1, hB⟩ := hEx
            exact ⟨next, len1, h1, h2, hd, hu, hB, hA⟩)
          hcyF
      exact cpsTripleWithin_weaken
        (teerAuthWalkNext0FlatRestIs_to_awn1Pre spC loadPtr lenW balPtr balLenW
          chainIdW s7 s11 spVal regionBase endL cursorV endW bs balBytes s
          innerVal p.1 p.2)
        (fun _ hq => hq) hcyF'
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => hq) hswap
  have hseq := cpsTripleWithin_seq_exists_same_cr hwn0E hstep
  exact cpsTripleWithin_mono_nSteps
    (by decide :
      nFrontToAuthWalkNext0SavePub + nAuthWalkNextCycle ≤ nFrontToAuthWalkNext1Save)
    hseq

set_option maxRecDepth 8000 in
/-- Flatten nested → applied-style AfterAuthWalkNext1Save post. -/
theorem teerAuthWalkNext1_applied_is
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
    (srcOff2 : Nat)
    (hoff2 : srcOff2 < bs.length)
    (hover2 : regionBase.toNat + srcOff2 < 2 ^ 64)
    (hvalid2 : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOff2) = true)
    (hss2 : ¬ BitVec.ult ((bs[srcOff2]'hoff2).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff2]'hoff2).zeroExtend 64) (0xb8 : Word) = true →
        srcOff2 + 1 < bs.length ∧ regionBase.toNat + (srcOff2 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff2 + 1)) = true)
    (hls2 : ¬ BitVec.ult ((bs[srcOff2]'hoff2).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff2]'hoff2).zeroExtend 64) (0xc0 : Word) = true →
        srcOff2 + 1 + ((bs[srcOff2]'hoff2).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff2 + 1 +
          ((bs[srcOff2]'hoff2).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff2]'hoff2).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff2 + 1 + k)) = true)
    (hll2 : ¬ BitVec.ult ((bs[srcOff2]'hoff2).zeroExtend 64) (0xf8 : Word) = true →
        srcOff2 + 1 + ((bs[srcOff2]'hoff2).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff2 + 1 +
          ((bs[srcOff2]'hoff2).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff2]'hoff2).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff2 + 1 + k)) = true)
    (hdec2 : ∃ next len2 : Word,
      rlpItemDecode bs srcOff2 (regionBase + BitVec.ofNat 64 srcOff2)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next len2)
    (hinb2 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOff2)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (srcOff3 : Nat)
    (hoff3 : srcOff3 < bs.length)
    (hover3 : regionBase.toNat + srcOff3 < 2 ^ 64)
    (hvalid3 : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOff3) = true)
    (hss3 : ¬ BitVec.ult ((bs[srcOff3]'hoff3).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff3]'hoff3).zeroExtend 64) (0xb8 : Word) = true →
        srcOff3 + 1 < bs.length ∧ regionBase.toNat + (srcOff3 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff3 + 1)) = true)
    (hls3 : ¬ BitVec.ult ((bs[srcOff3]'hoff3).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff3]'hoff3).zeroExtend 64) (0xc0 : Word) = true →
        srcOff3 + 1 + ((bs[srcOff3]'hoff3).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff3 + 1 +
          ((bs[srcOff3]'hoff3).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff3]'hoff3).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff3 + 1 + k)) = true)
    (hll3 : ¬ BitVec.ult ((bs[srcOff3]'hoff3).zeroExtend 64) (0xf8 : Word) = true →
        srcOff3 + 1 + ((bs[srcOff3]'hoff3).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff3 + 1 +
          ((bs[srcOff3]'hoff3).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff3]'hoff3).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff3 + 1 + k)) = true)
    (hdec3 : ∃ next len3 : Word,
      rlpItemDecode bs srcOff3 (regionBase + BitVec.ofNat 64 srcOff3)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next len3)
    (hinb3 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOff3)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (srcOff4 : Nat)
    (hoff4 : srcOff4 < bs.length)
    (hover4 : regionBase.toNat + srcOff4 < 2 ^ 64)
    (hvalid4 : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOff4) = true)
    (hss4 : ¬ BitVec.ult ((bs[srcOff4]'hoff4).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff4]'hoff4).zeroExtend 64) (0xb8 : Word) = true →
        srcOff4 + 1 < bs.length ∧ regionBase.toNat + (srcOff4 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff4 + 1)) = true)
    (hls4 : ¬ BitVec.ult ((bs[srcOff4]'hoff4).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff4]'hoff4).zeroExtend 64) (0xc0 : Word) = true →
        srcOff4 + 1 + ((bs[srcOff4]'hoff4).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff4 + 1 +
          ((bs[srcOff4]'hoff4).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff4]'hoff4).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff4 + 1 + k)) = true)
    (hll4 : ¬ BitVec.ult ((bs[srcOff4]'hoff4).zeroExtend 64) (0xf8 : Word) = true →
        srcOff4 + 1 + ((bs[srcOff4]'hoff4).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff4 + 1 +
          ((bs[srcOff4]'hoff4).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff4]'hoff4).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff4 + 1 + k)) = true)
    (hdec4 : ∃ next len4 : Word,
      rlpItemDecode bs srcOff4 (regionBase + BitVec.ofNat 64 srcOff4)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next len4)
    (hinb4 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOff4)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (srcOff5 : Nat)
    (hoff5 : srcOff5 < bs.length)
    (hover5 : regionBase.toNat + srcOff5 < 2 ^ 64)
    (hvalid5 : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOff5) = true)
    (hss5 : ¬ BitVec.ult ((bs[srcOff5]'hoff5).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff5]'hoff5).zeroExtend 64) (0xb8 : Word) = true →
        srcOff5 + 1 < bs.length ∧ regionBase.toNat + (srcOff5 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff5 + 1)) = true)
    (hls5 : ¬ BitVec.ult ((bs[srcOff5]'hoff5).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff5]'hoff5).zeroExtend 64) (0xc0 : Word) = true →
        srcOff5 + 1 + ((bs[srcOff5]'hoff5).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff5 + 1 +
          ((bs[srcOff5]'hoff5).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff5]'hoff5).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff5 + 1 + k)) = true)
    (hll5 : ¬ BitVec.ult ((bs[srcOff5]'hoff5).zeroExtend 64) (0xf8 : Word) = true →
        srcOff5 + 1 + ((bs[srcOff5]'hoff5).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff5 + 1 +
          ((bs[srcOff5]'hoff5).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff5]'hoff5).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff5 + 1 + k)) = true)
    (hdec5 : ∃ next len5 : Word,
      rlpItemDecode bs srcOff5 (regionBase + BitVec.ofNat 64 srcOff5)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next len5)
    (hinb5 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOff5)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridge : ∀ next0 len0 : Word,
      rlpItemDecode bs srcOff0 (regionBase + BitVec.ofNat 64 srcOff0)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next0 len0 →
      next0 = regionBase + BitVec.ofNat 64 srcOff1)
    (hbridge1 : ∀ next1 len1 : Word,
      rlpItemDecode bs srcOff1 (regionBase + BitVec.ofNat 64 srcOff1)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next1 len1 →
      next1 = regionBase + BitVec.ofNat 64 srcOff2)
    (hbridge2 : ∀ next2 len2 : Word,
      rlpItemDecode bs srcOff2 (regionBase + BitVec.ofNat 64 srcOff2)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next2 len2 →
      next2 = regionBase + BitVec.ofNat 64 srcOff3)
    (hbridge3 : ∀ next3 len3 : Word,
      rlpItemDecode bs srcOff3 (regionBase + BitVec.ofNat 64 srcOff3)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next3 len3 →
      next3 = regionBase + BitVec.ofNat 64 srcOff4)
    (hbridge4 : ∀ next4 len4 : Word,
      rlpItemDecode bs srcOff4 (regionBase + BitVec.ofNat 64 srcOff4)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next4 len4 →
      next4 = regionBase + BitVec.ofNat 64 srcOff5)
    (srcOffV : Nat)
    (hoffV : srcOffV < bs.length)
    (hoverV : regionBase.toNat + srcOffV < 2 ^ 64)
    (hvalidV : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOffV) = true)
    (hssV : ¬ BitVec.ult ((bs[srcOffV]'hoffV).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffV]'hoffV).zeroExtend 64) (0xb8 : Word) = true →
        srcOffV + 1 < bs.length ∧ regionBase.toNat + (srcOffV + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffV + 1)) = true)
    (hlsV : ¬ BitVec.ult ((bs[srcOffV]'hoffV).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffV]'hoffV).zeroExtend 64) (0xc0 : Word) = true →
        srcOffV + 1 + ((bs[srcOffV]'hoffV).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffV + 1 +
          ((bs[srcOffV]'hoffV).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffV]'hoffV).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffV + 1 + k)) = true)
    (hllV : ¬ BitVec.ult ((bs[srcOffV]'hoffV).zeroExtend 64) (0xf8 : Word) = true →
        srcOffV + 1 + ((bs[srcOffV]'hoffV).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffV + 1 +
          ((bs[srcOffV]'hoffV).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffV]'hoffV).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffV + 1 + k)) = true)
    (hdecV : ∃ next lenV : Word,
      rlpItemDecode bs srcOffV (regionBase + BitVec.ofNat 64 srcOffV)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenV)
    (hinbV : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffV)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridge5 : ∀ next5 len5 : Word,
      rlpItemDecode bs srcOff5 (regionBase + BitVec.ofNat 64 srcOff5)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next5 len5 →
      next5 = regionBase + BitVec.ofNat 64 srcOffV) 
    -- auth walk_next0 item
    (srcOffA : Nat)
    (hcurA : (regionBase + BitVec.ofNat 64 listOff) + signExtend12 (1 : BitVec 12) =
      regionBase + BitVec.ofNat 64 srcOffA)
    (hoffA : srcOffA < bs.length)
    (hoverA : regionBase.toNat + srcOffA < 2 ^ 64)
    (hvalidA : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOffA) = true)
    (hssA : ¬ BitVec.ult ((bs[srcOffA]'hoffA).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffA]'hoffA).zeroExtend 64) (0xb8 : Word) = true →
        srcOffA + 1 < bs.length ∧ regionBase.toNat + (srcOffA + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA + 1)) = true)
    (hlsA : ¬ BitVec.ult ((bs[srcOffA]'hoffA).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffA]'hoffA).zeroExtend 64) (0xc0 : Word) = true →
        srcOffA + 1 + ((bs[srcOffA]'hoffA).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA + 1 +
          ((bs[srcOffA]'hoffA).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA]'hoffA).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA + 1 + k)) = true)
    (hllA : ¬ BitVec.ult ((bs[srcOffA]'hoffA).zeroExtend 64) (0xf8 : Word) = true →
        srcOffA + 1 + ((bs[srcOffA]'hoffA).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA + 1 +
          ((bs[srcOffA]'hoffA).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA]'hoffA).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA + 1 + k)) = true)
    (hdecA : ∃ next lenA : Word,
      rlpItemDecode bs srcOffA (regionBase + BitVec.ofNat 64 srcOffA)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenA)
    (hinbA : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffA)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (srcOffA1 : Nat)
    (hoffA1 : srcOffA1 < bs.length)
    (hoverA1 : regionBase.toNat + srcOffA1 < 2 ^ 64)
    (hvalidA1 : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOffA1) = true)
    (hssA1 : ¬ BitVec.ult ((bs[srcOffA1]'hoffA1).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffA1]'hoffA1).zeroExtend 64) (0xb8 : Word) = true →
        srcOffA1 + 1 < bs.length ∧ regionBase.toNat + (srcOffA1 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA1 + 1)) = true)
    (hlsA1 : ¬ BitVec.ult ((bs[srcOffA1]'hoffA1).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffA1]'hoffA1).zeroExtend 64) (0xc0 : Word) = true →
        srcOffA1 + 1 + ((bs[srcOffA1]'hoffA1).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA1 + 1 +
          ((bs[srcOffA1]'hoffA1).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA1]'hoffA1).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA1 + 1 + k)) = true)
    (hllA1 : ¬ BitVec.ult ((bs[srcOffA1]'hoffA1).zeroExtend 64) (0xf8 : Word) = true →
        srcOffA1 + 1 + ((bs[srcOffA1]'hoffA1).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA1 + 1 +
          ((bs[srcOffA1]'hoffA1).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA1]'hoffA1).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA1 + 1 + k)) = true)
    (hdecA1 : ∃ next lenA1 : Word,
      rlpItemDecode bs srcOffA1 (regionBase + BitVec.ofNat 64 srcOffA1)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenA1)
    (hinbA1 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffA1)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridgeA : ∀ nextA lenA : Word,
      rlpItemDecode bs srcOffA (regionBase + BitVec.ofNat 64 srcOffA)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) nextA lenA →
      nextA = regionBase + BitVec.ofNat 64 srcOffA1) :
    let s : TeerSaved :=
      { ra := ret, s0 := s0, s1 := s1, s2 := s2, s3 := s3, s4 := s4
        s5 := s5, s6 := s6, s7 := s7, s8 := s8, s9 := s9
        s10 := s10, s11 := s11, a5 := baiW }
    let innerVal := (teerTxTypeDispatch (txSlice bs off len)).2.2
    let listLen := lenW - innerVal
    let endL := (regionBase + BitVec.ofNat 64 listOff) + listLen
    let endW := endL
    let cursorV := regionBase + BitVec.ofNat 64 srcOffV
    cpsTripleWithin nFrontToAuthWalkNext1Save
      E AfterAuthWalkNext1Save teerLinkedEarly
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
          (.x1 ↦ᵣ LinkAuthWalkNext1) **
          (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
          (.x18 ↦ᵣ balPtr) ** (.x19 ↦ᵣ balLenW) ** (.x20 ↦ᵣ chainIdW) **
          (.x21 ↦ᵣ next) ** (.x22 ↦ᵣ endL) **
          (.x23 ↦ᵣ s7) **
          (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len1) **
          (.x24 ↦ᵣ cursorV) ** (.x25 ↦ᵣ endW) **
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
          memOwn RecipientPtrAddr ** memOwn RecipientLenAddr **
          memOwn ValueNonzeroAddr **
          teerScratchZeroIs ** teerScratchRestWithoutVnzOwn **
          ⌜rlpItemDecode bs srcOffA1 (regionBase + BitVec.ofNat 64 srcOffA1)
            endL next len1⌝) h) := by
  intro s innerVal listLen endL endW cursorV
  have h0 := teerAuthWalkNext1_applied_nested_is ret spVal spC loadPtr lenW
    balPtr balLenW chainIdW baiW s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    regionBase bs balBytes off len hspC hnez hptr hlenW hsuccess htype4
    halign hbound hover hvalid0 listOff ha0 hoffL hoverL hvalidL hlenL
    h_ge h_hi h_exact srcOff0 hcur0 hoff0 hover0 hvalid0I hss0 hls0 hll0 hdec0 hinb0
    srcOff1 hoff1 hover1 hvalid1 hss1 hls1 hll1 hdec1 hinb1
    srcOff2 hoff2 hover2 hvalid2 hss2 hls2 hll2 hdec2 hinb2
    srcOff3 hoff3 hover3 hvalid3 hss3 hls3 hll3 hdec3 hinb3
    srcOff4 hoff4 hover4 hvalid4 hss4 hls4 hll4 hdec4 hinb4
    srcOff5 hoff5 hover5 hvalid5 hss5 hls5 hll5 hdec5 hinb5
    hbridge hbridge1 hbridge2 hbridge3 hbridge4
    srcOffV hoffV hoverV hvalidV hssV hlsV hllV hdecV hinbV hbridge5
    srcOffA hcurA hoffA hoverA hvalidA hssA hlsA hllA hdecA hinbA
    srcOffA1 hoffA1 hoverA1 hvalidA1 hssA1 hlsA1 hllA1 hdecA1 hinbA1 hbridgeA
  exact cpsTripleWithin_weaken (fun _ hp => hp)
    (fun h hq => by
      unfold teerAuthWalkNext1PostNestedIs teerAuthWalkNextSkipBodyPost
        teerAuthWalkNextSkipAmbientIs teerAuthWalkNext0AmbientIs at hq
      obtain ⟨next, len1, hq'⟩ := hq
      refine ⟨next, len1, ?_⟩
      xperm_hyp hq') h0

#print axioms teerAuthWalkNext1CycleOk_ownTemps
#print axioms teerAuthWalkNext1_applied_nested_is
#print axioms teerAuthWalkNext1_applied


#print axioms teerAuthWalkNext1_applied_nested_is
#print axioms teerAuthWalkNext1_applied_is

end EvmAsm.Codegen.TxEip7702TeerSpec
