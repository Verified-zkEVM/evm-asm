/-
  Teer front values-path type_dispatch: TypeAddr/InnerOff hold teer results.
  AfterBalCheck → AfterTypeBne under applied ambient (feeds Type4 next).
-/

import EvmAsm.Codegen.Programs.TxEip7702TeerFrontType
import EvmAsm.Codegen.Programs.TxEip7702TeerType4
import EvmAsm.Codegen.Programs.TxTypeDispatchAmbientTop
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
  (teerTxTypeDispatch txSlice typeDispatch_success_values_ambient_flat_typeCode)
open EvmAsm.Codegen.TxIntrinsicStateGasSpec (nTypeSteps)

set_option maxRecDepth 8000

local macro "pcf" : tactic => `(tactic|
  repeat first
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
    | exact pcFree_stackFree _ _
    | exact bytesRegion_pcFree _ _
    | exact pcFree_teerScratchOwn
    | exact pcFree_teerScratchWithoutTypeOwn
    | exact pcFree_teerScratchRestWithoutTypeOwn
    | exact pcFree_teerScratchZeroIs)

/-- Values-carrying type callee post (type/inner cells hold teer results). -/
def teerTypeCalleeQValuesAmbient (regionBase : Word) (bs : List (BitVec 8))
    (off len : Nat) : Assertion :=
  (.x10 ↦ᵣ (0 : Word)) **
  bytesRegion regionBase bs **
  (TypeAddr ↦ₘ (teerTxTypeDispatch (txSlice bs off len)).2.1) **
  (InnerOffAddr ↦ₘ (teerTxTypeDispatch (txSlice bs off len)).2.2) **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
  regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
  regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
  regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
  (.x0 ↦ᵣ (0 : Word))

/-- Values-path type JAL call under teerLinkedEarly. -/
theorem teerTypeCallValuesAmbient
    (regionBase loadPtr lenW : Word)
    (bs : List (BitVec 8)) (off len : Nat)
    (old1 : Word)
    (hptr : loadPtr = regionBase + BitVec.ofNat 64 off)
    (hlen : lenW = BitVec.ofNat 64 len)
    (hsuccess : (teerTxTypeDispatch (txSlice bs off len)).1 = (0 : Word))
    (halign : regionBase.toNat % 8 = 0)
    (hbound : off + len ≤ bs.length)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hvalid0 : isValidByteAccess (regionBase + BitVec.ofNat 64 off) = true) :
    cpsTripleWithin (1 + nTypeSteps) (E + 160) LinkType teerLinkedEarly
      ((.x1 ↦ᵣ old1) ** teerTypeCalleePAmbient regionBase loadPtr lenW bs)
      ((.x1 ↦ᵣ LinkType) ** teerTypeCalleeQValuesAmbient regionBase bs off len) := by
  have hret : (LinkType &&& ~~~(1 : Word)) = LinkType := by
    simp only [LinkType, E]; decide
  have hcallee0 := typeDispatch_success_values_ambient_flat_typeCode
    LinkType regionBase loadPtr lenW TypeAddr InnerOffAddr bs off len
    hret hptr hlen hsuccess halign hbound hover hvalid0
  have hcallee : cpsTripleWithin nTypeSteps TypeEntry LinkType teerLinkedEarly
      ((.x1 ↦ᵣ LinkType) ** teerTypeCalleePAmbient regionBase loadPtr lenW bs)
      ((.x1 ↦ᵣ LinkType) ** teerTypeCalleeQValuesAmbient regionBase bs off len) := by
    unfold teerTypeCalleePAmbient teerTypeCalleeQValuesAmbient TypeEntry
    have h1 := cpsTripleWithin_extend_code teerEarly_mono_type hcallee0
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) h1
  have hcall := callWithin_spec (E + 160) TypeEntry old1 typeJalOff nTypeSteps
    (by show (E + 160) + signExtend21 typeJalOff = TypeEntry; decide)
    (fun a i hi => teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E (E + 160) teerProg 40
        (.JAL .x1 typeJalOff) (by bv_omega) (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi))
    (teerTypeCalleePAmbient_pcFree regionBase loadPtr lenW bs)
    hcallee
  rw [show (E + 160 + 4 : Word) = LinkType from by
    simp only [LinkType]; bv_omega] at hcall
  exact hcall

/-- Values-path type setup+call+BNE: AfterBalCheck → AfterTypeBne. -/
theorem teerTypeSuccessValuesAmbient
    (regionBase loadPtr lenW balPtr : Word)
    (bs : List (BitVec 8)) (off len : Nat)
    (old1 v10 v11 v12 v13 : Word)
    (hptr : loadPtr = regionBase + BitVec.ofNat 64 off)
    (hlen : lenW = BitVec.ofNat 64 len)
    (hsuccess : (teerTxTypeDispatch (txSlice bs off len)).1 = (0 : Word))
    (halign : regionBase.toNat % 8 = 0)
    (hbound : off + len ≤ bs.length)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hvalid0 : isValidByteAccess (regionBase + BitVec.ofNat 64 off) = true) :
    cpsTripleWithin (6 + (1 + nTypeSteps) + 1) AfterBalCheck AfterTypeBne teerLinkedEarly
      ((.x1 ↦ᵣ old1) ** (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
        (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** (.x13 ↦ᵣ v13) **
        (.x18 ↦ᵣ balPtr) **
        bytesRegion regionBase bs **
        memOwn TypeAddr ** memOwn InnerOffAddr **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        (.x0 ↦ᵣ (0 : Word)))
      ((.x1 ↦ᵣ LinkType) ** (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) ** (.x18 ↦ᵣ balPtr) **
        bytesRegion regionBase bs **
        (TypeAddr ↦ₘ (teerTxTypeDispatch (txSlice bs off len)).2.1) **
        (InnerOffAddr ↦ₘ (teerTxTypeDispatch (txSlice bs off len)).2.2) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
        regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31) := by
  have hsetup := teerTypeSetup loadPtr lenW v10 v11 v12 v13
  have hsetupF := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ old1) ** (.x18 ↦ᵣ balPtr) **
      bytesRegion regionBase bs **
      memOwn TypeAddr ** memOwn InnerOffAddr **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
      regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      (.x0 ↦ᵣ (0 : Word))) (by pcf) hsetup
  have hcall := teerTypeCallValuesAmbient regionBase loadPtr lenW
    bs off len old1 hptr hlen hsuccess halign hbound hover hvalid0
  have hcallF := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) ** (.x18 ↦ᵣ balPtr)) (by pcf) hcall
  have h01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
    unfold teerTypeCalleePAmbient at *
    xperm_hyp hp) hsetupF hcallF
  have hbne := teerTypeBneOk
  have hbneF := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ LinkType) ** (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
      (.x18 ↦ᵣ balPtr) **
      bytesRegion regionBase bs **
      (TypeAddr ↦ₘ (teerTxTypeDispatch (txSlice bs off len)).2.1) **
      (InnerOffAddr ↦ₘ (teerTxTypeDispatch (txSlice bs off len)).2.2) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
      regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
      regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
    (by pcf) hbne
  have h12 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
    unfold teerTypeCalleeQValuesAmbient at *
    xperm_hyp hp) h01 hbneF
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) h12

/-- Values type focus after success (TypeAddr/InnerOff memIs). -/
def teerTypeValuesFocus
    (loadPtr lenW balPtr regionBase : Word) (bs : List (BitVec 8))
    (off len : Nat) : Assertion :=
  (.x1 ↦ᵣ LinkType) ** (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
  (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) ** (.x18 ↦ᵣ balPtr) **
  bytesRegion regionBase bs **
  (TypeAddr ↦ₘ (teerTxTypeDispatch (txSlice bs off len)).2.1) **
  (InnerOffAddr ↦ₘ (teerTxTypeDispatch (txSlice bs off len)).2.2) **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
  regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
  regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
  regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31

/-- Nested values type post under applied ambient (reuse teerTypeAmbient). -/
def teerTypeValuesPostNested
    (spC loadPtr lenW balPtr balLenW chainIdW
      s5 s6 s7 s8 s9 s11 spVal regionBase : Word)
    (bs balBytes : List (BitVec 8)) (s : TeerSaved) (off len : Nat) : Assertion :=
  teerTypeValuesFocus loadPtr lenW balPtr regionBase bs off len **
  teerTypeAmbient spC balPtr balLenW chainIdW
    s5 s6 s7 s8 s9 s11 spVal balBytes s

/-- AfterBalCheck → AfterTypeBne values nested under applied ambient. -/
theorem teerTypeSuccessValues_applied_nested
    (ret spVal spC loadPtr lenW balPtr balLenW chainIdW baiW : Word)
    (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : Word)
    (regionBase : Word) (bs balBytes : List (BitVec 8)) (off len : Nat)
    (hspC : spC = spVal + signExtend12 (-160 : BitVec 12))
    (hnez : balPtr ≠ (0 : Word))
    (hptr : loadPtr = regionBase + BitVec.ofNat 64 off)
    (hlen : lenW = BitVec.ofNat 64 len)
    (hsuccess : (teerTxTypeDispatch (txSlice bs off len)).1 = (0 : Word))
    (halign : regionBase.toNat % 8 = 0)
    (hbound : off + len ≤ bs.length)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hvalid0 : isValidByteAccess (regionBase + BitVec.ofNat 64 off) = true) :
    let s : TeerSaved :=
      { ra := ret, s0 := s0, s1 := s1, s2 := s2, s3 := s3, s4 := s4
        s5 := s5, s6 := s6, s7 := s7, s8 := s8, s9 := s9
        s10 := s10, s11 := s11, a5 := baiW }
    cpsTripleWithin (34 + (6 + (1 + nTypeSteps) + 1)) E AfterTypeBne teerLinkedEarly
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
      (teerTypeValuesPostNested spC loadPtr lenW balPtr balLenW chainIdW
        s5 s6 s7 s8 s9 s11 spVal regionBase bs balBytes s off len) := by
  intro s
  have hbal := teerPrologueScratchBal_applied ret spVal spC loadPtr lenW balPtr
    balLenW chainIdW baiW s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    regionBase bs balBytes hspC hnez
  have hbalE := cpsTripleWithin_extend_code teerEarly_mono_teer hbal
  have htype := teerTypeSuccessValuesAmbient regionBase loadPtr lenW balPtr
    bs off len ret loadPtr lenW balPtr balLenW
    hptr hlen hsuccess halign hbound hover hvalid0
  have htypeF := cpsTripleWithin_frameR
    (teerTypeAmbient spC balPtr balLenW chainIdW
      s5 s6 s7 s8 s9 s11 spVal balBytes s) (by
      unfold teerTypeAmbient; pcf) htype
  have hsc := teerAfterBalFlat_to_typePre ret spVal spC loadPtr lenW balPtr
    balLenW chainIdW baiW s5 s6 s7 s8 s9 s11 regionBase bs balBytes s
  have hseq := cpsTripleWithin_seq_perm_same_cr hsc hbalE htypeF
  exact cpsTripleWithin_weaken (fun _ hp => hp)
    (fun _ hq => by
      -- htypeF post is values-focus ** teerTypeAmbient; match PostNested.
      unfold teerTypeValuesPostNested teerTypeValuesFocus
      xperm_hyp hq)
    (cpsTripleWithin_mono_nSteps
      (by decide : 34 + (6 + (1 + nTypeSteps) + 1) ≤ 34 + (6 + (1 + nTypeSteps) + 1))
      hseq)

/-- Flatten values nested post (rebuild full scratch from type memIs + rest). -/
theorem teerTypeSuccessValues_applied
    (ret spVal spC loadPtr lenW balPtr balLenW chainIdW baiW : Word)
    (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : Word)
    (regionBase : Word) (bs balBytes : List (BitVec 8)) (off len : Nat)
    (hspC : spC = spVal + signExtend12 (-160 : BitVec 12))
    (hnez : balPtr ≠ (0 : Word))
    (hptr : loadPtr = regionBase + BitVec.ofNat 64 off)
    (hlen : lenW = BitVec.ofNat 64 len)
    (hsuccess : (teerTxTypeDispatch (txSlice bs off len)).1 = (0 : Word))
    (halign : regionBase.toNat % 8 = 0)
    (hbound : off + len ≤ bs.length)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hvalid0 : isValidByteAccess (regionBase + BitVec.ofNat 64 off) = true) :
    let s : TeerSaved :=
      { ra := ret, s0 := s0, s1 := s1, s2 := s2, s3 := s3, s4 := s4
        s5 := s5, s6 := s6, s7 := s7, s8 := s8, s9 := s9
        s10 := s10, s11 := s11, a5 := baiW }
    let typeVal := (teerTxTypeDispatch (txSlice bs off len)).2.1
    let innerVal := (teerTxTypeDispatch (txSlice bs off len)).2.2
    cpsTripleWithin (34 + (6 + (1 + nTypeSteps) + 1)) E AfterTypeBne teerLinkedEarly
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
        (.x1 ↦ᵣ LinkType) **
        (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
        (.x18 ↦ᵣ balPtr) ** (.x19 ↦ᵣ balLenW) ** (.x20 ↦ᵣ chainIdW) **
        (.x21 ↦ᵣ s5) ** (.x22 ↦ᵣ s6) ** (.x23 ↦ᵣ s7) **
        (.x24 ↦ᵣ s8) ** (.x25 ↦ᵣ s9) **
        (.x26 ↦ᵣ (0 : Word)) **
        (.x27 ↦ᵣ s11) **
        frameSlotsSaved teerFrame spC (teerSavedVals s) **
        (.x10 ↦ᵣ (0 : Word)) **
        (.x0 ↦ᵣ (0 : Word)) **
        (TypeAddr ↦ₘ typeVal) ** (InnerOffAddr ↦ₘ innerVal) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
        regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        stackFree spVal 6 **
        bytesRegion regionBase bs ** bytesRegion balPtr balBytes **
        teerScratchWithoutTypeOwn) := by
  intro s typeVal innerVal
  have h0 := teerTypeSuccessValues_applied_nested ret spVal spC loadPtr lenW
    balPtr balLenW chainIdW baiW s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    regionBase bs balBytes off len hspC hnez hptr hlen hsuccess
    halign hbound hover hvalid0
  exact cpsTripleWithin_weaken (fun _ hp => hp)
    (fun _ hq => by
      unfold teerTypeValuesPostNested teerTypeValuesFocus teerTypeAmbient at hq
      xperm_hyp hq) h0

#print axioms teerTypeCallValuesAmbient
#print axioms teerTypeSuccessValuesAmbient
#print axioms teerTypeSuccessValues_applied_nested
#print axioms teerTypeSuccessValues_applied

/-- Ambient through Type4 (no x21/x22 — body writes s5/s6). -/
def teerType4Ambient
    (spC balPtr balLenW chainIdW
      s7 s8 s9 s11 spVal : Word)
    (balBytes : List (BitVec 8)) (s : TeerSaved) : Assertion :=
  (.x2 ↦ᵣ spC) **
  (.x1 ↦ᵣ LinkType) **
  (.x18 ↦ᵣ balPtr) ** (.x19 ↦ᵣ balLenW) ** (.x20 ↦ᵣ chainIdW) **
  (.x23 ↦ᵣ s7) ** (.x24 ↦ᵣ s8) ** (.x25 ↦ᵣ s9) **
  (.x26 ↦ᵣ (0 : Word)) **
  (.x27 ↦ᵣ s11) **
  frameSlotsSaved teerFrame spC (teerSavedVals s) **
  (.x0 ↦ᵣ (0 : Word)) **
  regOwn .x12 ** regOwn .x13 ** regOwn .x14 ** regOwn .x15 **
  regOwn .x16 **
  regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
  stackFree spVal 6 **
  bytesRegion balPtr balBytes **
  teerScratchWithoutTypeOwn

private theorem pcFree_teerType4Ambient
    (spC balPtr balLenW chainIdW
      s7 s8 s9 s11 spVal : Word)
    (balBytes : List (BitVec 8)) (s : TeerSaved) :
    (teerType4Ambient spC balPtr balLenW chainIdW
      s7 s8 s9 s11 spVal balBytes s).pcFree := by
  unfold teerType4Ambient; pcf

/-- Core Type4 body atoms excluding x5/x6/x7/x11 (lifted to regOwn). -/
def teerType4BodyCore
    (loadPtr lenW typeVal innerVal v10 v21 v22 : Word) : Assertion :=
  (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
  (.x10 ↦ᵣ v10) **
  (.x21 ↦ᵣ v21) ** (.x22 ↦ᵣ v22) **
  (TypeAddr ↦ₘ typeVal) ** (InnerOffAddr ↦ₘ innerVal)

private def teerType4BodyPost
    (loadPtr lenW innerVal : Word) : Assertion :=
  (.x5 ↦ᵣ InnerOffAddr) ** (.x6 ↦ᵣ innerVal) ** (.x7 ↦ᵣ (4 : Word)) **
  (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
  (.x10 ↦ᵣ loadPtr + innerVal) ** (.x11 ↦ᵣ lenW - innerVal) **
  (.x21 ↦ᵣ loadPtr + innerVal) ** (.x22 ↦ᵣ lenW - innerVal) **
  (TypeAddr ↦ₘ (4 : Word)) ** (InnerOffAddr ↦ₘ innerVal)

/-- Type4 leaf with regOwn temps (x5/x6/x7/x11) via of_forall2 twice. -/
theorem teerType4ThenInner_ownTemps
    (loadPtr lenW typeVal innerVal v10 v21 v22 : Word)
    (htype4 : typeVal = (4 : Word)) :
    cpsTripleWithin (5 + 7) AfterTypeBne AtWalkInit teerLinkedEarly
      (teerType4BodyCore loadPtr lenW typeVal innerVal v10 v21 v22 **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x11)
      (teerType4BodyPost loadPtr lenW innerVal) := by
  have hcore (v5 v6 v7 v11 : Word) :
      cpsTripleWithin (5 + 7) AfterTypeBne AtWalkInit teerLinkedEarly
        ((.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
          (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
          (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) **
          (.x21 ↦ᵣ v21) ** (.x22 ↦ᵣ v22) **
          (TypeAddr ↦ₘ typeVal) ** (InnerOffAddr ↦ₘ innerVal))
        (teerType4BodyPost loadPtr lenW innerVal) := by
    have h0 := teerType4ThenInner loadPtr lenW typeVal innerVal
      v5 v6 v7 v10 v11 v21 v22 htype4
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by unfold teerType4BodyPost; xperm_hyp hq) h0
  -- Lift x5,x6 with concrete x7,x11. of_forall2 posts (P ** own1 ** own2);
  -- xperm flattens to right-assoc own chain.
  have h56 (v7 v11 : Word) :
      cpsTripleWithin (5 + 7) AfterTypeBne AtWalkInit teerLinkedEarly
        (teerType4BodyCore loadPtr lenW typeVal innerVal v10 v21 v22 **
          (.x7 ↦ᵣ v7) ** (.x11 ↦ᵣ v11) **
          regOwn .x5 ** regOwn .x6)
        (teerType4BodyPost loadPtr lenW innerVal) := by
    have h := cpsTripleWithin_of_forall_regIs_to_regOwn2
      (r1 := .x5) (r2 := .x6)
      (P := teerType4BodyCore loadPtr lenW typeVal innerVal v10 v21 v22 **
        (.x7 ↦ᵣ v7) ** (.x11 ↦ᵣ v11))
      (fun v5 v6 =>
        cpsTripleWithin_weaken (fun _ hp => by
            -- hp : (core ** x7 ** x11) ** x5 ** x6; unfold core then match leaf.
            unfold teerType4BodyCore at hp
            xperm_hyp hp)
          (fun _ hq => hq) (hcore v5 v6 v7 v11))
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => hq) h
  -- Lift x7,x11 with regOwn x5,x6
  have h := cpsTripleWithin_of_forall_regIs_to_regOwn2
    (r1 := .x7) (r2 := .x11)
    (P := teerType4BodyCore loadPtr lenW typeVal innerVal v10 v21 v22 **
      regOwn .x5 ** regOwn .x6)
    (fun v7 v11 =>
      cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
        (fun _ hq => hq) (h56 v7 v11))
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => hq) h

/-- Type4 body focus = ownTemps prest ** bs. -/
def teerType4Focus
    (loadPtr lenW typeVal innerVal v10 v21 v22 regionBase : Word)
    (bs : List (BitVec 8)) : Assertion :=
  (teerType4BodyCore loadPtr lenW typeVal innerVal v10 v21 v22 **
    regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x11) **
  bytesRegion regionBase bs

/-- Values-applied AfterTypeBne post → Type4 focus ** Type4 ambient. -/
theorem teerAfterTypeValuesFlat_to_type4Pre
    (spC loadPtr lenW balPtr balLenW chainIdW
      s5 s6 s7 s8 s9 s11 spVal regionBase : Word)
    (bs balBytes : List (BitVec 8)) (s : TeerSaved)
    (typeVal innerVal : Word) :
    ∀ h,
      ((.x2 ↦ᵣ spC) **
        (.x1 ↦ᵣ LinkType) **
        (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
        (.x18 ↦ᵣ balPtr) ** (.x19 ↦ᵣ balLenW) ** (.x20 ↦ᵣ chainIdW) **
        (.x21 ↦ᵣ s5) ** (.x22 ↦ᵣ s6) ** (.x23 ↦ᵣ s7) **
        (.x24 ↦ᵣ s8) ** (.x25 ↦ᵣ s9) **
        (.x26 ↦ᵣ (0 : Word)) **
        (.x27 ↦ᵣ s11) **
        frameSlotsSaved teerFrame spC (teerSavedVals s) **
        (.x10 ↦ᵣ (0 : Word)) **
        (.x0 ↦ᵣ (0 : Word)) **
        (TypeAddr ↦ₘ typeVal) ** (InnerOffAddr ↦ₘ innerVal) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
        regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        stackFree spVal 6 **
        bytesRegion regionBase bs ** bytesRegion balPtr balBytes **
        teerScratchWithoutTypeOwn) h →
      (teerType4Focus loadPtr lenW typeVal innerVal (0 : Word) s5 s6
          regionBase bs **
        teerType4Ambient spC balPtr balLenW chainIdW
          s7 s8 s9 s11 spVal balBytes s) h := by
  intro _ hp
  unfold teerType4Focus teerType4BodyCore teerType4Ambient
  xperm_hyp hp

/-- Nested Type4 post = (BodyPost ** bs) ** ambient (matches frameR ownTemps). -/
def teerType4PostNested
    (spC loadPtr lenW balPtr balLenW chainIdW
      s7 s8 s9 s11 spVal regionBase : Word)
    (bs balBytes : List (BitVec 8)) (s : TeerSaved)
    (innerVal : Word) : Assertion :=
  ((teerType4BodyPost loadPtr lenW innerVal **
      bytesRegion regionBase bs) **
    teerType4Ambient spC balPtr balLenW chainIdW
      s7 s8 s9 s11 spVal balBytes s)

/-- E → AtWalkInit under applied prest (values type + type4). -/
theorem teerType4ThenInner_applied_nested
    (ret spVal spC loadPtr lenW balPtr balLenW chainIdW baiW : Word)
    (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : Word)
    (regionBase : Word) (bs balBytes : List (BitVec 8)) (off len : Nat)
    (hspC : spC = spVal + signExtend12 (-160 : BitVec 12))
    (hnez : balPtr ≠ (0 : Word))
    (hptr : loadPtr = regionBase + BitVec.ofNat 64 off)
    (hlen : lenW = BitVec.ofNat 64 len)
    (hsuccess : (teerTxTypeDispatch (txSlice bs off len)).1 = (0 : Word))
    (htype4 : (teerTxTypeDispatch (txSlice bs off len)).2.1 = (4 : Word))
    (halign : regionBase.toNat % 8 = 0)
    (hbound : off + len ≤ bs.length)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hvalid0 : isValidByteAccess (regionBase + BitVec.ofNat 64 off) = true) :
    let s : TeerSaved :=
      { ra := ret, s0 := s0, s1 := s1, s2 := s2, s3 := s3, s4 := s4
        s5 := s5, s6 := s6, s7 := s7, s8 := s8, s9 := s9
        s10 := s10, s11 := s11, a5 := baiW }
    let typeVal := (teerTxTypeDispatch (txSlice bs off len)).2.1
    let innerVal := (teerTxTypeDispatch (txSlice bs off len)).2.2
    cpsTripleWithin
      ((34 + (6 + (1 + nTypeSteps) + 1)) + (5 + 7))
      E AtWalkInit teerLinkedEarly
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
      (teerType4PostNested spC loadPtr lenW balPtr balLenW chainIdW
        s7 s8 s9 s11 spVal regionBase bs balBytes s innerVal) := by
  intro s typeVal innerVal
  have hty := teerTypeSuccessValues_applied ret spVal spC loadPtr lenW
    balPtr balLenW chainIdW baiW s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    regionBase bs balBytes off len hspC hnez hptr hlen hsuccess
    halign hbound hover hvalid0
  -- ownTemps focus, then frame bs, then Type4 ambient
  have h4 := teerType4ThenInner_ownTemps loadPtr lenW typeVal innerVal
    (0 : Word) s5 s6 htype4
  have h4bs := cpsTripleWithin_frameR
    (bytesRegion regionBase bs) (by exact bytesRegion_pcFree _ _) h4
  have h4F0 := cpsTripleWithin_frameR
    (teerType4Ambient spC balPtr balLenW chainIdW
      s7 s8 s9 s11 spVal balBytes s)
    (by exact pcFree_teerType4Ambient _ _ _ _ _ _ _ _ _ _ _) h4bs
  -- Align prest/post to Focus ** ambient / PostNested.
  have h4F :
      cpsTripleWithin (5 + 7) AfterTypeBne AtWalkInit teerLinkedEarly
        (teerType4Focus loadPtr lenW typeVal innerVal (0 : Word) s5 s6
            regionBase bs **
          teerType4Ambient spC balPtr balLenW chainIdW
            s7 s8 s9 s11 spVal balBytes s)
        (teerType4PostNested spC loadPtr lenW balPtr balLenW chainIdW
          s7 s8 s9 s11 spVal regionBase bs balBytes s innerVal) := by
    exact cpsTripleWithin_weaken
      (fun _ hp => by
        unfold teerType4Focus at hp
        xperm_hyp hp)
      (fun _ hq => by
        unfold teerType4PostNested
        exact hq)
      h4F0
  have hsc := teerAfterTypeValuesFlat_to_type4Pre spC loadPtr lenW balPtr
    balLenW chainIdW s5 s6 s7 s8 s9 s11 spVal regionBase bs balBytes s
    typeVal innerVal
  have hseq := cpsTripleWithin_seq_perm_same_cr hsc hty h4F
  exact cpsTripleWithin_mono_nSteps
    (by decide :
      (34 + (6 + (1 + nTypeSteps) + 1)) + (5 + 7) ≤
        (34 + (6 + (1 + nTypeSteps) + 1)) + (5 + 7))
    hseq

/-- Flatten Type4 nested → applied-style AtWalkInit post. -/
theorem teerType4ThenInner_applied
    (ret spVal spC loadPtr lenW balPtr balLenW chainIdW baiW : Word)
    (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : Word)
    (regionBase : Word) (bs balBytes : List (BitVec 8)) (off len : Nat)
    (hspC : spC = spVal + signExtend12 (-160 : BitVec 12))
    (hnez : balPtr ≠ (0 : Word))
    (hptr : loadPtr = regionBase + BitVec.ofNat 64 off)
    (hlen : lenW = BitVec.ofNat 64 len)
    (hsuccess : (teerTxTypeDispatch (txSlice bs off len)).1 = (0 : Word))
    (htype4 : (teerTxTypeDispatch (txSlice bs off len)).2.1 = (4 : Word))
    (halign : regionBase.toNat % 8 = 0)
    (hbound : off + len ≤ bs.length)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hvalid0 : isValidByteAccess (regionBase + BitVec.ofNat 64 off) = true) :
    let s : TeerSaved :=
      { ra := ret, s0 := s0, s1 := s1, s2 := s2, s3 := s3, s4 := s4
        s5 := s5, s6 := s6, s7 := s7, s8 := s8, s9 := s9
        s10 := s10, s11 := s11, a5 := baiW }
    let innerVal := (teerTxTypeDispatch (txSlice bs off len)).2.2
    cpsTripleWithin
      ((34 + (6 + (1 + nTypeSteps) + 1)) + (5 + 7))
      E AtWalkInit teerLinkedEarly
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
        teerScratchWithoutTypeOwn) := by
  intro s innerVal
  have h0 := teerType4ThenInner_applied_nested ret spVal spC loadPtr lenW
    balPtr balLenW chainIdW baiW s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    regionBase bs balBytes off len hspC hnez hptr hlen hsuccess htype4
    halign hbound hover hvalid0
  exact cpsTripleWithin_weaken (fun _ hp => hp)
    (fun _ hq => by
      unfold teerType4PostNested teerType4BodyPost teerType4Ambient at hq
      xperm_hyp hq) h0

#print axioms teerType4ThenInner_ownTemps
#print axioms teerType4ThenInner_applied_nested
#print axioms teerType4ThenInner_applied

/-- Values nested under ZeroIs ambient. -/
def teerTypeValuesPostNestedIs
    (spC loadPtr lenW balPtr balLenW chainIdW
      s5 s6 s7 s8 s9 s11 spVal regionBase : Word)
    (bs balBytes : List (BitVec 8)) (s : TeerSaved) (off len : Nat) : Assertion :=
  teerTypeValuesFocus loadPtr lenW balPtr regionBase bs off len **
  teerTypeAmbientIs spC balPtr balLenW chainIdW
    s5 s6 s7 s8 s9 s11 spVal balBytes s

/-- AfterBal Is → AfterTypeBne values nested under ZeroIs. -/
theorem teerTypeSuccessValues_applied_nested_is
    (ret spVal spC loadPtr lenW balPtr balLenW chainIdW baiW : Word)
    (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : Word)
    (regionBase : Word) (bs balBytes : List (BitVec 8)) (off len : Nat)
    (hspC : spC = spVal + signExtend12 (-160 : BitVec 12))
    (hnez : balPtr ≠ (0 : Word))
    (hptr : loadPtr = regionBase + BitVec.ofNat 64 off)
    (hlen : lenW = BitVec.ofNat 64 len)
    (hsuccess : (teerTxTypeDispatch (txSlice bs off len)).1 = (0 : Word))
    (halign : regionBase.toNat % 8 = 0)
    (hbound : off + len ≤ bs.length)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hvalid0 : isValidByteAccess (regionBase + BitVec.ofNat 64 off) = true) :
    let s : TeerSaved :=
      { ra := ret, s0 := s0, s1 := s1, s2 := s2, s3 := s3, s4 := s4
        s5 := s5, s6 := s6, s7 := s7, s8 := s8, s9 := s9
        s10 := s10, s11 := s11, a5 := baiW }
    cpsTripleWithin (34 + (6 + (1 + nTypeSteps) + 1)) E AfterTypeBne teerLinkedEarly
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
      (teerTypeValuesPostNestedIs spC loadPtr lenW balPtr balLenW chainIdW
        s5 s6 s7 s8 s9 s11 spVal regionBase bs balBytes s off len) := by
  intro s
  have hbal := teerPrologueScratchBal_applied_is ret spVal spC loadPtr lenW balPtr
    balLenW chainIdW baiW s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    regionBase bs balBytes hspC hnez
  have hbalE := cpsTripleWithin_extend_code teerEarly_mono_teer hbal
  have htype := teerTypeSuccessValuesAmbient regionBase loadPtr lenW balPtr
    bs off len ret loadPtr lenW balPtr balLenW
    hptr hlen hsuccess halign hbound hover hvalid0
  have htypeF := cpsTripleWithin_frameR
    (teerTypeAmbientIs spC balPtr balLenW chainIdW
      s5 s6 s7 s8 s9 s11 spVal balBytes s)
    (pcFree_teerTypeAmbientIs spC balPtr balLenW chainIdW
      s5 s6 s7 s8 s9 s11 spVal balBytes s) htype
  have hsc := teerAfterBalFlatIs_to_typePre ret spVal spC loadPtr lenW balPtr
    balLenW chainIdW baiW s5 s6 s7 s8 s9 s11 regionBase bs balBytes s
  have hseq := cpsTripleWithin_seq_perm_same_cr hsc hbalE htypeF
  exact cpsTripleWithin_weaken (fun _ hp => hp)
    (fun _ hq => by
      unfold teerTypeValuesPostNestedIs teerTypeValuesFocus
      xperm_hyp hq)
    (cpsTripleWithin_mono_nSteps
      (by decide : 34 + (6 + (1 + nTypeSteps) + 1) ≤ 34 + (6 + (1 + nTypeSteps) + 1))
      hseq)

/-- Flatten values Is: Type/Inner memIs + ZeroIs ** RestWithoutType. -/
theorem teerTypeSuccessValues_applied_is
    (ret spVal spC loadPtr lenW balPtr balLenW chainIdW baiW : Word)
    (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : Word)
    (regionBase : Word) (bs balBytes : List (BitVec 8)) (off len : Nat)
    (hspC : spC = spVal + signExtend12 (-160 : BitVec 12))
    (hnez : balPtr ≠ (0 : Word))
    (hptr : loadPtr = regionBase + BitVec.ofNat 64 off)
    (hlen : lenW = BitVec.ofNat 64 len)
    (hsuccess : (teerTxTypeDispatch (txSlice bs off len)).1 = (0 : Word))
    (halign : regionBase.toNat % 8 = 0)
    (hbound : off + len ≤ bs.length)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hvalid0 : isValidByteAccess (regionBase + BitVec.ofNat 64 off) = true) :
    let s : TeerSaved :=
      { ra := ret, s0 := s0, s1 := s1, s2 := s2, s3 := s3, s4 := s4
        s5 := s5, s6 := s6, s7 := s7, s8 := s8, s9 := s9
        s10 := s10, s11 := s11, a5 := baiW }
    let typeVal := (teerTxTypeDispatch (txSlice bs off len)).2.1
    let innerVal := (teerTxTypeDispatch (txSlice bs off len)).2.2
    cpsTripleWithin (34 + (6 + (1 + nTypeSteps) + 1)) E AfterTypeBne teerLinkedEarly
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
        (.x1 ↦ᵣ LinkType) **
        (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
        (.x18 ↦ᵣ balPtr) ** (.x19 ↦ᵣ balLenW) ** (.x20 ↦ᵣ chainIdW) **
        (.x21 ↦ᵣ s5) ** (.x22 ↦ᵣ s6) ** (.x23 ↦ᵣ s7) **
        (.x24 ↦ᵣ s8) ** (.x25 ↦ᵣ s9) **
        (.x26 ↦ᵣ (0 : Word)) **
        (.x27 ↦ᵣ s11) **
        frameSlotsSaved teerFrame spC (teerSavedVals s) **
        (.x10 ↦ᵣ (0 : Word)) **
        (.x0 ↦ᵣ (0 : Word)) **
        (TypeAddr ↦ₘ typeVal) ** (InnerOffAddr ↦ₘ innerVal) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
        regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        stackFree spVal 6 **
        bytesRegion regionBase bs ** bytesRegion balPtr balBytes **
        teerScratchZeroIs ** teerScratchRestWithoutTypeOwn) := by
  intro s _typeVal _innerVal
  have h0 := teerTypeSuccessValues_applied_nested_is ret spVal spC loadPtr lenW
    balPtr balLenW chainIdW baiW s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    regionBase bs balBytes off len hspC hnez hptr hlen hsuccess
    halign hbound hover hvalid0
  exact cpsTripleWithin_weaken (fun _ hp => hp)
    (fun _ hq => by
      unfold teerTypeValuesPostNestedIs teerTypeValuesFocus teerTypeAmbientIs at hq
      xperm_hyp hq) h0

/-- Type4 ambient with ZeroIs (no x21/x22). -/
def teerType4AmbientIs
    (spC balPtr balLenW chainIdW
      s7 s8 s9 s11 spVal : Word)
    (balBytes : List (BitVec 8)) (s : TeerSaved) : Assertion :=
  (.x2 ↦ᵣ spC) **
  (.x1 ↦ᵣ LinkType) **
  (.x18 ↦ᵣ balPtr) ** (.x19 ↦ᵣ balLenW) ** (.x20 ↦ᵣ chainIdW) **
  (.x23 ↦ᵣ s7) ** (.x24 ↦ᵣ s8) ** (.x25 ↦ᵣ s9) **
  (.x26 ↦ᵣ (0 : Word)) **
  (.x27 ↦ᵣ s11) **
  frameSlotsSaved teerFrame spC (teerSavedVals s) **
  (.x0 ↦ᵣ (0 : Word)) **
  regOwn .x12 ** regOwn .x13 ** regOwn .x14 ** regOwn .x15 **
  regOwn .x16 **
  regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
  stackFree spVal 6 **
  bytesRegion balPtr balBytes **
  teerScratchZeroIs ** teerScratchRestWithoutTypeOwn

private theorem pcFree_teerType4AmbientIs
    (spC balPtr balLenW chainIdW
      s7 s8 s9 s11 spVal : Word)
    (balBytes : List (BitVec 8)) (s : TeerSaved) :
    (teerType4AmbientIs spC balPtr balLenW chainIdW
      s7 s8 s9 s11 spVal balBytes s).pcFree := by
  unfold teerType4AmbientIs teerScratchZeroIs teerScratchRestWithoutTypeOwn
  pcf

/-- Values Is-flat → Type4 focus ** Type4 ambient Is. -/
theorem teerAfterTypeValuesFlatIs_to_type4Pre
    (spC loadPtr lenW balPtr balLenW chainIdW
      s5 s6 s7 s8 s9 s11 spVal regionBase : Word)
    (bs balBytes : List (BitVec 8)) (s : TeerSaved)
    (typeVal innerVal : Word) :
    ∀ h,
      ((.x2 ↦ᵣ spC) **
        (.x1 ↦ᵣ LinkType) **
        (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
        (.x18 ↦ᵣ balPtr) ** (.x19 ↦ᵣ balLenW) ** (.x20 ↦ᵣ chainIdW) **
        (.x21 ↦ᵣ s5) ** (.x22 ↦ᵣ s6) ** (.x23 ↦ᵣ s7) **
        (.x24 ↦ᵣ s8) ** (.x25 ↦ᵣ s9) **
        (.x26 ↦ᵣ (0 : Word)) **
        (.x27 ↦ᵣ s11) **
        frameSlotsSaved teerFrame spC (teerSavedVals s) **
        (.x10 ↦ᵣ (0 : Word)) **
        (.x0 ↦ᵣ (0 : Word)) **
        (TypeAddr ↦ₘ typeVal) ** (InnerOffAddr ↦ₘ innerVal) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
        regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        stackFree spVal 6 **
        bytesRegion regionBase bs ** bytesRegion balPtr balBytes **
        teerScratchZeroIs ** teerScratchRestWithoutTypeOwn) h →
      (teerType4Focus loadPtr lenW typeVal innerVal (0 : Word) s5 s6
          regionBase bs **
        teerType4AmbientIs spC balPtr balLenW chainIdW
          s7 s8 s9 s11 spVal balBytes s) h := by
  intro _ hp
  unfold teerType4Focus teerType4BodyCore teerType4AmbientIs
  xperm_hyp hp

def teerType4PostNestedIs
    (spC loadPtr lenW balPtr balLenW chainIdW
      s7 s8 s9 s11 spVal regionBase : Word)
    (bs balBytes : List (BitVec 8)) (s : TeerSaved)
    (innerVal : Word) : Assertion :=
  ((teerType4BodyPost loadPtr lenW innerVal **
      bytesRegion regionBase bs) **
    teerType4AmbientIs spC balPtr balLenW chainIdW
      s7 s8 s9 s11 spVal balBytes s)

/-- E → AtWalkInit under applied Is path (values + type4). -/
theorem teerType4ThenInner_applied_nested_is
    (ret spVal spC loadPtr lenW balPtr balLenW chainIdW baiW : Word)
    (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : Word)
    (regionBase : Word) (bs balBytes : List (BitVec 8)) (off len : Nat)
    (hspC : spC = spVal + signExtend12 (-160 : BitVec 12))
    (hnez : balPtr ≠ (0 : Word))
    (hptr : loadPtr = regionBase + BitVec.ofNat 64 off)
    (hlen : lenW = BitVec.ofNat 64 len)
    (hsuccess : (teerTxTypeDispatch (txSlice bs off len)).1 = (0 : Word))
    (htype4 : (teerTxTypeDispatch (txSlice bs off len)).2.1 = (4 : Word))
    (halign : regionBase.toNat % 8 = 0)
    (hbound : off + len ≤ bs.length)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hvalid0 : isValidByteAccess (regionBase + BitVec.ofNat 64 off) = true) :
    let s : TeerSaved :=
      { ra := ret, s0 := s0, s1 := s1, s2 := s2, s3 := s3, s4 := s4
        s5 := s5, s6 := s6, s7 := s7, s8 := s8, s9 := s9
        s10 := s10, s11 := s11, a5 := baiW }
    let typeVal := (teerTxTypeDispatch (txSlice bs off len)).2.1
    let innerVal := (teerTxTypeDispatch (txSlice bs off len)).2.2
    cpsTripleWithin
      ((34 + (6 + (1 + nTypeSteps) + 1)) + (5 + 7))
      E AtWalkInit teerLinkedEarly
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
      (teerType4PostNestedIs spC loadPtr lenW balPtr balLenW chainIdW
        s7 s8 s9 s11 spVal regionBase bs balBytes s innerVal) := by
  intro s typeVal innerVal
  have hty := teerTypeSuccessValues_applied_is ret spVal spC loadPtr lenW
    balPtr balLenW chainIdW baiW s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    regionBase bs balBytes off len hspC hnez hptr hlen hsuccess
    halign hbound hover hvalid0
  have h4 := teerType4ThenInner_ownTemps loadPtr lenW typeVal innerVal
    (0 : Word) s5 s6 (by simpa using htype4)
  have h4bs := cpsTripleWithin_frameR
    (bytesRegion regionBase bs) (by exact bytesRegion_pcFree _ _) h4
  have h4F0 := cpsTripleWithin_frameR
    (teerType4AmbientIs spC balPtr balLenW chainIdW
      s7 s8 s9 s11 spVal balBytes s)
    (by exact pcFree_teerType4AmbientIs _ _ _ _ _ _ _ _ _ _ _) h4bs
  have h4F :
      cpsTripleWithin (5 + 7) AfterTypeBne AtWalkInit teerLinkedEarly
        (teerType4Focus loadPtr lenW typeVal innerVal (0 : Word) s5 s6
            regionBase bs **
          teerType4AmbientIs spC balPtr balLenW chainIdW
            s7 s8 s9 s11 spVal balBytes s)
        (teerType4PostNestedIs spC loadPtr lenW balPtr balLenW chainIdW
          s7 s8 s9 s11 spVal regionBase bs balBytes s innerVal) := by
    exact cpsTripleWithin_weaken
      (fun _ hp => by
        unfold teerType4Focus at hp
        xperm_hyp hp)
      (fun _ hq => by
        unfold teerType4PostNestedIs
        exact hq)
      h4F0
  have hsc := teerAfterTypeValuesFlatIs_to_type4Pre spC loadPtr lenW balPtr
    balLenW chainIdW s5 s6 s7 s8 s9 s11 spVal regionBase bs balBytes s
    typeVal innerVal
  have hseq := cpsTripleWithin_seq_perm_same_cr hsc hty h4F
  exact cpsTripleWithin_mono_nSteps
    (by decide :
      (34 + (6 + (1 + nTypeSteps) + 1)) + (5 + 7) ≤
        (34 + (6 + (1 + nTypeSteps) + 1)) + (5 + 7))
    hseq

/-- Flatten Type4 Is nested → AtWalkInit with ZeroIs ** RestWithoutType. -/
theorem teerType4ThenInner_applied_is
    (ret spVal spC loadPtr lenW balPtr balLenW chainIdW baiW : Word)
    (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : Word)
    (regionBase : Word) (bs balBytes : List (BitVec 8)) (off len : Nat)
    (hspC : spC = spVal + signExtend12 (-160 : BitVec 12))
    (hnez : balPtr ≠ (0 : Word))
    (hptr : loadPtr = regionBase + BitVec.ofNat 64 off)
    (hlen : lenW = BitVec.ofNat 64 len)
    (hsuccess : (teerTxTypeDispatch (txSlice bs off len)).1 = (0 : Word))
    (htype4 : (teerTxTypeDispatch (txSlice bs off len)).2.1 = (4 : Word))
    (halign : regionBase.toNat % 8 = 0)
    (hbound : off + len ≤ bs.length)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hvalid0 : isValidByteAccess (regionBase + BitVec.ofNat 64 off) = true) :
    let s : TeerSaved :=
      { ra := ret, s0 := s0, s1 := s1, s2 := s2, s3 := s3, s4 := s4
        s5 := s5, s6 := s6, s7 := s7, s8 := s8, s9 := s9
        s10 := s10, s11 := s11, a5 := baiW }
    let innerVal := (teerTxTypeDispatch (txSlice bs off len)).2.2
    cpsTripleWithin
      ((34 + (6 + (1 + nTypeSteps) + 1)) + (5 + 7))
      E AtWalkInit teerLinkedEarly
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
        teerScratchZeroIs ** teerScratchRestWithoutTypeOwn) := by
  intro s innerVal
  have h0 := teerType4ThenInner_applied_nested_is ret spVal spC loadPtr lenW
    balPtr balLenW chainIdW baiW s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    regionBase bs balBytes off len hspC hnez hptr hlen hsuccess htype4
    halign hbound hover hvalid0
  exact cpsTripleWithin_weaken (fun _ hp => hp)
    (fun _ hq => by
      unfold teerType4PostNestedIs teerType4BodyPost teerType4AmbientIs at hq
      xperm_hyp hq) h0

#print axioms teerTypeSuccessValues_applied_nested_is
#print axioms teerTypeSuccessValues_applied_is
#print axioms teerType4ThenInner_applied_nested_is
#print axioms teerType4ThenInner_applied_is

end EvmAsm.Codegen.TxEip7702TeerSpec
