/-
  Teer front values-path type_dispatch: TypeAddr/InnerOff hold teer results.
  AfterBalCheck → AfterTypeBne under applied ambient (feeds Type4 next).
-/

import EvmAsm.Codegen.Programs.TxEip7702TeerFrontType
import EvmAsm.Codegen.Programs.TxEip7702TeerType4
import EvmAsm.Codegen.Programs.TxTypeDispatchAmbientTop
import EvmAsm.Codegen.Programs.TxIntrinsicStateGasSpec
import EvmAsm.Rv64.CPSSpec
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
    | exact pcFree_teerScratchWithoutTypeOwn)

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

end EvmAsm.Codegen.TxEip7702TeerSpec
