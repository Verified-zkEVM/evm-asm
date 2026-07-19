/-
  Teer front: AfterBalCheck → AfterTypeBne under applied_flat prest.
  Composes teerTypeSuccessAmbient with scratch peel + regOwn lifts.
-/

import EvmAsm.Codegen.Programs.TxEip7702TeerFrontEarly
import EvmAsm.Codegen.Programs.TxEip7702TeerType
import EvmAsm.Codegen.Programs.TxTypeDispatchAmbientTop
import EvmAsm.Codegen.Programs.TxIntrinsicStateGasSpec
import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.Tactics.XSimp

namespace EvmAsm.Codegen.TxEip7702TeerSpec

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
open EvmAsm.Codegen.BlockVerdictTxStateGasArraySpec
open EvmAsm.Codegen.TxTypeDispatchSpec
  (teerTxTypeDispatch txSlice TypeDispatchAssumedAmbientFull)
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
    | exact pcFree_teerScratchOwn)

/-- Scratch without type/inner_off cells (peeled for type_dispatch). -/
def teerScratchWithoutTypeOwn : Assertion :=
  memOwn (BitVec.ofNat 64 GuestAddrs.teer_authority) **
  memOwn (BitVec.ofNat 64 GuestAddrs.teer_acct_ptr) **
  memOwn (BitVec.ofNat 64 GuestAddrs.teer_acct_len) **
  memOwn (BitVec.ofNat 64 GuestAddrs.teer_acct_absent) **
  memOwn (BitVec.ofNat 64 GuestAddrs.teer_rolled_back) **
  memOwn (BitVec.ofNat 64 GuestAddrs.teer_prior_count) **
  memOwn (BitVec.ofNat 64 GuestAddrs.teer_pre_acct) **
  memOwn (BitVec.ofNat 64 GuestAddrs.teer_success_count) **
  memOwn (BitVec.ofNat 64 GuestAddrs.teer_regular_refund) **
  memOwn (BitVec.ofNat 64 GuestAddrs.teer_prior_set_flag) **
  memOwn (BitVec.ofNat 64 GuestAddrs.teer_finals) **
  memOwn (BitVec.ofNat 64 GuestAddrs.teer_value_nonzero) **
  memOwn (BitVec.ofNat 64 GuestAddrs.teer_success_table) **
  memOwn (BitVec.ofNat 64 GuestAddrs.teer_recipient_ptr) **
  memOwn (BitVec.ofNat 64 GuestAddrs.teer_recipient_len) **
  memOwn (BitVec.ofNat 64 GuestAddrs.teer_predelegated_count) **
  memOwn (BitVec.ofNat 64 GuestAddrs.teer_auth_count) **
  memOwn (BitVec.ofNat 64 GuestAddrs.teer_wouldbe_state) **
  memOwn (BitVec.ofNat 64 GuestAddrs.teer_wouldbe_regular) **
  memOwn (BitVec.ofNat 64 GuestAddrs.teer_recover_scratch) **
  memOwn (BitVec.ofNat 64 GuestAddrs.teer_records_ptr)

private theorem pcFree_teerScratchWithoutTypeOwn :
    teerScratchWithoutTypeOwn.pcFree := by
  unfold teerScratchWithoutTypeOwn
  repeat' (first | exact pcFree_memOwn | apply pcFree_sepConj)

theorem teerScratchOwn_to_type_rest :
    ∀ h, teerScratchOwn h →
      (memOwn TypeAddr ** memOwn InnerOffAddr ** teerScratchWithoutTypeOwn) h := by
  intro h hp
  unfold teerScratchOwn teerScratchWithoutTypeOwn TypeAddr InnerOffAddr at *
  xperm_hyp hp

theorem teerScratchOwn_of_type_rest :
    ∀ h, (memOwn TypeAddr ** memOwn InnerOffAddr ** teerScratchWithoutTypeOwn) h →
      teerScratchOwn h := by
  intro h hp
  unfold teerScratchOwn teerScratchWithoutTypeOwn TypeAddr InnerOffAddr at *
  xperm_hyp hp

/-- Ambient under type focus at AfterBalCheck. -/
def teerTypeAmbient
    (spC balPtr balLenW chainIdW
      s5 s6 s7 s8 s9 s11 spVal : Word)
    (balBytes : List (BitVec 8)) (s : TeerSaved) : Assertion :=
  (.x2 ↦ᵣ spC) **
  (.x19 ↦ᵣ balLenW) ** (.x20 ↦ᵣ chainIdW) **
  (.x21 ↦ᵣ s5) ** (.x22 ↦ᵣ s6) ** (.x23 ↦ᵣ s7) **
  (.x24 ↦ᵣ s8) ** (.x25 ↦ᵣ s9) **
  (.x26 ↦ᵣ (0 : Word)) **
  (.x27 ↦ᵣ s11) **
  frameSlotsSaved teerFrame spC (teerSavedVals s) **
  stackFree spVal 6 **
  bytesRegion balPtr balBytes **
  teerScratchWithoutTypeOwn

private theorem pcFree_teerTypeAmbient
    (spC balPtr balLenW chainIdW
      s5 s6 s7 s8 s9 s11 spVal : Word)
    (balBytes : List (BitVec 8)) (s : TeerSaved) :
    (teerTypeAmbient spC balPtr balLenW chainIdW
      s5 s6 s7 s8 s9 s11 spVal balBytes s).pcFree := by
  unfold teerTypeAmbient; pcf

/-- Type focus = teerTypeSuccessAmbient prest (old a-regs = AfterBal values). -/
def teerTypeFocus
    (ret loadPtr lenW balPtr balLenW regionBase : Word)
    (bs : List (BitVec 8)) : Assertion :=
  (.x1 ↦ᵣ ret) ** (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
  (.x10 ↦ᵣ loadPtr) ** (.x11 ↦ᵣ lenW) **
  (.x12 ↦ᵣ balPtr) ** (.x13 ↦ᵣ balLenW) **
  (.x18 ↦ᵣ balPtr) **
  bytesRegion regionBase bs **
  memOwn TypeAddr ** memOwn InnerOffAddr **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
  regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
  regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
  (.x0 ↦ᵣ (0 : Word))

/-- AfterBal flat post → type focus ** ambient. -/
theorem teerAfterBalFlat_to_typePre
    (ret spVal spC loadPtr lenW balPtr balLenW chainIdW baiW : Word)
    (s5 s6 s7 s8 s9 s11 regionBase : Word)
    (bs balBytes : List (BitVec 8)) (s : TeerSaved) :
    ∀ h,
      ((.x2 ↦ᵣ spC) **
        (.x1 ↦ᵣ ret) **
        (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
        (.x18 ↦ᵣ balPtr) ** (.x19 ↦ᵣ balLenW) ** (.x20 ↦ᵣ chainIdW) **
        (.x21 ↦ᵣ s5) ** (.x22 ↦ᵣ s6) ** (.x23 ↦ᵣ s7) **
        (.x24 ↦ᵣ s8) ** (.x25 ↦ᵣ s9) **
        (.x26 ↦ᵣ (0 : Word)) **
        (.x27 ↦ᵣ s11) ** (.x15 ↦ᵣ baiW) **
        (.x5 ↦ᵣ RolledBackAddr) **
        frameSlotsSaved teerFrame spC (teerSavedVals s) **
        (.x10 ↦ᵣ loadPtr) ** (.x11 ↦ᵣ lenW) **
        (.x12 ↦ᵣ balPtr) ** (.x13 ↦ᵣ balLenW) ** (.x14 ↦ᵣ chainIdW) **
        regOwn .x6 ** regOwn .x7 ** regOwn .x16 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        (.x0 ↦ᵣ (0 : Word)) **
        stackFree spVal 6 **
        bytesRegion regionBase bs ** bytesRegion balPtr balBytes **
        teerScratchOwn) h →
      (teerTypeFocus ret loadPtr lenW balPtr balLenW regionBase bs **
        teerTypeAmbient spC balPtr balLenW chainIdW
          s5 s6 s7 s8 s9 s11 spVal balBytes s) h := by
  intro h hp
  unfold teerTypeFocus teerTypeAmbient
  -- `**` is right-assoc: pull scratch left, peel type/inner, then lift regs.
  have hpSc : (teerScratchOwn **
      ((.x2 ↦ᵣ spC) **
        (.x1 ↦ᵣ ret) **
        (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
        (.x18 ↦ᵣ balPtr) ** (.x19 ↦ᵣ balLenW) ** (.x20 ↦ᵣ chainIdW) **
        (.x21 ↦ᵣ s5) ** (.x22 ↦ᵣ s6) ** (.x23 ↦ᵣ s7) **
        (.x24 ↦ᵣ s8) ** (.x25 ↦ᵣ s9) **
        (.x26 ↦ᵣ (0 : Word)) **
        (.x27 ↦ᵣ s11) ** (.x15 ↦ᵣ baiW) **
        (.x5 ↦ᵣ RolledBackAddr) **
        frameSlotsSaved teerFrame spC (teerSavedVals s) **
        (.x10 ↦ᵣ loadPtr) ** (.x11 ↦ᵣ lenW) **
        (.x12 ↦ᵣ balPtr) ** (.x13 ↦ᵣ balLenW) ** (.x14 ↦ᵣ chainIdW) **
        regOwn .x6 ** regOwn .x7 ** regOwn .x16 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        (.x0 ↦ᵣ (0 : Word)) **
        stackFree spVal 6 **
        bytesRegion regionBase bs ** bytesRegion balPtr balBytes)) h := by
    xperm_hyp hp
  have hpPeel := sepConj_mono_left teerScratchOwn_to_type_rest h hpSc
  have hp1 : ((.x5 ↦ᵣ RolledBackAddr) **
      ((.x2 ↦ᵣ spC) **
        (.x1 ↦ᵣ ret) **
        (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
        (.x18 ↦ᵣ balPtr) ** (.x19 ↦ᵣ balLenW) ** (.x20 ↦ᵣ chainIdW) **
        (.x21 ↦ᵣ s5) ** (.x22 ↦ᵣ s6) ** (.x23 ↦ᵣ s7) **
        (.x24 ↦ᵣ s8) ** (.x25 ↦ᵣ s9) **
        (.x26 ↦ᵣ (0 : Word)) **
        (.x27 ↦ᵣ s11) ** (.x15 ↦ᵣ baiW) **
        frameSlotsSaved teerFrame spC (teerSavedVals s) **
        (.x10 ↦ᵣ loadPtr) ** (.x11 ↦ᵣ lenW) **
        (.x12 ↦ᵣ balPtr) ** (.x13 ↦ᵣ balLenW) ** (.x14 ↦ᵣ chainIdW) **
        regOwn .x6 ** regOwn .x7 ** regOwn .x16 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        (.x0 ↦ᵣ (0 : Word)) **
        stackFree spVal 6 **
        bytesRegion regionBase bs ** bytesRegion balPtr balBytes **
        (memOwn TypeAddr ** memOwn InnerOffAddr ** teerScratchWithoutTypeOwn))) h := by
    xperm_hyp hpPeel
  have hp2 := sepConj_mono_left
    (regIs_implies_regOwn (r := .x5) (v := RolledBackAddr)) h hp1
  have hp3 : ((.x14 ↦ᵣ chainIdW) **
      (regOwn .x5 **
        ((.x2 ↦ᵣ spC) **
          (.x1 ↦ᵣ ret) **
          (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
          (.x18 ↦ᵣ balPtr) ** (.x19 ↦ᵣ balLenW) ** (.x20 ↦ᵣ chainIdW) **
          (.x21 ↦ᵣ s5) ** (.x22 ↦ᵣ s6) ** (.x23 ↦ᵣ s7) **
          (.x24 ↦ᵣ s8) ** (.x25 ↦ᵣ s9) **
          (.x26 ↦ᵣ (0 : Word)) **
          (.x27 ↦ᵣ s11) ** (.x15 ↦ᵣ baiW) **
          frameSlotsSaved teerFrame spC (teerSavedVals s) **
          (.x10 ↦ᵣ loadPtr) ** (.x11 ↦ᵣ lenW) **
          (.x12 ↦ᵣ balPtr) ** (.x13 ↦ᵣ balLenW) **
          regOwn .x6 ** regOwn .x7 ** regOwn .x16 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          (.x0 ↦ᵣ (0 : Word)) **
          stackFree spVal 6 **
          bytesRegion regionBase bs ** bytesRegion balPtr balBytes **
          (memOwn TypeAddr ** memOwn InnerOffAddr ** teerScratchWithoutTypeOwn)))) h := by
    xperm_hyp hp2
  have hp4 := sepConj_mono_left
    (regIs_implies_regOwn (r := .x14) (v := chainIdW)) h hp3
  have hp5 : ((.x15 ↦ᵣ baiW) **
      (regOwn .x14 ** regOwn .x5 **
        ((.x2 ↦ᵣ spC) **
          (.x1 ↦ᵣ ret) **
          (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
          (.x18 ↦ᵣ balPtr) ** (.x19 ↦ᵣ balLenW) ** (.x20 ↦ᵣ chainIdW) **
          (.x21 ↦ᵣ s5) ** (.x22 ↦ᵣ s6) ** (.x23 ↦ᵣ s7) **
          (.x24 ↦ᵣ s8) ** (.x25 ↦ᵣ s9) **
          (.x26 ↦ᵣ (0 : Word)) **
          (.x27 ↦ᵣ s11) **
          frameSlotsSaved teerFrame spC (teerSavedVals s) **
          (.x10 ↦ᵣ loadPtr) ** (.x11 ↦ᵣ lenW) **
          (.x12 ↦ᵣ balPtr) ** (.x13 ↦ᵣ balLenW) **
          regOwn .x6 ** regOwn .x7 ** regOwn .x16 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          (.x0 ↦ᵣ (0 : Word)) **
          stackFree spVal 6 **
          bytesRegion regionBase bs ** bytesRegion balPtr balBytes **
          (memOwn TypeAddr ** memOwn InnerOffAddr ** teerScratchWithoutTypeOwn)))) h := by
    xperm_hyp hp4
  have hp6 := sepConj_mono_left
    (regIs_implies_regOwn (r := .x15) (v := baiW)) h hp5
  xperm_hyp hp6

/-- Type success post ** ambient (nested, before flatten). -/
def teerTypePostNested
    (spC loadPtr lenW balPtr balLenW chainIdW
      s5 s6 s7 s8 s9 s11 spVal regionBase : Word)
    (bs balBytes : List (BitVec 8)) (s : TeerSaved) : Assertion :=
  ((.x1 ↦ᵣ LinkType) ** (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
    (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) ** (.x18 ↦ᵣ balPtr) **
    bytesRegion regionBase bs **
    memOwn TypeAddr ** memOwn InnerOffAddr **
    regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
    regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
    regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
    regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31) **
  teerTypeAmbient spC balPtr balLenW chainIdW
    s5 s6 s7 s8 s9 s11 spVal balBytes s

/-- AfterBalCheck → AfterTypeBne nested under applied ambient (type Assumed). -/
theorem teerTypeSuccess_applied_nested
    (asm : TypeDispatchAssumedAmbientFull teerLinkedEarly)
    (hentry : asm.entry = TypeEntry)
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
      (teerTypePostNested spC loadPtr lenW balPtr balLenW chainIdW
        s5 s6 s7 s8 s9 s11 spVal regionBase bs balBytes s) := by
  intro s
  have hbal := teerPrologueScratchBal_applied ret spVal spC loadPtr lenW balPtr
    balLenW chainIdW baiW s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 regionBase bs
    balBytes hspC hnez
  have hbalE : cpsTripleWithin 34 E AfterBalCheck teerLinkedEarly _ _ :=
    cpsTripleWithin_extend_code teerEarly_mono_teer hbal
  have hty := teerTypeSuccessAmbient asm hentry regionBase loadPtr lenW balPtr
    bs off len ret loadPtr lenW balPtr balLenW
    hptr hlen hsuccess halign hbound hover hvalid0
  have htyF := cpsTripleWithin_frameR
    (teerTypeAmbient spC balPtr balLenW chainIdW
      s5 s6 s7 s8 s9 s11 spVal balBytes s)
    (pcFree_teerTypeAmbient spC balPtr balLenW chainIdW
      s5 s6 s7 s8 s9 s11 spVal balBytes s) hty
  have hseq := cpsTripleWithin_seq_perm_same_cr
    (teerAfterBalFlat_to_typePre ret spVal spC loadPtr lenW balPtr balLenW
      chainIdW baiW s5 s6 s7 s8 s9 s11 regionBase bs balBytes s)
    hbalE htyF
  -- Align nested post shape with teerTypePostNested.
  exact cpsTripleWithin_weaken (fun _ hp => hp)
    (fun _ hq => by
      unfold teerTypePostNested teerTypeAmbient at *
      xperm_hyp hq) hseq

/-- Flatten type nested post: rebuild teerScratchOwn, applied-style flat. -/
theorem teerTypeSuccess_applied
    (asm : TypeDispatchAssumedAmbientFull teerLinkedEarly)
    (hentry : asm.entry = TypeEntry)
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
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
        regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        stackFree spVal 6 **
        bytesRegion regionBase bs ** bytesRegion balPtr balBytes **
        teerScratchOwn) := by
  intro s
  have h0 := teerTypeSuccess_applied_nested asm hentry ret spVal spC loadPtr lenW
    balPtr balLenW chainIdW baiW s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    regionBase bs balBytes off len hspC hnez hptr hlen hsuccess halign hbound
    hover hvalid0
  exact cpsTripleWithin_weaken (fun _ hp => hp)
    (fun h hq => by
      unfold teerTypePostNested teerTypeAmbient at hq
      -- Rebuild full scratch from type cells + rest.
      have hq1 : (((.x1 ↦ᵣ LinkType) ** (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
          (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) ** (.x18 ↦ᵣ balPtr) **
          bytesRegion regionBase bs **
          memOwn TypeAddr ** memOwn InnerOffAddr **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
          regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31) **
        ((.x2 ↦ᵣ spC) **
          (.x19 ↦ᵣ balLenW) ** (.x20 ↦ᵣ chainIdW) **
          (.x21 ↦ᵣ s5) ** (.x22 ↦ᵣ s6) ** (.x23 ↦ᵣ s7) **
          (.x24 ↦ᵣ s8) ** (.x25 ↦ᵣ s9) **
          (.x26 ↦ᵣ (0 : Word)) **
          (.x27 ↦ᵣ s11) **
          frameSlotsSaved teerFrame spC (teerSavedVals s) **
          stackFree spVal 6 **
          bytesRegion balPtr balBytes **
          teerScratchWithoutTypeOwn)) h := hq
      have hq2 : (((.x1 ↦ᵣ LinkType) ** (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
          (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) ** (.x18 ↦ᵣ balPtr) **
          bytesRegion regionBase bs **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
          regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31) **
        ((.x2 ↦ᵣ spC) **
          (.x19 ↦ᵣ balLenW) ** (.x20 ↦ᵣ chainIdW) **
          (.x21 ↦ᵣ s5) ** (.x22 ↦ᵣ s6) ** (.x23 ↦ᵣ s7) **
          (.x24 ↦ᵣ s8) ** (.x25 ↦ᵣ s9) **
          (.x26 ↦ᵣ (0 : Word)) **
          (.x27 ↦ᵣ s11) **
          frameSlotsSaved teerFrame spC (teerSavedVals s) **
          stackFree spVal 6 **
          bytesRegion balPtr balBytes **
          teerScratchOwn)) h := by
        have hx : ((memOwn TypeAddr ** memOwn InnerOffAddr ** teerScratchWithoutTypeOwn) **
            (((.x1 ↦ᵣ LinkType) ** (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
              (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) ** (.x18 ↦ᵣ balPtr) **
              bytesRegion regionBase bs **
              regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
              regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
              regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
              regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31) **
            ((.x2 ↦ᵣ spC) **
              (.x19 ↦ᵣ balLenW) ** (.x20 ↦ᵣ chainIdW) **
              (.x21 ↦ᵣ s5) ** (.x22 ↦ᵣ s6) ** (.x23 ↦ᵣ s7) **
              (.x24 ↦ᵣ s8) ** (.x25 ↦ᵣ s9) **
              (.x26 ↦ᵣ (0 : Word)) **
              (.x27 ↦ᵣ s11) **
              frameSlotsSaved teerFrame spC (teerSavedVals s) **
              stackFree spVal 6 **
              bytesRegion balPtr balBytes))) h := by
          xperm_hyp hq1
        have hx2 := (sepConj_mono teerScratchOwn_of_type_rest (fun _ hy => hy)) _ hx
        xperm_hyp hx2
      xperm_hyp hq2) h0

#print axioms teerScratchOwn_to_type_rest
#print axioms teerAfterBalFlat_to_typePre
#print axioms teerTypeSuccess_applied_nested
#print axioms teerTypeSuccess_applied

end EvmAsm.Codegen.TxEip7702TeerSpec
