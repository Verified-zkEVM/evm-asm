/-
  Teer front value_nonzero under applied prest.
  E → AfterValueNonzero via FrontRecipient + teerValueNonzeroCycleOk.
-/

import EvmAsm.Codegen.Programs.TxEip7702TeerFrontRecipient
import EvmAsm.Codegen.Programs.TxEip7702TeerValueNonzero
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
import EvmAsm.Codegen.GuestAddrs

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

private abbrev nFrontToWalkNext5Bne : Nat :=
  ((34 + (6 + (1 + nTypeSteps) + 1)) + (5 + 7)) + (1 + 15 + 1 + 2) +
    nWalkNextCycle * 5 + nWalkNext5CycleOnly

private abbrev nFrontToRecipientSave : Nat := nFrontToWalkNext5Bne + 8
private abbrev nFrontToValueNonzero : Nat := nFrontToRecipientSave + nValueNonzeroCyclePub

local macro "pcf" : tactic => `(tactic|
  repeat first
    | apply pcFree_sepConj
    | exact pcFree_regIs
    | exact pcFree_regOwn
    | exact pcFree_memIs
    | exact pcFree_memOwn
    | exact pcFree_emp
    | exact pcFree_pure
    | exact pcFree_frameSlotsSaved
    | exact bytesRegion_pcFree _ _)

/-- WithoutRecipient minus value_nonzero. -/
def teerScratchWithoutVnzOwn : Assertion :=
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
  memOwn (BitVec.ofNat 64 GuestAddrs.teer_success_table) **
  memOwn (BitVec.ofNat 64 GuestAddrs.teer_predelegated_count) **
  memOwn (BitVec.ofNat 64 GuestAddrs.teer_auth_count) **
  memOwn (BitVec.ofNat 64 GuestAddrs.teer_wouldbe_state) **
  memOwn (BitVec.ofNat 64 GuestAddrs.teer_wouldbe_regular) **
  memOwn (BitVec.ofNat 64 GuestAddrs.teer_recover_scratch) **
  memOwn (BitVec.ofNat 64 GuestAddrs.teer_records_ptr)

private theorem pcFree_teerScratchWithoutVnzOwn :
    teerScratchWithoutVnzOwn.pcFree := by
  unfold teerScratchWithoutVnzOwn
  repeat' (first | exact pcFree_memOwn | apply pcFree_sepConj)

theorem teerScratchWithoutRecipient_to_vnz_rest :
    ∀ h, teerScratchWithoutRecipientOwn h →
      (memOwn ValueNonzeroAddr ** teerScratchWithoutVnzOwn) h := by
  intro h hp
  unfold teerScratchWithoutRecipientOwn teerScratchWithoutVnzOwn
    ValueNonzeroAddr at *
  xperm_hyp hp

theorem teerScratchWithoutRecipient_of_vnz_rest :
    ∀ h, (memOwn ValueNonzeroAddr ** teerScratchWithoutVnzOwn) h →
      teerScratchWithoutRecipientOwn h := by
  intro h hp
  unfold teerScratchWithoutRecipientOwn teerScratchWithoutVnzOwn
    ValueNonzeroAddr at *
  xperm_hyp hp

/-- CycleOk with regOwn temps (x5–7, x28–31). -/
theorem teerValueNonzeroCycleOk_ownTemps
    (listBase endPtr : Word)
    (bs : List (BitVec 8)) (srcOff : Nat) (old1 v24 v25 a0Old a1Old a2Old : Word)
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
    let cursor := listBase + BitVec.ofNat 64 srcOff
    cpsTripleWithin nValueNonzeroCyclePub AfterRecipientSave AfterValueNonzero
      teerLinkedEarly
      ((.x1 ↦ᵣ old1) ** (.x24 ↦ᵣ v24) ** (.x25 ↦ᵣ v25) **
        (.x10 ↦ᵣ a0Old) ** (.x11 ↦ᵣ a1Old) ** (.x12 ↦ᵣ a2Old) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs **
        memOwn ValueNonzeroAddr)
      (fun h => ∃ next len : Word,
        ((.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
          (.x24 ↦ᵣ cursor) ** (.x25 ↦ᵣ endPtr) **
          (.x0 ↦ᵣ (0 : Word)) **
          (.x30 ↦ᵣ (if BitVec.ult (0 : Word) len then (1 : Word) else 0)) **
          (.x5 ↦ᵣ ValueNonzeroAddr) **
          regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x31 ** (.x1 ↦ᵣ LinkWalkNextValue) **
          bytesRegion listBase bs ** memOwn ValueNonzeroAddr **
          ⌜rlpItemDecode bs srcOff cursor endPtr next len⌝) h) := by
  intro cursor
  have hcore (t0 t1 t2 t3 t4 t5 t6 : Word) :=
    teerValueNonzeroCycleOk listBase endPtr a2Old t0 t1 t2 t3 t4 t5 t6
      bs srcOff old1 v24 v25 a0Old a1Old
      hsalign hoff hover hvalid hss hls hll hdec hinb hcur hend
  let Q : Assertion := fun h => ∃ next len : Word,
    ((.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
      (.x24 ↦ᵣ cursor) ** (.x25 ↦ᵣ endPtr) **
      (.x0 ↦ᵣ (0 : Word)) **
      (.x30 ↦ᵣ (if BitVec.ult (0 : Word) len then (1 : Word) else 0)) **
      (.x5 ↦ᵣ ValueNonzeroAddr) **
      regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
      regOwn .x31 ** (.x1 ↦ᵣ LinkWalkNextValue) **
      bytesRegion listBase bs ** memOwn ValueNonzeroAddr **
      ⌜rlpItemDecode bs srcOff cursor endPtr next len⌝) h
  -- Lift x31..x5 rightmost; final prest matches theorem (regOwns before x0)
  have hx (t0 t1 t2 t3 t4 t5 : Word) :
      cpsTripleWithin nValueNonzeroCyclePub AfterRecipientSave AfterValueNonzero
        teerLinkedEarly
        ((.x1 ↦ᵣ old1) ** (.x24 ↦ᵣ v24) ** (.x25 ↦ᵣ v25) **
          (.x10 ↦ᵣ a0Old) ** (.x11 ↦ᵣ a1Old) ** (.x12 ↦ᵣ a2Old) **
          (.x5 ↦ᵣ t0) ** (.x6 ↦ᵣ t1) ** (.x7 ↦ᵣ t2) **
          (.x28 ↦ᵣ t3) ** (.x29 ↦ᵣ t4) ** (.x30 ↦ᵣ t5) **
          (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs **
          memOwn ValueNonzeroAddr ** regOwn .x31)
        Q := by
    have h1 := cpsTripleWithin_of_forall_regIs_to_regOwn
      (r := .x31)
      (P := (.x1 ↦ᵣ old1) ** (.x24 ↦ᵣ v24) ** (.x25 ↦ᵣ v25) **
        (.x10 ↦ᵣ a0Old) ** (.x11 ↦ᵣ a1Old) ** (.x12 ↦ᵣ a2Old) **
        (.x5 ↦ᵣ t0) ** (.x6 ↦ᵣ t1) ** (.x7 ↦ᵣ t2) **
        (.x28 ↦ᵣ t3) ** (.x29 ↦ᵣ t4) ** (.x30 ↦ᵣ t5) **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs **
        memOwn ValueNonzeroAddr)
      (fun t6 =>
        cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
          (fun _ hq => hq) (hcore t0 t1 t2 t3 t4 t5 t6))
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => hq) h1
  have h2 (t0 t1 t2 t3 t4 : Word) :
      cpsTripleWithin nValueNonzeroCyclePub AfterRecipientSave AfterValueNonzero
        teerLinkedEarly
        ((.x1 ↦ᵣ old1) ** (.x24 ↦ᵣ v24) ** (.x25 ↦ᵣ v25) **
          (.x10 ↦ᵣ a0Old) ** (.x11 ↦ᵣ a1Old) ** (.x12 ↦ᵣ a2Old) **
          (.x5 ↦ᵣ t0) ** (.x6 ↦ᵣ t1) ** (.x7 ↦ᵣ t2) **
          (.x28 ↦ᵣ t3) ** (.x29 ↦ᵣ t4) **
          (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs **
          memOwn ValueNonzeroAddr ** regOwn .x30 ** regOwn .x31)
        Q := by
    have h1 := cpsTripleWithin_of_forall_regIs_to_regOwn
      (r := .x30)
      (P := (.x1 ↦ᵣ old1) ** (.x24 ↦ᵣ v24) ** (.x25 ↦ᵣ v25) **
        (.x10 ↦ᵣ a0Old) ** (.x11 ↦ᵣ a1Old) ** (.x12 ↦ᵣ a2Old) **
        (.x5 ↦ᵣ t0) ** (.x6 ↦ᵣ t1) ** (.x7 ↦ᵣ t2) **
        (.x28 ↦ᵣ t3) ** (.x29 ↦ᵣ t4) **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs **
        memOwn ValueNonzeroAddr ** regOwn .x31)
      (fun t5 =>
        cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
          (fun _ hq => hq) (hx t0 t1 t2 t3 t4 t5))
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => hq) h1
  have h3 (t0 t1 t2 t3 : Word) :
      cpsTripleWithin nValueNonzeroCyclePub AfterRecipientSave AfterValueNonzero
        teerLinkedEarly
        ((.x1 ↦ᵣ old1) ** (.x24 ↦ᵣ v24) ** (.x25 ↦ᵣ v25) **
          (.x10 ↦ᵣ a0Old) ** (.x11 ↦ᵣ a1Old) ** (.x12 ↦ᵣ a2Old) **
          (.x5 ↦ᵣ t0) ** (.x6 ↦ᵣ t1) ** (.x7 ↦ᵣ t2) **
          (.x28 ↦ᵣ t3) **
          (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs **
          memOwn ValueNonzeroAddr **
          regOwn .x29 ** regOwn .x30 ** regOwn .x31)
        Q := by
    have h1 := cpsTripleWithin_of_forall_regIs_to_regOwn
      (r := .x29)
      (P := (.x1 ↦ᵣ old1) ** (.x24 ↦ᵣ v24) ** (.x25 ↦ᵣ v25) **
        (.x10 ↦ᵣ a0Old) ** (.x11 ↦ᵣ a1Old) ** (.x12 ↦ᵣ a2Old) **
        (.x5 ↦ᵣ t0) ** (.x6 ↦ᵣ t1) ** (.x7 ↦ᵣ t2) **
        (.x28 ↦ᵣ t3) **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs **
        memOwn ValueNonzeroAddr ** regOwn .x30 ** regOwn .x31)
      (fun t4 =>
        cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
          (fun _ hq => hq) (h2 t0 t1 t2 t3 t4))
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => hq) h1
  have h4 (t0 t1 t2 : Word) :
      cpsTripleWithin nValueNonzeroCyclePub AfterRecipientSave AfterValueNonzero
        teerLinkedEarly
        ((.x1 ↦ᵣ old1) ** (.x24 ↦ᵣ v24) ** (.x25 ↦ᵣ v25) **
          (.x10 ↦ᵣ a0Old) ** (.x11 ↦ᵣ a1Old) ** (.x12 ↦ᵣ a2Old) **
          (.x5 ↦ᵣ t0) ** (.x6 ↦ᵣ t1) ** (.x7 ↦ᵣ t2) **
          (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs **
          memOwn ValueNonzeroAddr **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
        Q := by
    have h1 := cpsTripleWithin_of_forall_regIs_to_regOwn
      (r := .x28)
      (P := (.x1 ↦ᵣ old1) ** (.x24 ↦ᵣ v24) ** (.x25 ↦ᵣ v25) **
        (.x10 ↦ᵣ a0Old) ** (.x11 ↦ᵣ a1Old) ** (.x12 ↦ᵣ a2Old) **
        (.x5 ↦ᵣ t0) ** (.x6 ↦ᵣ t1) ** (.x7 ↦ᵣ t2) **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs **
        memOwn ValueNonzeroAddr **
        regOwn .x29 ** regOwn .x30 ** regOwn .x31)
      (fun t3 =>
        cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
          (fun _ hq => hq) (h3 t0 t1 t2 t3))
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => hq) h1
  have h5 (t0 t1 : Word) :
      cpsTripleWithin nValueNonzeroCyclePub AfterRecipientSave AfterValueNonzero
        teerLinkedEarly
        ((.x1 ↦ᵣ old1) ** (.x24 ↦ᵣ v24) ** (.x25 ↦ᵣ v25) **
          (.x10 ↦ᵣ a0Old) ** (.x11 ↦ᵣ a1Old) ** (.x12 ↦ᵣ a2Old) **
          (.x5 ↦ᵣ t0) ** (.x6 ↦ᵣ t1) **
          (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs **
          memOwn ValueNonzeroAddr **
          regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
        Q := by
    have h1 := cpsTripleWithin_of_forall_regIs_to_regOwn
      (r := .x7)
      (P := (.x1 ↦ᵣ old1) ** (.x24 ↦ᵣ v24) ** (.x25 ↦ᵣ v25) **
        (.x10 ↦ᵣ a0Old) ** (.x11 ↦ᵣ a1Old) ** (.x12 ↦ᵣ a2Old) **
        (.x5 ↦ᵣ t0) ** (.x6 ↦ᵣ t1) **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs **
        memOwn ValueNonzeroAddr **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
      (fun t2 =>
        cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
          (fun _ hq => hq) (h4 t0 t1 t2))
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => hq) h1
  have h6 (t0 : Word) :
      cpsTripleWithin nValueNonzeroCyclePub AfterRecipientSave AfterValueNonzero
        teerLinkedEarly
        ((.x1 ↦ᵣ old1) ** (.x24 ↦ᵣ v24) ** (.x25 ↦ᵣ v25) **
          (.x10 ↦ᵣ a0Old) ** (.x11 ↦ᵣ a1Old) ** (.x12 ↦ᵣ a2Old) **
          (.x5 ↦ᵣ t0) **
          (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs **
          memOwn ValueNonzeroAddr **
          regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31)
        Q := by
    have h1 := cpsTripleWithin_of_forall_regIs_to_regOwn
      (r := .x6)
      (P := (.x1 ↦ᵣ old1) ** (.x24 ↦ᵣ v24) ** (.x25 ↦ᵣ v25) **
        (.x10 ↦ᵣ a0Old) ** (.x11 ↦ᵣ a1Old) ** (.x12 ↦ᵣ a2Old) **
        (.x5 ↦ᵣ t0) **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs **
        memOwn ValueNonzeroAddr **
        regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
      (fun t1 =>
        cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
          (fun _ hq => hq) (h5 t0 t1))
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => hq) h1
  have h7 :
      cpsTripleWithin nValueNonzeroCyclePub AfterRecipientSave AfterValueNonzero
        teerLinkedEarly
        ((.x1 ↦ᵣ old1) ** (.x24 ↦ᵣ v24) ** (.x25 ↦ᵣ v25) **
          (.x10 ↦ᵣ a0Old) ** (.x11 ↦ᵣ a1Old) ** (.x12 ↦ᵣ a2Old) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs **
          memOwn ValueNonzeroAddr)
        Q := by
    have h1 := cpsTripleWithin_of_forall_regIs_to_regOwn
      (r := .x5)
      (P := (.x1 ↦ᵣ old1) ** (.x24 ↦ᵣ v24) ** (.x25 ↦ᵣ v25) **
        (.x10 ↦ᵣ a0Old) ** (.x11 ↦ᵣ a1Old) ** (.x12 ↦ᵣ a2Old) **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs **
        memOwn ValueNonzeroAddr **
        regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31)
      (fun t0 =>
        cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
          (fun _ hq => hq) (h6 t0))
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => hq) h1
  exact h7

def teerValueNonzeroAmbient
    (spVal spC loadPtr lenW balPtr balLenW chainIdW : Word)
    (s : TeerSaved) (_regionBase : Word) (_bs balBytes : List (BitVec 8))
    (innerVal : Word) (s7 s11 : Word) : Assertion :=
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
    memOwn RecipientPtrAddr ** memOwn RecipientLenAddr **
    teerScratchWithoutVnzOwn

private theorem pcFree_teerValueNonzeroAmbient
    (spVal spC loadPtr lenW balPtr balLenW chainIdW : Word)
    (s : TeerSaved) (regionBase : Word) (bs balBytes : List (BitVec 8))
    (innerVal : Word) (s7 s11 : Word) :
    (teerValueNonzeroAmbient spVal spC loadPtr lenW balPtr balLenW chainIdW
      s regionBase bs balBytes innerVal s7 s11).pcFree := by
  unfold teerValueNonzeroAmbient; pcf

def teerValueNonzeroBodyPost
    (regionBase : Word) (bs : List (BitVec 8))
    (next lenV cursor endW : Word) : Assertion :=
  (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ lenV) **
    (.x24 ↦ᵣ cursor) ** (.x25 ↦ᵣ endW) **
    (.x0 ↦ᵣ (0 : Word)) **
    (.x30 ↦ᵣ (if BitVec.ult (0 : Word) lenV then (1 : Word) else 0)) **
    (.x5 ↦ᵣ ValueNonzeroAddr) **
    regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
    regOwn .x31 ** (.x1 ↦ᵣ LinkWalkNextValue) **
    bytesRegion regionBase bs ** memOwn ValueNonzeroAddr

def teerValueNonzeroFocus
    (regionBase : Word) (bs : List (BitVec 8))
    (old1 v24 v25 a0Old a1Old a2Old : Word) : Assertion :=
  (.x1 ↦ᵣ old1) ** (.x24 ↦ᵣ v24) ** (.x25 ↦ᵣ v25) **
    (.x10 ↦ᵣ a0Old) ** (.x11 ↦ᵣ a1Old) ** (.x12 ↦ᵣ a2Old) **
    regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
    regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
    (.x0 ↦ᵣ (0 : Word)) ** bytesRegion regionBase bs **
    memOwn ValueNonzeroAddr

/-- Recipient flat body (no pure) for reshape. -/
def teerRecipientFlatRest
    (spVal spC loadPtr lenW balPtr balLenW chainIdW : Word)
    (s : TeerSaved) (regionBase : Word) (bs balBytes : List (BitVec 8))
    (innerVal endW : Word) (s7 s11 next len5 : Word) : Assertion :=
  (.x2 ↦ᵣ spC) **
    (.x1 ↦ᵣ LinkWalkNext5) **
    (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
    (.x18 ↦ᵣ balPtr) ** (.x19 ↦ᵣ balLenW) ** (.x20 ↦ᵣ chainIdW) **
    (.x21 ↦ᵣ loadPtr + innerVal) ** (.x22 ↦ᵣ lenW - innerVal) **
    (.x23 ↦ᵣ s7) **
    (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len5) **
    (.x24 ↦ᵣ next) ** (.x25 ↦ᵣ endW) **
    (.x26 ↦ᵣ (0 : Word)) **
    (.x27 ↦ᵣ s11) **
    frameSlotsSaved teerFrame spC (teerSavedVals s) **
    (.x0 ↦ᵣ (0 : Word)) **
    (TypeAddr ↦ₘ (4 : Word)) ** (InnerOffAddr ↦ₘ innerVal) **
    (.x30 ↦ᵣ (next - len5)) ** (.x5 ↦ᵣ RecipientLenAddr) **
    regOwn .x6 ** regOwn .x7 **
    regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
    regOwn .x28 ** regOwn .x29 ** regOwn .x31 **
    stackFree spVal 6 **
    bytesRegion regionBase bs ** bytesRegion balPtr balBytes **
    memOwn RecipientPtrAddr ** memOwn RecipientLenAddr **
    teerScratchWithoutRecipientOwn

theorem teerRecipientFlatRest_to_vnzPre
    (spVal spC loadPtr lenW balPtr balLenW chainIdW : Word)
    (s : TeerSaved) (regionBase : Word) (bs balBytes : List (BitVec 8))
    (innerVal endW : Word) (s7 s11 next len5 : Word) :
    ∀ h,
      (teerRecipientFlatRest spVal spC loadPtr lenW balPtr balLenW chainIdW
          s regionBase bs balBytes innerVal endW s7 s11 next len5) h →
      (teerValueNonzeroFocus regionBase bs
          LinkWalkNext5 next endW next (0 : Word) len5 **
        teerValueNonzeroAmbient spVal spC loadPtr lenW balPtr balLenW chainIdW
          s regionBase bs balBytes innerVal s7 s11) h := by
  intro h hp
  unfold teerRecipientFlatRest at hp
  -- Pull x5 left; mono regIs→regOwn (FrontType peel pattern)
  have hp1 :
      ((.x5 ↦ᵣ RecipientLenAddr) **
        ((.x2 ↦ᵣ spC) **
          (.x1 ↦ᵣ LinkWalkNext5) **
          (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
          (.x18 ↦ᵣ balPtr) ** (.x19 ↦ᵣ balLenW) ** (.x20 ↦ᵣ chainIdW) **
          (.x21 ↦ᵣ loadPtr + innerVal) ** (.x22 ↦ᵣ lenW - innerVal) **
          (.x23 ↦ᵣ s7) **
          (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len5) **
          (.x24 ↦ᵣ next) ** (.x25 ↦ᵣ endW) **
          (.x26 ↦ᵣ (0 : Word)) **
          (.x27 ↦ᵣ s11) **
          frameSlotsSaved teerFrame spC (teerSavedVals s) **
          (.x0 ↦ᵣ (0 : Word)) **
          (TypeAddr ↦ₘ (4 : Word)) ** (InnerOffAddr ↦ₘ innerVal) **
          (.x30 ↦ᵣ (next - len5)) **
          regOwn .x6 ** regOwn .x7 **
          regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x31 **
          stackFree spVal 6 **
          bytesRegion regionBase bs ** bytesRegion balPtr balBytes **
          memOwn RecipientPtrAddr ** memOwn RecipientLenAddr **
          teerScratchWithoutRecipientOwn)) h := by
    xperm_hyp hp
  have hp2 := sepConj_mono_left
    (regIs_implies_regOwn (r := .x5) (v := RecipientLenAddr)) h hp1
  -- Pull x30 left; mono regIs→regOwn
  have hp3 :
      ((.x30 ↦ᵣ (next - len5)) **
        (regOwn .x5 **
          ((.x2 ↦ᵣ spC) **
            (.x1 ↦ᵣ LinkWalkNext5) **
            (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
            (.x18 ↦ᵣ balPtr) ** (.x19 ↦ᵣ balLenW) ** (.x20 ↦ᵣ chainIdW) **
            (.x21 ↦ᵣ loadPtr + innerVal) ** (.x22 ↦ᵣ lenW - innerVal) **
            (.x23 ↦ᵣ s7) **
            (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len5) **
            (.x24 ↦ᵣ next) ** (.x25 ↦ᵣ endW) **
            (.x26 ↦ᵣ (0 : Word)) **
            (.x27 ↦ᵣ s11) **
            frameSlotsSaved teerFrame spC (teerSavedVals s) **
            (.x0 ↦ᵣ (0 : Word)) **
            (TypeAddr ↦ₘ (4 : Word)) ** (InnerOffAddr ↦ₘ innerVal) **
            regOwn .x6 ** regOwn .x7 **
            regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
            regOwn .x28 ** regOwn .x29 ** regOwn .x31 **
            stackFree spVal 6 **
            bytesRegion regionBase bs ** bytesRegion balPtr balBytes **
            memOwn RecipientPtrAddr ** memOwn RecipientLenAddr **
            teerScratchWithoutRecipientOwn))) h := by
    xperm_hyp hp2
  have hp4 := sepConj_mono_left
    (regIs_implies_regOwn (r := .x30) (v := next - len5)) h hp3
  -- Pull scratch left; peel Vnz ** WithoutVnz
  have hp5 :
      (teerScratchWithoutRecipientOwn **
        (regOwn .x30 ** regOwn .x5 **
          ((.x2 ↦ᵣ spC) **
            (.x1 ↦ᵣ LinkWalkNext5) **
            (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
            (.x18 ↦ᵣ balPtr) ** (.x19 ↦ᵣ balLenW) ** (.x20 ↦ᵣ chainIdW) **
            (.x21 ↦ᵣ loadPtr + innerVal) ** (.x22 ↦ᵣ lenW - innerVal) **
            (.x23 ↦ᵣ s7) **
            (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len5) **
            (.x24 ↦ᵣ next) ** (.x25 ↦ᵣ endW) **
            (.x26 ↦ᵣ (0 : Word)) **
            (.x27 ↦ᵣ s11) **
            frameSlotsSaved teerFrame spC (teerSavedVals s) **
            (.x0 ↦ᵣ (0 : Word)) **
            (TypeAddr ↦ₘ (4 : Word)) ** (InnerOffAddr ↦ₘ innerVal) **
            regOwn .x6 ** regOwn .x7 **
            regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
            regOwn .x28 ** regOwn .x29 ** regOwn .x31 **
            stackFree spVal 6 **
            bytesRegion regionBase bs ** bytesRegion balPtr balBytes **
            memOwn RecipientPtrAddr ** memOwn RecipientLenAddr))) h := by
    xperm_hyp hp4
  have hp6 := sepConj_mono_left teerScratchWithoutRecipient_to_vnz_rest h hp5
  unfold teerValueNonzeroFocus teerValueNonzeroAmbient
    ValueNonzeroAddr RecipientPtrAddr RecipientLenAddr
  xperm_hyp hp6

#print axioms teerValueNonzeroCycleOk_ownTemps
#print axioms teerScratchWithoutRecipient_to_vnz_rest
#print axioms teerRecipientFlatRest_to_vnzPre

set_option maxRecDepth 8000 in
theorem teerValueNonzero_applied
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
      next5 = regionBase + BitVec.ofNat 64 srcOffV) :
    let s : TeerSaved :=
      { ra := ret, s0 := s0, s1 := s1, s2 := s2, s3 := s3, s4 := s4
        s5 := s5, s6 := s6, s7 := s7, s8 := s8, s9 := s9
        s10 := s10, s11 := s11, a5 := baiW }
    let innerVal := (teerTxTypeDispatch (txSlice bs off len)).2.2
    let endW := (regionBase + BitVec.ofNat 64 listOff) + (lenW - innerVal)
    cpsTripleWithin nFrontToValueNonzero
      E AfterValueNonzero teerLinkedEarly
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
      (fun h => ∃ next lenV : Word,
        (((.x2 ↦ᵣ spC) **
          (.x1 ↦ᵣ LinkWalkNextValue) **
          (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
          (.x18 ↦ᵣ balPtr) ** (.x19 ↦ᵣ balLenW) ** (.x20 ↦ᵣ chainIdW) **
          (.x21 ↦ᵣ loadPtr + innerVal) ** (.x22 ↦ᵣ lenW - innerVal) **
          (.x23 ↦ᵣ s7) **
          (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ lenV) **
          (.x24 ↦ᵣ (regionBase + BitVec.ofNat 64 srcOffV)) ** (.x25 ↦ᵣ endW) **
          (.x26 ↦ᵣ (0 : Word)) **
          (.x27 ↦ᵣ s11) **
          frameSlotsSaved teerFrame spC (teerSavedVals s) **
          (.x0 ↦ᵣ (0 : Word)) **
          (TypeAddr ↦ₘ (4 : Word)) ** (InnerOffAddr ↦ₘ innerVal) **
          (.x30 ↦ᵣ (if BitVec.ult (0 : Word) lenV then (1 : Word) else 0)) **
          (.x5 ↦ᵣ ValueNonzeroAddr) **
          regOwn .x6 ** regOwn .x7 **
          regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x31 **
          stackFree spVal 6 **
          bytesRegion regionBase bs ** bytesRegion balPtr balBytes **
          memOwn RecipientPtrAddr ** memOwn RecipientLenAddr **
          memOwn ValueNonzeroAddr **
          teerScratchWithoutVnzOwn) **
          ⌜rlpItemDecode bs srcOffV (regionBase + BitVec.ofNat 64 srcOffV)
            endW next lenV⌝) h) := by
  intro s innerVal endW
  have hrec := teerRecipient_applied ret spVal spC loadPtr lenW
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
  let Flat (p : Word × Word) : Assertion :=
    teerRecipientFlatRest spVal spC loadPtr lenW balPtr balLenW chainIdW
      s regionBase bs balBytes innerVal endW s7 s11 p.1 p.2 **
    ⌜rlpItemDecode bs srcOff5 (regionBase + BitVec.ofNat 64 srcOff5)
      endW p.1 p.2⌝
  have hrecE :
      cpsTripleWithin nFrontToRecipientSave E AfterRecipientSave teerLinkedEarly
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
    refine cpsTripleWithin_weaken (fun _ hp => hp) (fun h hq => ?_) hrec
    obtain ⟨next, len5, hq'⟩ := hq
    refine ⟨(next, len5), ?_⟩
    dsimp only [Flat, teerRecipientFlatRest]
    xperm_hyp hq'
  let VnzPost : Assertion := fun h =>
    ∃ next lenV : Word,
      ((teerValueNonzeroBodyPost regionBase bs next lenV
          (regionBase + BitVec.ofNat 64 srcOffV) endW **
        teerValueNonzeroAmbient spVal spC loadPtr lenW balPtr balLenW chainIdW
          s regionBase bs balBytes innerVal s7 s11) **
        ⌜rlpItemDecode bs srcOffV (regionBase + BitVec.ofNat 64 srcOffV)
          endW next lenV⌝) h
  have hstep (p : Word × Word) :
      cpsTripleWithin nValueNonzeroCyclePub AfterRecipientSave AfterValueNonzero
        teerLinkedEarly (Flat p) VnzPost := by
    dsimp only [Flat]
    have hswap :
        cpsTripleWithin nValueNonzeroCyclePub AfterRecipientSave AfterValueNonzero
          teerLinkedEarly
          (⌜rlpItemDecode bs srcOff5 (regionBase + BitVec.ofNat 64 srcOff5)
              endW p.1 p.2⌝ **
            teerRecipientFlatRest spVal spC loadPtr lenW balPtr balLenW chainIdW
              s regionBase bs balBytes innerVal endW s7 s11 p.1 p.2)
          VnzPost := by
      refine cpsTripleWithin_pure_pre (fun hpure => ?_)
      have hcurV : p.1 = regionBase + BitVec.ofNat 64 srcOffV :=
        hbridge5 p.1 p.2 hpure
      have hstore := teerValueNonzeroCycleOk_ownTemps regionBase endW bs srcOffV
        LinkWalkNext5 p.1 endW p.1 (0 : Word) p.2
        halign hoffV hoverV hvalidV hssV hlsV hllV hdecV hinbV hcurV rfl
      have hstoreF := cpsTripleWithin_frameR
        (teerValueNonzeroAmbient spVal spC loadPtr lenW balPtr balLenW chainIdW
          s regionBase bs balBytes innerVal s7 s11)
        (pcFree_teerValueNonzeroAmbient spVal spC loadPtr lenW balPtr balLenW
          chainIdW s regionBase bs balBytes innerVal s7 s11) hstore
      have hstoreW :
          cpsTripleWithin nValueNonzeroCyclePub AfterRecipientSave AfterValueNonzero
            teerLinkedEarly
            (teerRecipientFlatRest spVal spC loadPtr lenW balPtr balLenW chainIdW
              s regionBase bs balBytes innerVal endW s7 s11 p.1 p.2)
            VnzPost := by
        refine cpsTripleWithin_weaken
          (teerRecipientFlatRest_to_vnzPre
            spVal spC loadPtr lenW balPtr balLenW chainIdW s regionBase bs balBytes
            innerVal endW s7 s11 p.1 p.2)
          (fun h hq => ?_) hstoreF
        -- frameR post = (fun h => ∃ next len, ownTempsBody) ** Amb
        -- Float ∃ via pair reshape + sepConj_exists_left (CycleOk pattern)
        let Amb := teerValueNonzeroAmbient spVal spC loadPtr lenW balPtr balLenW
          chainIdW s regionBase bs balBytes innerVal s7 s11
        let cursorV := regionBase + BitVec.ofNat 64 srcOffV
        have hqP :
            ((fun hp => ∃ q : Word × Word,
                ((.x10 ↦ᵣ q.1) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ q.2) **
                  (.x24 ↦ᵣ cursorV) ** (.x25 ↦ᵣ endW) **
                  (.x0 ↦ᵣ (0 : Word)) **
                  (.x30 ↦ᵣ (if BitVec.ult (0 : Word) q.2 then (1 : Word) else 0)) **
                  (.x5 ↦ᵣ ValueNonzeroAddr) **
                  regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
                  regOwn .x31 ** (.x1 ↦ᵣ LinkWalkNextValue) **
                  bytesRegion regionBase bs ** memOwn ValueNonzeroAddr **
                  ⌜rlpItemDecode bs srcOffV cursorV endW q.1 q.2⌝) hp) **
              Amb) h := by
          -- Destructure frameR heap split; ownTemps post is nested ∃ inside left
          obtain ⟨h1, h2, hd, hu, hEx, hR⟩ := hq
          obtain ⟨nxt, ln, hB⟩ := hEx
          exact ⟨h1, h2, hd, hu, ⟨(nxt, ln), hB⟩, hR⟩
        have hq1 :=
          (sepConj_exists_left
            (F := fun (q : Word × Word) =>
              (.x10 ↦ᵣ q.1) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ q.2) **
                (.x24 ↦ᵣ cursorV) ** (.x25 ↦ᵣ endW) **
                (.x0 ↦ᵣ (0 : Word)) **
                (.x30 ↦ᵣ (if BitVec.ult (0 : Word) q.2 then (1 : Word) else 0)) **
                (.x5 ↦ᵣ ValueNonzeroAddr) **
                regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
                regOwn .x31 ** (.x1 ↦ᵣ LinkWalkNextValue) **
                bytesRegion regionBase bs ** memOwn ValueNonzeroAddr **
                ⌜rlpItemDecode bs srcOffV cursorV endW q.1 q.2⌝)
            (R := Amb) h).mp hqP
        obtain ⟨⟨nxt, ln⟩, hq4⟩ := hq1
        -- hq4 : (ownTemps body ** pure) ** Amb
        refine ⟨nxt, ln, ?_⟩
        have hq2 :
            ((teerValueNonzeroBodyPost regionBase bs nxt ln cursorV endW **
              ⌜rlpItemDecode bs srcOffV cursorV endW nxt ln⌝) ** Amb) h := by
          unfold teerValueNonzeroBodyPost
          xperm_hyp hq4
        have hq3 :
            ((teerValueNonzeroBodyPost regionBase bs nxt ln cursorV endW ** Amb) **
              ⌜rlpItemDecode bs srcOffV cursorV endW nxt ln⌝) h := by
          unfold teerValueNonzeroBodyPost at hq2 ⊢
          xperm_hyp hq2
        exact hq3
      exact hstoreW
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => hq) hswap
  have hseq := cpsTripleWithin_seq_exists_same_cr hrecE hstep
  have hmono := cpsTripleWithin_mono_nSteps
    (by decide : nFrontToRecipientSave + nValueNonzeroCyclePub ≤ nFrontToValueNonzero)
    hseq
  refine cpsTripleWithin_weaken (fun _ hp => hp) (fun h hq => ?_) hmono
  obtain ⟨next, lenV, hq'⟩ := hq
  refine ⟨next, lenV, ?_⟩
  have hq2 := (sepConj_pure_right _).1 hq'
  obtain ⟨hqBodyAmb, hpure⟩ := hq2
  unfold teerValueNonzeroBodyPost teerValueNonzeroAmbient at hqBodyAmb
  have hqflat :
      ((.x2 ↦ᵣ spC) **
        (.x1 ↦ᵣ LinkWalkNextValue) **
        (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
        (.x18 ↦ᵣ balPtr) ** (.x19 ↦ᵣ balLenW) ** (.x20 ↦ᵣ chainIdW) **
        (.x21 ↦ᵣ loadPtr + innerVal) ** (.x22 ↦ᵣ lenW - innerVal) **
        (.x23 ↦ᵣ s7) **
        (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ lenV) **
        (.x24 ↦ᵣ (regionBase + BitVec.ofNat 64 srcOffV)) ** (.x25 ↦ᵣ endW) **
        (.x26 ↦ᵣ (0 : Word)) **
        (.x27 ↦ᵣ s11) **
        frameSlotsSaved teerFrame spC (teerSavedVals s) **
        (.x0 ↦ᵣ (0 : Word)) **
        (TypeAddr ↦ₘ (4 : Word)) ** (InnerOffAddr ↦ₘ innerVal) **
        (.x30 ↦ᵣ (if BitVec.ult (0 : Word) lenV then (1 : Word) else 0)) **
        (.x5 ↦ᵣ ValueNonzeroAddr) **
        regOwn .x6 ** regOwn .x7 **
        regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x31 **
        stackFree spVal 6 **
        bytesRegion regionBase bs ** bytesRegion balPtr balBytes **
        memOwn RecipientPtrAddr ** memOwn RecipientLenAddr **
        memOwn ValueNonzeroAddr **
        teerScratchWithoutVnzOwn) h := by
    xperm_hyp hqBodyAmb
  exact (sepConj_pure_right _).2 ⟨hqflat, hpure⟩


#print axioms teerValueNonzero_applied

end EvmAsm.Codegen.TxEip7702TeerSpec
