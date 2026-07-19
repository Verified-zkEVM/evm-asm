/-
  Teer front recipient store under applied prest.
  E → AfterRecipientSave via FrontWalkNext5 + teerRecipientStore.
-/

import EvmAsm.Codegen.Programs.TxEip7702TeerFrontWalkNext5
import EvmAsm.Codegen.Programs.TxEip7702TeerRecipient
import EvmAsm.Codegen.Programs.TxTypeDispatchAmbient
import EvmAsm.Codegen.Programs.TxIntrinsicStateGasSpec
import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SAsm.MeasureLoop
import EvmAsm.Rv64.SAsm.StmtSoundCall
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

private abbrev nFrontToWalkNext5Bne : Nat :=
  ((34 + (6 + (1 + nTypeSteps) + 1)) + (5 + 7)) + (1 + 15 + 1 + 2) +
    nWalkNextCycle * 5 + nWalkNext5CycleOnly

private abbrev nFrontToRecipientSave : Nat := nFrontToWalkNext5Bne + 8

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

/-- WithoutType minus recipient_ptr/len. -/
def teerScratchWithoutRecipientOwn : Assertion :=
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
  memOwn (BitVec.ofNat 64 GuestAddrs.teer_predelegated_count) **
  memOwn (BitVec.ofNat 64 GuestAddrs.teer_auth_count) **
  memOwn (BitVec.ofNat 64 GuestAddrs.teer_wouldbe_state) **
  memOwn (BitVec.ofNat 64 GuestAddrs.teer_wouldbe_regular) **
  memOwn (BitVec.ofNat 64 GuestAddrs.teer_recover_scratch) **
  memOwn (BitVec.ofNat 64 GuestAddrs.teer_records_ptr)

private theorem pcFree_teerScratchWithoutRecipientOwn :
    teerScratchWithoutRecipientOwn.pcFree := by
  unfold teerScratchWithoutRecipientOwn
  repeat' (first | exact pcFree_memOwn | apply pcFree_sepConj)

theorem teerScratchWithoutType_to_recipient_rest :
    ∀ h, teerScratchWithoutTypeOwn h →
      (memOwn RecipientPtrAddr ** memOwn RecipientLenAddr **
        teerScratchWithoutRecipientOwn) h := by
  intro h hp
  unfold teerScratchWithoutTypeOwn teerScratchWithoutRecipientOwn
    RecipientPtrAddr RecipientLenAddr at *
  xperm_hyp hp

theorem teerScratchWithoutType_of_recipient_rest :
    ∀ h, (memOwn RecipientPtrAddr ** memOwn RecipientLenAddr **
        teerScratchWithoutRecipientOwn) h →
      teerScratchWithoutTypeOwn h := by
  intro h hp
  unfold teerScratchWithoutTypeOwn teerScratchWithoutRecipientOwn
    RecipientPtrAddr RecipientLenAddr at *
  xperm_hyp hp

/-- Recipient store with regOwn x5/x30. -/
theorem teerRecipientStore_ownTemps (next lenW v24 : Word) :
    cpsTripleWithin 8 AfterWalkNext5Bne AfterRecipientSave teerLinkedEarly
      ((.x10 ↦ᵣ next) ** (.x12 ↦ᵣ lenW) **
        (.x24 ↦ᵣ v24) **
        memOwn RecipientPtrAddr ** memOwn RecipientLenAddr **
        regOwn .x30 ** regOwn .x5)
      ((.x10 ↦ᵣ next) ** (.x12 ↦ᵣ lenW) **
        (.x30 ↦ᵣ (next - lenW)) ** (.x5 ↦ᵣ RecipientLenAddr) **
        (.x24 ↦ᵣ next) **
        memOwn RecipientPtrAddr ** memOwn RecipientLenAddr) := by
  have hcore (t5 v5 : Word) :
      cpsTripleWithin 8 AfterWalkNext5Bne AfterRecipientSave teerLinkedEarly
        ((.x10 ↦ᵣ next) ** (.x12 ↦ᵣ lenW) **
          (.x30 ↦ᵣ t5) ** (.x5 ↦ᵣ v5) ** (.x24 ↦ᵣ v24) **
          memOwn RecipientPtrAddr ** memOwn RecipientLenAddr)
        ((.x10 ↦ᵣ next) ** (.x12 ↦ᵣ lenW) **
          (.x30 ↦ᵣ (next - lenW)) ** (.x5 ↦ᵣ RecipientLenAddr) **
          (.x24 ↦ᵣ next) **
          memOwn RecipientPtrAddr ** memOwn RecipientLenAddr) :=
    teerRecipientStore next lenW t5 v5 v24
  have h5 (t5 : Word) :
      cpsTripleWithin 8 AfterWalkNext5Bne AfterRecipientSave teerLinkedEarly
        ((.x10 ↦ᵣ next) ** (.x12 ↦ᵣ lenW) **
          (.x30 ↦ᵣ t5) ** (.x24 ↦ᵣ v24) **
          memOwn RecipientPtrAddr ** memOwn RecipientLenAddr **
          regOwn .x5)
        ((.x10 ↦ᵣ next) ** (.x12 ↦ᵣ lenW) **
          (.x30 ↦ᵣ (next - lenW)) ** (.x5 ↦ᵣ RecipientLenAddr) **
          (.x24 ↦ᵣ next) **
          memOwn RecipientPtrAddr ** memOwn RecipientLenAddr) := by
    have h0 := cpsTripleWithin_of_forall_regIs_to_regOwn
      (r := .x5)
      (P := (.x10 ↦ᵣ next) ** (.x12 ↦ᵣ lenW) **
        (.x30 ↦ᵣ t5) ** (.x24 ↦ᵣ v24) **
        memOwn RecipientPtrAddr ** memOwn RecipientLenAddr)
      (fun v5 =>
        cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
          (fun _ hq => hq) (hcore t5 v5))
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => hq) h0
  have h30 :
      cpsTripleWithin 8 AfterWalkNext5Bne AfterRecipientSave teerLinkedEarly
        ((.x10 ↦ᵣ next) ** (.x12 ↦ᵣ lenW) **
          (.x24 ↦ᵣ v24) **
          memOwn RecipientPtrAddr ** memOwn RecipientLenAddr **
          regOwn .x30 ** regOwn .x5)
        ((.x10 ↦ᵣ next) ** (.x12 ↦ᵣ lenW) **
          (.x30 ↦ᵣ (next - lenW)) ** (.x5 ↦ᵣ RecipientLenAddr) **
          (.x24 ↦ᵣ next) **
          memOwn RecipientPtrAddr ** memOwn RecipientLenAddr) := by
    have h0 := cpsTripleWithin_of_forall_regIs_to_regOwn
      (r := .x30)
      (P := (.x10 ↦ᵣ next) ** (.x12 ↦ᵣ lenW) **
        (.x24 ↦ᵣ v24) **
        memOwn RecipientPtrAddr ** memOwn RecipientLenAddr **
        regOwn .x5)
      (fun t5 =>
        cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
          (fun _ hq => hq) (h5 t5))
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => hq) h0
  exact h30

/-- Ambient around recipient focus. -/
def teerRecipientAmbient
    (spVal spC loadPtr lenW balPtr balLenW chainIdW : Word)
    (s : TeerSaved) (regionBase : Word) (bs balBytes : List (BitVec 8))
    (innerVal endW : Word) (s7 s11 : Word) : Assertion :=
  (.x2 ↦ᵣ spC) **
    (.x1 ↦ᵣ LinkWalkNext5) **
    (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
    (.x18 ↦ᵣ balPtr) ** (.x19 ↦ᵣ balLenW) ** (.x20 ↦ᵣ chainIdW) **
    (.x21 ↦ᵣ loadPtr + innerVal) ** (.x22 ↦ᵣ lenW - innerVal) **
    (.x23 ↦ᵣ s7) **
    (.x11 ↦ᵣ (0 : Word)) **
    (.x25 ↦ᵣ endW) **
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
    teerScratchWithoutRecipientOwn

private theorem pcFree_teerRecipientAmbient
    (spVal spC loadPtr lenW balPtr balLenW chainIdW : Word)
    (s : TeerSaved) (regionBase : Word) (bs balBytes : List (BitVec 8))
    (innerVal endW : Word) (s7 s11 : Word) :
    (teerRecipientAmbient spVal spC loadPtr lenW balPtr balLenW chainIdW
      s regionBase bs balBytes innerVal endW s7 s11).pcFree := by
  unfold teerRecipientAmbient; pcf

def teerRecipientBodyPost (next len5 : Word) : Assertion :=
  (.x10 ↦ᵣ next) ** (.x12 ↦ᵣ len5) **
    (.x30 ↦ᵣ (next - len5)) ** (.x5 ↦ᵣ RecipientLenAddr) **
    (.x24 ↦ᵣ next) **
    memOwn RecipientPtrAddr ** memOwn RecipientLenAddr

def teerRecipientFocus (next len5 v24 : Word) : Assertion :=
  (.x10 ↦ᵣ next) ** (.x12 ↦ᵣ len5) **
    (.x24 ↦ᵣ v24) **
    memOwn RecipientPtrAddr ** memOwn RecipientLenAddr **
    regOwn .x30 ** regOwn .x5

/-- wn5 flat body (no pure) for reshape. -/
def teerWalkNext5FlatRest
    (spVal spC loadPtr lenW balPtr balLenW chainIdW : Word)
    (s : TeerSaved) (regionBase : Word) (bs balBytes : List (BitVec 8))
    (innerVal endW : Word) (s7 s11 next len5 srcOff5 : Word) : Assertion :=
  (.x2 ↦ᵣ spC) **
    (.x1 ↦ᵣ LinkWalkNext5) **
    (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
    (.x18 ↦ᵣ balPtr) ** (.x19 ↦ᵣ balLenW) ** (.x20 ↦ᵣ chainIdW) **
    (.x21 ↦ᵣ loadPtr + innerVal) ** (.x22 ↦ᵣ lenW - innerVal) **
    (.x23 ↦ᵣ s7) **
    (.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len5) **
    (.x24 ↦ᵣ srcOff5) ** (.x25 ↦ᵣ endW) **
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

theorem teerWalkNext5FlatRest_to_recipientPre
    (spVal spC loadPtr lenW balPtr balLenW chainIdW : Word)
    (s : TeerSaved) (regionBase : Word) (bs balBytes : List (BitVec 8))
    (innerVal endW : Word) (s7 s11 next len5 cursor : Word) :
    ∀ h,
      (teerWalkNext5FlatRest spVal spC loadPtr lenW balPtr balLenW chainIdW
          s regionBase bs balBytes innerVal endW s7 s11 next len5 cursor) h →
      (teerRecipientFocus next len5 cursor **
        teerRecipientAmbient spVal spC loadPtr lenW balPtr balLenW chainIdW
          s regionBase bs balBytes innerVal endW s7 s11) h := by
  intro h hp
  unfold teerWalkNext5FlatRest teerRecipientFocus teerRecipientAmbient
    teerScratchWithoutTypeOwn teerScratchWithoutRecipientOwn
    RecipientPtrAddr RecipientLenAddr at *
  xperm_hyp hp

def teerRecipientPostNested
    (spVal spC loadPtr lenW balPtr balLenW chainIdW : Word)
    (s : TeerSaved) (regionBase : Word) (bs balBytes : List (BitVec 8))
    (innerVal endW : Word) (s7 s11 : Word) (srcOff5 : Nat) : Assertion :=
  fun h => ∃ next len5 : Word,
    (teerRecipientBodyPost next len5 **
      teerRecipientAmbient spVal spC loadPtr lenW balPtr balLenW chainIdW
        s regionBase bs balBytes innerVal endW s7 s11 **
      ⌜rlpItemDecode bs srcOff5 (regionBase + BitVec.ofNat 64 srcOff5)
        endW next len5⌝) h


set_option maxRecDepth 8000 in
theorem teerRecipient_applied
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
      next4 = regionBase + BitVec.ofNat 64 srcOff5) :
    let s : TeerSaved :=
      { ra := ret, s0 := s0, s1 := s1, s2 := s2, s3 := s3, s4 := s4
        s5 := s5, s6 := s6, s7 := s7, s8 := s8, s9 := s9
        s10 := s10, s11 := s11, a5 := baiW }
    let innerVal := (teerTxTypeDispatch (txSlice bs off len)).2.2
    let endW := (regionBase + BitVec.ofNat 64 listOff) + (lenW - innerVal)
    cpsTripleWithin nFrontToRecipientSave
      E AfterRecipientSave teerLinkedEarly
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
      (fun h => ∃ next len5 : Word,
        (((.x2 ↦ᵣ spC) **
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
          teerScratchWithoutRecipientOwn) **
          ⌜rlpItemDecode bs srcOff5 (regionBase + BitVec.ofNat 64 srcOff5)
            endW next len5⌝) h) := by
  intro s innerVal endW
  have hwn5 := teerWalkNext5_applied ret spVal spC loadPtr lenW
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
    teerWalkNext5FlatRest spVal spC loadPtr lenW balPtr balLenW chainIdW
      s regionBase bs balBytes innerVal endW s7 s11 p.1 p.2
      (regionBase + BitVec.ofNat 64 srcOff5) **
    ⌜rlpItemDecode bs srcOff5 (regionBase + BitVec.ofNat 64 srcOff5)
      endW p.1 p.2⌝
  have hwn5E :
      cpsTripleWithin nFrontToWalkNext5Bne E AfterWalkNext5Bne teerLinkedEarly
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
    refine cpsTripleWithin_weaken (fun _ hp => hp) (fun h hq => ?_) hwn5
    obtain ⟨next, len5, hq'⟩ := hq
    refine ⟨(next, len5), ?_⟩
    dsimp only [Flat, teerWalkNext5FlatRest]
    xperm_hyp hq'
  let RecPost : Assertion := fun h =>
    ∃ next len5 : Word,
      ((teerRecipientBodyPost next len5 **
        teerRecipientAmbient spVal spC loadPtr lenW balPtr balLenW chainIdW
          s regionBase bs balBytes innerVal endW s7 s11) **
        ⌜rlpItemDecode bs srcOff5 (regionBase + BitVec.ofNat 64 srcOff5)
          endW next len5⌝) h
  have hstep (p : Word × Word) :
      cpsTripleWithin 8 AfterWalkNext5Bne AfterRecipientSave teerLinkedEarly
        (Flat p) RecPost := by
    dsimp only [Flat]
    have hswap :
        cpsTripleWithin 8 AfterWalkNext5Bne AfterRecipientSave teerLinkedEarly
          (⌜rlpItemDecode bs srcOff5 (regionBase + BitVec.ofNat 64 srcOff5)
              endW p.1 p.2⌝ **
            teerWalkNext5FlatRest spVal spC loadPtr lenW balPtr balLenW chainIdW
              s regionBase bs balBytes innerVal endW s7 s11 p.1 p.2
              (regionBase + BitVec.ofNat 64 srcOff5))
          RecPost := by
      refine cpsTripleWithin_pure_pre (fun hpure => ?_)
      have hstore := teerRecipientStore_ownTemps p.1 p.2
        (regionBase + BitVec.ofNat 64 srcOff5)
      have hstoreF := cpsTripleWithin_frameR
        (teerRecipientAmbient spVal spC loadPtr lenW balPtr balLenW chainIdW
          s regionBase bs balBytes innerVal endW s7 s11)
        (pcFree_teerRecipientAmbient spVal spC loadPtr lenW balPtr balLenW
          chainIdW s regionBase bs balBytes innerVal endW s7 s11) hstore
      have hstoreW :
          cpsTripleWithin 8 AfterWalkNext5Bne AfterRecipientSave teerLinkedEarly
            (teerWalkNext5FlatRest spVal spC loadPtr lenW balPtr balLenW chainIdW
              s regionBase bs balBytes innerVal endW s7 s11 p.1 p.2
              (regionBase + BitVec.ofNat 64 srcOff5))
            (teerRecipientBodyPost p.1 p.2 **
              teerRecipientAmbient spVal spC loadPtr lenW balPtr balLenW chainIdW
                s regionBase bs balBytes innerVal endW s7 s11) := by
        refine cpsTripleWithin_weaken
          (teerWalkNext5FlatRest_to_recipientPre
            spVal spC loadPtr lenW balPtr balLenW chainIdW s regionBase bs balBytes
            innerVal endW s7 s11 p.1 p.2
            (regionBase + BitVec.ofNat 64 srcOff5))
          (fun _ hq => by
            change (teerRecipientBodyPost p.1 p.2 **
              teerRecipientAmbient spVal spC loadPtr lenW balPtr balLenW chainIdW
                s regionBase bs balBytes innerVal endW s7 s11) _
            unfold teerRecipientBodyPost
            xperm_hyp hq) hstoreF
      exact cpsTripleWithin_weaken (fun _ hp => hp)
        (fun _ hq => by
          refine ⟨p.1, p.2, ?_⟩
          exact (sepConj_pure_right _).2 ⟨hq, hpure⟩) hstoreW
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => hq) hswap
  have hseq := cpsTripleWithin_seq_exists_same_cr hwn5E hstep
  have hmono := cpsTripleWithin_mono_nSteps
    (by decide : nFrontToWalkNext5Bne + 8 ≤ nFrontToRecipientSave) hseq
  refine cpsTripleWithin_weaken (fun _ hp => hp) (fun h hq => ?_) hmono
  -- RecPost = ∃ next len5, (Body ** Amb) ** pure
  obtain ⟨next, len5, hq'⟩ := hq
  refine ⟨next, len5, ?_⟩
  have hq2 := (sepConj_pure_right _).1 hq'
  obtain ⟨hqBodyAmb, hpure⟩ := hq2
  unfold teerRecipientBodyPost teerRecipientAmbient at hqBodyAmb
  have hqflat :
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
        (.x30 ↦ᵣ (next - len5)) ** (.x5 ↦ᵣ RecipientLenAddr) **
        regOwn .x6 ** regOwn .x7 **
        regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x31 **
        stackFree spVal 6 **
        bytesRegion regionBase bs ** bytesRegion balPtr balBytes **
        memOwn RecipientPtrAddr ** memOwn RecipientLenAddr **
        teerScratchWithoutRecipientOwn) h := by
    xperm_hyp hqBodyAmb
  exact (sepConj_pure_right _).2 ⟨hqflat, hpure⟩

#print axioms teerRecipientStore_ownTemps
#print axioms teerScratchWithoutType_to_recipient_rest
#print axioms teerRecipient_applied

end EvmAsm.Codegen.TxEip7702TeerSpec
