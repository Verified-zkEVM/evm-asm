/-
  AuthLoop empty post → ExitPre packaging.

  After list_count count=0 + AuthLoopStart:
  * x1 = LinkWalkInitAuth (epi restores ra from frame)
  * x21/x22 = walk cursors (s5/s6 overwritten)
  * x23 = 0, x24 = 0, x26 = 0
  * nested stackFree spC 6 below frame (outside TeerAssumed 20)

  ExitRet needs regsAt teerEpiFrame liveCur with s7=s8=s10=0.
  Live cur uses walk cursors for s5/s6 and LinkWalkInitAuth as ra.

  Nested free preserved as third conjunct of ExitPack.
  Residual reshape: TeerAuthLoopEmptyToExitAssumed.
-/

import EvmAsm.Codegen.Programs.TxEip7702TeerFrontListCount
import EvmAsm.Codegen.Programs.TxEip7702TeerFrontListCountCompose
import EvmAsm.Codegen.Programs.TxEip7702TeerAssumed
import EvmAsm.Codegen.Programs.TxEip7702TeerDischarge
import EvmAsm.Codegen.Programs.TxEip7702TeerAuthLoopStart
import EvmAsm.Codegen.Programs.TxEip7702TeerAuthLoopField0
import EvmAsm.Codegen.Programs.TxEip7702TeerScratchZero
import EvmAsm.Codegen.Programs.TxEip7702TeerWouldbe
import EvmAsm.Codegen.Programs.TxEip7702TeerExitRet
import EvmAsm.Codegen.Programs.TxEip7702TeerEpilogue
import EvmAsm.Codegen.Programs.RlpListCountItemsSAsmBase
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.SAsm.AbiFrame
import EvmAsm.Rv64.SAsm.StmtSoundCall
import EvmAsm.Rv64.SAsm.RwSubwindow

namespace EvmAsm.Codegen.TxEip7702TeerSpec

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Rv64.SAsm (cpsTripleWithin_exists_pre_gen)
open EvmAsm.Codegen
open EvmAsm.Codegen.BlockVerdictTxStateGasArraySpec (teerScratchOwn nTeerStackDwords nTeerSteps)
open EvmAsm.Codegen.RlpListCountItemsSAsm

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
    | exact pcFree_stackFree _ _
    | exact bytesRegion_pcFree _ _)

/-- ((ExitPre ** ExitFrame) ** nested free) — left-nested for double frameR.
    ExitPre/liveCur live in Assumed (shared with FrontToAuthLoopAssumed). -/
def teerAuthLoopEmptyExitPack
    (spVal spC : Word) (s : TeerSaved)
    (walkCur walkEnd refund a0Old a1Old t0Old t1Old baiW : Word)
    (regionBase : Word) (bs balBytes : List (BitVec 8)) (balPtr : Word) :
    Assertion :=
  ((teerAuthLoopEmptyExitPre spC s walkCur walkEnd refund a0Old a1Old t0Old t1Old **
      teerEmptyAuthExitFrame baiW spVal spC regionBase bs balBytes balPtr) **
    stackFree spC 6)

/-- Empty-auth exit → ret under AuthLoop live cur (s10=0, s7=s8=0). -/
theorem teerAuthLoopEmpty_exitToRet_rolled0
    (sp0 spC : Word) (s : TeerSaved)
    (walkCur walkEnd a0Old a1Old t0Old t1Old refund : Word)
    (hspC : spC = sp0 + signExtend12 (-160 : BitVec 12))
    (hret : s.ra &&& ~~~(1 : Word) = s.ra) :
    cpsTripleWithin 30 AfterAuthLoopLi s.ra teerLinkedField0
      (teerAuthLoopEmptyExitPre spC s walkCur walkEnd refund
        a0Old a1Old t0Old t1Old)
      ((.x10 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ s.ra) ** (.x2 ↦ᵣ sp0) **
        (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
        (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) **
        (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) **
        (.x23 ↦ᵣ s.s7) ** (.x24 ↦ᵣ s.s8) ** (.x25 ↦ᵣ s.s9) **
        (.x26 ↦ᵣ s.s10) ** (.x27 ↦ᵣ s.s11) **
        frameSlotsSaved teerEpiFrame spC (teerSavedVals s) **
        (.x11 ↦ᵣ refund) ** (.x5 ↦ᵣ RolledBackAddr) **
        (.x6 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        (RegularRefundAddr ↦ₘ refund) **
        memOwn WouldbeStateAddr ** memOwn WouldbeRegularAddr **
        (RolledBackAddr ↦ₘ (0 : Word))) := by
  have h0 := teerEmptyAuthToRet_rolled0 sp0 spC s
    (teerAuthLoopEmptyLiveCur s walkCur walkEnd) (0 : Word)
    a0Old a1Old t0Old t1Old refund hspC hret
    (teerAuthLoopEmptyLiveCur_s10 s walkCur walkEnd)
    (teerAuthLoopEmptyLiveCur_s78 s walkCur walkEnd)
  -- prest of h0 is expanded ExitPre body
  dsimp only [teerAuthLoopEmptyExitPre]
  exact h0

private theorem pcFree_teerEmptyAuthExitFrame
    (baiW spVal spC regionBase : Word)
    (bs balBytes : List (BitVec 8)) (balPtr : Word) :
    (teerEmptyAuthExitFrame baiW spVal spC regionBase bs balBytes balPtr).pcFree := by
  unfold teerEmptyAuthExitFrame
  pcf

/-- ExitPack → ret framed under ExitFrame + nested free.
    Post is right-assoc `((core) ** Frame) ** nested` matching frameR. -/
theorem teerAuthLoopEmptyExitPack_toRet
    (sp0 spC : Word) (s : TeerSaved)
    (walkCur walkEnd a0Old a1Old t0Old t1Old refund baiW : Word)
    (regionBase : Word) (bs balBytes : List (BitVec 8)) (balPtr : Word)
    (hspC : spC = sp0 + signExtend12 (-160 : BitVec 12))
    (hret : s.ra &&& ~~~(1 : Word) = s.ra) :
    cpsTripleWithin 30 AfterAuthLoopLi s.ra teerLinkedField0
      (teerAuthLoopEmptyExitPack sp0 spC s walkCur walkEnd refund
        a0Old a1Old t0Old t1Old baiW regionBase bs balBytes balPtr)
      ((((.x10 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ s.ra) ** (.x2 ↦ᵣ sp0) **
          (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
          (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) **
          (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) **
          (.x23 ↦ᵣ s.s7) ** (.x24 ↦ᵣ s.s8) ** (.x25 ↦ᵣ s.s9) **
          (.x26 ↦ᵣ s.s10) ** (.x27 ↦ᵣ s.s11) **
          frameSlotsSaved teerEpiFrame spC (teerSavedVals s) **
          (.x11 ↦ᵣ refund) ** (.x5 ↦ᵣ RolledBackAddr) **
          (.x6 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
          (RegularRefundAddr ↦ₘ refund) **
          memOwn WouldbeStateAddr ** memOwn WouldbeRegularAddr **
          (RolledBackAddr ↦ₘ (0 : Word))) **
          teerEmptyAuthExitFrame baiW sp0 spC regionBase bs balBytes balPtr) **
        stackFree spC 6) := by
  have hcore := teerAuthLoopEmpty_exitToRet_rolled0 sp0 spC s walkCur walkEnd
    a0Old a1Old t0Old t1Old refund hspC hret
  have hF1 :=
    cpsTripleWithin_frameR
      (teerEmptyAuthExitFrame baiW sp0 spC regionBase bs balBytes balPtr)
      (pcFree_teerEmptyAuthExitFrame baiW sp0 spC regionBase bs balBytes balPtr)
      hcore
  have hF2 :=
    cpsTripleWithin_frameR (stackFree spC 6) (pcFree_stackFree spC 6) hF1
  -- ExitPack defeq hF2 prest
  simpa [teerAuthLoopEmptyExitPack] using hF2

/-- AuthLoop empty post**ambient (refund/rolled value-carrying; listOff=0).
    Matches `teerListCountAuthLoop_framed_empty` post with memIs refund/rolled. -/
def teerAuthLoopEmptySource
    (spVal spC listBase listLenW s0 s1 s2 s3 : Word)
    (bytes : List (BitVec 8))
    (balPtr chainIdW : Word)
    (s : TeerSaved) (balBytes : List (BitVec 8))
    (innerVal endW s11 refund : Word) : Assertion :=
  (teerListCountAuthLoopPost spC listBase AuthCountAddr s0 s1 s2 s3
      (0 : Word) bytes 0 listLenW) **
    ((.x20 ↦ᵣ chainIdW) ** (.x25 ↦ᵣ endW) **
      (.x26 ↦ᵣ (0 : Word)) ** (.x27 ↦ᵣ s11) **
      regOwn .x15 **
      frameSlotsSaved teerFrame spC (teerSavedVals s) **
      (BitVec.ofNat 64 GuestAddrs.teer_type ↦ₘ (4 : Word)) **
      (BitVec.ofNat 64 GuestAddrs.teer_inner_off ↦ₘ innerVal) **
      regOwn .x13 ** regOwn .x14 ** regOwn .x16 **
      stackFree spVal 6 **
      bytesRegion balPtr balBytes **
      memOwn (BitVec.ofNat 64 GuestAddrs.teer_recipient_ptr) **
      memOwn (BitVec.ofNat 64 GuestAddrs.teer_recipient_len) **
      memOwn (BitVec.ofNat 64 GuestAddrs.teer_value_nonzero) **
      memOwn (BitVec.ofNat 64 GuestAddrs.teer_authority) **
      memOwn (BitVec.ofNat 64 GuestAddrs.teer_acct_ptr) **
      memOwn (BitVec.ofNat 64 GuestAddrs.teer_acct_len) **
      memOwn (BitVec.ofNat 64 GuestAddrs.teer_acct_absent) **
      (RolledBackAddr ↦ₘ (0 : Word)) **
      memOwn (BitVec.ofNat 64 GuestAddrs.teer_prior_count) **
      memOwn (BitVec.ofNat 64 GuestAddrs.teer_pre_acct) **
      memOwn (BitVec.ofNat 64 GuestAddrs.teer_success_count) **
      (RegularRefundAddr ↦ₘ refund) **
      memOwn (BitVec.ofNat 64 GuestAddrs.teer_prior_set_flag) **
      memOwn (BitVec.ofNat 64 GuestAddrs.teer_finals) **
      memOwn (BitVec.ofNat 64 GuestAddrs.teer_success_table) **
      memOwn (BitVec.ofNat 64 GuestAddrs.teer_predelegated_count) **
      memOwn WouldbeStateAddr **
      memOwn WouldbeRegularAddr **
      memOwn (BitVec.ofNat 64 GuestAddrs.teer_recover_scratch) **
      memOwn (BitVec.ofNat 64 GuestAddrs.teer_records_ptr))

/-- Reshape AuthLoop empty source → ExitPack.
    Peels regOwn x5/x6/x15 (temps not value-preserved through list_count).
    Identity blob: listBase = regionBase, bytes = bs. -/
private theorem listBase_add_ofNat_zero (listBase : Word) :
    listBase + BitVec.ofNat 64 0 = listBase :=
  BitVec.add_zero listBase

/-- Flattened AuthLoop-empty source (listOff=0, identity blob, s-regs wired). -/
def teerAuthLoopEmptySourceFlat
    (spVal spC listLenW : Word)
    (s : TeerSaved) (balBytes : List (BitVec 8))
    (innerVal refund balPtr regionBase : Word) (bs : List (BitVec 8)) :
    Assertion :=
  let walkCur := regionBase + signExtend12 (1 : BitVec 12)
  let walkEnd := regionBase + listLenW
  regOwn .x5 ** regOwn .x6 ** regOwn .x15 **
    (.x1 ↦ᵣ LinkWalkInitAuth) **
    (.x10 ↦ᵣ walkCur) ** (.x11 ↦ᵣ walkEnd) **
    (.x12 ↦ᵣ (0 : Word)) **
    (.x21 ↦ᵣ walkCur) ** (.x22 ↦ᵣ walkEnd) **
    (.x24 ↦ᵣ (0 : Word)) **
    regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
    (.x0 ↦ᵣ (0 : Word)) ** bytesRegion regionBase bs **
    (.x2 ↦ᵣ spC) **
    (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) ** (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) **
    stackFree spC 6 **
    (.x23 ↦ᵣ (0 : Word)) **
    (BitVec.ofNat 64 GuestAddrs.teer_auth_count ↦ₘ (0 : Word)) **
    (.x20 ↦ᵣ s.s4) ** (.x25 ↦ᵣ s.s9) **
    (.x26 ↦ᵣ (0 : Word)) ** (.x27 ↦ᵣ s.s11) **
    frameSlotsSaved teerFrame spC (teerSavedVals s) **
    (BitVec.ofNat 64 GuestAddrs.teer_type ↦ₘ (4 : Word)) **
    (BitVec.ofNat 64 GuestAddrs.teer_inner_off ↦ₘ innerVal) **
    regOwn .x13 ** regOwn .x14 ** regOwn .x16 **
    stackFree spVal 6 **
    bytesRegion balPtr balBytes **
    memOwn (BitVec.ofNat 64 GuestAddrs.teer_recipient_ptr) **
    memOwn (BitVec.ofNat 64 GuestAddrs.teer_recipient_len) **
    memOwn (BitVec.ofNat 64 GuestAddrs.teer_value_nonzero) **
    memOwn (BitVec.ofNat 64 GuestAddrs.teer_authority) **
    memOwn (BitVec.ofNat 64 GuestAddrs.teer_acct_ptr) **
    memOwn (BitVec.ofNat 64 GuestAddrs.teer_acct_len) **
    memOwn (BitVec.ofNat 64 GuestAddrs.teer_acct_absent) **
    (RolledBackAddr ↦ₘ (0 : Word)) **
    memOwn (BitVec.ofNat 64 GuestAddrs.teer_prior_count) **
    memOwn (BitVec.ofNat 64 GuestAddrs.teer_pre_acct) **
    memOwn (BitVec.ofNat 64 GuestAddrs.teer_success_count) **
    (RegularRefundAddr ↦ₘ refund) **
    memOwn (BitVec.ofNat 64 GuestAddrs.teer_prior_set_flag) **
    memOwn (BitVec.ofNat 64 GuestAddrs.teer_finals) **
    memOwn (BitVec.ofNat 64 GuestAddrs.teer_success_table) **
    memOwn (BitVec.ofNat 64 GuestAddrs.teer_predelegated_count) **
    memOwn WouldbeStateAddr **
    memOwn WouldbeRegularAddr **
    memOwn (BitVec.ofNat 64 GuestAddrs.teer_recover_scratch) **
    memOwn (BitVec.ofNat 64 GuestAddrs.teer_records_ptr)

theorem teerAuthLoopEmptySource_to_flat
    (spVal spC listBase listLenW s0 s1 s2 s3 : Word)
    (bytes : List (BitVec 8))
    (balPtr chainIdW : Word)
    (s : TeerSaved) (balBytes : List (BitVec 8))
    (innerVal endW s11 refund : Word)
    (regionBase : Word) (bs : List (BitVec 8))
    (hbase : listBase = regionBase)
    (hbytes : bytes = bs)
    (hs0 : s0 = s.s0) (hs1 : s1 = s.s1) (hs2 : s2 = s.s2) (hs3 : s3 = s.s3)
    (hs4 : chainIdW = s.s4)
    (hs9 : endW = s.s9) (hs11 : s11 = s.s11) :
    ∀ h,
      teerAuthLoopEmptySource spVal spC listBase listLenW s0 s1 s2 s3 bytes
        balPtr chainIdW s balBytes innerVal endW s11 refund h →
      teerAuthLoopEmptySourceFlat spVal spC listLenW s balBytes innerVal refund
        balPtr regionBase bs h := by
  intro h hp
  dsimp only [teerAuthLoopEmptySource, teerListCountAuthLoopPost,
    teerAuthLoopStartBodyPost, teerAuthLoopEmptySourceFlat, AuthCountAddr] at hp ⊢
  simp only [hs0, hs1, hs2, hs3, hs4, hs9, hs11, hbytes, hbase,
    listBase_add_ofNat_zero] at hp ⊢
  xperm_hyp hp

theorem teerAuthLoopEmpty_to_exitPack
    (spVal spC listBase listLenW s0 s1 s2 s3 : Word)
    (bytes : List (BitVec 8))
    (balPtr chainIdW : Word)
    (s : TeerSaved) (balBytes : List (BitVec 8))
    (innerVal endW s11 refund : Word)
    (regionBase : Word) (bs : List (BitVec 8))
    (hbase : listBase = regionBase)
    (hbytes : bytes = bs)
    (hs0 : s0 = s.s0) (hs1 : s1 = s.s1) (hs2 : s2 = s.s2) (hs3 : s3 = s.s3)
    (hs4 : chainIdW = s.s4)
    (hs9 : endW = s.s9) (hs11 : s11 = s.s11) :
    ∀ h,
      teerAuthLoopEmptySource spVal spC listBase listLenW s0 s1 s2 s3 bytes
        balPtr chainIdW s balBytes innerVal endW s11 refund h →
      ∃ t0Old t1Old baiW,
        teerAuthLoopEmptyExitPack spVal spC s
          (teerAuthLoopEmptyWalkCur listBase)
          (teerAuthLoopEmptyWalkEnd listBase listLenW)
          refund
          (teerAuthLoopEmptyWalkCur listBase)
          (teerAuthLoopEmptyWalkEnd listBase listLenW)
          t0Old t1Old baiW
          regionBase bs balBytes balPtr h := by
  intro h hp
  have hpF0 :=
    teerAuthLoopEmptySource_to_flat spVal spC listBase listLenW s0 s1 s2 s3 bytes
      balPtr chainIdW s balBytes innerVal endW s11 refund regionBase bs
      hbase hbytes hs0 hs1 hs2 hs3 hs4 hs9 hs11 h hp
  dsimp only [teerAuthLoopEmptySourceFlat] at hpF0
  -- Peel x5 (leftmost)
  obtain ⟨t0Old, hpF0⟩ := sepConj_choose_regOwn (r := .x5) hpF0
  -- Reorder so regOwn x6 is leftmost, peel
  have hpF1 :
      (regOwn .x6 **
        ((.x5 ↦ᵣ t0Old) ** regOwn .x15 **
          (.x1 ↦ᵣ LinkWalkInitAuth) **
          (.x10 ↦ᵣ regionBase + signExtend12 (1 : BitVec 12)) **
          (.x11 ↦ᵣ regionBase + listLenW) **
          (.x12 ↦ᵣ (0 : Word)) **
          (.x21 ↦ᵣ regionBase + signExtend12 (1 : BitVec 12)) **
          (.x22 ↦ᵣ regionBase + listLenW) **
          (.x24 ↦ᵣ (0 : Word)) **
          regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          (.x0 ↦ᵣ (0 : Word)) ** bytesRegion regionBase bs **
          (.x2 ↦ᵣ spC) **
          (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) ** (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) **
          stackFree spC 6 **
          (.x23 ↦ᵣ (0 : Word)) **
          (BitVec.ofNat 64 GuestAddrs.teer_auth_count ↦ₘ (0 : Word)) **
          (.x20 ↦ᵣ s.s4) ** (.x25 ↦ᵣ s.s9) **
          (.x26 ↦ᵣ (0 : Word)) ** (.x27 ↦ᵣ s.s11) **
          frameSlotsSaved teerFrame spC (teerSavedVals s) **
          (BitVec.ofNat 64 GuestAddrs.teer_type ↦ₘ (4 : Word)) **
          (BitVec.ofNat 64 GuestAddrs.teer_inner_off ↦ₘ innerVal) **
          regOwn .x13 ** regOwn .x14 ** regOwn .x16 **
          stackFree spVal 6 **
          bytesRegion balPtr balBytes **
          memOwn (BitVec.ofNat 64 GuestAddrs.teer_recipient_ptr) **
          memOwn (BitVec.ofNat 64 GuestAddrs.teer_recipient_len) **
          memOwn (BitVec.ofNat 64 GuestAddrs.teer_value_nonzero) **
          memOwn (BitVec.ofNat 64 GuestAddrs.teer_authority) **
          memOwn (BitVec.ofNat 64 GuestAddrs.teer_acct_ptr) **
          memOwn (BitVec.ofNat 64 GuestAddrs.teer_acct_len) **
          memOwn (BitVec.ofNat 64 GuestAddrs.teer_acct_absent) **
          (RolledBackAddr ↦ₘ (0 : Word)) **
          memOwn (BitVec.ofNat 64 GuestAddrs.teer_prior_count) **
          memOwn (BitVec.ofNat 64 GuestAddrs.teer_pre_acct) **
          memOwn (BitVec.ofNat 64 GuestAddrs.teer_success_count) **
          (RegularRefundAddr ↦ₘ refund) **
          memOwn (BitVec.ofNat 64 GuestAddrs.teer_prior_set_flag) **
          memOwn (BitVec.ofNat 64 GuestAddrs.teer_finals) **
          memOwn (BitVec.ofNat 64 GuestAddrs.teer_success_table) **
          memOwn (BitVec.ofNat 64 GuestAddrs.teer_predelegated_count) **
          memOwn WouldbeStateAddr **
          memOwn WouldbeRegularAddr **
          memOwn (BitVec.ofNat 64 GuestAddrs.teer_recover_scratch) **
          memOwn (BitVec.ofNat 64 GuestAddrs.teer_records_ptr))) h := by
    xperm_hyp hpF0
  obtain ⟨t1Old, hpF1⟩ := sepConj_choose_regOwn (r := .x6) hpF1
  have hpF2 :
      (regOwn .x15 **
        ((.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) **
          (.x1 ↦ᵣ LinkWalkInitAuth) **
          (.x10 ↦ᵣ regionBase + signExtend12 (1 : BitVec 12)) **
          (.x11 ↦ᵣ regionBase + listLenW) **
          (.x12 ↦ᵣ (0 : Word)) **
          (.x21 ↦ᵣ regionBase + signExtend12 (1 : BitVec 12)) **
          (.x22 ↦ᵣ regionBase + listLenW) **
          (.x24 ↦ᵣ (0 : Word)) **
          regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          (.x0 ↦ᵣ (0 : Word)) ** bytesRegion regionBase bs **
          (.x2 ↦ᵣ spC) **
          (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) ** (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) **
          stackFree spC 6 **
          (.x23 ↦ᵣ (0 : Word)) **
          (BitVec.ofNat 64 GuestAddrs.teer_auth_count ↦ₘ (0 : Word)) **
          (.x20 ↦ᵣ s.s4) ** (.x25 ↦ᵣ s.s9) **
          (.x26 ↦ᵣ (0 : Word)) ** (.x27 ↦ᵣ s.s11) **
          frameSlotsSaved teerFrame spC (teerSavedVals s) **
          (BitVec.ofNat 64 GuestAddrs.teer_type ↦ₘ (4 : Word)) **
          (BitVec.ofNat 64 GuestAddrs.teer_inner_off ↦ₘ innerVal) **
          regOwn .x13 ** regOwn .x14 ** regOwn .x16 **
          stackFree spVal 6 **
          bytesRegion balPtr balBytes **
          memOwn (BitVec.ofNat 64 GuestAddrs.teer_recipient_ptr) **
          memOwn (BitVec.ofNat 64 GuestAddrs.teer_recipient_len) **
          memOwn (BitVec.ofNat 64 GuestAddrs.teer_value_nonzero) **
          memOwn (BitVec.ofNat 64 GuestAddrs.teer_authority) **
          memOwn (BitVec.ofNat 64 GuestAddrs.teer_acct_ptr) **
          memOwn (BitVec.ofNat 64 GuestAddrs.teer_acct_len) **
          memOwn (BitVec.ofNat 64 GuestAddrs.teer_acct_absent) **
          (RolledBackAddr ↦ₘ (0 : Word)) **
          memOwn (BitVec.ofNat 64 GuestAddrs.teer_prior_count) **
          memOwn (BitVec.ofNat 64 GuestAddrs.teer_pre_acct) **
          memOwn (BitVec.ofNat 64 GuestAddrs.teer_success_count) **
          (RegularRefundAddr ↦ₘ refund) **
          memOwn (BitVec.ofNat 64 GuestAddrs.teer_prior_set_flag) **
          memOwn (BitVec.ofNat 64 GuestAddrs.teer_finals) **
          memOwn (BitVec.ofNat 64 GuestAddrs.teer_success_table) **
          memOwn (BitVec.ofNat 64 GuestAddrs.teer_predelegated_count) **
          memOwn WouldbeStateAddr **
          memOwn WouldbeRegularAddr **
          memOwn (BitVec.ofNat 64 GuestAddrs.teer_recover_scratch) **
          memOwn (BitVec.ofNat 64 GuestAddrs.teer_records_ptr))) h := by
    xperm_hyp hpF1
  obtain ⟨baiW, hpF2⟩ := sepConj_choose_regOwn (r := .x15) hpF2
  refine ⟨t0Old, t1Old, baiW, ?_⟩
  -- Pull frame left, split teerFrame → epi ** a5@104
  have hp1 :
      (frameSlotsSaved teerFrame spC (teerSavedVals s) **
        ((.x1 ↦ᵣ LinkWalkInitAuth) **
          (.x10 ↦ᵣ regionBase + signExtend12 (1 : BitVec 12)) **
          (.x11 ↦ᵣ regionBase + listLenW) **
          (.x12 ↦ᵣ (0 : Word)) **
          (.x21 ↦ᵣ regionBase + signExtend12 (1 : BitVec 12)) **
          (.x22 ↦ᵣ regionBase + listLenW) **
          (.x24 ↦ᵣ (0 : Word)) **
          (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x15 ↦ᵣ baiW) **
          regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          (.x0 ↦ᵣ (0 : Word)) ** bytesRegion regionBase bs **
          (.x2 ↦ᵣ spC) **
          (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) ** (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) **
          stackFree spC 6 **
          (.x23 ↦ᵣ (0 : Word)) **
          (BitVec.ofNat 64 GuestAddrs.teer_auth_count ↦ₘ (0 : Word)) **
          (.x20 ↦ᵣ s.s4) ** (.x25 ↦ᵣ s.s9) **
          (.x26 ↦ᵣ (0 : Word)) ** (.x27 ↦ᵣ s.s11) **
          (BitVec.ofNat 64 GuestAddrs.teer_type ↦ₘ (4 : Word)) **
          (BitVec.ofNat 64 GuestAddrs.teer_inner_off ↦ₘ innerVal) **
          regOwn .x13 ** regOwn .x14 ** regOwn .x16 **
          stackFree spVal 6 **
          bytesRegion balPtr balBytes **
          memOwn (BitVec.ofNat 64 GuestAddrs.teer_recipient_ptr) **
          memOwn (BitVec.ofNat 64 GuestAddrs.teer_recipient_len) **
          memOwn (BitVec.ofNat 64 GuestAddrs.teer_value_nonzero) **
          memOwn (BitVec.ofNat 64 GuestAddrs.teer_authority) **
          memOwn (BitVec.ofNat 64 GuestAddrs.teer_acct_ptr) **
          memOwn (BitVec.ofNat 64 GuestAddrs.teer_acct_len) **
          memOwn (BitVec.ofNat 64 GuestAddrs.teer_acct_absent) **
          (RolledBackAddr ↦ₘ (0 : Word)) **
          memOwn (BitVec.ofNat 64 GuestAddrs.teer_prior_count) **
          memOwn (BitVec.ofNat 64 GuestAddrs.teer_pre_acct) **
          memOwn (BitVec.ofNat 64 GuestAddrs.teer_success_count) **
          (RegularRefundAddr ↦ₘ refund) **
          memOwn (BitVec.ofNat 64 GuestAddrs.teer_prior_set_flag) **
          memOwn (BitVec.ofNat 64 GuestAddrs.teer_finals) **
          memOwn (BitVec.ofNat 64 GuestAddrs.teer_success_table) **
          memOwn (BitVec.ofNat 64 GuestAddrs.teer_predelegated_count) **
          memOwn WouldbeStateAddr **
          memOwn WouldbeRegularAddr **
          memOwn (BitVec.ofNat 64 GuestAddrs.teer_recover_scratch) **
          memOwn (BitVec.ofNat 64 GuestAddrs.teer_records_ptr))) h := by
    xperm_hyp hpF2
  have hp2 :=
    sepConj_mono (teerAuthLoopFrame_to_exitFrame_own spC s) (fun _ hh => hh) h hp1
  -- Pull memIs triple left, convert to memOwn
  have hp3 :
      ((BitVec.ofNat 64 GuestAddrs.teer_auth_count ↦ₘ (0 : Word)) **
        (BitVec.ofNat 64 GuestAddrs.teer_type ↦ₘ (4 : Word)) **
        (BitVec.ofNat 64 GuestAddrs.teer_inner_off ↦ₘ innerVal) **
        ((frameSlotsSaved teerEpiFrame spC (teerSavedVals s) **
            memOwn (spC + signExtend12 (104 : BitVec 12))) **
          ((.x1 ↦ᵣ LinkWalkInitAuth) **
            (.x10 ↦ᵣ regionBase + signExtend12 (1 : BitVec 12)) **
            (.x11 ↦ᵣ regionBase + listLenW) **
            (.x12 ↦ᵣ (0 : Word)) **
            (.x21 ↦ᵣ regionBase + signExtend12 (1 : BitVec 12)) **
            (.x22 ↦ᵣ regionBase + listLenW) **
            (.x24 ↦ᵣ (0 : Word)) **
            (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x15 ↦ᵣ baiW) **
            regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
            (.x0 ↦ᵣ (0 : Word)) ** bytesRegion regionBase bs **
            (.x2 ↦ᵣ spC) **
            (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) ** (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) **
            stackFree spC 6 **
            (.x23 ↦ᵣ (0 : Word)) **
            (.x20 ↦ᵣ s.s4) ** (.x25 ↦ᵣ s.s9) **
            (.x26 ↦ᵣ (0 : Word)) ** (.x27 ↦ᵣ s.s11) **
            regOwn .x13 ** regOwn .x14 ** regOwn .x16 **
            stackFree spVal 6 **
            bytesRegion balPtr balBytes **
            memOwn (BitVec.ofNat 64 GuestAddrs.teer_recipient_ptr) **
            memOwn (BitVec.ofNat 64 GuestAddrs.teer_recipient_len) **
            memOwn (BitVec.ofNat 64 GuestAddrs.teer_value_nonzero) **
            memOwn (BitVec.ofNat 64 GuestAddrs.teer_authority) **
            memOwn (BitVec.ofNat 64 GuestAddrs.teer_acct_ptr) **
            memOwn (BitVec.ofNat 64 GuestAddrs.teer_acct_len) **
            memOwn (BitVec.ofNat 64 GuestAddrs.teer_acct_absent) **
            (RolledBackAddr ↦ₘ (0 : Word)) **
            memOwn (BitVec.ofNat 64 GuestAddrs.teer_prior_count) **
            memOwn (BitVec.ofNat 64 GuestAddrs.teer_pre_acct) **
            memOwn (BitVec.ofNat 64 GuestAddrs.teer_success_count) **
            (RegularRefundAddr ↦ₘ refund) **
            memOwn (BitVec.ofNat 64 GuestAddrs.teer_prior_set_flag) **
            memOwn (BitVec.ofNat 64 GuestAddrs.teer_finals) **
            memOwn (BitVec.ofNat 64 GuestAddrs.teer_success_table) **
            memOwn (BitVec.ofNat 64 GuestAddrs.teer_predelegated_count) **
            memOwn WouldbeStateAddr **
            memOwn WouldbeRegularAddr **
            memOwn (BitVec.ofNat 64 GuestAddrs.teer_recover_scratch) **
            memOwn (BitVec.ofNat 64 GuestAddrs.teer_records_ptr)))) h := by
    xperm_hyp hp2
  have hp4 :=
    sepConj_mono memIs_implies_memOwn
      (fun h' hh =>
        sepConj_mono memIs_implies_memOwn
          (fun h'' hh =>
            sepConj_mono memIs_implies_memOwn (fun _ hh => hh) h'' hh)
          h' hh)
      h hp3
  -- regIs x12 → regOwn
  have hp5 :
      ((.x12 ↦ᵣ (0 : Word)) **
        (memOwn (BitVec.ofNat 64 GuestAddrs.teer_auth_count) **
          memOwn (BitVec.ofNat 64 GuestAddrs.teer_type) **
          memOwn (BitVec.ofNat 64 GuestAddrs.teer_inner_off) **
          ((frameSlotsSaved teerEpiFrame spC (teerSavedVals s) **
              memOwn (spC + signExtend12 (104 : BitVec 12))) **
            ((.x1 ↦ᵣ LinkWalkInitAuth) **
              (.x10 ↦ᵣ regionBase + signExtend12 (1 : BitVec 12)) **
              (.x11 ↦ᵣ regionBase + listLenW) **
              (.x21 ↦ᵣ regionBase + signExtend12 (1 : BitVec 12)) **
              (.x22 ↦ᵣ regionBase + listLenW) **
              (.x24 ↦ᵣ (0 : Word)) **
              (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x15 ↦ᵣ baiW) **
              regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
              (.x0 ↦ᵣ (0 : Word)) ** bytesRegion regionBase bs **
              (.x2 ↦ᵣ spC) **
              (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) ** (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) **
              stackFree spC 6 **
              (.x23 ↦ᵣ (0 : Word)) **
              (.x20 ↦ᵣ s.s4) ** (.x25 ↦ᵣ s.s9) **
              (.x26 ↦ᵣ (0 : Word)) ** (.x27 ↦ᵣ s.s11) **
              regOwn .x13 ** regOwn .x14 ** regOwn .x16 **
              stackFree spVal 6 **
              bytesRegion balPtr balBytes **
              memOwn (BitVec.ofNat 64 GuestAddrs.teer_recipient_ptr) **
              memOwn (BitVec.ofNat 64 GuestAddrs.teer_recipient_len) **
              memOwn (BitVec.ofNat 64 GuestAddrs.teer_value_nonzero) **
              memOwn (BitVec.ofNat 64 GuestAddrs.teer_authority) **
              memOwn (BitVec.ofNat 64 GuestAddrs.teer_acct_ptr) **
              memOwn (BitVec.ofNat 64 GuestAddrs.teer_acct_len) **
              memOwn (BitVec.ofNat 64 GuestAddrs.teer_acct_absent) **
              (RolledBackAddr ↦ₘ (0 : Word)) **
              memOwn (BitVec.ofNat 64 GuestAddrs.teer_prior_count) **
              memOwn (BitVec.ofNat 64 GuestAddrs.teer_pre_acct) **
              memOwn (BitVec.ofNat 64 GuestAddrs.teer_success_count) **
              (RegularRefundAddr ↦ₘ refund) **
              memOwn (BitVec.ofNat 64 GuestAddrs.teer_prior_set_flag) **
              memOwn (BitVec.ofNat 64 GuestAddrs.teer_finals) **
              memOwn (BitVec.ofNat 64 GuestAddrs.teer_success_table) **
              memOwn (BitVec.ofNat 64 GuestAddrs.teer_predelegated_count) **
              memOwn WouldbeStateAddr **
              memOwn WouldbeRegularAddr **
              memOwn (BitVec.ofNat 64 GuestAddrs.teer_recover_scratch) **
              memOwn (BitVec.ofNat 64 GuestAddrs.teer_records_ptr))))) h := by
    xperm_hyp hp4
  have hp6 :=
    sepConj_mono (regIs_implies_regOwn .x12) (fun _ hh => hh) h hp5
  -- Match ExitPack expanded form
  dsimp only [teerAuthLoopEmptyExitPack, teerAuthLoopEmptyExitPre,
    teerEmptyAuthExitFrame, teerAuthLoopEmptyWalkCur, teerAuthLoopEmptyWalkEnd,
    teerAuthLoopEmptyLiveCur, RegularRefundAddr, RolledBackAddr,
    WouldbeStateAddr, WouldbeRegularAddr] at hp6 ⊢
  simp only [regsAt_teerEpiFrame, hbase] at hp6 ⊢
  xperm_hyp hp6

/-- Named hyp packaging (discharged by `teerAuthLoopEmpty_to_exitPack`). -/
structure TeerAuthLoopEmptyToExitAssumed where
  reshape :
    ∀ (spVal spC listBase listLenW s0 s1 s2 s3 : Word)
      (bytes : List (BitVec 8))
      (balPtr chainIdW : Word)
      (s : TeerSaved) (balBytes : List (BitVec 8))
      (innerVal endW s11 refund : Word)
      (regionBase : Word) (bs : List (BitVec 8)),
      listBase = regionBase →
      bytes = bs →
      s0 = s.s0 → s1 = s.s1 → s2 = s.s2 → s3 = s.s3 →
      chainIdW = s.s4 →
      endW = s.s9 → s11 = s.s11 →
      ∀ h,
        teerAuthLoopEmptySource spVal spC listBase listLenW s0 s1 s2 s3 bytes
          balPtr chainIdW s balBytes innerVal endW s11 refund h →
        ∃ t0Old t1Old baiW,
          teerAuthLoopEmptyExitPack spVal spC s
            (teerAuthLoopEmptyWalkCur listBase)
            (teerAuthLoopEmptyWalkEnd listBase listLenW)
            refund
            (teerAuthLoopEmptyWalkCur listBase)
            (teerAuthLoopEmptyWalkEnd listBase listLenW)
            t0Old t1Old baiW
            regionBase bs balBytes balPtr h

def teerAuthLoopEmptyToExitAssumed : TeerAuthLoopEmptyToExitAssumed where
  reshape := fun spVal spC listBase listLenW s0 s1 s2 s3 bytes balPtr chainIdW
      s balBytes innerVal endW s11 refund regionBase bs
      hbase hbytes hs0 hs1 hs2 hs3 hs4 hs9 hs11 =>
    teerAuthLoopEmpty_to_exitPack spVal spC listBase listLenW s0 s1 s2 s3 bytes
      balPtr chainIdW s balBytes innerVal endW s11 refund regionBase bs
      hbase hbytes hs0 hs1 hs2 hs3 hs4 hs9 hs11


/-- Framed_empty post: AuthLoopPost ** Ambient (memOwn rolled/regular).
    Peel to Source needs memIs refund/rolled + rolled=0 (ScratchZero preserve). -/
def teerAuthLoopEmptyAmbientPost
    (spVal spC listBase listLenW s0 s1 s2 s3 : Word)
    (bytes : List (BitVec 8))
    (balPtr chainIdW baiW : Word)
    (s : TeerSaved) (balBytes : List (BitVec 8))
    (innerVal cursorV endW s11 : Word) : Assertion :=
  (teerListCountAuthLoopPost spC listBase AuthCountAddr s0 s1 s2 s3
      (0 : Word) bytes 0 listLenW) **
    teerListCountAuthLoopAmbient spVal spC balPtr chainIdW
      baiW s balBytes innerVal cursorV endW s11

/-- Source → ret a0=0 (30 steps) under identity wire + hspC/hret.
    Floats ExitPack temps (t0/t1 peeled but not in ret post). -/
theorem teerAuthLoopEmptySource_toRet
    (spVal spC listBase listLenW s0 s1 s2 s3 : Word)
    (bytes : List (BitVec 8))
    (balPtr chainIdW : Word)
    (s : TeerSaved) (balBytes : List (BitVec 8))
    (innerVal endW s11 refund : Word)
    (regionBase : Word) (bs : List (BitVec 8))
    (hbase : listBase = regionBase) (hbytes : bytes = bs)
    (hs0 : s0 = s.s0) (hs1 : s1 = s.s1) (hs2 : s2 = s.s2) (hs3 : s3 = s.s3)
    (hs4 : chainIdW = s.s4) (hs9 : endW = s.s9) (hs11 : s11 = s.s11)
    (hspC : spC = spVal + signExtend12 (-160 : BitVec 12))
    (hret : s.ra &&& ~~~(1 : Word) = s.ra) :
    cpsTripleWithin 30 AfterAuthLoopLi s.ra teerLinkedField0
      (teerAuthLoopEmptySource spVal spC listBase listLenW s0 s1 s2 s3 bytes
        balPtr chainIdW s balBytes innerVal endW s11 refund)
      (fun hp =>
        ∃ (_t0Old _t1Old baiW : Word),
          ((((.x10 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ s.ra) ** (.x2 ↦ᵣ spVal) **
              (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
              (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) **
              (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) **
              (.x23 ↦ᵣ s.s7) ** (.x24 ↦ᵣ s.s8) ** (.x25 ↦ᵣ s.s9) **
              (.x26 ↦ᵣ s.s10) ** (.x27 ↦ᵣ s.s11) **
              frameSlotsSaved teerEpiFrame spC (teerSavedVals s) **
              (.x11 ↦ᵣ refund) ** (.x5 ↦ᵣ RolledBackAddr) **
              (.x6 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
              (RegularRefundAddr ↦ₘ refund) **
              memOwn WouldbeStateAddr ** memOwn WouldbeRegularAddr **
              (RolledBackAddr ↦ₘ (0 : Word))) **
              teerEmptyAuthExitFrame baiW spVal spC regionBase bs balBytes balPtr) **
            stackFree spC 6) hp) := by
  have hpre :
      ∀ h,
        teerAuthLoopEmptySource spVal spC listBase listLenW s0 s1 s2 s3 bytes
          balPtr chainIdW s balBytes innerVal endW s11 refund h →
        ∃ (t0Old t1Old baiW : Word),
          teerAuthLoopEmptyExitPack spVal spC s
            (teerAuthLoopEmptyWalkCur listBase)
            (teerAuthLoopEmptyWalkEnd listBase listLenW)
            refund
            (teerAuthLoopEmptyWalkCur listBase)
            (teerAuthLoopEmptyWalkEnd listBase listLenW)
            t0Old t1Old baiW
            regionBase bs balBytes balPtr h :=
    teerAuthLoopEmpty_to_exitPack spVal spC listBase listLenW s0 s1 s2 s3 bytes
      balPtr chainIdW s balBytes innerVal endW s11 refund regionBase bs
      hbase hbytes hs0 hs1 hs2 hs3 hs4 hs9 hs11
  -- Fixed temps: ExitPack peels produce some t0/t1/bai; post keeps ∃.
  -- Direct: weaken Source→ExitPack then run ExitPack_toRet with witnesses from hpre.
  intro R hR st hcr hPR hpc
  obtain ⟨h0, hcompat, h1, h2, hd, hu, hSrc, hR2⟩ := hPR
  obtain ⟨t0Old, t1Old, baiW, hPack⟩ := hpre h1 hSrc
  have hrun :=
    teerAuthLoopEmptyExitPack_toRet spVal spC s
      (teerAuthLoopEmptyWalkCur listBase)
      (teerAuthLoopEmptyWalkEnd listBase listLenW)
      (teerAuthLoopEmptyWalkCur listBase)
      (teerAuthLoopEmptyWalkEnd listBase listLenW)
      t0Old t1Old refund baiW
      regionBase bs balBytes balPtr hspC hret
  have hPR' :
      (((teerAuthLoopEmptyExitPack spVal spC s
            (teerAuthLoopEmptyWalkCur listBase)
            (teerAuthLoopEmptyWalkEnd listBase listLenW)
            refund
            (teerAuthLoopEmptyWalkCur listBase)
            (teerAuthLoopEmptyWalkEnd listBase listLenW)
            t0Old t1Old baiW
            regionBase bs balBytes balPtr) ** R)).holdsFor st :=
    ⟨h0, hcompat, h1, h2, hd, hu, hPack, hR2⟩
  obtain ⟨k, hk, st', hexec, hpc', hQ⟩ :=
    hrun R hR st hcr hPR' hpc
  refine ⟨k, hk, st', hexec, hpc', ?_⟩
  obtain ⟨h0', hcompat', h1', h2', hd', hu', hRet, hR'⟩ := hQ
  exact ⟨h0', hcompat', h1', h2', hd', hu', ⟨t0Old, t1Old, baiW, hRet⟩, hR'⟩

/-- Ambient half with peeled rolled/regular (rolledVal may be nonzero).
    Uses GuestAddrs for wouldbe cells (Wouldbe*Addr are defs, not abbrevs). -/
def teerAuthLoopEmptyAmbientMemIs
    (spVal spC balPtr chainIdW : Word)
    (s : TeerSaved) (balBytes : List (BitVec 8))
    (innerVal endW s11 refund rolledVal : Word) : Assertion :=
  (.x20 ↦ᵣ chainIdW) ** (.x25 ↦ᵣ endW) **
    (.x26 ↦ᵣ (0 : Word)) ** (.x27 ↦ᵣ s11) **
    regOwn .x15 **
    frameSlotsSaved teerFrame spC (teerSavedVals s) **
    (BitVec.ofNat 64 GuestAddrs.teer_type ↦ₘ (4 : Word)) **
    (BitVec.ofNat 64 GuestAddrs.teer_inner_off ↦ₘ innerVal) **
    regOwn .x13 ** regOwn .x14 ** regOwn .x16 **
    stackFree spVal 6 **
    bytesRegion balPtr balBytes **
    memOwn (BitVec.ofNat 64 GuestAddrs.teer_recipient_ptr) **
    memOwn (BitVec.ofNat 64 GuestAddrs.teer_recipient_len) **
    memOwn (BitVec.ofNat 64 GuestAddrs.teer_value_nonzero) **
    memOwn (BitVec.ofNat 64 GuestAddrs.teer_authority) **
    memOwn (BitVec.ofNat 64 GuestAddrs.teer_acct_ptr) **
    memOwn (BitVec.ofNat 64 GuestAddrs.teer_acct_len) **
    memOwn (BitVec.ofNat 64 GuestAddrs.teer_acct_absent) **
    (BitVec.ofNat 64 GuestAddrs.teer_rolled_back ↦ₘ rolledVal) **
    memOwn (BitVec.ofNat 64 GuestAddrs.teer_prior_count) **
    memOwn (BitVec.ofNat 64 GuestAddrs.teer_pre_acct) **
    memOwn (BitVec.ofNat 64 GuestAddrs.teer_success_count) **
    (BitVec.ofNat 64 GuestAddrs.teer_regular_refund ↦ₘ refund) **
    memOwn (BitVec.ofNat 64 GuestAddrs.teer_prior_set_flag) **
    memOwn (BitVec.ofNat 64 GuestAddrs.teer_finals) **
    memOwn (BitVec.ofNat 64 GuestAddrs.teer_success_table) **
    memOwn (BitVec.ofNat 64 GuestAddrs.teer_predelegated_count) **
    memOwn (BitVec.ofNat 64 GuestAddrs.teer_wouldbe_state) **
    memOwn (BitVec.ofNat 64 GuestAddrs.teer_wouldbe_regular) **
    memOwn (BitVec.ofNat 64 GuestAddrs.teer_recover_scratch) **
    memOwn (BitVec.ofNat 64 GuestAddrs.teer_records_ptr)

/-- Peel memOwn rolled/regular from AmbientPost → ∃ values (memIs). -/
theorem teerAuthLoopEmptyAmbientPost_peel
    (spVal spC listBase listLenW s0 s1 s2 s3 : Word)
    (bytes : List (BitVec 8))
    (balPtr chainIdW baiW : Word)
    (s : TeerSaved) (balBytes : List (BitVec 8))
    (innerVal cursorV endW s11 : Word) :
    ∀ h,
      teerAuthLoopEmptyAmbientPost spVal spC listBase listLenW s0 s1 s2 s3 bytes
        balPtr chainIdW baiW s balBytes innerVal cursorV endW s11 h →
      ∃ (refund rolledVal : Word),
        ((teerListCountAuthLoopPost spC listBase AuthCountAddr s0 s1 s2 s3
            (0 : Word) bytes 0 listLenW) **
          teerAuthLoopEmptyAmbientMemIs spVal spC balPtr chainIdW s balBytes
            innerVal endW s11 refund rolledVal) h := by
  intro h hp0
  dsimp only [teerAuthLoopEmptyAmbientPost, teerListCountAuthLoopAmbient] at hp0
  -- Pull memOwn rolled leftmost (GuestAddrs form matches Ambient unfold)
  have hp1 :
      (memOwn (BitVec.ofNat 64 GuestAddrs.teer_rolled_back) **
        ((teerListCountAuthLoopPost spC listBase AuthCountAddr s0 s1 s2 s3
            (0 : Word) bytes 0 listLenW) **
          ((.x20 ↦ᵣ chainIdW) ** (.x25 ↦ᵣ endW) **
            (.x26 ↦ᵣ (0 : Word)) ** (.x27 ↦ᵣ s11) **
            regOwn .x15 **
            frameSlotsSaved teerFrame spC (teerSavedVals s) **
            (BitVec.ofNat 64 GuestAddrs.teer_type ↦ₘ (4 : Word)) **
            (BitVec.ofNat 64 GuestAddrs.teer_inner_off ↦ₘ innerVal) **
            regOwn .x13 ** regOwn .x14 ** regOwn .x16 **
            stackFree spVal 6 **
            bytesRegion balPtr balBytes **
            memOwn (BitVec.ofNat 64 GuestAddrs.teer_recipient_ptr) **
            memOwn (BitVec.ofNat 64 GuestAddrs.teer_recipient_len) **
            memOwn (BitVec.ofNat 64 GuestAddrs.teer_value_nonzero) **
            memOwn (BitVec.ofNat 64 GuestAddrs.teer_authority) **
            memOwn (BitVec.ofNat 64 GuestAddrs.teer_acct_ptr) **
            memOwn (BitVec.ofNat 64 GuestAddrs.teer_acct_len) **
            memOwn (BitVec.ofNat 64 GuestAddrs.teer_acct_absent) **
            memOwn (BitVec.ofNat 64 GuestAddrs.teer_prior_count) **
            memOwn (BitVec.ofNat 64 GuestAddrs.teer_pre_acct) **
            memOwn (BitVec.ofNat 64 GuestAddrs.teer_success_count) **
            memOwn (BitVec.ofNat 64 GuestAddrs.teer_regular_refund) **
            memOwn (BitVec.ofNat 64 GuestAddrs.teer_prior_set_flag) **
            memOwn (BitVec.ofNat 64 GuestAddrs.teer_finals) **
            memOwn (BitVec.ofNat 64 GuestAddrs.teer_success_table) **
            memOwn (BitVec.ofNat 64 GuestAddrs.teer_predelegated_count) **
            memOwn (BitVec.ofNat 64 GuestAddrs.teer_wouldbe_state) **
            memOwn (BitVec.ofNat 64 GuestAddrs.teer_wouldbe_regular) **
            memOwn (BitVec.ofNat 64 GuestAddrs.teer_recover_scratch) **
            memOwn (BitVec.ofNat 64 GuestAddrs.teer_records_ptr)))) h := by
    xperm_hyp hp0
  obtain ⟨rolledVal, hp2⟩ := sepConj_choose_memOwn hp1
  have hp3 :
      (memOwn (BitVec.ofNat 64 GuestAddrs.teer_regular_refund) **
        ((teerListCountAuthLoopPost spC listBase AuthCountAddr s0 s1 s2 s3
            (0 : Word) bytes 0 listLenW) **
          ((.x20 ↦ᵣ chainIdW) ** (.x25 ↦ᵣ endW) **
            (.x26 ↦ᵣ (0 : Word)) ** (.x27 ↦ᵣ s11) **
            regOwn .x15 **
            frameSlotsSaved teerFrame spC (teerSavedVals s) **
            (BitVec.ofNat 64 GuestAddrs.teer_type ↦ₘ (4 : Word)) **
            (BitVec.ofNat 64 GuestAddrs.teer_inner_off ↦ₘ innerVal) **
            regOwn .x13 ** regOwn .x14 ** regOwn .x16 **
            stackFree spVal 6 **
            bytesRegion balPtr balBytes **
            memOwn (BitVec.ofNat 64 GuestAddrs.teer_recipient_ptr) **
            memOwn (BitVec.ofNat 64 GuestAddrs.teer_recipient_len) **
            memOwn (BitVec.ofNat 64 GuestAddrs.teer_value_nonzero) **
            memOwn (BitVec.ofNat 64 GuestAddrs.teer_authority) **
            memOwn (BitVec.ofNat 64 GuestAddrs.teer_acct_ptr) **
            memOwn (BitVec.ofNat 64 GuestAddrs.teer_acct_len) **
            memOwn (BitVec.ofNat 64 GuestAddrs.teer_acct_absent) **
            (BitVec.ofNat 64 GuestAddrs.teer_rolled_back ↦ₘ rolledVal) **
            memOwn (BitVec.ofNat 64 GuestAddrs.teer_prior_count) **
            memOwn (BitVec.ofNat 64 GuestAddrs.teer_pre_acct) **
            memOwn (BitVec.ofNat 64 GuestAddrs.teer_success_count) **
            memOwn (BitVec.ofNat 64 GuestAddrs.teer_prior_set_flag) **
            memOwn (BitVec.ofNat 64 GuestAddrs.teer_finals) **
            memOwn (BitVec.ofNat 64 GuestAddrs.teer_success_table) **
            memOwn (BitVec.ofNat 64 GuestAddrs.teer_predelegated_count) **
            memOwn (BitVec.ofNat 64 GuestAddrs.teer_wouldbe_state) **
            memOwn (BitVec.ofNat 64 GuestAddrs.teer_wouldbe_regular) **
            memOwn (BitVec.ofNat 64 GuestAddrs.teer_recover_scratch) **
            memOwn (BitVec.ofNat 64 GuestAddrs.teer_records_ptr)))) h := by
    xperm_hyp hp2
  obtain ⟨refund, hp4⟩ := sepConj_choose_memOwn hp3
  refine ⟨refund, rolledVal, ?_⟩
  dsimp only [teerAuthLoopEmptyAmbientMemIs]
  xperm_hyp hp4

/-- MemIs ambient + rolledVal=0 → Source. -/
theorem teerAuthLoopEmptyAmbientMemIs_to_source
    (spVal spC listBase listLenW s0 s1 s2 s3 : Word)
    (bytes : List (BitVec 8))
    (balPtr chainIdW : Word)
    (s : TeerSaved) (balBytes : List (BitVec 8))
    (innerVal endW s11 refund rolledVal : Word)
    (hrolled0 : rolledVal = (0 : Word)) :
    ∀ h,
      ((teerListCountAuthLoopPost spC listBase AuthCountAddr s0 s1 s2 s3
          (0 : Word) bytes 0 listLenW) **
        teerAuthLoopEmptyAmbientMemIs spVal spC balPtr chainIdW s balBytes
          innerVal endW s11 refund rolledVal) h →
      teerAuthLoopEmptySource spVal spC listBase listLenW s0 s1 s2 s3 bytes
        balPtr chainIdW s balBytes innerVal endW s11 refund h := by
  intro h hp
  dsimp only [teerAuthLoopEmptySource, teerAuthLoopEmptyAmbientMemIs,
    RolledBackAddr, RegularRefundAddr, WouldbeStateAddr, WouldbeRegularAddr] at hp ⊢
  -- Both sides now GuestAddrs form; rolledVal→0
  simpa [hrolled0] using hp

/-- AmbientPost → ∃ refund, Source under ScratchZero preserve (rolled stays 0).
    `hrolled0` discharges the peeled rolled cell value. -/
theorem teerAuthLoopEmptyAmbientPost_to_source
    (spVal spC listBase listLenW s0 s1 s2 s3 : Word)
    (bytes : List (BitVec 8))
    (balPtr chainIdW baiW : Word)
    (s : TeerSaved) (balBytes : List (BitVec 8))
    (innerVal cursorV endW s11 : Word)
    (hrolled0 : ∀ (refund rolledVal : Word) h,
      ((teerListCountAuthLoopPost spC listBase AuthCountAddr s0 s1 s2 s3
          (0 : Word) bytes 0 listLenW) **
        teerAuthLoopEmptyAmbientMemIs spVal spC balPtr chainIdW s balBytes
          innerVal endW s11 refund rolledVal) h →
      rolledVal = (0 : Word)) :
    ∀ h,
      teerAuthLoopEmptyAmbientPost spVal spC listBase listLenW s0 s1 s2 s3 bytes
        balPtr chainIdW baiW s balBytes innerVal cursorV endW s11 h →
      ∃ (refund : Word),
        teerAuthLoopEmptySource spVal spC listBase listLenW s0 s1 s2 s3 bytes
          balPtr chainIdW s balBytes innerVal endW s11 refund h := by
  intro h hp
  obtain ⟨refund, rolledVal, hpM⟩ :=
    teerAuthLoopEmptyAmbientPost_peel spVal spC listBase listLenW s0 s1 s2 s3
      bytes balPtr chainIdW baiW s balBytes innerVal cursorV endW s11 h hp
  refine ⟨refund, ?_⟩
  exact teerAuthLoopEmptyAmbientMemIs_to_source spVal spC listBase listLenW
    s0 s1 s2 s3 bytes balPtr chainIdW s balBytes innerVal endW s11
    refund rolledVal (hrolled0 refund rolledVal h hpM) h hpM

/-- Named residual packaging: AmbientPost → Source.
    Filled when ScratchZero preserve gives rolled=0 after peel. -/
structure TeerAuthLoopEmptyAmbientToSourceAssumed where
  reshape :
    ∀ (spVal spC listBase listLenW s0 s1 s2 s3 : Word)
      (bytes : List (BitVec 8))
      (balPtr chainIdW baiW : Word)
      (s : TeerSaved) (balBytes : List (BitVec 8))
      (innerVal cursorV endW s11 : Word),
      ∀ h,
        teerAuthLoopEmptyAmbientPost spVal spC listBase listLenW s0 s1 s2 s3 bytes
          balPtr chainIdW baiW s balBytes innerVal cursorV endW s11 h →
        ∃ refund,
          teerAuthLoopEmptySource spVal spC listBase listLenW s0 s1 s2 s3 bytes
            balPtr chainIdW s balBytes innerVal endW s11 refund h

/-- Fill Ambient→Source Assumed from rolled=0 preserve hyp. -/
def teerAuthLoopEmptyAmbientToSourceAssumed_of_rolled0
    (hrolled0_all :
      ∀ (spVal spC listBase listLenW s0 s1 s2 s3 : Word)
        (bytes : List (BitVec 8))
        (balPtr chainIdW : Word)
        (s : TeerSaved) (balBytes : List (BitVec 8))
        (innerVal endW s11 refund rolledVal : Word) h,
        ((teerListCountAuthLoopPost spC listBase AuthCountAddr s0 s1 s2 s3
            (0 : Word) bytes 0 listLenW) **
          teerAuthLoopEmptyAmbientMemIs spVal spC balPtr chainIdW s balBytes
            innerVal endW s11 refund rolledVal) h →
        rolledVal = (0 : Word)) :
    TeerAuthLoopEmptyAmbientToSourceAssumed where
  reshape := fun spVal spC listBase listLenW s0 s1 s2 s3 bytes
      balPtr chainIdW baiW s balBytes innerVal cursorV endW s11 =>
    teerAuthLoopEmptyAmbientPost_to_source spVal spC listBase listLenW
      s0 s1 s2 s3 bytes balPtr chainIdW baiW s balBytes innerVal cursorV
      endW s11 (fun refund rolledVal h hp =>
        hrolled0_all spVal spC listBase listLenW s0 s1 s2 s3 bytes
          balPtr chainIdW s balBytes innerVal endW s11 refund rolledVal h hp)

/-- AmbientPost → ret under rolled=0 preserve + identity wire.
    Composes peel→Source→Source_toRet. -/
theorem teerAuthLoopEmptyAmbientPost_toRet
    (spVal spC listBase listLenW s0 s1 s2 s3 : Word)
    (bytes : List (BitVec 8))
    (balPtr chainIdW baiW : Word)
    (s : TeerSaved) (balBytes : List (BitVec 8))
    (innerVal cursorV endW s11 : Word)
    (regionBase : Word) (bs : List (BitVec 8))
    (hbase : listBase = regionBase) (hbytes : bytes = bs)
    (hs0 : s0 = s.s0) (hs1 : s1 = s.s1) (hs2 : s2 = s.s2) (hs3 : s3 = s.s3)
    (hs4 : chainIdW = s.s4) (hs9 : endW = s.s9) (hs11 : s11 = s.s11)
    (hspC : spC = spVal + signExtend12 (-160 : BitVec 12))
    (hret : s.ra &&& ~~~(1 : Word) = s.ra)
    (hrolled0 : ∀ (refund rolledVal : Word) h,
      ((teerListCountAuthLoopPost spC listBase AuthCountAddr s0 s1 s2 s3
          (0 : Word) bytes 0 listLenW) **
        teerAuthLoopEmptyAmbientMemIs spVal spC balPtr chainIdW s balBytes
          innerVal endW s11 refund rolledVal) h →
      rolledVal = (0 : Word)) :
    cpsTripleWithin 30 AfterAuthLoopLi s.ra teerLinkedField0
      (teerAuthLoopEmptyAmbientPost spVal spC listBase listLenW s0 s1 s2 s3 bytes
        balPtr chainIdW baiW s balBytes innerVal cursorV endW s11)
      (fun hp =>
        ∃ (refund _t0Old _t1Old baiW' : Word),
          ((((.x10 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ s.ra) ** (.x2 ↦ᵣ spVal) **
              (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
              (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) **
              (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) **
              (.x23 ↦ᵣ s.s7) ** (.x24 ↦ᵣ s.s8) ** (.x25 ↦ᵣ s.s9) **
              (.x26 ↦ᵣ s.s10) ** (.x27 ↦ᵣ s.s11) **
              frameSlotsSaved teerEpiFrame spC (teerSavedVals s) **
              (.x11 ↦ᵣ refund) ** (.x5 ↦ᵣ RolledBackAddr) **
              (.x6 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
              (RegularRefundAddr ↦ₘ refund) **
              memOwn WouldbeStateAddr ** memOwn WouldbeRegularAddr **
              (RolledBackAddr ↦ₘ (0 : Word))) **
              teerEmptyAuthExitFrame baiW' spVal spC regionBase bs balBytes balPtr) **
            stackFree spC 6) hp) := by
  intro R hR st hcr hPR hpc
  obtain ⟨h0, hcompat, h1, h2, hd, hu, hAmb, hR2⟩ := hPR
  obtain ⟨refund, hSrc⟩ :=
    teerAuthLoopEmptyAmbientPost_to_source spVal spC listBase listLenW
      s0 s1 s2 s3 bytes balPtr chainIdW baiW s balBytes innerVal cursorV
      endW s11 hrolled0 h1 hAmb
  have hrun :=
    teerAuthLoopEmptySource_toRet spVal spC listBase listLenW s0 s1 s2 s3 bytes
      balPtr chainIdW s balBytes innerVal endW s11 refund regionBase bs
      hbase hbytes hs0 hs1 hs2 hs3 hs4 hs9 hs11 hspC hret
  have hPR' :
      ((teerAuthLoopEmptySource spVal spC listBase listLenW s0 s1 s2 s3 bytes
          balPtr chainIdW s balBytes innerVal endW s11 refund ** R)).holdsFor st :=
    ⟨h0, hcompat, h1, h2, hd, hu, hSrc, hR2⟩
  obtain ⟨k, hk, st', hexec, hpc', hQ⟩ :=
    hrun R hR st hcr hPR' hpc
  refine ⟨k, hk, st', hexec, hpc', ?_⟩
  obtain ⟨h0', hcompat', h1', h2', hd', hu', ⟨t0, t1, bai', hRet⟩, hR'⟩ := hQ
  exact ⟨h0', hcompat', h1', h2', hd', hu', ⟨refund, t0, t1, bai', hRet⟩, hR'⟩

/-- BridgePre → ret under empty count=0 + hrolled0 + identity wire.
    nSteps = nListCountAuthLoopStart + 30. -/
def nBridgePreToRet (listLen : Nat) : Nat :=
  nListCountAuthLoopStart listLen + 30

theorem teerBridgePre_toRet_empty
    (asm : TeerListCountAuthLoopAssumed teerLinkedCount)
    (spVal spC newSp listBase listLenW oldCount s0 s1 s2 s3 : Word)
    (bytes : List (BitVec 8)) (listLen : Nat)
    (old1 s7Old v24 : Word)
    (balPtr chainIdW baiW : Word)
    (s : TeerSaved) (balBytes : List (BitVec 8))
    (innerVal cursorV endW s11 loadPtr lenW balLenW : Word)
    (regionBase : Word) (bs : List (BitVec 8))
    (content : Word)
    (hoff : (0 : Nat) < bytes.length)
    (hbase : listBase = regionBase) (hbytes : bytes = bs)
    (hcontent : content = listBase)
    (hs0 : s0 = loadPtr) (hs1 : s1 = lenW) (hs2 : s2 = balPtr) (hs3 : s3 = balLenW)
    (hv24 : v24 = cursorV)
    (hs0s : s0 = s.s0) (hs1s : s1 = s.s1) (hs2s : s2 = s.s2) (hs3s : s3 = s.s3)
    (hs4 : chainIdW = s.s4) (hs9 : endW = s.s9) (hs11 : s11 = s.s11)
    (hspC : spC = spVal + signExtend12 (-160 : BitVec 12))
    (hretRa : s.ra &&& ~~~(1 : Word) = s.ra)
    (hlistLenW : listLenW = BitVec.ofNat 64 listLen)
    (hsalign : listBase.toNat % 8 = 0)
    (hslack : listLen + 9 ≤ bytes.length)
    (hover : listBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true)
    (hnewSp : newSp = spC + signExtend12 (-48 : BitVec 12))
    (hret : (LinkListCount &&& ~~~(1 : Word)) = LinkListCount)
    (hsuccess : Success bytes listBase listLen 0)
    (hspe : ListCountResultSpecialize bytes listBase listLen 0 (0 : Word))
    (hlen : listLenW ≠ (0 : Word))
    (hoverOff : listBase.toNat + 0 < 2 ^ 64)
    (hvalidOff : isValidByteAccess (listBase + BitVec.ofNat 64 0) = true)
    (h_ge : ¬ BitVec.ult ((bytes[0]'hoff).zeroExtend 64) (0xc0 : Word) = true)
    (h_hi : BitVec.ult ((bytes[0]'hoff).zeroExtend 64) (0xf8 : Word) = true)
    (h_exact : (listBase + BitVec.ofNat 64 0) +
        (((bytes[0]'hoff).zeroExtend 64 - (0xc0 : Word)) +
          signExtend12 (1 : BitVec 12)) =
      (listBase + BitVec.ofNat 64 0) + listLenW)
    (hrolled0 : ∀ (refund rolledVal : Word) h,
      ((teerListCountAuthLoopPost spC listBase AuthCountAddr s0 s1 s2 s3
          (0 : Word) bytes 0 listLenW) **
        teerAuthLoopEmptyAmbientMemIs spVal spC balPtr chainIdW s balBytes
          innerVal endW s11 refund rolledVal) h →
      rolledVal = (0 : Word)) :
    cpsTripleWithin (nBridgePreToRet listLen) AtListCount s.ra teerLinkedField0
      (teerAuthContentBridgePre spVal spC old1 loadPtr lenW balPtr balLenW chainIdW
        content listLenW s7Old cursorV endW s11 s innerVal oldCount
        regionBase bs balBytes)
      (fun hp =>
        ∃ (refund _t0Old _t1Old baiW' : Word),
          ((((.x10 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ s.ra) ** (.x2 ↦ᵣ spVal) **
              (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
              (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) **
              (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) **
              (.x23 ↦ᵣ s.s7) ** (.x24 ↦ᵣ s.s8) ** (.x25 ↦ᵣ s.s9) **
              (.x26 ↦ᵣ s.s10) ** (.x27 ↦ᵣ s.s11) **
              frameSlotsSaved teerEpiFrame spC (teerSavedVals s) **
              (.x11 ↦ᵣ refund) ** (.x5 ↦ᵣ RolledBackAddr) **
              (.x6 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
              (RegularRefundAddr ↦ₘ refund) **
              memOwn WouldbeStateAddr ** memOwn WouldbeRegularAddr **
              (RolledBackAddr ↦ₘ (0 : Word))) **
              teerEmptyAuthExitFrame baiW' spVal spC regionBase bs balBytes balPtr) **
            stackFree spC 6) hp) := by
  have hmid :=
    teerBridgePre_to_AfterAuthLoopLi_empty asm spVal spC newSp listBase listLenW
      oldCount s0 s1 s2 s3 bytes listLen old1 s7Old v24 balPtr chainIdW baiW s
      balBytes innerVal cursorV endW s11 loadPtr lenW balLenW regionBase bs content
      hoff hbase hbytes hcontent hs0 hs1 hs2 hs3 hv24 hlistLenW hsalign hslack
      hover hvalid hnewSp hret hsuccess hspe hlen hoverOff hvalidOff h_ge h_hi h_exact
  have hmidF :
      cpsTripleWithin (nListCountAuthLoopStart listLen) AtListCount AfterAuthLoopLi
        teerLinkedField0
        (teerAuthContentBridgePre spVal spC old1 loadPtr lenW balPtr balLenW chainIdW
          content listLenW s7Old cursorV endW s11 s innerVal oldCount
          regionBase bs balBytes)
        (teerAuthLoopEmptyAmbientPost spVal spC listBase listLenW s0 s1 s2 s3 bytes
          balPtr chainIdW baiW s balBytes innerVal cursorV endW s11) := by
    have h :=
      cpsTripleWithin_extend_code teerField0_mono_count hmid
    exact cpsTripleWithin_weaken (fun _ hp => hp)
      (fun _ hq => by
        dsimp only [teerAuthLoopEmptyAmbientPost]
        exact hq) h
  have hretT :=
    teerAuthLoopEmptyAmbientPost_toRet spVal spC listBase listLenW s0 s1 s2 s3
      bytes balPtr chainIdW baiW s balBytes innerVal cursorV endW s11
      regionBase bs hbase hbytes hs0s hs1s hs2s hs3s hs4 hs9 hs11 hspC hretRa
      hrolled0
  have hseq :=
    cpsTripleWithin_seq_perm_same_cr (fun _ hp => hp) hmidF hretT
  exact cpsTripleWithin_mono_nSteps (by
    dsimp only [nBridgePreToRet]; omega) hseq

/-- AmbientPost → ∃ refund t0 t1 bai, ExitPack under hrolled0 + identity wire.
    Composes peel→Source→to_exitPack. Pure reshape (0 steps).
    Front post ExitPre**ExitFrame is ExitPack without nested free;
    ExitPack is the honest list_count empty exit shape (nested free preserved). -/
theorem teerAuthLoopEmptyAmbientPost_to_exitPack
    (spVal spC listBase listLenW s0 s1 s2 s3 : Word)
    (bytes : List (BitVec 8))
    (balPtr chainIdW baiW : Word)
    (s : TeerSaved) (balBytes : List (BitVec 8))
    (innerVal cursorV endW s11 : Word)
    (regionBase : Word) (bs : List (BitVec 8))
    (hbase : listBase = regionBase) (hbytes : bytes = bs)
    (hs0 : s0 = s.s0) (hs1 : s1 = s.s1) (hs2 : s2 = s.s2) (hs3 : s3 = s.s3)
    (hs4 : chainIdW = s.s4) (hs9 : endW = s.s9) (hs11 : s11 = s.s11)
    (hrolled0 : ∀ (refund rolledVal : Word) h,
      ((teerListCountAuthLoopPost spC listBase AuthCountAddr s0 s1 s2 s3
          (0 : Word) bytes 0 listLenW) **
        teerAuthLoopEmptyAmbientMemIs spVal spC balPtr chainIdW s balBytes
          innerVal endW s11 refund rolledVal) h →
      rolledVal = (0 : Word)) :
    ∀ h,
      teerAuthLoopEmptyAmbientPost spVal spC listBase listLenW s0 s1 s2 s3 bytes
        balPtr chainIdW baiW s balBytes innerVal cursorV endW s11 h →
      ∃ (refund t0Old t1Old baiW' : Word),
        teerAuthLoopEmptyExitPack spVal spC s
          (teerAuthLoopEmptyWalkCur listBase)
          (teerAuthLoopEmptyWalkEnd listBase listLenW)
          refund
          (teerAuthLoopEmptyWalkCur listBase)
          (teerAuthLoopEmptyWalkEnd listBase listLenW)
          t0Old t1Old baiW'
          regionBase bs balBytes balPtr h := by
  intro h hp
  obtain ⟨refund, hSrc⟩ :=
    teerAuthLoopEmptyAmbientPost_to_source spVal spC listBase listLenW s0 s1 s2 s3
      bytes balPtr chainIdW baiW s balBytes innerVal cursorV endW s11 hrolled0 h hp
  obtain ⟨t0Old, t1Old, baiW', hPack⟩ :=
    teerAuthLoopEmpty_to_exitPack spVal spC listBase listLenW s0 s1 s2 s3 bytes
      balPtr chainIdW s balBytes innerVal endW s11 refund regionBase bs
      hbase hbytes hs0 hs1 hs2 hs3 hs4 hs9 hs11 h hSrc
  exact ⟨refund, t0Old, t1Old, baiW', hPack⟩

/-- BridgePre → AfterAuthLoopLi with ExitPack post under empty count + hrolled0.
    Pure reshape of AmbientPost after framed_empty. Mid-segment for Front inhabit. -/
theorem teerBridgePre_to_exitPack_empty
    (asm : TeerListCountAuthLoopAssumed teerLinkedCount)
    (spVal spC newSp listBase listLenW oldCount s0 s1 s2 s3 : Word)
    (bytes : List (BitVec 8)) (listLen : Nat)
    (old1 s7Old v24 : Word)
    (balPtr chainIdW baiW : Word)
    (s : TeerSaved) (balBytes : List (BitVec 8))
    (innerVal cursorV endW s11 loadPtr lenW balLenW : Word)
    (regionBase : Word) (bs : List (BitVec 8))
    (content : Word)
    (hoff : (0 : Nat) < bytes.length)
    (hbase : listBase = regionBase) (hbytes : bytes = bs)
    (hcontent : content = listBase)
    (hs0 : s0 = loadPtr) (hs1 : s1 = lenW) (hs2 : s2 = balPtr) (hs3 : s3 = balLenW)
    (hv24 : v24 = cursorV)
    (hs0s : s0 = s.s0) (hs1s : s1 = s.s1) (hs2s : s2 = s.s2) (hs3s : s3 = s.s3)
    (hs4 : chainIdW = s.s4) (hs9 : endW = s.s9) (hs11 : s11 = s.s11)
    (hlistLenW : listLenW = BitVec.ofNat 64 listLen)
    (hsalign : listBase.toNat % 8 = 0)
    (hslack : listLen + 9 ≤ bytes.length)
    (hover : listBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true)
    (hnewSp : newSp = spC + signExtend12 (-48 : BitVec 12))
    (hret : (LinkListCount &&& ~~~(1 : Word)) = LinkListCount)
    (hsuccess : Success bytes listBase listLen 0)
    (hspe : ListCountResultSpecialize bytes listBase listLen 0 (0 : Word))
    (hlen : listLenW ≠ (0 : Word))
    (hoverOff : listBase.toNat + 0 < 2 ^ 64)
    (hvalidOff : isValidByteAccess (listBase + BitVec.ofNat 64 0) = true)
    (h_ge : ¬ BitVec.ult ((bytes[0]'hoff).zeroExtend 64) (0xc0 : Word) = true)
    (h_hi : BitVec.ult ((bytes[0]'hoff).zeroExtend 64) (0xf8 : Word) = true)
    (h_exact : (listBase + BitVec.ofNat 64 0) +
        (((bytes[0]'hoff).zeroExtend 64 - (0xc0 : Word)) +
          signExtend12 (1 : BitVec 12)) =
      (listBase + BitVec.ofNat 64 0) + listLenW)
    (hrolled0 : ∀ (refund rolledVal : Word) h,
      ((teerListCountAuthLoopPost spC listBase AuthCountAddr s0 s1 s2 s3
          (0 : Word) bytes 0 listLenW) **
        teerAuthLoopEmptyAmbientMemIs spVal spC balPtr chainIdW s balBytes
          innerVal endW s11 refund rolledVal) h →
      rolledVal = (0 : Word)) :
    cpsTripleWithin (nListCountAuthLoopStart listLen) AtListCount AfterAuthLoopLi
      teerLinkedField0
      (teerAuthContentBridgePre spVal spC old1 loadPtr lenW balPtr balLenW chainIdW
        content listLenW s7Old cursorV endW s11 s innerVal oldCount
        regionBase bs balBytes)
      (fun hp =>
        ∃ (refund t0Old t1Old baiW' : Word),
          teerAuthLoopEmptyExitPack spVal spC s
            (teerAuthLoopEmptyWalkCur listBase)
            (teerAuthLoopEmptyWalkEnd listBase listLenW)
            refund
            (teerAuthLoopEmptyWalkCur listBase)
            (teerAuthLoopEmptyWalkEnd listBase listLenW)
            t0Old t1Old baiW'
            regionBase bs balBytes balPtr hp) := by
  have hmid :=
    teerBridgePre_to_AfterAuthLoopLi_empty asm spVal spC newSp listBase listLenW
      oldCount s0 s1 s2 s3 bytes listLen old1 s7Old v24 balPtr chainIdW baiW s
      balBytes innerVal cursorV endW s11 loadPtr lenW balLenW regionBase bs content
      hoff hbase hbytes hcontent hs0 hs1 hs2 hs3 hv24 hlistLenW hsalign hslack
      hover hvalid hnewSp hret hsuccess hspe hlen hoverOff hvalidOff h_ge h_hi h_exact
  have hmidF :
      cpsTripleWithin (nListCountAuthLoopStart listLen) AtListCount AfterAuthLoopLi
        teerLinkedField0
        (teerAuthContentBridgePre spVal spC old1 loadPtr lenW balPtr balLenW chainIdW
          content listLenW s7Old cursorV endW s11 s innerVal oldCount
          regionBase bs balBytes)
        (teerAuthLoopEmptyAmbientPost spVal spC listBase listLenW s0 s1 s2 s3 bytes
          balPtr chainIdW baiW s balBytes innerVal cursorV endW s11) := by
    have h :=
      cpsTripleWithin_extend_code teerField0_mono_count hmid
    exact cpsTripleWithin_weaken (fun _ hp => hp)
      (fun _ hq => by
        dsimp only [teerAuthLoopEmptyAmbientPost]
        exact hq) h
  exact cpsTripleWithin_weaken (fun _ hp => hp)
    (fun h hq =>
      teerAuthLoopEmptyAmbientPost_to_exitPack spVal spC listBase listLenW
        s0 s1 s2 s3 bytes balPtr chainIdW baiW s balBytes innerVal cursorV
        endW s11 regionBase bs hbase hbytes hs0s hs1s hs2s hs3s hs4 hs9 hs11
        hrolled0 h hq) hmidF

/-- ExitPack splits to Front ExitPre**ExitFrame on h1 + nested free on h2.
    FrontToAuthLoopAssumed posts ExitPre**ExitFrame (free20 path);
    free26 callers keep nested free via this split + stackFree26_split. -/
theorem teerAuthLoopEmptyExitPack_split
    (spVal spC : Word) (s : TeerSaved)
    (walkCur walkEnd refund a0Old a1Old t0Old t1Old baiW : Word)
    (regionBase : Word) (bs balBytes : List (BitVec 8)) (balPtr : Word) :
    ∀ h,
      teerAuthLoopEmptyExitPack spVal spC s walkCur walkEnd refund
        a0Old a1Old t0Old t1Old baiW regionBase bs balBytes balPtr h →
      ∃ h1 h2,
        h1.Disjoint h2 ∧ h1.union h2 = h ∧
          (teerAuthLoopEmptyExitPre spC s walkCur walkEnd refund
              a0Old a1Old t0Old t1Old **
            teerEmptyAuthExitFrame baiW spVal spC regionBase bs balBytes balPtr) h1 ∧
          stackFree spC 6 h2 := by
  intro h hp
  dsimp only [teerAuthLoopEmptyExitPack] at hp
  exact hp

#print axioms teerAuthLoopEmpty_exitToRet_rolled0
#print axioms teerAuthLoopEmptyExitPack_toRet
#print axioms teerAuthLoopEmpty_to_exitPack
#print axioms teerAuthLoopEmptySource_toRet
#print axioms teerAuthLoopEmptyAmbientPost_peel
#print axioms teerAuthLoopEmptyAmbientMemIs_to_source
#print axioms teerAuthLoopEmptyAmbientPost_to_source
#print axioms teerAuthLoopEmptyAmbientPost_toRet
#print axioms teerBridgePre_toRet_empty
#print axioms teerAuthLoopEmptyAmbientPost_to_exitPack
#print axioms teerAuthLoopEmptyExitPack_split
#print axioms teerBridgePre_to_exitPack_empty

/-- Residual packaging: AuthContent free26 → BridgePre with fixed content witnesses.
    Witnesses (`content`/`listLenW`/`oldCount`) are structure fields (not ∀-quantified),
    matching applied exists post after specialize (empty identity: content=listBase).
    Body residual: wire `teerAuthContent_applied` as hrun into
    `teerAuthContent_free26_to_bridgePre_field0`, then specialize ∃→fields. -/
structure TeerFrontAuthContentToBridgeAssumed where
  nSteps : Nat
  content : Word
  listLenW : Word
  oldCount : Word
  run :
    ∀ (ret spVal spC regionBase loadPtr lenW balPtr balLenW chainIdW baiW : Word)
      (s : TeerSaved)
      (bs balBytes : List (BitVec 8)) (off len : Nat)
      (old1 s7Old cursorV endW s11 innerVal : Word),
      (ret &&& ~~~(1 : Word)) = ret →
      balPtr ≠ 0 →
      loadPtr = regionBase + BitVec.ofNat 64 off →
      off + len ≤ bs.length →
      spC = spVal + signExtend12 (-160 : BitVec 12) →
      s.ra = ret →
      cpsTripleWithin nSteps E AtListCount teerLinkedField0
        ((.x1 ↦ᵣ ret) ** (.x2 ↦ᵣ spVal) **
          stackFree spVal nTeerStackWithListCount **
          (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
          (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) ** (.x20 ↦ᵣ s.s4) **
          (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) ** (.x23 ↦ᵣ s.s7) **
          (.x24 ↦ᵣ s.s8) ** (.x25 ↦ᵣ s.s9) ** (.x26 ↦ᵣ s.s10) **
          (.x27 ↦ᵣ s.s11) **
          (.x10 ↦ᵣ loadPtr) ** (.x11 ↦ᵣ lenW) **
          (.x12 ↦ᵣ balPtr) ** (.x13 ↦ᵣ balLenW) **
          (.x14 ↦ᵣ chainIdW) ** (.x15 ↦ᵣ baiW) **
          bytesRegion regionBase bs ** bytesRegion balPtr balBytes **
          teerScratchOwn **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x16 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
          regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)))
        (teerAuthContentBridgePre spVal spC old1 loadPtr lenW balPtr balLenW
          chainIdW content listLenW s7Old cursorV endW s11 s innerVal oldCount
          regionBase bs balBytes)


/-- free26 empty path: FrontToBridge + list_count AuthLoop steps. -/
def nFree26EmptyToExitPack (nFront listLen : Nat) : Nat :=
  nFront + nListCountAuthLoopStart listLen

def nFree26EmptyToRet (nFront listLen : Nat) : Nat :=
  nFree26EmptyToExitPack nFront listLen + 30

/-- free26 → ExitPack under residual FrontToBridge + empty mid + hrolled0.
    Uses `front.content` / `front.listLenW` / `front.oldCount` witnesses. -/
theorem teerEmptyAuth_free26_to_exitPack
    (front : TeerFrontAuthContentToBridgeAssumed)
    (asm : TeerListCountAuthLoopAssumed teerLinkedCount)
    (ret spVal spC regionBase loadPtr lenW balPtr balLenW chainIdW baiW : Word)
    (s : TeerSaved)
    (bs balBytes : List (BitVec 8)) (off len : Nat)
    (old1 s7Old cursorV endW s11 innerVal : Word)
    (newSp listBase : Word) (listLen : Nat) (bytes : List (BitVec 8))
    (s0 s1 s2 s3 v24 : Word)
    (hoff : (0 : Nat) < bytes.length)
    (hbase : listBase = regionBase) (hbytes : bytes = bs)
    (hcontent : front.content = listBase)
    (hs0 : s0 = loadPtr) (hs1 : s1 = lenW) (hs2 : s2 = balPtr) (hs3 : s3 = balLenW)
    (hv24 : v24 = cursorV)
    (hs0s : s0 = s.s0) (hs1s : s1 = s.s1) (hs2s : s2 = s.s2) (hs3s : s3 = s.s3)
    (hs4 : chainIdW = s.s4) (hs9 : endW = s.s9) (hs11 : s11 = s.s11)
    (hlistLenW : front.listLenW = BitVec.ofNat 64 listLen)
    (hsalign : listBase.toNat % 8 = 0)
    (hslack : listLen + 9 ≤ bytes.length)
    (hover : listBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true)
    (hnewSp : newSp = spC + signExtend12 (-48 : BitVec 12))
    (hretLink : (LinkListCount &&& ~~~(1 : Word)) = LinkListCount)
    (hsuccess : Success bytes listBase listLen 0)
    (hspe : ListCountResultSpecialize bytes listBase listLen 0 (0 : Word))
    (hlen : front.listLenW ≠ (0 : Word))
    (hoverOff : listBase.toNat + 0 < 2 ^ 64)
    (hvalidOff : isValidByteAccess (listBase + BitVec.ofNat 64 0) = true)
    (h_ge : ¬ BitVec.ult ((bytes[0]'hoff).zeroExtend 64) (0xc0 : Word) = true)
    (h_hi : BitVec.ult ((bytes[0]'hoff).zeroExtend 64) (0xf8 : Word) = true)
    (h_exact : (listBase + BitVec.ofNat 64 0) +
        (((bytes[0]'hoff).zeroExtend 64 - (0xc0 : Word)) +
          signExtend12 (1 : BitVec 12)) =
      (listBase + BitVec.ofNat 64 0) + front.listLenW)
    (hrolled0 : ∀ (refund rolledVal : Word) h,
      ((teerListCountAuthLoopPost spC listBase AuthCountAddr s0 s1 s2 s3
          (0 : Word) bytes 0 front.listLenW) **
        teerAuthLoopEmptyAmbientMemIs spVal spC balPtr chainIdW s balBytes
          innerVal endW s11 refund rolledVal) h →
      rolledVal = (0 : Word))
    (hret : (ret &&& ~~~(1 : Word)) = ret)
    (hbal : balPtr ≠ 0)
    (hptr : loadPtr = regionBase + BitVec.ofNat 64 off)
    (hbound : off + len ≤ bs.length)
    (hspC : spC = spVal + signExtend12 (-160 : BitVec 12))
    (hra : s.ra = ret)
    (hold1 : old1 = LinkAuthWalkNext9) :
    cpsTripleWithin (nFree26EmptyToExitPack front.nSteps listLen) E AfterAuthLoopLi
      teerLinkedField0
      ((.x1 ↦ᵣ ret) ** (.x2 ↦ᵣ spVal) **
        stackFree spVal nTeerStackWithListCount **
        (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
        (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) ** (.x20 ↦ᵣ s.s4) **
        (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) ** (.x23 ↦ᵣ s.s7) **
        (.x24 ↦ᵣ s.s8) ** (.x25 ↦ᵣ s.s9) ** (.x26 ↦ᵣ s.s10) **
        (.x27 ↦ᵣ s.s11) **
        (.x10 ↦ᵣ loadPtr) ** (.x11 ↦ᵣ lenW) **
        (.x12 ↦ᵣ balPtr) ** (.x13 ↦ᵣ balLenW) **
        (.x14 ↦ᵣ chainIdW) ** (.x15 ↦ᵣ baiW) **
        bytesRegion regionBase bs ** bytesRegion balPtr balBytes **
        teerScratchOwn **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x16 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
        regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)))
      (fun hp =>
        ∃ (refund t0Old t1Old baiW' : Word),
          teerAuthLoopEmptyExitPack spVal spC s
            (teerAuthLoopEmptyWalkCur listBase)
            (teerAuthLoopEmptyWalkEnd listBase front.listLenW)
            refund
            (teerAuthLoopEmptyWalkCur listBase)
            (teerAuthLoopEmptyWalkEnd listBase front.listLenW)
            t0Old t1Old baiW'
            regionBase bs balBytes balPtr hp) := by
  have hf0 :=
    front.run ret spVal spC regionBase loadPtr lenW balPtr balLenW chainIdW baiW
      s bs balBytes off len old1 s7Old cursorV endW s11 innerVal
      hret hbal hptr hbound hspC hra
  have hf :
      cpsTripleWithin front.nSteps E AtListCount teerLinkedField0
        ((.x1 ↦ᵣ ret) ** (.x2 ↦ᵣ spVal) **
          stackFree spVal nTeerStackWithListCount **
          (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
          (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) ** (.x20 ↦ᵣ s.s4) **
          (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) ** (.x23 ↦ᵣ s.s7) **
          (.x24 ↦ᵣ s.s8) ** (.x25 ↦ᵣ s.s9) ** (.x26 ↦ᵣ s.s10) **
          (.x27 ↦ᵣ s.s11) **
          (.x10 ↦ᵣ loadPtr) ** (.x11 ↦ᵣ lenW) **
          (.x12 ↦ᵣ balPtr) ** (.x13 ↦ᵣ balLenW) **
          (.x14 ↦ᵣ chainIdW) ** (.x15 ↦ᵣ baiW) **
          bytesRegion regionBase bs ** bytesRegion balPtr balBytes **
          teerScratchOwn **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x16 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
          regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)))
        (teerAuthContentBridgePre spVal spC LinkAuthWalkNext9 loadPtr lenW
          balPtr balLenW chainIdW front.content front.listLenW s7Old cursorV endW
          s11 s innerVal front.oldCount regionBase bs balBytes) := by
    simpa [hold1] using hf0
  have hmid :=
    teerBridgePre_to_exitPack_empty asm spVal spC newSp listBase front.listLenW
      front.oldCount s0 s1 s2 s3 bytes listLen LinkAuthWalkNext9 s7Old v24 balPtr
      chainIdW baiW s balBytes innerVal cursorV endW s11 loadPtr lenW balLenW
      regionBase bs front.content hoff hbase hbytes hcontent hs0 hs1 hs2 hs3 hv24
      hs0s hs1s hs2s hs3s hs4 hs9 hs11 hlistLenW hsalign hslack hover hvalid
      hnewSp hretLink hsuccess hspe hlen hoverOff hvalidOff h_ge h_hi h_exact
      hrolled0
  have hseq :=
    cpsTripleWithin_seq_perm_same_cr (fun _ hp => hp) hf hmid
  have hseq' :
      cpsTripleWithin (nFree26EmptyToExitPack front.nSteps listLen) E AfterAuthLoopLi
        teerLinkedField0
        ((.x1 ↦ᵣ ret) ** (.x2 ↦ᵣ spVal) **
          stackFree spVal nTeerStackWithListCount **
          (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
          (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) ** (.x20 ↦ᵣ s.s4) **
          (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) ** (.x23 ↦ᵣ s.s7) **
          (.x24 ↦ᵣ s.s8) ** (.x25 ↦ᵣ s.s9) ** (.x26 ↦ᵣ s.s10) **
          (.x27 ↦ᵣ s.s11) **
          (.x10 ↦ᵣ loadPtr) ** (.x11 ↦ᵣ lenW) **
          (.x12 ↦ᵣ balPtr) ** (.x13 ↦ᵣ balLenW) **
          (.x14 ↦ᵣ chainIdW) ** (.x15 ↦ᵣ baiW) **
          bytesRegion regionBase bs ** bytesRegion balPtr balBytes **
          teerScratchOwn **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x16 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
          regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)))
        (fun hp =>
          ∃ (refund t0Old t1Old baiW' : Word),
            teerAuthLoopEmptyExitPack spVal spC s
              (teerAuthLoopEmptyWalkCur listBase)
              (teerAuthLoopEmptyWalkEnd listBase front.listLenW)
              refund
              (teerAuthLoopEmptyWalkCur listBase)
              (teerAuthLoopEmptyWalkEnd listBase front.listLenW)
              t0Old t1Old baiW'
              regionBase bs balBytes balPtr hp) := by
    dsimp only [nFree26EmptyToExitPack]
    exact hseq
  exact hseq'

/-- free26 → ret a0=0 under residual FrontToBridge + empty mid + hrolled0. -/
theorem teerEmptyAuth_free26_toRet
    (front : TeerFrontAuthContentToBridgeAssumed)
    (asm : TeerListCountAuthLoopAssumed teerLinkedCount)
    (ret spVal spC regionBase loadPtr lenW balPtr balLenW chainIdW baiW : Word)
    (s : TeerSaved)
    (bs balBytes : List (BitVec 8)) (off len : Nat)
    (old1 s7Old cursorV endW s11 innerVal : Word)
    (newSp listBase : Word) (listLen : Nat) (bytes : List (BitVec 8))
    (s0 s1 s2 s3 v24 : Word)
    (hoff : (0 : Nat) < bytes.length)
    (hbase : listBase = regionBase) (hbytes : bytes = bs)
    (hcontent : front.content = listBase)
    (hs0 : s0 = loadPtr) (hs1 : s1 = lenW) (hs2 : s2 = balPtr) (hs3 : s3 = balLenW)
    (hv24 : v24 = cursorV)
    (hs0s : s0 = s.s0) (hs1s : s1 = s.s1) (hs2s : s2 = s.s2) (hs3s : s3 = s.s3)
    (hs4 : chainIdW = s.s4) (hs9 : endW = s.s9) (hs11 : s11 = s.s11)
    (hlistLenW : front.listLenW = BitVec.ofNat 64 listLen)
    (hsalign : listBase.toNat % 8 = 0)
    (hslack : listLen + 9 ≤ bytes.length)
    (hover : listBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true)
    (hnewSp : newSp = spC + signExtend12 (-48 : BitVec 12))
    (hretLink : (LinkListCount &&& ~~~(1 : Word)) = LinkListCount)
    (hsuccess : Success bytes listBase listLen 0)
    (hspe : ListCountResultSpecialize bytes listBase listLen 0 (0 : Word))
    (hlen : front.listLenW ≠ (0 : Word))
    (hoverOff : listBase.toNat + 0 < 2 ^ 64)
    (hvalidOff : isValidByteAccess (listBase + BitVec.ofNat 64 0) = true)
    (h_ge : ¬ BitVec.ult ((bytes[0]'hoff).zeroExtend 64) (0xc0 : Word) = true)
    (h_hi : BitVec.ult ((bytes[0]'hoff).zeroExtend 64) (0xf8 : Word) = true)
    (h_exact : (listBase + BitVec.ofNat 64 0) +
        (((bytes[0]'hoff).zeroExtend 64 - (0xc0 : Word)) +
          signExtend12 (1 : BitVec 12)) =
      (listBase + BitVec.ofNat 64 0) + front.listLenW)
    (hrolled0 : ∀ (refund rolledVal : Word) h,
      ((teerListCountAuthLoopPost spC listBase AuthCountAddr s0 s1 s2 s3
          (0 : Word) bytes 0 front.listLenW) **
        teerAuthLoopEmptyAmbientMemIs spVal spC balPtr chainIdW s balBytes
          innerVal endW s11 refund rolledVal) h →
      rolledVal = (0 : Word))
    (hret : (ret &&& ~~~(1 : Word)) = ret)
    (hbal : balPtr ≠ 0)
    (hptr : loadPtr = regionBase + BitVec.ofNat 64 off)
    (hbound : off + len ≤ bs.length)
    (hspC : spC = spVal + signExtend12 (-160 : BitVec 12))
    (hra : s.ra = ret)
    (hold1 : old1 = LinkAuthWalkNext9) :
    cpsTripleWithin (nFree26EmptyToRet front.nSteps listLen) E ret teerLinkedField0
      ((.x1 ↦ᵣ ret) ** (.x2 ↦ᵣ spVal) **
        stackFree spVal nTeerStackWithListCount **
        (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
        (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) ** (.x20 ↦ᵣ s.s4) **
        (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) ** (.x23 ↦ᵣ s.s7) **
        (.x24 ↦ᵣ s.s8) ** (.x25 ↦ᵣ s.s9) ** (.x26 ↦ᵣ s.s10) **
        (.x27 ↦ᵣ s.s11) **
        (.x10 ↦ᵣ loadPtr) ** (.x11 ↦ᵣ lenW) **
        (.x12 ↦ᵣ balPtr) ** (.x13 ↦ᵣ balLenW) **
        (.x14 ↦ᵣ chainIdW) ** (.x15 ↦ᵣ baiW) **
        bytesRegion regionBase bs ** bytesRegion balPtr balBytes **
        teerScratchOwn **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x16 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
        regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)))
      (fun hp =>
        ∃ (refund _t0Old _t1Old baiW' : Word),
          ((((.x10 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ ret) ** (.x2 ↦ᵣ spVal) **
              (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
              (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) **
              (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) **
              (.x23 ↦ᵣ s.s7) ** (.x24 ↦ᵣ s.s8) ** (.x25 ↦ᵣ s.s9) **
              (.x26 ↦ᵣ s.s10) ** (.x27 ↦ᵣ s.s11) **
              frameSlotsSaved teerEpiFrame spC (teerSavedVals s) **
              (.x11 ↦ᵣ refund) ** (.x5 ↦ᵣ RolledBackAddr) **
              (.x6 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
              (RegularRefundAddr ↦ₘ refund) **
              memOwn WouldbeStateAddr ** memOwn WouldbeRegularAddr **
              (RolledBackAddr ↦ₘ (0 : Word))) **
              teerEmptyAuthExitFrame baiW' spVal spC regionBase bs balBytes balPtr) **
            stackFree spC 6) hp) := by
  have hpack :=
    teerEmptyAuth_free26_to_exitPack front asm ret spVal spC regionBase loadPtr
      lenW balPtr balLenW chainIdW baiW s bs balBytes off len old1 s7Old cursorV
      endW s11 innerVal newSp listBase listLen bytes
      s0 s1 s2 s3 v24 hoff hbase hbytes hcontent hs0 hs1 hs2 hs3 hv24 hs0s hs1s
      hs2s hs3s hs4 hs9 hs11 hlistLenW hsalign hslack hover hvalid hnewSp hretLink
      hsuccess hspe hlen hoverOff hvalidOff h_ge h_hi h_exact hrolled0 hret hbal
      hptr hbound hspC hra hold1
  have hexit :
      cpsTripleWithin 30 AfterAuthLoopLi ret teerLinkedField0
        (fun hp =>
          ∃ (refund t0Old t1Old baiW' : Word),
            teerAuthLoopEmptyExitPack spVal spC s
              (teerAuthLoopEmptyWalkCur listBase)
              (teerAuthLoopEmptyWalkEnd listBase front.listLenW)
              refund
              (teerAuthLoopEmptyWalkCur listBase)
              (teerAuthLoopEmptyWalkEnd listBase front.listLenW)
              t0Old t1Old baiW'
              regionBase bs balBytes balPtr hp)
        (fun hp =>
          ∃ (refund _t0Old _t1Old baiW' : Word),
            ((((.x10 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ ret) ** (.x2 ↦ᵣ spVal) **
                (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
                (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) **
                (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) **
                (.x23 ↦ᵣ s.s7) ** (.x24 ↦ᵣ s.s8) ** (.x25 ↦ᵣ s.s9) **
                (.x26 ↦ᵣ s.s10) ** (.x27 ↦ᵣ s.s11) **
                frameSlotsSaved teerEpiFrame spC (teerSavedVals s) **
                (.x11 ↦ᵣ refund) ** (.x5 ↦ᵣ RolledBackAddr) **
                (.x6 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
                (RegularRefundAddr ↦ₘ refund) **
                memOwn WouldbeStateAddr ** memOwn WouldbeRegularAddr **
                (RolledBackAddr ↦ₘ (0 : Word))) **
                teerEmptyAuthExitFrame baiW' spVal spC regionBase bs balBytes balPtr) **
              stackFree spC 6) hp) := by
    intro R hR st hcr hPR hpc
    obtain ⟨h0, hcompat, h1, h2, hd, hu, ⟨refund, t0, t1, bai', hPack⟩, hR2⟩ := hPR
    have hleaf :=
      teerAuthLoopEmptyExitPack_toRet spVal spC s
        (teerAuthLoopEmptyWalkCur listBase)
        (teerAuthLoopEmptyWalkEnd listBase front.listLenW)
        (teerAuthLoopEmptyWalkCur listBase)
        (teerAuthLoopEmptyWalkEnd listBase front.listLenW)
        t0 t1 refund bai' regionBase bs balBytes balPtr hspC
        (by simpa [hra] using hret)
    have hleaf' :
        cpsTripleWithin 30 AfterAuthLoopLi ret teerLinkedField0
          (teerAuthLoopEmptyExitPack spVal spC s
            (teerAuthLoopEmptyWalkCur listBase)
            (teerAuthLoopEmptyWalkEnd listBase front.listLenW)
            refund
            (teerAuthLoopEmptyWalkCur listBase)
            (teerAuthLoopEmptyWalkEnd listBase front.listLenW)
            t0 t1 bai' regionBase bs balBytes balPtr)
          (fun hp =>
            ((((.x10 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ ret) ** (.x2 ↦ᵣ spVal) **
                (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
                (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) **
                (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) **
                (.x23 ↦ᵣ s.s7) ** (.x24 ↦ᵣ s.s8) ** (.x25 ↦ᵣ s.s9) **
                (.x26 ↦ᵣ s.s10) ** (.x27 ↦ᵣ s.s11) **
                frameSlotsSaved teerEpiFrame spC (teerSavedVals s) **
                (.x11 ↦ᵣ refund) ** (.x5 ↦ᵣ RolledBackAddr) **
                (.x6 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
                (RegularRefundAddr ↦ₘ refund) **
                memOwn WouldbeStateAddr ** memOwn WouldbeRegularAddr **
                (RolledBackAddr ↦ₘ (0 : Word))) **
                teerEmptyAuthExitFrame bai' spVal spC regionBase bs balBytes balPtr) **
              stackFree spC 6) hp) := by
      simpa [hra] using hleaf
    obtain ⟨k, hk, st', hexec, hpc', hQ⟩ :=
      hleaf' R hR st hcr ⟨h0, hcompat, h1, h2, hd, hu, hPack, hR2⟩ hpc
    refine ⟨k, hk, st', hexec, hpc', ?_⟩
    obtain ⟨h0', hcompat', h1', h2', hd', hu', hRet, hR'⟩ := hQ
    exact ⟨h0', hcompat', h1', h2', hd', hu', ⟨refund, t0, t1, bai', hRet⟩, hR'⟩
  have hseq :=
    cpsTripleWithin_seq_perm_same_cr (fun _ hp => hp) hpack hexit
  have hseq' :
      cpsTripleWithin (nFree26EmptyToRet front.nSteps listLen) E ret teerLinkedField0
        ((.x1 ↦ᵣ ret) ** (.x2 ↦ᵣ spVal) **
          stackFree spVal nTeerStackWithListCount **
          (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
          (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) ** (.x20 ↦ᵣ s.s4) **
          (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) ** (.x23 ↦ᵣ s.s7) **
          (.x24 ↦ᵣ s.s8) ** (.x25 ↦ᵣ s.s9) ** (.x26 ↦ᵣ s.s10) **
          (.x27 ↦ᵣ s.s11) **
          (.x10 ↦ᵣ loadPtr) ** (.x11 ↦ᵣ lenW) **
          (.x12 ↦ᵣ balPtr) ** (.x13 ↦ᵣ balLenW) **
          (.x14 ↦ᵣ chainIdW) ** (.x15 ↦ᵣ baiW) **
          bytesRegion regionBase bs ** bytesRegion balPtr balBytes **
          teerScratchOwn **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x16 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
          regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)))
        (fun hp =>
          ∃ (refund _t0Old _t1Old baiW' : Word),
            ((((.x10 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ ret) ** (.x2 ↦ᵣ spVal) **
                (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
                (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) **
                (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) **
                (.x23 ↦ᵣ s.s7) ** (.x24 ↦ᵣ s.s8) ** (.x25 ↦ᵣ s.s9) **
                (.x26 ↦ᵣ s.s10) ** (.x27 ↦ᵣ s.s11) **
                frameSlotsSaved teerEpiFrame spC (teerSavedVals s) **
                (.x11 ↦ᵣ refund) ** (.x5 ↦ᵣ RolledBackAddr) **
                (.x6 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
                (RegularRefundAddr ↦ₘ refund) **
                memOwn WouldbeStateAddr ** memOwn WouldbeRegularAddr **
                (RolledBackAddr ↦ₘ (0 : Word))) **
                teerEmptyAuthExitFrame baiW' spVal spC regionBase bs balBytes balPtr) **
              stackFree spC 6) hp) := by
    dsimp only [nFree26EmptyToRet, nFree26EmptyToExitPack]
    exact hseq
  exact hseq'

/-- free26 → ExitPack under hrun free20→PostEx packaging (no structure).
    Residual: supply `hrun := teerAuthContent_applied ...` + pure specialize
    ∃ next,lenK,oldCount → front fields (content=next-lenK, etc.). -/
theorem teerEmptyAuth_free26_to_exitPack_of_hrun
    {n : Nat}
    (ret spVal spC regionBase loadPtr lenW balPtr balLenW chainIdW baiW : Word)
    (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : Word)
    (s : TeerSaved)
    (bs balBytes : List (BitVec 8))
    (hspC : spC = spVal + signExtend12 (-160 : BitVec 12))
    (innerVal endL endW cursorV : Word) (srcOffA9 : Nat)
    (hrun : cpsTripleWithin n E AtListCount teerLinkedCount
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
      (teerAuthContentAppliedPostEx spVal spC loadPtr lenW balPtr balLenW chainIdW
        s7 cursorV endW s11 s innerVal endL regionBase bs balBytes srcOffA9)) :
    cpsTripleWithin n E AtListCount teerLinkedField0
      (stackFree spVal nTeerStackWithListCount **
        teerAuthContentAppliedEntryRest ret spVal loadPtr lenW balPtr balLenW
          chainIdW baiW s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
          regionBase bs balBytes)
      (fun h =>
        ∃ (next lenK oldCount : Word),
          teerAuthContentBridgePre spVal spC LinkAuthWalkNext9 loadPtr lenW
            balPtr balLenW chainIdW (next - lenK) lenK s7 cursorV endW s11 s
            innerVal oldCount regionBase bs balBytes h) :=
  teerAuthContent_free26_to_bridgePre_field0 ret spVal spC loadPtr lenW
    balPtr balLenW chainIdW baiW s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    regionBase bs balBytes hspC s innerVal endL endW cursorV srcOffA9 hrun

/-- Specialize ∃ BridgePre post to fixed content/listLenW/oldCount under pure eqs.
    Residual pure from applied: content = next−lenK, listLenW = lenK. -/
theorem teerAuthContentBridgePre_exists_to_fixed
    (spVal spC loadPtr lenW balPtr balLenW chainIdW : Word)
    (s7Old cursorV endW s11 : Word) (s : TeerSaved) (innerVal : Word)
    (regionBase : Word) (bs balBytes : List (BitVec 8))
    (content listLenW oldCount : Word)
    (hspecialize : ∀ (next lenK oc : Word) h,
      teerAuthContentBridgePre spVal spC LinkAuthWalkNext9 loadPtr lenW
          balPtr balLenW chainIdW (next - lenK) lenK s7Old cursorV endW s11 s
          innerVal oc regionBase bs balBytes h →
        next - lenK = content ∧ lenK = listLenW ∧ oc = oldCount) :
    ∀ h,
      (∃ (next lenK oc : Word),
        teerAuthContentBridgePre spVal spC LinkAuthWalkNext9 loadPtr lenW
          balPtr balLenW chainIdW (next - lenK) lenK s7Old cursorV endW s11 s
          innerVal oc regionBase bs balBytes h) →
      teerAuthContentBridgePre spVal spC LinkAuthWalkNext9 loadPtr lenW
        balPtr balLenW chainIdW content listLenW s7Old cursorV endW s11 s
        innerVal oldCount regionBase bs balBytes h := by
  intro h ⟨next, lenK, oc, hBr⟩
  obtain ⟨hc, hl, ho⟩ := hspecialize next lenK oc h hBr
  subst ho
  have hc' : next - listLenW = content := by simpa [hl] using hc
  rw [hl, hc'] at hBr
  exact hBr

/-- free26 → fixed BridgePre under hrun + pure specialize residual. -/
theorem teerEmptyAuth_free26_to_bridgePre_fixed
    {n : Nat}
    (ret spVal spC regionBase loadPtr lenW balPtr balLenW chainIdW baiW : Word)
    (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : Word)
    (s : TeerSaved)
    (bs balBytes : List (BitVec 8))
    (hspC : spC = spVal + signExtend12 (-160 : BitVec 12))
    (innerVal endL endW cursorV : Word) (srcOffA9 : Nat)
    (content listLenW oldCount : Word)
    (hrun : cpsTripleWithin n E AtListCount teerLinkedCount
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
      (teerAuthContentAppliedPostEx spVal spC loadPtr lenW balPtr balLenW chainIdW
        s7 cursorV endW s11 s innerVal endL regionBase bs balBytes srcOffA9))
    (hspecialize : ∀ (next lenK oc : Word) h,
      teerAuthContentBridgePre spVal spC LinkAuthWalkNext9 loadPtr lenW
          balPtr balLenW chainIdW (next - lenK) lenK s7 cursorV endW s11 s
          innerVal oc regionBase bs balBytes h →
        next - lenK = content ∧ lenK = listLenW ∧ oc = oldCount) :
    cpsTripleWithin n E AtListCount teerLinkedField0
      (stackFree spVal nTeerStackWithListCount **
        teerAuthContentAppliedEntryRest ret spVal loadPtr lenW balPtr balLenW
          chainIdW baiW s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
          regionBase bs balBytes)
      (teerAuthContentBridgePre spVal spC LinkAuthWalkNext9 loadPtr lenW
        balPtr balLenW chainIdW content listLenW s7 cursorV endW s11 s
        innerVal oldCount regionBase bs balBytes) := by
  have hex :=
    teerEmptyAuth_free26_to_exitPack_of_hrun ret spVal spC regionBase loadPtr lenW
      balPtr balLenW chainIdW baiW s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
      s bs balBytes hspC innerVal endL endW cursorV srcOffA9 hrun
  exact cpsTripleWithin_weaken (fun _ hp => hp)
    (teerAuthContentBridgePre_exists_to_fixed spVal spC loadPtr lenW balPtr balLenW
      chainIdW s7 cursorV endW s11 s innerVal regionBase bs balBytes
      content listLenW oldCount hspecialize)
    hex

/-- Fill FrontToBridge from free26→fixed BridgePre run (witnesses as fields). -/
def teerFrontAuthContentToBridgeAssumed_of_fixed
    (nSteps : Nat) (content listLenW oldCount : Word)
    (run :
      ∀ (ret spVal spC regionBase loadPtr lenW balPtr balLenW chainIdW baiW : Word)
        (s : TeerSaved)
        (bs balBytes : List (BitVec 8)) (off len : Nat)
        (old1 s7Old cursorV endW s11 innerVal : Word),
        (ret &&& ~~~(1 : Word)) = ret →
        balPtr ≠ 0 →
        loadPtr = regionBase + BitVec.ofNat 64 off →
        off + len ≤ bs.length →
        spC = spVal + signExtend12 (-160 : BitVec 12) →
        s.ra = ret →
        cpsTripleWithin nSteps E AtListCount teerLinkedField0
          ((.x1 ↦ᵣ ret) ** (.x2 ↦ᵣ spVal) **
            stackFree spVal nTeerStackWithListCount **
            (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
            (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) ** (.x20 ↦ᵣ s.s4) **
            (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) ** (.x23 ↦ᵣ s.s7) **
            (.x24 ↦ᵣ s.s8) ** (.x25 ↦ᵣ s.s9) ** (.x26 ↦ᵣ s.s10) **
            (.x27 ↦ᵣ s.s11) **
            (.x10 ↦ᵣ loadPtr) ** (.x11 ↦ᵣ lenW) **
            (.x12 ↦ᵣ balPtr) ** (.x13 ↦ᵣ balLenW) **
            (.x14 ↦ᵣ chainIdW) ** (.x15 ↦ᵣ baiW) **
            bytesRegion regionBase bs ** bytesRegion balPtr balBytes **
            teerScratchOwn **
            regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
            regOwn .x16 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
            regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)))
          (teerAuthContentBridgePre spVal spC old1 loadPtr lenW balPtr balLenW
            chainIdW content listLenW s7Old cursorV endW s11 s innerVal oldCount
            regionBase bs balBytes)) :
    TeerFrontAuthContentToBridgeAssumed where
  nSteps := nSteps
  content := content
  listLenW := listLenW
  oldCount := oldCount
  run := run

#print axioms teerEmptyAuth_free26_to_exitPack
#print axioms teerEmptyAuth_free26_toRet
#print axioms teerEmptyAuth_free26_to_exitPack_of_hrun
#print axioms teerAuthContentBridgePre_exists_to_fixed
#print axioms teerEmptyAuth_free26_to_bridgePre_fixed


/-- free26 → ExitPack under hrun free20→PostEx + pure specialize + empty list_count mid.
    Avoids `TeerFrontAuthContentToBridgeAssumed` structure: witnesses are theorem params.
    Residual: supply `hrun := teerAuthContent_applied ...` (post matches PostEx);
    pure specialize content=next−lenK; hrolled0. -/
theorem teerEmptyAuth_free26_to_exitPack_of_hrun_fixed
    {n : Nat}
    (asm : TeerListCountAuthLoopAssumed teerLinkedCount)
    (ret spVal spC regionBase loadPtr lenW balPtr balLenW chainIdW baiW : Word)
    (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : Word)
    (s : TeerSaved)
    (bs balBytes : List (BitVec 8))
    (hspC : spC = spVal + signExtend12 (-160 : BitVec 12))
    (innerVal endL endW cursorV : Word) (srcOffA9 : Nat)
    (content listLenW oldCount : Word)
    (newSp listBase : Word) (listLen : Nat) (bytes : List (BitVec 8))
    (s0' s1' s2' s3' v24 : Word)
    (hoff : (0 : Nat) < bytes.length)
    (hbase : listBase = regionBase) (hbytes : bytes = bs)
    (hcontent : content = listBase)
    (hs0 : s0' = loadPtr) (hs1 : s1' = lenW) (hs2 : s2' = balPtr) (hs3 : s3' = balLenW)
    (hv24 : v24 = cursorV)
    (hs0s : s0' = s.s0) (hs1s : s1' = s.s1) (hs2s : s2' = s.s2) (hs3s : s3' = s.s3)
    (hs4 : chainIdW = s.s4) (hs9 : endW = s.s9) (hs11 : s11 = s.s11)
    (hlistLenW : listLenW = BitVec.ofNat 64 listLen)
    (hsalign : listBase.toNat % 8 = 0)
    (hslack : listLen + 9 ≤ bytes.length)
    (hover : listBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true)
    (hnewSp : newSp = spC + signExtend12 (-48 : BitVec 12))
    (hretLink : (LinkListCount &&& ~~~(1 : Word)) = LinkListCount)
    (hsuccess : Success bytes listBase listLen 0)
    (hspe : ListCountResultSpecialize bytes listBase listLen 0 (0 : Word))
    (hlen : listLenW ≠ (0 : Word))
    (hoverOff : listBase.toNat + 0 < 2 ^ 64)
    (hvalidOff : isValidByteAccess (listBase + BitVec.ofNat 64 0) = true)
    (h_ge : ¬ BitVec.ult ((bytes[0]'hoff).zeroExtend 64) (0xc0 : Word) = true)
    (h_hi : BitVec.ult ((bytes[0]'hoff).zeroExtend 64) (0xf8 : Word) = true)
    (h_exact : (listBase + BitVec.ofNat 64 0) +
        (((bytes[0]'hoff).zeroExtend 64 - (0xc0 : Word)) +
          signExtend12 (1 : BitVec 12)) =
      (listBase + BitVec.ofNat 64 0) + listLenW)
    (hrolled0 : ∀ (refund rolledVal : Word) h,
      ((teerListCountAuthLoopPost spC listBase AuthCountAddr s0' s1' s2' s3'
          (0 : Word) bytes 0 listLenW) **
        teerAuthLoopEmptyAmbientMemIs spVal spC balPtr chainIdW s balBytes
          innerVal endW s11 refund rolledVal) h →
      rolledVal = (0 : Word))
    (hrun : cpsTripleWithin n E AtListCount teerLinkedCount
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
      (teerAuthContentAppliedPostEx spVal spC loadPtr lenW balPtr balLenW chainIdW
        s7 cursorV endW s11 s innerVal endL regionBase bs balBytes srcOffA9))
    (hspecialize : ∀ (next lenK oc : Word) h,
      teerAuthContentBridgePre spVal spC LinkAuthWalkNext9 loadPtr lenW
          balPtr balLenW chainIdW (next - lenK) lenK s7 cursorV endW s11 s
          innerVal oc regionBase bs balBytes h →
        next - lenK = content ∧ lenK = listLenW ∧ oc = oldCount) :
    cpsTripleWithin (n + nListCountAuthLoopStart listLen) E AfterAuthLoopLi
      teerLinkedField0
      (stackFree spVal nTeerStackWithListCount **
        teerAuthContentAppliedEntryRest ret spVal loadPtr lenW balPtr balLenW
          chainIdW baiW s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
          regionBase bs balBytes)
      (fun hp =>
        ∃ (refund t0Old t1Old baiW' : Word),
          teerAuthLoopEmptyExitPack spVal spC s
            (teerAuthLoopEmptyWalkCur listBase)
            (teerAuthLoopEmptyWalkEnd listBase listLenW)
            refund
            (teerAuthLoopEmptyWalkCur listBase)
            (teerAuthLoopEmptyWalkEnd listBase listLenW)
            t0Old t1Old baiW'
            regionBase bs balBytes balPtr hp) := by
  have hBr :=
    teerEmptyAuth_free26_to_bridgePre_fixed ret spVal spC regionBase loadPtr lenW
      balPtr balLenW chainIdW baiW s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
      s bs balBytes hspC innerVal endL endW cursorV srcOffA9 content listLenW oldCount
      hrun hspecialize
  have hmid :=
    teerBridgePre_to_exitPack_empty asm spVal spC newSp listBase listLenW oldCount
      s0' s1' s2' s3' bytes listLen LinkAuthWalkNext9 s7 v24 balPtr chainIdW baiW s
      balBytes innerVal cursorV endW s11 loadPtr lenW balLenW regionBase bs content
      hoff hbase hbytes hcontent hs0 hs1 hs2 hs3 hv24 hs0s hs1s hs2s hs3s hs4 hs9 hs11
      hlistLenW hsalign hslack hover hvalid hnewSp hretLink hsuccess hspe hlen
      hoverOff hvalidOff h_ge h_hi h_exact hrolled0
  have hseq :=
    cpsTripleWithin_seq_perm_same_cr (fun _ hp => hp) hBr hmid
  have hseq' :
      cpsTripleWithin (n + nListCountAuthLoopStart listLen) E AfterAuthLoopLi
        teerLinkedField0
        (stackFree spVal nTeerStackWithListCount **
          teerAuthContentAppliedEntryRest ret spVal loadPtr lenW balPtr balLenW
            chainIdW baiW s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
            regionBase bs balBytes)
        (fun hp =>
          ∃ (refund t0Old t1Old baiW' : Word),
            teerAuthLoopEmptyExitPack spVal spC s
              (teerAuthLoopEmptyWalkCur listBase)
              (teerAuthLoopEmptyWalkEnd listBase listLenW)
              refund
              (teerAuthLoopEmptyWalkCur listBase)
              (teerAuthLoopEmptyWalkEnd listBase listLenW)
              t0Old t1Old baiW'
              regionBase bs balBytes balPtr hp) := by
    -- nSteps: free26_to_bridgePre_fixed uses n; mid uses nListCountAuthLoopStart
    simpa using hseq
  exact hseq'

/-- free26 → ret under hrun + specialize + empty mid (no Front structure). -/
theorem teerEmptyAuth_free26_toRet_of_hrun_fixed
    {n : Nat}
    (asm : TeerListCountAuthLoopAssumed teerLinkedCount)
    (ret spVal spC regionBase loadPtr lenW balPtr balLenW chainIdW baiW : Word)
    (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : Word)
    (s : TeerSaved)
    (bs balBytes : List (BitVec 8))
    (hspC : spC = spVal + signExtend12 (-160 : BitVec 12))
    (innerVal endL endW cursorV : Word) (srcOffA9 : Nat)
    (content listLenW oldCount : Word)
    (newSp listBase : Word) (listLen : Nat) (bytes : List (BitVec 8))
    (s0' s1' s2' s3' v24 : Word)
    (hoff : (0 : Nat) < bytes.length)
    (hbase : listBase = regionBase) (hbytes : bytes = bs)
    (hcontent : content = listBase)
    (hs0 : s0' = loadPtr) (hs1 : s1' = lenW) (hs2 : s2' = balPtr) (hs3 : s3' = balLenW)
    (hv24 : v24 = cursorV)
    (hs0s : s0' = s.s0) (hs1s : s1' = s.s1) (hs2s : s2' = s.s2) (hs3s : s3' = s.s3)
    (hs4 : chainIdW = s.s4) (hs9 : endW = s.s9) (hs11 : s11 = s.s11)
    (hlistLenW : listLenW = BitVec.ofNat 64 listLen)
    (hsalign : listBase.toNat % 8 = 0)
    (hslack : listLen + 9 ≤ bytes.length)
    (hover : listBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true)
    (hnewSp : newSp = spC + signExtend12 (-48 : BitVec 12))
    (hretLink : (LinkListCount &&& ~~~(1 : Word)) = LinkListCount)
    (hsuccess : Success bytes listBase listLen 0)
    (hspe : ListCountResultSpecialize bytes listBase listLen 0 (0 : Word))
    (hlen : listLenW ≠ (0 : Word))
    (hoverOff : listBase.toNat + 0 < 2 ^ 64)
    (hvalidOff : isValidByteAccess (listBase + BitVec.ofNat 64 0) = true)
    (h_ge : ¬ BitVec.ult ((bytes[0]'hoff).zeroExtend 64) (0xc0 : Word) = true)
    (h_hi : BitVec.ult ((bytes[0]'hoff).zeroExtend 64) (0xf8 : Word) = true)
    (h_exact : (listBase + BitVec.ofNat 64 0) +
        (((bytes[0]'hoff).zeroExtend 64 - (0xc0 : Word)) +
          signExtend12 (1 : BitVec 12)) =
      (listBase + BitVec.ofNat 64 0) + listLenW)
    (hrolled0 : ∀ (refund rolledVal : Word) h,
      ((teerListCountAuthLoopPost spC listBase AuthCountAddr s0' s1' s2' s3'
          (0 : Word) bytes 0 listLenW) **
        teerAuthLoopEmptyAmbientMemIs spVal spC balPtr chainIdW s balBytes
          innerVal endW s11 refund rolledVal) h →
      rolledVal = (0 : Word))
    (hret : (ret &&& ~~~(1 : Word)) = ret)
    (hra : s.ra = ret)
    (hrun : cpsTripleWithin n E AtListCount teerLinkedCount
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
      (teerAuthContentAppliedPostEx spVal spC loadPtr lenW balPtr balLenW chainIdW
        s7 cursorV endW s11 s innerVal endL regionBase bs balBytes srcOffA9))
    (hspecialize : ∀ (next lenK oc : Word) h,
      teerAuthContentBridgePre spVal spC LinkAuthWalkNext9 loadPtr lenW
          balPtr balLenW chainIdW (next - lenK) lenK s7 cursorV endW s11 s
          innerVal oc regionBase bs balBytes h →
        next - lenK = content ∧ lenK = listLenW ∧ oc = oldCount) :
    cpsTripleWithin (n + nListCountAuthLoopStart listLen + 30) E ret
      teerLinkedField0
      (stackFree spVal nTeerStackWithListCount **
        teerAuthContentAppliedEntryRest ret spVal loadPtr lenW balPtr balLenW
          chainIdW baiW s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
          regionBase bs balBytes)
      (fun hp =>
        ∃ (refund _t0Old _t1Old baiW' : Word),
          ((((.x10 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ ret) ** (.x2 ↦ᵣ spVal) **
              (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
              (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) **
              (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) **
              (.x23 ↦ᵣ s.s7) ** (.x24 ↦ᵣ s.s8) ** (.x25 ↦ᵣ s.s9) **
              (.x26 ↦ᵣ s.s10) ** (.x27 ↦ᵣ s.s11) **
              frameSlotsSaved teerEpiFrame spC (teerSavedVals s) **
              (.x11 ↦ᵣ refund) ** (.x5 ↦ᵣ RolledBackAddr) **
              (.x6 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
              (RegularRefundAddr ↦ₘ refund) **
              memOwn WouldbeStateAddr ** memOwn WouldbeRegularAddr **
              (RolledBackAddr ↦ₘ (0 : Word))) **
              teerEmptyAuthExitFrame baiW' spVal spC regionBase bs balBytes balPtr) **
            stackFree spC 6) hp) := by
  have hpack :=
    teerEmptyAuth_free26_to_exitPack_of_hrun_fixed asm ret spVal spC regionBase
      loadPtr lenW balPtr balLenW chainIdW baiW s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
      s bs balBytes hspC innerVal endL endW cursorV srcOffA9 content listLenW oldCount
      newSp listBase listLen bytes s0' s1' s2' s3' v24 hoff hbase hbytes hcontent
      hs0 hs1 hs2 hs3 hv24 hs0s hs1s hs2s hs3s hs4 hs9 hs11 hlistLenW hsalign hslack
      hover hvalid hnewSp hretLink hsuccess hspe hlen hoverOff hvalidOff h_ge h_hi
      h_exact hrolled0 hrun hspecialize
  have hexit :
      cpsTripleWithin 30 AfterAuthLoopLi ret teerLinkedField0
        (fun hp =>
          ∃ (refund t0Old t1Old baiW' : Word),
            teerAuthLoopEmptyExitPack spVal spC s
              (teerAuthLoopEmptyWalkCur listBase)
              (teerAuthLoopEmptyWalkEnd listBase listLenW)
              refund
              (teerAuthLoopEmptyWalkCur listBase)
              (teerAuthLoopEmptyWalkEnd listBase listLenW)
              t0Old t1Old baiW'
              regionBase bs balBytes balPtr hp)
        (fun hp =>
          ∃ (refund _t0Old _t1Old baiW' : Word),
            ((((.x10 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ ret) ** (.x2 ↦ᵣ spVal) **
                (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
                (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) **
                (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) **
                (.x23 ↦ᵣ s.s7) ** (.x24 ↦ᵣ s.s8) ** (.x25 ↦ᵣ s.s9) **
                (.x26 ↦ᵣ s.s10) ** (.x27 ↦ᵣ s.s11) **
                frameSlotsSaved teerEpiFrame spC (teerSavedVals s) **
                (.x11 ↦ᵣ refund) ** (.x5 ↦ᵣ RolledBackAddr) **
                (.x6 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
                (RegularRefundAddr ↦ₘ refund) **
                memOwn WouldbeStateAddr ** memOwn WouldbeRegularAddr **
                (RolledBackAddr ↦ₘ (0 : Word))) **
                teerEmptyAuthExitFrame baiW' spVal spC regionBase bs balBytes balPtr) **
              stackFree spC 6) hp) := by
    intro R hR st hcr hPR hpc
    obtain ⟨h0, hcompat, h1, h2, hd, hu, ⟨refund, t0, t1, bai', hPack⟩, hR2⟩ := hPR
    have hleaf :=
      teerAuthLoopEmptyExitPack_toRet spVal spC s
        (teerAuthLoopEmptyWalkCur listBase)
        (teerAuthLoopEmptyWalkEnd listBase listLenW)
        (teerAuthLoopEmptyWalkCur listBase)
        (teerAuthLoopEmptyWalkEnd listBase listLenW)
        t0 t1 refund bai' regionBase bs balBytes balPtr hspC
        (by simpa [hra] using hret)
    have hleaf' :
        cpsTripleWithin 30 AfterAuthLoopLi ret teerLinkedField0
          (teerAuthLoopEmptyExitPack spVal spC s
            (teerAuthLoopEmptyWalkCur listBase)
            (teerAuthLoopEmptyWalkEnd listBase listLenW)
            refund
            (teerAuthLoopEmptyWalkCur listBase)
            (teerAuthLoopEmptyWalkEnd listBase listLenW)
            t0 t1 bai' regionBase bs balBytes balPtr)
          (fun hp =>
            ((((.x10 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ ret) ** (.x2 ↦ᵣ spVal) **
                (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
                (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) **
                (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) **
                (.x23 ↦ᵣ s.s7) ** (.x24 ↦ᵣ s.s8) ** (.x25 ↦ᵣ s.s9) **
                (.x26 ↦ᵣ s.s10) ** (.x27 ↦ᵣ s.s11) **
                frameSlotsSaved teerEpiFrame spC (teerSavedVals s) **
                (.x11 ↦ᵣ refund) ** (.x5 ↦ᵣ RolledBackAddr) **
                (.x6 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
                (RegularRefundAddr ↦ₘ refund) **
                memOwn WouldbeStateAddr ** memOwn WouldbeRegularAddr **
                (RolledBackAddr ↦ₘ (0 : Word))) **
                teerEmptyAuthExitFrame bai' spVal spC regionBase bs balBytes balPtr) **
              stackFree spC 6) hp) := by
      simpa [hra] using hleaf
    obtain ⟨k, hk, st', hexec, hpc', hQ⟩ :=
      hleaf' R hR st hcr ⟨h0, hcompat, h1, h2, hd, hu, hPack, hR2⟩ hpc
    refine ⟨k, hk, st', hexec, hpc', ?_⟩
    obtain ⟨h0', hcompat', h1', h2', hd', hu', hRet, hR'⟩ := hQ
    exact ⟨h0', hcompat', h1', h2', hd', hu', ⟨refund, t0, t1, bai', hRet⟩, hR'⟩
  have hseq :=
    cpsTripleWithin_seq_perm_same_cr (fun _ hp => hp) hpack hexit
  have hseq' :
      cpsTripleWithin (n + nListCountAuthLoopStart listLen + 30) E ret
        teerLinkedField0
        (stackFree spVal nTeerStackWithListCount **
          teerAuthContentAppliedEntryRest ret spVal loadPtr lenW balPtr balLenW
            chainIdW baiW s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
            regionBase bs balBytes)
        (fun hp =>
          ∃ (refund _t0Old _t1Old baiW' : Word),
            ((((.x10 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ ret) ** (.x2 ↦ᵣ spVal) **
                (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
                (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) **
                (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) **
                (.x23 ↦ᵣ s.s7) ** (.x24 ↦ᵣ s.s8) ** (.x25 ↦ᵣ s.s9) **
                (.x26 ↦ᵣ s.s10) ** (.x27 ↦ᵣ s.s11) **
                frameSlotsSaved teerEpiFrame spC (teerSavedVals s) **
                (.x11 ↦ᵣ refund) ** (.x5 ↦ᵣ RolledBackAddr) **
                (.x6 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
                (RegularRefundAddr ↦ₘ refund) **
                memOwn WouldbeStateAddr ** memOwn WouldbeRegularAddr **
                (RolledBackAddr ↦ₘ (0 : Word))) **
                teerEmptyAuthExitFrame baiW' spVal spC regionBase bs balBytes balPtr) **
              stackFree spC 6) hp) := by
    simpa using hseq
  exact hseq'

#print axioms teerEmptyAuth_free26_to_exitPack_of_hrun_fixed
#print axioms teerEmptyAuth_free26_toRet_of_hrun_fixed

/-- `Word` round-trip: `ofNat (toNat v) = v`. -/
private theorem teerWord_ofNat_toNat (v : Word) :
    BitVec.ofNat 64 v.toNat = v := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt v.isLt

/-- Pick BridgePre witnesses as content/listLenW/oldCount (no specialize residual).
    Exists form `(next−lenK, lenK, oc)` → named content form. -/
theorem teerAuthContentBridgePre_exists_pick
    (spVal spC loadPtr lenW balPtr balLenW chainIdW : Word)
    (s7Old cursorV endW s11 : Word) (s : TeerSaved) (innerVal : Word)
    (regionBase : Word) (bs balBytes : List (BitVec 8)) :
    ∀ h,
      (∃ (next lenK oc : Word),
        teerAuthContentBridgePre spVal spC LinkAuthWalkNext9 loadPtr lenW
          balPtr balLenW chainIdW (next - lenK) lenK s7Old cursorV endW s11 s
          innerVal oc regionBase bs balBytes h) →
      ∃ (content listLenW oldCount : Word),
        teerAuthContentBridgePre spVal spC LinkAuthWalkNext9 loadPtr lenW
          balPtr balLenW chainIdW content listLenW s7Old cursorV endW s11 s
          innerVal oldCount regionBase bs balBytes h := by
  intro h ⟨next, lenK, oc, hBr⟩
  exact ⟨next - lenK, lenK, oc, hBr⟩

/-- free26 → ∃ content listLenW oldCount BridgePre under hrun (pick, no specialize). -/
theorem teerEmptyAuth_free26_to_bridgePre_pick
    {n : Nat}
    (ret spVal spC regionBase loadPtr lenW balPtr balLenW chainIdW baiW : Word)
    (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : Word)
    (s : TeerSaved)
    (bs balBytes : List (BitVec 8))
    (hspC : spC = spVal + signExtend12 (-160 : BitVec 12))
    (innerVal endL endW cursorV : Word) (srcOffA9 : Nat)
    (hrun : cpsTripleWithin n E AtListCount teerLinkedCount
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
      (teerAuthContentAppliedPostEx spVal spC loadPtr lenW balPtr balLenW chainIdW
        s7 cursorV endW s11 s innerVal endL regionBase bs balBytes srcOffA9)) :
    cpsTripleWithin n E AtListCount teerLinkedField0
      (stackFree spVal nTeerStackWithListCount **
        teerAuthContentAppliedEntryRest ret spVal loadPtr lenW balPtr balLenW
          chainIdW baiW s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
          regionBase bs balBytes)
      (fun h =>
        ∃ (content listLenW oldCount : Word),
          teerAuthContentBridgePre spVal spC LinkAuthWalkNext9 loadPtr lenW
            balPtr balLenW chainIdW content listLenW s7 cursorV endW s11 s
            innerVal oldCount regionBase bs balBytes h) := by
  have hex :=
    teerEmptyAuth_free26_to_exitPack_of_hrun ret spVal spC regionBase loadPtr lenW
      balPtr balLenW chainIdW baiW s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
      s bs balBytes hspC innerVal endL endW cursorV srcOffA9 hrun
  exact cpsTripleWithin_weaken (fun _ hp => hp)
    (teerAuthContentBridgePre_exists_pick spVal spC loadPtr lenW balPtr balLenW
      chainIdW s7 cursorV endW s11 s innerVal regionBase bs balBytes)
    hex

/-- Fill FrontToBridge from exists-pick BridgePre run.
    Witnesses are the picked content/listLenW/oldCount (no separate specialize).
    Caller supplies `run` after `free26_to_bridgePre_pick` + mid with those fields. -/
def teerFrontAuthContentToBridgeAssumed_of_pick
    (nSteps : Nat) (content listLenW oldCount : Word)
    (run :
      ∀ (ret spVal spC regionBase loadPtr lenW balPtr balLenW chainIdW baiW : Word)
        (s : TeerSaved)
        (bs balBytes : List (BitVec 8)) (off len : Nat)
        (old1 s7Old cursorV endW s11 innerVal : Word),
        (ret &&& ~~~(1 : Word)) = ret →
        balPtr ≠ 0 →
        loadPtr = regionBase + BitVec.ofNat 64 off →
        off + len ≤ bs.length →
        spC = spVal + signExtend12 (-160 : BitVec 12) →
        s.ra = ret →
        cpsTripleWithin nSteps E AtListCount teerLinkedField0
          ((.x1 ↦ᵣ ret) ** (.x2 ↦ᵣ spVal) **
            stackFree spVal nTeerStackWithListCount **
            (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
            (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) ** (.x20 ↦ᵣ s.s4) **
            (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) ** (.x23 ↦ᵣ s.s7) **
            (.x24 ↦ᵣ s.s8) ** (.x25 ↦ᵣ s.s9) ** (.x26 ↦ᵣ s.s10) **
            (.x27 ↦ᵣ s.s11) **
            (.x10 ↦ᵣ loadPtr) ** (.x11 ↦ᵣ lenW) **
            (.x12 ↦ᵣ balPtr) ** (.x13 ↦ᵣ balLenW) **
            (.x14 ↦ᵣ chainIdW) ** (.x15 ↦ᵣ baiW) **
            bytesRegion regionBase bs ** bytesRegion balPtr balBytes **
            teerScratchOwn **
            regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
            regOwn .x16 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
            regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)))
          (teerAuthContentBridgePre spVal spC old1 loadPtr lenW balPtr balLenW
            chainIdW content listLenW s7Old cursorV endW s11 s innerVal oldCount
            regionBase bs balBytes)) :
    TeerFrontAuthContentToBridgeAssumed where
  nSteps := nSteps
  content := content
  listLenW := listLenW
  oldCount := oldCount
  run := run

#print axioms teerAuthContentBridgePre_exists_pick
#print axioms teerEmptyAuth_free26_to_bridgePre_pick
#print axioms teerWord_ofNat_toNat


/-! ## Heap uniqueness (regIs / memIs) -/

/-- Register value is unique on a partial heap. -/
theorem teerRegIs_unique {r : Reg} {v1 v2 : Word} {h : PartialState} :
    (r ↦ᵣ v1) h → (r ↦ᵣ v2) h → v1 = v2 := by
  intro h1 h2
  simp only [regIs] at h1 h2
  -- h1: h = singletonReg r v1; h2: h = singletonReg r v2
  have heq : PartialState.singletonReg r v1 = PartialState.singletonReg r v2 :=
    h1.symm.trans h2
  have hv := congrArg (fun p : PartialState => p.regs r) heq
  simp only [PartialState.singletonReg, beq_self_eq_true, ↓reduceIte] at hv
  exact Option.some_injective _ hv

/-- Memory cell value is unique on a partial heap. -/
theorem teerMemIs_unique {a v1 v2 : Word} {h : PartialState} :
    (a ↦ₘ v1) h → (a ↦ₘ v2) h → v1 = v2 := by
  intro h1 h2
  simp only [memIs] at h1 h2
  obtain ⟨heq1, _⟩ := h1
  obtain ⟨heq2, _⟩ := h2
  -- heq1: h = singletonMem a v1; heq2: h = singletonMem a v2
  have heq : PartialState.singletonMem a v1 = PartialState.singletonMem a v2 :=
    heq1.symm.trans heq2
  have hv := congrArg (fun p : PartialState => p.mem a) heq
  simp only [PartialState.singletonMem, beq_self_eq_true, ↓reduceIte] at hv
  exact Option.some_injective _ hv

/-- Rolled cell value 0 is unique: peel + `↦ₘ 0` forces `rolledVal = 0`. -/
theorem teerRolledVal_eq_zero_of_memIs0 {rolledVal : Word} {h : PartialState}
    (h0 : (RolledBackAddr ↦ₘ (0 : Word)) h)
    (hv : (RolledBackAddr ↦ₘ rolledVal) h) :
    rolledVal = (0 : Word) :=
  (teerMemIs_unique h0 hv).symm

/-- holdsFor form: machine state with rolled ↦ 0 forces peeled value 0. -/
theorem teerRolledVal_eq_zero_of_holdsFor
    {rolledVal : Word} {s : MachineState}
    (h0 : (RolledBackAddr ↦ₘ (0 : Word)).holdsFor s)
    (hv : (RolledBackAddr ↦ₘ rolledVal).holdsFor s) :
    rolledVal = (0 : Word) := by
  have h0' := holdsFor_memIs.mp h0
  have hv' := holdsFor_memIs.mp hv
  exact hv'.1.symm.trans h0'.1

#print axioms teerRegIs_unique
#print axioms teerMemIs_unique
#print axioms teerRolledVal_eq_zero_of_memIs0
#print axioms teerRolledVal_eq_zero_of_holdsFor


/-! ## hrolled0 packaging -/

/-- Named hyp: empty path preserves ScratchZero `teer_rolled_back = 0` through
    list_count..AfterAuthLoopLi. `memOwn` discards the value after ScratchZero;
    this re-pins it. Free when ambient already carries `RolledBack ↦ₘ 0`
    (`teerRolledVal_eq_zero_of_memIs0`). -/
structure TeerRolledZeroAssumed where
  holds :
    ∀ (spVal spC listBase listLenW s0 s1 s2 s3 : Word)
      (bytes : List (BitVec 8))
      (balPtr chainIdW _baiW : Word)
      (s : TeerSaved) (balBytes : List (BitVec 8))
      (innerVal _cursorV endW s11 : Word)
      (refund rolledVal : Word) (h : PartialState),
      ((teerListCountAuthLoopPost spC listBase AuthCountAddr s0 s1 s2 s3
          (0 : Word) bytes 0 listLenW) **
        teerAuthLoopEmptyAmbientMemIs spVal spC balPtr chainIdW s balBytes
          innerVal endW s11 refund rolledVal) h →
      rolledVal = (0 : Word)

/-- AmbientPost → Source under `TeerRolledZeroAssumed` (packages open `hrolled0`). -/
theorem teerAuthLoopEmptyAmbientPost_to_source_of_rolledZero
    (rz : TeerRolledZeroAssumed)
    (spVal spC listBase listLenW s0 s1 s2 s3 : Word)
    (bytes : List (BitVec 8))
    (balPtr chainIdW baiW : Word)
    (s : TeerSaved) (balBytes : List (BitVec 8))
    (innerVal cursorV endW s11 : Word) :
    ∀ h,
      teerAuthLoopEmptyAmbientPost spVal spC listBase listLenW s0 s1 s2 s3 bytes
        balPtr chainIdW baiW s balBytes innerVal cursorV endW s11 h →
      ∃ (refund : Word),
        teerAuthLoopEmptySource spVal spC listBase listLenW s0 s1 s2 s3 bytes
          balPtr chainIdW s balBytes innerVal endW s11 refund h :=
  teerAuthLoopEmptyAmbientPost_to_source spVal spC listBase listLenW s0 s1 s2 s3
    bytes balPtr chainIdW baiW s balBytes innerVal cursorV endW s11
    (fun refund rolledVal h hp =>
      rz.holds spVal spC listBase listLenW s0 s1 s2 s3 bytes balPtr chainIdW baiW
        s balBytes innerVal cursorV endW s11 refund rolledVal h hp)

/-- free26 Front residual structure: E free26 → AfterAuthLoopLi ExitPack.
    Identity nested-free path: requires `content = regionBase` (list at blob base).
    Inhabit via FrontToBridge + `TeerEmptyAuthFree26MidAssumed`
    (`teerFrontToAuthLoopAssumedFree26_of`). -/
structure TeerFrontToAuthLoopAssumedFree26 where
  nSteps : Nat
  hn : nSteps + 30 ≤ nTeerSteps
  content : Word
  listLenW : Word
  run :
    ∀ (ret spVal spC regionBase loadPtr lenW balPtr balLenW chainIdW baiW : Word)
      (s : TeerSaved)
      (bs balBytes : List (BitVec 8)) (off len : Nat)
      (old1 _s7Old _cursorV _endW _s11 _innerVal : Word),
      content = regionBase →
      old1 = LinkAuthWalkNext9 →
      (ret &&& ~~~(1 : Word)) = ret →
      balPtr ≠ 0 →
      loadPtr = regionBase + BitVec.ofNat 64 off →
      off + len ≤ bs.length →
      spC = spVal + signExtend12 (-160 : BitVec 12) →
      s.ra = ret →
      cpsTripleWithin nSteps E AfterAuthLoopLi teerLinkedField0
        ((.x1 ↦ᵣ ret) ** (.x2 ↦ᵣ spVal) **
          stackFree spVal nTeerStackWithListCount **
          (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
          (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) ** (.x20 ↦ᵣ s.s4) **
          (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) ** (.x23 ↦ᵣ s.s7) **
          (.x24 ↦ᵣ s.s8) ** (.x25 ↦ᵣ s.s9) ** (.x26 ↦ᵣ s.s10) **
          (.x27 ↦ᵣ s.s11) **
          (.x10 ↦ᵣ loadPtr) ** (.x11 ↦ᵣ lenW) **
          (.x12 ↦ᵣ balPtr) ** (.x13 ↦ᵣ balLenW) **
          (.x14 ↦ᵣ chainIdW) ** (.x15 ↦ᵣ baiW) **
          bytesRegion regionBase bs ** bytesRegion balPtr balBytes **
          teerScratchOwn **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x16 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
          regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)))
        (fun hp =>
          ∃ (refund t0Old t1Old baiW' : Word),
            teerAuthLoopEmptyExitPack spVal spC s
              (teerAuthLoopEmptyWalkCur content)
              (teerAuthLoopEmptyWalkEnd content listLenW)
              refund
              (teerAuthLoopEmptyWalkCur content)
              (teerAuthLoopEmptyWalkEnd content listLenW)
              t0Old t1Old baiW'
              regionBase bs balBytes balPtr hp)

/-- Residual empty-path mid domain for Free26 inhabit (identity listBase=content).
    Bundles list_count Success/guards + hrolled0 + s-reg wire equalities. -/
structure TeerEmptyAuthFree26MidAssumed where
  listLen : Nat
  asm : TeerListCountAuthLoopAssumed teerLinkedCount
  mid :
    ∀ (spVal spC regionBase loadPtr lenW balPtr balLenW chainIdW _baiW : Word)
      (s : TeerSaved) (bs balBytes : List (BitVec 8))
      (content listLenW _oldCount _s7Old cursorV endW s11 innerVal : Word),
      content = regionBase →
      listLenW = BitVec.ofNat 64 listLen →
      listLenW ≠ (0 : Word) →
      ∃ (newSp : Word) (bytes : List (BitVec 8)) (s0 s1 s2 s3 v24 : Word)
        (hoff : (0 : Nat) < bytes.length),
        bytes = bs ∧
        newSp = spC + signExtend12 (-48 : BitVec 12) ∧
        s0 = loadPtr ∧ s1 = lenW ∧ s2 = balPtr ∧ s3 = balLenW ∧
        v24 = cursorV ∧
        s0 = s.s0 ∧ s1 = s.s1 ∧ s2 = s.s2 ∧ s3 = s.s3 ∧
        chainIdW = s.s4 ∧ endW = s.s9 ∧ s11 = s.s11 ∧
        regionBase.toNat % 8 = 0 ∧
        listLen + 9 ≤ bytes.length ∧
        regionBase.toNat + bytes.length < 2 ^ 64 ∧
        (∀ k, k < bytes.length →
          isValidByteAccess (regionBase + BitVec.ofNat 64 k) = true) ∧
        (LinkListCount &&& ~~~(1 : Word)) = LinkListCount ∧
        Success bytes regionBase listLen 0 ∧
        ListCountResultSpecialize bytes regionBase listLen 0 (0 : Word) ∧
        regionBase.toNat + 0 < 2 ^ 64 ∧
        isValidByteAccess (regionBase + BitVec.ofNat 64 0) = true ∧
        ¬ BitVec.ult ((bytes[0]'hoff).zeroExtend 64) (0xc0 : Word) = true ∧
        BitVec.ult ((bytes[0]'hoff).zeroExtend 64) (0xf8 : Word) = true ∧
        (regionBase + BitVec.ofNat 64 0) +
            (((bytes[0]'hoff).zeroExtend 64 - (0xc0 : Word)) +
              signExtend12 (1 : BitVec 12)) =
          (regionBase + BitVec.ofNat 64 0) + listLenW ∧
        (∀ (refund rolledVal : Word) h,
          ((teerListCountAuthLoopPost spC regionBase AuthCountAddr s0 s1 s2 s3
              (0 : Word) bytes 0 listLenW) **
            teerAuthLoopEmptyAmbientMemIs spVal spC balPtr chainIdW s balBytes
              innerVal endW s11 refund rolledVal) h →
          rolledVal = (0 : Word))

/-- Fill Free26 from FrontToBridge + residual mid domain (identity content=regionBase).
    Residual: inhabit `front` (applied hrun) and `midA` (Success/guards/hrolled0). -/
def teerFrontToAuthLoopAssumedFree26_of
    (front : TeerFrontAuthContentToBridgeAssumed)
    (midA : TeerEmptyAuthFree26MidAssumed)
    (hlistLenW : front.listLenW = BitVec.ofNat 64 midA.listLen)
    (hlen : front.listLenW ≠ (0 : Word))
    (hn : nFree26EmptyToExitPack front.nSteps midA.listLen + 30 ≤ nTeerSteps) :
    TeerFrontToAuthLoopAssumedFree26 where
  nSteps := nFree26EmptyToExitPack front.nSteps midA.listLen
  hn := hn
  content := front.content
  listLenW := front.listLenW
  run := fun ret spVal spC regionBase loadPtr lenW balPtr balLenW chainIdW baiW
      s bs balBytes off len old1 s7Old cursorV endW s11 innerVal
      hc hold1 hret hbal hptr hbound hspC hra => by
    obtain ⟨newSp, bytes, s0, s1, s2, s3, v24, hoff,
        hbytes, hnewSp, hs0, hs1, hs2, hs3, hv24,
        hs0s, hs1s, hs2s, hs3s, hs4, hs9, hs11,
        hsalign, hslack, hover, hvalid, hretLink,
        hsuccess, hspe, hoverOff, hvalidOff, h_ge, h_hi, h_exact, hrolled0⟩ :=
      midA.mid spVal spC regionBase loadPtr lenW balPtr balLenW chainIdW baiW
        s bs balBytes front.content front.listLenW front.oldCount
        s7Old cursorV endW s11 innerVal hc hlistLenW hlen
    simpa [hc] using
      teerEmptyAuth_free26_to_exitPack front midA.asm ret spVal spC regionBase
        loadPtr lenW balPtr balLenW chainIdW baiW s bs balBytes off len
        old1 s7Old cursorV endW s11 innerVal newSp regionBase midA.listLen bytes
        s0 s1 s2 s3 v24 hoff rfl hbytes hc
        hs0 hs1 hs2 hs3 hv24 hs0s hs1s hs2s hs3s hs4 hs9 hs11 hlistLenW
        hsalign hslack hover hvalid hnewSp hretLink hsuccess hspe hlen
        hoverOff hvalidOff h_ge h_hi h_exact hrolled0 hret hbal hptr hbound hspC
        hra hold1

#print axioms teerAuthLoopEmptyAmbientPost_to_source_of_rolledZero
#print axioms teerFrontToAuthLoopAssumedFree26_of

/-- Free26 Front → ret a0=0 under ExitPack_toRet. Residual: inhabit Free26 (front+midA). -/
theorem teerEmptyAuth_free26_front_then_exit
    (front : TeerFrontToAuthLoopAssumedFree26)
    (ret spVal spC regionBase loadPtr lenW balPtr balLenW chainIdW baiW : Word)
    (s : TeerSaved)
    (bs balBytes : List (BitVec 8)) (off len : Nat)
    (old1 s7Old cursorV endW s11 innerVal : Word)
    (hcontent : front.content = regionBase)
    (hold1 : old1 = LinkAuthWalkNext9)
    (hret : (ret &&& ~~~(1 : Word)) = ret)
    (hbal : balPtr ≠ 0)
    (hptr : loadPtr = regionBase + BitVec.ofNat 64 off)
    (hbound : off + len ≤ bs.length)
    (hspC : spC = spVal + signExtend12 (-160 : BitVec 12))
    (hra : s.ra = ret) :
    cpsTripleWithin (front.nSteps + 30) E ret teerLinkedField0
      ((.x1 ↦ᵣ ret) ** (.x2 ↦ᵣ spVal) **
        stackFree spVal nTeerStackWithListCount **
        (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
        (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) ** (.x20 ↦ᵣ s.s4) **
        (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) ** (.x23 ↦ᵣ s.s7) **
        (.x24 ↦ᵣ s.s8) ** (.x25 ↦ᵣ s.s9) ** (.x26 ↦ᵣ s.s10) **
        (.x27 ↦ᵣ s.s11) **
        (.x10 ↦ᵣ loadPtr) ** (.x11 ↦ᵣ lenW) **
        (.x12 ↦ᵣ balPtr) ** (.x13 ↦ᵣ balLenW) **
        (.x14 ↦ᵣ chainIdW) ** (.x15 ↦ᵣ baiW) **
        bytesRegion regionBase bs ** bytesRegion balPtr balBytes **
        teerScratchOwn **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x16 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
        regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)))
      (fun hp =>
        ∃ (refund _t0Old _t1Old baiW' : Word),
          ((((.x10 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ ret) ** (.x2 ↦ᵣ spVal) **
              (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
              (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) **
              (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) **
              (.x23 ↦ᵣ s.s7) ** (.x24 ↦ᵣ s.s8) ** (.x25 ↦ᵣ s.s9) **
              (.x26 ↦ᵣ s.s10) ** (.x27 ↦ᵣ s.s11) **
              frameSlotsSaved teerEpiFrame spC (teerSavedVals s) **
              (.x11 ↦ᵣ refund) ** (.x5 ↦ᵣ RolledBackAddr) **
              (.x6 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
              (RegularRefundAddr ↦ₘ refund) **
              memOwn WouldbeStateAddr ** memOwn WouldbeRegularAddr **
              (RolledBackAddr ↦ₘ (0 : Word))) **
              teerEmptyAuthExitFrame baiW' spVal spC regionBase bs balBytes balPtr) **
            stackFree spC 6) hp) := by
  have hf := front.run ret spVal spC regionBase loadPtr lenW balPtr balLenW
    chainIdW baiW s bs balBytes off len old1 s7Old cursorV endW s11 innerVal
    hcontent hold1 hret hbal hptr hbound hspC hra
  have hexit :
      cpsTripleWithin 30 AfterAuthLoopLi ret teerLinkedField0
        (fun hp =>
          ∃ (refund t0Old t1Old baiW' : Word),
            teerAuthLoopEmptyExitPack spVal spC s
              (teerAuthLoopEmptyWalkCur front.content)
              (teerAuthLoopEmptyWalkEnd front.content front.listLenW)
              refund
              (teerAuthLoopEmptyWalkCur front.content)
              (teerAuthLoopEmptyWalkEnd front.content front.listLenW)
              t0Old t1Old baiW'
              regionBase bs balBytes balPtr hp)
        (fun hp =>
          ∃ (refund _t0Old _t1Old baiW' : Word),
            ((((.x10 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ ret) ** (.x2 ↦ᵣ spVal) **
                (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
                (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) **
                (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) **
                (.x23 ↦ᵣ s.s7) ** (.x24 ↦ᵣ s.s8) ** (.x25 ↦ᵣ s.s9) **
                (.x26 ↦ᵣ s.s10) ** (.x27 ↦ᵣ s.s11) **
                frameSlotsSaved teerEpiFrame spC (teerSavedVals s) **
                (.x11 ↦ᵣ refund) ** (.x5 ↦ᵣ RolledBackAddr) **
                (.x6 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
                (RegularRefundAddr ↦ₘ refund) **
                memOwn WouldbeStateAddr ** memOwn WouldbeRegularAddr **
                (RolledBackAddr ↦ₘ (0 : Word))) **
                teerEmptyAuthExitFrame baiW' spVal spC regionBase bs balBytes balPtr) **
              stackFree spC 6) hp) := by
    intro R hR st hcr hPR hpc
    obtain ⟨h0, hcompat, h1, h2, hd, hu, ⟨refund, t0, t1, bai', hPack⟩, hR2⟩ := hPR
    have hleaf :=
      teerAuthLoopEmptyExitPack_toRet spVal spC s
        (teerAuthLoopEmptyWalkCur front.content)
        (teerAuthLoopEmptyWalkEnd front.content front.listLenW)
        (teerAuthLoopEmptyWalkCur front.content)
        (teerAuthLoopEmptyWalkEnd front.content front.listLenW)
        t0 t1 refund bai' regionBase bs balBytes balPtr hspC
        (by simpa [hra] using hret)
    have hleaf' :
        cpsTripleWithin 30 AfterAuthLoopLi ret teerLinkedField0
          (teerAuthLoopEmptyExitPack spVal spC s
            (teerAuthLoopEmptyWalkCur front.content)
            (teerAuthLoopEmptyWalkEnd front.content front.listLenW)
            refund
            (teerAuthLoopEmptyWalkCur front.content)
            (teerAuthLoopEmptyWalkEnd front.content front.listLenW)
            t0 t1 bai' regionBase bs balBytes balPtr)
          (fun hp =>
            ((((.x10 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ ret) ** (.x2 ↦ᵣ spVal) **
                (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
                (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) **
                (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) **
                (.x23 ↦ᵣ s.s7) ** (.x24 ↦ᵣ s.s8) ** (.x25 ↦ᵣ s.s9) **
                (.x26 ↦ᵣ s.s10) ** (.x27 ↦ᵣ s.s11) **
                frameSlotsSaved teerEpiFrame spC (teerSavedVals s) **
                (.x11 ↦ᵣ refund) ** (.x5 ↦ᵣ RolledBackAddr) **
                (.x6 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
                (RegularRefundAddr ↦ₘ refund) **
                memOwn WouldbeStateAddr ** memOwn WouldbeRegularAddr **
                (RolledBackAddr ↦ₘ (0 : Word))) **
                teerEmptyAuthExitFrame bai' spVal spC regionBase bs balBytes balPtr) **
              stackFree spC 6) hp) := by
      simpa [hra] using hleaf
    obtain ⟨k, hk, st', hexec, hpc', hQ⟩ :=
      hleaf' R hR st hcr ⟨h0, hcompat, h1, h2, hd, hu, hPack, hR2⟩ hpc
    refine ⟨k, hk, st', hexec, hpc', ?_⟩
    obtain ⟨h0', hcompat', h1', h2', hd', hu', hRet, hR'⟩ := hQ
    exact ⟨h0', hcompat', h1', h2', hd', hu', ⟨refund, t0, t1, bai', hRet⟩, hR'⟩
  exact cpsTripleWithin_seq_perm_same_cr (fun _ hp => hp) hf hexit

/-- Mono: Free26 front+exit fits nTeerSteps. -/
theorem teerEmptyAuth_free26_front_then_exit_mono
    (front : TeerFrontToAuthLoopAssumedFree26)
    (ret spVal spC regionBase loadPtr lenW balPtr balLenW chainIdW baiW : Word)
    (s : TeerSaved)
    (bs balBytes : List (BitVec 8)) (off len : Nat)
    (old1 s7Old cursorV endW s11 innerVal : Word)
    (hcontent : front.content = regionBase)
    (hold1 : old1 = LinkAuthWalkNext9)
    (hret : (ret &&& ~~~(1 : Word)) = ret)
    (hbal : balPtr ≠ 0)
    (hptr : loadPtr = regionBase + BitVec.ofNat 64 off)
    (hbound : off + len ≤ bs.length)
    (hspC : spC = spVal + signExtend12 (-160 : BitVec 12))
    (hra : s.ra = ret) :
    cpsTripleWithin nTeerSteps E ret teerLinkedField0
      ((.x1 ↦ᵣ ret) ** (.x2 ↦ᵣ spVal) **
        stackFree spVal nTeerStackWithListCount **
        (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
        (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) ** (.x20 ↦ᵣ s.s4) **
        (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) ** (.x23 ↦ᵣ s.s7) **
        (.x24 ↦ᵣ s.s8) ** (.x25 ↦ᵣ s.s9) ** (.x26 ↦ᵣ s.s10) **
        (.x27 ↦ᵣ s.s11) **
        (.x10 ↦ᵣ loadPtr) ** (.x11 ↦ᵣ lenW) **
        (.x12 ↦ᵣ balPtr) ** (.x13 ↦ᵣ balLenW) **
        (.x14 ↦ᵣ chainIdW) ** (.x15 ↦ᵣ baiW) **
        bytesRegion regionBase bs ** bytesRegion balPtr balBytes **
        teerScratchOwn **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x16 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
        regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)))
      (fun hp =>
        ∃ (refund _t0Old _t1Old baiW' : Word),
          ((((.x10 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ ret) ** (.x2 ↦ᵣ spVal) **
              (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
              (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) **
              (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) **
              (.x23 ↦ᵣ s.s7) ** (.x24 ↦ᵣ s.s8) ** (.x25 ↦ᵣ s.s9) **
              (.x26 ↦ᵣ s.s10) ** (.x27 ↦ᵣ s.s11) **
              frameSlotsSaved teerEpiFrame spC (teerSavedVals s) **
              (.x11 ↦ᵣ refund) ** (.x5 ↦ᵣ RolledBackAddr) **
              (.x6 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
              (RegularRefundAddr ↦ₘ refund) **
              memOwn WouldbeStateAddr ** memOwn WouldbeRegularAddr **
              (RolledBackAddr ↦ₘ (0 : Word))) **
              teerEmptyAuthExitFrame baiW' spVal spC regionBase bs balBytes balPtr) **
            stackFree spC 6) hp) :=
  cpsTripleWithin_mono_nSteps front.hn
    (teerEmptyAuth_free26_front_then_exit front ret spVal spC regionBase loadPtr
      lenW balPtr balLenW chainIdW baiW s bs balBytes off len old1 s7Old cursorV
      endW s11 innerVal hcontent hold1 hret hbal hptr hbound hspC hra)

/-- Free pure: list_count link PC is 2-aligned (ret target). -/
theorem teerLinkListCount_aligned :
    (LinkListCount &&& ~~~(1 : Word)) = LinkListCount := by
  decide

#print axioms teerEmptyAuth_free26_front_then_exit
#print axioms teerEmptyAuth_free26_front_then_exit_mono
#print axioms teerLinkListCount_aligned

end EvmAsm.Codegen.TxEip7702TeerSpec
