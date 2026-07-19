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
import EvmAsm.Codegen.Programs.TxEip7702TeerAssumed
import EvmAsm.Codegen.Programs.TxEip7702TeerDischarge
import EvmAsm.Codegen.Programs.TxEip7702TeerAuthLoopStart
import EvmAsm.Codegen.Programs.TxEip7702TeerScratchZero
import EvmAsm.Codegen.Programs.TxEip7702TeerWouldbe
import EvmAsm.Codegen.Programs.TxEip7702TeerExitRet
import EvmAsm.Codegen.Programs.TxEip7702TeerEpilogue
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.SAsm.AbiFrame
import EvmAsm.Rv64.SAsm.StmtSoundCall

namespace EvmAsm.Codegen.TxEip7702TeerSpec

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Rv64.SAsm (cpsTripleWithin_exists_pre_gen)
open EvmAsm.Codegen

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

/-- Live TeerSaved at AfterAuthLoopLi after empty list_count + AuthLoopStart. -/
def teerAuthLoopEmptyLiveCur (s : TeerSaved)
    (walkCur walkEnd : Word) : TeerSaved where
  ra := LinkWalkInitAuth
  s0 := s.s0
  s1 := s.s1
  s2 := s.s2
  s3 := s.s3
  s4 := s.s4
  s5 := walkCur
  s6 := walkEnd
  s7 := 0
  s8 := 0
  s9 := s.s9
  s10 := 0
  s11 := s.s11
  a5 := s.a5

theorem teerAuthLoopEmptyLiveCur_s78 (s : TeerSaved) (c e : Word) :
    (teerAuthLoopEmptyLiveCur s c e).s8 = (0 : Word) ∧
      (teerAuthLoopEmptyLiveCur s c e).s7 = (0 : Word) :=
  ⟨rfl, rfl⟩

theorem teerAuthLoopEmptyLiveCur_s10 (s : TeerSaved) (c e : Word) :
    (teerAuthLoopEmptyLiveCur s c e).s10 = (0 : Word) := rfl

theorem teerAuthLoopEmptyLiveCur_ra (s : TeerSaved) (c e : Word) :
    (teerAuthLoopEmptyLiveCur s c e).ra = LinkWalkInitAuth := rfl

def teerAuthLoopEmptyWalkCur (listBase : Word) : Word :=
  listBase + signExtend12 (1 : BitVec 12)

def teerAuthLoopEmptyWalkEnd (listBase listLenW : Word) : Word :=
  listBase + listLenW

/-- ExitPre: live regs = AuthLoop-empty cur; frame slots = original saved `s`.
    Do NOT reuse `teerEmptyAuthExitPre liveCur` — that would double-empty and
    save liveCur into the frame slots. -/
def teerAuthLoopEmptyExitPre (spC : Word) (s : TeerSaved)
    (walkCur walkEnd refund a0Old a1Old t0Old t1Old : Word) : Assertion :=
  (.x2 ↦ᵣ spC) **
    regsAt teerEpiFrame (teerSavedVals (teerAuthLoopEmptyLiveCur s walkCur walkEnd)) **
    frameSlotsSaved teerEpiFrame spC (teerSavedVals s) **
    (.x10 ↦ᵣ a0Old) ** (.x11 ↦ᵣ a1Old) **
    (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x0 ↦ᵣ (0 : Word)) **
    (RegularRefundAddr ↦ₘ refund) **
    memOwn WouldbeStateAddr ** memOwn WouldbeRegularAddr **
    (RolledBackAddr ↦ₘ (0 : Word))

/-- ((ExitPre ** ExitFrame) ** nested free) — left-nested for double frameR. -/
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

#print axioms teerAuthLoopEmptyLiveCur_s78
#print axioms teerAuthLoopEmptyLiveCur_s10
#print axioms teerAuthLoopEmptyLiveCur_ra
#print axioms teerAuthLoopEmpty_exitToRet_rolled0
#print axioms teerAuthLoopEmptyExitPack_toRet
#print axioms teerAuthLoopEmpty_to_exitPack
#print axioms teerAuthLoopEmptySource_toRet
#print axioms teerAuthLoopEmptyAmbientPost_peel
#print axioms teerAuthLoopEmptyAmbientMemIs_to_source
#print axioms teerAuthLoopEmptyAmbientPost_to_source
#print axioms teerAuthLoopEmptyAmbientPost_toRet

end EvmAsm.Codegen.TxEip7702TeerSpec
