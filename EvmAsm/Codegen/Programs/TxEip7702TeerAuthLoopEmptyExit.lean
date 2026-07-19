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
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.Tactics.XSimp

namespace EvmAsm.Codegen.TxEip7702TeerSpec

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
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

/-- Named hyp: reshape AuthLoop empty post**ambient → ExitPack. -/
structure TeerAuthLoopEmptyToExitAssumed where
  reshape :
    ∀ (spVal spC listBase listLenW s0 s1 s2 s3 : Word)
      (bytes : List (BitVec 8))
      (balPtr chainIdW : Word)
      (s : TeerSaved) (balBytes : List (BitVec 8))
      (innerVal endW s11 refund : Word)
      (regionBase : Word) (bs : List (BitVec 8))
      (baiW a0Old a1Old t0Old t1Old : Word),
      listBase = regionBase →
      bytes = bs →
      s0 = s.s0 → s1 = s.s1 → s2 = s.s2 → s3 = s.s3 →
      chainIdW = s.s4 →
      endW = s.s9 → s11 = s.s11 →
      baiW = s.a5 →
      a0Old = teerAuthLoopEmptyWalkCur listBase →
      a1Old = teerAuthLoopEmptyWalkEnd listBase listLenW →
      ∀ h,
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
            memOwn (BitVec.ofNat 64 GuestAddrs.teer_records_ptr))) h →
        teerAuthLoopEmptyExitPack spVal spC s
          (teerAuthLoopEmptyWalkCur listBase)
          (teerAuthLoopEmptyWalkEnd listBase listLenW)
          refund a0Old a1Old t0Old t1Old baiW
          regionBase bs balBytes balPtr h

#print axioms teerAuthLoopEmptyLiveCur_s78
#print axioms teerAuthLoopEmptyLiveCur_s10
#print axioms teerAuthLoopEmptyLiveCur_ra
#print axioms teerAuthLoopEmpty_exitToRet_rolled0
#print axioms teerAuthLoopEmptyExitPack_toRet

end EvmAsm.Codegen.TxEip7702TeerSpec
