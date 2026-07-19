/-
  TeerAssumed packaging substrate.

  * TeerCalleeAssumptions — bundle of named Assumed body leaves
  * TeerFrontToAuthLoopAssumed — E → AfterAuthLoopLi (empty-auth live state)
  * teerEmptyAuth_front_then_exit — front + empty exit → ret (rolled=0, a0=0)

  Full TeerAssumed.applied_flat fill residual: stackFree/teerScratchOwn
  reassembly + teer pure = 0 bridge on ambient post.
-/

import EvmAsm.Codegen.Programs.TxEip7702TeerExitRet
import EvmAsm.Codegen.Programs.TxEip7702TeerAuthLoopRecoverCall
import EvmAsm.Codegen.Programs.TxEip7702TeerAuthLoopBalFind
import EvmAsm.Codegen.Programs.TxEip7702TeerAuthLoopBalFinals
import EvmAsm.Codegen.Programs.TxEip7702TeerAuthLoopCodeAt
import EvmAsm.Codegen.Programs.TxEip7702TeerAuthLoopBalNonce
import EvmAsm.Codegen.Programs.TxEip7702TeerAuthLoopNonceJoin
import EvmAsm.Codegen.Programs.TxEip7702TeerAuthLoopOrZero
import EvmAsm.Codegen.Programs.TxEip7702TeerSuccessWrite
import EvmAsm.Codegen.Programs.TxEip7702TeerPriorZero
import EvmAsm.Codegen.Programs.TxEip7702TeerFrontListCount
import EvmAsm.Codegen.Programs.TxEip7702TeerSpec
import EvmAsm.Codegen.Programs.BlockVerdictTxStateGasArraySpec
import EvmAsm.Codegen.Programs.BlockVerdictTxStateGasArrayModel
import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.SAsm.AbiFrame

namespace EvmAsm.Codegen.TxEip7702TeerSpec

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
open EvmAsm.Codegen.BlockVerdictTxStateGasArraySpec
open EvmAsm.Codegen.BlockVerdictTxStateGasArrayModel

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
    | exact bytesRegion_pcFree _ _)

/-- Named Assumed hyps for unproven teer body leaves / mid-loop blocks. -/
structure TeerCalleeAssumptions (cr : CodeReq) where
  recover : TeerRecoverAssumed cr
  balFind : TeerBalFindAssumed cr
  balFinals : TeerBalFinalsAssumed cr
  codeAt : TeerCodeAtAssumed cr
  balNonce : TeerBalNonceAssumed cr
  authSenderMatch : TeerAuthSenderMatchAssumed cr
  authOrZero : TeerAuthOrZeroAssumed cr
  successWrite : TeerSuccessWriteAssumed cr
  priorZero : TeerPriorZeroAssumed cr
  listCountAuthLoop : TeerListCountAuthLoopAssumed cr
  /-- AuthContent flat → ListCount CalleeP prest (nested free + bytes window). -/
  contentBridge : TeerAuthContentBridgeAssumed

/-- Live regs at AfterAuthLoopLi for empty-auth exit (s7=s8=0, s10=0). -/
def teerEmptyAuthCur (s : TeerSaved) : TeerSaved where
  ra := s.ra
  s0 := s.s0
  s1 := s.s1
  s2 := s.s2
  s3 := s.s3
  s4 := s.s4
  s5 := s.s5
  s6 := s.s6
  s7 := 0
  s8 := 0
  s9 := s.s9
  s10 := 0
  s11 := s.s11
  a5 := s.a5

theorem teerEmptyAuthCur_s10 (s : TeerSaved) :
    (teerEmptyAuthCur s).s10 = (0 : Word) := rfl

theorem teerEmptyAuthCur_s78 (s : TeerSaved) :
    (teerEmptyAuthCur s).s8 = (0 : Word) ∧ (teerEmptyAuthCur s).s7 = (0 : Word) :=
  ⟨rfl, rfl⟩

/-- Prest at AfterAuthLoopLi matching `teerEmptyAuthToRet_rolled0`. -/
def teerEmptyAuthExitPre (spC : Word) (s : TeerSaved)
    (refund a0Old a1Old t0Old t1Old : Word) : Assertion :=
  (.x2 ↦ᵣ spC) **
    regsAt teerEpiFrame (teerSavedVals (teerEmptyAuthCur s)) **
    frameSlotsSaved teerEpiFrame spC (teerSavedVals s) **
    (.x10 ↦ᵣ a0Old) ** (.x11 ↦ᵣ a1Old) **
    (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x0 ↦ᵣ (0 : Word)) **
    (RegularRefundAddr ↦ₘ refund) **
    memOwn WouldbeStateAddr ** memOwn WouldbeRegularAddr **
    (RolledBackAddr ↦ₘ (0 : Word))

/-- Front half Assumed: entry → AfterAuthLoopLi with empty-auth live state.
    Residual: compose Spec..ListCount..AuthLoopStart under bal≠0. -/
structure TeerFrontToAuthLoopAssumed (cr : CodeReq) where
  nSteps : Nat
  hn : nSteps + 30 ≤ nTeerSteps
  run :
    ∀ (ret spVal spC regionBase loadPtr lenW balPtr balLenW chainIdW baiW : Word)
      (s : TeerSaved)
      (bs balBytes : List (BitVec 8)) (off len : Nat)
      (refund a0Old a1Old t0Old t1Old : Word),
      (ret &&& ~~~(1 : Word)) = ret →
      balPtr ≠ 0 →
      loadPtr = regionBase + BitVec.ofNat 64 off →
      off + len ≤ bs.length →
      spC = spVal + signExtend12 (-160 : BitVec 12) →
      s.ra = ret →
      cpsTripleWithin nSteps E AfterAuthLoopLi cr
        ((.x1 ↦ᵣ ret) ** (.x2 ↦ᵣ spVal) **
          stackFree spVal nTeerStackDwords **
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
        (teerEmptyAuthExitPre spC s refund a0Old a1Old t0Old t1Old **
          (.x15 ↦ᵣ baiW) **
          stackFree spVal 6 **
          memOwn (spC + signExtend12 (104 : BitVec 12)) **
          bytesRegion regionBase bs ** bytesRegion balPtr balBytes **
          memOwn (BitVec.ofNat 64 GuestAddrs.teer_authority) **
          memOwn (BitVec.ofNat 64 GuestAddrs.teer_acct_ptr) **
          memOwn (BitVec.ofNat 64 GuestAddrs.teer_acct_len) **
          memOwn (BitVec.ofNat 64 GuestAddrs.teer_acct_absent) **
          memOwn (BitVec.ofNat 64 GuestAddrs.teer_prior_count) **
          memOwn (BitVec.ofNat 64 GuestAddrs.teer_pre_acct) **
          memOwn (BitVec.ofNat 64 GuestAddrs.teer_success_count) **
          memOwn (BitVec.ofNat 64 GuestAddrs.teer_prior_set_flag) **
          memOwn (BitVec.ofNat 64 GuestAddrs.teer_inner_off) **
          memOwn (BitVec.ofNat 64 GuestAddrs.teer_finals) **
          memOwn (BitVec.ofNat 64 GuestAddrs.teer_value_nonzero) **
          memOwn (BitVec.ofNat 64 GuestAddrs.teer_type) **
          memOwn (BitVec.ofNat 64 GuestAddrs.teer_success_table) **
          memOwn (BitVec.ofNat 64 GuestAddrs.teer_recipient_ptr) **
          memOwn (BitVec.ofNat 64 GuestAddrs.teer_recipient_len) **
          memOwn (BitVec.ofNat 64 GuestAddrs.teer_predelegated_count) **
          memOwn (BitVec.ofNat 64 GuestAddrs.teer_auth_count) **
          memOwn (BitVec.ofNat 64 GuestAddrs.teer_recover_scratch) **
          memOwn (BitVec.ofNat 64 GuestAddrs.teer_records_ptr) **
          regOwn .x7 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
          regOwn .x16 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
          regOwn .x31)

/-- Ambient frame carried through empty exit (not touched by wouldbe/epi).
    Carries top-6 free padding + a5@104 slot (epi does not restore a5). -/
def teerEmptyAuthExitFrame (baiW spVal spC regionBase : Word)
    (bs balBytes : List (BitVec 8)) (balPtr : Word) : Assertion :=
  (.x15 ↦ᵣ baiW) **
    stackFree spVal 6 **
    memOwn (spC + signExtend12 (104 : BitVec 12)) **
    bytesRegion regionBase bs ** bytesRegion balPtr balBytes **
    memOwn (BitVec.ofNat 64 GuestAddrs.teer_authority) **
    memOwn (BitVec.ofNat 64 GuestAddrs.teer_acct_ptr) **
    memOwn (BitVec.ofNat 64 GuestAddrs.teer_acct_len) **
    memOwn (BitVec.ofNat 64 GuestAddrs.teer_acct_absent) **
    memOwn (BitVec.ofNat 64 GuestAddrs.teer_prior_count) **
    memOwn (BitVec.ofNat 64 GuestAddrs.teer_pre_acct) **
    memOwn (BitVec.ofNat 64 GuestAddrs.teer_success_count) **
    memOwn (BitVec.ofNat 64 GuestAddrs.teer_prior_set_flag) **
    memOwn (BitVec.ofNat 64 GuestAddrs.teer_inner_off) **
    memOwn (BitVec.ofNat 64 GuestAddrs.teer_finals) **
    memOwn (BitVec.ofNat 64 GuestAddrs.teer_value_nonzero) **
    memOwn (BitVec.ofNat 64 GuestAddrs.teer_type) **
    memOwn (BitVec.ofNat 64 GuestAddrs.teer_success_table) **
    memOwn (BitVec.ofNat 64 GuestAddrs.teer_recipient_ptr) **
    memOwn (BitVec.ofNat 64 GuestAddrs.teer_recipient_len) **
    memOwn (BitVec.ofNat 64 GuestAddrs.teer_predelegated_count) **
    memOwn (BitVec.ofNat 64 GuestAddrs.teer_auth_count) **
    memOwn (BitVec.ofNat 64 GuestAddrs.teer_recover_scratch) **
    memOwn (BitVec.ofNat 64 GuestAddrs.teer_records_ptr) **
    regOwn .x7 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
    regOwn .x16 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
    regOwn .x31

/-- Front (Assumed) + empty-auth exit → ret with a0=0 (rolled=0).
    Step count ≤ nTeerSteps via front.hn. -/
theorem teerEmptyAuth_front_then_exit
    (front : TeerFrontToAuthLoopAssumed teerLinkedField0)
    (ret spVal spC regionBase loadPtr lenW balPtr balLenW chainIdW baiW : Word)
    (s : TeerSaved)
    (bs balBytes : List (BitVec 8)) (off len : Nat)
    (refund a0Old a1Old t0Old t1Old : Word)
    (hret : (ret &&& ~~~(1 : Word)) = ret)
    (hbal : balPtr ≠ 0)
    (hptr : loadPtr = regionBase + BitVec.ofNat 64 off)
    (hbound : off + len ≤ bs.length)
    (hspC : spC = spVal + signExtend12 (-160 : BitVec 12))
    (hra : s.ra = ret) :
    cpsTripleWithin (front.nSteps + 30) E ret teerLinkedField0
      ((.x1 ↦ᵣ ret) ** (.x2 ↦ᵣ spVal) **
        stackFree spVal nTeerStackDwords **
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
      ((.x10 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ ret) ** (.x2 ↦ᵣ spVal) **
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
        (RolledBackAddr ↦ₘ (0 : Word)) **
        teerEmptyAuthExitFrame baiW spVal spC regionBase bs balBytes balPtr) := by
  have hf := front.run ret spVal spC regionBase loadPtr lenW balPtr balLenW
    chainIdW baiW s bs balBytes off len refund a0Old a1Old t0Old t1Old
    hret hbal hptr hbound hspC hra
  have hx0 := teerEmptyAuthToRet_rolled0 spVal spC s (teerEmptyAuthCur s)
    (0 : Word) a0Old a1Old t0Old t1Old refund hspC
    (by simpa [hra] using hret)
    (teerEmptyAuthCur_s10 s)
    (teerEmptyAuthCur_s78 s)
  -- Exit PC is s.ra; rewrite to ret via hra.
  have hx : cpsTripleWithin 30 AfterAuthLoopLi ret teerLinkedField0
      (teerEmptyAuthExitPre spC s refund a0Old a1Old t0Old t1Old)
      ((.x10 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ ret) ** (.x2 ↦ᵣ spVal) **
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
    simpa [hra, teerEmptyAuthExitPre] using hx0
  have hxF := cpsTripleWithin_frameR
    (teerEmptyAuthExitFrame baiW spVal spC regionBase bs balBytes balPtr)
    (by pcf) hx
  have hall := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
      dsimp only [teerEmptyAuthExitPre, teerEmptyAuthExitFrame] at hp ⊢
      xperm_hyp hp) hf hxF
  exact cpsTripleWithin_weaken (fun _ hp => hp)
    (fun _ hq => by xperm_hyp hq) hall

/-- Mono: empty-auth front+exit fits nTeerSteps. -/
theorem teerEmptyAuth_front_then_exit_mono
    (front : TeerFrontToAuthLoopAssumed teerLinkedField0)
    (ret spVal spC regionBase loadPtr lenW balPtr balLenW chainIdW baiW : Word)
    (s : TeerSaved)
    (bs balBytes : List (BitVec 8)) (off len : Nat)
    (refund a0Old a1Old t0Old t1Old : Word)
    (hret : (ret &&& ~~~(1 : Word)) = ret)
    (hbal : balPtr ≠ 0)
    (hptr : loadPtr = regionBase + BitVec.ofNat 64 off)
    (hbound : off + len ≤ bs.length)
    (hspC : spC = spVal + signExtend12 (-160 : BitVec 12))
    (hra : s.ra = ret) :
    cpsTripleWithin nTeerSteps E ret teerLinkedField0
      ((.x1 ↦ᵣ ret) ** (.x2 ↦ᵣ spVal) **
        stackFree spVal nTeerStackDwords **
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
      ((.x10 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ ret) ** (.x2 ↦ᵣ spVal) **
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
        (RolledBackAddr ↦ₘ (0 : Word)) **
        teerEmptyAuthExitFrame baiW spVal spC regionBase bs balBytes balPtr) :=
  cpsTripleWithin_mono_nSteps front.hn
    (teerEmptyAuth_front_then_exit front ret spVal spC regionBase loadPtr lenW
      balPtr balLenW chainIdW baiW s bs balBytes off len refund a0Old a1Old
      t0Old t1Old hret hbal hptr hbound hspC hra)

#print axioms teerEmptyAuthCur_s10
#print axioms teerEmptyAuthCur_s78
#print axioms teerEmptyAuth_front_then_exit
#print axioms teerEmptyAuth_front_then_exit_mono

end EvmAsm.Codegen.TxEip7702TeerSpec
