/-
  Early teer front under applied_flat prest shape:
  E → AfterAbiMoves (prologue) with regOwn temps matching TeerAssumed PRE.

  First segment toward discharging TeerFrontToAuthLoopAssumed.
-/

import EvmAsm.Codegen.Programs.TxEip7702TeerPrologue
import EvmAsm.Codegen.Programs.TxEip7702TeerScratchZero
import EvmAsm.Codegen.Programs.TxEip7702TeerBalCheck
import EvmAsm.Codegen.Programs.TxEip7702TeerDischarge
import EvmAsm.Codegen.Programs.BlockVerdictTxStateGasArraySpec
import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.SAsm.AbiFrame

namespace EvmAsm.Codegen.TxEip7702TeerSpec

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
open EvmAsm.Codegen.BlockVerdictTxStateGasArraySpec

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

/-- ABI a0–a4 + regOwn temps (applied_flat PRE shape). -/
def prologueAbiRestOwn
    (loadPtr lenW balPtr balLenW chainIdW : Word) : Assertion :=
  (.x10 ↦ᵣ loadPtr) ** (.x11 ↦ᵣ lenW) ** (.x12 ↦ᵣ balPtr) **
  (.x13 ↦ᵣ balLenW) ** (.x14 ↦ᵣ chainIdW) **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x16 **
  regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
  (.x0 ↦ᵣ (0 : Word))

/-- Post-prologue with regOwn temps + free6 ambient. -/
def prologuePostOwn (spC : Word) (s : TeerSaved)
    (loadPtr lenW balPtr balLenW chainIdW spVal regionBase balPtr' : Word)
    (bs balBytes : List (BitVec 8)) : Assertion :=
  (.x2 ↦ᵣ spC) **
  (.x1 ↦ᵣ s.ra) **
  (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
  (.x18 ↦ᵣ balPtr) ** (.x19 ↦ᵣ balLenW) ** (.x20 ↦ᵣ chainIdW) **
  (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) ** (.x23 ↦ᵣ s.s7) **
  (.x24 ↦ᵣ s.s8) ** (.x25 ↦ᵣ s.s9) ** (.x26 ↦ᵣ s.s10) **
  (.x27 ↦ᵣ s.s11) ** (.x15 ↦ᵣ s.a5) **
  frameSlotsSaved teerFrame spC (teerSavedVals s) **
  prologueAbiRestOwn loadPtr lenW balPtr balLenW chainIdW **
  stackFree spVal 6 **
  bytesRegion regionBase bs ** bytesRegion balPtr' balBytes **
  teerScratchOwn

/-- Prologue with regOwn temps (no value-carrying x5–x7,x16). Dual teerPrologue. -/
theorem teerPrologue_ownTemps (sp0 spC : Word) (s : TeerSaved)
    (loadPtr lenW balPtr balLenW chainIdW : Word)
    (hspC : spC = sp0 + signExtend12 teerSpDelta) :
    cpsTripleWithin 20 E AfterAbiMoves teerCode
      ((.x2 ↦ᵣ sp0) ** regsAt teerFrame (teerSavedVals s) **
        frameSlotsOwn teerFrame spC **
        prologueAbiRestOwn loadPtr lenW balPtr balLenW chainIdW)
      ((.x2 ↦ᵣ spC) **
        (.x1 ↦ᵣ s.ra) **
        (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
        (.x18 ↦ᵣ balPtr) ** (.x19 ↦ᵣ balLenW) ** (.x20 ↦ᵣ chainIdW) **
        (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) ** (.x23 ↦ᵣ s.s7) **
        (.x24 ↦ᵣ s.s8) ** (.x25 ↦ᵣ s.s9) ** (.x26 ↦ᵣ s.s10) **
        (.x27 ↦ᵣ s.s11) ** (.x15 ↦ᵣ s.a5) **
        frameSlotsSaved teerFrame spC (teerSavedVals s) **
        prologueAbiRestOwn loadPtr lenW balPtr balLenW chainIdW) := by
  have hsave := teerFrameSave sp0 spC s hspC
  have hsaveF := cpsTripleWithin_frameR
    (prologueAbiRestOwn loadPtr lenW balPtr balLenW chainIdW) (by pcf) hsave
  have hmv := teerAbiMoves loadPtr lenW balPtr balLenW chainIdW
    s.s0 s.s1 s.s2 s.s3 s.s4
  -- Frame moves with ambient after peeling s0–s4 + a0–a4 (dual teerPrologue)
  have hmvF := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ s.ra) **
      (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) ** (.x23 ↦ᵣ s.s7) **
      (.x24 ↦ᵣ s.s8) ** (.x25 ↦ᵣ s.s9) ** (.x26 ↦ᵣ s.s10) **
      (.x27 ↦ᵣ s.s11) ** (.x15 ↦ᵣ s.a5) **
      frameSlotsSaved teerFrame spC (teerSavedVals s) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x16 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      (.x0 ↦ᵣ (0 : Word))) (by pcf) hmv
  have h01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
    rw [regsAt_teerFrame] at hp
    dsimp only [prologueAbiRestOwn] at hp
    xperm_hyp hp) hsaveF hmvF
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by
      dsimp only [prologueAbiRestOwn] at hq ⊢
      xperm_hyp hq) h01

/-- Applied entry prest → prologue_ownTemps prest. -/
theorem teerAppliedEntry_to_prologueOwnPre
    (ret spVal spC loadPtr lenW balPtr balLenW chainIdW baiW : Word)
    (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : Word)
    (regionBase : Word) (bs balBytes : List (BitVec 8))
    (hspC : spC = spVal + signExtend12 (-160 : BitVec 12)) :
    ∀ h,
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
        regOwn .x31 ** (.x0 ↦ᵣ (0 : Word))) h →
      (((.x2 ↦ᵣ spVal) **
          regsAt teerFrame (teerSavedVals
            { ra := ret, s0 := s0, s1 := s1, s2 := s2, s3 := s3, s4 := s4
              s5 := s5, s6 := s6, s7 := s7, s8 := s8, s9 := s9
              s10 := s10, s11 := s11, a5 := baiW }) **
          frameSlotsOwn teerFrame spC **
          prologueAbiRestOwn loadPtr lenW balPtr balLenW chainIdW) **
        (stackFree spVal 6 **
          bytesRegion regionBase bs ** bytesRegion balPtr balBytes **
          teerScratchOwn)) h := by
  intro h hp
  have heq := stackFree20_split spVal
  have hp1 :
      ((.x1 ↦ᵣ ret) ** (.x2 ↦ᵣ spVal) **
        (frameSlotsOwn teerFrame (spVal + signExtend12 (-160 : BitVec 12)) **
          stackFree spVal 6) **
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
        regOwn .x31 ** (.x0 ↦ᵣ (0 : Word))) h := by
    simpa [heq] using hp
  have hp2 :
      ((.x1 ↦ᵣ ret) ** (.x2 ↦ᵣ spVal) **
        (frameSlotsOwn teerFrame spC ** stackFree spVal 6) **
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
        regOwn .x31 ** (.x0 ↦ᵣ (0 : Word))) h := by
    simpa [hspC] using hp1
  simp only [regsAt_teerFrame, prologueAbiRestOwn] at hp2 ⊢
  xperm_hyp hp2

/-- Applied entry → AfterAbiMoves (20 steps), free6+regions+scratch ambient. -/
theorem teerPrologue_applied
    (ret spVal spC loadPtr lenW balPtr balLenW chainIdW baiW : Word)
    (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : Word)
    (regionBase : Word) (bs balBytes : List (BitVec 8))
    (hspC : spC = spVal + signExtend12 (-160 : BitVec 12)) :
    let s : TeerSaved :=
      { ra := ret, s0 := s0, s1 := s1, s2 := s2, s3 := s3, s4 := s4
        s5 := s5, s6 := s6, s7 := s7, s8 := s8, s9 := s9
        s10 := s10, s11 := s11, a5 := baiW }
    cpsTripleWithin 20 E AfterAbiMoves teerCode
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
        (.x1 ↦ᵣ ret) **
        (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
        (.x18 ↦ᵣ balPtr) ** (.x19 ↦ᵣ balLenW) ** (.x20 ↦ᵣ chainIdW) **
        (.x21 ↦ᵣ s5) ** (.x22 ↦ᵣ s6) ** (.x23 ↦ᵣ s7) **
        (.x24 ↦ᵣ s8) ** (.x25 ↦ᵣ s9) ** (.x26 ↦ᵣ s10) **
        (.x27 ↦ᵣ s11) ** (.x15 ↦ᵣ baiW) **
        frameSlotsSaved teerFrame spC (teerSavedVals s) **
        prologueAbiRestOwn loadPtr lenW balPtr balLenW chainIdW **
        stackFree spVal 6 **
        bytesRegion regionBase bs ** bytesRegion balPtr balBytes **
        teerScratchOwn) := by
  intro s
  have hspC' : spC = spVal + signExtend12 teerSpDelta := by
    simpa [teerSpDelta] using hspC
  have hpre := teerAppliedEntry_to_prologueOwnPre ret spVal spC loadPtr lenW
    balPtr balLenW chainIdW baiW s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    regionBase bs balBytes hspC
  have hrun0 := teerPrologue_ownTemps spVal spC s loadPtr lenW balPtr balLenW
    chainIdW hspC'
  have hrunF := cpsTripleWithin_frameR
    (stackFree spVal 6 **
      bytesRegion regionBase bs ** bytesRegion balPtr balBytes **
      teerScratchOwn) (by pcf) hrun0
  have hrun := cpsTripleWithin_weaken hpre (fun _ hq => hq) hrunF
  -- s fields definitional; reassoc nested ambient to flat post
  exact cpsTripleWithin_weaken (fun _ hp => hp)
    (fun _ hq => by
      simp only [s] at hq ⊢
      xperm_hyp hq) hrun


#print axioms teerPrologue_ownTemps
#print axioms teerAppliedEntry_to_prologueOwnPre
#print axioms teerPrologue_applied


/-- Remaining scratch cells after peeling the four zeroed ones. -/
def teerScratchRestOwn : Assertion :=
  memOwn (BitVec.ofNat 64 GuestAddrs.teer_authority) **
  memOwn (BitVec.ofNat 64 GuestAddrs.teer_acct_ptr) **
  memOwn (BitVec.ofNat 64 GuestAddrs.teer_acct_len) **
  memOwn (BitVec.ofNat 64 GuestAddrs.teer_acct_absent) **
  memOwn (BitVec.ofNat 64 GuestAddrs.teer_prior_count) **
  memOwn (BitVec.ofNat 64 GuestAddrs.teer_pre_acct) **
  memOwn (BitVec.ofNat 64 GuestAddrs.teer_prior_set_flag) **
  memOwn (BitVec.ofNat 64 GuestAddrs.teer_inner_off) **
  memOwn (BitVec.ofNat 64 GuestAddrs.teer_finals) **
  memOwn (BitVec.ofNat 64 GuestAddrs.teer_value_nonzero) **
  memOwn (BitVec.ofNat 64 GuestAddrs.teer_type) **
  memOwn (BitVec.ofNat 64 GuestAddrs.teer_success_table) **
  memOwn (BitVec.ofNat 64 GuestAddrs.teer_recipient_ptr) **
  memOwn (BitVec.ofNat 64 GuestAddrs.teer_recipient_len) **
  memOwn (BitVec.ofNat 64 GuestAddrs.teer_auth_count) **
  memOwn (BitVec.ofNat 64 GuestAddrs.teer_wouldbe_state) **
  memOwn (BitVec.ofNat 64 GuestAddrs.teer_wouldbe_regular) **
  memOwn (BitVec.ofNat 64 GuestAddrs.teer_recover_scratch) **
  memOwn (BitVec.ofNat 64 GuestAddrs.teer_records_ptr)

private theorem pcFree_teerScratchRestOwn : teerScratchRestOwn.pcFree := by
  unfold teerScratchRestOwn
  repeat' (first | exact pcFree_memOwn | apply pcFree_sepConj)

theorem teerScratchOwn_to_zero_rest :
    ∀ h, teerScratchOwn h → (teerScratchZeroOwn ** teerScratchRestOwn) h := by
  intro h hp
  unfold teerScratchOwn teerScratchZeroOwn teerScratchRestOwn
    RegularRefundAddr SuccessCountAddr PredelegatedAddr RolledBackAddr at *
  xperm_hyp hp

theorem teerScratchOwn_of_zero_rest :
    ∀ h, (teerScratchZeroOwn ** teerScratchRestOwn) h → teerScratchOwn h := by
  intro h hp
  unfold teerScratchOwn teerScratchZeroOwn teerScratchRestOwn
    RegularRefundAddr SuccessCountAddr PredelegatedAddr RolledBackAddr at *
  xperm_hyp hp

/-- Scratch-zero with regOwn x5 (forall-lift). Parenthesize for of_forall. -/
theorem teerScratchZero_regOwn (v26 : Word) :
    cpsTripleWithin 13 AfterAbiMoves AtBalCheck teerCode
      (((.x26 ↦ᵣ v26) ** (.x0 ↦ᵣ (0 : Word)) ** teerScratchZeroOwn) ** regOwn .x5)
      ((.x26 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ RolledBackAddr) ** (.x0 ↦ᵣ (0 : Word)) **
        teerScratchZeroOwn) := by
  refine cpsTripleWithin_of_forall_regIs_to_regOwn
    (P := (.x26 ↦ᵣ v26) ** (.x0 ↦ᵣ (0 : Word)) ** teerScratchZeroOwn) ?_
  intro v5
  have h0 := teerScratchZero v26 v5
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) h0

/-- Framed scratch-zero under full teerScratchOwn. -/
theorem teerScratchZero_fullScratch (v26 : Word) (R : Assertion)
    (hR : R.pcFree) :
    cpsTripleWithin 13 AfterAbiMoves AtBalCheck teerCode
      (((.x26 ↦ᵣ v26) ** (.x0 ↦ᵣ (0 : Word)) ** teerScratchOwn) **
        regOwn .x5 ** R)
      ((.x26 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ RolledBackAddr) ** (.x0 ↦ᵣ (0 : Word)) **
        teerScratchOwn ** R) := by
  have hbody := teerScratchZero_regOwn v26
  have hF := cpsTripleWithin_frameR (teerScratchRestOwn ** R)
    (pcFree_sepConj pcFree_teerScratchRestOwn hR) hbody
  exact cpsTripleWithin_weaken
    (fun _ hp => by
      -- Expand full scratch in hyp; expand zero/rest+abbrevs in goal only.
      unfold teerScratchOwn at hp
      unfold teerScratchZeroOwn teerScratchRestOwn
        RegularRefundAddr SuccessCountAddr PredelegatedAddr RolledBackAddr
      xperm_hyp hp)
    (fun _ hq => by
      unfold teerScratchZeroOwn teerScratchRestOwn
        RegularRefundAddr SuccessCountAddr PredelegatedAddr RolledBackAddr at hq
      unfold teerScratchOwn
      xperm_hyp hq) hF

#print axioms teerScratchOwn_to_zero_rest
#print axioms teerScratchZero_regOwn
#print axioms teerScratchZero_fullScratch

/-! ## Value-carrying scratch-zero under applied (RolledZero thread)

`teerScratchZero_fullScratch` rebuilds `teerScratchOwn` (memOwn). Empty-auth
RolledZero needs `RolledBack ↦ₘ 0` preserved; these duals post
`teerScratchZeroIs ** teerScratchRestOwn` instead. -/

/-- Scratch-zero Is with regOwn x5 (forall-lift). -/
theorem teerScratchZero_regOwn_is (v26 : Word) :
    cpsTripleWithin 13 AfterAbiMoves AtBalCheck teerCode
      (((.x26 ↦ᵣ v26) ** (.x0 ↦ᵣ (0 : Word)) ** teerScratchZeroOwn) ** regOwn .x5)
      ((.x26 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ RolledBackAddr) ** (.x0 ↦ᵣ (0 : Word)) **
        teerScratchZeroIs) := by
  refine cpsTripleWithin_of_forall_regIs_to_regOwn
    (P := (.x26 ↦ᵣ v26) ** (.x0 ↦ᵣ (0 : Word)) ** teerScratchZeroOwn) ?_
  intro v5
  have h0 := teerScratchZero_is v26 v5
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) h0

/-- Framed scratch-zero Is under full teerScratchOwn → ZeroIs ** RestOwn. -/
theorem teerScratchZero_fullScratch_is (v26 : Word) (R : Assertion)
    (hR : R.pcFree) :
    cpsTripleWithin 13 AfterAbiMoves AtBalCheck teerCode
      (((.x26 ↦ᵣ v26) ** (.x0 ↦ᵣ (0 : Word)) ** teerScratchOwn) **
        regOwn .x5 ** R)
      ((.x26 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ RolledBackAddr) ** (.x0 ↦ᵣ (0 : Word)) **
        teerScratchZeroIs ** teerScratchRestOwn ** R) := by
  have hbody := teerScratchZero_regOwn_is v26
  have hF := cpsTripleWithin_frameR (teerScratchRestOwn ** R)
    (pcFree_sepConj pcFree_teerScratchRestOwn hR) hbody
  exact cpsTripleWithin_weaken
    (fun _ hp => by
      unfold teerScratchOwn at hp
      unfold teerScratchZeroOwn teerScratchRestOwn
        RegularRefundAddr SuccessCountAddr PredelegatedAddr RolledBackAddr
      xperm_hyp hp)
    (fun _ hq => by
      -- Nested frameR post: (bodyIs ** (Rest ** R)); flatten to bodyIs ** Rest ** R
      xperm_hyp hq) hF

/-- Rebuild full memOwn scratch from Is + Rest (applied_flat exit). -/
theorem teerScratchOwn_of_zeroIs_rest :
    ∀ h, (teerScratchZeroIs ** teerScratchRestOwn) h → teerScratchOwn h := by
  intro h hp
  exact teerScratchOwn_of_zero_rest h
    (sepConj_mono (teerScratchZeroIs_to_own) (fun _ hq => hq) h hp)

#print axioms teerScratchZero_regOwn_is
#print axioms teerScratchZero_fullScratch_is
#print axioms teerScratchOwn_of_zeroIs_rest

/-- Ambient frame after peeling scratch body regs from prologue post. -/
def teerScratchAmbient
    (spC ret loadPtr lenW balPtr balLenW chainIdW baiW
      s5 s6 s7 s8 s9 s11 spVal regionBase : Word)
    (bs balBytes : List (BitVec 8)) (s : TeerSaved) : Assertion :=
  (.x2 ↦ᵣ spC) **
  (.x1 ↦ᵣ ret) **
  (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
  (.x18 ↦ᵣ balPtr) ** (.x19 ↦ᵣ balLenW) ** (.x20 ↦ᵣ chainIdW) **
  (.x21 ↦ᵣ s5) ** (.x22 ↦ᵣ s6) ** (.x23 ↦ᵣ s7) **
  (.x24 ↦ᵣ s8) ** (.x25 ↦ᵣ s9) **
  (.x27 ↦ᵣ s11) ** (.x15 ↦ᵣ baiW) **
  frameSlotsSaved teerFrame spC (teerSavedVals s) **
  (.x10 ↦ᵣ loadPtr) ** (.x11 ↦ᵣ lenW) **
  (.x12 ↦ᵣ balPtr) ** (.x13 ↦ᵣ balLenW) ** (.x14 ↦ᵣ chainIdW) **
  regOwn .x6 ** regOwn .x7 ** regOwn .x16 **
  regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
  stackFree spVal 6 **
  bytesRegion regionBase bs ** bytesRegion balPtr balBytes

private theorem pcFree_teerScratchAmbient
    (spC ret loadPtr lenW balPtr balLenW chainIdW baiW
      s5 s6 s7 s8 s9 s11 spVal regionBase : Word)
    (bs balBytes : List (BitVec 8)) (s : TeerSaved) :
    (teerScratchAmbient spC ret loadPtr lenW balPtr balLenW chainIdW baiW
      s5 s6 s7 s8 s9 s11 spVal regionBase bs balBytes s).pcFree := by
  unfold teerScratchAmbient
  pcf

/-- Prologue post → fullScratch prest. -/
theorem teerProloguePost_to_scratchFullPre
    (spC ret loadPtr lenW balPtr balLenW chainIdW baiW
      s5 s6 s7 s8 s9 s10 s11 spVal regionBase : Word)
    (bs balBytes : List (BitVec 8)) (s : TeerSaved) :
    ∀ h,
      ((.x2 ↦ᵣ spC) **
        (.x1 ↦ᵣ ret) **
        (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
        (.x18 ↦ᵣ balPtr) ** (.x19 ↦ᵣ balLenW) ** (.x20 ↦ᵣ chainIdW) **
        (.x21 ↦ᵣ s5) ** (.x22 ↦ᵣ s6) ** (.x23 ↦ᵣ s7) **
        (.x24 ↦ᵣ s8) ** (.x25 ↦ᵣ s9) ** (.x26 ↦ᵣ s10) **
        (.x27 ↦ᵣ s11) ** (.x15 ↦ᵣ baiW) **
        frameSlotsSaved teerFrame spC (teerSavedVals s) **
        prologueAbiRestOwn loadPtr lenW balPtr balLenW chainIdW **
        stackFree spVal 6 **
        bytesRegion regionBase bs ** bytesRegion balPtr balBytes **
        teerScratchOwn) h →
      (((.x26 ↦ᵣ s10) ** (.x0 ↦ᵣ (0 : Word)) ** teerScratchOwn) **
        regOwn .x5 **
        teerScratchAmbient spC ret loadPtr lenW balPtr balLenW chainIdW baiW
          s5 s6 s7 s8 s9 s11 spVal regionBase bs balBytes s) h := by
  intro h hp
  unfold prologueAbiRestOwn at hp
  unfold teerScratchAmbient
  xperm_hyp hp

/-- Applied entry → AtBalCheck (33). Post keeps fullScratch nested shape. -/
theorem teerPrologueScratch_applied
    (ret spVal spC loadPtr lenW balPtr balLenW chainIdW baiW : Word)
    (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : Word)
    (regionBase : Word) (bs balBytes : List (BitVec 8))
    (hspC : spC = spVal + signExtend12 (-160 : BitVec 12)) :
    let s : TeerSaved :=
      { ra := ret, s0 := s0, s1 := s1, s2 := s2, s3 := s3, s4 := s4
        s5 := s5, s6 := s6, s7 := s7, s8 := s8, s9 := s9
        s10 := s10, s11 := s11, a5 := baiW }
    let amb :=
      teerScratchAmbient spC ret loadPtr lenW balPtr balLenW chainIdW baiW
        s5 s6 s7 s8 s9 s11 spVal regionBase bs balBytes s
    cpsTripleWithin 33 E AtBalCheck teerCode
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
      ((.x26 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ RolledBackAddr) **
        (.x0 ↦ᵣ (0 : Word)) ** teerScratchOwn ** amb) := by
  intro s amb
  have hpro := teerPrologue_applied ret spVal spC loadPtr lenW balPtr balLenW
    chainIdW baiW s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 regionBase bs balBytes hspC
  have hR := pcFree_teerScratchAmbient spC ret loadPtr lenW balPtr balLenW
    chainIdW baiW s5 s6 s7 s8 s9 s11 spVal regionBase bs balBytes s
  have hsc := teerScratchZero_fullScratch s10 amb hR
  have hscW := cpsTripleWithin_weaken
    (teerProloguePost_to_scratchFullPre spC ret loadPtr lenW balPtr balLenW
      chainIdW baiW s5 s6 s7 s8 s9 s10 s11 spVal regionBase bs balBytes s)
    (fun _ hq => hq) hsc
  have hseq := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by
      -- hpro post uses local s from teerPrologue_applied let; align
      simp only [s] at hp ⊢
      exact hp) hpro hscW
  exact cpsTripleWithin_mono_nSteps (by decide : 20 + 13 ≤ 33) hseq

/-- Flatten nested Amb post to applied-style flat post at AtBalCheck. -/
theorem teerPrologueScratch_applied_flat
    (ret spVal spC loadPtr lenW balPtr balLenW chainIdW baiW : Word)
    (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : Word)
    (regionBase : Word) (bs balBytes : List (BitVec 8))
    (hspC : spC = spVal + signExtend12 (-160 : BitVec 12)) :
    let s : TeerSaved :=
      { ra := ret, s0 := s0, s1 := s1, s2 := s2, s3 := s3, s4 := s4
        s5 := s5, s6 := s6, s7 := s7, s8 := s8, s9 := s9
        s10 := s10, s11 := s11, a5 := baiW }
    cpsTripleWithin 33 E AtBalCheck teerCode
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
        teerScratchOwn) := by
  intro s
  have h0 := teerPrologueScratch_applied ret spVal spC loadPtr lenW balPtr balLenW
    chainIdW baiW s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 regionBase bs balBytes hspC
  exact cpsTripleWithin_weaken (fun _ hp => hp)
    (fun _ hq => by
      unfold teerScratchAmbient at hq
      xperm_hyp hq) h0

#print axioms teerPrologueScratch_applied
#print axioms teerPrologueScratch_applied_flat

/-- AtBalCheck flat post → bal BEQ prest (x18/x0) + ambient. -/
theorem teerAtBalCheckFlat_to_balPre
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
      (((.x18 ↦ᵣ balPtr) ** (.x0 ↦ᵣ (0 : Word))) **
        ((.x2 ↦ᵣ spC) **
          (.x1 ↦ᵣ ret) **
          (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
          (.x19 ↦ᵣ balLenW) ** (.x20 ↦ᵣ chainIdW) **
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
          stackFree spVal 6 **
          bytesRegion regionBase bs ** bytesRegion balPtr balBytes **
          teerScratchOwn)) h := by
  intro h hp
  xperm_hyp hp

/-- Applied entry → AfterBalCheck (34) nested post (bal focus ** ambient). -/
theorem teerPrologueScratchBal_applied_nested
    (ret spVal spC loadPtr lenW balPtr balLenW chainIdW baiW : Word)
    (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : Word)
    (regionBase : Word) (bs balBytes : List (BitVec 8))
    (hspC : spC = spVal + signExtend12 (-160 : BitVec 12))
    (hnez : balPtr ≠ (0 : Word)) :
    let s : TeerSaved :=
      { ra := ret, s0 := s0, s1 := s1, s2 := s2, s3 := s3, s4 := s4
        s5 := s5, s6 := s6, s7 := s7, s8 := s8, s9 := s9
        s10 := s10, s11 := s11, a5 := baiW }
    cpsTripleWithin 34 E AfterBalCheck teerCode
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
      (((.x18 ↦ᵣ balPtr) ** (.x0 ↦ᵣ (0 : Word))) **
        ((.x2 ↦ᵣ spC) **
          (.x1 ↦ᵣ ret) **
          (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
          (.x19 ↦ᵣ balLenW) ** (.x20 ↦ᵣ chainIdW) **
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
          stackFree spVal 6 **
          bytesRegion regionBase bs ** bytesRegion balPtr balBytes **
          teerScratchOwn)) := by
  intro s
  have hsc := teerPrologueScratch_applied_flat ret spVal spC loadPtr lenW balPtr
    balLenW chainIdW baiW s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 regionBase bs
    balBytes hspC
  have hbal := teerBalNezBeq balPtr hnez
  have hbalF := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spC) **
      (.x1 ↦ᵣ ret) **
      (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
      (.x19 ↦ᵣ balLenW) ** (.x20 ↦ᵣ chainIdW) **
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
      stackFree spVal 6 **
      bytesRegion regionBase bs ** bytesRegion balPtr balBytes **
      teerScratchOwn) (by pcf) hbal
  have hseq := cpsTripleWithin_seq_perm_same_cr
    (teerAtBalCheckFlat_to_balPre ret spVal spC loadPtr lenW balPtr balLenW
      chainIdW baiW s5 s6 s7 s8 s9 s11 regionBase bs balBytes s)
    hsc hbalF
  exact cpsTripleWithin_mono_nSteps (by decide : 33 + 1 ≤ 34) hseq

/-- Flatten bal nested post to applied-style flat AfterBalCheck post. -/
theorem teerPrologueScratchBal_applied
    (ret spVal spC loadPtr lenW balPtr balLenW chainIdW baiW : Word)
    (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : Word)
    (regionBase : Word) (bs balBytes : List (BitVec 8))
    (hspC : spC = spVal + signExtend12 (-160 : BitVec 12))
    (hnez : balPtr ≠ (0 : Word)) :
    let s : TeerSaved :=
      { ra := ret, s0 := s0, s1 := s1, s2 := s2, s3 := s3, s4 := s4
        s5 := s5, s6 := s6, s7 := s7, s8 := s8, s9 := s9
        s10 := s10, s11 := s11, a5 := baiW }
    cpsTripleWithin 34 E AfterBalCheck teerCode
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
        teerScratchOwn) := by
  intro s
  have h0 := teerPrologueScratchBal_applied_nested ret spVal spC loadPtr lenW balPtr
    balLenW chainIdW baiW s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 regionBase bs
    balBytes hspC hnez
  exact cpsTripleWithin_weaken (fun _ hp => hp)
    (fun _ hq => by xperm_hyp hq) h0

#print axioms teerPrologueScratchBal_applied_nested
#print axioms teerPrologueScratchBal_applied

/-! ## Applied prologue+scratch+bal posting ZeroIs (RolledZero thread) -/

/-- Applied entry → AtBalCheck with `teerScratchZeroIs ** teerScratchRestOwn`. -/
theorem teerPrologueScratch_applied_is
    (ret spVal spC loadPtr lenW balPtr balLenW chainIdW baiW : Word)
    (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : Word)
    (regionBase : Word) (bs balBytes : List (BitVec 8))
    (hspC : spC = spVal + signExtend12 (-160 : BitVec 12)) :
    let s : TeerSaved :=
      { ra := ret, s0 := s0, s1 := s1, s2 := s2, s3 := s3, s4 := s4
        s5 := s5, s6 := s6, s7 := s7, s8 := s8, s9 := s9
        s10 := s10, s11 := s11, a5 := baiW }
    let amb :=
      teerScratchAmbient spC ret loadPtr lenW balPtr balLenW chainIdW baiW
        s5 s6 s7 s8 s9 s11 spVal regionBase bs balBytes s
    cpsTripleWithin 33 E AtBalCheck teerCode
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
      ((.x26 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ RolledBackAddr) **
        (.x0 ↦ᵣ (0 : Word)) ** teerScratchZeroIs ** teerScratchRestOwn ** amb) := by
  intro s amb
  have hpro := teerPrologue_applied ret spVal spC loadPtr lenW balPtr balLenW
    chainIdW baiW s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 regionBase bs balBytes hspC
  have hR := pcFree_teerScratchAmbient spC ret loadPtr lenW balPtr balLenW
    chainIdW baiW s5 s6 s7 s8 s9 s11 spVal regionBase bs balBytes s
  have hsc := teerScratchZero_fullScratch_is s10 amb hR
  have hscW := cpsTripleWithin_weaken
    (teerProloguePost_to_scratchFullPre spC ret loadPtr lenW balPtr balLenW
      chainIdW baiW s5 s6 s7 s8 s9 s10 s11 spVal regionBase bs balBytes s)
    (fun _ hq => hq) hsc
  have hseq := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by
      simp only [s] at hp ⊢
      exact hp) hpro hscW
  exact cpsTripleWithin_mono_nSteps (by decide : 20 + 13 ≤ 33) hseq

/-- Flatten Is nested post at AtBalCheck. -/
theorem teerPrologueScratch_applied_flat_is
    (ret spVal spC loadPtr lenW balPtr balLenW chainIdW baiW : Word)
    (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : Word)
    (regionBase : Word) (bs balBytes : List (BitVec 8))
    (hspC : spC = spVal + signExtend12 (-160 : BitVec 12)) :
    let s : TeerSaved :=
      { ra := ret, s0 := s0, s1 := s1, s2 := s2, s3 := s3, s4 := s4
        s5 := s5, s6 := s6, s7 := s7, s8 := s8, s9 := s9
        s10 := s10, s11 := s11, a5 := baiW }
    cpsTripleWithin 33 E AtBalCheck teerCode
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
        teerScratchZeroIs ** teerScratchRestOwn) := by
  intro s
  have h0 := teerPrologueScratch_applied_is ret spVal spC loadPtr lenW balPtr balLenW
    chainIdW baiW s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 regionBase bs balBytes hspC
  exact cpsTripleWithin_weaken (fun _ hp => hp)
    (fun _ hq => by
      unfold teerScratchAmbient at hq
      xperm_hyp hq) h0

/-- AtBalCheck Is-flat → bal prest + ambient carrying ZeroIs ** RestOwn. -/
theorem teerAtBalCheckFlatIs_to_balPre
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
        teerScratchZeroIs ** teerScratchRestOwn) h →
      (((.x18 ↦ᵣ balPtr) ** (.x0 ↦ᵣ (0 : Word))) **
        ((.x2 ↦ᵣ spC) **
          (.x1 ↦ᵣ ret) **
          (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
          (.x19 ↦ᵣ balLenW) ** (.x20 ↦ᵣ chainIdW) **
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
          stackFree spVal 6 **
          bytesRegion regionBase bs ** bytesRegion balPtr balBytes **
          teerScratchZeroIs ** teerScratchRestOwn)) h := by
  intro h hp
  xperm_hyp hp

/-- Applied entry → AfterBalCheck with ZeroIs ** RestOwn (bal≠0). -/
theorem teerPrologueScratchBal_applied_is
    (ret spVal spC loadPtr lenW balPtr balLenW chainIdW baiW : Word)
    (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : Word)
    (regionBase : Word) (bs balBytes : List (BitVec 8))
    (hspC : spC = spVal + signExtend12 (-160 : BitVec 12))
    (hnez : balPtr ≠ (0 : Word)) :
    let s : TeerSaved :=
      { ra := ret, s0 := s0, s1 := s1, s2 := s2, s3 := s3, s4 := s4
        s5 := s5, s6 := s6, s7 := s7, s8 := s8, s9 := s9
        s10 := s10, s11 := s11, a5 := baiW }
    cpsTripleWithin 34 E AfterBalCheck teerCode
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
        teerScratchZeroIs ** teerScratchRestOwn) := by
  intro s
  have hsc := teerPrologueScratch_applied_flat_is ret spVal spC loadPtr lenW balPtr
    balLenW chainIdW baiW s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 regionBase bs
    balBytes hspC
  have hbal := teerBalNezBeq balPtr hnez
  have hbalF := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spC) **
      (.x1 ↦ᵣ ret) **
      (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
      (.x19 ↦ᵣ balLenW) ** (.x20 ↦ᵣ chainIdW) **
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
      stackFree spVal 6 **
      bytesRegion regionBase bs ** bytesRegion balPtr balBytes **
      teerScratchZeroIs ** teerScratchRestOwn) (by
      unfold teerScratchZeroIs teerScratchRestOwn
      pcf) hbal
  have hseq := cpsTripleWithin_seq_perm_same_cr
    (teerAtBalCheckFlatIs_to_balPre ret spVal spC loadPtr lenW balPtr balLenW
      chainIdW baiW s5 s6 s7 s8 s9 s11 regionBase bs balBytes s)
    hsc hbalF
  have hnest := cpsTripleWithin_mono_nSteps (by decide : 33 + 1 ≤ 34) hseq
  exact cpsTripleWithin_weaken (fun _ hp => hp)
    (fun _ hq => by xperm_hyp hq) hnest

#print axioms teerPrologueScratch_applied_is
#print axioms teerPrologueScratch_applied_flat_is
#print axioms teerPrologueScratchBal_applied_is

end EvmAsm.Codegen.TxEip7702TeerSpec
