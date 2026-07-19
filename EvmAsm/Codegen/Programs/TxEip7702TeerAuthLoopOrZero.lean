/-
  Teer auth-loop AfterPriorJoin (E+2384):
  MV x7←x27; LI x28,20; LI x29,0; 20B OR-reduce over authority (Assumed);
  BEQ OR==0 → AtSuccessCount (E+2708) skip prior_set/code_at2.
-/

import EvmAsm.Codegen.Programs.TxEip7702TeerAuthLoopPrior
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.LaResolve
import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic

namespace EvmAsm.Codegen.TxEip7702TeerSpec

open EvmAsm.Rv64
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
    | exact bytesRegion_pcFree _ _)

abbrev AfterMvAuthPtr : Word := E + 2388
abbrev AfterLi20Oz : Word := E + 2392
abbrev AfterLi0Oz : Word := E + 2396
/-- After OR-zero loop (falls through BEQ counter==0 at loop head). -/
abbrev AfterOrZeroLoop : Word := E + 2420
/-- `beq x29,x0` target when OR-acc == 0 (skip to success_count). -/
abbrev AtSuccessCount : Word := E + 2708

abbrev teerOrZeroBeqOff : BitVec 13 := (288 : BitVec 13)

theorem teerOrZeroBeqOff_taken :
    AfterOrZeroLoop + signExtend13 teerOrZeroBeqOff = AtSuccessCount := by
  simp only [AfterOrZeroLoop, AtSuccessCount, teerOrZeroBeqOff, E]; decide

/-- Named hyp: 20B OR-reduce over authority bytes at x7.
    Prest AfterLi0Oz (x28=20, x29=0, x7=authPtr).
    Post AfterOrZeroLoop with x29 = OR of 20 bytes (caller supplies). -/
structure TeerAuthOrZeroAssumed (cr : CodeReq) where
  nSteps : Nat
  or_flat :
    ∀ (authPtr orAcc : Word),
      cpsTripleWithin nSteps AfterLi0Oz AfterOrZeroLoop cr
        ((.x7 ↦ᵣ authPtr) ** (.x28 ↦ᵣ (20 : Word)) ** (.x29 ↦ᵣ (0 : Word)) **
          regOwn .x30 **
          memOwn authPtr **
          (.x0 ↦ᵣ (0 : Word)))
        ((.x7 ↦ᵣ (authPtr + (20 : Word))) **
          (.x28 ↦ᵣ (0 : Word)) ** (.x29 ↦ᵣ orAcc) **
          regOwn .x30 **
          memOwn authPtr **
          (.x0 ↦ᵣ (0 : Word)))

/-- `mv x7, x27` AfterPriorJoin. -/
theorem teerMvAuthPtrOz (authPtr x7Old : Word) :
    cpsTripleWithin 1 AfterPriorJoin AfterMvAuthPtr teerLinkedField0
      ((.x7 ↦ᵣ x7Old) ** (.x27 ↦ᵣ authPtr))
      ((.x7 ↦ᵣ authPtr) ** (.x27 ↦ᵣ authPtr)) := by
  have h0 := mv_spec_gen_within .x7 .x27 authPtr x7Old AfterPriorJoin (by decide)
  have h1 := cpsTripleWithin_extend_code
    (fun a i hi => teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterPriorJoin teerProg 596
        (.MV .x7 .x27) (by simp only [AfterPriorJoin]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : (AfterPriorJoin + 4 : Word) = AfterMvAuthPtr := by
    simp only [AfterPriorJoin, AfterMvAuthPtr]; bv_omega
  rw [hpc] at h1
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) h1

/-- `li x28, 20` AfterMvAuthPtr. -/
theorem teerLi20Oz (v : Word) :
    cpsTripleWithin 1 AfterMvAuthPtr AfterLi20Oz teerLinkedField0
      (.x28 ↦ᵣ v) (.x28 ↦ᵣ (20 : Word)) := by
  have h0 := li_spec_gen_within .x28 v (20 : Word) AfterMvAuthPtr (by decide)
  have h1 := cpsTripleWithin_extend_code
    (fun a i hi => teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterMvAuthPtr teerProg 597
        (.LI .x28 (20 : Word)) (by simp only [AfterMvAuthPtr]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : (AfterMvAuthPtr + 4 : Word) = AfterLi20Oz := by
    simp only [AfterMvAuthPtr, AfterLi20Oz]; bv_omega
  rw [hpc] at h1
  exact h1

/-- `li x29, 0` AfterLi20Oz. -/
theorem teerLi0Oz (v : Word) :
    cpsTripleWithin 1 AfterLi20Oz AfterLi0Oz teerLinkedField0
      (.x29 ↦ᵣ v) (.x29 ↦ᵣ (0 : Word)) := by
  have h0 := li_spec_gen_within .x29 v (0 : Word) AfterLi20Oz (by decide)
  have h1 := cpsTripleWithin_extend_code
    (fun a i hi => teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterLi20Oz teerProg 598
        (.LI .x29 (0 : Word)) (by simp only [AfterLi20Oz]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : (AfterLi20Oz + 4 : Word) = AfterLi0Oz := by
    simp only [AfterLi20Oz, AfterLi0Oz]; bv_omega
  rw [hpc] at h1
  exact h1

/-- Setup through LI 0: AfterPriorJoin → AfterLi0Oz (3 steps). -/
theorem teerOrZeroSetup (authPtr x7Old x28Old x29Old : Word) :
    cpsTripleWithin 3 AfterPriorJoin AfterLi0Oz teerLinkedField0
      ((.x7 ↦ᵣ x7Old) ** (.x27 ↦ᵣ authPtr) **
        (.x28 ↦ᵣ x28Old) ** (.x29 ↦ᵣ x29Old))
      ((.x7 ↦ᵣ authPtr) ** (.x27 ↦ᵣ authPtr) **
        (.x28 ↦ᵣ (20 : Word)) ** (.x29 ↦ᵣ (0 : Word))) := by
  have hmv := teerMvAuthPtrOz authPtr x7Old
  have hmvF := cpsTripleWithin_frameR
    ((.x28 ↦ᵣ x28Old) ** (.x29 ↦ᵣ x29Old)) (by pcf) hmv
  have hli20 := teerLi20Oz x28Old
  have hli20F := cpsTripleWithin_frameR
    ((.x7 ↦ᵣ authPtr) ** (.x27 ↦ᵣ authPtr) ** (.x29 ↦ᵣ x29Old)) (by pcf) hli20
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hmvF hli20F
  have hli0 := teerLi0Oz x29Old
  have hli0F := cpsTripleWithin_frameR
    ((.x7 ↦ᵣ authPtr) ** (.x27 ↦ᵣ authPtr) ** (.x28 ↦ᵣ (20 : Word))) (by pcf) hli0
  have c12 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c01 hli0F
  exact cpsTripleWithin_mono_nSteps (by decide : (1 + 1 + 1 : Nat) ≤ 3)
    (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) c12)

/-- `beq x29, x0` taken: OR-acc = 0 → AtSuccessCount. -/
theorem teerOrZeroBeqTaken_zero :
    cpsTripleWithin 1 AfterOrZeroLoop AtSuccessCount teerLinkedField0
      ((.x29 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x29 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) := by
  have hbr := beq_spec_gen_within .x29 .x0 teerOrZeroBeqOff
    (0 : Word) (0 : Word) AfterOrZeroLoop
  rw [teerOrZeroBeqOff_taken] at hbr
  exact cpsBranchWithin_takenStripPure2
    (cpsBranchWithin_extend_code
      (fun a i hi => teerField0_mono_teer a i
        (CodeReq.ofProg_mem_at E AfterOrZeroLoop teerProg 605
          (.BEQ .x29 .x0 teerOrZeroBeqOff)
          (by simp only [AfterOrZeroLoop]; bv_omega)
          (by rw [teer_length]; decide) rfl
          (by rw [teer_length]; decide) a i hi)) hbr)
    (fun _ hQf => by
      obtain ⟨_, _, _, _, _, hBP⟩ := hQf
      exact ((sepConj_pure_right _).1 hBP).2 rfl)

/-- `beq x29, x0` ntaken: OR-acc ≠ 0 → fallthrough prior_set. -/
theorem teerOrZeroBeqNtaken (orAcc : Word) (hne : orAcc ≠ (0 : Word)) :
    cpsTripleWithin 1 AfterOrZeroLoop (AfterOrZeroLoop + 4) teerLinkedField0
      ((.x29 ↦ᵣ orAcc) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x29 ↦ᵣ orAcc) ** (.x0 ↦ᵣ (0 : Word))) := by
  have hbr := beq_spec_gen_within .x29 .x0 teerOrZeroBeqOff
    orAcc (0 : Word) AfterOrZeroLoop
  change cpsBranchWithin _ _ _ _ _ _ (AfterOrZeroLoop + 4) _ at hbr
  exact cpsBranchWithin_ntakenStripPure2
    (cpsBranchWithin_extend_code
      (fun a i hi => teerField0_mono_teer a i
        (CodeReq.ofProg_mem_at E AfterOrZeroLoop teerProg 605
          (.BEQ .x29 .x0 teerOrZeroBeqOff)
          (by simp only [AfterOrZeroLoop]; bv_omega)
          (by rw [teer_length]; decide) rfl
          (by rw [teer_length]; decide) a i hi)) hbr)
    (fun _ hQt => by
      obtain ⟨_, _, _, _, _, hBP⟩ := hQt
      exact absurd ((sepConj_pure_right _).1 hBP).2 hne)

/-- Setup + Assumed OR loop + BEQ zero → AtSuccessCount. -/
theorem teerOrZeroThenSuccessSkip (hAssumed : TeerAuthOrZeroAssumed teerLinkedField0)
    (authPtr x7Old x28Old x29Old : Word) :
    cpsTripleWithin (3 + hAssumed.nSteps + 1) AfterPriorJoin AtSuccessCount
      teerLinkedField0
      ((.x7 ↦ᵣ x7Old) ** (.x27 ↦ᵣ authPtr) **
        (.x28 ↦ᵣ x28Old) ** (.x29 ↦ᵣ x29Old) **
        regOwn .x30 ** memOwn authPtr ** (.x0 ↦ᵣ (0 : Word)))
      ((.x7 ↦ᵣ (authPtr + (20 : Word))) ** (.x27 ↦ᵣ authPtr) **
        (.x28 ↦ᵣ (0 : Word)) ** (.x29 ↦ᵣ (0 : Word)) **
        regOwn .x30 ** memOwn authPtr ** (.x0 ↦ᵣ (0 : Word))) := by
  have hsetup := teerOrZeroSetup authPtr x7Old x28Old x29Old
  have hsetupF := cpsTripleWithin_frameR
    (regOwn .x30 ** memOwn authPtr ** (.x0 ↦ᵣ (0 : Word))) (by pcf) hsetup
  have hor := hAssumed.or_flat authPtr (0 : Word)
  have horF := cpsTripleWithin_frameR (.x27 ↦ᵣ authPtr) (by pcf) hor
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hsetupF horF
  have hbeq := teerOrZeroBeqTaken_zero
  have hbeqF := cpsTripleWithin_frameR
    ((.x7 ↦ᵣ (authPtr + (20 : Word))) ** (.x27 ↦ᵣ authPtr) **
      (.x28 ↦ᵣ (0 : Word)) ** regOwn .x30 ** memOwn authPtr) (by pcf) hbeq
  have c12 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c01 hbeqF
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) c12

#print axioms teerOrZeroSetup
#print axioms teerOrZeroBeqTaken_zero
#print axioms teerOrZeroThenSuccessSkip

end EvmAsm.Codegen.TxEip7702TeerSpec
