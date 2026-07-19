/-
  Teer auth-loop after rolled join:
  AfterRolledJoin (E+2168) la/ld teer_prior_count;
  BNE ≠0 → AfterPriorJoin (E+2384) skips absent/auth/value block;
  fallthrough prior==0 residual (acct_absent + 20B cmp + …).
-/

import EvmAsm.Codegen.Programs.TxEip7702TeerAuthLoopRolledBack
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.LaResolve
import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic

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
    | exact bytesRegion_pcFree _ _)

abbrev AfterLaPriorPc : Word := E + 2176
abbrev AfterLdPriorPc : Word := E + 2180
abbrev AfterPriorBeqNtaken : Word := E + 2184
/-- Join after prior≠0 skip / end of prior==0 block (MV x7,x27). -/
abbrev AfterPriorJoin : Word := E + 2384

abbrev teerPriorBneOff : BitVec 13 := (204 : BitVec 13)

theorem teerPriorBneOff_taken :
    AfterLdPriorPc + signExtend13 teerPriorBneOff = AfterPriorJoin := by
  simp only [AfterLdPriorPc, AfterPriorJoin, teerPriorBneOff, E]; decide

private theorem se12_zero_pc : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide

/-- `la x5, teer_prior_count` AfterRolledJoin. -/
theorem teerLaPriorPc (v : Word) :
    cpsTripleWithin 2 AfterRolledJoin AfterLaPriorPc teerLinkedField0
      (.x5 ↦ᵣ v) (.x5 ↦ᵣ PriorCountAddr) := by
  have hau : ∀ a i, CodeReq.singleton AfterRolledJoin
      (.AUIPC .x5 (Codegen.laHi GuestAddrs.teer_prior_count
        (GuestAddrs.tx_eip7702_existing_authority_refund + 2168)))
        a = some i → teerLinkedField0 a = some i := fun a i hi =>
    teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterRolledJoin teerProg 542
        (.AUIPC .x5 (Codegen.laHi GuestAddrs.teer_prior_count
          (GuestAddrs.tx_eip7702_existing_authority_refund + 2168)))
        (by simp only [AfterRolledJoin]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)
  have had : ∀ a i, CodeReq.singleton (E + 2172)
      (.ADDI .x5 .x5 (Codegen.laLo GuestAddrs.teer_prior_count
        (GuestAddrs.tx_eip7702_existing_authority_refund + 2168)))
        a = some i → teerLinkedField0 a = some i := fun a i hi =>
    teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E (E + 2172) teerProg 543
        (.ADDI .x5 .x5 (Codegen.laLo GuestAddrs.teer_prior_count
          (GuestAddrs.tx_eip7702_existing_authority_refund + 2168)))
        (by bv_omega) (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi)
  have h := la_materialize_within .x5 v AfterRolledJoin PriorCountAddr
    (by decide) (by decide) hau had
  rw [show (AfterRolledJoin : Word) + 8 = AfterLaPriorPc from by
    simp only [AfterRolledJoin, AfterLaPriorPc]; bv_omega] at h
  exact h

/-- `ld x6, 0(x5)` prior_count. -/
theorem teerLdPriorPc (prior t1Old : Word) :
    cpsTripleWithin 1 AfterLaPriorPc AfterLdPriorPc teerLinkedField0
      ((.x5 ↦ᵣ PriorCountAddr) ** (.x6 ↦ᵣ t1Old) ** (PriorCountAddr ↦ₘ prior))
      ((.x5 ↦ᵣ PriorCountAddr) ** (.x6 ↦ᵣ prior) ** (PriorCountAddr ↦ₘ prior)) := by
  have h0 := ld_spec_gen_within .x6 .x5 PriorCountAddr t1Old prior
    (0 : BitVec 12) AfterLaPriorPc (by decide)
  rw [show PriorCountAddr + signExtend12 (0 : BitVec 12) = PriorCountAddr from by
    rw [se12_zero_pc]; exact BitVec.add_zero PriorCountAddr] at h0
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterLaPriorPc teerProg 544
        (.LD .x6 .x5 (0 : BitVec 12))
        (by simp only [AfterLaPriorPc]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : AfterLaPriorPc + 4 = AfterLdPriorPc := by
    simp only [AfterLaPriorPc, AfterLdPriorPc]; bv_omega
  rw [hpc] at e0
  exact e0

/-- `bne x6, x0` taken: prior ≠ 0 → AfterPriorJoin. -/
theorem teerPriorBneTaken (prior : Word) (hne : prior ≠ (0 : Word)) :
    cpsTripleWithin 1 AfterLdPriorPc AfterPriorJoin teerLinkedField0
      ((.x6 ↦ᵣ prior) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x6 ↦ᵣ prior) ** (.x0 ↦ᵣ (0 : Word))) := by
  have hbr := bne_spec_gen_within .x6 .x0 teerPriorBneOff
    prior (0 : Word) AfterLdPriorPc
  rw [teerPriorBneOff_taken] at hbr
  exact cpsBranchWithin_takenStripPure2
    (cpsBranchWithin_extend_code
      (fun a i hi => teerField0_mono_teer a i
        (CodeReq.ofProg_mem_at E AfterLdPriorPc teerProg 545
          (.BNE .x6 .x0 teerPriorBneOff)
          (by simp only [AfterLdPriorPc]; bv_omega)
          (by rw [teer_length]; decide) rfl
          (by rw [teer_length]; decide) a i hi)) hbr)
    (fun _ hQf => by
      obtain ⟨_, _, _, _, _, hBP⟩ := hQf
      exact absurd ((sepConj_pure_right _).1 hBP).2 hne)

/-- `bne x6, x0` ntaken: prior = 0 → fallthrough. -/
theorem teerPriorBneNtaken_zero :
    cpsTripleWithin 1 AfterLdPriorPc AfterPriorBeqNtaken teerLinkedField0
      ((.x6 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x6 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) := by
  have hbr := bne_spec_gen_within .x6 .x0 teerPriorBneOff
    (0 : Word) (0 : Word) AfterLdPriorPc
  change cpsBranchWithin _ _ _ _ _ _ AfterPriorBeqNtaken _ at hbr
  exact cpsBranchWithin_ntakenStripPure2
    (cpsBranchWithin_extend_code
      (fun a i hi => teerField0_mono_teer a i
        (CodeReq.ofProg_mem_at E AfterLdPriorPc teerProg 545
          (.BNE .x6 .x0 teerPriorBneOff)
          (by simp only [AfterLdPriorPc]; bv_omega)
          (by rw [teer_length]; decide) rfl
          (by rw [teer_length]; decide) a i hi)) hbr)
    (fun _ hQt => by
      obtain ⟨_, _, _, _, _, hBP⟩ := hQt
      exact ((sepConj_pure_right _).1 hBP).2 rfl)

/-- prior ≠ 0 skip: AfterRolledJoin → AfterPriorJoin (4 steps). -/
theorem teerPriorNezSkip
    (prior t0Old t1Old : Word) (hne : prior ≠ (0 : Word)) :
    cpsTripleWithin 4 AfterRolledJoin AfterPriorJoin teerLinkedField0
      ((.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x0 ↦ᵣ (0 : Word)) **
        (PriorCountAddr ↦ₘ prior))
      ((.x5 ↦ᵣ PriorCountAddr) ** (.x6 ↦ᵣ prior) ** (.x0 ↦ᵣ (0 : Word)) **
        (PriorCountAddr ↦ₘ prior)) := by
  have hla := teerLaPriorPc t0Old
  have hlaF := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ t1Old) ** (.x0 ↦ᵣ (0 : Word)) ** (PriorCountAddr ↦ₘ prior))
    (by pcf) hla
  have hld := teerLdPriorPc prior t1Old
  have hldF := cpsTripleWithin_frameR
    ((.x0 ↦ᵣ (0 : Word))) (by pcf) hld
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hlaF hldF
  have hbr := teerPriorBneTaken prior hne
  have hbrF := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ PriorCountAddr) ** (PriorCountAddr ↦ₘ prior)) (by pcf) hbr
  have c12 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c01 hbrF
  exact cpsTripleWithin_mono_nSteps (by decide : (2 + 1 + 1 : Nat) ≤ 4)
    (cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => by xperm_hyp hq) c12)

/-- prior = 0 fallthrough load: AfterRolledJoin → AfterPriorBeqNtaken. -/
theorem teerPriorZeroFallthrough (t0Old t1Old : Word) :
    cpsTripleWithin 4 AfterRolledJoin AfterPriorBeqNtaken teerLinkedField0
      ((.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x0 ↦ᵣ (0 : Word)) **
        (PriorCountAddr ↦ₘ (0 : Word)))
      ((.x5 ↦ᵣ PriorCountAddr) ** (.x6 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        (PriorCountAddr ↦ₘ (0 : Word))) := by
  have hla := teerLaPriorPc t0Old
  have hlaF := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ t1Old) ** (.x0 ↦ᵣ (0 : Word)) ** (PriorCountAddr ↦ₘ (0 : Word)))
    (by pcf) hla
  have hld := teerLdPriorPc (0 : Word) t1Old
  have hldF := cpsTripleWithin_frameR
    ((.x0 ↦ᵣ (0 : Word))) (by pcf) hld
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hlaF hldF
  have hbr := teerPriorBneNtaken_zero
  have hbrF := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ PriorCountAddr) ** (PriorCountAddr ↦ₘ (0 : Word))) (by pcf) hbr
  have c12 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c01 hbrF
  exact cpsTripleWithin_mono_nSteps (by decide : (2 + 1 + 1 : Nat) ≤ 4)
    (cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => by xperm_hyp hq) c12)

#print axioms teerLaPriorPc
#print axioms teerPriorNezSkip
#print axioms teerPriorZeroFallthrough

end EvmAsm.Codegen.TxEip7702TeerSpec
