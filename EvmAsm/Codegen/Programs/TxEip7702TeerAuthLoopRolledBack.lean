/-
  Teer auth-loop after nonce-eq:
  AfterNonceEq (E+2100) → AfterRolledJoin (E+2168):
    la/ld teer_acct_ptr; beq ==0 skip → join;
    la/ld finals+40; beq ==0 → set rolled;
    la/ld finals+48; ld nonce@144(sp); bltu nonce < finals skip set;
    else la/sd teer_rolled_back := 1 → join.
-/

import EvmAsm.Codegen.Programs.TxEip7702TeerAuthLoopNonceJoin
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

abbrev AfterLaAcctPtrRb : Word := E + 2108
abbrev AfterLdAcctPtrRb : Word := E + 2112
abbrev AfterAcctPtrBeqNtaken : Word := E + 2116
abbrev AfterLaFinals40 : Word := E + 2124
abbrev AfterLdFinals40 : Word := E + 2128
abbrev AfterFinals40BeqNtaken : Word := E + 2132
abbrev AfterLaFinals48 : Word := E + 2140
abbrev AfterLdFinals48 : Word := E + 2144
abbrev AfterLdNonceRb : Word := E + 2148
abbrev AfterBltuNtaken : Word := E + 2152
abbrev AfterLaRolled : Word := E + 2160
abbrev AfterLiRolled1 : Word := E + 2164
abbrev AfterSdRolled : Word := E + 2168
/-- Join after acct/finals/rolled skips (prior_count la). -/
abbrev AfterRolledJoin : Word := E + 2168

abbrev teerAcctPtrBeqOff : BitVec 13 := (56 : BitVec 13)
abbrev teerFinals40BeqOff : BitVec 13 := (24 : BitVec 13)
abbrev teerNonceBltuOff : BitVec 13 := (20 : BitVec 13)

theorem teerAcctPtrBeqOff_taken :
    AfterLdAcctPtrRb + signExtend13 teerAcctPtrBeqOff = AfterRolledJoin := by
  simp only [AfterLdAcctPtrRb, AfterRolledJoin, teerAcctPtrBeqOff, E]; decide

theorem teerFinals40BeqOff_taken :
    AfterLdFinals40 + signExtend13 teerFinals40BeqOff = AfterBltuNtaken := by
  simp only [AfterLdFinals40, AfterBltuNtaken, teerFinals40BeqOff, E]; decide

theorem teerNonceBltuOff_taken :
    AfterLdNonceRb + signExtend13 teerNonceBltuOff = AfterRolledJoin := by
  simp only [AfterLdNonceRb, AfterRolledJoin, teerNonceBltuOff, E]; decide

private theorem se12_zero_rb : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
private theorem se12_40_rb : signExtend12 (40 : BitVec 12) = (40 : Word) := by decide
private theorem se12_48_rb : signExtend12 (48 : BitVec 12) = (48 : Word) := by decide
private theorem se12_144_rb : signExtend12 (144 : BitVec 12) = (144 : Word) := by decide

/-- `la x5, teer_acct_ptr` AfterNonceEq → AfterLaAcctPtrRb. -/
theorem teerLaAcctPtrRb (v : Word) :
    cpsTripleWithin 2 AfterNonceEq AfterLaAcctPtrRb teerLinkedField0
      (.x5 ↦ᵣ v) (.x5 ↦ᵣ AcctPtrAddr) := by
  have hau : ∀ a i, CodeReq.singleton AfterNonceEq
      (.AUIPC .x5 (Codegen.laHi GuestAddrs.teer_acct_ptr
        (GuestAddrs.tx_eip7702_existing_authority_refund + 2100)))
        a = some i → teerLinkedField0 a = some i := fun a i hi =>
    teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterNonceEq teerProg 525
        (.AUIPC .x5 (Codegen.laHi GuestAddrs.teer_acct_ptr
          (GuestAddrs.tx_eip7702_existing_authority_refund + 2100)))
        (by simp only [AfterNonceEq]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)
  have had : ∀ a i, CodeReq.singleton (E + 2104)
      (.ADDI .x5 .x5 (Codegen.laLo GuestAddrs.teer_acct_ptr
        (GuestAddrs.tx_eip7702_existing_authority_refund + 2100)))
        a = some i → teerLinkedField0 a = some i := fun a i hi =>
    teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E (E + 2104) teerProg 526
        (.ADDI .x5 .x5 (Codegen.laLo GuestAddrs.teer_acct_ptr
          (GuestAddrs.tx_eip7702_existing_authority_refund + 2100)))
        (by bv_omega) (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi)
  have h := la_materialize_within .x5 v AfterNonceEq AcctPtrAddr
    (by decide) (by decide) hau had
  rw [show (AfterNonceEq : Word) + 8 = AfterLaAcctPtrRb from by
    simp only [AfterNonceEq, AfterLaAcctPtrRb]; bv_omega] at h
  exact h

/-- `ld x6, 0(x5)` acct_ptr. -/
theorem teerLdAcctPtrRb (acctPtr t1Old : Word) :
    cpsTripleWithin 1 AfterLaAcctPtrRb AfterLdAcctPtrRb teerLinkedField0
      ((.x5 ↦ᵣ AcctPtrAddr) ** (.x6 ↦ᵣ t1Old) ** (AcctPtrAddr ↦ₘ acctPtr))
      ((.x5 ↦ᵣ AcctPtrAddr) ** (.x6 ↦ᵣ acctPtr) ** (AcctPtrAddr ↦ₘ acctPtr)) := by
  have h0 := ld_spec_gen_within .x6 .x5 AcctPtrAddr t1Old acctPtr
    (0 : BitVec 12) AfterLaAcctPtrRb (by decide)
  rw [show AcctPtrAddr + signExtend12 (0 : BitVec 12) = AcctPtrAddr from by
    rw [se12_zero_rb]; exact BitVec.add_zero AcctPtrAddr] at h0
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterLaAcctPtrRb teerProg 527
        (.LD .x6 .x5 (0 : BitVec 12))
        (by simp only [AfterLaAcctPtrRb]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : AfterLaAcctPtrRb + 4 = AfterLdAcctPtrRb := by
    simp only [AfterLaAcctPtrRb, AfterLdAcctPtrRb]; bv_omega
  rw [hpc] at e0
  exact e0

/-- `beq x6, x0` taken: acct_ptr = 0 → AfterRolledJoin. -/
theorem teerAcctPtrBeqTaken_zero :
    cpsTripleWithin 1 AfterLdAcctPtrRb AfterRolledJoin teerLinkedField0
      ((.x6 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x6 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) := by
  have hbeq := beq_spec_gen_within .x6 .x0 teerAcctPtrBeqOff
    (0 : Word) (0 : Word) AfterLdAcctPtrRb
  rw [teerAcctPtrBeqOff_taken] at hbeq
  exact cpsBranchWithin_takenStripPure2
    (cpsBranchWithin_extend_code
      (fun a i hi => teerField0_mono_teer a i
        (CodeReq.ofProg_mem_at E AfterLdAcctPtrRb teerProg 528
          (.BEQ .x6 .x0 teerAcctPtrBeqOff)
          (by simp only [AfterLdAcctPtrRb]; bv_omega)
          (by rw [teer_length]; decide) rfl
          (by rw [teer_length]; decide) a i hi)) hbeq)
    (fun _ hQf => by
      obtain ⟨_, _, _, _, _, hBP⟩ := hQf
      exact ((sepConj_pure_right _).1 hBP).2 rfl)

/-- `beq x6, x0` ntaken: acct_ptr ≠ 0. -/
theorem teerAcctPtrBeqNtaken (acctPtr : Word) (hne : acctPtr ≠ (0 : Word)) :
    cpsTripleWithin 1 AfterLdAcctPtrRb AfterAcctPtrBeqNtaken teerLinkedField0
      ((.x6 ↦ᵣ acctPtr) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x6 ↦ᵣ acctPtr) ** (.x0 ↦ᵣ (0 : Word))) := by
  have hbeq := beq_spec_gen_within .x6 .x0 teerAcctPtrBeqOff
    acctPtr (0 : Word) AfterLdAcctPtrRb
  change cpsBranchWithin _ _ _ _ _ _ AfterAcctPtrBeqNtaken _ at hbeq
  exact cpsBranchWithin_ntakenStripPure2
    (cpsBranchWithin_extend_code
      (fun a i hi => teerField0_mono_teer a i
        (CodeReq.ofProg_mem_at E AfterLdAcctPtrRb teerProg 528
          (.BEQ .x6 .x0 teerAcctPtrBeqOff)
          (by simp only [AfterLdAcctPtrRb]; bv_omega)
          (by rw [teer_length]; decide) rfl
          (by rw [teer_length]; decide) a i hi)) hbeq)
    (fun _ hQt => by
      obtain ⟨_, _, _, _, _, hBP⟩ := hQt
      exact absurd ((sepConj_pure_right _).1 hBP).2 hne)

/-- la/ld acct_ptr + beq ntaken: AfterNonceEq → AfterAcctPtrBeqNtaken. -/
theorem teerAcctPtrLoadNez
    (acctPtr t0Old t1Old : Word) (hne : acctPtr ≠ (0 : Word)) :
    cpsTripleWithin 4 AfterNonceEq AfterAcctPtrBeqNtaken teerLinkedField0
      ((.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x0 ↦ᵣ (0 : Word)) **
        (AcctPtrAddr ↦ₘ acctPtr))
      ((.x5 ↦ᵣ AcctPtrAddr) ** (.x6 ↦ᵣ acctPtr) ** (.x0 ↦ᵣ (0 : Word)) **
        (AcctPtrAddr ↦ₘ acctPtr)) := by
  have hla := teerLaAcctPtrRb t0Old
  have hlaF := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ t1Old) ** (.x0 ↦ᵣ (0 : Word)) ** (AcctPtrAddr ↦ₘ acctPtr))
    (by pcf) hla
  have hld := teerLdAcctPtrRb acctPtr t1Old
  have hldF := cpsTripleWithin_frameR
    ((.x0 ↦ᵣ (0 : Word))) (by pcf) hld
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hlaF hldF
  have hbne := teerAcctPtrBeqNtaken acctPtr hne
  have hbneF := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ AcctPtrAddr) ** (AcctPtrAddr ↦ₘ acctPtr)) (by pcf) hbne
  have c12 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c01 hbneF
  exact cpsTripleWithin_mono_nSteps (by decide : (2 + 1 + 1 : Nat) ≤ 4)
    (cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => by xperm_hyp hq) c12)

/-- Empty acct_ptr skip: AfterNonceEq → AfterRolledJoin. -/
theorem teerAcctPtrZeroSkip (t0Old t1Old : Word) :
    cpsTripleWithin 4 AfterNonceEq AfterRolledJoin teerLinkedField0
      ((.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x0 ↦ᵣ (0 : Word)) **
        (AcctPtrAddr ↦ₘ (0 : Word)))
      ((.x5 ↦ᵣ AcctPtrAddr) ** (.x6 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        (AcctPtrAddr ↦ₘ (0 : Word))) := by
  have hla := teerLaAcctPtrRb t0Old
  have hlaF := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ t1Old) ** (.x0 ↦ᵣ (0 : Word)) ** (AcctPtrAddr ↦ₘ (0 : Word)))
    (by pcf) hla
  have hld := teerLdAcctPtrRb (0 : Word) t1Old
  have hldF := cpsTripleWithin_frameR
    ((.x0 ↦ᵣ (0 : Word))) (by pcf) hld
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hlaF hldF
  have hbeq := teerAcctPtrBeqTaken_zero
  have hbeqF := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ AcctPtrAddr) ** (AcctPtrAddr ↦ₘ (0 : Word))) (by pcf) hbeq
  have c12 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c01 hbeqF
  exact cpsTripleWithin_mono_nSteps (by decide : (2 + 1 + 1 : Nat) ≤ 4)
    (cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => by xperm_hyp hq) c12)

/-- `la x5, teer_finals` AfterAcctPtrBeqNtaken. -/
theorem teerLaFinals40 (v : Word) :
    cpsTripleWithin 2 AfterAcctPtrBeqNtaken AfterLaFinals40 teerLinkedField0
      (.x5 ↦ᵣ v) (.x5 ↦ᵣ FinalsAddr) := by
  have hau : ∀ a i, CodeReq.singleton AfterAcctPtrBeqNtaken
      (.AUIPC .x5 (Codegen.laHi GuestAddrs.teer_finals
        (GuestAddrs.tx_eip7702_existing_authority_refund + 2116)))
        a = some i → teerLinkedField0 a = some i := fun a i hi =>
    teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterAcctPtrBeqNtaken teerProg 529
        (.AUIPC .x5 (Codegen.laHi GuestAddrs.teer_finals
          (GuestAddrs.tx_eip7702_existing_authority_refund + 2116)))
        (by simp only [AfterAcctPtrBeqNtaken]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)
  have had : ∀ a i, CodeReq.singleton (E + 2120)
      (.ADDI .x5 .x5 (Codegen.laLo GuestAddrs.teer_finals
        (GuestAddrs.tx_eip7702_existing_authority_refund + 2116)))
        a = some i → teerLinkedField0 a = some i := fun a i hi =>
    teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E (E + 2120) teerProg 530
        (.ADDI .x5 .x5 (Codegen.laLo GuestAddrs.teer_finals
          (GuestAddrs.tx_eip7702_existing_authority_refund + 2116)))
        (by bv_omega) (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi)
  have h := la_materialize_within .x5 v AfterAcctPtrBeqNtaken FinalsAddr
    (by decide) (by decide) hau had
  rw [show (AfterAcctPtrBeqNtaken : Word) + 8 = AfterLaFinals40 from by
    simp only [AfterAcctPtrBeqNtaken, AfterLaFinals40]; bv_omega] at h
  exact h

/-- `ld x6, 40(x5)` finals field. -/
theorem teerLdFinals40 (f40 t1Old : Word) :
    cpsTripleWithin 1 AfterLaFinals40 AfterLdFinals40 teerLinkedField0
      ((.x5 ↦ᵣ FinalsAddr) ** (.x6 ↦ᵣ t1Old) **
        ((FinalsAddr + (40 : Word)) ↦ₘ f40))
      ((.x5 ↦ᵣ FinalsAddr) ** (.x6 ↦ᵣ f40) **
        ((FinalsAddr + (40 : Word)) ↦ₘ f40)) := by
  have h0 := ld_spec_gen_within .x6 .x5 FinalsAddr t1Old f40
    (40 : BitVec 12) AfterLaFinals40 (by decide)
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterLaFinals40 teerProg 531
        (.LD .x6 .x5 (40 : BitVec 12))
        (by simp only [AfterLaFinals40]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have e1 : cpsTripleWithin 1 AfterLaFinals40 (AfterLaFinals40 + 4) teerLinkedField0
      ((.x5 ↦ᵣ FinalsAddr) ** (.x6 ↦ᵣ t1Old) **
        ((FinalsAddr + (40 : Word)) ↦ₘ f40))
      ((.x5 ↦ᵣ FinalsAddr) ** (.x6 ↦ᵣ f40) **
        ((FinalsAddr + (40 : Word)) ↦ₘ f40)) := by
    simpa only [se12_40_rb] using e0
  have hpc : AfterLaFinals40 + 4 = AfterLdFinals40 := by
    simp only [AfterLaFinals40, AfterLdFinals40]; bv_omega
  rw [hpc] at e1
  exact e1

/-- `beq x6, x0` ntaken: finals+40 ≠ 0. -/
theorem teerFinals40BeqNtaken (f40 : Word) (hne : f40 ≠ (0 : Word)) :
    cpsTripleWithin 1 AfterLdFinals40 AfterFinals40BeqNtaken teerLinkedField0
      ((.x6 ↦ᵣ f40) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x6 ↦ᵣ f40) ** (.x0 ↦ᵣ (0 : Word))) := by
  have hbeq := beq_spec_gen_within .x6 .x0 teerFinals40BeqOff
    f40 (0 : Word) AfterLdFinals40
  change cpsBranchWithin _ _ _ _ _ _ AfterFinals40BeqNtaken _ at hbeq
  exact cpsBranchWithin_ntakenStripPure2
    (cpsBranchWithin_extend_code
      (fun a i hi => teerField0_mono_teer a i
        (CodeReq.ofProg_mem_at E AfterLdFinals40 teerProg 532
          (.BEQ .x6 .x0 teerFinals40BeqOff)
          (by simp only [AfterLdFinals40]; bv_omega)
          (by rw [teer_length]; decide) rfl
          (by rw [teer_length]; decide) a i hi)) hbeq)
    (fun _ hQt => by
      obtain ⟨_, _, _, _, _, hBP⟩ := hQt
      exact absurd ((sepConj_pure_right _).1 hBP).2 hne)

/-- `beq x6, x0` taken: finals+40 = 0 → AfterBltuNtaken (set rolled path). -/
theorem teerFinals40BeqTaken_zero :
    cpsTripleWithin 1 AfterLdFinals40 AfterBltuNtaken teerLinkedField0
      ((.x6 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x6 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) := by
  have hbeq := beq_spec_gen_within .x6 .x0 teerFinals40BeqOff
    (0 : Word) (0 : Word) AfterLdFinals40
  rw [teerFinals40BeqOff_taken] at hbeq
  exact cpsBranchWithin_takenStripPure2
    (cpsBranchWithin_extend_code
      (fun a i hi => teerField0_mono_teer a i
        (CodeReq.ofProg_mem_at E AfterLdFinals40 teerProg 532
          (.BEQ .x6 .x0 teerFinals40BeqOff)
          (by simp only [AfterLdFinals40]; bv_omega)
          (by rw [teer_length]; decide) rfl
          (by rw [teer_length]; decide) a i hi)) hbeq)
    (fun _ hQf => by
      obtain ⟨_, _, _, _, _, hBP⟩ := hQf
      exact ((sepConj_pure_right _).1 hBP).2 rfl)

/-- `la x5, teer_finals` AfterFinals40BeqNtaken. -/
theorem teerLaFinals48 (v : Word) :
    cpsTripleWithin 2 AfterFinals40BeqNtaken AfterLaFinals48 teerLinkedField0
      (.x5 ↦ᵣ v) (.x5 ↦ᵣ FinalsAddr) := by
  have hau : ∀ a i, CodeReq.singleton AfterFinals40BeqNtaken
      (.AUIPC .x5 (Codegen.laHi GuestAddrs.teer_finals
        (GuestAddrs.tx_eip7702_existing_authority_refund + 2132)))
        a = some i → teerLinkedField0 a = some i := fun a i hi =>
    teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterFinals40BeqNtaken teerProg 533
        (.AUIPC .x5 (Codegen.laHi GuestAddrs.teer_finals
          (GuestAddrs.tx_eip7702_existing_authority_refund + 2132)))
        (by simp only [AfterFinals40BeqNtaken]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)
  have had : ∀ a i, CodeReq.singleton (E + 2136)
      (.ADDI .x5 .x5 (Codegen.laLo GuestAddrs.teer_finals
        (GuestAddrs.tx_eip7702_existing_authority_refund + 2132)))
        a = some i → teerLinkedField0 a = some i := fun a i hi =>
    teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E (E + 2136) teerProg 534
        (.ADDI .x5 .x5 (Codegen.laLo GuestAddrs.teer_finals
          (GuestAddrs.tx_eip7702_existing_authority_refund + 2132)))
        (by bv_omega) (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi)
  have h := la_materialize_within .x5 v AfterFinals40BeqNtaken FinalsAddr
    (by decide) (by decide) hau had
  rw [show (AfterFinals40BeqNtaken : Word) + 8 = AfterLaFinals48 from by
    simp only [AfterFinals40BeqNtaken, AfterLaFinals48]; bv_omega] at h
  exact h

/-- `ld x6, 48(x5)` finals field. -/
theorem teerLdFinals48 (f48 t1Old : Word) :
    cpsTripleWithin 1 AfterLaFinals48 AfterLdFinals48 teerLinkedField0
      ((.x5 ↦ᵣ FinalsAddr) ** (.x6 ↦ᵣ t1Old) **
        ((FinalsAddr + (48 : Word)) ↦ₘ f48))
      ((.x5 ↦ᵣ FinalsAddr) ** (.x6 ↦ᵣ f48) **
        ((FinalsAddr + (48 : Word)) ↦ₘ f48)) := by
  have h0 := ld_spec_gen_within .x6 .x5 FinalsAddr t1Old f48
    (48 : BitVec 12) AfterLaFinals48 (by decide)
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterLaFinals48 teerProg 535
        (.LD .x6 .x5 (48 : BitVec 12))
        (by simp only [AfterLaFinals48]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have e1 : cpsTripleWithin 1 AfterLaFinals48 (AfterLaFinals48 + 4) teerLinkedField0
      ((.x5 ↦ᵣ FinalsAddr) ** (.x6 ↦ᵣ t1Old) **
        ((FinalsAddr + (48 : Word)) ↦ₘ f48))
      ((.x5 ↦ᵣ FinalsAddr) ** (.x6 ↦ᵣ f48) **
        ((FinalsAddr + (48 : Word)) ↦ₘ f48)) := by
    simpa only [se12_48_rb] using e0
  have hpc : AfterLaFinals48 + 4 = AfterLdFinals48 := by
    simp only [AfterLaFinals48, AfterLdFinals48]; bv_omega
  rw [hpc] at e1
  exact e1

/-- `ld x7, 144(sp)` nonce scratch. -/
theorem teerLdNonceRb (spVal nonce t1Old : Word) :
    cpsTripleWithin 1 AfterLdFinals48 AfterLdNonceRb teerLinkedField0
      ((.x2 ↦ᵣ spVal) ** (.x7 ↦ᵣ t1Old) ** ((spVal + (144 : Word)) ↦ₘ nonce))
      ((.x2 ↦ᵣ spVal) ** (.x7 ↦ᵣ nonce) ** ((spVal + (144 : Word)) ↦ₘ nonce)) := by
  have h0 := ld_spec_gen_within .x7 .x2 spVal t1Old nonce
    (144 : BitVec 12) AfterLdFinals48 (by decide)
  rw [show spVal + signExtend12 (144 : BitVec 12) = spVal + (144 : Word) from by
    rw [se12_144_rb]] at h0
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterLdFinals48 teerProg 536
        (.LD .x7 .x2 (144 : BitVec 12))
        (by simp only [AfterLdFinals48]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : AfterLdFinals48 + 4 = AfterLdNonceRb := by
    simp only [AfterLdFinals48, AfterLdNonceRb]; bv_omega
  rw [hpc] at e0
  exact e0

/-- `bltu x7, x6` ntaken: ¬(nonce <u f48) → set rolled path. -/
theorem teerNonceBltuNtaken (nonce f48 : Word)
    (hge : ¬ BitVec.ult nonce f48) :
    cpsTripleWithin 1 AfterLdNonceRb AfterBltuNtaken teerLinkedField0
      ((.x7 ↦ᵣ nonce) ** (.x6 ↦ᵣ f48))
      ((.x7 ↦ᵣ nonce) ** (.x6 ↦ᵣ f48)) := by
  have hbr := bltu_spec_gen_within .x7 .x6 teerNonceBltuOff nonce f48 AfterLdNonceRb
  change cpsBranchWithin _ _ _ _ _ _ AfterBltuNtaken _ at hbr
  exact cpsBranchWithin_ntakenStripPure2
    (cpsBranchWithin_extend_code
      (fun a i hi => teerField0_mono_teer a i
        (CodeReq.ofProg_mem_at E AfterLdNonceRb teerProg 537
          (.BLTU .x7 .x6 teerNonceBltuOff)
          (by simp only [AfterLdNonceRb]; bv_omega)
          (by rw [teer_length]; decide) rfl
          (by rw [teer_length]; decide) a i hi)) hbr)
    (fun _ hQt => by
      obtain ⟨_, _, _, _, _, hBP⟩ := hQt
      exact absurd ((sepConj_pure_right _).1 hBP).2 hge)

/-- `bltu x7, x6` taken: nonce <u f48 → skip set → AfterRolledJoin. -/
theorem teerNonceBltuTaken (nonce f48 : Word)
    (hlt : BitVec.ult nonce f48) :
    cpsTripleWithin 1 AfterLdNonceRb AfterRolledJoin teerLinkedField0
      ((.x7 ↦ᵣ nonce) ** (.x6 ↦ᵣ f48))
      ((.x7 ↦ᵣ nonce) ** (.x6 ↦ᵣ f48)) := by
  have hbr := bltu_spec_gen_within .x7 .x6 teerNonceBltuOff nonce f48 AfterLdNonceRb
  rw [teerNonceBltuOff_taken] at hbr
  exact cpsBranchWithin_takenStripPure2
    (cpsBranchWithin_extend_code
      (fun a i hi => teerField0_mono_teer a i
        (CodeReq.ofProg_mem_at E AfterLdNonceRb teerProg 537
          (.BLTU .x7 .x6 teerNonceBltuOff)
          (by simp only [AfterLdNonceRb]; bv_omega)
          (by rw [teer_length]; decide) rfl
          (by rw [teer_length]; decide) a i hi)) hbr)
    (fun _ hQf => by
      obtain ⟨_, _, _, _, _, hBP⟩ := hQf
      exact ((sepConj_pure_right _).1 hBP).2 hlt)

/-- `la x5, teer_rolled_back` AfterBltuNtaken. -/
theorem teerLaRolled (v : Word) :
    cpsTripleWithin 2 AfterBltuNtaken AfterLaRolled teerLinkedField0
      (.x5 ↦ᵣ v) (.x5 ↦ᵣ RolledBackAddr) := by
  have hau : ∀ a i, CodeReq.singleton AfterBltuNtaken
      (.AUIPC .x5 (Codegen.laHi GuestAddrs.teer_rolled_back
        (GuestAddrs.tx_eip7702_existing_authority_refund + 2152)))
        a = some i → teerLinkedField0 a = some i := fun a i hi =>
    teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterBltuNtaken teerProg 538
        (.AUIPC .x5 (Codegen.laHi GuestAddrs.teer_rolled_back
          (GuestAddrs.tx_eip7702_existing_authority_refund + 2152)))
        (by simp only [AfterBltuNtaken]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)
  have had : ∀ a i, CodeReq.singleton (E + 2156)
      (.ADDI .x5 .x5 (Codegen.laLo GuestAddrs.teer_rolled_back
        (GuestAddrs.tx_eip7702_existing_authority_refund + 2152)))
        a = some i → teerLinkedField0 a = some i := fun a i hi =>
    teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E (E + 2156) teerProg 539
        (.ADDI .x5 .x5 (Codegen.laLo GuestAddrs.teer_rolled_back
          (GuestAddrs.tx_eip7702_existing_authority_refund + 2152)))
        (by bv_omega) (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi)
  have h := la_materialize_within .x5 v AfterBltuNtaken RolledBackAddr
    (by decide) (by decide) hau had
  rw [show (AfterBltuNtaken : Word) + 8 = AfterLaRolled from by
    simp only [AfterBltuNtaken, AfterLaRolled]; bv_omega] at h
  exact h

/-- `li x6, 1`. -/
theorem teerLiRolled1 (v6 : Word) :
    cpsTripleWithin 1 AfterLaRolled AfterLiRolled1 teerLinkedField0
      (.x6 ↦ᵣ v6) (.x6 ↦ᵣ (1 : Word)) := by
  have h0 := li_spec_gen_within .x6 v6 (1 : Word) AfterLaRolled (by decide)
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterLaRolled teerProg 540
        (.LI .x6 (1 : Word))
        (by simp only [AfterLaRolled]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : AfterLaRolled + 4 = AfterLiRolled1 := by
    simp only [AfterLaRolled, AfterLiRolled1]; bv_omega
  rw [hpc] at e0
  exact e0

/-- `sd x6, 0(x5)` rolled_back := 1. -/
theorem teerSdRolled1 :
    cpsTripleWithin 1 AfterLiRolled1 AfterSdRolled teerLinkedField0
      ((.x5 ↦ᵣ RolledBackAddr) ** (.x6 ↦ᵣ (1 : Word)) ** memOwn RolledBackAddr)
      ((.x5 ↦ᵣ RolledBackAddr) ** (.x6 ↦ᵣ (1 : Word)) ** memOwn RolledBackAddr) := by
  have heq : RolledBackAddr + signExtend12 (0 : BitVec 12) = RolledBackAddr := by
    rw [se12_zero_rb]; exact BitVec.add_zero RolledBackAddr
  have h0 := sd_spec_gen_own_within .x5 .x6 RolledBackAddr (1 : Word)
    (0 : BitVec 12) AfterLiRolled1
  have h1 := cpsTripleWithin_extend_code
    (fun a i hi => teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterLiRolled1 teerProg 541
        (.SD .x5 .x6 (0 : BitVec 12))
        (by simp only [AfterLiRolled1]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have h2 : cpsTripleWithin 1 AfterLiRolled1 (AfterLiRolled1 + 4) teerLinkedField0
      ((.x5 ↦ᵣ RolledBackAddr) ** (.x6 ↦ᵣ (1 : Word)) ** memOwn RolledBackAddr)
      ((.x5 ↦ᵣ RolledBackAddr) ** (.x6 ↦ᵣ (1 : Word)) **
        (RolledBackAddr ↦ₘ (1 : Word))) := by
    convert h1 using 1 <;> simp only [heq]
  have h3 := cpsTripleWithin_weaken (fun _ hp => hp)
    (fun _ hq =>
      sepConj_mono_right
        (sepConj_mono_right (fun _ hh => memIs_implies_memOwn _ hh)) _ hq) h2
  have hpc : AfterLiRolled1 + 4 = AfterSdRolled := by
    simp only [AfterLiRolled1, AfterSdRolled]; bv_omega
  rw [hpc] at h3
  exact h3

/-- Set rolled_back=1: AfterBltuNtaken → AfterRolledJoin. -/
theorem teerRolledBackSet1 (t0Old t1Old : Word) :
    cpsTripleWithin 4 AfterBltuNtaken AfterRolledJoin teerLinkedField0
      ((.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** memOwn RolledBackAddr)
      ((.x5 ↦ᵣ RolledBackAddr) ** (.x6 ↦ᵣ (1 : Word)) ** memOwn RolledBackAddr) := by
  have hla := teerLaRolled t0Old
  have hlaF := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ t1Old) ** memOwn RolledBackAddr) (by pcf) hla
  have hli := teerLiRolled1 t1Old
  have hliF := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ RolledBackAddr) ** memOwn RolledBackAddr) (by pcf) hli
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hlaF hliF
  have hsd := teerSdRolled1
  have c12 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c01 hsd
  have hpc : AfterSdRolled = AfterRolledJoin := rfl
  rw [hpc] at c12
  exact cpsTripleWithin_mono_nSteps (by decide : (2 + 1 + 1 : Nat) ≤ 4)
    (cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => by xperm_hyp hq) c12)

/-- Main path: acct≠0, finals40≠0, ¬ult(nonce,f48) → set rolled → join.
    AfterNonceEq → AfterRolledJoin (17 steps). -/
theorem teerAcctFinalsRolledSet
    (acctPtr f40 f48 nonce spVal t0Old t1Old t7Old : Word)
    (hneA : acctPtr ≠ (0 : Word))
    (hneF : f40 ≠ (0 : Word))
    (hge : ¬ BitVec.ult nonce f48) :
    cpsTripleWithin 17 AfterNonceEq AfterRolledJoin teerLinkedField0
      ((.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t7Old) **
        (.x2 ↦ᵣ spVal) ** (.x0 ↦ᵣ (0 : Word)) **
        (AcctPtrAddr ↦ₘ acctPtr) **
        ((FinalsAddr + (40 : Word)) ↦ₘ f40) **
        ((FinalsAddr + (48 : Word)) ↦ₘ f48) **
        ((spVal + (144 : Word)) ↦ₘ nonce) **
        memOwn RolledBackAddr)
      ((.x5 ↦ᵣ RolledBackAddr) ** (.x6 ↦ᵣ (1 : Word)) ** (.x7 ↦ᵣ nonce) **
        (.x2 ↦ᵣ spVal) ** (.x0 ↦ᵣ (0 : Word)) **
        (AcctPtrAddr ↦ₘ acctPtr) **
        ((FinalsAddr + (40 : Word)) ↦ₘ f40) **
        ((FinalsAddr + (48 : Word)) ↦ₘ f48) **
        ((spVal + (144 : Word)) ↦ₘ nonce) **
        memOwn RolledBackAddr) := by
  have h0 := teerAcctPtrLoadNez acctPtr t0Old t1Old hneA
  have h0F := cpsTripleWithin_frameR
    ((.x7 ↦ᵣ t7Old) ** (.x2 ↦ᵣ spVal) **
      ((FinalsAddr + (40 : Word)) ↦ₘ f40) **
      ((FinalsAddr + (48 : Word)) ↦ₘ f48) **
      ((spVal + (144 : Word)) ↦ₘ nonce) **
      memOwn RolledBackAddr) (by pcf) h0
  have hla40 := teerLaFinals40 AcctPtrAddr
  have hla40F := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ acctPtr) ** (.x7 ↦ᵣ t7Old) ** (.x2 ↦ᵣ spVal) ** (.x0 ↦ᵣ (0 : Word)) **
      (AcctPtrAddr ↦ₘ acctPtr) **
      ((FinalsAddr + (40 : Word)) ↦ₘ f40) **
      ((FinalsAddr + (48 : Word)) ↦ₘ f48) **
      ((spVal + (144 : Word)) ↦ₘ nonce) **
      memOwn RolledBackAddr) (by pcf) hla40
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h0F hla40F
  have hld40 := teerLdFinals40 f40 acctPtr
  have hld40F := cpsTripleWithin_frameR
    ((.x7 ↦ᵣ t7Old) ** (.x2 ↦ᵣ spVal) ** (.x0 ↦ᵣ (0 : Word)) **
      (AcctPtrAddr ↦ₘ acctPtr) **
      ((FinalsAddr + (48 : Word)) ↦ₘ f48) **
      ((spVal + (144 : Word)) ↦ₘ nonce) **
      memOwn RolledBackAddr) (by pcf) hld40
  have c12 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c01 hld40F
  have hb40 := teerFinals40BeqNtaken f40 hneF
  have hb40F := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ FinalsAddr) ** (.x7 ↦ᵣ t7Old) ** (.x2 ↦ᵣ spVal) **
      (AcctPtrAddr ↦ₘ acctPtr) **
      ((FinalsAddr + (40 : Word)) ↦ₘ f40) **
      ((FinalsAddr + (48 : Word)) ↦ₘ f48) **
      ((spVal + (144 : Word)) ↦ₘ nonce) **
      memOwn RolledBackAddr) (by pcf) hb40
  have c23 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c12 hb40F
  have hla48 := teerLaFinals48 FinalsAddr
  have hla48F := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ f40) ** (.x7 ↦ᵣ t7Old) ** (.x2 ↦ᵣ spVal) ** (.x0 ↦ᵣ (0 : Word)) **
      (AcctPtrAddr ↦ₘ acctPtr) **
      ((FinalsAddr + (40 : Word)) ↦ₘ f40) **
      ((FinalsAddr + (48 : Word)) ↦ₘ f48) **
      ((spVal + (144 : Word)) ↦ₘ nonce) **
      memOwn RolledBackAddr) (by pcf) hla48
  have c34 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c23 hla48F
  have hld48 := teerLdFinals48 f48 f40
  have hld48F := cpsTripleWithin_frameR
    ((.x7 ↦ᵣ t7Old) ** (.x2 ↦ᵣ spVal) ** (.x0 ↦ᵣ (0 : Word)) **
      (AcctPtrAddr ↦ₘ acctPtr) **
      ((FinalsAddr + (40 : Word)) ↦ₘ f40) **
      ((spVal + (144 : Word)) ↦ₘ nonce) **
      memOwn RolledBackAddr) (by pcf) hld48
  have c45 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c34 hld48F
  have hldN := teerLdNonceRb spVal nonce t7Old
  have hldNF := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ FinalsAddr) ** (.x6 ↦ᵣ f48) ** (.x0 ↦ᵣ (0 : Word)) **
      (AcctPtrAddr ↦ₘ acctPtr) **
      ((FinalsAddr + (40 : Word)) ↦ₘ f40) **
      ((FinalsAddr + (48 : Word)) ↦ₘ f48) **
      memOwn RolledBackAddr) (by pcf) hldN
  have c56 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c45 hldNF
  have hbl := teerNonceBltuNtaken nonce f48 hge
  have hblF := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ FinalsAddr) ** (.x2 ↦ᵣ spVal) ** (.x0 ↦ᵣ (0 : Word)) **
      (AcctPtrAddr ↦ₘ acctPtr) **
      ((FinalsAddr + (40 : Word)) ↦ₘ f40) **
      ((FinalsAddr + (48 : Word)) ↦ₘ f48) **
      ((spVal + (144 : Word)) ↦ₘ nonce) **
      memOwn RolledBackAddr) (by pcf) hbl
  have c67 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c56 hblF
  have hset := teerRolledBackSet1 FinalsAddr f48
  have hsetF := cpsTripleWithin_frameR
    ((.x7 ↦ᵣ nonce) ** (.x2 ↦ᵣ spVal) ** (.x0 ↦ᵣ (0 : Word)) **
      (AcctPtrAddr ↦ₘ acctPtr) **
      ((FinalsAddr + (40 : Word)) ↦ₘ f40) **
      ((FinalsAddr + (48 : Word)) ↦ₘ f48) **
      ((spVal + (144 : Word)) ↦ₘ nonce)) (by pcf) hset
  have c78 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c67 hsetF
  exact cpsTripleWithin_mono_nSteps
    (by decide : (4 + 2 + 1 + 1 + 2 + 1 + 1 + 1 + 4 : Nat) ≤ 17)
    (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) c78)

#print axioms teerLaAcctPtrRb
#print axioms teerAcctPtrZeroSkip
#print axioms teerAcctPtrLoadNez
#print axioms teerRolledBackSet1
#print axioms teerAcctFinalsRolledSet

end EvmAsm.Codegen.TxEip7702TeerSpec
