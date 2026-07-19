/-
  Teer auth-loop success_count load + empty-table skip:
  AfterPriorSetFlagZero (E+968) → AtBalFindSetup (E+1116) when success_count = 0.

  Path: la/ld teer_success_count; li x7,0; beq x7,x6 taken (offset 132).
-/

import EvmAsm.Codegen.Programs.TxEip7702TeerAuthLoopRecoverCall
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

abbrev AfterSuccessCountLa : Word := E + 976
abbrev AfterSuccessCountLd : Word := E + 980
abbrev AfterSuccessIdxLi : Word := E + 984
/-- BEQ taken target: skip empty success_table → bal_find setup. -/
abbrev AtBalFindSetup : Word := E + 1116
abbrev AfterSuccessTableBeqNtaken : Word := AfterSuccessIdxLi + 4

abbrev teerSuccessTableBeqOff : BitVec 13 := (132 : BitVec 13)

theorem teerSuccessTableBeqOff_taken :
    AfterSuccessIdxLi + signExtend13 teerSuccessTableBeqOff = AtBalFindSetup := by
  simp only [AfterSuccessIdxLi, AtBalFindSetup, teerSuccessTableBeqOff, E]; decide

private theorem se12_zero_st : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide

/-- `la x5, teer_success_count` AfterPriorSetFlagZero → AfterSuccessCountLa. -/
theorem teerLaSuccessCountLoad (v : Word) :
    cpsTripleWithin 2 AfterPriorSetFlagZero AfterSuccessCountLa teerLinkedField0
      (.x5 ↦ᵣ v) (.x5 ↦ᵣ SuccessCountAddr) := by
  have hau : ∀ a i, CodeReq.singleton AfterPriorSetFlagZero
      (.AUIPC .x5 (Codegen.laHi GuestAddrs.teer_success_count
        (GuestAddrs.tx_eip7702_existing_authority_refund + 968)))
        a = some i → teerLinkedField0 a = some i := fun a i hi =>
    teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterPriorSetFlagZero teerProg 242
        (.AUIPC .x5 (Codegen.laHi GuestAddrs.teer_success_count
          (GuestAddrs.tx_eip7702_existing_authority_refund + 968)))
        (by simp only [AfterPriorSetFlagZero]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)
  have had : ∀ a i, CodeReq.singleton (E + 972)
      (.ADDI .x5 .x5 (Codegen.laLo GuestAddrs.teer_success_count
        (GuestAddrs.tx_eip7702_existing_authority_refund + 968)))
        a = some i → teerLinkedField0 a = some i := fun a i hi =>
    teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E (E + 972) teerProg 243
        (.ADDI .x5 .x5 (Codegen.laLo GuestAddrs.teer_success_count
          (GuestAddrs.tx_eip7702_existing_authority_refund + 968)))
        (by bv_omega) (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi)
  have h := la_materialize_within .x5 v AfterPriorSetFlagZero SuccessCountAddr
    (by decide) (by decide) hau had
  rw [show (AfterPriorSetFlagZero : Word) + 8 = AfterSuccessCountLa from by
    simp only [AfterPriorSetFlagZero, AfterSuccessCountLa]; bv_omega] at h
  exact h

/-- `ld x6, 0(x5)` success_count. -/
theorem teerLdSuccessCount (countW t1Old : Word) :
    cpsTripleWithin 1 AfterSuccessCountLa AfterSuccessCountLd teerLinkedField0
      ((.x5 ↦ᵣ SuccessCountAddr) ** (.x6 ↦ᵣ t1Old) ** (SuccessCountAddr ↦ₘ countW))
      ((.x5 ↦ᵣ SuccessCountAddr) ** (.x6 ↦ᵣ countW) **
        (SuccessCountAddr ↦ₘ countW)) := by
  have h0 := ld_spec_gen_within .x6 .x5 SuccessCountAddr t1Old countW
    (0 : BitVec 12) AfterSuccessCountLa (by decide)
  rw [show SuccessCountAddr + signExtend12 (0 : BitVec 12) = SuccessCountAddr from by
    rw [se12_zero_st]; exact BitVec.add_zero SuccessCountAddr] at h0
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterSuccessCountLa teerProg 244
        (.LD .x6 .x5 (0 : BitVec 12))
        (by simp only [AfterSuccessCountLa]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : AfterSuccessCountLa + 4 = AfterSuccessCountLd := by
    simp only [AfterSuccessCountLa, AfterSuccessCountLd]; bv_omega
  rw [hpc] at e0
  exact e0

/-- `li x7, 0` scan index. -/
theorem teerLiSuccessIdx (v7 : Word) :
    cpsTripleWithin 1 AfterSuccessCountLd AfterSuccessIdxLi teerLinkedField0
      (.x7 ↦ᵣ v7) (.x7 ↦ᵣ (0 : Word)) := by
  have h0 := li_spec_gen_within .x7 v7 (0 : Word) AfterSuccessCountLd (by decide)
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterSuccessCountLd teerProg 245
        (.LI .x7 (0 : Word))
        (by simp only [AfterSuccessCountLd]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : AfterSuccessCountLd + 4 = AfterSuccessIdxLi := by
    simp only [AfterSuccessCountLd, AfterSuccessIdxLi]; bv_omega
  rw [hpc] at e0
  exact e0

/-- `beq x7, x6` taken: idx = count (empty table when both 0) → AtBalFindSetup. -/
theorem teerSuccessTableBeqTaken (idx countW : Word) (heq : idx = countW) :
    cpsTripleWithin 1 AfterSuccessIdxLi AtBalFindSetup teerLinkedField0
      ((.x7 ↦ᵣ idx) ** (.x6 ↦ᵣ countW))
      ((.x7 ↦ᵣ idx) ** (.x6 ↦ᵣ countW)) := by
  have hbeq := beq_spec_gen_within .x7 .x6 teerSuccessTableBeqOff idx countW
    AfterSuccessIdxLi
  rw [teerSuccessTableBeqOff_taken] at hbeq
  exact cpsBranchWithin_takenStripPure2
    (cpsBranchWithin_extend_code
      (fun a i hi => teerField0_mono_teer a i
        (CodeReq.ofProg_mem_at E AfterSuccessIdxLi teerProg 246
          (.BEQ .x7 .x6 teerSuccessTableBeqOff)
          (by simp only [AfterSuccessIdxLi]; bv_omega)
          (by rw [teer_length]; decide) rfl
          (by rw [teer_length]; decide) a i hi)) hbeq)
    (fun _ hQf => by
      obtain ⟨_, _, _, _, _, hBP⟩ := hQf
      exact ((sepConj_pure_right _).1 hBP).2 heq)

/-- Empty success_table: count=0 → skip scan → AtBalFindSetup. -/
theorem teerSuccessTableBeqTaken_zero :
    cpsTripleWithin 1 AfterSuccessIdxLi AtBalFindSetup teerLinkedField0
      ((.x7 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ (0 : Word)))
      ((.x7 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ (0 : Word))) :=
  teerSuccessTableBeqTaken (0 : Word) (0 : Word) rfl

/-- `beq x7, x6` not-taken: more table entries to scan. -/
theorem teerSuccessTableBeqNtaken (idx countW : Word) (hne : idx ≠ countW) :
    cpsTripleWithin 1 AfterSuccessIdxLi AfterSuccessTableBeqNtaken teerLinkedField0
      ((.x7 ↦ᵣ idx) ** (.x6 ↦ᵣ countW))
      ((.x7 ↦ᵣ idx) ** (.x6 ↦ᵣ countW)) := by
  have hbeq := beq_spec_gen_within .x7 .x6 teerSuccessTableBeqOff idx countW
    AfterSuccessIdxLi
  change cpsBranchWithin _ _ _ _ _ _ AfterSuccessTableBeqNtaken _ at hbeq
  exact cpsBranchWithin_ntakenStripPure2
    (cpsBranchWithin_extend_code
      (fun a i hi => teerField0_mono_teer a i
        (CodeReq.ofProg_mem_at E AfterSuccessIdxLi teerProg 246
          (.BEQ .x7 .x6 teerSuccessTableBeqOff)
          (by simp only [AfterSuccessIdxLi]; bv_omega)
          (by rw [teer_length]; decide) rfl
          (by rw [teer_length]; decide) a i hi)) hbeq)
    (fun _ hQt => by
      obtain ⟨_, _, _, _, _, hBP⟩ := hQt
      exact hne ((sepConj_pure_right _).1 hBP).2)

/-- Load success_count + li idx=0 (no BEQ): AfterPriorSetFlagZero → AfterSuccessIdxLi. -/
theorem teerSuccessCountLoadLi (countW t0Old t1Old t2Old : Word) :
    cpsTripleWithin 4 AfterPriorSetFlagZero AfterSuccessIdxLi teerLinkedField0
      ((.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) **
        (SuccessCountAddr ↦ₘ countW))
      ((.x5 ↦ᵣ SuccessCountAddr) ** (.x6 ↦ᵣ countW) ** (.x7 ↦ᵣ (0 : Word)) **
        (SuccessCountAddr ↦ₘ countW)) := by
  have hla := teerLaSuccessCountLoad t0Old
  have hlaF := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (SuccessCountAddr ↦ₘ countW))
    (by pcf) hla
  have hld := teerLdSuccessCount countW t1Old
  have hldF := cpsTripleWithin_frameR (.x7 ↦ᵣ t2Old) (by pcf) hld
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hlaF hldF
  have hli := teerLiSuccessIdx t2Old
  have hliF := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ SuccessCountAddr) ** (.x6 ↦ᵣ countW) **
      (SuccessCountAddr ↦ₘ countW)) (by pcf) hli
  have c12 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c01 hliF
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) c12

/-- Empty success_table: count=0 → load+li+BEQ taken → AtBalFindSetup. -/
theorem teerSuccessCountEmptySkip (t0Old t1Old t2Old : Word) :
    cpsTripleWithin 5 AfterPriorSetFlagZero AtBalFindSetup teerLinkedField0
      ((.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) **
        (SuccessCountAddr ↦ₘ (0 : Word)))
      ((.x5 ↦ᵣ SuccessCountAddr) ** (.x6 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ (0 : Word)) **
        (SuccessCountAddr ↦ₘ (0 : Word))) := by
  have hload := teerSuccessCountLoadLi (0 : Word) t0Old t1Old t2Old
  have hbeq := teerSuccessTableBeqTaken_zero
  have hbeqF := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ SuccessCountAddr) ** (SuccessCountAddr ↦ₘ (0 : Word)))
    (by pcf) hbeq
  have c := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hload hbeqF
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) c

#print axioms teerLaSuccessCountLoad
#print axioms teerLdSuccessCount
#print axioms teerLiSuccessIdx
#print axioms teerSuccessTableBeqTaken
#print axioms teerSuccessTableBeqTaken_zero
#print axioms teerSuccessTableBeqNtaken
#print axioms teerSuccessCountLoadLi
#print axioms teerSuccessCountEmptySkip

end EvmAsm.Codegen.TxEip7702TeerSpec
