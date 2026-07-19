/-
  Teer auth-loop chain-id check after field0 content_to_u64:
  MV t1,a0; BEQ t1,0 chain_ok; BNE t1,s4 next.
  AfterAuthField0Bne (E+816) → AfterChainOk (E+828) on success path.
-/

import EvmAsm.Codegen.Programs.TxEip7702TeerAuthLoopField0
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.Tactics.XSimp

namespace EvmAsm.Codegen.TxEip7702TeerSpec

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Codegen

/-- After MV t1,a0. -/
abbrev AfterChainMv : Word := E + 820

/-- After BEQ t1,x0 not-taken (nonzero chain id). -/
abbrev AfterChainBeqNtaken : Word := E + 824

/-- Chain-id accepted (zero or matches s4). -/
abbrev AfterChainOk : Word := E + 828

/-- Chain mismatch / skip-to-next target (`bne t1,s4,.Lteanse_next`). -/
abbrev AtChainMismatch : Word := E + 1844

abbrev teerChainBeqOff : BitVec 13 := (8 : BitVec 13)
abbrev teerChainBneOff : BitVec 13 := (1020 : BitVec 13)

theorem teerChainBeqOff_taken :
    AfterChainMv + signExtend13 teerChainBeqOff = AfterChainOk := by
  simp only [AfterChainMv, AfterChainOk, teerChainBeqOff, E]; decide

theorem teerChainBneOff_taken :
    AfterChainBeqNtaken + signExtend13 teerChainBneOff = AtChainMismatch := by
  simp only [AfterChainBeqNtaken, AtChainMismatch, teerChainBneOff, E]; decide

/-- `mv t1, a0` — stash chain-id value. -/
theorem teerChainMvT1 (chainVal t1Old : Word) :
    cpsTripleWithin 1 AfterAuthField0Bne AfterChainMv teerLinkedField0
      ((.x10 ↦ᵣ chainVal) ** (.x6 ↦ᵣ t1Old))
      ((.x10 ↦ᵣ chainVal) ** (.x6 ↦ᵣ chainVal)) := by
  have h0 := mv_spec_gen_within .x6 .x10 chainVal t1Old AfterAuthField0Bne (by decide)
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterAuthField0Bne teerProg 204
        (.MV .x6 .x10) (by simp only [AfterAuthField0Bne]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : (AfterAuthField0Bne + 4 : Word) = AfterChainMv := by
    simp only [AfterAuthField0Bne, AfterChainMv]; bv_omega
  rw [hpc] at e0
  exact e0

/-- `beq t1, x0` taken: chain id = 0 → AfterChainOk. -/
theorem teerChainBeqZeroTaken :
    cpsTripleWithin 1 AfterChainMv AfterChainOk teerLinkedField0
      ((.x6 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x6 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) := by
  have hbeq := beq_spec_gen_within .x6 .x0 teerChainBeqOff
    (0 : Word) (0 : Word) AfterChainMv
  rw [teerChainBeqOff_taken] at hbeq
  exact cpsBranchWithin_takenStripPure2
    (cpsBranchWithin_extend_code
      (fun a i hi => teerField0_mono_teer a i
        (CodeReq.ofProg_mem_at E AfterChainMv teerProg 205
          (.BEQ .x6 .x0 teerChainBeqOff)
          (by simp only [AfterChainMv]; bv_omega)
          (by rw [teer_length]; decide) rfl
          (by rw [teer_length]; decide) a i hi)) hbeq)
    (fun _ hQf => by
      obtain ⟨_, _, _, _, _, hBP⟩ := hQf
      exact ((sepConj_pure_right _).1 hBP).2 rfl)

/-- `beq t1, x0` not-taken: chain id ≠ 0 → AfterChainBeqNtaken. -/
theorem teerChainBeqZeroNtaken (chainVal : Word) (hne : chainVal ≠ (0 : Word)) :
    cpsTripleWithin 1 AfterChainMv AfterChainBeqNtaken teerLinkedField0
      ((.x6 ↦ᵣ chainVal) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x6 ↦ᵣ chainVal) ** (.x0 ↦ᵣ (0 : Word))) := by
  have hbeq := beq_spec_gen_within .x6 .x0 teerChainBeqOff
    chainVal (0 : Word) AfterChainMv
  change cpsBranchWithin _ _ _ _ _ _ AfterChainBeqNtaken _ at hbeq
  exact cpsBranchWithin_ntakenStripPure2
    (cpsBranchWithin_extend_code
      (fun a i hi => teerField0_mono_teer a i
        (CodeReq.ofProg_mem_at E AfterChainMv teerProg 205
          (.BEQ .x6 .x0 teerChainBeqOff)
          (by simp only [AfterChainMv]; bv_omega)
          (by rw [teer_length]; decide) rfl
          (by rw [teer_length]; decide) a i hi)) hbeq)
    (fun _ hQt => by
      obtain ⟨_, _, _, _, _, hBP⟩ := hQt
      exact hne ((sepConj_pure_right _).1 hBP).2)

/-- `bne t1, s4` not-taken: chain id = block chain id → AfterChainOk. -/
theorem teerChainBneMatchNtaken (chainVal : Word) :
    cpsTripleWithin 1 AfterChainBeqNtaken AfterChainOk teerLinkedField0
      ((.x6 ↦ᵣ chainVal) ** (.x20 ↦ᵣ chainVal))
      ((.x6 ↦ᵣ chainVal) ** (.x20 ↦ᵣ chainVal)) := by
  have hbr := bne_spec_gen_within .x6 .x20 teerChainBneOff
    chainVal chainVal AfterChainBeqNtaken
  have hbrC := cpsBranchWithin_extend_code
    (fun a i hi => teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterChainBeqNtaken teerProg 206
        (.BNE .x6 .x20 teerChainBneOff)
        (by simp only [AfterChainBeqNtaken]; bv_omega)
        (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi)) hbr
  have hnt := cpsBranchWithin_ntakenStripPure2 hbrC (fun _ hQt => by
    obtain ⟨_, _, _, _, _, hrest⟩ := hQt
    exact absurd rfl ((sepConj_pure_right _).1 hrest).2)
  have hpc : AfterChainBeqNtaken + 4 = AfterChainOk := by
    simp only [AfterChainBeqNtaken, AfterChainOk]; bv_omega
  rw [hpc] at hnt
  exact hnt

/-- `bne t1, s4` taken: chain id ≠ block chain id → AtChainMismatch. -/
theorem teerChainBneMismatchTaken (chainVal blockId : Word) (hne : chainVal ≠ blockId) :
    cpsTripleWithin 1 AfterChainBeqNtaken AtChainMismatch teerLinkedField0
      ((.x6 ↦ᵣ chainVal) ** (.x20 ↦ᵣ blockId))
      ((.x6 ↦ᵣ chainVal) ** (.x20 ↦ᵣ blockId)) := by
  have hbr := bne_spec_gen_within .x6 .x20 teerChainBneOff
    chainVal blockId AfterChainBeqNtaken
  rw [teerChainBneOff_taken] at hbr
  exact cpsBranchWithin_takenStripPure2
    (cpsBranchWithin_extend_code
      (fun a i hi => teerField0_mono_teer a i
        (CodeReq.ofProg_mem_at E AfterChainBeqNtaken teerProg 206
          (.BNE .x6 .x20 teerChainBneOff)
          (by simp only [AfterChainBeqNtaken]; bv_omega)
          (by rw [teer_length]; decide) rfl
          (by rw [teer_length]; decide) a i hi)) hbr)
    (fun _ hQf => by
      obtain ⟨_, _, _, _, _, hBP⟩ := hQf
      exact hne ((sepConj_pure_right _).1 hBP).2)

/-- Zero chain-id path: MV + BEQ taken → AfterChainOk. -/
theorem teerChainOk_zero (t1Old : Word) :
    cpsTripleWithin 2 AfterAuthField0Bne AfterChainOk teerLinkedField0
      ((.x10 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ t1Old) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x10 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) := by
  have h0 := teerChainMvT1 (0 : Word) t1Old
  have h0F := cpsTripleWithin_frameR (.x0 ↦ᵣ (0 : Word)) (by
    repeat first
      | apply pcFree_sepConj
      | exact pcFree_regIs
      | exact pcFree_regOwn
      | exact pcFree_emp
      | exact pcFree_pure) h0
  have h1 := teerChainBeqZeroTaken
  have h1F := cpsTripleWithin_frameR (.x10 ↦ᵣ (0 : Word)) (by
    repeat first
      | apply pcFree_sepConj
      | exact pcFree_regIs
      | exact pcFree_regOwn
      | exact pcFree_emp
      | exact pcFree_pure) h1
  have hseq := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h0F h1F
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hseq

/-- Matching nonzero chain-id path: MV + BEQ ntaken + BNE match → AfterChainOk. -/
theorem teerChainOk_match (chainVal t1Old : Word) (hne : chainVal ≠ (0 : Word)) :
    cpsTripleWithin 3 AfterAuthField0Bne AfterChainOk teerLinkedField0
      ((.x10 ↦ᵣ chainVal) ** (.x6 ↦ᵣ t1Old) ** (.x20 ↦ᵣ chainVal) **
        (.x0 ↦ᵣ (0 : Word)))
      ((.x10 ↦ᵣ chainVal) ** (.x6 ↦ᵣ chainVal) ** (.x20 ↦ᵣ chainVal) **
        (.x0 ↦ᵣ (0 : Word))) := by
  have h0 := teerChainMvT1 chainVal t1Old
  have h0F := cpsTripleWithin_frameR
    ((.x20 ↦ᵣ chainVal) ** (.x0 ↦ᵣ (0 : Word))) (by
    repeat first
      | apply pcFree_sepConj
      | exact pcFree_regIs
      | exact pcFree_regOwn
      | exact pcFree_emp
      | exact pcFree_pure) h0
  have h1 := teerChainBeqZeroNtaken chainVal hne
  have h1F := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ chainVal) ** (.x20 ↦ᵣ chainVal)) (by
    repeat first
      | apply pcFree_sepConj
      | exact pcFree_regIs
      | exact pcFree_regOwn
      | exact pcFree_emp
      | exact pcFree_pure) h1
  have h2 := teerChainBneMatchNtaken chainVal
  have h2F := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ chainVal) ** (.x0 ↦ᵣ (0 : Word))) (by
    repeat first
      | apply pcFree_sepConj
      | exact pcFree_regIs
      | exact pcFree_regOwn
      | exact pcFree_emp
      | exact pcFree_pure) h2
  have hseq01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h0F h1F
  have hseq := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hseq01 h2F
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hseq

#print axioms teerChainMvT1
#print axioms teerChainBeqZeroTaken
#print axioms teerChainBeqZeroNtaken
#print axioms teerChainBneMatchNtaken
#print axioms teerChainBneMismatchTaken
#print axioms teerChainOk_zero
#print axioms teerChainOk_match

end EvmAsm.Codegen.TxEip7702TeerSpec
