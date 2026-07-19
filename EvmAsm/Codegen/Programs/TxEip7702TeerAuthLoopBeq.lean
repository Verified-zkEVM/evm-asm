/-
  Teer auth-loop header BEQ s8,s7 (instr 181): empty-skip when count=0.
  AfterAuthLoopLi (E+724) → AfterAuthLoopBeq (E+728) ntaken, or AtLoopExit (E+2856) taken.
-/

import EvmAsm.Codegen.Programs.TxEip7702TeerAuthLoopStart
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.Tactics.XSimp

namespace EvmAsm.Codegen.TxEip7702TeerSpec

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Codegen

/-- PC after auth-loop BEQ not-taken (enter body). -/
abbrev AfterAuthLoopBeq : Word := AfterAuthLoopLi + 4

/-- Empty-auth / loop-done exit (BEQ taken target). -/
abbrev AtLoopExit : Word := E + 2856

/-- BEQ offset at instr 181 (`beq s8, s7, loop_exit`). -/
abbrev teerAuthLoopBeqOff : BitVec 13 := (2132 : BitVec 13)

theorem teerAuthLoopBeqOff_taken :
    AfterAuthLoopLi + signExtend13 teerAuthLoopBeqOff = AtLoopExit := by
  simp only [AfterAuthLoopLi, AtLoopExit, teerAuthLoopBeqOff, E]; decide

/-- `beq s8, s7` not-taken: s8 ≠ s7 (more auths to process). -/
theorem teerAuthLoopBeqNtaken (idx countW : Word) (hne : idx ≠ countW) :
    cpsTripleWithin 1 AfterAuthLoopLi AfterAuthLoopBeq teerLinkedCount
      ((.x24 ↦ᵣ idx) ** (.x23 ↦ᵣ countW))
      ((.x24 ↦ᵣ idx) ** (.x23 ↦ᵣ countW)) := by
  have hbeq := beq_spec_gen_within .x24 .x23 teerAuthLoopBeqOff idx countW AfterAuthLoopLi
  change cpsBranchWithin _ _ _ _ _ _ AfterAuthLoopBeq _ at hbeq
  exact cpsBranchWithin_ntakenStripPure2
    (cpsBranchWithin_extend_code
      (fun a i hi => teerCount_mono_teer a i
        (CodeReq.ofProg_mem_at E AfterAuthLoopLi teerProg 181
          (.BEQ .x24 .x23 teerAuthLoopBeqOff)
          (by simp only [AfterAuthLoopLi]; bv_omega)
          (by rw [teer_length]; decide) rfl
          (by rw [teer_length]; decide) a i hi)) hbeq)
    (fun _ hQt => by
      obtain ⟨_, _, _, _, _, hBP⟩ := hQt
      exact hne ((sepConj_pure_right _).1 hBP).2)

/-- `beq s8, s7` taken: s8 = s7 (empty auth list / loop done) → AtLoopExit. -/
theorem teerAuthLoopBeqTaken (idx countW : Word) (heq : idx = countW) :
    cpsTripleWithin 1 AfterAuthLoopLi AtLoopExit teerLinkedCount
      ((.x24 ↦ᵣ idx) ** (.x23 ↦ᵣ countW))
      ((.x24 ↦ᵣ idx) ** (.x23 ↦ᵣ countW)) := by
  have hbeq := beq_spec_gen_within .x24 .x23 teerAuthLoopBeqOff idx countW AfterAuthLoopLi
  rw [teerAuthLoopBeqOff_taken] at hbeq
  exact cpsBranchWithin_takenStripPure2
    (cpsBranchWithin_extend_code
      (fun a i hi => teerCount_mono_teer a i
        (CodeReq.ofProg_mem_at E AfterAuthLoopLi teerProg 181
          (.BEQ .x24 .x23 teerAuthLoopBeqOff)
          (by simp only [AfterAuthLoopLi]; bv_omega)
          (by rw [teer_length]; decide) rfl
          (by rw [teer_length]; decide) a i hi)) hbeq)
    (fun _ hQf => by
      obtain ⟨_, _, _, _, _, hBP⟩ := hQf
      exact ((sepConj_pure_right _).1 hBP).2 heq)

/-- Specialization: s8=0, count≠0 enters body. -/
theorem teerAuthLoopBeqNtaken_zero (countW : Word) (hne : countW ≠ (0 : Word)) :
    cpsTripleWithin 1 AfterAuthLoopLi AfterAuthLoopBeq teerLinkedCount
      ((.x24 ↦ᵣ (0 : Word)) ** (.x23 ↦ᵣ countW))
      ((.x24 ↦ᵣ (0 : Word)) ** (.x23 ↦ᵣ countW)) :=
  teerAuthLoopBeqNtaken (0 : Word) countW (Ne.symm hne)

/-- Specialization: s8=0, count=0 → AtLoopExit (empty auth list). -/
theorem teerAuthLoopBeqTaken_zero :
    cpsTripleWithin 1 AfterAuthLoopLi AtLoopExit teerLinkedCount
      ((.x24 ↦ᵣ (0 : Word)) ** (.x23 ↦ᵣ (0 : Word)))
      ((.x24 ↦ᵣ (0 : Word)) ** (.x23 ↦ᵣ (0 : Word))) :=
  teerAuthLoopBeqTaken (0 : Word) (0 : Word) rfl

#print axioms teerAuthLoopBeqNtaken
#print axioms teerAuthLoopBeqTaken
#print axioms teerAuthLoopBeqNtaken_zero
#print axioms teerAuthLoopBeqTaken_zero

end EvmAsm.Codegen.TxEip7702TeerSpec
