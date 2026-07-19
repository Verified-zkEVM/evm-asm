/-
  Teer bal≠0 BEQ (instr 33): not-taken arm of applied_flat.
  PC AtBalCheck → AfterBalCheck (E+136).
-/

import EvmAsm.Codegen.Programs.TxEip7702TeerScratchZero
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.Tactics.XSimp

namespace EvmAsm.Codegen.TxEip7702TeerSpec

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm

/-- PC after bal≠0 BEQ not-taken (E+136). -/
abbrev AfterBalCheck : Word := AtBalCheck + 4

/-- BEQ offset at instr 33 (bal==0 short-circuit). -/
abbrev teerBalBeqOff : BitVec 13 := (2724 : BitVec 13)

/-- `beq s2, x0, bal_zero` not-taken: balPtr ≠ 0. -/
theorem teerBalNezBeq (balPtr : Word) (hnez : balPtr ≠ (0 : Word)) :
    cpsTripleWithin 1 AtBalCheck AfterBalCheck teerCode
      ((.x18 ↦ᵣ balPtr) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x18 ↦ᵣ balPtr) ** (.x0 ↦ᵣ (0 : Word))) := by
  have hbeq := beq_spec_gen_within .x18 .x0 teerBalBeqOff balPtr (0 : Word) AtBalCheck
  rw [show (AtBalCheck : Word) + 4 = AfterBalCheck from by simp [AfterBalCheck]] at hbeq
  exact cpsBranchWithin_ntakenStripPure2
    (cpsBranchWithin_extend_code
      (CodeReq.ofProg_mem_at E AtBalCheck teerProg 33
        (.BEQ .x18 .x0 teerBalBeqOff) (by bv_omega) (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide)) hbeq)
    (fun _ hQt => by
      obtain ⟨_, _, _, _, _, hBP⟩ := hQt
      exact hnez ((sepConj_pure_right _).1 hBP).2)

#print axioms teerBalNezBeq

end EvmAsm.Codegen.TxEip7702TeerSpec
