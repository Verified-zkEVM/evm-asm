/-
  EvmAsm.Evm64.Compare.LimbSpec

  Shared per-limb comparison specs used by Lt, Gt, Slt, Sgt.
  - lt_limb0_spec, lt_limb_carry_spec: borrow propagation
  - beq_eq_spec, beq_ne_spec: BEQ branch helpers (for SLT/SGT)
  - slt_msb_load_spec: MSB limb load (for SLT/SGT)
-/

import EvmAsm.Evm64.Stack
import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.Tactics.RunBlock

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Rv64

-- ============================================================================
-- Per-limb Specs: LT (borrow propagation without storing results)
-- ============================================================================

/-- LT limb 0 spec (3 instructions): LD, LD, SLTU.
    Computes initial borrow = (a < b ? 1 : 0). Does NOT modify memory. -/
theorem lt_limb0_spec (off_a off_b : BitVec 12)
    (sp a_limb b_limb v7 v6 v5 : Word) (base : Word)
    (hvalid_a : isValidDwordAccess (sp + signExtend12 off_a) = true)
    (hvalid_b : isValidDwordAccess (sp + signExtend12 off_b) = true) :
    let mem_a := sp + signExtend12 off_a
    let mem_b := sp + signExtend12 off_b
    let borrow := if BitVec.ult a_limb b_limb then (1 : Word) else 0
    let cr :=
      CodeReq.union (CodeReq.singleton base (.LD .x7 .x12 off_a))
      (CodeReq.union (CodeReq.singleton (base + 4) (.LD .x6 .x12 off_b))
       (CodeReq.singleton (base + 8) (.SLTU .x5 .x7 .x6)))
    cpsTriple base (base + 12) cr
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) ** (.x5 ↦ᵣ v5) **
       (mem_a ↦ₘ a_limb) ** (mem_b ↦ₘ b_limb))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ a_limb) ** (.x6 ↦ᵣ b_limb) ** (.x5 ↦ᵣ borrow) **
       (mem_a ↦ₘ a_limb) ** (mem_b ↦ₘ b_limb)) := by
  runBlock

/-- LT carry limb spec (6 instructions): LD, LD, SLTU, SUB, SLTU, OR.
    Propagates borrow without storing result. Memory is NOT modified. -/
theorem lt_limb_carry_spec (off_a off_b : BitVec 12)
    (sp a_limb b_limb v7 v6 borrow_in v11 : Word) (base : Word)
    (hvalid_a : isValidDwordAccess (sp + signExtend12 off_a) = true)
    (hvalid_b : isValidDwordAccess (sp + signExtend12 off_b) = true) :
    let mem_a := sp + signExtend12 off_a
    let mem_b := sp + signExtend12 off_b
    let borrow1 := if BitVec.ult a_limb b_limb then (1 : Word) else 0
    let temp := a_limb - b_limb
    let borrow2 := if BitVec.ult temp borrow_in then (1 : Word) else 0
    let borrow_out := borrow1 ||| borrow2
    let cr :=
      CodeReq.union (CodeReq.singleton base (.LD .x7 .x12 off_a))
      (CodeReq.union (CodeReq.singleton (base + 4) (.LD .x6 .x12 off_b))
      (CodeReq.union (CodeReq.singleton (base + 8) (.SLTU .x11 .x7 .x6))
      (CodeReq.union (CodeReq.singleton (base + 12) (.SUB .x7 .x7 .x6))
      (CodeReq.union (CodeReq.singleton (base + 16) (.SLTU .x6 .x7 .x5))
       (CodeReq.singleton (base + 20) (.OR .x5 .x11 .x6))))))
    cpsTriple base (base + 24) cr
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) ** (.x5 ↦ᵣ borrow_in) ** (.x11 ↦ᵣ v11) **
       (mem_a ↦ₘ a_limb) ** (mem_b ↦ₘ b_limb))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ temp) ** (.x6 ↦ᵣ borrow2) ** (.x5 ↦ᵣ borrow_out) ** (.x11 ↦ᵣ borrow1) **
       (mem_a ↦ₘ a_limb) ** (mem_b ↦ₘ b_limb)) := by
  runBlock

-- ============================================================================
-- BEQ helper specs (single-path, for SLT/SGT composition)
-- ============================================================================

/-- BEQ when values are equal: always taken (jump to PC + signExtend13 offset).
    BEQ only modifies PC; all pcFree assertions are preserved. -/
theorem beq_eq_spec (rs1 rs2 : Reg) (offset : BitVec 13)
    (v : Word) (base : Word) :
    cpsTriple base (base + signExtend13 offset)
      (CodeReq.singleton base (.BEQ rs1 rs2 offset))
      ((rs1 ↦ᵣ v) ** (rs2 ↦ᵣ v))
      ((rs1 ↦ᵣ v) ** (rs2 ↦ᵣ v)) := by
  intro R hR s hcr hPR hpc; subst hpc
  have hfetch : s.code s.pc = some (.BEQ rs1 rs2 offset) :=
    hcr s.pc (.BEQ rs1 rs2 offset) (CodeReq.singleton_get s.pc (.BEQ rs1 rs2 offset))
  have hrs1 : s.getReg rs1 = v :=
    (holdsFor_regIs _ _ s).mp (holdsFor_sepConj_elim_left (holdsFor_sepConj_elim_left hPR))
  have hrs2 : s.getReg rs2 = v :=
    (holdsFor_regIs _ _ s).mp (holdsFor_sepConj_elim_right (holdsFor_sepConj_elim_left hPR))
  have hstep' : step s = some (execInstrBr s (.BEQ rs1 rs2 offset)) :=
    step_non_ecall_non_mem s _ hfetch (by nofun) (by nofun) (by rfl)
  have hexec' : execInstrBr s (.BEQ rs1 rs2 offset) = s.setPC (s.pc + signExtend13 offset) := by
    simp [execInstrBr, hrs1, hrs2]
  refine ⟨1, s.setPC (s.pc + signExtend13 offset), ?_, by simp [MachineState.setPC], ?_⟩
  · show (step s).bind (stepN 0) = some _
    rw [hstep', hexec']; rfl
  · exact holdsFor_pcFree_setPC
      (pcFree_sepConj (pcFree_sepConj (pcFree_regIs _ _) (pcFree_regIs _ _)) hR) _ _ hPR

/-- BEQ when values are not equal: never taken (fall through to PC + 4).
    BEQ only modifies PC; all pcFree assertions are preserved. -/
theorem beq_ne_spec (rs1 rs2 : Reg) (offset : BitVec 13)
    (v1 v2 : Word) (hne : v1 ≠ v2) (base : Word) :
    cpsTriple base (base + 4)
      (CodeReq.singleton base (.BEQ rs1 rs2 offset))
      ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2))
      ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2)) := by
  intro R hR s hcr hPR hpc; subst hpc
  have hfetch : s.code s.pc = some (.BEQ rs1 rs2 offset) :=
    hcr s.pc (.BEQ rs1 rs2 offset) (CodeReq.singleton_get s.pc (.BEQ rs1 rs2 offset))
  have hrs1 : s.getReg rs1 = v1 :=
    (holdsFor_regIs _ _ s).mp (holdsFor_sepConj_elim_left (holdsFor_sepConj_elim_left hPR))
  have hrs2 : s.getReg rs2 = v2 :=
    (holdsFor_regIs _ _ s).mp (holdsFor_sepConj_elim_right (holdsFor_sepConj_elim_left hPR))
  have hstep' : step s = some (execInstrBr s (.BEQ rs1 rs2 offset)) :=
    step_non_ecall_non_mem s _ hfetch (by nofun) (by nofun) (by rfl)
  have hexec' : execInstrBr s (.BEQ rs1 rs2 offset) = s.setPC (s.pc + 4) := by
    simp [execInstrBr, hrs1, hrs2, hne]
  refine ⟨1, s.setPC (s.pc + 4), ?_, by simp [MachineState.setPC], ?_⟩
  · show (step s).bind (stepN 0) = some _
    rw [hstep', hexec']; rfl
  · exact holdsFor_pcFree_setPC
      (pcFree_sepConj (pcFree_sepConj (pcFree_regIs _ _) (pcFree_regIs _ _)) hR) _ _ hPR

-- ============================================================================
-- Per-limb Specs: SLT (MSB load + signed comparison)
-- ============================================================================

/-- SLT MSB load spec (2 instructions): LD x7, LD x6.
    Loads the MSB limbs (limb 3) of both operands into x7 and x6. -/
theorem slt_msb_load_spec (off_a off_b : BitVec 12)
    (sp a3 b3 v7 v6 : Word) (base : Word)
    (hvalid_a : isValidDwordAccess (sp + signExtend12 off_a) = true)
    (hvalid_b : isValidDwordAccess (sp + signExtend12 off_b) = true) :
    let mem_a := sp + signExtend12 off_a
    let mem_b := sp + signExtend12 off_b
    let cr :=
      CodeReq.union (CodeReq.singleton base (.LD .x7 .x12 off_a))
       (CodeReq.singleton (base + 4) (.LD .x6 .x12 off_b))
    cpsTriple base (base + 8) cr
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       (mem_a ↦ₘ a3) ** (mem_b ↦ₘ b3))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ a3) ** (.x6 ↦ᵣ b3) **
       (mem_a ↦ₘ a3) ** (mem_b ↦ₘ b3)) := by
  runBlock

end EvmAsm.Rv64
