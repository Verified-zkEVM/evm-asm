/-
  EvmAsm.Rv64.SailEquiv.ALUProofs

  Per-instruction equivalence theorems for ALU register-register instructions:
  ADD, SUB, AND, OR, XOR.

  Each theorem proves StateRel is preserved: given StateRel before execution,
  StateRel holds between the Rv64 result and the SAIL result.
-/

import EvmAsm.Rv64.Execution
import EvmAsm.Rv64.SailEquiv.StateRel
import EvmAsm.Rv64.SailEquiv.MonadLemmas
import LeanRV64D

open LeanRV64D.Functions
open Sail

namespace EvmAsm.Rv64.SailEquiv

set_option maxHeartbeats 1600000

-- ============================================================================
-- Register inequality facts (pre-proved via native_decide)
-- ============================================================================

private theorem reg_ne_x1_x2 : (Register.x1 == Register.x2) = false := by native_decide
private theorem reg_ne_x1_x5 : (Register.x1 == Register.x5) = false := by native_decide
private theorem reg_ne_x1_x6 : (Register.x1 == Register.x6) = false := by native_decide
private theorem reg_ne_x1_x7 : (Register.x1 == Register.x7) = false := by native_decide
private theorem reg_ne_x1_x10 : (Register.x1 == Register.x10) = false := by native_decide
private theorem reg_ne_x1_x11 : (Register.x1 == Register.x11) = false := by native_decide
private theorem reg_ne_x1_x12 : (Register.x1 == Register.x12) = false := by native_decide
private theorem reg_ne_x2_x1 : (Register.x2 == Register.x1) = false := by native_decide
private theorem reg_ne_x2_x5 : (Register.x2 == Register.x5) = false := by native_decide
private theorem reg_ne_x2_x6 : (Register.x2 == Register.x6) = false := by native_decide
private theorem reg_ne_x2_x7 : (Register.x2 == Register.x7) = false := by native_decide
private theorem reg_ne_x2_x10 : (Register.x2 == Register.x10) = false := by native_decide
private theorem reg_ne_x2_x11 : (Register.x2 == Register.x11) = false := by native_decide
private theorem reg_ne_x2_x12 : (Register.x2 == Register.x12) = false := by native_decide
private theorem reg_ne_x5_x1 : (Register.x5 == Register.x1) = false := by native_decide
private theorem reg_ne_x5_x2 : (Register.x5 == Register.x2) = false := by native_decide
private theorem reg_ne_x5_x6 : (Register.x5 == Register.x6) = false := by native_decide
private theorem reg_ne_x5_x7 : (Register.x5 == Register.x7) = false := by native_decide
private theorem reg_ne_x5_x10 : (Register.x5 == Register.x10) = false := by native_decide
private theorem reg_ne_x5_x11 : (Register.x5 == Register.x11) = false := by native_decide
private theorem reg_ne_x5_x12 : (Register.x5 == Register.x12) = false := by native_decide
private theorem reg_ne_x6_x1 : (Register.x6 == Register.x1) = false := by native_decide
private theorem reg_ne_x6_x2 : (Register.x6 == Register.x2) = false := by native_decide
private theorem reg_ne_x6_x5 : (Register.x6 == Register.x5) = false := by native_decide
private theorem reg_ne_x6_x7 : (Register.x6 == Register.x7) = false := by native_decide
private theorem reg_ne_x6_x10 : (Register.x6 == Register.x10) = false := by native_decide
private theorem reg_ne_x6_x11 : (Register.x6 == Register.x11) = false := by native_decide
private theorem reg_ne_x6_x12 : (Register.x6 == Register.x12) = false := by native_decide
private theorem reg_ne_x7_x1 : (Register.x7 == Register.x1) = false := by native_decide
private theorem reg_ne_x7_x2 : (Register.x7 == Register.x2) = false := by native_decide
private theorem reg_ne_x7_x5 : (Register.x7 == Register.x5) = false := by native_decide
private theorem reg_ne_x7_x6 : (Register.x7 == Register.x6) = false := by native_decide
private theorem reg_ne_x7_x10 : (Register.x7 == Register.x10) = false := by native_decide
private theorem reg_ne_x7_x11 : (Register.x7 == Register.x11) = false := by native_decide
private theorem reg_ne_x7_x12 : (Register.x7 == Register.x12) = false := by native_decide
private theorem reg_ne_x10_x1 : (Register.x10 == Register.x1) = false := by native_decide
private theorem reg_ne_x10_x2 : (Register.x10 == Register.x2) = false := by native_decide
private theorem reg_ne_x10_x5 : (Register.x10 == Register.x5) = false := by native_decide
private theorem reg_ne_x10_x6 : (Register.x10 == Register.x6) = false := by native_decide
private theorem reg_ne_x10_x7 : (Register.x10 == Register.x7) = false := by native_decide
private theorem reg_ne_x10_x11 : (Register.x10 == Register.x11) = false := by native_decide
private theorem reg_ne_x10_x12 : (Register.x10 == Register.x12) = false := by native_decide
private theorem reg_ne_x11_x1 : (Register.x11 == Register.x1) = false := by native_decide
private theorem reg_ne_x11_x2 : (Register.x11 == Register.x2) = false := by native_decide
private theorem reg_ne_x11_x5 : (Register.x11 == Register.x5) = false := by native_decide
private theorem reg_ne_x11_x6 : (Register.x11 == Register.x6) = false := by native_decide
private theorem reg_ne_x11_x7 : (Register.x11 == Register.x7) = false := by native_decide
private theorem reg_ne_x11_x10 : (Register.x11 == Register.x10) = false := by native_decide
private theorem reg_ne_x11_x12 : (Register.x11 == Register.x12) = false := by native_decide
private theorem reg_ne_x12_x1 : (Register.x12 == Register.x1) = false := by native_decide
private theorem reg_ne_x12_x2 : (Register.x12 == Register.x2) = false := by native_decide
private theorem reg_ne_x12_x5 : (Register.x12 == Register.x5) = false := by native_decide
private theorem reg_ne_x12_x6 : (Register.x12 == Register.x6) = false := by native_decide
private theorem reg_ne_x12_x7 : (Register.x12 == Register.x7) = false := by native_decide
private theorem reg_ne_x12_x10 : (Register.x12 == Register.x10) = false := by native_decide
private theorem reg_ne_x12_x11 : (Register.x12 == Register.x11) = false := by native_decide

-- ============================================================================
-- Bridge: reg_agree after a register insert (9x9 case split)
-- ============================================================================

theorem reg_agree_after_insert (s_sail : SailState) (s_rv : MachineState)
    (hrel : StateRel s_rv s_sail) (rd : Reg) (v : BitVec 64) :
    ∀ r : Reg, sailRegVal
      (match rd with
        | .x0 => s_sail
        | .x1 => { s_sail with regs := s_sail.regs.insert Register.x1 v }
        | .x2 => { s_sail with regs := s_sail.regs.insert Register.x2 v }
        | .x5 => { s_sail with regs := s_sail.regs.insert Register.x5 v }
        | .x6 => { s_sail with regs := s_sail.regs.insert Register.x6 v }
        | .x7 => { s_sail with regs := s_sail.regs.insert Register.x7 v }
        | .x10 => { s_sail with regs := s_sail.regs.insert Register.x10 v }
        | .x11 => { s_sail with regs := s_sail.regs.insert Register.x11 v }
        | .x12 => { s_sail with regs := s_sail.regs.insert Register.x12 v }) r =
      some ((s_rv.setReg rd v).getReg r) := by
  intro r
  set_option maxHeartbeats 800000 in
  cases rd <;> cases r <;>
    simp only [sailRegVal, MachineState.setReg, MachineState.getReg,
      Std.ExtDHashMap.get?_insert_self, Std.ExtDHashMap.get?_insert,
      beq_self_eq_true, ite_true, ite_false, decide_true, decide_false,
      reg_ne_x1_x2, reg_ne_x1_x5, reg_ne_x1_x6, reg_ne_x1_x7,
      reg_ne_x1_x10, reg_ne_x1_x11, reg_ne_x1_x12,
      reg_ne_x2_x1, reg_ne_x2_x5, reg_ne_x2_x6, reg_ne_x2_x7,
      reg_ne_x2_x10, reg_ne_x2_x11, reg_ne_x2_x12,
      reg_ne_x5_x1, reg_ne_x5_x2, reg_ne_x5_x6, reg_ne_x5_x7,
      reg_ne_x5_x10, reg_ne_x5_x11, reg_ne_x5_x12,
      reg_ne_x6_x1, reg_ne_x6_x2, reg_ne_x6_x5, reg_ne_x6_x7,
      reg_ne_x6_x10, reg_ne_x6_x11, reg_ne_x6_x12,
      reg_ne_x7_x1, reg_ne_x7_x2, reg_ne_x7_x5, reg_ne_x7_x6,
      reg_ne_x7_x10, reg_ne_x7_x11, reg_ne_x7_x12,
      reg_ne_x10_x1, reg_ne_x10_x2, reg_ne_x10_x5, reg_ne_x10_x6,
      reg_ne_x10_x7, reg_ne_x10_x11, reg_ne_x10_x12,
      reg_ne_x11_x1, reg_ne_x11_x2, reg_ne_x11_x5, reg_ne_x11_x6,
      reg_ne_x11_x7, reg_ne_x11_x10, reg_ne_x11_x12,
      reg_ne_x12_x1, reg_ne_x12_x2, reg_ne_x12_x5, reg_ne_x12_x6,
      reg_ne_x12_x7, reg_ne_x12_x10, reg_ne_x12_x11,
      dite_true, dite_false] <;>
    all_goals (first | rfl | (
      have ha := hrel.reg_agree
      first
        | (have := ha .x1; simp [sailRegVal, MachineState.getReg] at this; exact this)
        | (have := ha .x2; simp [sailRegVal, MachineState.getReg] at this; exact this)
        | (have := ha .x5; simp [sailRegVal, MachineState.getReg] at this; exact this)
        | (have := ha .x6; simp [sailRegVal, MachineState.getReg] at this; exact this)
        | (have := ha .x7; simp [sailRegVal, MachineState.getReg] at this; exact this)
        | (have := ha .x10; simp [sailRegVal, MachineState.getReg] at this; exact this)
        | (have := ha .x11; simp [sailRegVal, MachineState.getReg] at this; exact this)
        | (have := ha .x12; simp [sailRegVal, MachineState.getReg] at this; exact this)))

-- ============================================================================
-- ADD, SUB, AND, OR, XOR
-- ============================================================================

-- The proof pattern: unfold execute_RTYPE, bridge rX_bits reads, case-split rd
-- for wX_bits, witness state, build StateRel (reg_agree from bridge + mem_agree trivial).

theorem add_sail_equiv (s_rv : MachineState) (s_sail : SailState)
    (hrel : StateRel s_rv s_sail) (rd rs1 rs2 : Reg) :
    ∃ s_sail',
      runSail (execute_RTYPE (regToRegidx rs2) (regToRegidx rs1) (regToRegidx rd) rop.ADD) s_sail
        = some (RETIRE_SUCCESS, s_sail') ∧
      StateRel (execInstrBr s_rv (.ADD rd rs1 rs2)) s_sail' := by
  unfold execute_RTYPE
  simp only [runSail_bind, runSail_rX_bits_of_stateRel s_rv s_sail hrel, runSail_pure]
  cases rd <;>
    simp only [regToRegidx,
      runSail_wX_bits_x0, runSail_wX_bits_x1, runSail_wX_bits_x2,
      runSail_wX_bits_x5, runSail_wX_bits_x6, runSail_wX_bits_x7,
      runSail_wX_bits_x10, runSail_wX_bits_x11, runSail_wX_bits_x12]
  -- Each goal after `cases rd`: witness state, build StateRel with concrete rd
  all_goals first
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x0 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x1 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x2 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x5 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x6 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x7 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x10 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x11 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x12 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩

theorem sub_sail_equiv (s_rv : MachineState) (s_sail : SailState)
    (hrel : StateRel s_rv s_sail) (rd rs1 rs2 : Reg) :
    ∃ s_sail',
      runSail (execute_RTYPE (regToRegidx rs2) (regToRegidx rs1) (regToRegidx rd) rop.SUB) s_sail
        = some (RETIRE_SUCCESS, s_sail') ∧
      StateRel (execInstrBr s_rv (.SUB rd rs1 rs2)) s_sail' := by
  unfold execute_RTYPE
  simp only [runSail_bind, runSail_rX_bits_of_stateRel s_rv s_sail hrel, runSail_pure]
  cases rd <;>
    simp only [regToRegidx,
      runSail_wX_bits_x0, runSail_wX_bits_x1, runSail_wX_bits_x2,
      runSail_wX_bits_x5, runSail_wX_bits_x6, runSail_wX_bits_x7,
      runSail_wX_bits_x10, runSail_wX_bits_x11, runSail_wX_bits_x12]
  all_goals first
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x0 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x1 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x2 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x5 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x6 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x7 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x10 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x11 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x12 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩

theorem and_sail_equiv (s_rv : MachineState) (s_sail : SailState)
    (hrel : StateRel s_rv s_sail) (rd rs1 rs2 : Reg) :
    ∃ s_sail',
      runSail (execute_RTYPE (regToRegidx rs2) (regToRegidx rs1) (regToRegidx rd) rop.AND) s_sail
        = some (RETIRE_SUCCESS, s_sail') ∧
      StateRel (execInstrBr s_rv (.AND rd rs1 rs2)) s_sail' := by
  unfold execute_RTYPE
  simp only [runSail_bind, runSail_rX_bits_of_stateRel s_rv s_sail hrel, runSail_pure]
  cases rd <;>
    simp only [regToRegidx,
      runSail_wX_bits_x0, runSail_wX_bits_x1, runSail_wX_bits_x2,
      runSail_wX_bits_x5, runSail_wX_bits_x6, runSail_wX_bits_x7,
      runSail_wX_bits_x10, runSail_wX_bits_x11, runSail_wX_bits_x12]
  all_goals first
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x0 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x1 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x2 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x5 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x6 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x7 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x10 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x11 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x12 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩

theorem or_sail_equiv (s_rv : MachineState) (s_sail : SailState)
    (hrel : StateRel s_rv s_sail) (rd rs1 rs2 : Reg) :
    ∃ s_sail',
      runSail (execute_RTYPE (regToRegidx rs2) (regToRegidx rs1) (regToRegidx rd) rop.OR) s_sail
        = some (RETIRE_SUCCESS, s_sail') ∧
      StateRel (execInstrBr s_rv (.OR rd rs1 rs2)) s_sail' := by
  unfold execute_RTYPE
  simp only [runSail_bind, runSail_rX_bits_of_stateRel s_rv s_sail hrel, runSail_pure]
  cases rd <;>
    simp only [regToRegidx,
      runSail_wX_bits_x0, runSail_wX_bits_x1, runSail_wX_bits_x2,
      runSail_wX_bits_x5, runSail_wX_bits_x6, runSail_wX_bits_x7,
      runSail_wX_bits_x10, runSail_wX_bits_x11, runSail_wX_bits_x12]
  all_goals first
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x0 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x1 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x2 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x5 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x6 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x7 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x10 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x11 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x12 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩

theorem xor_sail_equiv (s_rv : MachineState) (s_sail : SailState)
    (hrel : StateRel s_rv s_sail) (rd rs1 rs2 : Reg) :
    ∃ s_sail',
      runSail (execute_RTYPE (regToRegidx rs2) (regToRegidx rs1) (regToRegidx rd) rop.XOR) s_sail
        = some (RETIRE_SUCCESS, s_sail') ∧
      StateRel (execInstrBr s_rv (.XOR rd rs1 rs2)) s_sail' := by
  unfold execute_RTYPE
  simp only [runSail_bind, runSail_rX_bits_of_stateRel s_rv s_sail hrel, runSail_pure]
  cases rd <;>
    simp only [regToRegidx,
      runSail_wX_bits_x0, runSail_wX_bits_x1, runSail_wX_bits_x2,
      runSail_wX_bits_x5, runSail_wX_bits_x6, runSail_wX_bits_x7,
      runSail_wX_bits_x10, runSail_wX_bits_x11, runSail_wX_bits_x12]
  all_goals first
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x0 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x1 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x2 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x5 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x6 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x7 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x10 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x11 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert s_sail s_rv hrel .x12 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩

end EvmAsm.Rv64.SailEquiv
