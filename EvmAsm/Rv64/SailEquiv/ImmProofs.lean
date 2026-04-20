/-
  EvmAsm.Rv64.SailEquiv.ImmProofs

  Per-instruction equivalence theorems for ALU immediate instructions:
  ADDI, ANDI, ORI, XORI.

  These use execute_ITYPE which reads one register (rs1), applies an operation
  with a sign-extended 12-bit immediate, and writes the result to rd.
  Both models use BitVec.signExtend 64 for the immediate, so no helper
  equivalence lemmas are needed.
-/

import EvmAsm.Rv64.Execution
import EvmAsm.Rv64.SailEquiv.StateRel
import EvmAsm.Rv64.SailEquiv.MonadLemmas
import EvmAsm.Rv64.SailEquiv.ALUProofs  -- for reg_ne_* and reg_agree_after_insert
import LeanRV64D

open LeanRV64D.Functions
open Sail

namespace EvmAsm.Rv64.SailEquiv


-- ============================================================================
-- ADDI, ANDI, ORI, XORI
-- ============================================================================

theorem addi_sail_equiv (sRv : MachineState) (sSail : SailState)
    (hrel : StateRel sRv sSail) (rd rs1 : Reg) (imm : BitVec 12) :
    ∃ sSail',
      runSail (execute_ITYPE imm (regToRegidx rs1) (regToRegidx rd) iop.ADDI) sSail
        = some (RETIRE_SUCCESS, sSail') ∧
      StateRel (execInstrBr sRv (.ADDI rd rs1 imm)) sSail' := by
  unfold execute_ITYPE
  simp only [runSail_bind, runSail_rX_bits_of_stateRel sRv sSail hrel, runSail_pure,
    sign_extend, Sail.BitVec.signExtend]
  cases rd <;>
    simp only [regToRegidx,
      runSail_wX_bits_x0, runSail_wX_bits_x1, runSail_wX_bits_x2,
      runSail_wX_bits_x5, runSail_wX_bits_x6, runSail_wX_bits_x7,
      runSail_wX_bits_x10, runSail_wX_bits_x11, runSail_wX_bits_x12]
  all_goals first
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC, signExtend12] using reg_agree_after_insert sSail sRv hrel .x0 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC, signExtend12] using reg_agree_after_insert sSail sRv hrel .x1 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC, signExtend12] using reg_agree_after_insert sSail sRv hrel .x2 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC, signExtend12] using reg_agree_after_insert sSail sRv hrel .x5 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC, signExtend12] using reg_agree_after_insert sSail sRv hrel .x6 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC, signExtend12] using reg_agree_after_insert sSail sRv hrel .x7 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC, signExtend12] using reg_agree_after_insert sSail sRv hrel .x10 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC, signExtend12] using reg_agree_after_insert sSail sRv hrel .x11 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC, signExtend12] using reg_agree_after_insert sSail sRv hrel .x12 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩

theorem andi_sail_equiv (sRv : MachineState) (sSail : SailState)
    (hrel : StateRel sRv sSail) (rd rs1 : Reg) (imm : BitVec 12) :
    ∃ sSail',
      runSail (execute_ITYPE imm (regToRegidx rs1) (regToRegidx rd) iop.ANDI) sSail
        = some (RETIRE_SUCCESS, sSail') ∧
      StateRel (execInstrBr sRv (.ANDI rd rs1 imm)) sSail' := by
  unfold execute_ITYPE
  simp only [runSail_bind, runSail_rX_bits_of_stateRel sRv sSail hrel, runSail_pure,
    sign_extend, Sail.BitVec.signExtend]
  cases rd <;>
    simp only [regToRegidx,
      runSail_wX_bits_x0, runSail_wX_bits_x1, runSail_wX_bits_x2,
      runSail_wX_bits_x5, runSail_wX_bits_x6, runSail_wX_bits_x7,
      runSail_wX_bits_x10, runSail_wX_bits_x11, runSail_wX_bits_x12]
  all_goals first
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC, signExtend12] using reg_agree_after_insert sSail sRv hrel .x0 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC, signExtend12] using reg_agree_after_insert sSail sRv hrel .x1 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC, signExtend12] using reg_agree_after_insert sSail sRv hrel .x2 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC, signExtend12] using reg_agree_after_insert sSail sRv hrel .x5 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC, signExtend12] using reg_agree_after_insert sSail sRv hrel .x6 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC, signExtend12] using reg_agree_after_insert sSail sRv hrel .x7 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC, signExtend12] using reg_agree_after_insert sSail sRv hrel .x10 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC, signExtend12] using reg_agree_after_insert sSail sRv hrel .x11 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC, signExtend12] using reg_agree_after_insert sSail sRv hrel .x12 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩

theorem ori_sail_equiv (sRv : MachineState) (sSail : SailState)
    (hrel : StateRel sRv sSail) (rd rs1 : Reg) (imm : BitVec 12) :
    ∃ sSail',
      runSail (execute_ITYPE imm (regToRegidx rs1) (regToRegidx rd) iop.ORI) sSail
        = some (RETIRE_SUCCESS, sSail') ∧
      StateRel (execInstrBr sRv (.ORI rd rs1 imm)) sSail' := by
  unfold execute_ITYPE
  simp only [runSail_bind, runSail_rX_bits_of_stateRel sRv sSail hrel, runSail_pure,
    sign_extend, Sail.BitVec.signExtend]
  cases rd <;>
    simp only [regToRegidx,
      runSail_wX_bits_x0, runSail_wX_bits_x1, runSail_wX_bits_x2,
      runSail_wX_bits_x5, runSail_wX_bits_x6, runSail_wX_bits_x7,
      runSail_wX_bits_x10, runSail_wX_bits_x11, runSail_wX_bits_x12]
  all_goals first
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC, signExtend12] using reg_agree_after_insert sSail sRv hrel .x0 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC, signExtend12] using reg_agree_after_insert sSail sRv hrel .x1 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC, signExtend12] using reg_agree_after_insert sSail sRv hrel .x2 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC, signExtend12] using reg_agree_after_insert sSail sRv hrel .x5 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC, signExtend12] using reg_agree_after_insert sSail sRv hrel .x6 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC, signExtend12] using reg_agree_after_insert sSail sRv hrel .x7 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC, signExtend12] using reg_agree_after_insert sSail sRv hrel .x10 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC, signExtend12] using reg_agree_after_insert sSail sRv hrel .x11 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC, signExtend12] using reg_agree_after_insert sSail sRv hrel .x12 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩

theorem xori_sail_equiv (sRv : MachineState) (sSail : SailState)
    (hrel : StateRel sRv sSail) (rd rs1 : Reg) (imm : BitVec 12) :
    ∃ sSail',
      runSail (execute_ITYPE imm (regToRegidx rs1) (regToRegidx rd) iop.XORI) sSail
        = some (RETIRE_SUCCESS, sSail') ∧
      StateRel (execInstrBr sRv (.XORI rd rs1 imm)) sSail' := by
  unfold execute_ITYPE
  simp only [runSail_bind, runSail_rX_bits_of_stateRel sRv sSail hrel, runSail_pure,
    sign_extend, Sail.BitVec.signExtend]
  cases rd <;>
    simp only [regToRegidx,
      runSail_wX_bits_x0, runSail_wX_bits_x1, runSail_wX_bits_x2,
      runSail_wX_bits_x5, runSail_wX_bits_x6, runSail_wX_bits_x7,
      runSail_wX_bits_x10, runSail_wX_bits_x11, runSail_wX_bits_x12]
  all_goals first
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC, signExtend12] using reg_agree_after_insert sSail sRv hrel .x0 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC, signExtend12] using reg_agree_after_insert sSail sRv hrel .x1 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC, signExtend12] using reg_agree_after_insert sSail sRv hrel .x2 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC, signExtend12] using reg_agree_after_insert sSail sRv hrel .x5 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC, signExtend12] using reg_agree_after_insert sSail sRv hrel .x6 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC, signExtend12] using reg_agree_after_insert sSail sRv hrel .x7 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC, signExtend12] using reg_agree_after_insert sSail sRv hrel .x10 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC, signExtend12] using reg_agree_after_insert sSail sRv hrel .x11 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC, signExtend12] using reg_agree_after_insert sSail sRv hrel .x12 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩

-- ============================================================================
-- SLTI, SLTIU (immediate comparisons)
-- ============================================================================

theorem slti_sail_equiv (sRv : MachineState) (sSail : SailState)
    (hrel : StateRel sRv sSail) (rd rs1 : Reg) (imm : BitVec 12) :
    ∃ sSail',
      runSail (execute_ITYPE imm (regToRegidx rs1) (regToRegidx rd) iop.SLTI) sSail
        = some (RETIRE_SUCCESS, sSail') ∧
      StateRel (execInstrBr sRv (.SLTI rd rs1 imm)) sSail' := by
  unfold execute_ITYPE
  simp only [runSail_bind, runSail_rX_bits_of_stateRel sRv sSail hrel, runSail_pure,
    sign_extend, Sail.BitVec.signExtend, slt_value_equiv]
  cases rd <;>
    simp only [regToRegidx,
      runSail_wX_bits_x0, runSail_wX_bits_x1, runSail_wX_bits_x2,
      runSail_wX_bits_x5, runSail_wX_bits_x6, runSail_wX_bits_x7,
      runSail_wX_bits_x10, runSail_wX_bits_x11, runSail_wX_bits_x12]
  all_goals first
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC, signExtend12] using reg_agree_after_insert sSail sRv hrel .x0 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC, signExtend12] using reg_agree_after_insert sSail sRv hrel .x1 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC, signExtend12] using reg_agree_after_insert sSail sRv hrel .x2 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC, signExtend12] using reg_agree_after_insert sSail sRv hrel .x5 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC, signExtend12] using reg_agree_after_insert sSail sRv hrel .x6 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC, signExtend12] using reg_agree_after_insert sSail sRv hrel .x7 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC, signExtend12] using reg_agree_after_insert sSail sRv hrel .x10 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC, signExtend12] using reg_agree_after_insert sSail sRv hrel .x11 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC, signExtend12] using reg_agree_after_insert sSail sRv hrel .x12 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩

theorem sltiu_sail_equiv (sRv : MachineState) (sSail : SailState)
    (hrel : StateRel sRv sSail) (rd rs1 : Reg) (imm : BitVec 12) :
    ∃ sSail',
      runSail (execute_ITYPE imm (regToRegidx rs1) (regToRegidx rd) iop.SLTIU) sSail
        = some (RETIRE_SUCCESS, sSail') ∧
      StateRel (execInstrBr sRv (.SLTIU rd rs1 imm)) sSail' := by
  unfold execute_ITYPE
  simp only [runSail_bind, runSail_rX_bits_of_stateRel sRv sSail hrel, runSail_pure,
    sign_extend, Sail.BitVec.signExtend, sltu_value_equiv]
  cases rd <;>
    simp only [regToRegidx,
      runSail_wX_bits_x0, runSail_wX_bits_x1, runSail_wX_bits_x2,
      runSail_wX_bits_x5, runSail_wX_bits_x6, runSail_wX_bits_x7,
      runSail_wX_bits_x10, runSail_wX_bits_x11, runSail_wX_bits_x12]
  all_goals first
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC, signExtend12] using reg_agree_after_insert sSail sRv hrel .x0 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC, signExtend12] using reg_agree_after_insert sSail sRv hrel .x1 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC, signExtend12] using reg_agree_after_insert sSail sRv hrel .x2 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC, signExtend12] using reg_agree_after_insert sSail sRv hrel .x5 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC, signExtend12] using reg_agree_after_insert sSail sRv hrel .x6 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC, signExtend12] using reg_agree_after_insert sSail sRv hrel .x7 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC, signExtend12] using reg_agree_after_insert sSail sRv hrel .x10 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC, signExtend12] using reg_agree_after_insert sSail sRv hrel .x11 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC, signExtend12] using reg_agree_after_insert sSail sRv hrel .x12 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩

-- ============================================================================
-- MV (pseudo: ADDI rd rs 0), NOP (pseudo: ADDI x0 x0 0)
-- ============================================================================

theorem mv_sail_equiv (sRv : MachineState) (sSail : SailState)
    (hrel : StateRel sRv sSail) (rd rs : Reg) :
    ∃ sSail',
      runSail (execute_ITYPE 0 (regToRegidx rs) (regToRegidx rd) iop.ADDI) sSail
        = some (RETIRE_SUCCESS, sSail') ∧
      StateRel (execInstrBr sRv (.MV rd rs)) sSail' := by
  unfold execute_ITYPE
  simp only [runSail_bind, runSail_rX_bits_of_stateRel sRv sSail hrel, runSail_pure,
    sign_extend, Sail.BitVec.signExtend]
  cases rd <;>
    simp only [regToRegidx,
      runSail_wX_bits_x0, runSail_wX_bits_x1, runSail_wX_bits_x2,
      runSail_wX_bits_x5, runSail_wX_bits_x6, runSail_wX_bits_x7,
      runSail_wX_bits_x10, runSail_wX_bits_x11, runSail_wX_bits_x12]
  all_goals first
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert sSail sRv hrel .x0 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert sSail sRv hrel .x1 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert sSail sRv hrel .x2 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert sSail sRv hrel .x5 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert sSail sRv hrel .x6 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert sSail sRv hrel .x7 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert sSail sRv hrel .x10 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert sSail sRv hrel .x11 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert sSail sRv hrel .x12 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩

theorem nop_sail_equiv (sRv : MachineState) (sSail : SailState)
    (hrel : StateRel sRv sSail) :
    ∃ sSail',
      runSail (execute_ITYPE 0 (regidx.Regidx 0) (regidx.Regidx 0) iop.ADDI) sSail
        = some (RETIRE_SUCCESS, sSail') ∧
      StateRel (execInstrBr sRv .NOP) sSail' := by
  unfold execute_ITYPE
  simp only [runSail_bind, runSail_rX_bits_x0, runSail_pure,
    sign_extend, Sail.BitVec.signExtend, runSail_wX_bits_x0]
  exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using hrel.reg_agree r,
    fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩

end EvmAsm.Rv64.SailEquiv
