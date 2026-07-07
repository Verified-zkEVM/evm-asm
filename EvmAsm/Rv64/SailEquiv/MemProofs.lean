/-
  EvmAsm.Rv64.SailEquiv.MemProofs

  Per-instruction equivalence theorems for memory instructions:
  LD, SD, LW, LWU, SW, LB, LH, LBU, LHU, SB, SH.

  Each proof uses an opaque hypothesis (h_exec) asserting that the SAIL
  execute_LOAD/execute_STORE computation succeeds at the EStateM level
  and produces a state satisfying StateRel. This defers the deep vmem_read/
  vmem_write bare-mode reduction (6+ layers) to a separate verification effort.

  The h_exec hypothesis is dischargeable when:
  - The SAIL state is in bare mode (Machine privilege, satp=0)
  - The memory access is aligned
  - The relevant privilege/status registers are readable
  - The byte-level SAIL memory agrees with Rv64's doubleword memory (StateRel.mem_agree)
-/

import EvmAsm.Rv64.SailEquiv.ALUProofs

open Out.Functions
open Sail

namespace EvmAsm.Rv64.SailEquiv

-- ============================================================================
-- Doubleword loads/stores (LD/SD)
-- ============================================================================

-- `ld_sail_equiv` (doubleword load) is now DISCHARGED unconditionally as
-- `EvmAsm.Rv64.SailEquiv.ld_sail_equiv` in `VmemReduction.lean` — it takes a real
-- `StateRel` + `BareModeInv` + per-access bundle instead of the vacuous `h_exec`
-- hypothesis the other (still-deferred) memory lemmas below carry.

theorem sd_sail_equiv_stub (sRv : MachineState) (sSail : SailState)
    (rs1 rs2 : Reg) (offset : BitVec 12)
    (h_exec : ∃ sSail',
      execute_STORE offset (regToRegidx rs2) (regToRegidx rs1) 8 sSail =
        .ok RETIRE_SUCCESS sSail' ∧
      StateRel (execInstrBr sRv (.SD rs1 rs2 offset)) sSail') :
    ∃ sSail',
      runSail (execute_STORE offset (regToRegidx rs2) (regToRegidx rs1) 8) sSail
        = some (RETIRE_SUCCESS, sSail') ∧
      StateRel (execInstrBr sRv (.SD rs1 rs2 offset)) sSail' := by
  obtain ⟨s', h_ok, hrel'⟩ := h_exec
  exact ⟨s', by simp [runSail, h_ok], hrel'⟩

-- ============================================================================
-- Word loads/stores (LW/LWU/SW)
-- ============================================================================

-- `lw_sail_equiv` / `lwu_sail_equiv` are now DISCHARGED unconditionally in
-- `VmemReductionLoads.lean` (no `h_exec`); the deferred conditional versions were removed.

theorem sw_sail_equiv_stub (sRv : MachineState) (sSail : SailState)
    (rs1 rs2 : Reg) (offset : BitVec 12)
    (h_exec : ∃ sSail',
      execute_STORE offset (regToRegidx rs2) (regToRegidx rs1) 4 sSail =
        .ok RETIRE_SUCCESS sSail' ∧
      StateRel (execInstrBr sRv (.SW rs1 rs2 offset)) sSail') :
    ∃ sSail',
      runSail (execute_STORE offset (regToRegidx rs2) (regToRegidx rs1) 4) sSail
        = some (RETIRE_SUCCESS, sSail') ∧
      StateRel (execInstrBr sRv (.SW rs1 rs2 offset)) sSail' := by
  obtain ⟨s', h_ok, hrel'⟩ := h_exec
  exact ⟨s', by simp [runSail, h_ok], hrel'⟩

-- ============================================================================
-- Byte loads/stores (LB/LBU/SB)
-- ============================================================================

-- `lb_sail_equiv` / `lbu_sail_equiv` are now DISCHARGED unconditionally in
-- `VmemReductionLoads.lean` (no `h_exec`); the deferred conditional versions were removed.

theorem sb_sail_equiv_stub (sRv : MachineState) (sSail : SailState)
    (rs1 rs2 : Reg) (offset : BitVec 12)
    (h_exec : ∃ sSail',
      execute_STORE offset (regToRegidx rs2) (regToRegidx rs1) 1 sSail =
        .ok RETIRE_SUCCESS sSail' ∧
      StateRel (execInstrBr sRv (.SB rs1 rs2 offset)) sSail') :
    ∃ sSail',
      runSail (execute_STORE offset (regToRegidx rs2) (regToRegidx rs1) 1) sSail
        = some (RETIRE_SUCCESS, sSail') ∧
      StateRel (execInstrBr sRv (.SB rs1 rs2 offset)) sSail' := by
  obtain ⟨s', h_ok, hrel'⟩ := h_exec
  exact ⟨s', by simp [runSail, h_ok], hrel'⟩

-- ============================================================================
-- Halfword loads/stores (LH/LHU/SH)
-- ============================================================================

-- `lh_sail_equiv` / `lhu_sail_equiv` are now DISCHARGED unconditionally in
-- `VmemReductionLoads.lean` (no `h_exec`); the deferred conditional versions were removed.

theorem sh_sail_equiv_stub (sRv : MachineState) (sSail : SailState)
    (rs1 rs2 : Reg) (offset : BitVec 12)
    (h_exec : ∃ sSail',
      execute_STORE offset (regToRegidx rs2) (regToRegidx rs1) 2 sSail =
        .ok RETIRE_SUCCESS sSail' ∧
      StateRel (execInstrBr sRv (.SH rs1 rs2 offset)) sSail') :
    ∃ sSail',
      runSail (execute_STORE offset (regToRegidx rs2) (regToRegidx rs1) 2) sSail
        = some (RETIRE_SUCCESS, sSail') ∧
      StateRel (execInstrBr sRv (.SH rs1 rs2 offset)) sSail' := by
  obtain ⟨s', h_ok, hrel'⟩ := h_exec
  exact ⟨s', by simp [runSail, h_ok], hrel'⟩

end EvmAsm.Rv64.SailEquiv
