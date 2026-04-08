/-
  EvmAsm.Rv64.SailEquiv.MiscProofs

  Per-instruction equivalence theorems for pseudo-instructions and system instructions:
  MV, LI, NOP, FENCE, EBREAK.

  ECALL is intentionally omitted — Rv64 treats it as a NOP (zkVM syscall semantics
  are defined separately), while SAIL traps. This is an intentional divergence.
-/

import EvmAsm.Rv64.Execution
import EvmAsm.Rv64.SailEquiv.StateRel
import EvmAsm.Rv64.SailEquiv.InstrMap
import EvmAsm.Rv64.SailEquiv.MonadLemmas
import EvmAsm.Rv64.SailEquiv.HelperEquiv

open LeanRV64D.Functions
open LeanRV64D.Defs

namespace EvmAsm.Rv64.SailEquiv

-- ============================================================================
-- Pseudo-instructions
-- ============================================================================

/-- MV rd rs: equivalent to ADDI rd rs 0.
    Both Rv64 and SAIL compute getReg(rs) + 0 = getReg(rs). -/
theorem mv_sail_equiv (s_rv : MachineState) (s_sail : SailState)
    (hrel : StateRel s_rv s_sail) (rd rs : Reg) :
    let s_rv' := execInstrBr s_rv (.MV rd rs)
    ∃ s_sail',
      runSail (execute_ITYPE 0 (regToRegidx rs) (regToRegidx rd) iop.ADDI) s_sail
        = some (RETIRE_SUCCESS, s_sail') ∧
      StateRel s_rv' s_sail' := by
  sorry

/-- NOP: equivalent to ADDI x0 x0 0.
    Both models leave all state unchanged (except PC += 4). -/
theorem nop_sail_equiv (s_rv : MachineState) (s_sail : SailState)
    (hrel : StateRel s_rv s_sail) :
    let s_rv' := execInstrBr s_rv .NOP
    ∃ s_sail',
      runSail (execute_ITYPE 0 (Regidx 0) (Regidx 0) iop.ADDI) s_sail
        = some (RETIRE_SUCCESS, s_sail') ∧
      StateRel s_rv' s_sail' := by
  sorry

-- ============================================================================
-- System instructions
-- ============================================================================

/-- FENCE: memory ordering NOP in single-hart zkVM.
    Note: We map FENCE to FENCE_TSO in SAIL, which is also a NOP for ordering
    in a single-hart model. Both leave state unchanged. -/
theorem fence_sail_equiv (s_rv : MachineState) (s_sail : SailState)
    (hrel : StateRel s_rv s_sail) :
    let s_rv' := execInstrBr s_rv .FENCE
    -- FENCE_TSO is the closest SAIL equivalent for a single-hart NOP
    StateRel s_rv' s_sail := by  -- no SAIL state change needed
  sorry

/-- EBREAK: breakpoint trap. Both models treat as NOP for state. -/
theorem ebreak_sail_equiv (s_rv : MachineState) (s_sail : SailState)
    (hrel : StateRel s_rv s_sail) :
    let s_rv' := execInstrBr s_rv .EBREAK
    ∃ s_sail',
      runSail (execute (.EBREAK ())) s_sail
        = some (RETIRE_SUCCESS, s_sail') ∧
      StateRel s_rv' s_sail' := by
  sorry

-- ============================================================================
-- LI (pseudo-instruction)
-- ============================================================================

/-- LI rd imm for small immediates that fit in 12 bits:
    equivalent to ADDI rd x0 imm.
    Note: For larger immediates, LI expands to LUI+ADDI or longer sequences.
    This theorem only covers the single-instruction case. -/
theorem li_small_sail_equiv (s_rv : MachineState) (s_sail : SailState)
    (hrel : StateRel s_rv s_sail) (rd : Reg) (imm : BitVec 12) :
    let s_rv' := execInstrBr s_rv (.LI rd (signExtend12 imm))
    ∃ s_sail',
      runSail (execute_ITYPE imm (Regidx 0) (regToRegidx rd) iop.ADDI) s_sail
        = some (RETIRE_SUCCESS, s_sail') ∧
      StateRel s_rv' s_sail' := by
  sorry

-- ============================================================================
-- Master equivalence theorem
-- ============================================================================

/-- For any non-pseudo, non-ECALL instruction, execInstrBr on the Rv64 model
    agrees with execute on the SAIL model (modulo StateRel). -/
theorem execInstrBr_sail_equiv (s_rv : MachineState) (s_sail : SailState)
    (hrel : StateRel s_rv s_sail) (i : Instr)
    (h_not_ecall : i ≠ .ECALL)
    (h_not_li : ∀ rd imm, i ≠ .LI rd imm)
    (h_not_mv : ∀ rd rs, i ≠ .MV rd rs)
    (h_not_nop : i ≠ .NOP)
    (h_not_fence : i ≠ .FENCE)
    (h_not_ebreak : i ≠ .EBREAK) :
    let s_rv' := execInstrBr s_rv i
    ∃ s_sail',
      runSail (execute (toSailInstr i)) s_sail = some (RETIRE_SUCCESS, s_sail') ∧
      StateRel s_rv' s_sail' := by
  sorry

end EvmAsm.Rv64.SailEquiv
