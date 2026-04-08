/-
  EvmAsm.Rv64.SailEquiv.UpperImmProofs

  Per-instruction equivalence theorems for upper immediate and word-size instructions:
  LUI, AUIPC, ADDIW.
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
-- LUI
-- ============================================================================

/-- LUI rd imm: execInstrBr agrees with SAIL's execute_UTYPE ... uop.LUI.
    Key lemma needed: lui_equiv (two representations of sext(imm << 12) agree). -/
theorem lui_sail_equiv (s_rv : MachineState) (s_sail : SailState)
    (hrel : StateRel s_rv s_sail) (rd : Reg) (imm : BitVec 20) :
    let s_rv' := execInstrBr s_rv (.LUI rd imm)
    ∃ s_sail',
      runSail (execute_UTYPE imm (regToRegidx rd) uop.LUI) s_sail
        = some (RETIRE_SUCCESS, s_sail') ∧
      StateRel s_rv' s_sail' := by
  sorry

-- ============================================================================
-- AUIPC
-- ============================================================================

/-- AUIPC rd imm: execInstrBr agrees with SAIL's execute_UTYPE ... uop.AUIPC.
    Both compute PC + sext(imm << 12). -/
theorem auipc_sail_equiv (s_rv : MachineState) (s_sail : SailState)
    (hrel : StateRel s_rv s_sail) (rd : Reg) (imm : BitVec 20) :
    let s_rv' := execInstrBr s_rv (.AUIPC rd imm)
    ∃ s_sail',
      runSail (execute_UTYPE imm (regToRegidx rd) uop.AUIPC) s_sail
        = some (RETIRE_SUCCESS, s_sail') ∧
      StateRel s_rv' s_sail' := by
  sorry

-- ============================================================================
-- ADDIW
-- ============================================================================

/-- ADDIW rd rs1 imm: execInstrBr agrees with SAIL's execute_ADDIW.
    Key lemma needed: addiw_equiv (truncate-then-add = add-then-truncate). -/
theorem addiw_sail_equiv (s_rv : MachineState) (s_sail : SailState)
    (hrel : StateRel s_rv s_sail) (rd rs1 : Reg) (imm : BitVec 12) :
    let s_rv' := execInstrBr s_rv (.ADDIW rd rs1 imm)
    ∃ s_sail',
      runSail (execute_ADDIW imm (regToRegidx rs1) (regToRegidx rd)) s_sail
        = some (RETIRE_SUCCESS, s_sail') ∧
      StateRel s_rv' s_sail' := by
  sorry

end EvmAsm.Rv64.SailEquiv
