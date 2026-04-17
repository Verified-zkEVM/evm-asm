/-
  EvmAsm.Rv64.SailEquiv.ShiftProofs

  Per-instruction equivalence theorems for immediate shift instructions:
  SLLI, SRLI, SRAI.

  Key insight: prove that SAIL's `shift_bits_* v (extractLsb shamt ...)` equals
  Rv64's `v <<</>>>/sshiftRight shamt.toNat` as a direct rewrite lemma, avoiding
  the intermediate `% 64` form that simp introduces.
-/

import EvmAsm.Rv64.Execution
import EvmAsm.Rv64.SailEquiv.StateRel
import EvmAsm.Rv64.SailEquiv.MonadLemmas
import EvmAsm.Rv64.SailEquiv.ALUProofs
import LeanRV64D

open LeanRV64D.Functions
open Sail

namespace EvmAsm.Rv64.SailEquiv


-- ============================================================================
-- Shift rewrite lemmas: normalize SAIL shift expression to Rv64 form
-- ============================================================================

private theorem extractLsb_bv6_id (shamt : BitVec 6) :
    BitVec.extractLsb (↑(6 : Nat) - 1 : Int).toNat 0 shamt = shamt := by
  show BitVec.extractLsb 5 0 shamt = shamt
  apply BitVec.eq_of_toNat_eq; simp; omega

private theorem sll_extractLsb_bv6 (v : BitVec 64) (shamt : BitVec 6) :
    shift_bits_left v (Sail.BitVec.extractLsb shamt (LeanRV64D.Functions.log2_xlen -i 1) 0) =
    v <<< shamt.toNat := by
  simp only [shift_bits_left, Sail.BitVec.extractLsb, LeanRV64D.Functions.log2_xlen]
  rw [extractLsb_bv6_id]; rfl

private theorem srl_extractLsb_bv6 (v : BitVec 64) (shamt : BitVec 6) :
    shift_bits_right v (Sail.BitVec.extractLsb shamt (LeanRV64D.Functions.log2_xlen -i 1) 0) =
    v >>> shamt.toNat := by
  simp only [shift_bits_right, Sail.BitVec.extractLsb, LeanRV64D.Functions.log2_xlen]
  rw [extractLsb_bv6_id]; rfl

private theorem sra_extractLsb_bv6 (v : BitVec 64) (shamt : BitVec 6) :
    shift_bits_right_arith v (Sail.BitVec.extractLsb shamt (LeanRV64D.Functions.log2_xlen -i 1) 0) =
    BitVec.sshiftRight v shamt.toNat := by
  simp only [shift_bits_right_arith, Sail.BitVec.extractLsb, LeanRV64D.Functions.log2_xlen,
    BitVec.toNatInt]
  congr 1; simp [Int.toNat]; omega

-- ============================================================================
-- SLLI, SRLI, SRAI
-- ============================================================================

theorem slli_sail_equiv (s_rv : MachineState) (s_sail : SailState)
    (hrel : StateRel s_rv s_sail) (rd rs1 : Reg) (shamt : BitVec 6) :
    ∃ s_sail',
      runSail (execute_SHIFTIOP shamt (regToRegidx rs1) (regToRegidx rd) sop.SLLI) s_sail
        = some (RETIRE_SUCCESS, s_sail') ∧
      StateRel (execInstrBr s_rv (.SLLI rd rs1 shamt)) s_sail' := by
  unfold execute_SHIFTIOP
  simp only [runSail_bind, runSail_rX_bits_of_stateRel s_rv s_sail hrel, runSail_pure,
    sll_extractLsb_bv6]
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

theorem srli_sail_equiv (s_rv : MachineState) (s_sail : SailState)
    (hrel : StateRel s_rv s_sail) (rd rs1 : Reg) (shamt : BitVec 6) :
    ∃ s_sail',
      runSail (execute_SHIFTIOP shamt (regToRegidx rs1) (regToRegidx rd) sop.SRLI) s_sail
        = some (RETIRE_SUCCESS, s_sail') ∧
      StateRel (execInstrBr s_rv (.SRLI rd rs1 shamt)) s_sail' := by
  unfold execute_SHIFTIOP
  simp only [runSail_bind, runSail_rX_bits_of_stateRel s_rv s_sail hrel, runSail_pure,
    srl_extractLsb_bv6]
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

theorem srai_sail_equiv (s_rv : MachineState) (s_sail : SailState)
    (hrel : StateRel s_rv s_sail) (rd rs1 : Reg) (shamt : BitVec 6) :
    ∃ s_sail',
      runSail (execute_SHIFTIOP shamt (regToRegidx rs1) (regToRegidx rd) sop.SRAI) s_sail
        = some (RETIRE_SUCCESS, s_sail') ∧
      StateRel (execInstrBr s_rv (.SRAI rd rs1 shamt)) s_sail' := by
  unfold execute_SHIFTIOP
  simp only [runSail_bind, runSail_rX_bits_of_stateRel s_rv s_sail hrel, runSail_pure,
    sra_extractLsb_bv6]
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
