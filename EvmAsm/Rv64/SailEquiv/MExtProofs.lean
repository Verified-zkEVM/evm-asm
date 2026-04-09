/-
  EvmAsm.Rv64.SailEquiv.MExtProofs

  Per-instruction equivalence theorems for M-extension instructions:
  MULH, MULHSU, MULHU, DIV, DIVU, REM, REMU.

  MUL (low 64 bits) is already proved in ALUProofs.lean.
-/

import EvmAsm.Rv64.Execution
import EvmAsm.Rv64.SailEquiv.StateRel
import EvmAsm.Rv64.SailEquiv.MonadLemmas
import EvmAsm.Rv64.SailEquiv.ALUProofs
import LeanRV64D

open LeanRV64D.Functions
open Sail

namespace EvmAsm.Rv64.SailEquiv

set_option maxHeartbeats 1600000
set_option maxRecDepth 2000

-- ============================================================================
-- Proved helper lemmas for division/remainder
-- ============================================================================

/-- to_bits_truncate on a non-negative integer = BitVec.ofNat. -/
theorem to_bits_truncate_natCast (n : Nat) :
    to_bits_truncate (l := 64) (↑n : Int) = BitVec.ofNat 64 n := by
  simp [to_bits_truncate, get_slice_int]; apply BitVec.eq_of_toNat_eq; simp

/-- to_bits_truncate (-1) = allOnes 64. -/
theorem to_bits_truncate_neg1 :
    to_bits_truncate (l := 64) (-1 : Int) = BitVec.allOnes 64 := by
  simp [to_bits_truncate, get_slice_int, BitVec.allOnes]

/-- to_bits_truncate roundtrips through toNatInt (unsigned interpretation). -/
theorem to_bits_truncate_toNatInt (a : BitVec 64) :
    to_bits_truncate (l := 64) (BitVec.toNatInt a) = a := by
  simp [BitVec.toNatInt, to_bits_truncate, get_slice_int]
  apply BitVec.eq_of_toNat_eq; simp; omega

/-- BEq bridge: Int.ofNat b.toNat == 0 ↔ b == 0#64. -/
theorem int_ofNat_beq_zero (b : BitVec 64) :
    (Int.ofNat b.toNat == (0 : Int)) = (b == 0#64) := by
  simp [BEq.beq, decide_eq_decide]
  constructor
  · intro h; exact BitVec.eq_of_toNat_eq (by simp; omega)
  · intro h; subst h; simp

/-- Unsigned division: SAIL's Int.tdiv on non-negative = BitVec udiv. -/
theorem unsigned_div_equiv (a b : BitVec 64) (hb : b ≠ 0#64) :
    to_bits_truncate (l := 64) ((↑a.toNat : Int).tdiv (↑b.toNat : Int)) = a / b := by
  rw [(Int.ofNat_tdiv a.toNat b.toNat).symm, to_bits_truncate_natCast]
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_udiv]
  exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) a.isLt

/-- Unsigned remainder: SAIL's Int.tmod on non-negative = BitVec umod. -/
theorem unsigned_rem_equiv (a b : BitVec 64) (hb : b ≠ 0#64) :
    to_bits_truncate (l := 64) ((↑a.toNat : Int).tmod (↑b.toNat : Int)) = a % b := by
  have hbn : b.toNat ≠ 0 := by intro h; exact hb (BitVec.eq_of_toNat_eq (by simp [h]))
  rw [(Int.ofNat_tmod a.toNat b.toNat).symm, to_bits_truncate_natCast]
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_umod]
  have : a.toNat % b.toNat < b.toNat := Nat.mod_lt _ (by omega)
  omega

-- ============================================================================
-- Signed division/remainder core equivalences
-- ============================================================================

/-- to_bits_truncate is equivalent to BitVec.ofInt. -/
theorem to_bits_truncate_eq_ofInt (x : Int) :
    to_bits_truncate (l := 64) x = BitVec.ofInt 64 x := by
  simp [to_bits_truncate, get_slice_int]
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_ofInt]; omega

/-- Signed division: to_bits_truncate of Int.tdiv = BitVec.sdiv. -/
theorem signed_div_equiv (a b : BitVec 64) :
    to_bits_truncate (l := 64) (a.toInt.tdiv b.toInt) = BitVec.sdiv a b := by
  rw [to_bits_truncate_eq_ofInt,
    show a.sdiv b = BitVec.ofInt 64 (a.sdiv b).toInt from BitVec.ofInt_toInt.symm,
    BitVec.toInt_sdiv]
  apply BitVec.eq_of_toInt_eq; simp [BitVec.toInt_ofInt]

/-- Signed remainder: to_bits_truncate of Int.tmod = BitVec.srem. -/
theorem signed_rem_equiv (a b : BitVec 64) :
    to_bits_truncate (l := 64) (a.toInt.tmod b.toInt) = BitVec.srem a b := by
  rw [to_bits_truncate_eq_ofInt,
    show BitVec.ofInt 64 (a.toInt.tmod b.toInt) = BitVec.ofInt 64 (a.srem b).toInt from by
      rw [BitVec.toInt_srem]]
  exact BitVec.ofInt_toInt

/-- to_bits_truncate roundtrips through toInt (signed interpretation). -/
theorem to_bits_truncate_toInt (a : BitVec 64) :
    to_bits_truncate (l := 64) a.toInt = a := by
  rw [to_bits_truncate_eq_ofInt]; exact BitVec.ofInt_toInt

/-- BEq bridge for signed zero check: b.toInt == 0 ↔ b == 0#64. -/
theorem int_toInt_beq_zero (b : BitVec 64) :
    (b.toInt == (0 : Int)) = (b == 0#64) := by
  simp [BEq.beq, decide_eq_decide, BitVec.toInt]
  constructor
  · intro h; split at h <;> (apply BitVec.eq_of_toNat_eq; simp at h ⊢; omega)
  · intro h; subst h; simp

-- ============================================================================
-- Value equivalence wrappers (match exact post-simp SAIL form)
-- ============================================================================

/-- DIVU value equivalence: SAIL unsigned division computation = rv64_divu. -/
theorem divu_full_equiv (a b : BitVec 64) :
    to_bits_truncate (l := 64)
      (if ((BitVec.toNatInt b == (0 : Int)) : Bool) then (-1 : Int)
       else (BitVec.toNatInt a).tdiv (BitVec.toNatInt b)) =
    rv64_divu a b := by
  unfold rv64_divu BitVec.toNatInt; rw [int_ofNat_beq_zero]
  by_cases hb : b = 0#64
  · subst hb; simp [to_bits_truncate_neg1]
  · simp only [show (b == 0#64) = false from by simp [hb], ite_false, Bool.false_eq_true]
    exact unsigned_div_equiv a b hb

/-- REMU value equivalence: SAIL unsigned remainder computation = rv64_remu. -/
theorem remu_full_equiv (a b : BitVec 64) :
    to_bits_truncate (l := 64)
      (if ((BitVec.toNatInt b == (0 : Int)) : Bool) then (BitVec.toNatInt a)
       else (BitVec.toNatInt a).tmod (BitVec.toNatInt b)) =
    rv64_remu a b := by
  unfold rv64_remu BitVec.toNatInt; rw [int_ofNat_beq_zero]
  by_cases hb : b = 0#64
  · subst hb; simp [to_bits_truncate_natCast]
  · simp only [show (b == 0#64) = false from by simp [hb], ite_false, Bool.false_eq_true]
    exact unsigned_rem_equiv a b hb

-- ============================================================================
-- Instruction proofs
-- ============================================================================

theorem mulh_sail_equiv (s_rv : MachineState) (s_sail : SailState)
    (hrel : StateRel s_rv s_sail) (rd rs1 rs2 : Reg) :
    ∃ s_sail',
      runSail (execute_MUL (regToRegidx rs2) (regToRegidx rs1) (regToRegidx rd)
        { result_part := VectorHalf.High, signed_rs1 := Signedness.Signed,
          signed_rs2 := Signedness.Signed }) s_sail
        = some (RETIRE_SUCCESS, s_sail') ∧
      StateRel (execInstrBr s_rv (.MULH rd rs1 rs2)) s_sail' := by sorry

theorem mulhsu_sail_equiv (s_rv : MachineState) (s_sail : SailState)
    (hrel : StateRel s_rv s_sail) (rd rs1 rs2 : Reg) :
    ∃ s_sail',
      runSail (execute_MUL (regToRegidx rs2) (regToRegidx rs1) (regToRegidx rd)
        { result_part := VectorHalf.High, signed_rs1 := Signedness.Signed,
          signed_rs2 := Signedness.Unsigned }) s_sail
        = some (RETIRE_SUCCESS, s_sail') ∧
      StateRel (execInstrBr s_rv (.MULHSU rd rs1 rs2)) s_sail' := by sorry

theorem mulhu_sail_equiv (s_rv : MachineState) (s_sail : SailState)
    (hrel : StateRel s_rv s_sail) (rd rs1 rs2 : Reg) :
    ∃ s_sail',
      runSail (execute_MUL (regToRegidx rs2) (regToRegidx rs1) (regToRegidx rd)
        { result_part := VectorHalf.High, signed_rs1 := Signedness.Unsigned,
          signed_rs2 := Signedness.Unsigned }) s_sail
        = some (RETIRE_SUCCESS, s_sail') ∧
      StateRel (execInstrBr s_rv (.MULHU rd rs1 rs2)) s_sail' := by sorry

theorem div_sail_equiv (s_rv : MachineState) (s_sail : SailState)
    (hrel : StateRel s_rv s_sail) (rd rs1 rs2 : Reg) :
    ∃ s_sail',
      runSail (execute_DIV (regToRegidx rs2) (regToRegidx rs1) (regToRegidx rd) false) s_sail
        = some (RETIRE_SUCCESS, s_sail') ∧
      StateRel (execInstrBr s_rv (.DIV rd rs1 rs2)) s_sail' := by sorry

theorem divu_sail_equiv (s_rv : MachineState) (s_sail : SailState)
    (hrel : StateRel s_rv s_sail) (rd rs1 rs2 : Reg) :
    ∃ s_sail',
      runSail (execute_DIV (regToRegidx rs2) (regToRegidx rs1) (regToRegidx rd) true) s_sail
        = some (RETIRE_SUCCESS, s_sail') ∧
      StateRel (execInstrBr s_rv (.DIVU rd rs1 rs2)) s_sail' := by
  unfold execute_DIV
  simp only [runSail_bind, runSail_rX_bits_of_stateRel s_rv s_sail hrel, runSail_pure,
    LeanRV64D.Functions.xlen, LeanRV64D.Functions.not,
    Bool.not_true, Bool.false_and, ite_true, ite_false, Bool.false_eq_true]
  conv in to_bits_truncate _ => rw [divu_full_equiv]
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

theorem rem_sail_equiv (s_rv : MachineState) (s_sail : SailState)
    (hrel : StateRel s_rv s_sail) (rd rs1 rs2 : Reg) :
    ∃ s_sail',
      runSail (execute_REM (regToRegidx rs2) (regToRegidx rs1) (regToRegidx rd) false) s_sail
        = some (RETIRE_SUCCESS, s_sail') ∧
      StateRel (execInstrBr s_rv (.REM rd rs1 rs2)) s_sail' := by sorry

theorem remu_sail_equiv (s_rv : MachineState) (s_sail : SailState)
    (hrel : StateRel s_rv s_sail) (rd rs1 rs2 : Reg) :
    ∃ s_sail',
      runSail (execute_REM (regToRegidx rs2) (regToRegidx rs1) (regToRegidx rd) true) s_sail
        = some (RETIRE_SUCCESS, s_sail') ∧
      StateRel (execInstrBr s_rv (.REMU rd rs1 rs2)) s_sail' := by
  unfold execute_REM
  simp only [runSail_bind, runSail_rX_bits_of_stateRel s_rv s_sail hrel, runSail_pure, ite_true]
  conv in to_bits_truncate _ => rw [remu_full_equiv]
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
