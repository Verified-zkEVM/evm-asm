/-
  EvmAsm.Rv64.SailEquiv.ALUProofs

  Per-instruction equivalence theorems for RTYPE and UTYPE instructions.

  ## Bidirectionality

  Each theorem has the form:
    Given StateRel sRv sSail,
    ∃ sSail', runSail (execute_*) sSail = some (RETIRE_SUCCESS, sSail')
              ∧ StateRel (execInstrBr sRv instr) sSail'

  This is **bidirectional** for total instructions:

  - **Safety (Rv64 → SAIL):** The SAIL spec can execute and produces a matching
    state. Every Rv64 behavior is a valid SAIL behavior.

  - **Liveness (SAIL → Rv64):** The `some` witness proves SAIL succeeds. Since
    `execInstrBr` is total (pure function, always returns), the Rv64 model also
    "succeeds." `StateRel` ensures they agree. The Rv64 model doesn't get stuck
    on any instruction that SAIL accepts.

  Both directions hold because `execInstrBr` is total and `runSail` is
  deterministic for these instructions (no `choose`, no external state).
-/

import EvmAsm.Rv64.Execution
import EvmAsm.Rv64.SailEquiv.MonadLemmas

open LeanRV64D.Functions
open Sail

namespace EvmAsm.Rv64.SailEquiv


-- ============================================================================
-- Bridge: reg_agree after a register insert (32x32 case split)
-- ============================================================================

set_option maxHeartbeats 4000000 in
theorem reg_agree_after_insert (sSail : SailState) (sRv : MachineState)
    (hrel : StateRel sRv sSail) (rd : Reg) (v : BitVec 64) :
    ∀ r : Reg, sailRegVal (sailStateWithReg sSail rd v) r =
      some ((sRv.setReg rd v).getReg r) := by
  intro r
  have ha := hrel.reg_agree r
  -- After case-splitting rd, both the insert key and the query key are concrete,
  -- so `Std.ExtDHashMap.get?_insert` produces `if (concrete == concrete) then …
  -- else …` and simp evaluates the condition via decide.
  cases rd <;>
    simp only [sailStateWithReg, MachineState.setReg] <;>
    (first
      | exact ha
      | (cases r <;>
          simp only [sailRegVal, Std.ExtDHashMap.get?_insert_self,
            Std.ExtDHashMap.get?_insert, MachineState.getReg,
            beq_self_eq_true, ite_true,
            show (Register.x0 == Register.x0) = true from rfl] <;>
          (first
            | rfl
            | (simp only [sailRegVal, MachineState.getReg] at ha; exact ha)
            | exact ha)))

-- ============================================================================
-- ADD, SUB, AND, OR, XOR
-- ============================================================================

-- The proof pattern: unfold execute_RTYPE, bridge rX_bits reads, case-split rd
-- for wX_bits, witness state, build StateRel (reg_agree from bridge + mem_agree trivial).

theorem add_sail_equiv (sRv : MachineState) (sSail : SailState)
    (hrel : StateRel sRv sSail) (rd rs1 rs2 : Reg) :
    ∃ sSail',
      runSail (execute_RTYPE (regToRegidx rs2) (regToRegidx rs1) (regToRegidx rd) rop.ADD) sSail
        = some (RETIRE_SUCCESS, sSail') ∧
      StateRel (execInstrBr sRv (.ADD rd rs1 rs2)) sSail' := by
  unfold execute_RTYPE
  simp only [runSail_bind, runSail_rX_bits_of_stateRel hrel, runSail_pure,
    runSail_wX_bits_of_reg]
  exact ⟨_, rfl, ⟨
    fun r => by simpa [execInstrBr, MachineState.setPC]
                 using reg_agree_after_insert sSail sRv hrel rd _ r,
    fun a => by simpa [execInstrBr, MachineState.setPC, MachineState.getMem]
                 using hrel.mem_agree a⟩⟩

theorem sub_sail_equiv (sRv : MachineState) (sSail : SailState)
    (hrel : StateRel sRv sSail) (rd rs1 rs2 : Reg) :
    ∃ sSail',
      runSail (execute_RTYPE (regToRegidx rs2) (regToRegidx rs1) (regToRegidx rd) rop.SUB) sSail
        = some (RETIRE_SUCCESS, sSail') ∧
      StateRel (execInstrBr sRv (.SUB rd rs1 rs2)) sSail' := by
  unfold execute_RTYPE
  simp only [runSail_bind, runSail_rX_bits_of_stateRel hrel, runSail_pure]
  simp only [runSail_wX_bits_of_reg]
  exact ⟨_, rfl, ⟨
    fun r => by simpa [execInstrBr, MachineState.setPC]
                 using reg_agree_after_insert sSail sRv hrel rd _ r,
    fun a => by simpa [execInstrBr, MachineState.setPC, MachineState.getMem]
                 using hrel.mem_agree a⟩⟩

theorem and_sail_equiv (sRv : MachineState) (sSail : SailState)
    (hrel : StateRel sRv sSail) (rd rs1 rs2 : Reg) :
    ∃ sSail',
      runSail (execute_RTYPE (regToRegidx rs2) (regToRegidx rs1) (regToRegidx rd) rop.AND) sSail
        = some (RETIRE_SUCCESS, sSail') ∧
      StateRel (execInstrBr sRv (.AND rd rs1 rs2)) sSail' := by
  unfold execute_RTYPE
  simp only [runSail_bind, runSail_rX_bits_of_stateRel hrel, runSail_pure]
  simp only [runSail_wX_bits_of_reg]
  exact ⟨_, rfl, ⟨
    fun r => by simpa [execInstrBr, MachineState.setPC]
                 using reg_agree_after_insert sSail sRv hrel rd _ r,
    fun a => by simpa [execInstrBr, MachineState.setPC, MachineState.getMem]
                 using hrel.mem_agree a⟩⟩

theorem or_sail_equiv (sRv : MachineState) (sSail : SailState)
    (hrel : StateRel sRv sSail) (rd rs1 rs2 : Reg) :
    ∃ sSail',
      runSail (execute_RTYPE (regToRegidx rs2) (regToRegidx rs1) (regToRegidx rd) rop.OR) sSail
        = some (RETIRE_SUCCESS, sSail') ∧
      StateRel (execInstrBr sRv (.OR rd rs1 rs2)) sSail' := by
  unfold execute_RTYPE
  simp only [runSail_bind, runSail_rX_bits_of_stateRel hrel, runSail_pure]
  simp only [runSail_wX_bits_of_reg]
  exact ⟨_, rfl, ⟨
    fun r => by simpa [execInstrBr, MachineState.setPC]
                 using reg_agree_after_insert sSail sRv hrel rd _ r,
    fun a => by simpa [execInstrBr, MachineState.setPC, MachineState.getMem]
                 using hrel.mem_agree a⟩⟩

theorem xor_sail_equiv (sRv : MachineState) (sSail : SailState)
    (hrel : StateRel sRv sSail) (rd rs1 rs2 : Reg) :
    ∃ sSail',
      runSail (execute_RTYPE (regToRegidx rs2) (regToRegidx rs1) (regToRegidx rd) rop.XOR) sSail
        = some (RETIRE_SUCCESS, sSail') ∧
      StateRel (execInstrBr sRv (.XOR rd rs1 rs2)) sSail' := by
  unfold execute_RTYPE
  simp only [runSail_bind, runSail_rX_bits_of_stateRel hrel, runSail_pure]
  simp only [runSail_wX_bits_of_reg]
  exact ⟨_, rfl, ⟨
    fun r => by simpa [execInstrBr, MachineState.setPC]
                 using reg_agree_after_insert sSail sRv hrel rd _ r,
    fun a => by simpa [execInstrBr, MachineState.setPC, MachineState.getMem]
                 using hrel.mem_agree a⟩⟩

-- ============================================================================
-- Comparison helper equivalences
-- ============================================================================

/-- SAIL's signed comparison value matches Rv64's SLT result. -/
theorem slt_value_equiv (a b : BitVec 64) :
    zero_extend (m := 64) (bool_to_bit (zopz0zI_s a b)) =
    if BitVec.slt a b then (1 : BitVec 64) else 0 := by
  unfold zopz0zI_s bool_to_bit bool_bit_forwards zero_extend Sail.BitVec.zeroExtend
  cases h : (a.toInt <b b.toInt) <;> simp [h, BitVec.slt] <;> decide

/-- SAIL's unsigned comparison value matches Rv64's SLTU result. -/
theorem sltu_value_equiv (a b : BitVec 64) :
    zero_extend (m := 64) (bool_to_bit (zopz0zI_u a b)) =
    if BitVec.ult a b then (1 : BitVec 64) else 0 := by
  unfold zopz0zI_u bool_to_bit bool_bit_forwards zero_extend Sail.BitVec.zeroExtend BitVec.toNatInt
  cases h : (↑a.toNat <b ↑b.toNat) <;> simp [h, BitVec.ult] <;> decide

-- ============================================================================
-- SLT, SLTU
-- ============================================================================

theorem slt_sail_equiv (sRv : MachineState) (sSail : SailState)
    (hrel : StateRel sRv sSail) (rd rs1 rs2 : Reg) :
    ∃ sSail',
      runSail (execute_RTYPE (regToRegidx rs2) (regToRegidx rs1) (regToRegidx rd) rop.SLT) sSail
        = some (RETIRE_SUCCESS, sSail') ∧
      StateRel (execInstrBr sRv (.SLT rd rs1 rs2)) sSail' := by
  unfold execute_RTYPE
  simp only [runSail_bind, runSail_rX_bits_of_stateRel hrel, runSail_pure,
    slt_value_equiv]
  simp only [runSail_wX_bits_of_reg]
  exact ⟨_, rfl, ⟨
    fun r => by simpa [execInstrBr, MachineState.setPC]
                 using reg_agree_after_insert sSail sRv hrel rd _ r,
    fun a => by simpa [execInstrBr, MachineState.setPC, MachineState.getMem]
                 using hrel.mem_agree a⟩⟩

theorem sltu_sail_equiv (sRv : MachineState) (sSail : SailState)
    (hrel : StateRel sRv sSail) (rd rs1 rs2 : Reg) :
    ∃ sSail',
      runSail (execute_RTYPE (regToRegidx rs2) (regToRegidx rs1) (regToRegidx rd) rop.SLTU) sSail
        = some (RETIRE_SUCCESS, sSail') ∧
      StateRel (execInstrBr sRv (.SLTU rd rs1 rs2)) sSail' := by
  unfold execute_RTYPE
  simp only [runSail_bind, runSail_rX_bits_of_stateRel hrel, runSail_pure,
    sltu_value_equiv]
  simp only [runSail_wX_bits_of_reg]
  exact ⟨_, rfl, ⟨
    fun r => by simpa [execInstrBr, MachineState.setPC]
                 using reg_agree_after_insert sSail sRv hrel rd _ r,
    fun a => by simpa [execInstrBr, MachineState.setPC, MachineState.getMem]
                 using hrel.mem_agree a⟩⟩

-- ============================================================================
-- SLL, SRL, SRA (register shifts)
--
-- SAIL uses: shift_bits_left/right v (extractLsb rs2 5 0)
-- Rv64 uses: v <<< (rs2.toNat % 64) / v >>> ... / sshiftRight v ...
-- After simp, shift_bits_left = <<<, extractLsb reduces to % 64.
-- SRA additionally needs Int.toNat_emod for shift_bits_right_arith.
-- ============================================================================

theorem sll_sail_equiv (sRv : MachineState) (sSail : SailState)
    (hrel : StateRel sRv sSail) (rd rs1 rs2 : Reg) :
    ∃ sSail',
      runSail (execute_RTYPE (regToRegidx rs2) (regToRegidx rs1) (regToRegidx rd) rop.SLL) sSail
        = some (RETIRE_SUCCESS, sSail') ∧
      StateRel (execInstrBr sRv (.SLL rd rs1 rs2)) sSail' := by
  unfold execute_RTYPE
  simp only [runSail_bind, runSail_rX_bits_of_stateRel hrel, runSail_pure,
    shift_bits_left, Sail.BitVec.extractLsb]
  simp only [runSail_wX_bits_of_reg]
  exact ⟨_, rfl, ⟨
    fun r => by simpa [execInstrBr, MachineState.setPC]
                 using reg_agree_after_insert sSail sRv hrel rd _ r,
    fun a => by simpa [execInstrBr, MachineState.setPC, MachineState.getMem]
                 using hrel.mem_agree a⟩⟩

theorem srl_sail_equiv (sRv : MachineState) (sSail : SailState)
    (hrel : StateRel sRv sSail) (rd rs1 rs2 : Reg) :
    ∃ sSail',
      runSail (execute_RTYPE (regToRegidx rs2) (regToRegidx rs1) (regToRegidx rd) rop.SRL) sSail
        = some (RETIRE_SUCCESS, sSail') ∧
      StateRel (execInstrBr sRv (.SRL rd rs1 rs2)) sSail' := by
  unfold execute_RTYPE
  simp only [runSail_bind, runSail_rX_bits_of_stateRel hrel, runSail_pure,
    shift_bits_right, Sail.BitVec.extractLsb]
  simp only [runSail_wX_bits_of_reg]
  exact ⟨_, rfl, ⟨
    fun r => by simpa [execInstrBr, MachineState.setPC]
                 using reg_agree_after_insert sSail sRv hrel rd _ r,
    fun a => by simpa [execInstrBr, MachineState.setPC, MachineState.getMem]
                 using hrel.mem_agree a⟩⟩

theorem sra_sail_equiv (sRv : MachineState) (sSail : SailState)
    (hrel : StateRel sRv sSail) (rd rs1 rs2 : Reg) :
    ∃ sSail',
      runSail (execute_RTYPE (regToRegidx rs2) (regToRegidx rs1) (regToRegidx rd) rop.SRA) sSail
        = some (RETIRE_SUCCESS, sSail') ∧
      StateRel (execInstrBr sRv (.SRA rd rs1 rs2)) sSail' := by
  unfold execute_RTYPE
  simp only [runSail_bind, runSail_rX_bits_of_stateRel hrel, runSail_pure,
    shift_bits_right_arith, Sail.BitVec.extractLsb, BitVec.toNatInt]
  simp only [runSail_wX_bits_of_reg]
  exact ⟨_, rfl, ⟨
    fun r => by simpa [execInstrBr, MachineState.setPC]
                 using reg_agree_after_insert sSail sRv hrel rd _ r,
    fun a => by simpa [execInstrBr, MachineState.setPC, MachineState.getMem]
                 using hrel.mem_agree a⟩⟩

-- ============================================================================
-- LUI helper + proof
-- ============================================================================

/-- SAIL's sign_extend(imm ++ 0x000) equals Rv64's (imm.zeroExtend 32 <<< 12).signExtend 64. -/
private theorem lui_inner (imm : BitVec 20) :
    (imm ++ (0 : BitVec 12) : BitVec 32) = (imm.zeroExtend 32 <<< 12 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_append]
  simp [BitVec.toNat_shiftLeft, BitVec.toNat_setWidth]; omega

theorem lui_equiv (imm : BitVec 20) :
    sign_extend (m := 64) (imm ++ (0 : BitVec 12)) =
    (imm.zeroExtend 32 <<< 12).signExtend 64 := by
  simp only [sign_extend, Sail.BitVec.signExtend]; rw [lui_inner]

theorem lui_sail_equiv (sRv : MachineState) (sSail : SailState)
    (hrel : StateRel sRv sSail) (rd : Reg) (imm : BitVec 20) :
    ∃ sSail',
      runSail (execute_UTYPE imm (regToRegidx rd) uop.LUI) sSail
        = some (RETIRE_SUCCESS, sSail') ∧
      StateRel (execInstrBr sRv (.LUI rd imm)) sSail' := by
  unfold execute_UTYPE
  simp only [runSail_bind, runSail_pure]
  simp only [runSail_wX_bits_of_reg]
  exact ⟨_, rfl, ⟨
    fun r => by simpa [execInstrBr, MachineState.setPC, ← lui_equiv]
                 using reg_agree_after_insert sSail sRv hrel rd _ r,
    fun a => by simpa [execInstrBr, MachineState.setPC, MachineState.getMem]
                 using hrel.mem_agree a⟩⟩

-- ============================================================================
-- ADDIW helper + proof
-- ============================================================================

/-- SAIL's sign_extend(extractLsb (rs1 + sign_extend imm) 31 0) equals
    Rv64's ((rs1.truncate 32 + (signExtend12 imm).truncate 32) : BitVec 32).signExtend 64. -/
theorem addiw_equiv (rs1 : BitVec 64) (imm : BitVec 12) :
    (Sail.BitVec.signExtend (Sail.BitVec.extractLsb (rs1 + sign_extend (m := 64) imm) 31 0) 64 : BitVec 64) =
    ((rs1.truncate 32 + (imm.signExtend 64).truncate 32 : BitVec 32).signExtend 64 : BitVec 64) := by
  simp only [sign_extend, Sail.BitVec.signExtend, Sail.BitVec.extractLsb]
  congr 1; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_setWidth]

theorem addiw_sail_equiv (sRv : MachineState) (sSail : SailState)
    (hrel : StateRel sRv sSail) (rd rs1 : Reg) (imm : BitVec 12) :
    ∃ sSail',
      runSail (execute_ADDIW imm (regToRegidx rs1) (regToRegidx rd)) sSail
        = some (RETIRE_SUCCESS, sSail') ∧
      StateRel (execInstrBr sRv (.ADDIW rd rs1 imm)) sSail' := by
  unfold execute_ADDIW
  simp only [runSail_bind, runSail_rX_bits_of_stateRel hrel, runSail_pure]
  simp only [runSail_wX_bits_of_reg]
  exact ⟨_, rfl, ⟨
    fun r => by simpa [execInstrBr, MachineState.setPC, signExtend12, ← addiw_equiv]
                 using reg_agree_after_insert sSail sRv hrel rd _ r,
    fun a => by simpa [execInstrBr, MachineState.setPC, MachineState.getMem]
                 using hrel.mem_agree a⟩⟩

-- ============================================================================
-- AUIPC
--
-- Like LUI but adds the PC value. Needs PC agreement as a separate hypothesis
-- (not part of StateRel, since SAIL execute_* doesn't update PC — that's done
-- by the outer stepping loop, while Rv64's execInstrBr bakes in PC += 4).
-- ============================================================================

theorem auipc_sail_equiv (sRv : MachineState) (sSail : SailState)
    (hrel : StateRel sRv sSail)
    (h_pc : sSail.regs.get? Register.PC = some sRv.pc)
    (rd : Reg) (imm : BitVec 20) :
    ∃ sSail',
      runSail (execute_UTYPE imm (regToRegidx rd) uop.AUIPC) sSail
        = some (RETIRE_SUCCESS, sSail') ∧
      StateRel (execInstrBr sRv (.AUIPC rd imm)) sSail' := by
  unfold execute_UTYPE
  simp only [runSail_bind, runSail_pure, runSail_get_arch_pc h_pc]
  simp only [runSail_wX_bits_of_reg]
  exact ⟨_, rfl, ⟨
    fun r => by simpa [execInstrBr, MachineState.setPC, ← lui_equiv]
                 using reg_agree_after_insert sSail sRv hrel rd _ r,
    fun a => by simpa [execInstrBr, MachineState.setPC, MachineState.getMem]
                 using hrel.mem_agree a⟩⟩

-- ============================================================================
-- MUL (M-extension, low 64 bits)
-- ============================================================================

/-- SAIL's mult_to_bits_half Signed Signed a b Low equals Rv64's a * b.
    Signed multiplication agrees with unsigned on the lower 64 bits. -/
theorem mul_low_equiv (a b : BitVec 64) :
    mult_to_bits_half (l := 64) Signedness.Signed Signedness.Signed a b VectorHalf.Low = a * b := by
  rw [mult_to_bits_half.eq_5]
  simp only [to_bits_truncate, get_slice_int, Sail.BitVec.extractLsb]
  apply BitVec.eq_of_toNat_eq
  simp
  have h_reduce : ∀ x : Int,
      (x % (680564733841876926926749214863536422912 : Int)).toNat % (18446744073709551616 : Nat) =
      (x % (18446744073709551616 : Int)).toNat := by omega
  rw [h_reduce]
  have h1 : a.toInt % (2^64 : Int) = ↑a.toNat := by simp [BitVec.toInt]; split <;> omega
  have h2 : b.toInt % (2^64 : Int) = ↑b.toNat := by simp [BitVec.toInt]; split <;> omega
  rw [show (18446744073709551616 : Int) = 2 ^ 64 from by decide]
  rw [Int.mul_emod, h1, h2]
  exact_mod_cast rfl

theorem mul_sail_equiv (sRv : MachineState) (sSail : SailState)
    (hrel : StateRel sRv sSail) (rd rs1 rs2 : Reg) :
    ∃ sSail',
      runSail (execute_MUL (regToRegidx rs2) (regToRegidx rs1) (regToRegidx rd)
        { result_part := VectorHalf.Low, signed_rs1 := Signedness.Signed,
          signed_rs2 := Signedness.Signed }) sSail
        = some (RETIRE_SUCCESS, sSail') ∧
      StateRel (execInstrBr sRv (.MUL rd rs1 rs2)) sSail' := by
  unfold execute_MUL
  simp only [runSail_bind, runSail_rX_bits_of_stateRel hrel, runSail_pure,
    mul_low_equiv, LeanRV64D.Functions.xlen]
  simp only [runSail_wX_bits_of_reg]
  exact ⟨_, rfl, ⟨
    fun r => by simpa [execInstrBr, MachineState.setPC]
                 using reg_agree_after_insert sSail sRv hrel rd _ r,
    fun a => by simpa [execInstrBr, MachineState.setPC, MachineState.getMem]
                 using hrel.mem_agree a⟩⟩

end EvmAsm.Rv64.SailEquiv
