/-
  EvmAsm.Rv64.SailEquiv.BranchProofs

  Per-instruction equivalence theorems for branch and jump instructions:
  BEQ, BNE, BLT, BGE, BLTU, BGEU, JAL, JALR.

  Branches don't write general registers — they only update nextPC. Since
  StateRel doesn't track PC or nextPC, branches trivially preserve StateRel
  for registers and memory.

  JAL/JALR additionally write a link register (rd := next_pc).
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
-- Helper lemmas for branch proofs
-- ============================================================================

private theorem sign_extend_13_eq (imm : BitVec 13) :
    sign_extend (m := 64) imm = signExtend13 imm := by
  unfold sign_extend signExtend13 Sail.BitVec.signExtend; rfl

/-- Writing Register.nextPC preserves StateRel (nextPC is not in the tracked register set). -/
theorem stateRel_nextPC (sRv : MachineState) (sSail : SailState)
    (hrel : StateRel sRv sSail) (v : BitVec 64) :
    StateRel sRv { sSail with regs := sSail.regs.insert Register.nextPC v } :=
  ⟨fun r => by
    have ha := hrel.reg_agree r
    cases r <;> simp only [sailRegVal, Std.ExtDHashMap.get?_insert,
      show (Register.nextPC == Register.x1) = false from by decide,
      show (Register.nextPC == Register.x2) = false from by decide,
      show (Register.nextPC == Register.x5) = false from by decide,
      show (Register.nextPC == Register.x6) = false from by decide,
      show (Register.nextPC == Register.x7) = false from by decide,
      show (Register.nextPC == Register.x10) = false from by decide,
      show (Register.nextPC == Register.x11) = false from by decide,
      show (Register.nextPC == Register.x12) = false from by decide,
      ite_false] at ha ⊢ <;> exact ha,
   fun a => hrel.mem_agree a⟩

-- Comparison operator equivalences (definitional: SAIL and Lean use the same operations)
private theorem slt_equiv (a b : BitVec 64) : zopz0zI_s a b = BitVec.slt a b := by
  unfold zopz0zI_s BitVec.slt; rfl
private theorem sge_equiv (a b : BitVec 64) : zopz0zKzJ_s a b = !zopz0zI_s a b := by
  unfold zopz0zKzJ_s zopz0zI_s
  by_cases h : a.toInt < b.toInt <;>
    simp [h, show ¬(a.toInt < b.toInt) → a.toInt ≥ b.toInt from by omega]
private theorem ult_equiv (a b : BitVec 64) : zopz0zI_u a b = BitVec.ult a b := by
  unfold zopz0zI_u BitVec.ult BitVec.toNatInt
  simp [BEq.beq, decide_eq_decide, Int.ofNat_lt]
private theorem uge_equiv (a b : BitVec 64) : zopz0zKzJ_u a b = !zopz0zI_u a b := by
  unfold zopz0zKzJ_u zopz0zI_u BitVec.toNatInt
  by_cases h : (↑a.toNat : Int) < (↑b.toNat : Int) <;> (simp [h]; omega)

-- ============================================================================
-- Common branch proof tactic
-- ============================================================================

-- The proof pattern for all 6 conditional branches is identical:
-- 1. Unfold execute_BTYPE, apply monad lemmas
-- 2. Case-split on branch condition
-- 3. Taken: apply jump_to, StateRel preserved via stateRel_nextPC
-- 4. Not taken: pure RETIRE_SUCCESS, StateRel trivially preserved

-- ============================================================================
-- Conditional branches (BEQ, BNE, BLT, BGE, BLTU, BGEU)
-- ============================================================================

theorem beq_sail_equiv (sRv : MachineState) (sSail : SailState)
    (hrel : StateRel sRv sSail)
    (h_pc : sSail.regs.get? Register.PC = some sRv.pc)
    (h_misa : ∃ v, sSail.regs.get? Register.misa = some v)
    (rs1 rs2 : Reg) (offset : BitVec 13)
    (h_align : (sRv.pc + signExtend13 offset) &&& 3 = 0) :
    ∃ sSail',
      runSail (execute_BTYPE offset (regToRegidx rs2) (regToRegidx rs1) bop.BEQ) sSail
        = some (RETIRE_SUCCESS, sSail') ∧
      StateRel (execInstrBr sRv (.BEQ rs1 rs2 offset)) sSail' := by
  obtain ⟨misa_val, h_misa⟩ := h_misa
  unfold execute_BTYPE
  simp only [runSail_bind, runSail_rX_bits_of_stateRel hrel, runSail_pure]
  by_cases h : sRv.getReg rs1 == sRv.getReg rs2
  · simp only [h, ite_true, runSail_bind,
      runSail_readReg_PC sSail sRv.pc h_pc, runSail_pure, sign_extend_13_eq]
    rw [runSail_jump_to _ _ misa_val h_align h_misa]
    exact ⟨_, rfl, stateRel_nextPC _ _
      ⟨fun r => by simp [execInstrBr, h]; exact hrel.reg_agree r,
       fun a => by simp [execInstrBr, h]; exact hrel.mem_agree a⟩ _⟩
  · simp only [h, ite_false]
    exact ⟨_, rfl,
      ⟨fun r => by simp [execInstrBr, h]; exact hrel.reg_agree r,
       fun a => by simp [execInstrBr, h]; exact hrel.mem_agree a⟩⟩

theorem bne_sail_equiv (sRv : MachineState) (sSail : SailState)
    (hrel : StateRel sRv sSail)
    (h_pc : sSail.regs.get? Register.PC = some sRv.pc)
    (h_misa : ∃ v, sSail.regs.get? Register.misa = some v)
    (rs1 rs2 : Reg) (offset : BitVec 13)
    (h_align : (sRv.pc + signExtend13 offset) &&& 3 = 0) :
    ∃ sSail',
      runSail (execute_BTYPE offset (regToRegidx rs2) (regToRegidx rs1) bop.BNE) sSail
        = some (RETIRE_SUCCESS, sSail') ∧
      StateRel (execInstrBr sRv (.BNE rs1 rs2 offset)) sSail' := by
  obtain ⟨misa_val, h_misa⟩ := h_misa
  unfold execute_BTYPE
  simp only [runSail_bind, runSail_rX_bits_of_stateRel hrel, runSail_pure]
  by_cases h : sRv.getReg rs1 != sRv.getReg rs2
  · simp only [h, ite_true, runSail_bind,
      runSail_readReg_PC sSail sRv.pc h_pc, runSail_pure, sign_extend_13_eq]
    rw [runSail_jump_to _ _ misa_val h_align h_misa]
    exact ⟨_, rfl, stateRel_nextPC _ _
      ⟨fun r => by simp [execInstrBr, h]; exact hrel.reg_agree r,
       fun a => by simp [execInstrBr, h]; exact hrel.mem_agree a⟩ _⟩
  · simp only [h, ite_false]
    exact ⟨_, rfl,
      ⟨fun r => by simp [execInstrBr, h]; exact hrel.reg_agree r,
       fun a => by simp [execInstrBr, h]; exact hrel.mem_agree a⟩⟩

theorem blt_sail_equiv (sRv : MachineState) (sSail : SailState)
    (hrel : StateRel sRv sSail)
    (h_pc : sSail.regs.get? Register.PC = some sRv.pc)
    (h_misa : ∃ v, sSail.regs.get? Register.misa = some v)
    (rs1 rs2 : Reg) (offset : BitVec 13)
    (h_align : (sRv.pc + signExtend13 offset) &&& 3 = 0) :
    ∃ sSail',
      runSail (execute_BTYPE offset (regToRegidx rs2) (regToRegidx rs1) bop.BLT) sSail
        = some (RETIRE_SUCCESS, sSail') ∧
      StateRel (execInstrBr sRv (.BLT rs1 rs2 offset)) sSail' := by
  obtain ⟨misa_val, h_misa⟩ := h_misa
  unfold execute_BTYPE
  simp only [runSail_bind, runSail_rX_bits_of_stateRel hrel, runSail_pure, slt_equiv]
  by_cases h : BitVec.slt (sRv.getReg rs1) (sRv.getReg rs2)
  · simp only [h, ite_true, runSail_bind,
      runSail_readReg_PC sSail sRv.pc h_pc, runSail_pure, sign_extend_13_eq]
    rw [runSail_jump_to _ _ misa_val h_align h_misa]
    exact ⟨_, rfl, stateRel_nextPC _ _
      ⟨fun r => by simp [execInstrBr, h]; exact hrel.reg_agree r,
       fun a => by simp [execInstrBr, h]; exact hrel.mem_agree a⟩ _⟩
  · simp only [h, ite_false]
    exact ⟨_, rfl,
      ⟨fun r => by simp [execInstrBr, h]; exact hrel.reg_agree r,
       fun a => by simp [execInstrBr, h]; exact hrel.mem_agree a⟩⟩

theorem bge_sail_equiv (sRv : MachineState) (sSail : SailState)
    (hrel : StateRel sRv sSail)
    (h_pc : sSail.regs.get? Register.PC = some sRv.pc)
    (h_misa : ∃ v, sSail.regs.get? Register.misa = some v)
    (rs1 rs2 : Reg) (offset : BitVec 13)
    (h_align : (sRv.pc + signExtend13 offset) &&& 3 = 0) :
    ∃ sSail',
      runSail (execute_BTYPE offset (regToRegidx rs2) (regToRegidx rs1) bop.BGE) sSail
        = some (RETIRE_SUCCESS, sSail') ∧
      StateRel (execInstrBr sRv (.BGE rs1 rs2 offset)) sSail' := by
  obtain ⟨misa_val, h_misa⟩ := h_misa
  unfold execute_BTYPE
  simp only [runSail_bind, runSail_rX_bits_of_stateRel hrel, runSail_pure,
    sge_equiv, slt_equiv]
  by_cases h : BitVec.slt (sRv.getReg rs1) (sRv.getReg rs2)
  · -- slt = true, so !slt = false → not taken
    simp only [h, Bool.not_true, ite_false]
    exact ⟨_, rfl,
      ⟨fun r => by simp [execInstrBr, show ¬¬BitVec.slt _ _ from fun h' => absurd h h']; exact hrel.reg_agree r,
       fun a => by simp [execInstrBr, show ¬¬BitVec.slt _ _ from fun h' => absurd h h']; exact hrel.mem_agree a⟩⟩
  · -- slt = false, so !slt = true → taken
    simp only [show BitVec.slt (sRv.getReg rs1) (sRv.getReg rs2) = false from by simp [h],
      Bool.not_false, ite_true, runSail_bind,
      runSail_readReg_PC sSail sRv.pc h_pc, runSail_pure, sign_extend_13_eq]
    rw [runSail_jump_to _ _ misa_val h_align h_misa]
    exact ⟨_, rfl, stateRel_nextPC _ _
      ⟨fun r => by simp [execInstrBr, h]; exact hrel.reg_agree r,
       fun a => by simp [execInstrBr, h]; exact hrel.mem_agree a⟩ _⟩

theorem bltu_sail_equiv (sRv : MachineState) (sSail : SailState)
    (hrel : StateRel sRv sSail)
    (h_pc : sSail.regs.get? Register.PC = some sRv.pc)
    (h_misa : ∃ v, sSail.regs.get? Register.misa = some v)
    (rs1 rs2 : Reg) (offset : BitVec 13)
    (h_align : (sRv.pc + signExtend13 offset) &&& 3 = 0) :
    ∃ sSail',
      runSail (execute_BTYPE offset (regToRegidx rs2) (regToRegidx rs1) bop.BLTU) sSail
        = some (RETIRE_SUCCESS, sSail') ∧
      StateRel (execInstrBr sRv (.BLTU rs1 rs2 offset)) sSail' := by
  obtain ⟨misa_val, h_misa⟩ := h_misa
  unfold execute_BTYPE
  simp only [runSail_bind, runSail_rX_bits_of_stateRel hrel, runSail_pure, ult_equiv]
  by_cases h : BitVec.ult (sRv.getReg rs1) (sRv.getReg rs2)
  · simp only [h, ite_true, runSail_bind,
      runSail_readReg_PC sSail sRv.pc h_pc, runSail_pure, sign_extend_13_eq]
    rw [runSail_jump_to _ _ misa_val h_align h_misa]
    exact ⟨_, rfl, stateRel_nextPC _ _
      ⟨fun r => by simp [execInstrBr, h]; exact hrel.reg_agree r,
       fun a => by simp [execInstrBr, h]; exact hrel.mem_agree a⟩ _⟩
  · simp only [h, ite_false]
    exact ⟨_, rfl,
      ⟨fun r => by simp [execInstrBr, h]; exact hrel.reg_agree r,
       fun a => by simp [execInstrBr, h]; exact hrel.mem_agree a⟩⟩

theorem bgeu_sail_equiv (sRv : MachineState) (sSail : SailState)
    (hrel : StateRel sRv sSail)
    (h_pc : sSail.regs.get? Register.PC = some sRv.pc)
    (h_misa : ∃ v, sSail.regs.get? Register.misa = some v)
    (rs1 rs2 : Reg) (offset : BitVec 13)
    (h_align : (sRv.pc + signExtend13 offset) &&& 3 = 0) :
    ∃ sSail',
      runSail (execute_BTYPE offset (regToRegidx rs2) (regToRegidx rs1) bop.BGEU) sSail
        = some (RETIRE_SUCCESS, sSail') ∧
      StateRel (execInstrBr sRv (.BGEU rs1 rs2 offset)) sSail' := by
  obtain ⟨misa_val, h_misa⟩ := h_misa
  unfold execute_BTYPE
  simp only [runSail_bind, runSail_rX_bits_of_stateRel hrel, runSail_pure,
    uge_equiv, ult_equiv]
  by_cases h : BitVec.ult (sRv.getReg rs1) (sRv.getReg rs2)
  · -- ult = true, so !ult = false → not taken
    simp only [h, Bool.not_true, ite_false]
    exact ⟨_, rfl,
      ⟨fun r => by simp [execInstrBr, show ¬¬BitVec.ult _ _ from fun h' => absurd h h']; exact hrel.reg_agree r,
       fun a => by simp [execInstrBr, show ¬¬BitVec.ult _ _ from fun h' => absurd h h']; exact hrel.mem_agree a⟩⟩
  · -- ult = false, so !ult = true → taken
    simp only [show BitVec.ult (sRv.getReg rs1) (sRv.getReg rs2) = false from by simp [h],
      Bool.not_false, ite_true, runSail_bind,
      runSail_readReg_PC sSail sRv.pc h_pc, runSail_pure, sign_extend_13_eq]
    rw [runSail_jump_to _ _ misa_val h_align h_misa]
    exact ⟨_, rfl, stateRel_nextPC _ _
      ⟨fun r => by simp [execInstrBr, h]; exact hrel.reg_agree r,
       fun a => by simp [execInstrBr, h]; exact hrel.mem_agree a⟩ _⟩

-- ============================================================================
-- Unconditional jumps (JAL, JALR)
-- ============================================================================

private theorem sign_extend_21_eq (imm : BitVec 21) :
    sign_extend (m := 64) imm = signExtend21 imm := by
  unfold sign_extend signExtend21 Sail.BitVec.signExtend; rfl

theorem jal_sail_equiv (sRv : MachineState) (sSail : SailState)
    (hrel : StateRel sRv sSail)
    (h_pc : sSail.regs.get? Register.PC = some sRv.pc)
    (h_nextpc : sSail.regs.get? Register.nextPC = some (sRv.pc + 4))
    (h_misa : ∃ v, sSail.regs.get? Register.misa = some v)
    (rd : Reg) (offset : BitVec 21)
    (h_align : (sRv.pc + signExtend21 offset) &&& 3 = 0) :
    ∃ sSail',
      runSail (execute_JAL offset (regToRegidx rd)) sSail
        = some (RETIRE_SUCCESS, sSail') ∧
      StateRel (execInstrBr sRv (.JAL rd offset)) sSail' := by
  obtain ⟨misa_val, h_misa⟩ := h_misa
  unfold execute_JAL
  simp only [runSail_bind,
    runSail_get_next_pc sSail (sRv.pc + 4) h_nextpc,
    runSail_readReg_PC sSail sRv.pc h_pc,
    sign_extend_21_eq]
  rw [runSail_jump_to _ _ misa_val h_align h_misa]
  simp only [RETIRE_SUCCESS, runSail_bind, runSail_pure]
  cases rd <;>
    simp only [regToRegidx,
      runSail_wX_bits_x0, runSail_wX_bits_x1, runSail_wX_bits_x2,
      runSail_wX_bits_x5, runSail_wX_bits_x6, runSail_wX_bits_x7,
      runSail_wX_bits_x10, runSail_wX_bits_x11, runSail_wX_bits_x12]
  all_goals first
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert _ _ (stateRel_nextPC _ _ hrel _) .x0 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert _ _ (stateRel_nextPC _ _ hrel _) .x1 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert _ _ (stateRel_nextPC _ _ hrel _) .x2 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert _ _ (stateRel_nextPC _ _ hrel _) .x5 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert _ _ (stateRel_nextPC _ _ hrel _) .x6 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert _ _ (stateRel_nextPC _ _ hrel _) .x7 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert _ _ (stateRel_nextPC _ _ hrel _) .x10 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert _ _ (stateRel_nextPC _ _ hrel _) .x11 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert _ _ (stateRel_nextPC _ _ hrel _) .x12 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩

private theorem sign_extend_12_eq (imm : BitVec 12) :
    sign_extend (m := 64) imm = signExtend12 imm := by
  unfold sign_extend signExtend12 Sail.BitVec.signExtend; rfl

/-- SAIL's BitVec.update (set bit 0 to 0) equals ANDing with ~~~1. -/
private theorem jalr_mask_equiv (v : BitVec 64) :
    Sail.BitVec.update v 0 (0 : BitVec 1) = v &&& ~~~1#64 := by
  simp only [Sail.BitVec.update, BitVec.updateSubrange']
  ext i; simp [Bool.and_comm]

/-- Helper: if a monadic computation succeeds with .ok, runSail reduces through bind. -/
private theorem runSail_ok_bind (f : Unit → SailM β) (s s' : SailState)
    (m : SailM Unit) (hm : m s = .ok () s') :
    runSail (m >>= f) s = runSail (f ()) s' := by
  simp [runSail, bind, EStateM.bind, hm]

theorem jalr_sail_equiv (sRv : MachineState) (sSail : SailState)
    (hrel : StateRel sRv sSail)
    (h_pc : sSail.regs.get? Register.PC = some sRv.pc)
    (h_nextpc : sSail.regs.get? Register.nextPC = some (sRv.pc + 4))
    (h_misa : ∃ v, sSail.regs.get? Register.misa = some v)
    (rd rs1 : Reg) (offset : BitVec 12)
    -- update_elp_state succeeds and preserves StateRel + relevant state
    (h_elp : ∃ s_mid, update_elp_state (regToRegidx rs1) sSail = .ok () s_mid ∧
      StateRel sRv s_mid ∧
      s_mid.regs.get? Register.PC = some sRv.pc ∧
      s_mid.regs.get? Register.nextPC = some (sRv.pc + 4) ∧
      (∃ v, s_mid.regs.get? Register.misa = some v))
    (h_align : ((sRv.getReg rs1 + signExtend12 offset) &&& ~~~1#64) &&& 3 = 0) :
    ∃ sSail',
      runSail (execute_JALR offset (regToRegidx rs1) (regToRegidx rd)) sSail
        = some (RETIRE_SUCCESS, sSail') ∧
      StateRel (execInstrBr sRv (.JALR rd rs1 offset)) sSail' := by
  obtain ⟨s_mid, h_elp_ok, hrel_mid, h_pc_mid, h_nextpc_mid, h_misa_mid⟩ := h_elp
  obtain ⟨misa_val, h_misa_mid⟩ := h_misa_mid
  unfold execute_JALR
  rw [runSail_ok_bind _ sSail s_mid _ h_elp_ok]
  simp only [runSail_bind, runSail_pure,
    runSail_get_next_pc s_mid (sRv.pc + 4) h_nextpc_mid,
    runSail_rX_bits_of_stateRel hrel_mid,
    sign_extend_12_eq]
  -- Rewrite BitVec.update to &&& ~~~1 before applying jump_to
  simp only [show @Sail.BitVec.update (m := 64) (sRv.getReg rs1 + signExtend12 offset) 0 0#1 =
    (sRv.getReg rs1 + signExtend12 offset) &&& ~~~1#64 from jalr_mask_equiv _]
  rw [runSail_jump_to _ _ misa_val h_align h_misa_mid]
  simp only [RETIRE_SUCCESS, runSail_bind, runSail_pure]
  cases rd <;>
    simp only [regToRegidx,
      runSail_wX_bits_x0, runSail_wX_bits_x1, runSail_wX_bits_x2,
      runSail_wX_bits_x5, runSail_wX_bits_x6, runSail_wX_bits_x7,
      runSail_wX_bits_x10, runSail_wX_bits_x11, runSail_wX_bits_x12]
  all_goals first
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert _ _ (stateRel_nextPC _ _ hrel_mid _) .x0 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel_mid.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert _ _ (stateRel_nextPC _ _ hrel_mid _) .x1 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel_mid.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert _ _ (stateRel_nextPC _ _ hrel_mid _) .x2 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel_mid.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert _ _ (stateRel_nextPC _ _ hrel_mid _) .x5 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel_mid.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert _ _ (stateRel_nextPC _ _ hrel_mid _) .x6 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel_mid.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert _ _ (stateRel_nextPC _ _ hrel_mid _) .x7 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel_mid.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert _ _ (stateRel_nextPC _ _ hrel_mid _) .x10 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel_mid.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert _ _ (stateRel_nextPC _ _ hrel_mid _) .x11 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel_mid.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert _ _ (stateRel_nextPC _ _ hrel_mid _) .x12 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel_mid.mem_agree a⟩⟩

end EvmAsm.Rv64.SailEquiv
