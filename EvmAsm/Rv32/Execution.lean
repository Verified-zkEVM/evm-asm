/-
  EvmAsm.Rv32.Execution

  Branch-aware instruction execution, code memory, and step-based execution.

  This module provides an alternative execution model that handles branch and
  jump instructions with proper PC semantics (as opposed to the straight-line
  execInstr which always advances PC by 4).

  Key components:
  - execInstrBr: per-instruction PC control (branches change PC by offset)
  - CodeMem: maps addresses to instructions
  - loadProgram: loads a program into code memory at a base address
  - step / stepN: single-step and multi-step execution over code memory
-/

import EvmAsm.Rv32.Basic
import EvmAsm.Rv32.Instructions
import EvmAsm.Rv32.Program

namespace EvmAsm

-- ============================================================================
-- Branch-aware instruction execution
-- ============================================================================

/-- Execute a single instruction with full PC control.
    Non-branch instructions: PC += 4.
    Branch instructions: PC += offset (taken) or PC += 4 (not taken).
    JAL: rd := PC + 4, PC += offset.
    JALR: rd := PC + 4, PC := (rs1 + sext(offset)) & ~1. -/
def execInstrBr (s : MachineState) (i : Instr) : MachineState :=
  match i with
  -- RV32I ALU register-register
  | .ADD rd rs1 rs2 =>
      (s.setReg rd (s.getReg rs1 + s.getReg rs2)).setPC (s.pc + 4)
  | .SUB rd rs1 rs2 =>
      (s.setReg rd (s.getReg rs1 - s.getReg rs2)).setPC (s.pc + 4)
  | .SLL rd rs1 rs2 =>
      let shamt := (s.getReg rs2).toNat % 32
      (s.setReg rd (s.getReg rs1 <<< shamt)).setPC (s.pc + 4)
  | .SRL rd rs1 rs2 =>
      let shamt := (s.getReg rs2).toNat % 32
      (s.setReg rd (s.getReg rs1 >>> shamt)).setPC (s.pc + 4)
  | .SRA rd rs1 rs2 =>
      let shamt := (s.getReg rs2).toNat % 32
      (s.setReg rd (BitVec.sshiftRight (s.getReg rs1) shamt)).setPC (s.pc + 4)
  | .AND rd rs1 rs2 =>
      (s.setReg rd (s.getReg rs1 &&& s.getReg rs2)).setPC (s.pc + 4)
  | .OR rd rs1 rs2 =>
      (s.setReg rd (s.getReg rs1 ||| s.getReg rs2)).setPC (s.pc + 4)
  | .XOR rd rs1 rs2 =>
      (s.setReg rd (s.getReg rs1 ^^^ s.getReg rs2)).setPC (s.pc + 4)
  | .SLT rd rs1 rs2 =>
      (s.setReg rd (if BitVec.slt (s.getReg rs1) (s.getReg rs2) then 1 else 0)).setPC (s.pc + 4)
  | .SLTU rd rs1 rs2 =>
      (s.setReg rd (if BitVec.ult (s.getReg rs1) (s.getReg rs2) then 1 else 0)).setPC (s.pc + 4)
  -- RV32I ALU immediate
  | .ADDI rd rs1 imm =>
      (s.setReg rd (s.getReg rs1 + signExtend12 imm)).setPC (s.pc + 4)
  | .ANDI rd rs1 imm =>
      (s.setReg rd (s.getReg rs1 &&& signExtend12 imm)).setPC (s.pc + 4)
  | .ORI rd rs1 imm =>
      (s.setReg rd (s.getReg rs1 ||| signExtend12 imm)).setPC (s.pc + 4)
  | .XORI rd rs1 imm =>
      (s.setReg rd (s.getReg rs1 ^^^ signExtend12 imm)).setPC (s.pc + 4)
  | .SLTI rd rs1 imm =>
      (s.setReg rd (if BitVec.slt (s.getReg rs1) (signExtend12 imm) then 1 else 0)).setPC (s.pc + 4)
  | .SLTIU rd rs1 imm =>
      (s.setReg rd (if BitVec.ult (s.getReg rs1) (signExtend12 imm) then 1 else 0)).setPC (s.pc + 4)
  | .SLLI rd rs1 shamt =>
      (s.setReg rd (s.getReg rs1 <<< shamt.toNat)).setPC (s.pc + 4)
  | .SRLI rd rs1 shamt =>
      (s.setReg rd (s.getReg rs1 >>> shamt.toNat)).setPC (s.pc + 4)
  | .SRAI rd rs1 shamt =>
      (s.setReg rd (BitVec.sshiftRight (s.getReg rs1) shamt.toNat)).setPC (s.pc + 4)
  -- RV32I upper immediate
  | .LUI rd imm =>
      let val : Word := imm.zeroExtend 32 <<< 12
      (s.setReg rd val).setPC (s.pc + 4)
  | .AUIPC rd imm =>
      let val : Word := s.pc + (imm.zeroExtend 32 <<< 12)
      (s.setReg rd val).setPC (s.pc + 4)
  -- RV32I word memory
  | .LW rd rs1 offset =>
      let addr := s.getReg rs1 + signExtend12 offset
      (s.setReg rd (s.getMem addr)).setPC (s.pc + 4)
  | .SW rs1 rs2 offset =>
      let addr := s.getReg rs1 + signExtend12 offset
      (s.setMem addr (s.getReg rs2)).setPC (s.pc + 4)
  -- RV32I sub-word memory
  | .LB rd rs1 offset =>
      let addr := s.getReg rs1 + signExtend12 offset
      (s.setReg rd ((s.getByte addr).signExtend 32)).setPC (s.pc + 4)
  | .LH rd rs1 offset =>
      let addr := s.getReg rs1 + signExtend12 offset
      (s.setReg rd ((s.getHalfword addr).signExtend 32)).setPC (s.pc + 4)
  | .LBU rd rs1 offset =>
      let addr := s.getReg rs1 + signExtend12 offset
      (s.setReg rd ((s.getByte addr).zeroExtend 32)).setPC (s.pc + 4)
  | .LHU rd rs1 offset =>
      let addr := s.getReg rs1 + signExtend12 offset
      (s.setReg rd ((s.getHalfword addr).zeroExtend 32)).setPC (s.pc + 4)
  | .SB rs1 rs2 offset =>
      let addr := s.getReg rs1 + signExtend12 offset
      (s.setByte addr ((s.getReg rs2).truncate 8)).setPC (s.pc + 4)
  | .SH rs1 rs2 offset =>
      let addr := s.getReg rs1 + signExtend12 offset
      (s.setHalfword addr ((s.getReg rs2).truncate 16)).setPC (s.pc + 4)
  -- RV32I branches
  | .BEQ rs1 rs2 offset =>
      if s.getReg rs1 == s.getReg rs2 then
        s.setPC (s.pc + signExtend13 offset)
      else
        s.setPC (s.pc + 4)
  | .BNE rs1 rs2 offset =>
      if s.getReg rs1 != s.getReg rs2 then
        s.setPC (s.pc + signExtend13 offset)
      else
        s.setPC (s.pc + 4)
  | .BLT rs1 rs2 offset =>
      if BitVec.slt (s.getReg rs1) (s.getReg rs2) then
        s.setPC (s.pc + signExtend13 offset)
      else
        s.setPC (s.pc + 4)
  | .BGE rs1 rs2 offset =>
      if ¬ BitVec.slt (s.getReg rs1) (s.getReg rs2) then
        s.setPC (s.pc + signExtend13 offset)
      else
        s.setPC (s.pc + 4)
  | .BLTU rs1 rs2 offset =>
      if BitVec.ult (s.getReg rs1) (s.getReg rs2) then
        s.setPC (s.pc + signExtend13 offset)
      else
        s.setPC (s.pc + 4)
  | .BGEU rs1 rs2 offset =>
      if ¬ BitVec.ult (s.getReg rs1) (s.getReg rs2) then
        s.setPC (s.pc + signExtend13 offset)
      else
        s.setPC (s.pc + 4)
  -- RV32I jumps
  | .JAL rd offset =>
      (s.setReg rd (s.pc + 4)).setPC (s.pc + signExtend21 offset)
  | .JALR rd rs1 offset =>
      (s.setReg rd (s.pc + 4)).setPC ((s.getReg rs1 + signExtend12 offset) &&& ~~~1#32)
  -- RV32I pseudo-instructions
  | .MV rd rs =>
      (s.setReg rd (s.getReg rs)).setPC (s.pc + 4)
  | .LI rd imm =>
      (s.setReg rd imm).setPC (s.pc + 4)
  | .NOP =>
      s.setPC (s.pc + 4)
  -- RV32I system
  | .ECALL =>
      s.setPC (s.pc + 4)
  | .FENCE =>
      s.setPC (s.pc + 4)
  | .EBREAK =>
      s.setPC (s.pc + 4)
  -- RV32M multiply
  | .MUL rd rs1 rs2 =>
      (s.setReg rd (s.getReg rs1 * s.getReg rs2)).setPC (s.pc + 4)
  | .MULH rd rs1 rs2 =>
      (s.setReg rd (rv32_mulh (s.getReg rs1) (s.getReg rs2))).setPC (s.pc + 4)
  | .MULHSU rd rs1 rs2 =>
      (s.setReg rd (rv32_mulhsu (s.getReg rs1) (s.getReg rs2))).setPC (s.pc + 4)
  | .MULHU rd rs1 rs2 =>
      (s.setReg rd (rv32_mulhu (s.getReg rs1) (s.getReg rs2))).setPC (s.pc + 4)
  -- RV32M divide
  | .DIV rd rs1 rs2 =>
      (s.setReg rd (rv32_div (s.getReg rs1) (s.getReg rs2))).setPC (s.pc + 4)
  | .DIVU rd rs1 rs2 =>
      (s.setReg rd (rv32_divu (s.getReg rs1) (s.getReg rs2))).setPC (s.pc + 4)
  | .REM rd rs1 rs2 =>
      (s.setReg rd (rv32_rem (s.getReg rs1) (s.getReg rs2))).setPC (s.pc + 4)
  | .REMU rd rs1 rs2 =>
      (s.setReg rd (rv32_remu (s.getReg rs1) (s.getReg rs2))).setPC (s.pc + 4)

/-- For non-branch instructions, execInstrBr agrees with execInstr
    (both advance PC by 4 and compute the same state update). -/
theorem execInstrBr_eq_execInstr (s : MachineState) (i : Instr)
    (h : i.isBranch = false) : execInstrBr s i = execInstr s i := by
  cases i <;> simp_all [execInstrBr, execInstr, Instr.isBranch,
    MachineState.pc_setReg, MachineState.pc_setMem,
    MachineState.pc_setByte, MachineState.pc_setHalfword]

@[simp] theorem committed_execInstrBr (s : MachineState) (i : Instr) :
    (execInstrBr s i).committed = s.committed := by
  cases i <;> simp [execInstrBr, MachineState.committed_setPC,
    MachineState.committed_setReg, MachineState.committed_setMem,
    MachineState.committed_setByte, MachineState.committed_setHalfword]
  all_goals split <;> simp [MachineState.committed_setPC]

@[simp] theorem publicValues_execInstrBr (s : MachineState) (i : Instr) :
    (execInstrBr s i).publicValues = s.publicValues := by
  cases i <;> simp [execInstrBr, MachineState.publicValues_setPC,
    MachineState.publicValues_setReg, MachineState.publicValues_setMem,
    MachineState.publicValues_setByte, MachineState.publicValues_setHalfword]
  all_goals split <;> simp [MachineState.publicValues_setPC]

@[simp] theorem privateInput_execInstrBr (s : MachineState) (i : Instr) :
    (execInstrBr s i).privateInput = s.privateInput := by
  cases i <;> simp [execInstrBr, MachineState.privateInput_setPC,
    MachineState.privateInput_setReg, MachineState.privateInput_setMem,
    MachineState.privateInput_setByte, MachineState.privateInput_setHalfword]
  all_goals split <;> simp [MachineState.privateInput_setPC]

@[simp] theorem code_execInstrBr (s : MachineState) (i : Instr) :
    (execInstrBr s i).code = s.code := by
  cases i <;> simp [execInstrBr, MachineState.code_setPC,
    MachineState.code_setReg, MachineState.code_setMem,
    MachineState.code_setByte, MachineState.code_setHalfword]
  all_goals split <;> simp [MachineState.code_setPC]

-- ============================================================================
-- Code memory
-- ============================================================================

/-- Code memory: maps addresses to instructions. -/
def CodeMem := Addr → Option Instr

/-- Load a program into code memory at a base address.
    Instruction k is at address base + 4*k. -/
def loadProgram (base : Addr) (prog : List Instr) : CodeMem :=
  fun addr =>
    let offset := addr - base
    let idx := offset.toNat / 4
    if offset.toNat % 4 == 0 ∧ idx < prog.length then
      prog[idx]?
    else
      none

-- ============================================================================
-- ProgramAt: abstract code memory predicate
-- ============================================================================

/-- ProgramAt code base prog asserts that program `prog` is loaded in `code`
    at base address `base`. Instruction i is at address base + 4*i. -/
def ProgramAt (code : CodeMem) (base : Addr) (prog : List Instr) : Prop :=
  ∀ (i : Nat), i < prog.length →
    code (base + BitVec.ofNat 32 (4 * i)) = prog[i]?

/-- Extract a single instruction fetch from ProgramAt. -/
theorem ProgramAt.get {code : CodeMem} {base : Addr} {prog : List Instr}
    (h : ProgramAt code base prog) {i : Nat} (hi : i < prog.length) :
    code (base + BitVec.ofNat 32 (4 * i)) = prog[i]? := h i hi

/-- ProgramAt for the first part of a concatenated program. -/
theorem ProgramAt.prefix {code : CodeMem} {base : Addr} {prog1 prog2 : List Instr}
    (h : ProgramAt code base (prog1 ++ prog2)) :
    ProgramAt code base prog1 := by
  intro i hi
  have hi' : i < (prog1 ++ prog2).length := by simp; omega
  have h_main := h i hi'
  rwa [List.getElem?_append_left hi] at h_main

/-- ProgramAt for the second part of a concatenated program. -/
theorem ProgramAt.suffix {code : CodeMem} {base : Addr} {prog1 prog2 : List Instr}
    (h : ProgramAt code base (prog1 ++ prog2)) :
    ProgramAt code (base + BitVec.ofNat 32 (4 * prog1.length)) prog2 := by
  intro i hi
  have hi' : prog1.length + i < (prog1 ++ prog2).length := by simp; omega
  have h_main := h (prog1.length + i) hi'
  rw [List.getElem?_append_right (by omega : prog1.length ≤ prog1.length + i)] at h_main
  simp only [Nat.add_sub_cancel_left] at h_main
  have haddr : base + BitVec.ofNat 32 (4 * (prog1.length + i))
             = base + BitVec.ofNat 32 (4 * prog1.length) + BitVec.ofNat 32 (4 * i) := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  rw [haddr] at h_main
  exact h_main

/-- Extract a single instruction from ProgramAt with address normalization.
    Useful for converting ProgramAt to individual code hypotheses. -/
theorem ProgramAt.fetch {code : CodeMem} {base : Addr} {prog : List Instr}
    (h : ProgramAt code base prog) (i : Nat) (addr : Addr) (instr : Instr)
    (hi : i < prog.length)
    (hinstr : prog[i]? = some instr)
    (haddr : base + BitVec.ofNat 32 (4 * i) = addr) :
    code addr = some instr := by
  rw [← haddr, ← hinstr]; exact h i hi

/-- loadProgram produces a ProgramAt. -/
theorem loadProgram_programAt (base : Addr) (prog : List Instr)
    (hlen : 4 * prog.length < 2^32) :
    ProgramAt (loadProgram base prog) base prog := by
  intro i hi
  simp [loadProgram]
  have hbase := base.isLt
  have : (4294967296 - BitVec.toNat base + (BitVec.toNat base + 4 * i)) % 4294967296
       = 4 * i := by omega
  rw [this]; simp [hi]; omega

-- ============================================================================
-- Step-based execution
-- ============================================================================

/-- Single step: fetch instruction at PC, execute with branch-aware semantics.
    Returns none if no instruction at PC (stuck/halted), or if the instruction
    is ECALL with t0 = 0 (HALT syscall, following SP1 convention).
    LW/SW trap (return none) on misaligned or out-of-range addresses.
    LB/LBU/SB trap on out-of-range addresses.
    LH/LHU/SH trap on misaligned or out-of-range addresses.
    EBREAK traps (returns none).
    WRITE (t0 = 0x02) to fd 13 appends words from memory to public values.
    COMMIT (t0 = 0x10) appends (a0, a1) to committed outputs.
    Other ECALLs continue execution. -/
def step (s : MachineState) : Option MachineState :=
  match s.code s.pc with
  | none => none
  | some (.LW rd rs1 offset) =>
    let addr := s.getReg rs1 + signExtend12 offset
    if isValidMemAccess addr then
      some (execInstrBr s (.LW rd rs1 offset))
    else none  -- trap: invalid memory access
  | some (.SW rs1 rs2 offset) =>
    let addr := s.getReg rs1 + signExtend12 offset
    if isValidMemAccess addr then
      some (execInstrBr s (.SW rs1 rs2 offset))
    else none  -- trap: invalid memory access
  | some (.LB rd rs1 offset) =>
    let addr := s.getReg rs1 + signExtend12 offset
    if isValidByteAccess addr then
      some (execInstrBr s (.LB rd rs1 offset))
    else none
  | some (.LBU rd rs1 offset) =>
    let addr := s.getReg rs1 + signExtend12 offset
    if isValidByteAccess addr then
      some (execInstrBr s (.LBU rd rs1 offset))
    else none
  | some (.LH rd rs1 offset) =>
    let addr := s.getReg rs1 + signExtend12 offset
    if isValidHalfwordAccess addr then
      some (execInstrBr s (.LH rd rs1 offset))
    else none
  | some (.LHU rd rs1 offset) =>
    let addr := s.getReg rs1 + signExtend12 offset
    if isValidHalfwordAccess addr then
      some (execInstrBr s (.LHU rd rs1 offset))
    else none
  | some (.SB rs1 rs2 offset) =>
    let addr := s.getReg rs1 + signExtend12 offset
    if isValidByteAccess addr then
      some (execInstrBr s (.SB rs1 rs2 offset))
    else none
  | some (.SH rs1 rs2 offset) =>
    let addr := s.getReg rs1 + signExtend12 offset
    if isValidHalfwordAccess addr then
      some (execInstrBr s (.SH rs1 rs2 offset))
    else none
  | some .EBREAK => none  -- trap: breakpoint
  | some .ECALL =>
    let t0 := s.getReg .x5
    if t0 == (0 : Word) then none  -- HALT syscall (SP1: t0 = 0)
    else if t0 == (0x02 : Word) then  -- WRITE syscall
      let fd := s.getReg .x10
      let buf := s.getReg .x11
      let nbytes := s.getReg .x12
      if fd == (13 : Word) then
        -- SP1: reads nbytes individual bytes from memory
        let bytes := s.readBytes buf nbytes.toNat
        some ((s.appendPublicValues bytes).setPC (s.pc + 4))
      else
        some (s.setPC (s.pc + 4))  -- other fd: continue
    else if t0 == (0x10 : Word) then  -- COMMIT syscall
      some ((s.appendCommit (s.getReg .x10) (s.getReg .x11)).setPC (s.pc + 4))
    else if t0 == (0xF0 : Word) then  -- HINT_LEN syscall
      -- SP1: returns actual byte count of input stream
      let len := BitVec.ofNat 32 s.privateInput.length
      some ((s.setReg .x10 len).setPC (s.pc + 4))
    else if t0 == (0xF1 : Word) then  -- HINT_READ syscall
      let addr := s.getReg .x10
      let nbytes := s.getReg .x11
      let nbytes_val := nbytes.toNat
      -- SP1: pops nbytes bytes, groups into 4-byte LE words, writes to word-aligned memory
      if nbytes_val ≤ s.privateInput.length then
        let bytes := s.privateInput.take nbytes_val
        let s' := { s with privateInput := s.privateInput.drop nbytes_val }
        some ((s'.writeBytesAsWords addr bytes).setPC (s.pc + 4))
      else
        none  -- trap: not enough input (SP1: panic)
    else some (execInstrBr s .ECALL)  -- other ecalls continue
  | some i => some (execInstrBr s i)

/-- step for non-ECALL, non-EBREAK, non-memory instructions. -/
@[simp] theorem step_non_ecall_non_mem (s : MachineState) (i : Instr)
    (hfetch : s.code s.pc = some i) (hne : i ≠ .ECALL) (hnb : i ≠ .EBREAK)
    (hnm : i.isMemAccess = false) :
    step s = some (execInstrBr s i) := by
  unfold step; rw [hfetch]; cases i <;> simp_all [Instr.isMemAccess]

/-- step for LW with valid memory access. -/
theorem step_lw (s : MachineState) (rd rs1 : Reg) (offset : BitVec 12)
    (hfetch : s.code s.pc = some (.LW rd rs1 offset))
    (hvalid : isValidMemAccess (s.getReg rs1 + signExtend12 offset) = true) :
    step s = some (execInstrBr s (.LW rd rs1 offset)) := by
  simp [step, hfetch, isValidMemAccess, isValidMemAddr, isAligned4, SP1_MEM_START, SP1_MEM_END] at hvalid ⊢
  omega

/-- step for SW with valid memory access. -/
theorem step_sw (s : MachineState) (rs1 rs2 : Reg) (offset : BitVec 12)
    (hfetch : s.code s.pc = some (.SW rs1 rs2 offset))
    (hvalid : isValidMemAccess (s.getReg rs1 + signExtend12 offset) = true) :
    step s = some (execInstrBr s (.SW rs1 rs2 offset)) := by
  simp [step, hfetch, isValidMemAccess, isValidMemAddr, isAligned4, SP1_MEM_START, SP1_MEM_END] at hvalid ⊢
  omega

/-- step for LW with invalid memory access (trap). -/
theorem step_lw_trap (s : MachineState) (rd rs1 : Reg) (offset : BitVec 12)
    (hfetch : s.code s.pc = some (.LW rd rs1 offset))
    (hinvalid : isValidMemAccess (s.getReg rs1 + signExtend12 offset) = false) :
    step s = none := by
  simp [step, hfetch, isValidMemAccess, isValidMemAddr, isAligned4, SP1_MEM_START, SP1_MEM_END] at hinvalid ⊢
  omega

/-- step for SW with invalid memory access (trap). -/
theorem step_sw_trap (s : MachineState) (rs1 rs2 : Reg) (offset : BitVec 12)
    (hfetch : s.code s.pc = some (.SW rs1 rs2 offset))
    (hinvalid : isValidMemAccess (s.getReg rs1 + signExtend12 offset) = false) :
    step s = none := by
  simp [step, hfetch, isValidMemAccess, isValidMemAddr, isAligned4, SP1_MEM_START, SP1_MEM_END] at hinvalid ⊢
  omega

/-- step for LB with valid byte access. -/
theorem step_lb (s : MachineState) (rd rs1 : Reg) (offset : BitVec 12)
    (hfetch : s.code s.pc = some (.LB rd rs1 offset))
    (hvalid : isValidByteAccess (s.getReg rs1 + signExtend12 offset) = true) :
    step s = some (execInstrBr s (.LB rd rs1 offset)) := by
  simp [step, hfetch, isValidByteAccess, isValidMemAddr, SP1_MEM_START, SP1_MEM_END] at hvalid ⊢
  omega

/-- step for LB with invalid byte access (trap). -/
theorem step_lb_trap (s : MachineState) (rd rs1 : Reg) (offset : BitVec 12)
    (hfetch : s.code s.pc = some (.LB rd rs1 offset))
    (hinvalid : isValidByteAccess (s.getReg rs1 + signExtend12 offset) = false) :
    step s = none := by
  simp [step, hfetch, isValidByteAccess, isValidMemAddr, SP1_MEM_START, SP1_MEM_END] at hinvalid ⊢
  omega

/-- step for LBU with valid byte access. -/
theorem step_lbu (s : MachineState) (rd rs1 : Reg) (offset : BitVec 12)
    (hfetch : s.code s.pc = some (.LBU rd rs1 offset))
    (hvalid : isValidByteAccess (s.getReg rs1 + signExtend12 offset) = true) :
    step s = some (execInstrBr s (.LBU rd rs1 offset)) := by
  simp [step, hfetch, isValidByteAccess, isValidMemAddr, SP1_MEM_START, SP1_MEM_END] at hvalid ⊢
  omega

/-- step for LBU with invalid byte access (trap). -/
theorem step_lbu_trap (s : MachineState) (rd rs1 : Reg) (offset : BitVec 12)
    (hfetch : s.code s.pc = some (.LBU rd rs1 offset))
    (hinvalid : isValidByteAccess (s.getReg rs1 + signExtend12 offset) = false) :
    step s = none := by
  simp [step, hfetch, isValidByteAccess, isValidMemAddr, SP1_MEM_START, SP1_MEM_END] at hinvalid ⊢
  omega

/-- step for LH with valid halfword access. -/
theorem step_lh (s : MachineState) (rd rs1 : Reg) (offset : BitVec 12)
    (hfetch : s.code s.pc = some (.LH rd rs1 offset))
    (hvalid : isValidHalfwordAccess (s.getReg rs1 + signExtend12 offset) = true) :
    step s = some (execInstrBr s (.LH rd rs1 offset)) := by
  simp [step, hfetch, isValidHalfwordAccess, isValidMemAddr, isAligned2, SP1_MEM_START, SP1_MEM_END] at hvalid ⊢
  omega

/-- step for LH with invalid halfword access (trap). -/
theorem step_lh_trap (s : MachineState) (rd rs1 : Reg) (offset : BitVec 12)
    (hfetch : s.code s.pc = some (.LH rd rs1 offset))
    (hinvalid : isValidHalfwordAccess (s.getReg rs1 + signExtend12 offset) = false) :
    step s = none := by
  simp [step, hfetch, isValidHalfwordAccess, isValidMemAddr, isAligned2, SP1_MEM_START, SP1_MEM_END] at hinvalid ⊢
  omega

/-- step for LHU with valid halfword access. -/
theorem step_lhu (s : MachineState) (rd rs1 : Reg) (offset : BitVec 12)
    (hfetch : s.code s.pc = some (.LHU rd rs1 offset))
    (hvalid : isValidHalfwordAccess (s.getReg rs1 + signExtend12 offset) = true) :
    step s = some (execInstrBr s (.LHU rd rs1 offset)) := by
  simp [step, hfetch, isValidHalfwordAccess, isValidMemAddr, isAligned2, SP1_MEM_START, SP1_MEM_END] at hvalid ⊢
  omega

/-- step for LHU with invalid halfword access (trap). -/
theorem step_lhu_trap (s : MachineState) (rd rs1 : Reg) (offset : BitVec 12)
    (hfetch : s.code s.pc = some (.LHU rd rs1 offset))
    (hinvalid : isValidHalfwordAccess (s.getReg rs1 + signExtend12 offset) = false) :
    step s = none := by
  simp [step, hfetch, isValidHalfwordAccess, isValidMemAddr, isAligned2, SP1_MEM_START, SP1_MEM_END] at hinvalid ⊢
  omega

/-- step for SB with valid byte access. -/
theorem step_sb (s : MachineState) (rs1 rs2 : Reg) (offset : BitVec 12)
    (hfetch : s.code s.pc = some (.SB rs1 rs2 offset))
    (hvalid : isValidByteAccess (s.getReg rs1 + signExtend12 offset) = true) :
    step s = some (execInstrBr s (.SB rs1 rs2 offset)) := by
  simp [step, hfetch, isValidByteAccess, isValidMemAddr, SP1_MEM_START, SP1_MEM_END] at hvalid ⊢
  omega

/-- step for SB with invalid byte access (trap). -/
theorem step_sb_trap (s : MachineState) (rs1 rs2 : Reg) (offset : BitVec 12)
    (hfetch : s.code s.pc = some (.SB rs1 rs2 offset))
    (hinvalid : isValidByteAccess (s.getReg rs1 + signExtend12 offset) = false) :
    step s = none := by
  simp [step, hfetch, isValidByteAccess, isValidMemAddr, SP1_MEM_START, SP1_MEM_END] at hinvalid ⊢
  omega

/-- step for SH with valid halfword access. -/
theorem step_sh (s : MachineState) (rs1 rs2 : Reg) (offset : BitVec 12)
    (hfetch : s.code s.pc = some (.SH rs1 rs2 offset))
    (hvalid : isValidHalfwordAccess (s.getReg rs1 + signExtend12 offset) = true) :
    step s = some (execInstrBr s (.SH rs1 rs2 offset)) := by
  simp [step, hfetch, isValidHalfwordAccess, isValidMemAddr, isAligned2, SP1_MEM_START, SP1_MEM_END] at hvalid ⊢
  omega

/-- step for SH with invalid halfword access (trap). -/
theorem step_sh_trap (s : MachineState) (rs1 rs2 : Reg) (offset : BitVec 12)
    (hfetch : s.code s.pc = some (.SH rs1 rs2 offset))
    (hinvalid : isValidHalfwordAccess (s.getReg rs1 + signExtend12 offset) = false) :
    step s = none := by
  simp [step, hfetch, isValidHalfwordAccess, isValidMemAddr, isAligned2, SP1_MEM_START, SP1_MEM_END] at hinvalid ⊢
  omega

/-- step for EBREAK (always traps). -/
theorem step_ebreak (s : MachineState)
    (hfetch : s.code s.pc = some .EBREAK) :
    step s = none := by
  simp [step, hfetch]

theorem step_ecall_halt (s : MachineState)
    (hfetch : s.code s.pc = some .ECALL) (ht0 : s.getReg .x5 = 0) :
    step s = none := by
  simp [step, hfetch, ht0]

theorem step_ecall_continue (s : MachineState)
    (hfetch : s.code s.pc = some .ECALL)
    (ht0 : s.getReg .x5 ≠ 0)
    (ht0_nw : s.getReg .x5 ≠ (0x02 : Word))
    (ht0_nc : s.getReg .x5 ≠ (0x10 : Word))
    (ht0_nhl : s.getReg .x5 ≠ (0xF0 : Word))
    (ht0_nhr : s.getReg .x5 ≠ (0xF1 : Word)) :
    step s = some (execInstrBr s .ECALL) := by
  simp only [step, hfetch, beq_iff_eq, ht0, ht0_nw, ht0_nc, ht0_nhl, ht0_nhr, ↓reduceIte]

/-- COMMIT syscall (SP1 convention: t0 = 0x10) appends (a0, a1) to committed outputs. -/
theorem step_ecall_commit (s : MachineState)
    (hfetch : s.code s.pc = some .ECALL)
    (ht0 : s.getReg .x5 = BitVec.ofNat 32 0x10) :
    step s =
      some ((s.appendCommit (s.getReg .x10) (s.getReg .x11)).setPC (s.pc + 4)) := by
  simp [step, hfetch, ht0]

/-- WRITE syscall to FD_PUBLIC_VALUES (t0 = 0x02, fd = 13) appends bytes from memory. -/
theorem step_ecall_write_public (s : MachineState)
    (hfetch : s.code s.pc = some .ECALL)
    (ht0 : s.getReg .x5 = BitVec.ofNat 32 0x02)
    (hfd : s.getReg .x10 = 13) :
    step s =
      some ((s.appendPublicValues (s.readBytes (s.getReg .x11) (s.getReg .x12).toNat)).setPC (s.pc + 4)) := by
  simp [step, hfetch, ht0, hfd]

/-- WRITE syscall to non-public-values fd (t0 = 0x02, fd ≠ 13) just advances PC. -/
theorem step_ecall_write_other (s : MachineState)
    (hfetch : s.code s.pc = some .ECALL)
    (ht0 : s.getReg .x5 = BitVec.ofNat 32 0x02)
    (hfd : s.getReg .x10 ≠ (13 : Word)) :
    step s = some (s.setPC (s.pc + 4)) := by
  simp only [step, hfetch, ht0, beq_iff_eq, hfd, ite_false]
  simp (config := { decide := true })

/-- HINT_LEN syscall (SP1 convention: t0 = 0xF0) returns privateInput.length in a0. -/
theorem step_ecall_hint_len (s : MachineState)
    (hfetch : s.code s.pc = some .ECALL)
    (ht0 : s.getReg .x5 = BitVec.ofNat 32 0xF0) :
    step s =
      some ((s.setReg .x10 (BitVec.ofNat 32 s.privateInput.length)).setPC (s.pc + 4)) := by
  simp [step, hfetch, ht0]

/-- HINT_READ syscall (SP1 convention: t0 = 0xF1) reads bytes from privateInput into memory as LE words. -/
theorem step_ecall_hint_read (s : MachineState)
    (hfetch : s.code s.pc = some .ECALL)
    (ht0 : s.getReg .x5 = BitVec.ofNat 32 0xF1)
    (hsuff : (s.getReg .x11).toNat ≤ s.privateInput.length) :
    step s =
      let nbytes_val := (s.getReg .x11).toNat
      let bytes := s.privateInput.take nbytes_val
      let s' := { s with privateInput := s.privateInput.drop nbytes_val }
      some ((s'.writeBytesAsWords (s.getReg .x10) bytes).setPC (s.pc + 4)) := by
  simp [step, hfetch, ht0, hsuff]

/-- HINT_READ syscall traps when not enough input is available. -/
theorem step_ecall_hint_read_trap (s : MachineState)
    (hfetch : s.code s.pc = some .ECALL)
    (ht0 : s.getReg .x5 = BitVec.ofNat 32 0xF1)
    (hinsuff : ¬ ((s.getReg .x11).toNat ≤ s.privateInput.length)) :
    step s = none := by
  simp [step, hfetch, ht0, hinsuff]

/-- Multi-step execution (n steps). -/
def stepN : Nat → MachineState → Option MachineState
  | 0,     s => some s
  | n + 1, s => (step s).bind (stepN n ·)

-- ============================================================================
-- stepN lemmas
-- ============================================================================

@[simp]
theorem stepN_zero (s : MachineState) :
    stepN 0 s = some s := rfl

@[simp]
theorem stepN_succ (s : MachineState) (n : Nat) :
    stepN (n + 1) s = (step s).bind (stepN n ·) := rfl

theorem stepN_one (s : MachineState) :
    stepN 1 s = step s := by
  simp [stepN, Option.bind]
  cases step s <;> simp

/-- Composing step counts: n+m steps = n steps then m steps. -/
theorem stepN_add (n m : Nat) (s : MachineState) :
    stepN (n + m) s = (stepN n s).bind (stepN m ·) := by
  induction n generalizing s with
  | zero => simp [Option.bind]
  | succ k ih =>
    simp only [Nat.succ_add, stepN_succ]
    cases h : step s with
    | none => simp [Option.bind]
    | some s' => simp [Option.bind, ih]

/-- If stepN n succeeds and then stepN m succeeds, stepN (n+m) gives the same result. -/
theorem stepN_add_eq (n m : Nat) (s s' s'' : MachineState)
    (h1 : stepN n s = some s')
    (h2 : stepN m s' = some s'') :
    stepN (n + m) s = some s'' := by
  rw [stepN_add, h1, Option.bind]
  exact h2

-- ============================================================================
-- Code preservation through execution
-- ============================================================================

/-- step preserves code memory. -/
theorem code_step {s s' : MachineState} (h : step s = some s') :
    s'.code = s.code := by
  simp only [step] at h
  -- Split the outer match on s.code s.pc, then recursively split ifs
  -- Each leaf is either `none = some s'` (contradiction) or `some x = some s'` (extract+simp)
  split at h <;> (
    first
    | (simp only [Option.some.injEq] at h; rw [← h]; simp)
    | (simp at h; done)
    | (split at h <;> first
        | (simp only [Option.some.injEq] at h; rw [← h]; simp)
        | (simp at h; done)
        | (split at h <;> first
            | (simp only [Option.some.injEq] at h; rw [← h]; simp)
            | (simp at h; done)
            | (split at h <;> first
                | (simp only [Option.some.injEq] at h; rw [← h]; simp)
                | (simp at h; done)
                | (split at h <;> first
                    | (simp only [Option.some.injEq] at h; rw [← h]; simp)
                    | (simp at h; done)
                    | (split at h <;> first
                        | (simp only [Option.some.injEq] at h; rw [← h]; simp)
                        | (simp at h; done)
                        | (split at h <;> first
                            | (simp only [Option.some.injEq] at h; rw [← h]; simp)
                            | (simp at h; done))))))))

/-- stepN preserves code memory. -/
theorem code_stepN {k : Nat} {s s' : MachineState} (h : stepN k s = some s') :
    s'.code = s.code := by
  induction k generalizing s with
  | zero => simp at h; exact h ▸ rfl
  | succ n ih =>
    simp [stepN, Option.bind] at h
    cases hs : step s with
    | none => simp [hs] at h
    | some s_mid =>
      rw [hs] at h; simp at h
      have h1 := code_step hs
      have h2 := ih h
      rw [h2, h1]

end EvmAsm
