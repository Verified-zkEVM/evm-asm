/-
  EvmAsm.Rv64.Execution

  Branch-aware instruction execution, code memory, and step-based execution.
  64-bit variant of EvmAsm.Execution (which models RV32IM).

  This module provides an alternative execution model that handles branch and
  jump instructions with proper PC semantics (as opposed to the straight-line
  execInstr which always advances PC by 4).

  Key components:
  - execInstrBr: per-instruction PC control (branches change PC by offset)
  - CodeMem: maps addresses to instructions
  - loadProgram: loads a program into code memory at a base address
  - step / stepN: single-step and multi-step execution over code memory
-/

-- `Instructions` transitively imports `Basic`. `Program` is not used in this
-- module — its consumers (RLP/opcode programs, ControlFlow) import `Program`
-- directly.
import EvmAsm.Rv64.Instructions

namespace EvmAsm.Rv64

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
  -- RV64I ALU register-register
  | .ADD rd rs1 rs2 =>
      (s.setReg rd (s.getReg rs1 + s.getReg rs2)).setPC (s.pc + 4)
  | .SUB rd rs1 rs2 =>
      (s.setReg rd (s.getReg rs1 - s.getReg rs2)).setPC (s.pc + 4)
  | .SLL rd rs1 rs2 =>
      let shamt := (s.getReg rs2).toNat % 64
      (s.setReg rd (s.getReg rs1 <<< shamt)).setPC (s.pc + 4)
  | .SRL rd rs1 rs2 =>
      let shamt := (s.getReg rs2).toNat % 64
      (s.setReg rd (s.getReg rs1 >>> shamt)).setPC (s.pc + 4)
  | .SRA rd rs1 rs2 =>
      let shamt := (s.getReg rs2).toNat % 64
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
  -- RV64I ALU immediate
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
  -- RV64I upper immediate
  | .LUI rd imm =>
      -- RV64: LUI sign-extends the 32-bit result to 64 bits
      let val32 : BitVec 32 := imm.zeroExtend 32 <<< 12
      (s.setReg rd (val32.signExtend 64)).setPC (s.pc + 4)
  | .AUIPC rd imm =>
      let val32 : BitVec 32 := imm.zeroExtend 32 <<< 12
      let val : Word := s.pc + (val32.signExtend 64)
      (s.setReg rd val).setPC (s.pc + 4)
  -- RV64I doubleword memory
  | .LD rd rs1 offset =>
      let addr := s.getReg rs1 + signExtend12 offset
      (s.setReg rd (s.getMem addr)).setPC (s.pc + 4)
  | .SD rs1 rs2 offset =>
      let addr := s.getReg rs1 + signExtend12 offset
      (s.setMem addr (s.getReg rs2)).setPC (s.pc + 4)
  -- RV64I word memory (LW sign-extends to 64 bits, SW stores lower 32 bits)
  | .LW rd rs1 offset =>
      let addr := s.getReg rs1 + signExtend12 offset
      (s.setReg rd ((s.getWord32 addr).signExtend 64)).setPC (s.pc + 4)
  | .LWU rd rs1 offset =>
      let addr := s.getReg rs1 + signExtend12 offset
      (s.setReg rd ((s.getWord32 addr).zeroExtend 64)).setPC (s.pc + 4)
  | .SW rs1 rs2 offset =>
      let addr := s.getReg rs1 + signExtend12 offset
      (s.setWord32 addr ((s.getReg rs2).truncate 32)).setPC (s.pc + 4)
  -- RV64I sub-word memory
  | .LB rd rs1 offset =>
      let addr := s.getReg rs1 + signExtend12 offset
      (s.setReg rd ((s.getByte addr).signExtend 64)).setPC (s.pc + 4)
  | .LH rd rs1 offset =>
      let addr := s.getReg rs1 + signExtend12 offset
      (s.setReg rd ((s.getHalfword addr).signExtend 64)).setPC (s.pc + 4)
  | .LBU rd rs1 offset =>
      let addr := s.getReg rs1 + signExtend12 offset
      (s.setReg rd ((s.getByte addr).zeroExtend 64)).setPC (s.pc + 4)
  | .LHU rd rs1 offset =>
      let addr := s.getReg rs1 + signExtend12 offset
      (s.setReg rd ((s.getHalfword addr).zeroExtend 64)).setPC (s.pc + 4)
  | .SB rs1 rs2 offset =>
      let addr := s.getReg rs1 + signExtend12 offset
      (s.setByte addr ((s.getReg rs2).truncate 8)).setPC (s.pc + 4)
  | .SH rs1 rs2 offset =>
      let addr := s.getReg rs1 + signExtend12 offset
      (s.setHalfword addr ((s.getReg rs2).truncate 16)).setPC (s.pc + 4)
  -- RV64I branches
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
  -- RV64I jumps
  | .JAL rd offset =>
      (s.setReg rd (s.pc + 4)).setPC (s.pc + signExtend21 offset)
  | .JALR rd rs1 offset =>
      (s.setReg rd (s.pc + 4)).setPC ((s.getReg rs1 + signExtend12 offset) &&& ~~~1#64)
  -- RV64I pseudo-instructions
  | .MV rd rs =>
      (s.setReg rd (s.getReg rs)).setPC (s.pc + 4)
  | .LI rd imm =>
      (s.setReg rd imm).setPC (s.pc + 4)
  | .NOP =>
      s.setPC (s.pc + 4)
  -- RV64I *W instructions
  | .ADDIW rd rs1 imm =>
      let sum32 : BitVec 32 := ((s.getReg rs1).truncate 32) + ((signExtend12 imm).truncate 32)
      (s.setReg rd (sum32.signExtend 64)).setPC (s.pc + 4)
  -- RV64I system
  | .ECALL =>
      s.setPC (s.pc + 4)
  -- ZisK accelerator call (validity checked by `step`)
  | .CSRS csr rs1 =>
      (s.execCsrs csr rs1).setPC (s.pc + 4)
  | .FENCE =>
      s.setPC (s.pc + 4)
  | .EBREAK =>
      s.setPC (s.pc + 4)
  -- RV64M multiply
  | .MUL rd rs1 rs2 =>
      (s.setReg rd (s.getReg rs1 * s.getReg rs2)).setPC (s.pc + 4)
  | .MULH rd rs1 rs2 =>
      (s.setReg rd (rv64_mulh (s.getReg rs1) (s.getReg rs2))).setPC (s.pc + 4)
  | .MULHSU rd rs1 rs2 =>
      (s.setReg rd (rv64_mulhsu (s.getReg rs1) (s.getReg rs2))).setPC (s.pc + 4)
  | .MULHU rd rs1 rs2 =>
      (s.setReg rd (rv64_mulhu (s.getReg rs1) (s.getReg rs2))).setPC (s.pc + 4)
  -- RV64M divide
  | .DIV rd rs1 rs2 =>
      (s.setReg rd (rv64_div (s.getReg rs1) (s.getReg rs2))).setPC (s.pc + 4)
  | .DIVU rd rs1 rs2 =>
      (s.setReg rd (rv64_divu (s.getReg rs1) (s.getReg rs2))).setPC (s.pc + 4)
  | .REM rd rs1 rs2 =>
      (s.setReg rd (rv64_rem (s.getReg rs1) (s.getReg rs2))).setPC (s.pc + 4)
  | .REMU rd rs1 rs2 =>
      (s.setReg rd (rv64_remu (s.getReg rs1) (s.getReg rs2))).setPC (s.pc + 4)

/-- For non-branch instructions, execInstrBr agrees with execInstr
    (both advance PC by 4 and compute the same state update). -/
theorem execInstrBr_eq_execInstr {s : MachineState} {i : Instr}
    (h : i.isBranch = false) : execInstrBr s i = execInstr s i := by
  cases i <;> simp_all [execInstrBr, execInstr, Instr.isBranch,
    MachineState.pc_setReg, MachineState.pc_setMem,
    MachineState.pc_setByte, MachineState.pc_setHalfword,
    MachineState.pc_setWord32]

@[simp] theorem committed_execInstrBr {s : MachineState} {i : Instr} :
    (execInstrBr s i).committed = s.committed := by
  cases i <;> simp [execInstrBr, MachineState.committed_setPC,
    MachineState.committed_setReg, MachineState.committed_setMem,
    MachineState.committed_setByte, MachineState.committed_setHalfword,
    MachineState.setWord32]
  all_goals split <;> simp [MachineState.committed_setPC]

@[simp] theorem publicValues_execInstrBr {s : MachineState} {i : Instr} :
    (execInstrBr s i).publicValues = s.publicValues := by
  cases i <;> simp [execInstrBr, MachineState.publicValues_setPC,
    MachineState.publicValues_setReg, MachineState.publicValues_setMem,
    MachineState.publicValues_setByte, MachineState.publicValues_setHalfword,
    MachineState.setWord32]
  all_goals split <;> simp [MachineState.publicValues_setPC]

@[simp] theorem privateInput_execInstrBr {s : MachineState} {i : Instr} :
    (execInstrBr s i).privateInput = s.privateInput := by
  cases i <;> simp [execInstrBr, MachineState.privateInput_setPC,
    MachineState.privateInput_setReg, MachineState.privateInput_setMem,
    MachineState.privateInput_setByte, MachineState.privateInput_setHalfword,
    MachineState.setWord32]
  all_goals split <;> simp [MachineState.privateInput_setPC]

@[simp] theorem code_execInstrBr {s : MachineState} {i : Instr} :
    (execInstrBr s i).code = s.code := by
  cases i <;> simp [execInstrBr, MachineState.code_setPC,
    MachineState.code_setReg, MachineState.code_setMem,
    MachineState.code_setByte, MachineState.code_setHalfword,
    MachineState.code_setWord32]
  all_goals split <;> simp [MachineState.code_setPC]

-- ============================================================================
-- Code memory
-- ============================================================================

/-- Code memory: maps addresses to instructions. -/
def CodeMem := Word → Option Instr

/-- Load a program into code memory at a base address.
    Instruction k is at address base + 4*k. -/
def loadProgram (base : Word) (prog : List Instr) : CodeMem :=
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
def ProgramAt (code : CodeMem) (base : Word) (prog : List Instr) : Prop :=
  ∀ (i : Nat), i < prog.length →
    code (base + BitVec.ofNat 64 (4 * i)) = prog[i]?

/-- Extract a single instruction fetch from ProgramAt. -/
theorem ProgramAt.get {code : CodeMem} {base : Word} {prog : List Instr}
    (h : ProgramAt code base prog) {i : Nat} (hi : i < prog.length) :
    code (base + BitVec.ofNat 64 (4 * i)) = prog[i]? := h i hi

/-- ProgramAt for the first part of a concatenated program. -/
theorem ProgramAt.prefix {code : CodeMem} {base : Word} {prog1 prog2 : List Instr}
    (h : ProgramAt code base (prog1 ++ prog2)) :
    ProgramAt code base prog1 := by
  intro i hi
  have hi' : i < (prog1 ++ prog2).length := by simp; omega
  have h_main := h i hi'
  rwa [List.getElem?_append_left hi] at h_main

/-- ProgramAt for the second part of a concatenated program. -/
theorem ProgramAt.suffix {code : CodeMem} {base : Word} {prog1 prog2 : List Instr}
    (h : ProgramAt code base (prog1 ++ prog2)) :
    ProgramAt code (base + BitVec.ofNat 64 (4 * prog1.length)) prog2 := by
  intro i hi
  have hi' : prog1.length + i < (prog1 ++ prog2).length := by simp; omega
  have h_main := h (prog1.length + i) hi'
  rw [List.getElem?_append_right (by omega : prog1.length ≤ prog1.length + i)] at h_main
  simp only [Nat.add_sub_cancel_left] at h_main
  have haddr : base + BitVec.ofNat 64 (4 * (prog1.length + i))
             = base + BitVec.ofNat 64 (4 * prog1.length) + BitVec.ofNat 64 (4 * i) := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  rw [haddr] at h_main
  exact h_main

/-- Extract a single instruction from ProgramAt with address normalization.
    Useful for converting ProgramAt to individual code hypotheses. -/
theorem ProgramAt.fetch {code : CodeMem} {base : Word} {prog : List Instr}
    (h : ProgramAt code base prog) (i : Nat) (addr : Word) (instr : Instr)
    (hi : i < prog.length)
    (hinstr : prog[i]? = some instr)
    (haddr : base + BitVec.ofNat 64 (4 * i) = addr) :
    code addr = some instr := by
  rw [← haddr, ← hinstr]; exact h i hi

/-- loadProgram produces a ProgramAt. -/
theorem loadProgram_programAt {base : Word} {prog : List Instr}
    (hlen : 4 * prog.length < 2^64) :
    ProgramAt (loadProgram base prog) base prog := by
  intro i hi
  simp [loadProgram]
  have := base.isLt
  have : (18446744073709551616 - BitVec.toNat base + (BitVec.toNat base + 4 * i)) % 18446744073709551616
       = 4 * i := by omega
  rw [this]; simp [hi]; omega

-- ============================================================================
-- Step-based execution
-- ============================================================================

/-- Single step: fetch instruction at PC, execute with branch-aware semantics.
    Returns none if no instruction at PC (stuck/halted), or if the instruction
    is ECALL with t0 = 0 (HALT syscall, following SP1 convention).
    LD/SD trap (return none) on misaligned or out-of-range dword addresses.
    LW/LWU/SW trap (return none) on misaligned or out-of-range addresses.
    LB/LBU/SB trap on out-of-range addresses.
    LH/LHU/SH trap on misaligned or out-of-range addresses.
    EBREAK traps (returns none).
    WRITE (t0 = 0x02) to fd 13 appends bytes from memory to public values.
    write_output (t0 = 0x10) appends a1 bytes from memory at a0 to public
    output bytes.
    Other ECALLs continue execution. -/
def step (s : MachineState) : Option MachineState :=
  match s.code s.pc with
  | none => none
  | some (.LD rd rs1 offset) =>
    let addr := s.getReg rs1 + signExtend12 offset
    if isValidDwordAccess addr then
      some (execInstrBr s (.LD rd rs1 offset))
    else none  -- trap: invalid dword memory access
  | some (.SD rs1 rs2 offset) =>
    let addr := s.getReg rs1 + signExtend12 offset
    if isValidDwordAccess addr then
      some (execInstrBr s (.SD rs1 rs2 offset))
    else none  -- trap: invalid dword memory access
  | some (.LW rd rs1 offset) =>
    let addr := s.getReg rs1 + signExtend12 offset
    if isValidMemAccess addr then
      some (execInstrBr s (.LW rd rs1 offset))
    else none  -- trap: invalid memory access
  | some (.LWU rd rs1 offset) =>
    let addr := s.getReg rs1 + signExtend12 offset
    if isValidMemAccess addr then
      some (execInstrBr s (.LWU rd rs1 offset))
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
  | some (.CSRS csr rs1) =>
    -- ZisK accelerator: all operand dwords valid (and, for Arith256Mod,
    -- modulus ≠ 0), else trap.  Unmodeled CSR ids always trap.
    if s.csrsValid csr rs1 then
      some (execInstrBr s (.CSRS csr rs1))
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
    else if t0 == (0x10 : Word) then  -- write_output syscall
      some ((s.writeOutput (s.getReg .x10) (s.getReg .x11)).setPC (s.pc + 4))
    else if t0 == (0xF2 : Word) then  -- read_input syscall (zkvm-standards C ABI)
      -- Idempotent: writes (inputBufBase, privateInput.length) to the
      -- two out-pointers supplied in a0/a1. Does not mutate input state.
      -- a0 = &buf_ptr  →  [a0] := s.inputBufBase
      -- a1 = &buf_size →  [a1] := s.privateInput.length (as 64-bit Word)
      if isValidDwordAccess (s.getReg .x10) && isValidDwordAccess (s.getReg .x11) then
        let s' := s.setMem (s.getReg .x10) s.inputBufBase
        let s'' := s'.setMem (s.getReg .x11) (BitVec.ofNat 64 s.privateInput.length)
        some (s''.setPC (s.pc + 4))
      else
        none  -- trap: out-pointer is not a valid dword address
    else some (execInstrBr s .ECALL)  -- other ecalls continue
  | some i => some (execInstrBr s i)

-- ============================================================================
-- Trap-aware step result (distinguishing misaligned access)
--
-- `step` collapses every trap to `none`. For stating equivalence/soundness
-- results cleanly ("unless a misaligned access happens, …") we surface a
-- misaligned-access trap as a distinct value via `stepResult`, WITHOUT touching
-- `step`/`stepN` (which underpin the CPS Hoare-triple framework and ~all proofs).
-- `stepResult` is connected back to `step` by `step_eq_stepResult_toOption`.
-- ============================================================================

/-- Kinds of trap an interpreter step can raise.

    Deliberately coarse for now: only `misalignedAccess` is distinguished; every
    other `step`-trap (HALT/EBREAK, decode failure, out-of-range access, bad
    syscall pointer) is lumped into `other`. **Extensible:** to surface a further
    kind (e.g. `outOfRange`, `halt`, `decodeFail`) add a constructor here and a
    corresponding classifier branch in `stepResult` (mirroring `isMisalignedAccess`);
    `StepResult.toOption` and the `step` bridge are unaffected since they only
    distinguish `ok` from "any trap". -/
inductive TrapKind where
  | misalignedAccess
  | other
  deriving DecidableEq, Repr

/-- Outcome of one interpreter step: a successful next state, or a trap. -/
inductive StepResult where
  | ok (s : MachineState)
  | trap (k : TrapKind)

/-- Forget the trap kind, recovering the `Option`-based view used by `step`. -/
def StepResult.toOption : StepResult → Option MachineState
  | .ok s   => some s
  | .trap _ => none

/-- Lift an `Option`-step into a `StepResult`, attributing a `none` to `other`. -/
def stepResultOfOption : Option MachineState → StepResult
  | some s => .ok s
  | none   => .trap .other

@[simp] theorem stepResultOfOption_toOption (o : Option MachineState) :
    (stepResultOfOption o).toOption = o := by
  cases o <;> rfl

/-- The current instruction is a memory access that is **in range but misaligned**
    (the one way a memory `step` can trap that the Sail golden model handles
    specially). Byte accesses never misalign. -/
def isMisalignedAccess (s : MachineState) : Bool :=
  match s.code s.pc with
  | some (.LD _ rs1 off)  => let a := s.getReg rs1 + signExtend12 off; isValidMemAddr a && !isAligned8 a
  | some (.SD rs1 _ off)  => let a := s.getReg rs1 + signExtend12 off; isValidMemAddr a && !isAligned8 a
  | some (.LW _ rs1 off)  => let a := s.getReg rs1 + signExtend12 off; isValidMemAddr a && !isAligned4 a
  | some (.LWU _ rs1 off) => let a := s.getReg rs1 + signExtend12 off; isValidMemAddr a && !isAligned4 a
  | some (.SW rs1 _ off)  => let a := s.getReg rs1 + signExtend12 off; isValidMemAddr a && !isAligned4 a
  | some (.LH _ rs1 off)  => let a := s.getReg rs1 + signExtend12 off; isValidMemAddr a && !isAligned2 a
  | some (.LHU _ rs1 off) => let a := s.getReg rs1 + signExtend12 off; isValidMemAddr a && !isAligned2 a
  | some (.SH rs1 _ off)  => let a := s.getReg rs1 + signExtend12 off; isValidMemAddr a && !isAligned2 a
  | _ => false

/-- Trap-aware single step: identical to `step`, except an in-range-but-misaligned
    memory access yields `.trap .misalignedAccess` rather than being collapsed to
    `none`. All other outcomes match `step` (success → `.ok`, any other trap →
    `.trap .other`). See `step_eq_stepResult_toOption` for the precise bridge. -/
def stepResult (s : MachineState) : StepResult :=
  if isMisalignedAccess s then .trap .misalignedAccess
  else stepResultOfOption (step s)

/-- A misaligned access makes `step` trap (return `none`): the access is in range
    but fails the alignment half of the `isValid*Access` guard. -/
theorem isMisalignedAccess_imp_step_none {s : MachineState}
    (h : isMisalignedAccess s = true) : step s = none := by
  unfold isMisalignedAccess at h
  unfold step
  split at h <;>
    simp_all [isValidDwordAccess, isValidMemAccess, isValidHalfwordAccess,
      Bool.and_eq_true]

/-- **Bridge.** `stepResult` refines `step`: forgetting the trap kind recovers
    `step` exactly. Lets results proved with the misaligned distinction transfer to
    the `step`/`stepN`-based corpus (and vice versa). -/
theorem step_eq_stepResult_toOption (s : MachineState) :
    step s = (stepResult s).toOption := by
  unfold stepResult
  by_cases h : isMisalignedAccess s
  · simp [h, StepResult.toOption, isMisalignedAccess_imp_step_none h]
  · simp [h, stepResultOfOption_toOption]

/-- `stepResult` succeeds exactly when `step` does. -/
theorem stepResult_ok_iff {s s' : MachineState} :
    stepResult s = .ok s' ↔ step s = some s' := by
  rw [step_eq_stepResult_toOption]
  cases hs : stepResult s <;> simp [StepResult.toOption]

/-- step for non-ECALL, non-EBREAK, non-memory instructions. -/
@[simp] theorem step_non_ecall_non_mem {s : MachineState} {i : Instr}
    (hfetch : s.code s.pc = some i) (hne : i ≠ .ECALL) (hnb : i ≠ .EBREAK)
    (hnm : i.isMemAccess = false) :
    step s = some (execInstrBr s i) := by
  unfold step; rw [hfetch]; cases i <;> simp_all [Instr.isMemAccess]

/-- step for a ZisK accelerator call with valid operand blocks. -/
theorem step_csrs {s : MachineState} {csr : BitVec 12} {rs1 : Reg}
    (hfetch : s.code s.pc = some (.CSRS csr rs1))
    (hvalid : s.csrsValid csr rs1 = true) :
    step s = some (execInstrBr s (.CSRS csr rs1)) := by
  unfold step; rw [hfetch]; simp [hvalid]

/-- step for a ZisK accelerator call with an invalid operand block (or an
    unmodeled CSR id): trap. -/
theorem step_csrs_trap {s : MachineState} {csr : BitVec 12} {rs1 : Reg}
    (hfetch : s.code s.pc = some (.CSRS csr rs1))
    (hinvalid : s.csrsValid csr rs1 = false) :
    step s = none := by
  unfold step; rw [hfetch]; simp [hinvalid]

/-- step for LD with valid dword memory access. -/
theorem step_ld {s : MachineState} {rd rs1 : Reg} {offset : BitVec 12}
    (hfetch : s.code s.pc = some (.LD rd rs1 offset))
    (hvalid : isValidDwordAccess (s.getReg rs1 + signExtend12 offset) = true) :
    step s = some (execInstrBr s (.LD rd rs1 offset)) := by
  simp [step, hfetch, isValidDwordAccess, isValidMemAddr, isAligned8, MEM_START, MEM_END] at hvalid ⊢
  omega

/-- step for SD with valid dword memory access. -/
theorem step_sd {s : MachineState} {rs1 rs2 : Reg} {offset : BitVec 12}
    (hfetch : s.code s.pc = some (.SD rs1 rs2 offset))
    (hvalid : isValidDwordAccess (s.getReg rs1 + signExtend12 offset) = true) :
    step s = some (execInstrBr s (.SD rs1 rs2 offset)) := by
  simp [step, hfetch, isValidDwordAccess, isValidMemAddr, isAligned8, MEM_START, MEM_END] at hvalid ⊢
  omega

/-- step for LD with invalid dword memory access (trap). -/
theorem step_ld_trap {s : MachineState} {rd rs1 : Reg} {offset : BitVec 12}
    (hfetch : s.code s.pc = some (.LD rd rs1 offset))
    (hinvalid : isValidDwordAccess (s.getReg rs1 + signExtend12 offset) = false) :
    step s = none := by
  simp [step, hfetch, isValidDwordAccess, isValidMemAddr, isAligned8, MEM_START, MEM_END] at hinvalid ⊢
  omega

/-- step for SD with invalid dword memory access (trap). -/
theorem step_sd_trap {s : MachineState} {rs1 rs2 : Reg} {offset : BitVec 12}
    (hfetch : s.code s.pc = some (.SD rs1 rs2 offset))
    (hinvalid : isValidDwordAccess (s.getReg rs1 + signExtend12 offset) = false) :
    step s = none := by
  simp [step, hfetch, isValidDwordAccess, isValidMemAddr, isAligned8, MEM_START, MEM_END] at hinvalid ⊢
  omega

/-- step for LW with valid memory access. -/
theorem step_lw {s : MachineState} {rd rs1 : Reg} {offset : BitVec 12}
    (hfetch : s.code s.pc = some (.LW rd rs1 offset))
    (hvalid : isValidMemAccess (s.getReg rs1 + signExtend12 offset) = true) :
    step s = some (execInstrBr s (.LW rd rs1 offset)) := by
  simp [step, hfetch, isValidMemAccess, isValidMemAddr, isAligned4, MEM_START, MEM_END] at hvalid ⊢
  omega

/-- step for SW with valid memory access. -/
theorem step_sw {s : MachineState} {rs1 rs2 : Reg} {offset : BitVec 12}
    (hfetch : s.code s.pc = some (.SW rs1 rs2 offset))
    (hvalid : isValidMemAccess (s.getReg rs1 + signExtend12 offset) = true) :
    step s = some (execInstrBr s (.SW rs1 rs2 offset)) := by
  simp [step, hfetch, isValidMemAccess, isValidMemAddr, isAligned4, MEM_START, MEM_END] at hvalid ⊢
  omega

/-- step for LW with invalid memory access (trap). -/
theorem step_lw_trap {s : MachineState} {rd rs1 : Reg} {offset : BitVec 12}
    (hfetch : s.code s.pc = some (.LW rd rs1 offset))
    (hinvalid : isValidMemAccess (s.getReg rs1 + signExtend12 offset) = false) :
    step s = none := by
  simp [step, hfetch, isValidMemAccess, isValidMemAddr, isAligned4, MEM_START, MEM_END] at hinvalid ⊢
  omega

/-- step for SW with invalid memory access (trap). -/
theorem step_sw_trap {s : MachineState} {rs1 rs2 : Reg} {offset : BitVec 12}
    (hfetch : s.code s.pc = some (.SW rs1 rs2 offset))
    (hinvalid : isValidMemAccess (s.getReg rs1 + signExtend12 offset) = false) :
    step s = none := by
  simp [step, hfetch, isValidMemAccess, isValidMemAddr, isAligned4, MEM_START, MEM_END] at hinvalid ⊢
  omega

/-- step for LWU with valid memory access. -/
theorem step_lwu {s : MachineState} {rd rs1 : Reg} {offset : BitVec 12}
    (hfetch : s.code s.pc = some (.LWU rd rs1 offset))
    (hvalid : isValidMemAccess (s.getReg rs1 + signExtend12 offset) = true) :
    step s = some (execInstrBr s (.LWU rd rs1 offset)) := by
  simp [step, hfetch, isValidMemAccess, isValidMemAddr, isAligned4, MEM_START, MEM_END] at hvalid ⊢
  omega

/-- step for LWU with invalid memory access (trap). -/
theorem step_lwu_trap {s : MachineState} {rd rs1 : Reg} {offset : BitVec 12}
    (hfetch : s.code s.pc = some (.LWU rd rs1 offset))
    (hinvalid : isValidMemAccess (s.getReg rs1 + signExtend12 offset) = false) :
    step s = none := by
  simp [step, hfetch, isValidMemAccess, isValidMemAddr, isAligned4, MEM_START, MEM_END] at hinvalid ⊢
  omega

/-- step for LB with valid byte access. -/
theorem step_lb {s : MachineState} {rd rs1 : Reg} {offset : BitVec 12}
    (hfetch : s.code s.pc = some (.LB rd rs1 offset))
    (hvalid : isValidByteAccess (s.getReg rs1 + signExtend12 offset) = true) :
    step s = some (execInstrBr s (.LB rd rs1 offset)) := by
  simp [step, hfetch, isValidByteAccess, isValidMemAddr, MEM_START, MEM_END] at hvalid ⊢
  omega

/-- step for LB with invalid byte access (trap). -/
theorem step_lb_trap {s : MachineState} {rd rs1 : Reg} {offset : BitVec 12}
    (hfetch : s.code s.pc = some (.LB rd rs1 offset))
    (hinvalid : isValidByteAccess (s.getReg rs1 + signExtend12 offset) = false) :
    step s = none := by
  simp [step, hfetch, isValidByteAccess, isValidMemAddr, MEM_START, MEM_END] at hinvalid ⊢
  omega

/-- step for LBU with valid byte access. -/
theorem step_lbu {s : MachineState} {rd rs1 : Reg} {offset : BitVec 12}
    (hfetch : s.code s.pc = some (.LBU rd rs1 offset))
    (hvalid : isValidByteAccess (s.getReg rs1 + signExtend12 offset) = true) :
    step s = some (execInstrBr s (.LBU rd rs1 offset)) := by
  simp [step, hfetch, isValidByteAccess, isValidMemAddr, MEM_START, MEM_END] at hvalid ⊢
  omega

/-- step for LBU with invalid byte access (trap). -/
theorem step_lbu_trap {s : MachineState} {rd rs1 : Reg} {offset : BitVec 12}
    (hfetch : s.code s.pc = some (.LBU rd rs1 offset))
    (hinvalid : isValidByteAccess (s.getReg rs1 + signExtend12 offset) = false) :
    step s = none := by
  simp [step, hfetch, isValidByteAccess, isValidMemAddr, MEM_START, MEM_END] at hinvalid ⊢
  omega

/-- step for LH with valid halfword access. -/
theorem step_lh {s : MachineState} {rd rs1 : Reg} {offset : BitVec 12}
    (hfetch : s.code s.pc = some (.LH rd rs1 offset))
    (hvalid : isValidHalfwordAccess (s.getReg rs1 + signExtend12 offset) = true) :
    step s = some (execInstrBr s (.LH rd rs1 offset)) := by
  simp [step, hfetch, isValidHalfwordAccess, isValidMemAddr, isAligned2, MEM_START, MEM_END] at hvalid ⊢
  omega

/-- step for LH with invalid halfword access (trap). -/
theorem step_lh_trap {s : MachineState} {rd rs1 : Reg} {offset : BitVec 12}
    (hfetch : s.code s.pc = some (.LH rd rs1 offset))
    (hinvalid : isValidHalfwordAccess (s.getReg rs1 + signExtend12 offset) = false) :
    step s = none := by
  simp [step, hfetch, isValidHalfwordAccess, isValidMemAddr, isAligned2, MEM_START, MEM_END] at hinvalid ⊢
  omega

/-- step for LHU with valid halfword access. -/
theorem step_lhu {s : MachineState} {rd rs1 : Reg} {offset : BitVec 12}
    (hfetch : s.code s.pc = some (.LHU rd rs1 offset))
    (hvalid : isValidHalfwordAccess (s.getReg rs1 + signExtend12 offset) = true) :
    step s = some (execInstrBr s (.LHU rd rs1 offset)) := by
  simp [step, hfetch, isValidHalfwordAccess, isValidMemAddr, isAligned2, MEM_START, MEM_END] at hvalid ⊢
  omega

/-- step for LHU with invalid halfword access (trap). -/
theorem step_lhu_trap {s : MachineState} {rd rs1 : Reg} {offset : BitVec 12}
    (hfetch : s.code s.pc = some (.LHU rd rs1 offset))
    (hinvalid : isValidHalfwordAccess (s.getReg rs1 + signExtend12 offset) = false) :
    step s = none := by
  simp [step, hfetch, isValidHalfwordAccess, isValidMemAddr, isAligned2, MEM_START, MEM_END] at hinvalid ⊢
  omega

/-- step for SB with valid byte access. -/
theorem step_sb {s : MachineState} {rs1 rs2 : Reg} {offset : BitVec 12}
    (hfetch : s.code s.pc = some (.SB rs1 rs2 offset))
    (hvalid : isValidByteAccess (s.getReg rs1 + signExtend12 offset) = true) :
    step s = some (execInstrBr s (.SB rs1 rs2 offset)) := by
  simp [step, hfetch, isValidByteAccess, isValidMemAddr, MEM_START, MEM_END] at hvalid ⊢
  omega

/-- step for SB with invalid byte access (trap). -/
theorem step_sb_trap {s : MachineState} {rs1 rs2 : Reg} {offset : BitVec 12}
    (hfetch : s.code s.pc = some (.SB rs1 rs2 offset))
    (hinvalid : isValidByteAccess (s.getReg rs1 + signExtend12 offset) = false) :
    step s = none := by
  simp [step, hfetch, isValidByteAccess, isValidMemAddr, MEM_START, MEM_END] at hinvalid ⊢
  omega

/-- step for SH with valid halfword access. -/
theorem step_sh {s : MachineState} {rs1 rs2 : Reg} {offset : BitVec 12}
    (hfetch : s.code s.pc = some (.SH rs1 rs2 offset))
    (hvalid : isValidHalfwordAccess (s.getReg rs1 + signExtend12 offset) = true) :
    step s = some (execInstrBr s (.SH rs1 rs2 offset)) := by
  simp [step, hfetch, isValidHalfwordAccess, isValidMemAddr, isAligned2, MEM_START, MEM_END] at hvalid ⊢
  omega

/-- step for SH with invalid halfword access (trap). -/
theorem step_sh_trap {s : MachineState} {rs1 rs2 : Reg} {offset : BitVec 12}
    (hfetch : s.code s.pc = some (.SH rs1 rs2 offset))
    (hinvalid : isValidHalfwordAccess (s.getReg rs1 + signExtend12 offset) = false) :
    step s = none := by
  simp [step, hfetch, isValidHalfwordAccess, isValidMemAddr, isAligned2, MEM_START, MEM_END] at hinvalid ⊢
  omega

/-- step for EBREAK (always traps). -/
theorem step_ebreak {s : MachineState}
    (hfetch : s.code s.pc = some .EBREAK) :
    step s = none := by
  simp [step, hfetch]

theorem step_ecall_halt {s : MachineState}
    (hfetch : s.code s.pc = some .ECALL) (ht0 : s.getReg .x5 = 0) :
    step s = none := by
  simp [step, hfetch, ht0]

theorem step_ecall_continue {s : MachineState}
    (hfetch : s.code s.pc = some .ECALL)
    (ht0 : s.getReg .x5 ≠ 0)
    (ht0_nw : s.getReg .x5 ≠ (0x02 : Word))
    (ht0_nwo : s.getReg .x5 ≠ (0x10 : Word))
    (ht0_nri : s.getReg .x5 ≠ (0xF2 : Word)) :
    step s = some (execInstrBr s .ECALL) := by
  simp only [step, hfetch, beq_iff_eq, ht0, ht0_nw, ht0_nwo, ht0_nri, ↓reduceIte]

/-- `write_output` syscall (t0 = 0x10) appends a1 bytes from memory at a0. -/
theorem step_ecall_write_output {s : MachineState}
    (hfetch : s.code s.pc = some .ECALL)
    (ht0 : s.getReg .x5 = BitVec.ofNat 64 0x10) :
    step s =
      some ((s.writeOutput (s.getReg .x10) (s.getReg .x11)).setPC (s.pc + 4)) := by
  simp [step, hfetch, ht0]

@[deprecated step_ecall_write_output (since := "2026-05-08")]
theorem step_ecall_commit {s : MachineState}
    (hfetch : s.code s.pc = some .ECALL)
    (ht0 : s.getReg .x5 = BitVec.ofNat 64 0x10) :
    step s =
      some ((s.writeOutput (s.getReg .x10) (s.getReg .x11)).setPC (s.pc + 4)) :=
  step_ecall_write_output hfetch ht0

/-- WRITE syscall to FD_PUBLIC_VALUES (t0 = 0x02, fd = 13) appends bytes from memory. -/
theorem step_ecall_write_public {s : MachineState}
    (hfetch : s.code s.pc = some .ECALL)
    (ht0 : s.getReg .x5 = BitVec.ofNat 64 0x02)
    (hfd : s.getReg .x10 = 13) :
    step s =
      some ((s.appendPublicValues (s.readBytes (s.getReg .x11) (s.getReg .x12).toNat)).setPC (s.pc + 4)) := by
  simp [step, hfetch, ht0, hfd]

/-- WRITE syscall to non-public-values fd (t0 = 0x02, fd ≠ 13) just advances PC. -/
theorem step_ecall_write_other {s : MachineState}
    (hfetch : s.code s.pc = some .ECALL)
    (ht0 : s.getReg .x5 = BitVec.ofNat 64 0x02)
    (hfd : s.getReg .x10 ≠ (13 : Word)) :
    step s = some (s.setPC (s.pc + 4)) := by
  simp only [step, hfetch, ht0, beq_iff_eq, hfd, ite_false]
  simp (config := { decide := true })

/-- `read_input` syscall (zkvm-standards C ABI, t0 = 0xF2): idempotently writes
    (inputBufBase, privateInput.length) to the out-pointers in a0/a1. -/
theorem step_ecall_read_input {s : MachineState}
    (hfetch : s.code s.pc = some .ECALL)
    (ht0 : s.getReg .x5 = BitVec.ofNat 64 0xF2)
    (hvalid_a0 : isValidDwordAccess (s.getReg .x10) = true)
    (hvalid_a1 : isValidDwordAccess (s.getReg .x11) = true) :
    let s' := s.setMem (s.getReg .x10) s.inputBufBase
    let s'' := s'.setMem (s.getReg .x11) (BitVec.ofNat 64 s.privateInput.length)
    step s = some (s''.setPC (s.pc + 4)) := by
  simp [step, hfetch, ht0, isValidDwordAccess, isValidMemAddr, isAligned8,
    MEM_START, MEM_END] at hvalid_a0 hvalid_a1 ⊢
  omega

/-- `read_input` syscall traps when the first out-pointer is not a valid dword address. -/
theorem step_ecall_read_input_trap_a0 {s : MachineState}
    (hfetch : s.code s.pc = some .ECALL)
    (ht0 : s.getReg .x5 = BitVec.ofNat 64 0xF2)
    (hinvalid : isValidDwordAccess (s.getReg .x10) = false) :
    step s = none := by
  simp [step, hfetch, ht0, isValidDwordAccess, isValidMemAddr, isAligned8,
    MEM_START, MEM_END] at hinvalid ⊢
  omega

/-- Multi-step execution (n steps). -/
def stepN : Nat → MachineState → Option MachineState
  | 0,     s => some s
  | n + 1, s => (step s).bind (stepN n ·)

-- ============================================================================
-- stepN lemmas
-- ============================================================================

@[simp]
theorem stepN_zero {s : MachineState} :
    stepN 0 s = some s := rfl

@[simp]
theorem stepN_succ {s : MachineState} {n : Nat} :
    stepN (n + 1) s = (step s).bind (stepN n ·) := rfl

theorem stepN_one {s : MachineState} :
    stepN 1 s = step s := by
  simp [stepN, Option.bind]
  cases step s <;> simp

/-- Composing step counts: n+m steps = n steps then m steps. -/
theorem stepN_add {n m : Nat} {s : MachineState} :
    stepN (n + m) s = (stepN n s).bind (stepN m ·) := by
  induction n generalizing s with
  | zero => simp [Option.bind]
  | succ k ih =>
    simp only [Nat.succ_add, stepN_succ]
    cases h : step s with
    | none => simp [Option.bind]
    | some s' => simp [Option.bind, ih]

/-- If stepN n succeeds and then stepN m succeeds, stepN (n+m) gives the same result. -/
theorem stepN_add_eq {n m : Nat} {s s' s'' : MachineState}
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
                            | (simp at h; done)
                            | (split at h <;> first
                                | (simp only [Option.some.injEq] at h; rw [← h]; simp)
                                | (simp at h; done)))))))))

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

-- ============================================================================
-- Sanity checks for the trap-aware step result
-- ============================================================================

/-- An aligned, in-range dword access steps successfully (`.ok`). -/
example (s : MachineState) (rd rs1 : Reg) (off : BitVec 12)
    (hcode : s.code s.pc = some (.LD rd rs1 off))
    (hvalid : isValidDwordAccess (s.getReg rs1 + signExtend12 off) = true) :
    stepResult s = .ok (execInstrBr s (.LD rd rs1 off)) := by
  rw [stepResult_ok_iff]; exact step_ld hcode hvalid

/-- An in-range but misaligned dword access surfaces a distinguished
    `.trap .misalignedAccess` — while plain `step` only sees `none`. -/
example (s : MachineState) (rd rs1 : Reg) (off : BitVec 12)
    (hcode : s.code s.pc = some (.LD rd rs1 off))
    (hrange : isValidMemAddr (s.getReg rs1 + signExtend12 off) = true)
    (hmis : isAligned8 (s.getReg rs1 + signExtend12 off) = false) :
    stepResult s = .trap .misalignedAccess ∧ step s = none := by
  have hm : isMisalignedAccess s = true := by
    simp only [isMisalignedAccess, hcode]; rw [hrange, hmis]; decide
  exact ⟨by unfold stepResult; simp [hm], isMisalignedAccess_imp_step_none hm⟩

end EvmAsm.Rv64
