/-
  EvmAsm.Rv32.Program

  Programs as sequences of instructions, with sequential composition.
  This is the "macro assembler" part: programs are Lean definitions that
  produce instruction sequences, allowing us to use Lean as a macro language.
-/

import EvmAsm.Rv32.Instructions

namespace EvmAsm

-- ============================================================================
-- Programs
-- ============================================================================

/-- A program is a list of instructions. -/
def Program := List Instr

instance : Append Program := ⟨List.append⟩

/-- Length of concatenated programs. -/
@[simp] theorem Program.length_append (p q : Program) : (p ++ q).length = p.length + q.length :=
  List.length_append (as := p) (bs := q)

/-- Element access across concatenated programs. -/
@[simp] theorem Program.getElem?_append (p q : Program) (i : Nat) :
    @getElem? (List Instr) Nat Instr _ _ (p ++ q) i =
    if i < p.length then @getElem? (List Instr) Nat Instr _ _ p i
    else @getElem? (List Instr) Nat Instr _ _ q (i - p.length) :=
  List.getElem?_append

/-- The empty program (no instructions). -/
def prog_skip : Program := []

/-- A single instruction as a program. -/
def single (i : Instr) : Program := [i]

/-- Sequential composition of programs. -/
def seq (p1 p2 : Program) : Program := p1 ++ p2

/-- Notation for sequential composition: p1 ;; p2 -/
infixr:50 " ;; " => seq

-- ============================================================================
-- Program Execution
-- ============================================================================

/-- Execute a program (list of instructions) sequentially. -/
def execProgram (s : MachineState) : Program → MachineState
  | []      => s
  | i :: is => execProgram (execInstr s i) is

/-- Executing the empty program is the identity. -/
@[simp]
theorem execProgram_nil (s : MachineState) :
    execProgram s [] = s := rfl

/-- Executing a single instruction. -/
@[simp]
theorem execProgram_cons (s : MachineState) (i : Instr) (is : List Instr) :
    execProgram s (i :: is) = execProgram (execInstr s i) is := rfl

/-- Sequential composition of programs composes execution. -/
theorem execProgram_append (s : MachineState) (p1 p2 : Program) :
    execProgram s (p1 ++ p2) = execProgram (execProgram s p1) p2 := by
  induction p1 generalizing s with
  | nil => rfl
  | cons i is ih =>
    simp only [execProgram]
    exact ih (execInstr s i)

/-- Sequential composition (;;) composes execution. -/
theorem execProgram_seq (s : MachineState) (p1 p2 : Program) :
    execProgram s (p1 ;; p2) = execProgram (execProgram s p1) p2 :=
  execProgram_append s p1 p2

-- ============================================================================
-- Convenience constructors (macro-assembler style)
-- ============================================================================

/-- Wrap a single instruction into a program. -/
def ADD  (rd rs1 rs2 : Reg)                 : Program := single (.ADD rd rs1 rs2)
def ADDI (rd rs1 : Reg) (imm : BitVec 12)   : Program := single (.ADDI rd rs1 imm)
def SUB  (rd rs1 rs2 : Reg)                 : Program := single (.SUB rd rs1 rs2)
def SLL  (rd rs1 rs2 : Reg)                 : Program := single (.SLL rd rs1 rs2)
def SLLI (rd rs1 : Reg) (shamt : BitVec 5)  : Program := single (.SLLI rd rs1 shamt)
def SRL  (rd rs1 rs2 : Reg)                 : Program := single (.SRL rd rs1 rs2)
def AND' (rd rs1 rs2 : Reg)                 : Program := single (.AND rd rs1 rs2)
def ANDI (rd rs1 : Reg) (imm : BitVec 12)   : Program := single (.ANDI rd rs1 imm)
def OR'  (rd rs1 rs2 : Reg)                 : Program := single (.OR rd rs1 rs2)
def LW   (rd rs1 : Reg) (offset : BitVec 12): Program := single (.LW rd rs1 offset)
def SW   (rs1 rs2 : Reg) (offset : BitVec 12): Program := single (.SW rs1 rs2 offset)
def LUI  (rd : Reg) (imm : BitVec 20)       : Program := single (.LUI rd imm)
def MV   (rd rs : Reg)                      : Program := single (.MV rd rs)
def LI   (rd : Reg) (imm : Word)            : Program := single (.LI rd imm)
def NOP                                     : Program := single .NOP
def SRA  (rd rs1 rs2 : Reg)                 : Program := single (.SRA rd rs1 rs2)
def XOR' (rd rs1 rs2 : Reg)                 : Program := single (.XOR rd rs1 rs2)
def SLT  (rd rs1 rs2 : Reg)                 : Program := single (.SLT rd rs1 rs2)
def SLTU (rd rs1 rs2 : Reg)                 : Program := single (.SLTU rd rs1 rs2)
def ORI  (rd rs1 : Reg) (imm : BitVec 12)   : Program := single (.ORI rd rs1 imm)
def XORI (rd rs1 : Reg) (imm : BitVec 12)   : Program := single (.XORI rd rs1 imm)
def SLTI (rd rs1 : Reg) (imm : BitVec 12)   : Program := single (.SLTI rd rs1 imm)
def SLTIU (rd rs1 : Reg) (imm : BitVec 12)  : Program := single (.SLTIU rd rs1 imm)
def SRLI (rd rs1 : Reg) (shamt : BitVec 5)  : Program := single (.SRLI rd rs1 shamt)
def SRAI (rd rs1 : Reg) (shamt : BitVec 5)  : Program := single (.SRAI rd rs1 shamt)
def AUIPC (rd : Reg) (imm : BitVec 20)      : Program := single (.AUIPC rd imm)
def LB   (rd rs1 : Reg) (offset : BitVec 12): Program := single (.LB rd rs1 offset)
def LH   (rd rs1 : Reg) (offset : BitVec 12): Program := single (.LH rd rs1 offset)
def LBU  (rd rs1 : Reg) (offset : BitVec 12): Program := single (.LBU rd rs1 offset)
def LHU  (rd rs1 : Reg) (offset : BitVec 12): Program := single (.LHU rd rs1 offset)
def SB   (rs1 rs2 : Reg) (offset : BitVec 12): Program := single (.SB rs1 rs2 offset)
def SH   (rs1 rs2 : Reg) (offset : BitVec 12): Program := single (.SH rs1 rs2 offset)
def BEQ  (rs1 rs2 : Reg) (offset : BitVec 13): Program := single (.BEQ rs1 rs2 offset)
def BNE  (rs1 rs2 : Reg) (offset : BitVec 13): Program := single (.BNE rs1 rs2 offset)
def BLT  (rs1 rs2 : Reg) (offset : BitVec 13): Program := single (.BLT rs1 rs2 offset)
def BGE  (rs1 rs2 : Reg) (offset : BitVec 13): Program := single (.BGE rs1 rs2 offset)
def BLTU (rs1 rs2 : Reg) (offset : BitVec 13): Program := single (.BLTU rs1 rs2 offset)
def BGEU (rs1 rs2 : Reg) (offset : BitVec 13): Program := single (.BGEU rs1 rs2 offset)
def JAL  (rd : Reg) (offset : BitVec 21)    : Program := single (.JAL rd offset)
def JALR (rd rs1 : Reg) (offset : BitVec 12): Program := single (.JALR rd rs1 offset)
def ECALL                                   : Program := single .ECALL
def FENCE                                   : Program := single .FENCE
def EBREAK                                  : Program := single .EBREAK
def MUL' (rd rs1 rs2 : Reg)                 : Program := single (.MUL rd rs1 rs2)
def MULH (rd rs1 rs2 : Reg)                 : Program := single (.MULH rd rs1 rs2)
def MULHSU (rd rs1 rs2 : Reg)               : Program := single (.MULHSU rd rs1 rs2)
def MULHU (rd rs1 rs2 : Reg)                : Program := single (.MULHU rd rs1 rs2)
def DIV' (rd rs1 rs2 : Reg)                 : Program := single (.DIV rd rs1 rs2)
def DIVU (rd rs1 rs2 : Reg)                 : Program := single (.DIVU rd rs1 rs2)
def REM' (rd rs1 rs2 : Reg)                 : Program := single (.REM rd rs1 rs2)
def REMU (rd rs1 rs2 : Reg)                 : Program := single (.REMU rd rs1 rs2)

/-- HALT macro (SP1 convention): set t0 := 0 (HALT syscall), a0 := exit code, then ecall. -/
def HALT (exitCode : Word := 0) : Program :=
  LI .x5 0 ;;
  LI .x10 exitCode ;;
  single .ECALL

/-- COMMIT macro (SP1 convention): set t0 := 0x10 (COMMIT syscall),
    a0/a1 for data, then ecall. Execution continues after commit. -/
def COMMIT (a0val a1val : Word) : Program :=
  LI .x5 0x10 ;;
  LI .x10 a0val ;;
  LI .x11 a1val ;;
  single .ECALL

/-- WRITE macro (SP1 convention): set t0 := 0x02 (WRITE syscall),
    a0 := fd, a1 := buffer pointer, a2 := nbytes, then ecall. -/
def WRITE (fd bufPtr nbytes : Word) : Program :=
  LI .x5 0x02 ;;
  LI .x10 fd ;;
  LI .x11 bufPtr ;;
  LI .x12 nbytes ;;
  single .ECALL

/-- HINT_LEN macro (SP1 convention): set t0 := 0xF0 (HINT_LEN syscall),
    then ecall. Returns byte length of available input in a0. -/
def HINT_LEN : Program :=
  LI .x5 0xF0 ;;
  single .ECALL

/-- HINT_READ macro (SP1 convention): set t0 := 0xF1 (HINT_READ syscall),
    a0 := destination address, a1 := nbytes, then ecall. -/
def HINT_READ (addr nbytes : Word) : Program :=
  LI .x5 0xF1 ;;
  LI .x10 addr ;;
  LI .x11 nbytes ;;
  single .ECALL

end EvmAsm
