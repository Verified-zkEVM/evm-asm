/-
  EvmAsm.Rv64.Program

  Programs as sequences of instructions, with sequential composition.
  64-bit variant of EvmAsm.Program.
-/

import EvmAsm.Rv64.Instructions

namespace EvmAsm.Rv64

-- ============================================================================
-- Programs
-- ============================================================================

/-- A program is a list of instructions. -/
def Program := List Instr

instance : Append Program := ⟨List.append⟩

@[simp] theorem Program.length_append {p q : Program} : (p ++ q).length = p.length + q.length :=
  List.length_append (as := p) (bs := q)

@[simp] theorem Program.getElem?_append (p q : Program) (i : Nat) :
    @getElem? (List Instr) Nat Instr _ _ (p ++ q) i =
    if i < p.length then @getElem? (List Instr) Nat Instr _ _ p i
    else @getElem? (List Instr) Nat Instr _ _ q (i - p.length) :=
  List.getElem?_append

def prog_skip : Program := []

def single (i : Instr) : Program := [i]

def seq (p1 p2 : Program) : Program := p1 ++ p2

infixr:50 " ;; " => seq

-- ============================================================================
-- Program Execution
-- ============================================================================

def execProgram (s : MachineState) : Program → MachineState
  | []      => s
  | i :: is => execProgram (execInstr s i) is

@[simp] theorem execProgram_nil {s : MachineState} :
    execProgram s [] = s := rfl

@[simp] theorem execProgram_cons {s : MachineState} {i : Instr} {is : List Instr} :
    execProgram s (i :: is) = execProgram (execInstr s i) is := rfl

theorem execProgram_append (s : MachineState) (p1 p2 : Program) :
    execProgram s (p1 ++ p2) = execProgram (execProgram s p1) p2 := by
  induction p1 generalizing s with
  | nil => rfl
  | cons i is ih =>
    simp only [execProgram]
    exact ih (execInstr s i)

theorem execProgram_seq (s : MachineState) (p1 p2 : Program) :
    execProgram s (p1 ;; p2) = execProgram (execProgram s p1) p2 :=
  execProgram_append s p1 p2

-- ============================================================================
-- Convenience constructors (macro-assembler style)
-- ============================================================================

def ADD  (rd rs1 rs2 : Reg)                 : Program := single (.ADD rd rs1 rs2)
def ADDI (rd rs1 : Reg) (imm : BitVec 12)   : Program := single (.ADDI rd rs1 imm)
def ADDIW (rd rs1 : Reg) (imm : BitVec 12)  : Program := single (.ADDIW rd rs1 imm)
def SUB  (rd rs1 rs2 : Reg)                 : Program := single (.SUB rd rs1 rs2)
def SLL  (rd rs1 rs2 : Reg)                 : Program := single (.SLL rd rs1 rs2)
def SLLI (rd rs1 : Reg) (shamt : BitVec 6)  : Program := single (.SLLI rd rs1 shamt)
def SRL  (rd rs1 rs2 : Reg)                 : Program := single (.SRL rd rs1 rs2)
def AND' (rd rs1 rs2 : Reg)                 : Program := single (.AND rd rs1 rs2)
def ANDI (rd rs1 : Reg) (imm : BitVec 12)   : Program := single (.ANDI rd rs1 imm)
def OR'  (rd rs1 rs2 : Reg)                 : Program := single (.OR rd rs1 rs2)
def LD   (rd rs1 : Reg) (offset : BitVec 12): Program := single (.LD rd rs1 offset)
def SD   (rs1 rs2 : Reg) (offset : BitVec 12): Program := single (.SD rs1 rs2 offset)
def LW   (rd rs1 : Reg) (offset : BitVec 12): Program := single (.LW rd rs1 offset)
def LWU  (rd rs1 : Reg) (offset : BitVec 12): Program := single (.LWU rd rs1 offset)
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
def SRLI (rd rs1 : Reg) (shamt : BitVec 6)  : Program := single (.SRLI rd rs1 shamt)
def SRAI (rd rs1 : Reg) (shamt : BitVec 6)  : Program := single (.SRAI rd rs1 shamt)
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

/-- HALT macro: set t0 := 0 (HALT syscall), a0 := exit code, then ecall. -/
def HALT (exitCode : Word := 0) : Program :=
  LI .x5 0 ;;
  LI .x10 exitCode ;;
  single .ECALL

end EvmAsm.Rv64
