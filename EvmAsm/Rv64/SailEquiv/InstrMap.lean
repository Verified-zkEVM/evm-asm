/-
  EvmAsm.Rv64.SailEquiv.InstrMap

  First bridge from the hand-written `Instr` AST to the SAIL-generated
  RISC-V `instruction` AST.

  Authored by @pirapira; implemented by Codex.
-/

import EvmAsm.Rv64.SailEquiv.StateRel

open LeanRV64D.Functions

namespace EvmAsm.Rv64.SailEquiv

/-- Local alias for the SAIL-generated RISC-V instruction AST. -/
abbrev SailInstr := instruction

/-- SAIL encoding of RV64M `mul`. -/
def sailMulOp : mul_op :=
  { result_part := VectorHalf.Low
    signed_rs1 := Signedness.Signed
    signed_rs2 := Signedness.Signed }

/-- SAIL encoding of RV64M `mulh`. -/
def sailMulhOp : mul_op :=
  { result_part := VectorHalf.High
    signed_rs1 := Signedness.Signed
    signed_rs2 := Signedness.Signed }

/-- SAIL encoding of RV64M `mulhsu`. -/
def sailMulhsuOp : mul_op :=
  { result_part := VectorHalf.High
    signed_rs1 := Signedness.Signed
    signed_rs2 := Signedness.Unsigned }

/-- SAIL encoding of RV64M `mulhu`. -/
def sailMulhuOp : mul_op :=
  { result_part := VectorHalf.High
    signed_rs1 := Signedness.Unsigned
    signed_rs2 := Signedness.Unsigned }

/-- Partial inverse of `regToRegidx` for SAIL register indices. -/
def regidxToReg? : regidx → Option Reg
  | regidx.Regidx 0  => some .x0
  | regidx.Regidx 1  => some .x1
  | regidx.Regidx 2  => some .x2
  | regidx.Regidx 3  => some .x3
  | regidx.Regidx 4  => some .x4
  | regidx.Regidx 5  => some .x5
  | regidx.Regidx 6  => some .x6
  | regidx.Regidx 7  => some .x7
  | regidx.Regidx 8  => some .x8
  | regidx.Regidx 9  => some .x9
  | regidx.Regidx 10 => some .x10
  | regidx.Regidx 11 => some .x11
  | regidx.Regidx 12 => some .x12
  | regidx.Regidx 13 => some .x13
  | regidx.Regidx 14 => some .x14
  | regidx.Regidx 15 => some .x15
  | regidx.Regidx 16 => some .x16
  | regidx.Regidx 17 => some .x17
  | regidx.Regidx 18 => some .x18
  | regidx.Regidx 19 => some .x19
  | regidx.Regidx 20 => some .x20
  | regidx.Regidx 21 => some .x21
  | regidx.Regidx 22 => some .x22
  | regidx.Regidx 23 => some .x23
  | regidx.Regidx 24 => some .x24
  | regidx.Regidx 25 => some .x25
  | regidx.Regidx 26 => some .x26
  | regidx.Regidx 27 => some .x27
  | regidx.Regidx 28 => some .x28
  | regidx.Regidx 29 => some .x29
  | regidx.Regidx 30 => some .x30
  | regidx.Regidx 31 => some .x31
  | _ => none

theorem regidxToReg?_regToRegidx (r : Reg) :
    regidxToReg? (regToRegidx r) = some r := by
  cases r <;> rfl

/-- Map the ALU/immediate subset of the hand-written AST into SAIL. -/
def toSailInstr? : Instr → Option SailInstr
  | .ADD rd rs1 rs2   => some <| instruction.RTYPE (regToRegidx rs2, regToRegidx rs1, regToRegidx rd, rop.ADD)
  | .SUB rd rs1 rs2   => some <| instruction.RTYPE (regToRegidx rs2, regToRegidx rs1, regToRegidx rd, rop.SUB)
  | .SLL rd rs1 rs2   => some <| instruction.RTYPE (regToRegidx rs2, regToRegidx rs1, regToRegidx rd, rop.SLL)
  | .SRL rd rs1 rs2   => some <| instruction.RTYPE (regToRegidx rs2, regToRegidx rs1, regToRegidx rd, rop.SRL)
  | .SRA rd rs1 rs2   => some <| instruction.RTYPE (regToRegidx rs2, regToRegidx rs1, regToRegidx rd, rop.SRA)
  | .AND rd rs1 rs2   => some <| instruction.RTYPE (regToRegidx rs2, regToRegidx rs1, regToRegidx rd, rop.AND)
  | .OR rd rs1 rs2    => some <| instruction.RTYPE (regToRegidx rs2, regToRegidx rs1, regToRegidx rd, rop.OR)
  | .XOR rd rs1 rs2   => some <| instruction.RTYPE (regToRegidx rs2, regToRegidx rs1, regToRegidx rd, rop.XOR)
  | .SLT rd rs1 rs2   => some <| instruction.RTYPE (regToRegidx rs2, regToRegidx rs1, regToRegidx rd, rop.SLT)
  | .SLTU rd rs1 rs2  => some <| instruction.RTYPE (regToRegidx rs2, regToRegidx rs1, regToRegidx rd, rop.SLTU)
  | .ADDI rd rs1 imm  => some <| instruction.ITYPE (imm, regToRegidx rs1, regToRegidx rd, iop.ADDI)
  | .ANDI rd rs1 imm  => some <| instruction.ITYPE (imm, regToRegidx rs1, regToRegidx rd, iop.ANDI)
  | .ORI rd rs1 imm   => some <| instruction.ITYPE (imm, regToRegidx rs1, regToRegidx rd, iop.ORI)
  | .XORI rd rs1 imm  => some <| instruction.ITYPE (imm, regToRegidx rs1, regToRegidx rd, iop.XORI)
  | .SLTI rd rs1 imm  => some <| instruction.ITYPE (imm, regToRegidx rs1, regToRegidx rd, iop.SLTI)
  | .SLTIU rd rs1 imm => some <| instruction.ITYPE (imm, regToRegidx rs1, regToRegidx rd, iop.SLTIU)
  | .SLLI rd rs1 sh   => some <| instruction.SHIFTIOP (sh, regToRegidx rs1, regToRegidx rd, sop.SLLI)
  | .SRLI rd rs1 sh   => some <| instruction.SHIFTIOP (sh, regToRegidx rs1, regToRegidx rd, sop.SRLI)
  | .SRAI rd rs1 sh   => some <| instruction.SHIFTIOP (sh, regToRegidx rs1, regToRegidx rd, sop.SRAI)
  | .BEQ rs1 rs2 off  => some <| instruction.BTYPE (off, regToRegidx rs2, regToRegidx rs1, bop.BEQ)
  | .BNE rs1 rs2 off  => some <| instruction.BTYPE (off, regToRegidx rs2, regToRegidx rs1, bop.BNE)
  | .BLT rs1 rs2 off  => some <| instruction.BTYPE (off, regToRegidx rs2, regToRegidx rs1, bop.BLT)
  | .BGE rs1 rs2 off  => some <| instruction.BTYPE (off, regToRegidx rs2, regToRegidx rs1, bop.BGE)
  | .BLTU rs1 rs2 off => some <| instruction.BTYPE (off, regToRegidx rs2, regToRegidx rs1, bop.BLTU)
  | .BGEU rs1 rs2 off => some <| instruction.BTYPE (off, regToRegidx rs2, regToRegidx rs1, bop.BGEU)
  | .JAL rd off       => some <| instruction.JAL (off, regToRegidx rd)
  | .JALR rd rs1 off  => some <| instruction.JALR (off, regToRegidx rs1, regToRegidx rd)
  | .LD rd rs1 off    => some <| instruction.LOAD (off, regToRegidx rs1, regToRegidx rd, false, 64)
  | .LW rd rs1 off    => some <| instruction.LOAD (off, regToRegidx rs1, regToRegidx rd, false, 32)
  | .LWU rd rs1 off   => some <| instruction.LOAD (off, regToRegidx rs1, regToRegidx rd, true, 32)
  | .LB rd rs1 off    => some <| instruction.LOAD (off, regToRegidx rs1, regToRegidx rd, false, 8)
  | .LBU rd rs1 off   => some <| instruction.LOAD (off, regToRegidx rs1, regToRegidx rd, true, 8)
  | .LH rd rs1 off    => some <| instruction.LOAD (off, regToRegidx rs1, regToRegidx rd, false, 16)
  | .LHU rd rs1 off   => some <| instruction.LOAD (off, regToRegidx rs1, regToRegidx rd, true, 16)
  | .SD rs1 rs2 off   => some <| instruction.STORE (off, regToRegidx rs2, regToRegidx rs1, 64)
  | .SW rs1 rs2 off   => some <| instruction.STORE (off, regToRegidx rs2, regToRegidx rs1, 32)
  | .SB rs1 rs2 off   => some <| instruction.STORE (off, regToRegidx rs2, regToRegidx rs1, 8)
  | .SH rs1 rs2 off   => some <| instruction.STORE (off, regToRegidx rs2, regToRegidx rs1, 16)
  | .MUL rd rs1 rs2   => some <| instruction.MUL (regToRegidx rs2, regToRegidx rs1, regToRegidx rd, sailMulOp)
  | .MULH rd rs1 rs2  => some <| instruction.MUL (regToRegidx rs2, regToRegidx rs1, regToRegidx rd, sailMulhOp)
  | .MULHSU rd rs1 rs2 =>
      some <| instruction.MUL (regToRegidx rs2, regToRegidx rs1, regToRegidx rd, sailMulhsuOp)
  | .MULHU rd rs1 rs2 =>
      some <| instruction.MUL (regToRegidx rs2, regToRegidx rs1, regToRegidx rd, sailMulhuOp)
  | .DIV rd rs1 rs2   => some <| instruction.DIV (regToRegidx rs2, regToRegidx rs1, regToRegidx rd, false)
  | .DIVU rd rs1 rs2  => some <| instruction.DIV (regToRegidx rs2, regToRegidx rs1, regToRegidx rd, true)
  | .REM rd rs1 rs2   => some <| instruction.REM (regToRegidx rs2, regToRegidx rs1, regToRegidx rd, false)
  | .REMU rd rs1 rs2  => some <| instruction.REM (regToRegidx rs2, regToRegidx rs1, regToRegidx rd, true)
  | .LUI rd imm       => some <| instruction.UTYPE (imm, regToRegidx rd, uop.LUI)
  | .AUIPC rd imm     => some <| instruction.UTYPE (imm, regToRegidx rd, uop.AUIPC)
  | .ADDIW rd rs1 imm => some <| instruction.ADDIW (imm, regToRegidx rs1, regToRegidx rd)
  | .ECALL            => some <| instruction.ECALL ()
  | .FENCE            => some <| instruction.FENCE (0, 0, 0, regToRegidx .x0, regToRegidx .x0)
  | .EBREAK           => some <| instruction.EBREAK ()
  | _                 => none

def rtypeToInstr? (rs2 rs1 rd : regidx) : rop → Option Instr
  | rop.ADD  => return .ADD  (← regidxToReg? rd) (← regidxToReg? rs1) (← regidxToReg? rs2)
  | rop.SUB  => return .SUB  (← regidxToReg? rd) (← regidxToReg? rs1) (← regidxToReg? rs2)
  | rop.SLL  => return .SLL  (← regidxToReg? rd) (← regidxToReg? rs1) (← regidxToReg? rs2)
  | rop.SRL  => return .SRL  (← regidxToReg? rd) (← regidxToReg? rs1) (← regidxToReg? rs2)
  | rop.SRA  => return .SRA  (← regidxToReg? rd) (← regidxToReg? rs1) (← regidxToReg? rs2)
  | rop.AND  => return .AND  (← regidxToReg? rd) (← regidxToReg? rs1) (← regidxToReg? rs2)
  | rop.OR   => return .OR   (← regidxToReg? rd) (← regidxToReg? rs1) (← regidxToReg? rs2)
  | rop.XOR  => return .XOR  (← regidxToReg? rd) (← regidxToReg? rs1) (← regidxToReg? rs2)
  | rop.SLT  => return .SLT  (← regidxToReg? rd) (← regidxToReg? rs1) (← regidxToReg? rs2)
  | rop.SLTU => return .SLTU (← regidxToReg? rd) (← regidxToReg? rs1) (← regidxToReg? rs2)

def itypeToInstr? (imm : BitVec 12) (rs1 rd : regidx) : iop → Option Instr
  | iop.ADDI  => return .ADDI  (← regidxToReg? rd) (← regidxToReg? rs1) imm
  | iop.ANDI  => return .ANDI  (← regidxToReg? rd) (← regidxToReg? rs1) imm
  | iop.ORI   => return .ORI   (← regidxToReg? rd) (← regidxToReg? rs1) imm
  | iop.XORI  => return .XORI  (← regidxToReg? rd) (← regidxToReg? rs1) imm
  | iop.SLTI  => return .SLTI  (← regidxToReg? rd) (← regidxToReg? rs1) imm
  | iop.SLTIU => return .SLTIU (← regidxToReg? rd) (← regidxToReg? rs1) imm

def shiftIToInstr? (shamt : BitVec 6) (rs1 rd : regidx) : sop → Option Instr
  | sop.SLLI => return .SLLI (← regidxToReg? rd) (← regidxToReg? rs1) shamt
  | sop.SRLI => return .SRLI (← regidxToReg? rd) (← regidxToReg? rs1) shamt
  | sop.SRAI => return .SRAI (← regidxToReg? rd) (← regidxToReg? rs1) shamt

def btypeToInstr? (off : BitVec 13) (rs2 rs1 : regidx) : bop → Option Instr
  | bop.BEQ  => return .BEQ  (← regidxToReg? rs1) (← regidxToReg? rs2) off
  | bop.BNE  => return .BNE  (← regidxToReg? rs1) (← regidxToReg? rs2) off
  | bop.BLT  => return .BLT  (← regidxToReg? rs1) (← regidxToReg? rs2) off
  | bop.BGE  => return .BGE  (← regidxToReg? rs1) (← regidxToReg? rs2) off
  | bop.BLTU => return .BLTU (← regidxToReg? rs1) (← regidxToReg? rs2) off
  | bop.BGEU => return .BGEU (← regidxToReg? rs1) (← regidxToReg? rs2) off

def loadToInstr? (off : BitVec 12) (rs1 rd : regidx)
    (isUnsigned : Bool) : word_width → Option Instr
  | 8  =>
      if isUnsigned then
        return .LBU (← regidxToReg? rd) (← regidxToReg? rs1) off
      else
        return .LB (← regidxToReg? rd) (← regidxToReg? rs1) off
  | 16 =>
      if isUnsigned then
        return .LHU (← regidxToReg? rd) (← regidxToReg? rs1) off
      else
        return .LH (← regidxToReg? rd) (← regidxToReg? rs1) off
  | 32 =>
      if isUnsigned then
        return .LWU (← regidxToReg? rd) (← regidxToReg? rs1) off
      else
        return .LW (← regidxToReg? rd) (← regidxToReg? rs1) off
  | 64 =>
      if isUnsigned then
        none
      else
        return .LD (← regidxToReg? rd) (← regidxToReg? rs1) off
  | _ => none

def storeToInstr? (off : BitVec 12) (rs2 rs1 : regidx) : word_width → Option Instr
  | 8  => return .SB (← regidxToReg? rs1) (← regidxToReg? rs2) off
  | 16 => return .SH (← regidxToReg? rs1) (← regidxToReg? rs2) off
  | 32 => return .SW (← regidxToReg? rs1) (← regidxToReg? rs2) off
  | 64 => return .SD (← regidxToReg? rs1) (← regidxToReg? rs2) off
  | _ => none

def mulToInstr? (rs2 rs1 rd : regidx) : mul_op → Option Instr
  | { result_part := VectorHalf.Low,
      signed_rs1 := Signedness.Signed,
      signed_rs2 := Signedness.Signed } =>
      return .MUL (← regidxToReg? rd) (← regidxToReg? rs1) (← regidxToReg? rs2)
  | { result_part := VectorHalf.High,
      signed_rs1 := Signedness.Signed,
      signed_rs2 := Signedness.Signed } =>
      return .MULH (← regidxToReg? rd) (← regidxToReg? rs1) (← regidxToReg? rs2)
  | { result_part := VectorHalf.High,
      signed_rs1 := Signedness.Signed,
      signed_rs2 := Signedness.Unsigned } =>
      return .MULHSU (← regidxToReg? rd) (← regidxToReg? rs1) (← regidxToReg? rs2)
  | { result_part := VectorHalf.High,
      signed_rs1 := Signedness.Unsigned,
      signed_rs2 := Signedness.Unsigned } =>
      return .MULHU (← regidxToReg? rd) (← regidxToReg? rs1) (← regidxToReg? rs2)
  | _ => none

def divToInstr? (rs2 rs1 rd : regidx) (isUnsigned : Bool) : Option Instr := do
  if isUnsigned then
    return .DIVU (← regidxToReg? rd) (← regidxToReg? rs1) (← regidxToReg? rs2)
  else
    return .DIV (← regidxToReg? rd) (← regidxToReg? rs1) (← regidxToReg? rs2)

def remToInstr? (rs2 rs1 rd : regidx) (isUnsigned : Bool) : Option Instr := do
  if isUnsigned then
    return .REMU (← regidxToReg? rd) (← regidxToReg? rs1) (← regidxToReg? rs2)
  else
    return .REM (← regidxToReg? rd) (← regidxToReg? rs1) (← regidxToReg? rs2)

def utypeToInstr? (imm : BitVec 20) (rd : regidx) : uop → Option Instr
  | uop.LUI => return .LUI (← regidxToReg? rd) imm
  | uop.AUIPC => return .AUIPC (← regidxToReg? rd) imm

/-- Map the supported SAIL ALU/immediate constructors back to the hand-written AST. -/
def fromSailInstr? : SailInstr → Option Instr
  | instruction.ECALL () => some .ECALL
  | instruction.FENCE _ => some .FENCE
  | instruction.EBREAK () => some .EBREAK
  | instruction.UTYPE (imm, rd, op) => utypeToInstr? imm rd op
  | instruction.JAL (off, rd) => return .JAL (← regidxToReg? rd) off
  | instruction.JALR (off, rs1, rd) => return .JALR (← regidxToReg? rd) (← regidxToReg? rs1) off
  | instruction.BTYPE (off, rs2, rs1, op) => btypeToInstr? off rs2 rs1 op
  | instruction.LOAD (off, rs1, rd, isUnsigned, width) =>
      loadToInstr? off rs1 rd isUnsigned width
  | instruction.STORE (off, rs2, rs1, width) => storeToInstr? off rs2 rs1 width
  | instruction.MUL (rs2, rs1, rd, op) => mulToInstr? rs2 rs1 rd op
  | instruction.DIV (rs2, rs1, rd, isUnsigned) => divToInstr? rs2 rs1 rd isUnsigned
  | instruction.REM (rs2, rs1, rd, isUnsigned) => remToInstr? rs2 rs1 rd isUnsigned
  | instruction.ADDIW (imm, rs1, rd) => return .ADDIW (← regidxToReg? rd) (← regidxToReg? rs1) imm
  | instruction.RTYPE (rs2, rs1, rd, op) => rtypeToInstr? rs2 rs1 rd op
  | instruction.ITYPE (imm, rs1, rd, op) => itypeToInstr? imm rs1 rd op
  | instruction.SHIFTIOP (shamt, rs1, rd, op) => shiftIToInstr? shamt rs1 rd op
  | _ => none

theorem fromSailInstr?_toSailInstr?_of_some
    {i : Instr} {sail : SailInstr} (h : toSailInstr? i = some sail) :
    fromSailInstr? sail = some i := by
  cases i <;> simp [toSailInstr?] at h
  all_goals
    cases h
    simp [fromSailInstr?, rtypeToInstr?, itypeToInstr?, shiftIToInstr?,
      btypeToInstr?, loadToInstr?, storeToInstr?, mulToInstr?, divToInstr?,
      remToInstr?, utypeToInstr?, sailMulOp, sailMulhOp, sailMulhsuOp, sailMulhuOp,
      regidxToReg?_regToRegidx]

theorem fromSailInstr?_toSailInstr?_ADD (rd rs1 rs2 : Reg) :
    fromSailInstr? (instruction.RTYPE
      (regToRegidx rs2, regToRegidx rs1, regToRegidx rd, rop.ADD)) =
    some (.ADD rd rs1 rs2) := by
  simp [fromSailInstr?, rtypeToInstr?, regidxToReg?_regToRegidx]

theorem fromSailInstr?_toSailInstr?_ADDI
    (rd rs1 : Reg) (imm : BitVec 12) :
    fromSailInstr? (instruction.ITYPE
      (imm, regToRegidx rs1, regToRegidx rd, iop.ADDI)) =
    some (.ADDI rd rs1 imm) := by
  simp [fromSailInstr?, itypeToInstr?, regidxToReg?_regToRegidx]

theorem fromSailInstr?_toSailInstr?_SLLI
    (rd rs1 : Reg) (shamt : BitVec 6) :
    fromSailInstr? (instruction.SHIFTIOP
      (shamt, regToRegidx rs1, regToRegidx rd, sop.SLLI)) =
    some (.SLLI rd rs1 shamt) := by
  simp [fromSailInstr?, shiftIToInstr?, regidxToReg?_regToRegidx]

theorem fromSailInstr?_toSailInstr?_BEQ
    (rs1 rs2 : Reg) (off : BitVec 13) :
    fromSailInstr? (instruction.BTYPE
      (off, regToRegidx rs2, regToRegidx rs1, bop.BEQ)) =
    some (.BEQ rs1 rs2 off) := by
  simp [fromSailInstr?, btypeToInstr?, regidxToReg?_regToRegidx]

theorem fromSailInstr?_toSailInstr?_JAL
    (rd : Reg) (off : BitVec 21) :
    fromSailInstr? (instruction.JAL (off, regToRegidx rd)) =
    some (.JAL rd off) := by
  simp [fromSailInstr?, regidxToReg?_regToRegidx]

theorem fromSailInstr?_toSailInstr?_JALR
    (rd rs1 : Reg) (off : BitVec 12) :
    fromSailInstr? (instruction.JALR
      (off, regToRegidx rs1, regToRegidx rd)) =
    some (.JALR rd rs1 off) := by
  simp [fromSailInstr?, regidxToReg?_regToRegidx]

theorem fromSailInstr?_toSailInstr?_LD
    (rd rs1 : Reg) (off : BitVec 12) :
    fromSailInstr? (instruction.LOAD
      (off, regToRegidx rs1, regToRegidx rd, false, 64)) =
    some (.LD rd rs1 off) := by
  simp [fromSailInstr?, loadToInstr?, regidxToReg?_regToRegidx]

theorem fromSailInstr?_toSailInstr?_LBU
    (rd rs1 : Reg) (off : BitVec 12) :
    fromSailInstr? (instruction.LOAD
      (off, regToRegidx rs1, regToRegidx rd, true, 8)) =
    some (.LBU rd rs1 off) := by
  simp [fromSailInstr?, loadToInstr?, regidxToReg?_regToRegidx]

theorem fromSailInstr?_toSailInstr?_SD
    (rs1 rs2 : Reg) (off : BitVec 12) :
    fromSailInstr? (instruction.STORE
      (off, regToRegidx rs2, regToRegidx rs1, 64)) =
    some (.SD rs1 rs2 off) := by
  simp [fromSailInstr?, storeToInstr?, regidxToReg?_regToRegidx]

theorem fromSailInstr?_toSailInstr?_SB
    (rs1 rs2 : Reg) (off : BitVec 12) :
    fromSailInstr? (instruction.STORE
      (off, regToRegidx rs2, regToRegidx rs1, 8)) =
    some (.SB rs1 rs2 off) := by
  simp [fromSailInstr?, storeToInstr?, regidxToReg?_regToRegidx]

theorem fromSailInstr?_toSailInstr?_MUL
    (rd rs1 rs2 : Reg) :
    fromSailInstr? (instruction.MUL
      (regToRegidx rs2, regToRegidx rs1, regToRegidx rd, sailMulOp)) =
    some (.MUL rd rs1 rs2) := by
  simp [fromSailInstr?, mulToInstr?, sailMulOp, regidxToReg?_regToRegidx]

theorem fromSailInstr?_toSailInstr?_MULHU
    (rd rs1 rs2 : Reg) :
    fromSailInstr? (instruction.MUL
      (regToRegidx rs2, regToRegidx rs1, regToRegidx rd, sailMulhuOp)) =
    some (.MULHU rd rs1 rs2) := by
  simp [fromSailInstr?, mulToInstr?, sailMulhuOp, regidxToReg?_regToRegidx]

theorem fromSailInstr?_toSailInstr?_DIVU
    (rd rs1 rs2 : Reg) :
    fromSailInstr? (instruction.DIV
      (regToRegidx rs2, regToRegidx rs1, regToRegidx rd, true)) =
    some (.DIVU rd rs1 rs2) := by
  simp [fromSailInstr?, divToInstr?, regidxToReg?_regToRegidx]

theorem fromSailInstr?_toSailInstr?_REMU
    (rd rs1 rs2 : Reg) :
    fromSailInstr? (instruction.REM
      (regToRegidx rs2, regToRegidx rs1, regToRegidx rd, true)) =
    some (.REMU rd rs1 rs2) := by
  simp [fromSailInstr?, remToInstr?, regidxToReg?_regToRegidx]

theorem fromSailInstr?_toSailInstr?_LUI
    (rd : Reg) (imm : BitVec 20) :
    fromSailInstr? (instruction.UTYPE (imm, regToRegidx rd, uop.LUI)) =
    some (.LUI rd imm) := by
  simp [fromSailInstr?, utypeToInstr?, regidxToReg?_regToRegidx]

theorem fromSailInstr?_toSailInstr?_AUIPC
    (rd : Reg) (imm : BitVec 20) :
    fromSailInstr? (instruction.UTYPE (imm, regToRegidx rd, uop.AUIPC)) =
    some (.AUIPC rd imm) := by
  simp [fromSailInstr?, utypeToInstr?, regidxToReg?_regToRegidx]

theorem fromSailInstr?_toSailInstr?_ADDIW
    (rd rs1 : Reg) (imm : BitVec 12) :
    fromSailInstr? (instruction.ADDIW (imm, regToRegidx rs1, regToRegidx rd)) =
    some (.ADDIW rd rs1 imm) := by
  simp [fromSailInstr?, regidxToReg?_regToRegidx]

theorem fromSailInstr?_toSailInstr?_ECALL :
    fromSailInstr? (instruction.ECALL ()) = some .ECALL := by
  simp [fromSailInstr?]

theorem fromSailInstr?_toSailInstr?_FENCE :
    fromSailInstr? (instruction.FENCE (0, 0, 0, regToRegidx .x0, regToRegidx .x0)) =
    some .FENCE := by
  simp [fromSailInstr?]

theorem fromSailInstr?_toSailInstr?_EBREAK :
    fromSailInstr? (instruction.EBREAK ()) = some .EBREAK := by
  simp [fromSailInstr?]

end EvmAsm.Rv64.SailEquiv
