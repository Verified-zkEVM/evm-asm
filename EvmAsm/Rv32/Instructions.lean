/-
  EvmAsm.Rv32.Instructions

  RISC-V instruction definitions and their semantics.
  We model the full RV32IM instruction set (base + M extension).
-/

import EvmAsm.Rv32.Basic

namespace EvmAsm

-- ============================================================================
-- Instruction classification
-- ============================================================================

/-- Is this instruction a branch or jump? -/
def Instr.isBranch : Instr → Bool
  | .BEQ _ _ _  => true
  | .BNE _ _ _  => true
  | .BLT _ _ _  => true
  | .BGE _ _ _  => true
  | .BLTU _ _ _ => true
  | .BGEU _ _ _ => true
  | .JAL _ _    => true
  | .JALR _ _ _ => true
  | _           => false

/-- Is this instruction a memory access? -/
def Instr.isMemAccess : Instr → Bool
  | .LW _ _ _   => true
  | .SW _ _ _   => true
  | .LB _ _ _   => true
  | .LH _ _ _   => true
  | .LBU _ _ _  => true
  | .LHU _ _ _  => true
  | .SB _ _ _   => true
  | .SH _ _ _   => true
  | _           => false

-- ============================================================================
-- Sign extension helpers
-- ============================================================================

/-- Sign-extend a 12-bit immediate to 32 bits. -/
def signExtend12 (imm : BitVec 12) : Word :=
  imm.signExtend 32

/-- Sign-extend a 13-bit branch offset to 32 bits. -/
def signExtend13 (imm : BitVec 13) : Word :=
  imm.signExtend 32

/-- Sign-extend a 21-bit jump offset to 32 bits. -/
def signExtend21 (imm : BitVec 21) : Word :=
  imm.signExtend 32

-- signExtend12 simplification lemmas for concrete offsets used by EVM opcode specs.
@[simp] theorem signExtend12_0  : signExtend12 (0  : BitVec 12) = (0  : Word) := by native_decide
@[simp] theorem signExtend12_4  : signExtend12 (4  : BitVec 12) = (4  : Word) := by native_decide
@[simp] theorem signExtend12_8  : signExtend12 (8  : BitVec 12) = (8  : Word) := by native_decide
@[simp] theorem signExtend12_12 : signExtend12 (12 : BitVec 12) = (12 : Word) := by native_decide
@[simp] theorem signExtend12_16 : signExtend12 (16 : BitVec 12) = (16 : Word) := by native_decide
@[simp] theorem signExtend12_20 : signExtend12 (20 : BitVec 12) = (20 : Word) := by native_decide
@[simp] theorem signExtend12_24 : signExtend12 (24 : BitVec 12) = (24 : Word) := by native_decide
@[simp] theorem signExtend12_28 : signExtend12 (28 : BitVec 12) = (28 : Word) := by native_decide
@[simp] theorem signExtend12_32 : signExtend12 (32 : BitVec 12) = (32 : Word) := by native_decide
@[simp] theorem signExtend12_36 : signExtend12 (36 : BitVec 12) = (36 : Word) := by native_decide
@[simp] theorem signExtend12_40 : signExtend12 (40 : BitVec 12) = (40 : Word) := by native_decide
@[simp] theorem signExtend12_44 : signExtend12 (44 : BitVec 12) = (44 : Word) := by native_decide
@[simp] theorem signExtend12_48 : signExtend12 (48 : BitVec 12) = (48 : Word) := by native_decide
@[simp] theorem signExtend12_52 : signExtend12 (52 : BitVec 12) = (52 : Word) := by native_decide
@[simp] theorem signExtend12_56 : signExtend12 (56 : BitVec 12) = (56 : Word) := by native_decide
@[simp] theorem signExtend12_60 : signExtend12 (60 : BitVec 12) = (60 : Word) := by native_decide
@[simp] theorem signExtend12_1  : signExtend12 (1  : BitVec 12) = (1  : Word) := by native_decide
@[simp] theorem signExtend12_2  : signExtend12 (2  : BitVec 12) = (2  : Word) := by native_decide
@[simp] theorem signExtend12_3  : signExtend12 (3  : BitVec 12) = (3  : Word) := by native_decide
@[simp] theorem signExtend12_5  : signExtend12 (5  : BitVec 12) = (5  : Word) := by native_decide
@[simp] theorem signExtend12_6  : signExtend12 (6  : BitVec 12) = (6  : Word) := by native_decide

-- ============================================================================
-- M-extension helper functions (division/multiply edge cases per RV32IM spec)
-- ============================================================================

/-- RV32IM signed division with spec-mandated edge cases:
    - Division by zero returns -1 (all ones)
    - Overflow (-2^31 / -1) returns -2^31 -/
def rv32_div (a b : Word) : Word :=
  if b == 0#32 then
    (BitVec.ofNat 32 0xFFFFFFFF)  -- -1
  else
    BitVec.sdiv a b  -- handles overflow correctly

/-- RV32IM unsigned division: division by zero returns 2^32-1. -/
def rv32_divu (a b : Word) : Word :=
  if b == 0#32 then
    (BitVec.ofNat 32 0xFFFFFFFF)  -- 2^32 - 1
  else
    a / b

/-- RV32IM signed remainder with spec-mandated edge cases:
    - Division by zero returns the dividend
    - Overflow (-2^31 % -1) returns 0 -/
def rv32_rem (a b : Word) : Word :=
  if b == 0#32 then
    a
  else
    BitVec.srem a b  -- handles overflow correctly (returns 0)

/-- RV32IM unsigned remainder: division by zero returns the dividend. -/
def rv32_remu (a b : Word) : Word :=
  if b == 0#32 then
    a
  else
    a % b

/-- MULH: signed × signed, upper 32 bits. -/
def rv32_mulh (a b : Word) : Word :=
  let a64 : BitVec 64 := a.signExtend 64
  let b64 : BitVec 64 := b.signExtend 64
  (a64 * b64 >>> 32).truncate 32

/-- MULHSU: signed × unsigned, upper 32 bits. -/
def rv32_mulhsu (a b : Word) : Word :=
  let a64 : BitVec 64 := a.signExtend 64
  let b64 : BitVec 64 := b.zeroExtend 64
  (a64 * b64 >>> 32).truncate 32

/-- MULHU: unsigned × unsigned, upper 32 bits. -/
def rv32_mulhu (a b : Word) : Word :=
  let a64 : BitVec 64 := a.zeroExtend 64
  let b64 : BitVec 64 := b.zeroExtend 64
  (a64 * b64 >>> 32).truncate 32

-- ============================================================================
-- Instruction Semantics
-- ============================================================================

/-- Execute a single instruction, returning the new state.
    The PC is advanced by 4 (one instruction width).
    Branch/jump instructions are treated as NOP in list-based execution;
    for proper branch semantics, use execInstrBr + step-based execution. -/
def execInstr (s : MachineState) (i : Instr) : MachineState :=
  let s' := match i with
    | .ADD rd rs1 rs2 =>
        s.setReg rd (s.getReg rs1 + s.getReg rs2)
    | .ADDI rd rs1 imm =>
        s.setReg rd (s.getReg rs1 + signExtend12 imm)
    | .SUB rd rs1 rs2 =>
        s.setReg rd (s.getReg rs1 - s.getReg rs2)
    | .SLL rd rs1 rs2 =>
        let shamt := (s.getReg rs2).toNat % 32
        s.setReg rd (s.getReg rs1 <<< shamt)
    | .SLLI rd rs1 shamt =>
        s.setReg rd (s.getReg rs1 <<< shamt.toNat)
    | .SRL rd rs1 rs2 =>
        let shamt := (s.getReg rs2).toNat % 32
        s.setReg rd (s.getReg rs1 >>> shamt)
    | .SRA rd rs1 rs2 =>
        let shamt := (s.getReg rs2).toNat % 32
        s.setReg rd (BitVec.sshiftRight (s.getReg rs1) shamt)
    | .AND rd rs1 rs2 =>
        s.setReg rd (s.getReg rs1 &&& s.getReg rs2)
    | .ANDI rd rs1 imm =>
        s.setReg rd (s.getReg rs1 &&& signExtend12 imm)
    | .OR rd rs1 rs2 =>
        s.setReg rd (s.getReg rs1 ||| s.getReg rs2)
    | .ORI rd rs1 imm =>
        s.setReg rd (s.getReg rs1 ||| signExtend12 imm)
    | .XOR rd rs1 rs2 =>
        s.setReg rd (s.getReg rs1 ^^^ s.getReg rs2)
    | .XORI rd rs1 imm =>
        s.setReg rd (s.getReg rs1 ^^^ signExtend12 imm)
    | .SLT rd rs1 rs2 =>
        s.setReg rd (if BitVec.slt (s.getReg rs1) (s.getReg rs2) then 1 else 0)
    | .SLTU rd rs1 rs2 =>
        s.setReg rd (if BitVec.ult (s.getReg rs1) (s.getReg rs2) then 1 else 0)
    | .SLTI rd rs1 imm =>
        s.setReg rd (if BitVec.slt (s.getReg rs1) (signExtend12 imm) then 1 else 0)
    | .SLTIU rd rs1 imm =>
        s.setReg rd (if BitVec.ult (s.getReg rs1) (signExtend12 imm) then 1 else 0)
    | .SRLI rd rs1 shamt =>
        s.setReg rd (s.getReg rs1 >>> shamt.toNat)
    | .SRAI rd rs1 shamt =>
        s.setReg rd (BitVec.sshiftRight (s.getReg rs1) shamt.toNat)
    | .LW rd rs1 offset =>
        let addr := s.getReg rs1 + signExtend12 offset
        s.setReg rd (s.getMem addr)
    | .SW rs1 rs2 offset =>
        let addr := s.getReg rs1 + signExtend12 offset
        s.setMem addr (s.getReg rs2)
    | .LB rd rs1 offset =>
        let addr := s.getReg rs1 + signExtend12 offset
        s.setReg rd ((s.getByte addr).signExtend 32)
    | .LH rd rs1 offset =>
        let addr := s.getReg rs1 + signExtend12 offset
        s.setReg rd ((s.getHalfword addr).signExtend 32)
    | .LBU rd rs1 offset =>
        let addr := s.getReg rs1 + signExtend12 offset
        s.setReg rd ((s.getByte addr).zeroExtend 32)
    | .LHU rd rs1 offset =>
        let addr := s.getReg rs1 + signExtend12 offset
        s.setReg rd ((s.getHalfword addr).zeroExtend 32)
    | .SB rs1 rs2 offset =>
        let addr := s.getReg rs1 + signExtend12 offset
        s.setByte addr ((s.getReg rs2).truncate 8)
    | .SH rs1 rs2 offset =>
        let addr := s.getReg rs1 + signExtend12 offset
        s.setHalfword addr ((s.getReg rs2).truncate 16)
    | .LUI rd imm =>
        let val : Word := imm.zeroExtend 32 <<< 12
        s.setReg rd val
    | .AUIPC rd imm =>
        let val : Word := s.pc + (imm.zeroExtend 32 <<< 12)
        s.setReg rd val
    | .MV rd rs =>
        s.setReg rd (s.getReg rs)
    | .LI rd imm =>
        s.setReg rd imm
    | .NOP => s
    | .FENCE => s  -- NOP in single-hart zkVM
    | .EBREAK => s  -- NOP in list-based execution
    -- M extension
    | .MUL rd rs1 rs2 =>
        s.setReg rd (s.getReg rs1 * s.getReg rs2)
    | .MULH rd rs1 rs2 =>
        s.setReg rd (rv32_mulh (s.getReg rs1) (s.getReg rs2))
    | .MULHSU rd rs1 rs2 =>
        s.setReg rd (rv32_mulhsu (s.getReg rs1) (s.getReg rs2))
    | .MULHU rd rs1 rs2 =>
        s.setReg rd (rv32_mulhu (s.getReg rs1) (s.getReg rs2))
    | .DIV rd rs1 rs2 =>
        s.setReg rd (rv32_div (s.getReg rs1) (s.getReg rs2))
    | .DIVU rd rs1 rs2 =>
        s.setReg rd (rv32_divu (s.getReg rs1) (s.getReg rs2))
    | .REM rd rs1 rs2 =>
        s.setReg rd (rv32_rem (s.getReg rs1) (s.getReg rs2))
    | .REMU rd rs1 rs2 =>
        s.setReg rd (rv32_remu (s.getReg rs1) (s.getReg rs2))
    -- Branch/jump instructions are treated as NOP in list-based execution.
    | .BEQ _ _ _ | .BNE _ _ _ | .BLT _ _ _ | .BGE _ _ _
    | .BLTU _ _ _ | .BGEU _ _ _ | .JAL _ _ | .JALR _ _ _ | .ECALL => s
  s'.setPC (s'.pc + 4#32)

end EvmAsm
