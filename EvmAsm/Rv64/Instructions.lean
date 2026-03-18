/-
  EvmAsm.Rv64.Instructions

  RISC-V 64-bit instruction definitions and their semantics (RV64IM).
-/

import EvmAsm.Rv64.Basic

namespace EvmAsm.Rv64

-- ============================================================================
-- Instruction classification
-- ============================================================================

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

def Instr.isMemAccess : Instr → Bool
  | .LD _ _ _   => true
  | .SD _ _ _   => true
  | .LW _ _ _   => true
  | .LWU _ _ _  => true
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

/-- Sign-extend a 12-bit immediate to 64 bits. -/
def signExtend12 (imm : BitVec 12) : Word :=
  imm.signExtend 64

/-- Sign-extend a 13-bit branch offset to 64 bits. -/
def signExtend13 (imm : BitVec 13) : Word :=
  imm.signExtend 64

/-- Sign-extend a 21-bit jump offset to 64 bits. -/
def signExtend21 (imm : BitVec 21) : Word :=
  imm.signExtend 64

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
@[simp] theorem signExtend12_63 : signExtend12 (63 : BitVec 12) = (63 : Word) := by native_decide

-- Negative offsets used by DivMod scratch memory (signExtend12 of values >= 2048)
@[simp] theorem signExtend12_4095 : signExtend12 (4095 : BitVec 12) = (18446744073709551615 : Word) := by native_decide  -- -1
@[simp] theorem signExtend12_4088 : signExtend12 (4088 : BitVec 12) = (18446744073709551608 : Word) := by native_decide  -- -8
@[simp] theorem signExtend12_4080 : signExtend12 (4080 : BitVec 12) = (18446744073709551600 : Word) := by native_decide  -- -16
@[simp] theorem signExtend12_4072 : signExtend12 (4072 : BitVec 12) = (18446744073709551592 : Word) := by native_decide  -- -24
@[simp] theorem signExtend12_4064 : signExtend12 (4064 : BitVec 12) = (18446744073709551584 : Word) := by native_decide  -- -32
@[simp] theorem signExtend12_4056 : signExtend12 (4056 : BitVec 12) = (18446744073709551576 : Word) := by native_decide  -- -40
@[simp] theorem signExtend12_4048 : signExtend12 (4048 : BitVec 12) = (18446744073709551568 : Word) := by native_decide  -- -48
@[simp] theorem signExtend12_4040 : signExtend12 (4040 : BitVec 12) = (18446744073709551560 : Word) := by native_decide  -- -56
@[simp] theorem signExtend12_4032 : signExtend12 (4032 : BitVec 12) = (18446744073709551552 : Word) := by native_decide  -- -64
@[simp] theorem signExtend12_4024 : signExtend12 (4024 : BitVec 12) = (18446744073709551544 : Word) := by native_decide  -- -72
@[simp] theorem signExtend12_4016 : signExtend12 (4016 : BitVec 12) = (18446744073709551536 : Word) := by native_decide  -- -80
@[simp] theorem signExtend12_4008 : signExtend12 (4008 : BitVec 12) = (18446744073709551528 : Word) := by native_decide  -- -88
@[simp] theorem signExtend12_4000 : signExtend12 (4000 : BitVec 12) = (18446744073709551520 : Word) := by native_decide  -- -96
@[simp] theorem signExtend12_3992 : signExtend12 (3992 : BitVec 12) = (18446744073709551512 : Word) := by native_decide  -- -104
@[simp] theorem signExtend12_3984 : signExtend12 (3984 : BitVec 12) = (18446744073709551504 : Word) := by native_decide  -- -112
@[simp] theorem signExtend12_3976 : signExtend12 (3976 : BitVec 12) = (18446744073709551496 : Word) := by native_decide  -- -120
@[simp] theorem signExtend12_3968 : signExtend12 (3968 : BitVec 12) = (18446744073709551488 : Word) := by native_decide  -- -128
@[simp] theorem signExtend12_3960 : signExtend12 (3960 : BitVec 12) = (18446744073709551480 : Word) := by native_decide  -- -136
@[simp] theorem signExtend12_3952 : signExtend12 (3952 : BitVec 12) = (18446744073709551472 : Word) := by native_decide  -- -144
@[simp] theorem signExtend12_3944 : signExtend12 (3944 : BitVec 12) = (18446744073709551464 : Word) := by native_decide  -- -152

-- ============================================================================
-- M-extension helper functions (RV64IM)
-- ============================================================================

/-- RV64IM signed division with spec-mandated edge cases. -/
def rv64_div (a b : Word) : Word :=
  if b == 0#64 then
    BitVec.allOnes 64  -- -1
  else
    BitVec.sdiv a b

/-- RV64IM unsigned division: division by zero returns 2^64-1. -/
def rv64_divu (a b : Word) : Word :=
  if b == 0#64 then
    BitVec.allOnes 64
  else
    a / b

/-- RV64IM signed remainder. -/
def rv64_rem (a b : Word) : Word :=
  if b == 0#64 then
    a
  else
    BitVec.srem a b

/-- RV64IM unsigned remainder. -/
def rv64_remu (a b : Word) : Word :=
  if b == 0#64 then
    a
  else
    a % b

/-- MULH: signed × signed, upper 64 bits. Uses 128-bit intermediate. -/
def rv64_mulh (a b : Word) : Word :=
  let a128 : BitVec 128 := a.signExtend 128
  let b128 : BitVec 128 := b.signExtend 128
  ((a128 * b128) >>> 64).truncate 64

/-- MULHSU: signed × unsigned, upper 64 bits. -/
def rv64_mulhsu (a b : Word) : Word :=
  let a128 : BitVec 128 := a.signExtend 128
  let b128 : BitVec 128 := b.zeroExtend 128
  ((a128 * b128) >>> 64).truncate 64

/-- MULHU: unsigned × unsigned, upper 64 bits. -/
def rv64_mulhu (a b : Word) : Word :=
  let a128 : BitVec 128 := a.zeroExtend 128
  let b128 : BitVec 128 := b.zeroExtend 128
  ((a128 * b128) >>> 64).truncate 64

-- ============================================================================
-- Instruction Semantics
-- ============================================================================

/-- Execute a single instruction, returning the new state.
    The PC is advanced by 4 (one instruction width).
    Branch/jump instructions are treated as NOP in list-based execution. -/
def execInstr (s : MachineState) (i : Instr) : MachineState :=
  let s' := match i with
    | .ADD rd rs1 rs2 =>
        s.setReg rd (s.getReg rs1 + s.getReg rs2)
    | .ADDI rd rs1 imm =>
        s.setReg rd (s.getReg rs1 + signExtend12 imm)
    | .SUB rd rs1 rs2 =>
        s.setReg rd (s.getReg rs1 - s.getReg rs2)
    | .SLL rd rs1 rs2 =>
        let shamt := (s.getReg rs2).toNat % 64
        s.setReg rd (s.getReg rs1 <<< shamt)
    | .SLLI rd rs1 shamt =>
        s.setReg rd (s.getReg rs1 <<< shamt.toNat)
    | .SRL rd rs1 rs2 =>
        let shamt := (s.getReg rs2).toNat % 64
        s.setReg rd (s.getReg rs1 >>> shamt)
    | .SRA rd rs1 rs2 =>
        let shamt := (s.getReg rs2).toNat % 64
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
    | .LD rd rs1 offset =>
        let addr := s.getReg rs1 + signExtend12 offset
        s.setReg rd (s.getMem addr)
    | .SD rs1 rs2 offset =>
        let addr := s.getReg rs1 + signExtend12 offset
        s.setMem addr (s.getReg rs2)
    | .LW rd rs1 offset =>
        let addr := s.getReg rs1 + signExtend12 offset
        s.setReg rd ((s.getWord32 addr).signExtend 64)
    | .LWU rd rs1 offset =>
        let addr := s.getReg rs1 + signExtend12 offset
        s.setReg rd ((s.getWord32 addr).zeroExtend 64)
    | .SW rs1 rs2 offset =>
        let addr := s.getReg rs1 + signExtend12 offset
        s.setWord32 addr ((s.getReg rs2).truncate 32)
    | .LB rd rs1 offset =>
        let addr := s.getReg rs1 + signExtend12 offset
        s.setReg rd ((s.getByte addr).signExtend 64)
    | .LH rd rs1 offset =>
        let addr := s.getReg rs1 + signExtend12 offset
        s.setReg rd ((s.getHalfword addr).signExtend 64)
    | .LBU rd rs1 offset =>
        let addr := s.getReg rs1 + signExtend12 offset
        s.setReg rd ((s.getByte addr).zeroExtend 64)
    | .LHU rd rs1 offset =>
        let addr := s.getReg rs1 + signExtend12 offset
        s.setReg rd ((s.getHalfword addr).zeroExtend 64)
    | .SB rs1 rs2 offset =>
        let addr := s.getReg rs1 + signExtend12 offset
        s.setByte addr ((s.getReg rs2).truncate 8)
    | .SH rs1 rs2 offset =>
        let addr := s.getReg rs1 + signExtend12 offset
        s.setHalfword addr ((s.getReg rs2).truncate 16)
    | .LUI rd imm =>
        -- RV64: LUI sign-extends the 32-bit result to 64 bits
        let val32 : BitVec 32 := imm.zeroExtend 32 <<< 12
        s.setReg rd (val32.signExtend 64)
    | .AUIPC rd imm =>
        let val32 : BitVec 32 := imm.zeroExtend 32 <<< 12
        let val : Word := s.pc + (val32.signExtend 64)
        s.setReg rd val
    | .MV rd rs =>
        s.setReg rd (s.getReg rs)
    | .LI rd imm =>
        s.setReg rd imm
    | .NOP => s
    | .ADDIW rd rs1 imm =>
        -- ADDIW: word-size add, result sign-extended to 64 bits
        let sum32 : BitVec 32 := ((s.getReg rs1).truncate 32) + ((signExtend12 imm).truncate 32)
        s.setReg rd (sum32.signExtend 64)
    | .FENCE => s
    | .EBREAK => s
    -- M extension
    | .MUL rd rs1 rs2 =>
        s.setReg rd (s.getReg rs1 * s.getReg rs2)
    | .MULH rd rs1 rs2 =>
        s.setReg rd (rv64_mulh (s.getReg rs1) (s.getReg rs2))
    | .MULHSU rd rs1 rs2 =>
        s.setReg rd (rv64_mulhsu (s.getReg rs1) (s.getReg rs2))
    | .MULHU rd rs1 rs2 =>
        s.setReg rd (rv64_mulhu (s.getReg rs1) (s.getReg rs2))
    | .DIV rd rs1 rs2 =>
        s.setReg rd (rv64_div (s.getReg rs1) (s.getReg rs2))
    | .DIVU rd rs1 rs2 =>
        s.setReg rd (rv64_divu (s.getReg rs1) (s.getReg rs2))
    | .REM rd rs1 rs2 =>
        s.setReg rd (rv64_rem (s.getReg rs1) (s.getReg rs2))
    | .REMU rd rs1 rs2 =>
        s.setReg rd (rv64_remu (s.getReg rs1) (s.getReg rs2))
    | .BEQ _ _ _ | .BNE _ _ _ | .BLT _ _ _ | .BGE _ _ _
    | .BLTU _ _ _ | .BGEU _ _ _ | .JAL _ _ | .JALR _ _ _ | .ECALL => s
  s'.setPC (s'.pc + 4#64)

end EvmAsm.Rv64
