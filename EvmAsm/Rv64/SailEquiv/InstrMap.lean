/-
  EvmAsm.Rv64.SailEquiv.InstrMap

  Translation from Rv64.Instr to SAIL instruction type.
-/

import EvmAsm.Rv64.Basic
import EvmAsm.Rv64.SailEquiv.StateRel
import LeanRV64D

open LeanRV64D.Functions
open LeanRV64D.Defs

namespace EvmAsm.Rv64.SailEquiv

-- ============================================================================
-- Instruction mapping
-- ============================================================================

/-- Map an Rv64 instruction to its SAIL equivalent.
    Pseudo-instructions (MV, LI, NOP) map to their base instruction equivalents.
    ECALL, FENCE, EBREAK map directly. -/
noncomputable def toSailInstr : Instr → instruction
  -- RV64I ALU register-register → RTYPE
  | .ADD rd rs1 rs2  => .RTYPE (regToRegidx rs2, regToRegidx rs1, regToRegidx rd, rop.ADD)
  | .SUB rd rs1 rs2  => .RTYPE (regToRegidx rs2, regToRegidx rs1, regToRegidx rd, rop.SUB)
  | .SLL rd rs1 rs2  => .RTYPE (regToRegidx rs2, regToRegidx rs1, regToRegidx rd, rop.SLL)
  | .SRL rd rs1 rs2  => .RTYPE (regToRegidx rs2, regToRegidx rs1, regToRegidx rd, rop.SRL)
  | .SRA rd rs1 rs2  => .RTYPE (regToRegidx rs2, regToRegidx rs1, regToRegidx rd, rop.SRA)
  | .AND rd rs1 rs2  => .RTYPE (regToRegidx rs2, regToRegidx rs1, regToRegidx rd, rop.AND)
  | .OR  rd rs1 rs2  => .RTYPE (regToRegidx rs2, regToRegidx rs1, regToRegidx rd, rop.OR)
  | .XOR rd rs1 rs2  => .RTYPE (regToRegidx rs2, regToRegidx rs1, regToRegidx rd, rop.XOR)
  | .SLT rd rs1 rs2  => .RTYPE (regToRegidx rs2, regToRegidx rs1, regToRegidx rd, rop.SLT)
  | .SLTU rd rs1 rs2 => .RTYPE (regToRegidx rs2, regToRegidx rs1, regToRegidx rd, rop.SLTU)
  -- RV64I ALU immediate → ITYPE
  | .ADDI rd rs1 imm  => .ITYPE (imm, regToRegidx rs1, regToRegidx rd, iop.ADDI)
  | .ANDI rd rs1 imm  => .ITYPE (imm, regToRegidx rs1, regToRegidx rd, iop.ANDI)
  | .ORI  rd rs1 imm  => .ITYPE (imm, regToRegidx rs1, regToRegidx rd, iop.ORI)
  | .XORI rd rs1 imm  => .ITYPE (imm, regToRegidx rs1, regToRegidx rd, iop.XORI)
  | .SLTI rd rs1 imm  => .ITYPE (imm, regToRegidx rs1, regToRegidx rd, iop.SLTI)
  | .SLTIU rd rs1 imm => .ITYPE (imm, regToRegidx rs1, regToRegidx rd, iop.SLTIU)
  -- RV64I shifts immediate → SHIFTIOP
  | .SLLI rd rs1 shamt => .SHIFTIOP (shamt, regToRegidx rs1, regToRegidx rd, sop.SLLI)
  | .SRLI rd rs1 shamt => .SHIFTIOP (shamt, regToRegidx rs1, regToRegidx rd, sop.SRLI)
  | .SRAI rd rs1 shamt => .SHIFTIOP (shamt, regToRegidx rs1, regToRegidx rd, sop.SRAI)
  -- RV64I upper immediate → UTYPE
  | .LUI rd imm   => .UTYPE (imm, regToRegidx rd, uop.LUI)
  | .AUIPC rd imm => .UTYPE (imm, regToRegidx rd, uop.AUIPC)
  -- RV64I memory → LOAD/STORE
  | .LD  rd rs1 off  => .LOAD (off, regToRegidx rs1, regToRegidx rd, false, 8)
  | .SD  rs1 rs2 off => .STORE (off, regToRegidx rs2, regToRegidx rs1, 8)
  | .LW  rd rs1 off  => .LOAD (off, regToRegidx rs1, regToRegidx rd, false, 4)
  | .LWU rd rs1 off  => .LOAD (off, regToRegidx rs1, regToRegidx rd, true, 4)
  | .SW  rs1 rs2 off => .STORE (off, regToRegidx rs2, regToRegidx rs1, 4)
  | .LB  rd rs1 off  => .LOAD (off, regToRegidx rs1, regToRegidx rd, false, 1)
  | .LH  rd rs1 off  => .LOAD (off, regToRegidx rs1, regToRegidx rd, false, 2)
  | .LBU rd rs1 off  => .LOAD (off, regToRegidx rs1, regToRegidx rd, true, 1)
  | .LHU rd rs1 off  => .LOAD (off, regToRegidx rs1, regToRegidx rd, true, 2)
  | .SB  rs1 rs2 off => .STORE (off, regToRegidx rs2, regToRegidx rs1, 1)
  | .SH  rs1 rs2 off => .STORE (off, regToRegidx rs2, regToRegidx rs1, 2)
  -- RV64I branches → BTYPE
  | .BEQ  rs1 rs2 off => .BTYPE (off, regToRegidx rs2, regToRegidx rs1, bop.BEQ)
  | .BNE  rs1 rs2 off => .BTYPE (off, regToRegidx rs2, regToRegidx rs1, bop.BNE)
  | .BLT  rs1 rs2 off => .BTYPE (off, regToRegidx rs2, regToRegidx rs1, bop.BLT)
  | .BGE  rs1 rs2 off => .BTYPE (off, regToRegidx rs2, regToRegidx rs1, bop.BGE)
  | .BLTU rs1 rs2 off => .BTYPE (off, regToRegidx rs2, regToRegidx rs1, bop.BLTU)
  | .BGEU rs1 rs2 off => .BTYPE (off, regToRegidx rs2, regToRegidx rs1, bop.BGEU)
  -- RV64I jumps
  | .JAL rd off       => .JAL (off, regToRegidx rd)
  | .JALR rd rs1 off  => .JALR (off, regToRegidx rs1, regToRegidx rd)
  -- RV64I pseudo-instructions (mapped to their base forms)
  | .MV rd rs    => .ITYPE (0, regToRegidx rs, regToRegidx rd, iop.ADDI)
  | .LI rd _imm  => .ITYPE (0, Regidx 0, regToRegidx rd, iop.ADDI) -- NOTE: LI is a pseudo; only works for small immediates
  | .NOP         => .ITYPE (0, Regidx 0, Regidx 0, iop.ADDI)
  -- RV64I *W instructions
  | .ADDIW rd rs1 imm => .ADDIW (imm, regToRegidx rs1, regToRegidx rd)
  -- System
  | .ECALL  => .ECALL ()
  | .FENCE  => .FENCE_TSO ()  -- approximate: both are memory ordering NOPs in single-hart
  | .EBREAK => .EBREAK ()
  -- RV64M multiply → MUL
  | .MUL rd rs1 rs2 =>
    .MUL (regToRegidx rs2, regToRegidx rs1, regToRegidx rd,
      { result_part := Low, signed_rs1 := Signed, signed_rs2 := Signed })
  | .MULH rd rs1 rs2 =>
    .MUL (regToRegidx rs2, regToRegidx rs1, regToRegidx rd,
      { result_part := High, signed_rs1 := Signed, signed_rs2 := Signed })
  | .MULHSU rd rs1 rs2 =>
    .MUL (regToRegidx rs2, regToRegidx rs1, regToRegidx rd,
      { result_part := High, signed_rs1 := Signed, signed_rs2 := Unsigned })
  | .MULHU rd rs1 rs2 =>
    .MUL (regToRegidx rs2, regToRegidx rs1, regToRegidx rd,
      { result_part := High, signed_rs1 := Unsigned, signed_rs2 := Unsigned })
  -- RV64M divide → DIV
  | .DIV  rd rs1 rs2 => .DIV (regToRegidx rs2, regToRegidx rs1, regToRegidx rd, false)
  | .DIVU rd rs1 rs2 => .DIV (regToRegidx rs2, regToRegidx rs1, regToRegidx rd, true)
  -- RV64M remainder → REM
  | .REM  rd rs1 rs2 => .REM (regToRegidx rs2, regToRegidx rs1, regToRegidx rd, false)
  | .REMU rd rs1 rs2 => .REM (regToRegidx rs2, regToRegidx rs1, regToRegidx rd, true)

-- ============================================================================
-- Mapping correctness: toSailInstr dispatches to the expected execute_* handler
-- ============================================================================

/-- For RTYPE instructions, execute dispatches to execute_RTYPE. -/
theorem execute_rtype_dispatch (rs2 rs1 rd : regidx) (op : rop) :
    execute (.RTYPE (rs2, rs1, rd, op)) = execute_RTYPE rs2 rs1 rd op := by
  sorry

/-- For ITYPE instructions, execute dispatches to execute_ITYPE. -/
theorem execute_itype_dispatch (imm : BitVec 12) (rs1 rd : regidx) (op : iop) :
    execute (.ITYPE (imm, rs1, rd, op)) = execute_ITYPE imm rs1 rd op := by
  sorry

/-- For SHIFTIOP instructions, execute dispatches to execute_SHIFTIOP. -/
theorem execute_shiftiop_dispatch (shamt : BitVec 6) (rs1 rd : regidx) (op : sop) :
    execute (.SHIFTIOP (shamt, rs1, rd, op)) = execute_SHIFTIOP shamt rs1 rd op := by
  sorry

/-- For UTYPE instructions, execute dispatches to execute_UTYPE. -/
theorem execute_utype_dispatch (imm : BitVec 20) (rd : regidx) (op : uop) :
    execute (.UTYPE (imm, rd, op)) = execute_UTYPE imm rd op := by
  sorry

/-- For BTYPE instructions, execute dispatches to execute_BTYPE. -/
theorem execute_btype_dispatch (imm : BitVec 13) (rs2 rs1 : regidx) (op : bop) :
    execute (.BTYPE (imm, rs2, rs1, op)) = execute_BTYPE imm rs2 rs1 op := by
  sorry

/-- For MUL instructions, execute dispatches to execute_MUL. -/
theorem execute_mul_dispatch (rs2 rs1 rd : regidx) (op : mul_op) :
    execute (.MUL (rs2, rs1, rd, op)) = execute_MUL rs2 rs1 rd op := by
  sorry

/-- For DIV instructions, execute dispatches to execute_DIV. -/
theorem execute_div_dispatch (rs2 rs1 rd : regidx) (is_unsigned : Bool) :
    execute (.DIV (rs2, rs1, rd, is_unsigned)) = execute_DIV rs2 rs1 rd is_unsigned := by
  sorry

/-- For REM instructions, execute dispatches to execute_REM. -/
theorem execute_rem_dispatch (rs2 rs1 rd : regidx) (is_unsigned : Bool) :
    execute (.REM (rs2, rs1, rd, is_unsigned)) = execute_REM rs2 rs1 rd is_unsigned := by
  sorry

end EvmAsm.Rv64.SailEquiv
