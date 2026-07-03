/-
  EvmAsm.Codegen.RoundTripTests

  `#guard` examples — one per shape — that fail elaboration if `emitInstr`
  drifts from the GNU-as syntax we feed `riscv64-elf-as`. The intent is
  cheap drift detection at build time, not exhaustive coverage; the real
  check is "the emitted .s assembles cleanly" (M1 exit criterion).
-/

import EvmAsm.Codegen.Emit

namespace EvmAsm.Codegen.RoundTripTests

open EvmAsm.Codegen
open EvmAsm.Rv64

-- ALU register-register
#guard emitInstr (.ADD  .x5 .x6 .x7) = "add x5, x6, x7"
#guard emitInstr (.SUB  .x5 .x6 .x7) = "sub x5, x6, x7"
#guard emitInstr (.SLL  .x5 .x6 .x7) = "sll x5, x6, x7"
#guard emitInstr (.SRL  .x5 .x6 .x7) = "srl x5, x6, x7"
#guard emitInstr (.SRA  .x5 .x6 .x7) = "sra x5, x6, x7"
#guard emitInstr (.AND  .x5 .x6 .x7) = "and x5, x6, x7"
#guard emitInstr (.OR   .x5 .x6 .x7) = "or x5, x6, x7"
#guard emitInstr (.XOR  .x5 .x6 .x7) = "xor x5, x6, x7"
#guard emitInstr (.SLT  .x5 .x6 .x7) = "slt x5, x6, x7"
#guard emitInstr (.SLTU .x5 .x6 .x7) = "sltu x5, x6, x7"

-- ALU immediate (signed 12-bit)
#guard emitInstr (.ADDI  .x5 .x6 (42 : BitVec 12))    = "addi x5, x6, 42"
#guard emitInstr (.ADDI  .x5 .x6 (-16 : BitVec 12))   = "addi x5, x6, -16"
#guard emitInstr (.ANDI  .x5 .x6 (0xFF : BitVec 12))  = "andi x5, x6, 255"
#guard emitInstr (.ORI   .x5 .x6 (1 : BitVec 12))     = "ori x5, x6, 1"
#guard emitInstr (.XORI  .x5 .x6 (0 : BitVec 12))     = "xori x5, x6, 0"
#guard emitInstr (.SLTI  .x5 .x6 (3 : BitVec 12))     = "slti x5, x6, 3"
#guard emitInstr (.SLTIU .x5 .x6 (3 : BitVec 12))     = "sltiu x5, x6, 3"

-- Shift immediate (unsigned 6-bit)
#guard emitInstr (.SLLI .x5 .x6 (3 : BitVec 6))  = "slli x5, x6, 3"
#guard emitInstr (.SRLI .x5 .x6 (63 : BitVec 6)) = "srli x5, x6, 63"
#guard emitInstr (.SRAI .x5 .x6 (1 : BitVec 6))  = "srai x5, x6, 1"

-- Upper immediate (unsigned 20-bit, hex)
#guard emitInstr (.LUI   .x5 (0x80000 : BitVec 20)) = "lui x5, 0x80000"
#guard emitInstr (.AUIPC .x5 (0x1 : BitVec 20))     = "auipc x5, 0x1"
#guard emitInstr (.LUI   .x5 (0 : BitVec 20))       = "lui x5, 0x0"

-- Doubleword memory
#guard emitInstr (.LD .x7 .x12 (32 : BitVec 12))      = "ld x7, 32(x12)"
#guard emitInstr (.SD .x12 .x7 (32 : BitVec 12))      = "sd x7, 32(x12)"
#guard emitInstr (.SD .x12 .x7 (-8 : BitVec 12))      = "sd x7, -8(x12)"

-- Word memory
#guard emitInstr (.LW  .x5 .x6 (4 : BitVec 12)) = "lw x5, 4(x6)"
#guard emitInstr (.LWU .x5 .x6 (4 : BitVec 12)) = "lwu x5, 4(x6)"
#guard emitInstr (.SW  .x6 .x5 (4 : BitVec 12)) = "sw x5, 4(x6)"

-- Sub-word memory
#guard emitInstr (.LB  .x5 .x6 (1 : BitVec 12)) = "lb x5, 1(x6)"
#guard emitInstr (.LH  .x5 .x6 (2 : BitVec 12)) = "lh x5, 2(x6)"
#guard emitInstr (.LBU .x5 .x6 (1 : BitVec 12)) = "lbu x5, 1(x6)"
#guard emitInstr (.LHU .x5 .x6 (2 : BitVec 12)) = "lhu x5, 2(x6)"
#guard emitInstr (.SB  .x6 .x5 (1 : BitVec 12)) = "sb x5, 1(x6)"
#guard emitInstr (.SH  .x6 .x5 (2 : BitVec 12)) = "sh x5, 2(x6)"

-- Branches (signed 13-bit byte offset)
#guard emitInstr (.BEQ  .x5 .x6 (16 : BitVec 13))  = "beq x5, x6, .+16"
#guard emitInstr (.BNE  .x5 .x6 (-8 : BitVec 13))  = "bne x5, x6, .-8"
#guard emitInstr (.BLT  .x5 .x6 (0 : BitVec 13))   = "blt x5, x6, .+0"
#guard emitInstr (.BGE  .x5 .x6 (4 : BitVec 13))   = "bge x5, x6, .+4"
#guard emitInstr (.BLTU .x5 .x6 (4 : BitVec 13))   = "bltu x5, x6, .+4"
#guard emitInstr (.BGEU .x5 .x6 (4 : BitVec 13))   = "bgeu x5, x6, .+4"

-- Jumps
#guard emitInstr (.JAL  .x1 (32 : BitVec 21))             = "jal x1, .+32"
#guard emitInstr (.JAL  .x1 (-16 : BitVec 21))            = "jal x1, .-16"
#guard emitInstr (.JALR .x0 .x1 (0 : BitVec 12))          = "jalr x0, 0(x1)"

-- Pseudo
#guard emitInstr (.MV  .x5 .x6)                = "mv x5, x6"
#guard emitInstr (.LI  .x10 (42 : Word))       = "li x10, 42"
#guard emitInstr (.LI  .x10 (-1 : Word))       = "li x10, -1"
#guard emitInstr .NOP                          = "nop"

-- *W
#guard emitInstr (.ADDIW .x5 .x6 (-1 : BitVec 12)) = "addiw x5, x6, -1"

-- System
#guard emitInstr .ECALL  = "ecall"
#guard emitInstr .FENCE  = "fence"
#guard emitInstr .EBREAK = "ebreak"

-- ZisK accelerator CSR calls (pre-encoded `.4byte` for the rv64imac toolchain)
#guard emitInstr (.CSRS 0x800 .x10) = s!".4byte {0x80052073}"
#guard emitInstr (.CSRS 0x802 .x5)  = s!".4byte {0x8022a073}"
#guard emitInstr (.CSRS 0x805 .x10) = s!".4byte {0x80552073}"

-- RV64M
#guard emitInstr (.MUL    .x5 .x6 .x7) = "mul x5, x6, x7"
#guard emitInstr (.MULH   .x5 .x6 .x7) = "mulh x5, x6, x7"
#guard emitInstr (.MULHSU .x5 .x6 .x7) = "mulhsu x5, x6, x7"
#guard emitInstr (.MULHU  .x5 .x6 .x7) = "mulhu x5, x6, x7"
#guard emitInstr (.DIV    .x5 .x6 .x7) = "div x5, x6, x7"
#guard emitInstr (.DIVU   .x5 .x6 .x7) = "divu x5, x6, x7"
#guard emitInstr (.REM    .x5 .x6 .x7) = "rem x5, x6, x7"
#guard emitInstr (.REMU   .x5 .x6 .x7) = "remu x5, x6, x7"

end EvmAsm.Codegen.RoundTripTests
