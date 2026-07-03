/-
  EvmAsm.Codegen.Programs.DynamicOpcodeGas

  Per-unit dynamic-gas leaves (bead nxio8.3) — the linear (per-word / per-byte)
  components the dispatcher currently drops (nxio8), completing the primitive set
  alongside `sstore_regular_gas` (#8630) and `memory_expansion_gas` (#8631). The
  memory-expansion term (for KECCAK256/*COPY/LOG) is added separately via
  `memory_expansion_gas`; these leaves are the opcode-intrinsic per-unit part.

  Exact Amsterdam constants (execution-specs `vm/gas.py`):
    KECCAK256 : OPCODE_KECCAK256_BASE(30) + OPCODE_KECCACK256_PER_WORD(6) * words
    *COPY     : OPCODE_COPY_PER_WORD(3) * words            (CALLDATA/CODE/RETURNDATA/MCOPY/EXTCODE)
    LOG       : OPCODE_LOG_BASE(375) + OPCODE_LOG_TOPIC(375) * num_topics
                + OPCODE_LOG_DATA_PER_BYTE(8) * data_bytes
  with words = ceil32(size_bytes) // 32 = (size_bytes + 31) >> 5.

  Pure unsigned 64-bit arithmetic, no helper calls. NOT wired into the dispatcher
  opcode handlers (that is the follow-up, dispatcher-gas / Dispatch.lean domain) →
  soundness-neutral, verdict byte-identical.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Emit

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## keccak256_word_gas
    a0 = size in bytes → a0 = OPCODE_KECCAK256_BASE(30) + 6 * ceil32(size)//32. -/
def keccak256WordGas_prog : Program :=
  [ .ADDI .x5 .x10 (31 : BitVec 12),
    .SRLI .x5 .x5 (5 : BitVec 6),
    .LI .x6 (6 : Word),
    .MUL .x5 .x5 .x6,
    .ADDI .x10 .x5 (30 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

def keccak256WordGasFunction : String :=
  "keccak256_word_gas:\n" ++ emitProgram keccak256WordGas_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `keccak256WordGas_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem keccak256WordGasFunction_eq_prog :
    keccak256WordGasFunction = "keccak256_word_gas:\n" ++ emitProgram keccak256WordGas_prog := rfl

#guard keccak256WordGasFunction.startsWith "keccak256_word_gas:\n"
#guard keccak256WordGas_prog.length = 6
/-! ## copy_word_gas
    a0 = size in bytes → a0 = OPCODE_COPY_PER_WORD(3) * ceil32(size)//32.
    (The *COPY base cost is the static opcode base; this is the per-word part.) -/
def copyWordGas_prog : Program :=
  [ .ADDI .x5 .x10 (31 : BitVec 12),
    .SRLI .x5 .x5 (5 : BitVec 6),
    .LI .x6 (3 : Word),
    .MUL .x10 .x5 .x6,
    .JALR .x0 .x1 (0 : BitVec 12) ]

def copyWordGasFunction : String :=
  "copy_word_gas:\n" ++ emitProgram copyWordGas_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `copyWordGas_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem copyWordGasFunction_eq_prog :
    copyWordGasFunction = "copy_word_gas:\n" ++ emitProgram copyWordGas_prog := rfl

#guard copyWordGasFunction.startsWith "copy_word_gas:\n"
#guard copyWordGas_prog.length = 5
/-! ## log_data_gas
    a0 = num_topics   a1 = data size in bytes
    a0 = OPCODE_LOG_BASE(375) + OPCODE_LOG_TOPIC(375)*num_topics
         + OPCODE_LOG_DATA_PER_BYTE(8)*data_bytes. -/
def logDataGas_prog : Program :=
  [ .LI .x5 (375 : Word),
    .MUL .x6 .x10 .x5,
    .ADD .x6 .x6 .x5,
    .LI .x7 (8 : Word),
    .MUL .x7 .x11 .x7,
    .ADD .x10 .x6 .x7,
    .JALR .x0 .x1 (0 : BitVec 12) ]

def logDataGasFunction : String :=
  "log_data_gas:\n" ++ emitProgram logDataGas_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `logDataGas_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem logDataGasFunction_eq_prog :
    logDataGasFunction = "log_data_gas:\n" ++ emitProgram logDataGas_prog := rfl

#guard logDataGasFunction.startsWith "log_data_gas:\n"
#guard logDataGas_prog.length = 7
/-! ## exp_gas
    a0 = exponent value ptr (32-byte BE)
    a0 = OPCODE_EXP_BASE(10) + OPCODE_EXP_PER_BYTE(50) * exponent_bytes, where
    exponent_bytes = (bit_length(exponent) + 7)//8 = 32 - leading_zero_bytes of the
    32-byte big-endian exponent (0 when the exponent is 0). Leaf, no calls. -/
def expGas_prog : Program :=
  [ .LI .x5 (0 : Word),
    .LI .x6 (32 : Word),
    .BEQ .x5 .x6 (48 : BitVec 13),
    .ADD .x7 .x10 .x5,
    .LBU .x7 .x7 (0 : BitVec 12),
    .BNE .x7 .x0 (12 : BitVec 13),
    .ADDI .x5 .x5 (1 : BitVec 12),
    .JAL .x0 (-24 : BitVec 21),
    .LI .x6 (32 : Word),
    .SUB .x6 .x6 .x5,
    .LI .x7 (50 : Word),
    .MUL .x6 .x6 .x7,
    .ADDI .x10 .x6 (10 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12),
    .LI .x10 (10 : Word),
    .JALR .x0 .x1 (0 : BitVec 12) ]

def expGasFunction : String :=
  "exp_gas:\n" ++ emitProgram expGas_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `expGas_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem expGasFunction_eq_prog :
    expGasFunction = "exp_gas:\n" ++ emitProgram expGas_prog := rfl

#guard expGasFunction.startsWith "exp_gas:\n"
#guard expGas_prog.length = 16
/-- `zisk_dynamic_opcode_gas`: probe over the leaves.
    Input (after the ziskemu length wrapper at 0x40000000):
      bytes  8..16 : keccak size in bytes
      bytes 16..24 : copy size in bytes
      bytes 24..32 : log num_topics
      bytes 32..40 : log data size in bytes
      bytes 40..72 : exp exponent (32-byte BE)
    Output: +0 keccak256_word_gas, +8 copy_word_gas, +16 log_data_gas, +24 exp_gas. -/
def ziskDynamicOpcodeGasPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t6, 0x40000000\n" ++
  "  li s0, 0xa0010000\n" ++
  "  ld a0, 8(t6);  jal ra, keccak256_word_gas; sd a0, 0(s0)\n" ++
  "  ld a0, 16(t6); jal ra, copy_word_gas;      sd a0, 8(s0)\n" ++
  "  ld a0, 24(t6); ld a1, 32(t6); jal ra, log_data_gas; sd a0, 16(s0)\n" ++
  "  addi a0, t6, 40; jal ra, exp_gas; sd a0, 24(s0)\n" ++
  "  j .Ldog_pdone\n" ++
  keccak256WordGasFunction ++ "\n" ++
  copyWordGasFunction ++ "\n" ++
  logDataGasFunction ++ "\n" ++
  expGasFunction ++ "\n" ++
  ".Ldog_pdone:"

def ziskDynamicOpcodeGasProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskDynamicOpcodeGasPrologue
  dataAsm     := ""
}

end EvmAsm.Codegen
