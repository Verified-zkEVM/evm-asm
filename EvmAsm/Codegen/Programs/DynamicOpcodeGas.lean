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

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## keccak256_word_gas
    a0 = size in bytes → a0 = OPCODE_KECCAK256_BASE(30) + 6 * ceil32(size)//32. -/
def keccak256WordGasFunction : String :=
  "keccak256_word_gas:\n" ++
  "  addi t0, a0, 31; srli t0, t0, 5   # words\n" ++
  "  li t1, 6; mul t0, t0, t1\n" ++
  "  addi a0, t0, 30                   # + KECCAK256 base\n" ++
  "  ret"

/-! ## copy_word_gas
    a0 = size in bytes → a0 = OPCODE_COPY_PER_WORD(3) * ceil32(size)//32.
    (The *COPY base cost is the static opcode base; this is the per-word part.) -/
def copyWordGasFunction : String :=
  "copy_word_gas:\n" ++
  "  addi t0, a0, 31; srli t0, t0, 5   # words\n" ++
  "  li t1, 3; mul a0, t0, t1\n" ++
  "  ret"

/-! ## log_data_gas
    a0 = num_topics   a1 = data size in bytes
    a0 = OPCODE_LOG_BASE(375) + OPCODE_LOG_TOPIC(375)*num_topics
         + OPCODE_LOG_DATA_PER_BYTE(8)*data_bytes. -/
def logDataGasFunction : String :=
  "log_data_gas:\n" ++
  "  li t0, 375; mul t1, a0, t0        # 375 * num_topics\n" ++
  "  add t1, t1, t0                    # + LOG base (375)\n" ++
  "  li t2, 8; mul t2, a1, t2          # 8 * data_bytes\n" ++
  "  add a0, t1, t2\n" ++
  "  ret"

/-- `zisk_dynamic_opcode_gas`: probe over the three leaves.
    Input (after the ziskemu length wrapper at 0x40000000):
      bytes  8..16 : keccak size in bytes
      bytes 16..24 : copy size in bytes
      bytes 24..32 : log num_topics
      bytes 32..40 : log data size in bytes
    Output: +0 keccak256_word_gas, +8 copy_word_gas, +16 log_data_gas. -/
def ziskDynamicOpcodeGasPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t6, 0x40000000\n" ++
  "  li s0, 0xa0010000\n" ++
  "  ld a0, 8(t6);  jal ra, keccak256_word_gas; sd a0, 0(s0)\n" ++
  "  ld a0, 16(t6); jal ra, copy_word_gas;      sd a0, 8(s0)\n" ++
  "  ld a0, 24(t6); ld a1, 32(t6); jal ra, log_data_gas; sd a0, 16(s0)\n" ++
  "  j .Ldog_pdone\n" ++
  keccak256WordGasFunction ++ "\n" ++
  copyWordGasFunction ++ "\n" ++
  logDataGasFunction ++ "\n" ++
  ".Ldog_pdone:"

def ziskDynamicOpcodeGasProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskDynamicOpcodeGasPrologue
  dataAsm     := ""
}

end EvmAsm.Codegen
