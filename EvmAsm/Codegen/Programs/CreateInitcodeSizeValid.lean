/-
  EvmAsm.Codegen.Programs.CreateInitcodeSizeValid

  `create_initcode_size_valid` (bead fhsxz.2.4.2.61.8, CREATE deposit slice) — the
  EIP-3860 init-code size gate a CREATE/CREATE2 must pass before executing the init
  code. Per execution-specs amsterdam (EIP-3860), CREATE fails (the sub-call is not
  entered, the opcode pushes 0) when

    len(initcode) > MAX_INITCODE_SIZE = 2 * MAX_CODE_SIZE = 49152 (0xC000).

  The inline CREATE tail (createUnsupportedTail) currently only rejects when the
  init code's mem span exceeds the 0x10000 (65536) static-memory bound — so init
  code in (49152, 65536] is wrongly accepted. This standalone gate fills that gap;
  it pairs with create_deployed_code_valid (#8601, the post-execution deployed-code
  EIP-3541/EIP-170 gate) and is wired into the CREATE tail alongside it when CREATE
  is activated (.8c). EIP-3860 also charges 2 gas/word of init code, which the tail
  already accounts for (createInitcodeGasAsm); this is the SIZE rejection only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-- EIP-3860 MAX_INITCODE_SIZE (bytes) = 2 * EIP-170 MAX_CODE_SIZE (24576). -/
def maxInitcodeSize : Nat := 49152

/-! ## create_initcode_size_valid
    a0 = init code length (bytes)
    a0 (output) = 0 valid / 1 invalid (len > MAX_INITCODE_SIZE).
    Leaf; clobbers t0. -/
def createInitcodeSizeValidFunction : String :=
  "create_initcode_size_valid:\n" ++
  "  li t0, " ++ toString maxInitcodeSize ++ "\n" ++
  "  bgtu a0, t0, .Lcisv_invalid    # len > MAX_INITCODE_SIZE (EIP-3860)\n" ++
  "  li a0, 0; ret\n" ++
  ".Lcisv_invalid:\n" ++
  "  li a0, 1; ret"

/-- `zisk_create_initcode_size_valid`: known-answer probe. Surfaces 4 results to
    OUTPUT (0xa0010000):
      +0  len 0      -> 0 valid
      +8  len 32     -> 0 valid
      +16 len 49152  -> 0 valid (boundary)
      +24 len 49153  -> 1 invalid -/
def ziskCreateInitcodeSizeValidPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li s0, 0xa0010000\n" ++
  "  li a0, 0;     jal ra, create_initcode_size_valid; sd a0, 0(s0)\n" ++
  "  li a0, 32;    jal ra, create_initcode_size_valid; sd a0, 8(s0)\n" ++
  "  li a0, 49152; jal ra, create_initcode_size_valid; sd a0, 16(s0)\n" ++
  "  li a0, 49153; jal ra, create_initcode_size_valid; sd a0, 24(s0)\n" ++
  "  li x17, 93\n  li x10, 0\n  ecall\n" ++
  "  j .Lcisv_done\n" ++
  createInitcodeSizeValidFunction ++ "\n" ++
  ".Lcisv_done:"

def ziskCreateInitcodeSizeValidDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "cisv_pad:\n  .zero 8\n"

def ziskCreateInitcodeSizeValidProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskCreateInitcodeSizeValidPrologue
  dataAsm     := ziskCreateInitcodeSizeValidDataSection
}

end EvmAsm.Codegen
