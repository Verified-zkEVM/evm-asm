/-
  EvmAsm.Codegen.Programs.CreateDeployedCodeValid

  `create_deployed_code_valid` (bead fhsxz.2.4.2.61.8b, CREATE deposit slice) —
  the deployed-code validity gate a successful CREATE/CREATE2 must pass before the
  returned init-code output becomes the account's code.

  Per execution-specs amsterdam (vm/instructions/system.py `_deploy_code` /
  process_create_message): after the init code RETURNs its output, deployment FAILS
  (the contract is not created, the CREATE pushes 0) when

    * len(code) > MAX_CODE_SIZE (Amsterdam EIP-7907, 32768 / 0x8000; was EIP-170 24576), or
    * len(code) > 0 and code[0] == 0xEF (EIP-3541: reject new 0xEF-prefixed code).

  The bounded init-code mini-interpreter (create_execute_initcode_frame) records the
  returned bytes as create_child_code with status 2 but does NOT apply these two
  checks, so the CREATE-tail deposit (.8b-2) calls this gate first: an invalid
  deployment must push 0 and deposit nothing (matching a BAL with no code_change for
  that address), else the all-accounts code comparator would false-reject. Empty
  deployed code (len 0) is VALID (the account exists with empty code).
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Emit

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-- Amsterdam (EIP-7907) deployed-code size limit (bytes) = 0x8000 = 32768 (raised from
    the EIP-170 0x6000 = 24576). Code longer than this fails deployment. -/
def maxDeployedCodeSize : Nat := 32768

/-- The `create_deployed_code_valid` body as a STRUCTURED RV64 program (a0=x10 code
    ptr + result, a1=x11 len, t0=x5 scratch, t1=x6 byte). `bgtu a1,t0`≡`bltu x5,x11`,
    `beqz a1`≡`beq x11,x0`, `ret`≡`jalr x0,0(x1)`, labels→PC-relative offsets. This is
    what `emitProgram` renders below — byte-identical to the former hand-written asm —
    and what `EvmAsm.Rv64.cdcv_spec` proves as a `cpsTriple`. -/
def cdcvProgram : Program :=
  [ .LI .x5 (32768 : Word), .BLTU .x5 .x11 (28 : BitVec 13), .BEQ .x11 .x0 (16 : BitVec 13),
    .LBU .x6 .x10 (0 : BitVec 12), .LI .x5 (0xEF : Word), .BEQ .x6 .x5 (12 : BitVec 13),
    .LI .x10 (0 : Word), .JALR .x0 .x1 0, .LI .x10 (1 : Word), .JALR .x0 .x1 0 ]

/-! ## create_deployed_code_valid
    a0 = deployed code ptr   a1 = deployed code length (bytes)
    a0 (output) = 0 valid (deploy) / 1 invalid (EIP-3541 0xEF prefix or > MAX_CODE_SIZE).
    Leaf (no calls); clobbers t0/t1. Emitted from the verified `cdcvProgram`
    (cpsTriple-proven by `cdcv_spec`); byte-identical to the prior hand-written asm. -/
def createDeployedCodeValidFunction : String :=
  "create_deployed_code_valid:\n" ++ emitProgram cdcvProgram

/-- `zisk_create_deployed_code_valid`: known-answer probe. Surfaces 5 results to
    OUTPUT (0xa0010000):
      +0 empty (len 0)            -> 0 valid
      +8 {0x60} (len 1)           -> 0 valid
      +16 {0xEF} (len 1)          -> 1 invalid (EIP-3541)
      +24 {0x60..} (len 32768)    -> 0 valid (boundary)
      +32 {0x60..} (len 32769)    -> 1 invalid (Amsterdam EIP-7907) -/
def ziskCreateDeployedCodeValidPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li s0, 0xa0010000\n" ++
  -- buf[0] = 0x60 (non-0xEF); the size tests use len only, content past [0] is 0.
  "  la t0, cdcv_buf; li t1, 0x60; sb t1, 0(t0)\n" ++
  -- empty (len 0) -> valid
  "  la a0, cdcv_buf; li a1, 0; jal ra, create_deployed_code_valid; sd a0, 0(s0)\n" ++
  -- {0x60} len 1 -> valid
  "  la a0, cdcv_buf; li a1, 1; jal ra, create_deployed_code_valid; sd a0, 8(s0)\n" ++
  -- {0xEF} len 1 -> invalid
  "  la t0, cdcv_buf; li t1, 0xEF; sb t1, 0(t0)\n" ++
  "  la a0, cdcv_buf; li a1, 1; jal ra, create_deployed_code_valid; sd a0, 16(s0)\n" ++
  -- restore buf[0] = 0x60 for the size-boundary tests
  "  la t0, cdcv_buf; li t1, 0x60; sb t1, 0(t0)\n" ++
  -- len 32768 -> valid (boundary)
  "  la a0, cdcv_buf; li a1, 32768; jal ra, create_deployed_code_valid; sd a0, 24(s0)\n" ++
  -- len 32769 -> invalid
  "  la a0, cdcv_buf; li a1, 32769; jal ra, create_deployed_code_valid; sd a0, 32(s0)\n" ++
  "  li x17, 93\n  li x10, 0\n  ecall\n" ++
  "  j .Lcdcv_done\n" ++
  createDeployedCodeValidFunction ++ "\n" ++
  ".Lcdcv_done:"

def ziskCreateDeployedCodeValidDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "cdcv_buf:\n  .zero 24608\n"

def ziskCreateDeployedCodeValidProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskCreateDeployedCodeValidPrologue
  dataAsm     := ziskCreateDeployedCodeValidDataSection
}

end EvmAsm.Codegen
