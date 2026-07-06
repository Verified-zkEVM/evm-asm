/-
  EvmAsm.Codegen.Programs.CreateInitcodeSizeValid

  `create_initcode_size_valid` (bead fhsxz.2.4.2.61.8, CREATE deposit slice) — the
  EIP-3860 init-code size gate a CREATE/CREATE2 must pass before executing the init
  code. Per execution-specs amsterdam (EIP-3860), CREATE fails (the sub-call is not
  entered, the opcode pushes 0) when

    len(initcode) > MAX_INITCODE_SIZE = 2 * MAX_CODE_SIZE = 65536 (0x10000).

  Amsterdam (EIP-7954) doubled MAX_CODE_SIZE to 0x8000 (32768), so MAX_INITCODE_SIZE
  = 65536 — NOT the pre-Amsterdam 2*0x6000 = 49152 (bead xpgl5; the stale cutoff
  wrongly rejected init code in (49152, 65536], which Amsterdam accepts). This is
  the same threshold the live tx-level gate enforces (BlockVerdictGasGate,
  `li t2, 65536`). This standalone gate enforces the EIP-3860 length rejection
  explicitly for the CREATE/CREATE2 path;
  it pairs with create_deployed_code_valid (#8601, the post-execution deployed-code
  EIP-3541/EIP-170 gate) and is wired into the CREATE tail alongside it when CREATE
  is activated (.8c). EIP-3860 also charges 2 gas/word of init code, which the tail
  already accounts for (createInitcodeGasAsm); this is the SIZE rejection only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Emit

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-- EIP-3860 MAX_INITCODE_SIZE (bytes) = 2 * Amsterdam/EIP-7954 MAX_CODE_SIZE (32768) = 65536. -/
def maxInitcodeSize : Nat := 65536

/-- The `create_initcode_size_valid` body as a STRUCTURED RV64 program (a0=x10,
    t0=x5; `bgtu a0,t0,L` ≡ `bltu x5,x10,.+12`, `ret` ≡ `jalr x0,0(x1)`). This is
    what `emitProgram` renders below — byte-identical to the former hand-written
    asm — and what `EvmAsm.Codegen.Proofs.cisv_spec` proves as a `cpsTriple`:
    `a0 := (if maxInitcodeSize < len then 1 else 0); return`. -/
def cisvProgram : Program :=
  [ .LI .x5 (65536 : Word), .BLTU .x5 .x10 (12 : BitVec 13),
    .LI .x10 (0 : Word), .JALR .x0 .x1 0,
    .LI .x10 (1 : Word), .JALR .x0 .x1 0 ]

/-! ## create_initcode_size_valid
    a0 = init code length (bytes)
    a0 (output) = 0 valid / 1 invalid (len > MAX_INITCODE_SIZE).
    Leaf; clobbers t0. Emitted from the verified `cisvProgram` (cpsTriple-proven
    by `cisv_spec`); byte-identical to the prior hand-written asm. -/
def createInitcodeSizeValidFunction : String :=
  "create_initcode_size_valid:\n" ++ emitProgram cisvProgram

/-- `zisk_create_initcode_size_valid`: known-answer probe. Surfaces 4 results to
    OUTPUT (0xa0010000):
      +0  len 0      -> 0 valid
      +8  len 32     -> 0 valid
      +16 len 65536  -> 0 valid (boundary)
      +24 len 65537  -> 1 invalid -/
def ziskCreateInitcodeSizeValidPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li s0, 0xa0010000\n" ++
  "  li a0, 0;     jal ra, create_initcode_size_valid; sd a0, 0(s0)\n" ++
  "  li a0, 32;    jal ra, create_initcode_size_valid; sd a0, 8(s0)\n" ++
  "  li a0, 65536; jal ra, create_initcode_size_valid; sd a0, 16(s0)\n" ++
  "  li a0, 65537; jal ra, create_initcode_size_valid; sd a0, 24(s0)\n" ++
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
