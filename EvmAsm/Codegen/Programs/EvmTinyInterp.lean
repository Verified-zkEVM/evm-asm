/-
  EvmAsm.Codegen.Programs.EvmTinyInterp

  M5a unrolled tiny EVM interpreter demo units.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Evm64.Push.Program
import EvmAsm.Codegen.Programs.EvmBasic

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## tiny_interp — M5a unrolled tiny EVM interpreter

    Two hand-picked EVM bytecodes laid out as `.data` bytes, executed
    by *chaining* verified opcode `Program`s with explicit `x10`
    advances between handlers. No runtime fetch/decode/dispatch loop
    (deferred to M5b). The point is to validate that verified opcode
    Programs compose under `++` while honoring the `x10` code-pointer
    convention that `evm_push` reads its immediates from.

    Stack layout: 256 bytes of writable EVM stack below label
    `evm_stack_top`, plus a post-top scratch window for opcode bodies that
    use positive offsets from the live stack pointer. The EVM stack grows
    downward; the prologue initializes `x12 = evm_stack_top` and each
    `evm_push` decrements `x12` by 32 to allocate a new slot. -/

/-- Dispatcher glue between unrolled opcode `Program`s: advance the
    EVM code pointer (`x10`) by the byte width of the opcode just
    executed (`1 + n` for `PUSHn`, `1` for `ADD`/`STOP`).

    In the M5b full dispatch loop this advance is computed inside the
    decoder; M5a inlines it directly so chained verified Programs read
    their PUSH immediates from the right byte. Stays in the verified
    `Program` world. -/
def advancePc (off : Nat) : Program :=
  ADDI .x10 .x10 (BitVec.ofNat 12 off)

/-- Prologue shared by all tiny-interp units. `la x10, evm_code`
    points the EVM code pointer at the start of the bytecode; `la
    x12, evm_stack_top` initializes the EVM stack pointer at the
    high-address end of a 256-byte writable scratch region. -/
def tinyInterpPrologue : String :=
  "  la x10, evm_code\n" ++
  "  la x12, evm_stack_top"

/-- `.data` section: a label `evm_code` holding the bytecode bytes,
    followed by the writable EVM stack and opcode scratch windows.
    `bytecodeBytes` is a comma-separated `.byte` directive payload
    (e.g. `"0x60, 0xff, 0x60, 0x01, 0x01, 0x00"`).

    Written as raw asm text rather than `emitDataLabel` because the
    layout is hybrid (`.byte` payload for the bytecode, `.zero` for
    the stack scratch) -- `emitDataLabel` only takes `UInt64` dwords. -/
def tinyInterpDataSection (bytecodeBytes : String) : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "evm_code:\n" ++
  s!"  .byte {bytecodeBytes}\n" ++
  ".balign 32\n" ++
  "evm_stack_low:\n" ++
  "  .zero 256\n" ++
  "evm_stack_top:\n" ++
  "evm_stack_positive_scratch:\n" ++
  "  .zero 256"

/-- M5a test case 1: `PUSH1 0xFF; PUSH1 0x01; ADD; STOP`. Expected
    256-bit sum = `0x100`, which as four LE u64 limbs is
    `[0x100, 0, 0, 0]` — first 8 bytes `00 01 00 00 00 00 00 00`.

    The chain is `Program ++ Program ++ ...`; each `advancePc`
    between opcode handlers is the only dispatcher glue. STOP needs
    no body — falling through to the halt stub appended by
    `emitBuildUnit` is equivalent. -/
def tinyInterpAdd : Program :=
  EvmAsm.Evm64.evm_push 1 ++ advancePc 2 ++
  EvmAsm.Evm64.evm_push 1 ++ advancePc 2 ++
  EvmAsm.Evm64.evm_add  ++ advancePc 1

/-- Bytecode for `tinyInterpAdd`: `60 ff 60 01 01 00`. -/
def tinyInterpAddBytecode : String :=
  "0x60, 0xff, 0x60, 0x01, 0x01, 0x00"

def tinyInterpAddUnit : BuildUnit := {
  body        := tinyInterpAdd ++ evmAddEpilogue
  prologueAsm := tinyInterpPrologue
  dataAsm     := tinyInterpDataSection tinyInterpAddBytecode
}

/-- M5a test case 2: `PUSH1 0x10; PUSH1 0x20; ADD; PUSH1 0x30; ADD;
    STOP`. Expected sum = `0x60`, LE limbs `[0x60, 0, 0, 0]` — first
    8 bytes `60 00 00 00 00 00 00 00`. Exercises chained ADDs and a
    stack-pointer history that walks back up after each ADD. -/
def tinyInterpAdd2 : Program :=
  EvmAsm.Evm64.evm_push 1 ++ advancePc 2 ++
  EvmAsm.Evm64.evm_push 1 ++ advancePc 2 ++
  EvmAsm.Evm64.evm_add  ++ advancePc 1 ++
  EvmAsm.Evm64.evm_push 1 ++ advancePc 2 ++
  EvmAsm.Evm64.evm_add  ++ advancePc 1

/-- Bytecode for `tinyInterpAdd2`: `60 10 60 20 01 60 30 01 00`. -/
def tinyInterpAdd2Bytecode : String :=
  "0x60, 0x10, 0x60, 0x20, 0x01, 0x60, 0x30, 0x01, 0x00"

def tinyInterpAdd2Unit : BuildUnit := {
  body        := tinyInterpAdd2 ++ evmAddEpilogue
  prologueAsm := tinyInterpPrologue
  dataAsm     := tinyInterpDataSection tinyInterpAdd2Bytecode
}

end EvmAsm.Codegen
