/-
  EvmAsm.Evm64.Code.SizeProgram

  RISC-V program implementing the EVM `CODESIZE` opcode.

  CODESIZE pushes the length of the *currently executing* bytecode onto the
  EVM stack as a 256-bit word. The dispatcher prologue seeds the exact
  running-bytecode length into the env block at `codeSizeOff = 496`
  (`Evm64/Code/Basic.lean`), so CODESIZE is a pure read of that cell followed
  by a stack push — byte-for-byte the same shape as `CALLDATASIZE`/`MSIZE`,
  differing only in the env-block offset it loads from.

  The length always fits in 64 bits, so the value goes in the LOW limb of the
  pushed word and the upper three limbs are zero.

  Implementation (6 instructions = 24 bytes). The `ADDI` precedes the `LD`
  so that the emitted program matches the running `h_CODESIZE` dispatcher
  handler byte-for-byte (the two are independent — `LD` touches `tmpReg`,
  `ADDI` touches `x12` — so the ordering is a free choice that we pin to the
  handler's existing emission, keeping EEST conformance untouched):

    ADDI x12    x12        -32           -- decrement EVM stack pointer
    LD   tmpReg envBaseReg codeSizeOff   -- load codeSize into tmpReg
    SD   x12    tmpReg     0             -- write low limb (size value)
    SD   x12    x0         8             -- zero upper three limbs
    SD   x12    x0         16
    SD   x12    x0         24
-/

import EvmAsm.Rv64.Program
import EvmAsm.Rv64.SepLogic
import EvmAsm.Evm64.Code.Basic

namespace EvmAsm.Evm64
namespace Code

open EvmAsm.Rv64

/-- Parameterized RISC-V program implementing `CODESIZE`.
    `envBaseReg` holds the env-block base; `tmpReg` is a caller-saved
    temporary distinct from `x0`, `x12`, and `envBaseReg`.
    6 instructions = 24 bytes. -/
def evm_codesize (envBaseReg tmpReg : Reg) : Program :=
  ADDI .x12 .x12 (-32) ;;
  LD tmpReg envBaseReg (BitVec.ofNat 12 codeSizeOff) ;;
  SD .x12 tmpReg 0 ;;
  SD .x12 .x0 8 ;;
  SD .x12 .x0 16 ;;
  SD .x12 .x0 24

abbrev evm_codesize_code (envBaseReg tmpReg : Reg) (base : Word) : CodeReq :=
  CodeReq.ofProg base (evm_codesize envBaseReg tmpReg)

/-- `evm_codesize` is exactly 6 RISC-V instructions = 24 bytes. -/
theorem evm_codesize_length (envBaseReg tmpReg : Reg) :
    (evm_codesize envBaseReg tmpReg).length = 6 := by
  simp [evm_codesize, LD, ADDI, SD, single, seq, Program.length_append]

theorem evm_codesize_byte_length (envBaseReg tmpReg : Reg) :
    4 * (evm_codesize envBaseReg tmpReg).length = 24 := by
  rw [evm_codesize_length]

end Code
end EvmAsm.Evm64
