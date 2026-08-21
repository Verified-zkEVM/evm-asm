/-
  EvmAsm.Evm64.Calldata.SizeProgram

  RISC-V program implementing the EVM `CALLDATASIZE` opcode.

  CALLDATASIZE pushes the calldata byte length (held in the env block at
  `callDataLenOff = 424`) onto the EVM stack as a 256-bit word.  Because the
  length always fits in 64 bits in any realistic execution, the value goes
  in the LOW limb of the pushed word and the upper three limbs are zero —
  the same shape as `MSIZE`.

  Implementation (6 instructions = 24 bytes):

    LD   tmpReg envBaseReg callDataLenOff   -- load callDataLen into tmpReg
    ADDI x12    x12        -32              -- decrement EVM stack pointer
    SD   x12    tmpReg     0                -- write low limb (size value)
    SD   x12    x0         8                -- zero upper three limbs
    SD   x12    x0         16
    SD   x12    x0         24

  Slice 3 of issue #104 (parent `evm-asm-xjk8`, this slice
  `evm-asm-8mp7`).  Authored by @pirapira; implemented by Hermes-bot
  (evm-hermes).
-/

import EvmAsm.Rv64.Program
import EvmAsm.Rv64.SepLogic
import EvmAsm.Evm64.Environment.Layout

namespace EvmAsm.Evm64
namespace Calldata

open EvmAsm.Rv64
open EvmAsm.Evm64.EvmEnv (callDataLenOff)

/-- Parameterized RISC-V program implementing `CALLDATASIZE`.
    `envBaseReg` is the caller's environment-base register (the env block
    starts at `envBaseReg`); `tmpReg` is a caller-saved temporary
    distinct from `x0`, `x12`, and `envBaseReg`.
    6 instructions = 24 bytes. -/
def evm_calldatasize (envBaseReg tmpReg : Reg) : Program :=
  LD tmpReg envBaseReg (BitVec.ofNat 12 callDataLenOff) ;;
  ADDI .x12 .x12 (-32) ;;
  SD .x12 tmpReg 0 ;;
  SD .x12 .x0 8 ;;
  SD .x12 .x0 16 ;;
  SD .x12 .x0 24

abbrev evm_calldatasize_code (envBaseReg tmpReg : Reg) (base : Word) : CodeReq :=
  CodeReq.ofProg base (evm_calldatasize envBaseReg tmpReg)

/-- `evm_calldatasize` is exactly 6 RISC-V instructions = 24 bytes. -/
theorem evm_calldatasize_length (envBaseReg tmpReg : Reg) :
    (evm_calldatasize envBaseReg tmpReg).length = 6 := by
  simp [evm_calldatasize, LD, ADDI, SD, single, seq]

theorem evm_calldatasize_byte_length (envBaseReg tmpReg : Reg) :
    4 * (evm_calldatasize envBaseReg tmpReg).length = 24 := by
  rw [evm_calldatasize_length]

end Calldata
end EvmAsm.Evm64
