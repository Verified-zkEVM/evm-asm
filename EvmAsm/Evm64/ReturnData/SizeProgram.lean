/-
  EvmAsm.Evm64.ReturnData.SizeProgram

  RISC-V program implementing the EVM `RETURNDATASIZE` opcode (0x3d).

  RETURNDATASIZE pushes the size (in bytes) of the return data buffer from the
  most recent sub-call. The dispatcher seeds this size as a u64 in the
  `evm_precompile_frame` region at offset 8, so RETURNDATASIZE is a pure read
  of that cell followed by a stack push — the same shape as GAS/CODESIZE,
  differing only in the base register / offset loaded.

  The value fits in 64 bits, so it goes in the LOW limb of the pushed word and
  the upper three limbs are zero.

  Implementation (6 instructions = 24 bytes), ordered LD-then-ADDI to match the
  running `h_RETURNDATASIZE` dispatcher handler emission byte-for-byte:

    LD   tmpReg   frameReg returnDataSizeOff  -- load returndata size into tmpReg
    ADDI x12      x12      -32                -- decrement EVM stack pointer
    SD   x12      tmpReg   0                  -- write low limb (size value)
    SD   x12      x0       8                  -- zero upper three limbs
    SD   x12      x0       16
    SD   x12      x0       24
-/

import EvmAsm.Rv64.Program
import EvmAsm.Rv64.SepLogic

namespace EvmAsm.Evm64
namespace ReturnData

open EvmAsm.Rv64

/-- Byte offset of the u64 returndata size within the `evm_precompile_frame`
    region. Seeded by the dispatcher; RETURNDATASIZE reads it. -/
def returnDataSizeOff : Nat := 8

/-- Parameterized RISC-V program implementing `RETURNDATASIZE`.
    `frameReg` holds the `evm_precompile_frame` base; `tmpReg` is a caller-saved
    temporary distinct from `x0`, `x12`, and `frameReg`.
    6 instructions = 24 bytes. -/
def evm_returndatasize (frameReg tmpReg : Reg) : Program :=
  LD tmpReg frameReg (BitVec.ofNat 12 returnDataSizeOff) ;;
  ADDI .x12 .x12 (-32) ;;
  SD .x12 tmpReg 0 ;;
  SD .x12 .x0 8 ;;
  SD .x12 .x0 16 ;;
  SD .x12 .x0 24

abbrev evm_returndatasize_code (frameReg tmpReg : Reg) (base : Word) : CodeReq :=
  CodeReq.ofProg base (evm_returndatasize frameReg tmpReg)

/-- `evm_returndatasize` is exactly 6 RISC-V instructions = 24 bytes. -/
theorem evm_returndatasize_length (frameReg tmpReg : Reg) :
    (evm_returndatasize frameReg tmpReg).length = 6 := by
  simp [evm_returndatasize, LD, ADDI, SD, single, seq, Program.length_append]

theorem evm_returndatasize_byte_length (frameReg tmpReg : Reg) :
    4 * (evm_returndatasize frameReg tmpReg).length = 24 := by
  rw [evm_returndatasize_length]

end ReturnData
end EvmAsm.Evm64
