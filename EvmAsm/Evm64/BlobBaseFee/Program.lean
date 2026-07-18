/-
  EvmAsm.Evm64.BlobBaseFee.Program

  RISC-V program implementing the EVM `BLOBBASEFEE` opcode (0x4a, EIP-7516).

  BLOBBASEFEE pushes the current block's blob base fee. The dispatcher seeds
  the full 256-bit value into the env block at offset 512 (four 64-bit limbs,
  little-endian: 512, 520, 528, 536), so the opcode is a pure four-limb copy
  from the env block onto the EVM stack — structurally identical to the simple
  environment loads (`evm_env_load`), differing only in that the source cell is
  a dispatcher-seeded region rather than a typed `EvmEnv` field.

  Implementation (9 instructions = 36 bytes):

    ADDI x12    x12        -32                 -- decrement EVM stack pointer
    LD   tmpReg envBaseReg blobBaseFeeOff+0    -- limb 0
    SD   x12    tmpReg     0
    LD   tmpReg envBaseReg blobBaseFeeOff+8    -- limb 1
    SD   x12    tmpReg     8
    LD   tmpReg envBaseReg blobBaseFeeOff+16   -- limb 2
    SD   x12    tmpReg     16
    LD   tmpReg envBaseReg blobBaseFeeOff+24   -- limb 3
    SD   x12    tmpReg     24
-/

import EvmAsm.Rv64.Program
import EvmAsm.Rv64.SepLogic

namespace EvmAsm.Evm64
namespace BlobBaseFee

open EvmAsm.Rv64

/-- Byte offset of the `blobBaseFee` value (four 64-bit limbs) within the
    dispatcher env block. Seeded by the dispatcher prologue. -/
def blobBaseFeeOff : Nat := 512

/-- One limb block: load limb `i` from the env block, store it to the freshly
    allocated stack slot. 2 instructions. -/
def blobbasefee_one_limb (envBaseReg tmpReg : Reg) (i : Nat) : Program :=
  LD tmpReg envBaseReg (BitVec.ofNat 12 (blobBaseFeeOff + 8 * i)) ;;
  SD .x12 tmpReg (BitVec.ofNat 12 (8 * i))

/-- Parameterized RISC-V program implementing `BLOBBASEFEE`.
    `envBaseReg` holds the env-block base; `tmpReg` is a caller-saved
    temporary distinct from `x0`, `x12`, and `envBaseReg`.
    9 instructions = 36 bytes. -/
def evm_blobbasefee (envBaseReg tmpReg : Reg) : Program :=
  ADDI .x12 .x12 (-32) ;;
  blobbasefee_one_limb envBaseReg tmpReg 0 ;;
  blobbasefee_one_limb envBaseReg tmpReg 1 ;;
  blobbasefee_one_limb envBaseReg tmpReg 2 ;;
  blobbasefee_one_limb envBaseReg tmpReg 3

abbrev evm_blobbasefee_code (envBaseReg tmpReg : Reg) (base : Word) : CodeReq :=
  CodeReq.ofProg base (evm_blobbasefee envBaseReg tmpReg)

theorem blobbasefee_one_limb_length (envBaseReg tmpReg : Reg) (i : Nat) :
    (blobbasefee_one_limb envBaseReg tmpReg i).length = 2 := by
  simp [blobbasefee_one_limb, LD, SD, single, seq, Program.length_append]

/-- `evm_blobbasefee` is exactly 9 RISC-V instructions = 36 bytes. -/
theorem evm_blobbasefee_length (envBaseReg tmpReg : Reg) :
    (evm_blobbasefee envBaseReg tmpReg).length = 9 := by
  simp [evm_blobbasefee, blobbasefee_one_limb, LD, ADDI, SD, single, seq,
        Program.length_append]

theorem evm_blobbasefee_byte_length (envBaseReg tmpReg : Reg) :
    4 * (evm_blobbasefee envBaseReg tmpReg).length = 36 := by
  rw [evm_blobbasefee_length]

end BlobBaseFee
end EvmAsm.Evm64
