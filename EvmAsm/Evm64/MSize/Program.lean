/-
  EvmAsm.Evm64.MSize.Program

  256-bit EVM MSIZE: push the current memory high-water mark (in bytes,
  already 32-byte aligned) onto the EVM stack.

  The high-water mark is held in a single 8-byte cell at the address held
  in `sizeReg`, modelled by `evmMemSizeIs sizeLoc sizeBytes` in
  `Evm64/Memory.lean` (issue #99 slice 2). MSIZE itself is a pure read of
  that cell followed by a stack push.

  Implementation (6 instructions = 24 bytes):

    LD   tempReg sizeReg 0     -- load size cell into tempReg
    ADDI x12     x12     -32   -- decrement EVM stack pointer by 32
    SD   x12     tempReg 0     -- write low limb (size value)
    SD   x12     x0      8     -- zero upper three limbs
    SD   x12     x0      16
    SD   x12     x0      24

  `sizeReg` and `tempReg` are caller-chosen registers (not x0, not x12,
  distinct from each other). The size value is 64-bit and is placed in
  the LOW limb of the pushed 256-bit word; the upper three limbs are
  zero, which matches the EVM yellow paper's MSIZE return convention
  (memory size in bytes, fits in 64 bits).

  Slice 6 of issue #99. Authored by @pirapira; implemented by Hermes-bot
  (evm-hermes).
-/

import EvmAsm.Evm64.Stack

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- 256-bit EVM MSIZE program parameterized over the register holding the
    EVM memory-size cell address (`sizeReg`) and a scratch register
    (`tempReg`). 6 instructions = 24 bytes. -/
def evm_msize (sizeReg tempReg : Reg) : Program :=
  LD tempReg sizeReg 0 ;;
  ADDI .x12 .x12 (-32) ;;
  SD .x12 tempReg 0 ;;
  SD .x12 .x0 8 ;;
  SD .x12 .x0 16 ;;
  SD .x12 .x0 24

abbrev evm_msize_code (sizeReg tempReg : Reg) (base : Word) : CodeReq :=
  CodeReq.ofProg base (evm_msize sizeReg tempReg)

/-- Concrete instruction length of `evm_msize`. -/
theorem evm_msize_length (sizeReg tempReg : Reg) :
    (evm_msize sizeReg tempReg).length = 6 := by
  simp [evm_msize, LD, ADDI, SD, single, seq, Program.length_append]

/-- Concrete byte length of `evm_msize` when placed in RV64 code memory. -/
theorem evm_msize_byte_length (sizeReg tempReg : Reg) :
    4 * (evm_msize sizeReg tempReg).length = 24 := by
  rw [evm_msize_length]

/-- Byte offset of the MSIZE memory-size load instruction. -/
theorem evm_msize_load_byte_off : 4 * 0 = 0 := by
  rfl

/-- Byte offset of the MSIZE stack-pointer decrement instruction. -/
theorem evm_msize_push_byte_off : 4 * 1 = 4 := by
  rfl

/-- Byte offset of the MSIZE low-limb store instruction. -/
theorem evm_msize_low_limb_store_byte_off : 4 * 2 = 8 := by
  rfl

/-- Byte offset of the first MSIZE zero-limb store instruction. -/
theorem evm_msize_zero_limb1_store_byte_off : 4 * 3 = 12 := by
  rfl

/-- Byte offset of the second MSIZE zero-limb store instruction. -/
theorem evm_msize_zero_limb2_store_byte_off : 4 * 4 = 16 := by
  rfl

/-- Byte offset of the third MSIZE zero-limb store instruction. -/
theorem evm_msize_zero_limb3_store_byte_off : 4 * 5 = 20 := by
  rfl

/-- Byte offset immediately after the full MSIZE program. -/
theorem evm_msize_end_byte_off : 4 * 6 = 24 := by
  rfl

end EvmAsm.Evm64
