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

end EvmAsm.Evm64
