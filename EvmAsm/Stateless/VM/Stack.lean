/-
  EvmAsm.Stateless.VM.Stack

  Per-frame EVM value stack (1024 x 256-bit slots). The opcode
  handlers in `EvmAsm/Evm64/{Pop, Push, Dup, Swap}/Program.lean`
  already implement the per-opcode stack semantics. This file is
  the per-frame book-keeping shim:

  - `stackArenaBase` : low end of the value-stack arena.
  - `stackPtr ptr`   : value-stack pointer (`x12`) for `ptr` live items.

  Stack overflow (push when `ptr = 1024`) and underflow (pop when
  `ptr = 0`) are checked at opcode dispatch via fixed bounds; on
  violation the interpreter routes to a frame-level revert (NOT
  to `unimplemented_exit` -- stack errors are an STF outcome).

  ## Value-stack arena geometry (#9450)

  The arena is laid out low -> high as

      [ scratch slack ][ 1024 value-stack slots ]

  and is REUSED per message frame (the EVM value stack is reset on
  each CALL; the parent's `x12` is saved on `EVM_FRAME_STACK` across
  the call). `sp` points at the top operand; push decrements `sp`,
  pop increments it:

      ptr = 0    (empty)  : sp = stackArenaTop
      ptr = 1024 (full)   : sp = stackSlotsLow

  The below-`sp` opcode scratch (DivMod/SDiv/SMod/AddMod/Multiply)
  lives at `sp - K` for `K <= STACK_SCRATCH_SLACK`, i.e. inside the
  low slack margin -- never in the caller's EVM stack tail (the
  #9447 bug class) and never underflowing a neighbour region (#9450):
  at any legal `ptr`, `sp - STACK_SCRATCH_SLACK` is a valid, 8-byte
  aligned, in-frame address (see `stackScratchLow_ge_base`,
  `stackScratchLow_aligned8`).

  Working RAM: `EVM_VALUE_STACK` (1 MiB; the reused arena occupies
  `EVM_VALUE_STACK_FRAME_BYTES` = 33 024 B of it).
-/

import EvmAsm.Stateless.MemoryLayout

namespace EvmAsm.Stateless.VM.Stack

open EvmAsm.Rv64 (RAM_MEM_START RAM_MEM_END)
open EvmAsm.Stateless (EVM_VALUE_STACK STACK_SCRATCH_SLACK
                       EVM_VALUE_STACK_SLOTS EVM_VALUE_SLOT_BYTES
                       EVM_VALUE_STACK_FRAME_BYTES)

/-! ## Arena anchors (single source of truth: `MemoryLayout.lean`). -/

/-- Low end of the reused value-stack arena -- the start of the scratch
    slack margin. -/
def stackArenaBase : Nat := EVM_VALUE_STACK.toNat

/-- Lowest value-stack slot -- sits just above the scratch slack. This is
    the value-stack pointer when the stack is full (`ptr = 1024`). -/
def stackSlotsLow : Nat := stackArenaBase + STACK_SCRATCH_SLACK

/-- One past the top slot -- the value-stack pointer when the stack is
    empty (`ptr = 0`). -/
def stackArenaTop : Nat := stackArenaBase + EVM_VALUE_STACK_FRAME_BYTES

/-! ## Value-stack pointer. -/

/-- The value-stack pointer (`x12`) for `ptr` live items on the stack.
    `ptr = 0` is empty (`sp = stackArenaTop`); `ptr = 1024` is full
    (`sp = stackSlotsLow`). Defined for any `Nat`; callers guard
    `ptr <= EVM_VALUE_STACK_SLOTS` before use. -/
def stackPtr (ptr : Nat) : Nat :=
  stackSlotsLow + (EVM_VALUE_STACK_SLOTS - ptr) * EVM_VALUE_SLOT_BYTES

/-! ## Below-`sp` opcode scratch reach. -/

/-- Lowest address the deepest opcode scratch can reach at `ptr`, i.e.
    `stackPtr ptr - STACK_SCRATCH_SLACK`. The scratch margin of frame
    occupies `[stackScratchLow ptr, stackPtr ptr)`. -/
def stackScratchLow (ptr : Nat) : Nat :=
  stackArenaBase + (EVM_VALUE_STACK_SLOTS - ptr) * EVM_VALUE_SLOT_BYTES

/-- The live operand region occupies `[stackPtr ptr, stackArenaTop)`. -/
def stackOperandLow (ptr : Nat) : Nat := stackPtr ptr

/-! ## Geometry invariants (`#9450`).

   These are the load-bearing facts opcode specs reduce their
   `sp - K` validity checks to. All are checked by `decide` /
   `omega` over the concrete layout constants. -/

/-- The slot stride (`EVM_VALUE_SLOT_BYTES = 32`) is a multiple of 8, so
    any run of `k` slots is 8-byte aligned. Used to discharge the
    `isValidDwordAccess` precondition on `sp - K` scratch. -/
private theorem slot_stride_mod8 (ptr : Nat) :
    (EVM_VALUE_STACK_SLOTS - ptr) * EVM_VALUE_SLOT_BYTES % 8 = 0 := by
  have hslot : EVM_VALUE_SLOT_BYTES % 8 = 0 := by decide
  simp [Nat.mul_mod, hslot]

/-- Empty / full stack pointer boundaries. -/
theorem stackPtr_empty : stackPtr 0 = stackArenaTop := by decide

theorem stackPtr_full : stackPtr EVM_VALUE_STACK_SLOTS = stackSlotsLow := by decide

/-- `stackScratchLow ptr` agrees with `stackPtr ptr - STACK_SCRATCH_SLACK`
    for any `ptr` (the equality needs no depth hypothesis). -/
theorem stackScratchLow_eq (ptr : Nat) :
    stackScratchLow ptr = stackPtr ptr - STACK_SCRATCH_SLACK := by
  simp only [stackScratchLow, stackPtr, stackSlotsLow, stackArenaBase]
  omega

/-- The deepest opcode scratch stays at or above the arena base -- it
    never underflows into `EVM_FRAME_STACK` or any other neighbour region.
    Holds for any `ptr`, so in particular at a full stack (`ptr = 1024`). -/
theorem stackScratchLow_ge_base (ptr : Nat) :
    stackArenaBase ≤ stackScratchLow ptr := by
  simp only [stackScratchLow]; omega

/-- The scratch margin sits strictly below the live operand region, i.e.
    scratch never aliases a value-stack slot. -/
theorem stackScratchLow_lt_operandLow (ptr : Nat) :
    stackScratchLow ptr < stackOperandLow ptr := by
  have hslack : (0 : Nat) < STACK_SCRATCH_SLACK := by decide
  simp only [stackScratchLow, stackOperandLow, stackPtr, stackSlotsLow, stackArenaBase]
  omega

/-- Every value-stack pointer is 8-byte aligned, so every dword
    (`LD`/`SD`) access at `sp` is a valid `isValidDwordAccess`. -/
theorem stackPtr_aligned8 (ptr : Nat) : stackPtr ptr % 8 = 0 := by
  have hbase : EVM_VALUE_STACK.toNat % 8 = 0 := by decide
  have hslack : STACK_SCRATCH_SLACK % 8 = 0 := by decide
  have hstride := slot_stride_mod8 ptr
  simp only [stackPtr, stackSlotsLow, stackArenaBase]
  omega

/-- Every deepest-scratch address (`sp - STACK_SCRATCH_SLACK`) is 8-byte
    aligned, so the lowest opcode scratch cell is a valid dword access. -/
theorem stackScratchLow_aligned8 (ptr : Nat) : stackScratchLow ptr % 8 = 0 := by
  have hbase : EVM_VALUE_STACK.toNat % 8 = 0 := by decide
  have hstride := slot_stride_mod8 ptr
  simp only [stackScratchLow, stackArenaBase]
  omega

/-- The reused arena `[stackArenaBase, stackArenaTop)` lies inside the
    verified RAM zone. -/
theorem stackArena_in_ram :
    RAM_MEM_START ≤ stackArenaBase ∧ stackArenaTop ≤ RAM_MEM_END := by
  decide

end EvmAsm.Stateless.VM.Stack
