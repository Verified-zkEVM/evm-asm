/-
  EvmAsm.Evm64.Push.Program

  256-bit EVM PUSH1..PUSH32: read `n` immediate bytes from the EVM code
  region, zero-extend them (right-aligned, big-endian) into a 256-bit
  EvmWord, push the result onto the EVM stack.

  Calling convention for PUSH (slice 2 of #101):
    x10  — EVM code pointer (pointing at the PUSHn opcode byte; the
           immediate bytes live at +1 .. +n)
    x12  — EVM stack pointer (decremented by 32 to allocate the new top
           slot, in line with the rest of the Evm64 opcode subroutines)
    x0   — hardwired zero, used by SD to zero the four limbs in one go
    x7   — temporary, holds the LBU'd byte before the SB

  The PC advance for `x10` is intentionally NOT added in this slice;
  the design note (`docs/push-opcode-design.md`) defers the EVM-level
  "PC advances by 1+n" claim to the spec slices (#101 slice 4).

  Total RISC-V instructions: 5 + 2 * n.

  Authored by @pirapira; implemented by Hermes-bot (evm-hermes).
-/

import EvmAsm.Evm64.Stack

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Source byte offset for immediate byte `i` of a PUSHn instruction. The
    opcode itself is at offset 0, so immediates start at offset 1. -/
def pushByteSrcOffset (i : Nat) : Nat :=
  1 + i

/-- Destination byte offset in the newly allocated stack word for immediate
    byte `i` of PUSH width `n`. PUSH immediates are big-endian, while the
    stack word is stored little-endian in memory, so byte `i` lands at
    offset `n - 1 - i`. -/
def pushByteDstOffset (n i : Nat) : Nat :=
  n - 1 - i

theorem pushByteSrcOffset_pos (i : Nat) :
    0 < pushByteSrcOffset i := by
  unfold pushByteSrcOffset
  omega

theorem pushByteSrcOffset_le_32_of_lt {n i : Nat}
    (hn : n ≤ 32) (hi : i < n) :
    pushByteSrcOffset i ≤ 32 := by
  unfold pushByteSrcOffset
  omega

theorem pushByteDstOffset_lt_32_of_lt {n i : Nat}
    (hn : n ≤ 32) (hi : i < n) :
    pushByteDstOffset n i < 32 := by
  unfold pushByteDstOffset
  omega

theorem pushByteDstOffset_lt_width_of_lt {n i : Nat} (hi : i < n) :
    pushByteDstOffset n i < n := by
  unfold pushByteDstOffset
  omega

theorem push1Byte0SrcOffset : pushByteSrcOffset 0 = 1 := by
  rfl

theorem push1Byte0DstOffset : pushByteDstOffset 1 0 = 0 := by
  rfl

theorem push2Byte0SrcOffset : pushByteSrcOffset 0 = 1 := by
  rfl

theorem push2Byte0DstOffset : pushByteDstOffset 2 0 = 1 := by
  rfl

theorem push2Byte1SrcOffset : pushByteSrcOffset 1 = 2 := by
  rfl

theorem push2Byte1DstOffset : pushByteDstOffset 2 1 = 0 := by
  rfl

theorem push3Byte0SrcOffset : pushByteSrcOffset 0 = 1 := by
  rfl

theorem push3Byte0DstOffset : pushByteDstOffset 3 0 = 2 := by
  rfl

theorem push3Byte1SrcOffset : pushByteSrcOffset 1 = 2 := by
  rfl

theorem push3Byte1DstOffset : pushByteDstOffset 3 1 = 1 := by
  rfl

theorem push3Byte2SrcOffset : pushByteSrcOffset 2 = 3 := by
  rfl

theorem push3Byte2DstOffset : pushByteDstOffset 3 2 = 0 := by
  rfl

theorem push4Byte0SrcOffset : pushByteSrcOffset 0 = 1 := by
  rfl

theorem push4Byte0DstOffset : pushByteDstOffset 4 0 = 3 := by
  rfl

theorem push4Byte1SrcOffset : pushByteSrcOffset 1 = 2 := by
  rfl

theorem push4Byte1DstOffset : pushByteDstOffset 4 1 = 2 := by
  rfl

theorem push4Byte2SrcOffset : pushByteSrcOffset 2 = 3 := by
  rfl

theorem push4Byte2DstOffset : pushByteDstOffset 4 2 = 1 := by
  rfl

theorem push4Byte3SrcOffset : pushByteSrcOffset 3 = 4 := by
  rfl

theorem push4Byte3DstOffset : pushByteDstOffset 4 3 = 0 := by
  rfl

theorem push5Byte0SrcOffset : pushByteSrcOffset 0 = 1 := by
  rfl

theorem push5Byte0DstOffset : pushByteDstOffset 5 0 = 4 := by
  rfl

theorem push5Byte1SrcOffset : pushByteSrcOffset 1 = 2 := by
  rfl

theorem push5Byte1DstOffset : pushByteDstOffset 5 1 = 3 := by
  rfl

theorem push5Byte2SrcOffset : pushByteSrcOffset 2 = 3 := by
  rfl

theorem push5Byte2DstOffset : pushByteDstOffset 5 2 = 2 := by
  rfl

theorem push5Byte3SrcOffset : pushByteSrcOffset 3 = 4 := by
  rfl

theorem push5Byte3DstOffset : pushByteDstOffset 5 3 = 1 := by
  rfl

theorem push5Byte4SrcOffset : pushByteSrcOffset 4 = 5 := by
  rfl

theorem push5Byte4DstOffset : pushByteDstOffset 5 4 = 0 := by
  rfl

theorem push6Byte0SrcOffset : pushByteSrcOffset 0 = 1 := by
  rfl

theorem push6Byte0DstOffset : pushByteDstOffset 6 0 = 5 := by
  rfl

theorem push6Byte1SrcOffset : pushByteSrcOffset 1 = 2 := by
  rfl

theorem push6Byte1DstOffset : pushByteDstOffset 6 1 = 4 := by
  rfl

theorem push6Byte2SrcOffset : pushByteSrcOffset 2 = 3 := by
  rfl

theorem push6Byte2DstOffset : pushByteDstOffset 6 2 = 3 := by
  rfl

theorem push6Byte3SrcOffset : pushByteSrcOffset 3 = 4 := by
  rfl

theorem push6Byte3DstOffset : pushByteDstOffset 6 3 = 2 := by
  rfl

theorem push6Byte4SrcOffset : pushByteSrcOffset 4 = 5 := by
  rfl

theorem push6Byte4DstOffset : pushByteDstOffset 6 4 = 1 := by
  rfl

theorem push6Byte5SrcOffset : pushByteSrcOffset 5 = 6 := by
  rfl

theorem push6Byte5DstOffset : pushByteDstOffset 6 5 = 0 := by
  rfl

theorem push7Byte0SrcOffset : pushByteSrcOffset 0 = 1 := by
  rfl

theorem push7Byte0DstOffset : pushByteDstOffset 7 0 = 6 := by
  rfl

theorem push7Byte1SrcOffset : pushByteSrcOffset 1 = 2 := by
  rfl

theorem push7Byte1DstOffset : pushByteDstOffset 7 1 = 5 := by
  rfl

theorem push7Byte2SrcOffset : pushByteSrcOffset 2 = 3 := by
  rfl

theorem push7Byte2DstOffset : pushByteDstOffset 7 2 = 4 := by
  rfl

theorem push7Byte3SrcOffset : pushByteSrcOffset 3 = 4 := by
  rfl

theorem push7Byte3DstOffset : pushByteDstOffset 7 3 = 3 := by
  rfl

theorem push7Byte4SrcOffset : pushByteSrcOffset 4 = 5 := by
  rfl

theorem push7Byte4DstOffset : pushByteDstOffset 7 4 = 2 := by
  rfl

theorem push7Byte5SrcOffset : pushByteSrcOffset 5 = 6 := by
  rfl

theorem push7Byte5DstOffset : pushByteDstOffset 7 5 = 1 := by
  rfl

theorem push7Byte6SrcOffset : pushByteSrcOffset 6 = 7 := by
  rfl

theorem push7Byte6DstOffset : pushByteDstOffset 7 6 = 0 := by
  rfl

theorem push8Byte0SrcOffset : pushByteSrcOffset 0 = 1 := by
  rfl

theorem push8Byte0DstOffset : pushByteDstOffset 8 0 = 7 := by
  rfl

theorem push8Byte1SrcOffset : pushByteSrcOffset 1 = 2 := by
  rfl

theorem push8Byte1DstOffset : pushByteDstOffset 8 1 = 6 := by
  rfl

theorem push8Byte2SrcOffset : pushByteSrcOffset 2 = 3 := by
  rfl

theorem push8Byte2DstOffset : pushByteDstOffset 8 2 = 5 := by
  rfl

theorem push8Byte3SrcOffset : pushByteSrcOffset 3 = 4 := by
  rfl

theorem push8Byte3DstOffset : pushByteDstOffset 8 3 = 4 := by
  rfl

theorem push8Byte4SrcOffset : pushByteSrcOffset 4 = 5 := by
  rfl

theorem push8Byte4DstOffset : pushByteDstOffset 8 4 = 3 := by
  rfl

theorem push8Byte5SrcOffset : pushByteSrcOffset 5 = 6 := by
  rfl

theorem push8Byte5DstOffset : pushByteDstOffset 8 5 = 2 := by
  rfl

theorem push8Byte6SrcOffset : pushByteSrcOffset 6 = 7 := by
  rfl

theorem push8Byte6DstOffset : pushByteDstOffset 8 6 = 1 := by
  rfl

theorem push8Byte7SrcOffset : pushByteSrcOffset 7 = 8 := by
  rfl

theorem push8Byte7DstOffset : pushByteDstOffset 8 7 = 0 := by
  rfl

theorem push9Byte0SrcOffset : pushByteSrcOffset 0 = 1 := by
  rfl

theorem push9Byte0DstOffset : pushByteDstOffset 9 0 = 8 := by
  rfl

theorem push9Byte1SrcOffset : pushByteSrcOffset 1 = 2 := by
  rfl

theorem push9Byte1DstOffset : pushByteDstOffset 9 1 = 7 := by
  rfl

theorem push9Byte2SrcOffset : pushByteSrcOffset 2 = 3 := by
  rfl

theorem push9Byte2DstOffset : pushByteDstOffset 9 2 = 6 := by
  rfl

theorem push9Byte3SrcOffset : pushByteSrcOffset 3 = 4 := by
  rfl

theorem push9Byte3DstOffset : pushByteDstOffset 9 3 = 5 := by
  rfl

theorem push9Byte4SrcOffset : pushByteSrcOffset 4 = 5 := by
  rfl

theorem push9Byte4DstOffset : pushByteDstOffset 9 4 = 4 := by
  rfl

theorem push9Byte5SrcOffset : pushByteSrcOffset 5 = 6 := by
  rfl

theorem push9Byte5DstOffset : pushByteDstOffset 9 5 = 3 := by
  rfl

theorem push9Byte6SrcOffset : pushByteSrcOffset 6 = 7 := by
  rfl

theorem push9Byte6DstOffset : pushByteDstOffset 9 6 = 2 := by
  rfl

theorem push9Byte7SrcOffset : pushByteSrcOffset 7 = 8 := by
  rfl

theorem push9Byte7DstOffset : pushByteDstOffset 9 7 = 1 := by
  rfl

theorem push9Byte8SrcOffset : pushByteSrcOffset 8 = 9 := by
  rfl

theorem push9Byte8DstOffset : pushByteDstOffset 9 8 = 0 := by
  rfl

theorem push10Byte0SrcOffset : pushByteSrcOffset 0 = 1 := by
  rfl

theorem push10Byte0DstOffset : pushByteDstOffset 10 0 = 9 := by
  rfl

theorem push10Byte1SrcOffset : pushByteSrcOffset 1 = 2 := by
  rfl

theorem push10Byte1DstOffset : pushByteDstOffset 10 1 = 8 := by
  rfl

theorem push10Byte2SrcOffset : pushByteSrcOffset 2 = 3 := by
  rfl

theorem push10Byte2DstOffset : pushByteDstOffset 10 2 = 7 := by
  rfl

theorem push10Byte3SrcOffset : pushByteSrcOffset 3 = 4 := by
  rfl

theorem push10Byte3DstOffset : pushByteDstOffset 10 3 = 6 := by
  rfl

theorem push10Byte4SrcOffset : pushByteSrcOffset 4 = 5 := by
  rfl

theorem push10Byte4DstOffset : pushByteDstOffset 10 4 = 5 := by
  rfl

theorem push10Byte5SrcOffset : pushByteSrcOffset 5 = 6 := by
  rfl

theorem push10Byte5DstOffset : pushByteDstOffset 10 5 = 4 := by
  rfl

theorem push10Byte6SrcOffset : pushByteSrcOffset 6 = 7 := by
  rfl

theorem push10Byte6DstOffset : pushByteDstOffset 10 6 = 3 := by
  rfl

theorem push10Byte7SrcOffset : pushByteSrcOffset 7 = 8 := by
  rfl

theorem push10Byte7DstOffset : pushByteDstOffset 10 7 = 2 := by
  rfl

theorem push10Byte8SrcOffset : pushByteSrcOffset 8 = 9 := by
  rfl

theorem push10Byte8DstOffset : pushByteDstOffset 10 8 = 1 := by
  rfl

theorem push10Byte9SrcOffset : pushByteSrcOffset 9 = 10 := by
  rfl

theorem push10Byte9DstOffset : pushByteDstOffset 10 9 = 0 := by
  rfl

theorem push11Byte0SrcOffset : pushByteSrcOffset 0 = 1 := by
  rfl

theorem push11Byte0DstOffset : pushByteDstOffset 11 0 = 10 := by
  rfl

theorem push11Byte1SrcOffset : pushByteSrcOffset 1 = 2 := by
  rfl

theorem push11Byte1DstOffset : pushByteDstOffset 11 1 = 9 := by
  rfl

theorem push11Byte2SrcOffset : pushByteSrcOffset 2 = 3 := by
  rfl

theorem push11Byte2DstOffset : pushByteDstOffset 11 2 = 8 := by
  rfl

theorem push11Byte3SrcOffset : pushByteSrcOffset 3 = 4 := by
  rfl

theorem push11Byte3DstOffset : pushByteDstOffset 11 3 = 7 := by
  rfl

theorem push11Byte4SrcOffset : pushByteSrcOffset 4 = 5 := by
  rfl

theorem push11Byte4DstOffset : pushByteDstOffset 11 4 = 6 := by
  rfl

theorem push11Byte5SrcOffset : pushByteSrcOffset 5 = 6 := by
  rfl

theorem push11Byte5DstOffset : pushByteDstOffset 11 5 = 5 := by
  rfl

theorem push11Byte6SrcOffset : pushByteSrcOffset 6 = 7 := by
  rfl

theorem push11Byte6DstOffset : pushByteDstOffset 11 6 = 4 := by
  rfl

theorem push11Byte7SrcOffset : pushByteSrcOffset 7 = 8 := by
  rfl

theorem push11Byte7DstOffset : pushByteDstOffset 11 7 = 3 := by
  rfl

theorem push11Byte8SrcOffset : pushByteSrcOffset 8 = 9 := by
  rfl

theorem push11Byte8DstOffset : pushByteDstOffset 11 8 = 2 := by
  rfl

theorem push11Byte9SrcOffset : pushByteSrcOffset 9 = 10 := by
  rfl

theorem push11Byte9DstOffset : pushByteDstOffset 11 9 = 1 := by
  rfl

theorem push11Byte10SrcOffset : pushByteSrcOffset 10 = 11 := by
  rfl

theorem push11Byte10DstOffset : pushByteDstOffset 11 10 = 0 := by
  rfl

theorem push12Byte0SrcOffset : pushByteSrcOffset 0 = 1 := by
  rfl

theorem push12Byte0DstOffset : pushByteDstOffset 12 0 = 11 := by
  rfl

theorem push12Byte1SrcOffset : pushByteSrcOffset 1 = 2 := by
  rfl

theorem push12Byte1DstOffset : pushByteDstOffset 12 1 = 10 := by
  rfl

theorem push12Byte2SrcOffset : pushByteSrcOffset 2 = 3 := by
  rfl

theorem push12Byte2DstOffset : pushByteDstOffset 12 2 = 9 := by
  rfl

theorem push12Byte3SrcOffset : pushByteSrcOffset 3 = 4 := by
  rfl

theorem push12Byte3DstOffset : pushByteDstOffset 12 3 = 8 := by
  rfl

theorem push12Byte4SrcOffset : pushByteSrcOffset 4 = 5 := by
  rfl

theorem push12Byte4DstOffset : pushByteDstOffset 12 4 = 7 := by
  rfl

theorem push12Byte5SrcOffset : pushByteSrcOffset 5 = 6 := by
  rfl

theorem push12Byte5DstOffset : pushByteDstOffset 12 5 = 6 := by
  rfl

theorem push12Byte6SrcOffset : pushByteSrcOffset 6 = 7 := by
  rfl

theorem push12Byte6DstOffset : pushByteDstOffset 12 6 = 5 := by
  rfl

theorem push12Byte7SrcOffset : pushByteSrcOffset 7 = 8 := by
  rfl

theorem push12Byte7DstOffset : pushByteDstOffset 12 7 = 4 := by
  rfl

theorem push12Byte8SrcOffset : pushByteSrcOffset 8 = 9 := by
  rfl

theorem push12Byte8DstOffset : pushByteDstOffset 12 8 = 3 := by
  rfl

theorem push12Byte9SrcOffset : pushByteSrcOffset 9 = 10 := by
  rfl

theorem push12Byte9DstOffset : pushByteDstOffset 12 9 = 2 := by
  rfl

theorem push12Byte10SrcOffset : pushByteSrcOffset 10 = 11 := by
  rfl

theorem push12Byte10DstOffset : pushByteDstOffset 12 10 = 1 := by
  rfl

theorem push12Byte11SrcOffset : pushByteSrcOffset 11 = 12 := by
  rfl

theorem push12Byte11DstOffset : pushByteDstOffset 12 11 = 0 := by
  rfl

theorem push13Byte0SrcOffset : pushByteSrcOffset 0 = 1 := by
  rfl

theorem push13Byte0DstOffset : pushByteDstOffset 13 0 = 12 := by
  rfl

theorem push13Byte1SrcOffset : pushByteSrcOffset 1 = 2 := by
  rfl

theorem push13Byte1DstOffset : pushByteDstOffset 13 1 = 11 := by
  rfl

theorem push13Byte2SrcOffset : pushByteSrcOffset 2 = 3 := by
  rfl

theorem push13Byte2DstOffset : pushByteDstOffset 13 2 = 10 := by
  rfl

theorem push13Byte3SrcOffset : pushByteSrcOffset 3 = 4 := by
  rfl

theorem push13Byte3DstOffset : pushByteDstOffset 13 3 = 9 := by
  rfl

theorem push13Byte4SrcOffset : pushByteSrcOffset 4 = 5 := by
  rfl

theorem push13Byte4DstOffset : pushByteDstOffset 13 4 = 8 := by
  rfl

theorem push13Byte5SrcOffset : pushByteSrcOffset 5 = 6 := by
  rfl

theorem push13Byte5DstOffset : pushByteDstOffset 13 5 = 7 := by
  rfl

theorem push13Byte6SrcOffset : pushByteSrcOffset 6 = 7 := by
  rfl

theorem push13Byte6DstOffset : pushByteDstOffset 13 6 = 6 := by
  rfl

theorem push13Byte7SrcOffset : pushByteSrcOffset 7 = 8 := by
  rfl

theorem push13Byte7DstOffset : pushByteDstOffset 13 7 = 5 := by
  rfl

theorem push13Byte8SrcOffset : pushByteSrcOffset 8 = 9 := by
  rfl

theorem push13Byte8DstOffset : pushByteDstOffset 13 8 = 4 := by
  rfl

theorem push13Byte9SrcOffset : pushByteSrcOffset 9 = 10 := by
  rfl

theorem push13Byte9DstOffset : pushByteDstOffset 13 9 = 3 := by
  rfl

theorem push13Byte10SrcOffset : pushByteSrcOffset 10 = 11 := by
  rfl

theorem push13Byte10DstOffset : pushByteDstOffset 13 10 = 2 := by
  rfl

theorem push13Byte11SrcOffset : pushByteSrcOffset 11 = 12 := by
  rfl

theorem push13Byte11DstOffset : pushByteDstOffset 13 11 = 1 := by
  rfl

theorem push13Byte12SrcOffset : pushByteSrcOffset 12 = 13 := by
  rfl

theorem push13Byte12DstOffset : pushByteDstOffset 13 12 = 0 := by
  rfl

theorem push14Byte0SrcOffset : pushByteSrcOffset 0 = 1 := by
  rfl

theorem push14Byte0DstOffset : pushByteDstOffset 14 0 = 13 := by
  rfl

theorem push14Byte1SrcOffset : pushByteSrcOffset 1 = 2 := by
  rfl

theorem push14Byte1DstOffset : pushByteDstOffset 14 1 = 12 := by
  rfl

theorem push14Byte2SrcOffset : pushByteSrcOffset 2 = 3 := by
  rfl

theorem push14Byte2DstOffset : pushByteDstOffset 14 2 = 11 := by
  rfl

theorem push14Byte3SrcOffset : pushByteSrcOffset 3 = 4 := by
  rfl

theorem push14Byte3DstOffset : pushByteDstOffset 14 3 = 10 := by
  rfl

theorem push14Byte4SrcOffset : pushByteSrcOffset 4 = 5 := by
  rfl

theorem push14Byte4DstOffset : pushByteDstOffset 14 4 = 9 := by
  rfl

theorem push14Byte5SrcOffset : pushByteSrcOffset 5 = 6 := by
  rfl

theorem push14Byte5DstOffset : pushByteDstOffset 14 5 = 8 := by
  rfl

theorem push14Byte6SrcOffset : pushByteSrcOffset 6 = 7 := by
  rfl

theorem push14Byte6DstOffset : pushByteDstOffset 14 6 = 7 := by
  rfl

theorem push14Byte7SrcOffset : pushByteSrcOffset 7 = 8 := by
  rfl

theorem push14Byte7DstOffset : pushByteDstOffset 14 7 = 6 := by
  rfl

theorem push14Byte8SrcOffset : pushByteSrcOffset 8 = 9 := by
  rfl

theorem push14Byte8DstOffset : pushByteDstOffset 14 8 = 5 := by
  rfl

theorem push14Byte9SrcOffset : pushByteSrcOffset 9 = 10 := by
  rfl

theorem push14Byte9DstOffset : pushByteDstOffset 14 9 = 4 := by
  rfl

theorem push14Byte10SrcOffset : pushByteSrcOffset 10 = 11 := by
  rfl

theorem push14Byte10DstOffset : pushByteDstOffset 14 10 = 3 := by
  rfl

theorem push14Byte11SrcOffset : pushByteSrcOffset 11 = 12 := by
  rfl

theorem push14Byte11DstOffset : pushByteDstOffset 14 11 = 2 := by
  rfl

theorem push14Byte12SrcOffset : pushByteSrcOffset 12 = 13 := by
  rfl

theorem push14Byte12DstOffset : pushByteDstOffset 14 12 = 1 := by
  rfl

theorem push14Byte13SrcOffset : pushByteSrcOffset 13 = 14 := by
  rfl

theorem push14Byte13DstOffset : pushByteDstOffset 14 13 = 0 := by
  rfl

theorem push15Byte0SrcOffset : pushByteSrcOffset 0 = 1 := by
  rfl

theorem push15Byte0DstOffset : pushByteDstOffset 15 0 = 14 := by
  rfl

theorem push15Byte1SrcOffset : pushByteSrcOffset 1 = 2 := by
  rfl

theorem push15Byte1DstOffset : pushByteDstOffset 15 1 = 13 := by
  rfl

theorem push15Byte2SrcOffset : pushByteSrcOffset 2 = 3 := by
  rfl

theorem push15Byte2DstOffset : pushByteDstOffset 15 2 = 12 := by
  rfl

theorem push15Byte3SrcOffset : pushByteSrcOffset 3 = 4 := by
  rfl

theorem push15Byte3DstOffset : pushByteDstOffset 15 3 = 11 := by
  rfl

theorem push15Byte4SrcOffset : pushByteSrcOffset 4 = 5 := by
  rfl

theorem push15Byte4DstOffset : pushByteDstOffset 15 4 = 10 := by
  rfl

theorem push15Byte5SrcOffset : pushByteSrcOffset 5 = 6 := by
  rfl

theorem push15Byte5DstOffset : pushByteDstOffset 15 5 = 9 := by
  rfl

theorem push15Byte6SrcOffset : pushByteSrcOffset 6 = 7 := by
  rfl

theorem push15Byte6DstOffset : pushByteDstOffset 15 6 = 8 := by
  rfl

theorem push15Byte7SrcOffset : pushByteSrcOffset 7 = 8 := by
  rfl

theorem push15Byte7DstOffset : pushByteDstOffset 15 7 = 7 := by
  rfl

theorem push15Byte8SrcOffset : pushByteSrcOffset 8 = 9 := by
  rfl

theorem push15Byte8DstOffset : pushByteDstOffset 15 8 = 6 := by
  rfl

theorem push15Byte9SrcOffset : pushByteSrcOffset 9 = 10 := by
  rfl

theorem push15Byte9DstOffset : pushByteDstOffset 15 9 = 5 := by
  rfl

theorem push15Byte10SrcOffset : pushByteSrcOffset 10 = 11 := by
  rfl

theorem push15Byte10DstOffset : pushByteDstOffset 15 10 = 4 := by
  rfl

theorem push15Byte11SrcOffset : pushByteSrcOffset 11 = 12 := by
  rfl

theorem push15Byte11DstOffset : pushByteDstOffset 15 11 = 3 := by
  rfl

theorem push15Byte12SrcOffset : pushByteSrcOffset 12 = 13 := by
  rfl

theorem push15Byte12DstOffset : pushByteDstOffset 15 12 = 2 := by
  rfl

theorem push15Byte13SrcOffset : pushByteSrcOffset 13 = 14 := by
  rfl

theorem push15Byte13DstOffset : pushByteDstOffset 15 13 = 1 := by
  rfl

theorem push15Byte14SrcOffset : pushByteSrcOffset 14 = 15 := by
  rfl

theorem push15Byte14DstOffset : pushByteDstOffset 15 14 = 0 := by
  rfl

theorem push16Byte0SrcOffset : pushByteSrcOffset 0 = 1 := by
  rfl

theorem push16Byte0DstOffset : pushByteDstOffset 16 0 = 15 := by
  rfl

theorem push16Byte1SrcOffset : pushByteSrcOffset 1 = 2 := by
  rfl

theorem push16Byte1DstOffset : pushByteDstOffset 16 1 = 14 := by
  rfl

theorem push16Byte2SrcOffset : pushByteSrcOffset 2 = 3 := by
  rfl

theorem push16Byte2DstOffset : pushByteDstOffset 16 2 = 13 := by
  rfl

theorem push16Byte3SrcOffset : pushByteSrcOffset 3 = 4 := by
  rfl

theorem push16Byte3DstOffset : pushByteDstOffset 16 3 = 12 := by
  rfl

theorem push16Byte4SrcOffset : pushByteSrcOffset 4 = 5 := by
  rfl

theorem push16Byte4DstOffset : pushByteDstOffset 16 4 = 11 := by
  rfl

theorem push16Byte5SrcOffset : pushByteSrcOffset 5 = 6 := by
  rfl

theorem push16Byte5DstOffset : pushByteDstOffset 16 5 = 10 := by
  rfl

theorem push16Byte6SrcOffset : pushByteSrcOffset 6 = 7 := by
  rfl

theorem push16Byte6DstOffset : pushByteDstOffset 16 6 = 9 := by
  rfl

theorem push16Byte7SrcOffset : pushByteSrcOffset 7 = 8 := by
  rfl

theorem push16Byte7DstOffset : pushByteDstOffset 16 7 = 8 := by
  rfl

theorem push16Byte8SrcOffset : pushByteSrcOffset 8 = 9 := by
  rfl

theorem push16Byte8DstOffset : pushByteDstOffset 16 8 = 7 := by
  rfl

theorem push16Byte9SrcOffset : pushByteSrcOffset 9 = 10 := by
  rfl

theorem push16Byte9DstOffset : pushByteDstOffset 16 9 = 6 := by
  rfl

theorem push16Byte10SrcOffset : pushByteSrcOffset 10 = 11 := by
  rfl

theorem push16Byte10DstOffset : pushByteDstOffset 16 10 = 5 := by
  rfl

theorem push16Byte11SrcOffset : pushByteSrcOffset 11 = 12 := by
  rfl

theorem push16Byte11DstOffset : pushByteDstOffset 16 11 = 4 := by
  rfl

theorem push16Byte12SrcOffset : pushByteSrcOffset 12 = 13 := by
  rfl

theorem push16Byte12DstOffset : pushByteDstOffset 16 12 = 3 := by
  rfl

theorem push16Byte13SrcOffset : pushByteSrcOffset 13 = 14 := by
  rfl

theorem push16Byte13DstOffset : pushByteDstOffset 16 13 = 2 := by
  rfl

theorem push16Byte14SrcOffset : pushByteSrcOffset 14 = 15 := by
  rfl

theorem push16Byte14DstOffset : pushByteDstOffset 16 14 = 1 := by
  rfl

theorem push16Byte15SrcOffset : pushByteSrcOffset 15 = 16 := by
  rfl

theorem push16Byte15DstOffset : pushByteDstOffset 16 15 = 0 := by
  rfl

theorem push17Byte0SrcOffset : pushByteSrcOffset 0 = 1 := by
  rfl

theorem push17Byte0DstOffset : pushByteDstOffset 17 0 = 16 := by
  rfl

theorem push17Byte1SrcOffset : pushByteSrcOffset 1 = 2 := by
  rfl

theorem push17Byte1DstOffset : pushByteDstOffset 17 1 = 15 := by
  rfl

theorem push17Byte2SrcOffset : pushByteSrcOffset 2 = 3 := by
  rfl

theorem push17Byte2DstOffset : pushByteDstOffset 17 2 = 14 := by
  rfl

theorem push17Byte3SrcOffset : pushByteSrcOffset 3 = 4 := by
  rfl

theorem push17Byte3DstOffset : pushByteDstOffset 17 3 = 13 := by
  rfl

theorem push17Byte4SrcOffset : pushByteSrcOffset 4 = 5 := by
  rfl

theorem push17Byte4DstOffset : pushByteDstOffset 17 4 = 12 := by
  rfl

theorem push17Byte5SrcOffset : pushByteSrcOffset 5 = 6 := by
  rfl

theorem push17Byte5DstOffset : pushByteDstOffset 17 5 = 11 := by
  rfl

theorem push17Byte6SrcOffset : pushByteSrcOffset 6 = 7 := by
  rfl

theorem push17Byte6DstOffset : pushByteDstOffset 17 6 = 10 := by
  rfl

theorem push17Byte7SrcOffset : pushByteSrcOffset 7 = 8 := by
  rfl

theorem push17Byte7DstOffset : pushByteDstOffset 17 7 = 9 := by
  rfl

theorem push17Byte8SrcOffset : pushByteSrcOffset 8 = 9 := by
  rfl

theorem push17Byte8DstOffset : pushByteDstOffset 17 8 = 8 := by
  rfl

theorem push17Byte9SrcOffset : pushByteSrcOffset 9 = 10 := by
  rfl

theorem push17Byte9DstOffset : pushByteDstOffset 17 9 = 7 := by
  rfl

theorem push17Byte10SrcOffset : pushByteSrcOffset 10 = 11 := by
  rfl

theorem push17Byte10DstOffset : pushByteDstOffset 17 10 = 6 := by
  rfl

theorem push17Byte11SrcOffset : pushByteSrcOffset 11 = 12 := by
  rfl

theorem push17Byte11DstOffset : pushByteDstOffset 17 11 = 5 := by
  rfl

theorem push17Byte12SrcOffset : pushByteSrcOffset 12 = 13 := by
  rfl

theorem push17Byte12DstOffset : pushByteDstOffset 17 12 = 4 := by
  rfl

theorem push17Byte13SrcOffset : pushByteSrcOffset 13 = 14 := by
  rfl

theorem push17Byte13DstOffset : pushByteDstOffset 17 13 = 3 := by
  rfl

theorem push17Byte14SrcOffset : pushByteSrcOffset 14 = 15 := by
  rfl

theorem push17Byte14DstOffset : pushByteDstOffset 17 14 = 2 := by
  rfl

theorem push17Byte15SrcOffset : pushByteSrcOffset 15 = 16 := by
  rfl

theorem push17Byte15DstOffset : pushByteDstOffset 17 15 = 1 := by
  rfl

theorem push17Byte16SrcOffset : pushByteSrcOffset 16 = 17 := by
  rfl

theorem push17Byte16DstOffset : pushByteDstOffset 17 16 = 0 := by
  rfl

theorem push18Byte0SrcOffset : pushByteSrcOffset 0 = 1 := by
  rfl

theorem push18Byte0DstOffset : pushByteDstOffset 18 0 = 17 := by
  rfl

theorem push18Byte1SrcOffset : pushByteSrcOffset 1 = 2 := by
  rfl

theorem push18Byte1DstOffset : pushByteDstOffset 18 1 = 16 := by
  rfl

theorem push18Byte2SrcOffset : pushByteSrcOffset 2 = 3 := by
  rfl

theorem push18Byte2DstOffset : pushByteDstOffset 18 2 = 15 := by
  rfl

theorem push18Byte3SrcOffset : pushByteSrcOffset 3 = 4 := by
  rfl

theorem push18Byte3DstOffset : pushByteDstOffset 18 3 = 14 := by
  rfl

theorem push18Byte4SrcOffset : pushByteSrcOffset 4 = 5 := by
  rfl

theorem push18Byte4DstOffset : pushByteDstOffset 18 4 = 13 := by
  rfl

theorem push18Byte5SrcOffset : pushByteSrcOffset 5 = 6 := by
  rfl

theorem push18Byte5DstOffset : pushByteDstOffset 18 5 = 12 := by
  rfl

theorem push18Byte6SrcOffset : pushByteSrcOffset 6 = 7 := by
  rfl

theorem push18Byte6DstOffset : pushByteDstOffset 18 6 = 11 := by
  rfl

theorem push18Byte7SrcOffset : pushByteSrcOffset 7 = 8 := by
  rfl

theorem push18Byte7DstOffset : pushByteDstOffset 18 7 = 10 := by
  rfl

theorem push18Byte8SrcOffset : pushByteSrcOffset 8 = 9 := by
  rfl

theorem push18Byte8DstOffset : pushByteDstOffset 18 8 = 9 := by
  rfl

theorem push18Byte9SrcOffset : pushByteSrcOffset 9 = 10 := by
  rfl

theorem push18Byte9DstOffset : pushByteDstOffset 18 9 = 8 := by
  rfl

theorem push18Byte10SrcOffset : pushByteSrcOffset 10 = 11 := by
  rfl

theorem push18Byte10DstOffset : pushByteDstOffset 18 10 = 7 := by
  rfl

theorem push18Byte11SrcOffset : pushByteSrcOffset 11 = 12 := by
  rfl

theorem push18Byte11DstOffset : pushByteDstOffset 18 11 = 6 := by
  rfl

theorem push18Byte12SrcOffset : pushByteSrcOffset 12 = 13 := by
  rfl

theorem push18Byte12DstOffset : pushByteDstOffset 18 12 = 5 := by
  rfl

theorem push18Byte13SrcOffset : pushByteSrcOffset 13 = 14 := by
  rfl

theorem push18Byte13DstOffset : pushByteDstOffset 18 13 = 4 := by
  rfl

theorem push18Byte14SrcOffset : pushByteSrcOffset 14 = 15 := by
  rfl

theorem push18Byte14DstOffset : pushByteDstOffset 18 14 = 3 := by
  rfl

theorem push18Byte15SrcOffset : pushByteSrcOffset 15 = 16 := by
  rfl

theorem push18Byte15DstOffset : pushByteDstOffset 18 15 = 2 := by
  rfl

theorem push18Byte16SrcOffset : pushByteSrcOffset 16 = 17 := by
  rfl

theorem push18Byte16DstOffset : pushByteDstOffset 18 16 = 1 := by
  rfl

theorem push18Byte17SrcOffset : pushByteSrcOffset 17 = 18 := by
  rfl

theorem push18Byte17DstOffset : pushByteDstOffset 18 17 = 0 := by
  rfl

theorem push19Byte0SrcOffset : pushByteSrcOffset 0 = 1 := by
  rfl

theorem push19Byte0DstOffset : pushByteDstOffset 19 0 = 18 := by
  rfl

theorem push19Byte1SrcOffset : pushByteSrcOffset 1 = 2 := by
  rfl

theorem push19Byte1DstOffset : pushByteDstOffset 19 1 = 17 := by
  rfl

theorem push19Byte2SrcOffset : pushByteSrcOffset 2 = 3 := by
  rfl

theorem push19Byte2DstOffset : pushByteDstOffset 19 2 = 16 := by
  rfl

theorem push19Byte3SrcOffset : pushByteSrcOffset 3 = 4 := by
  rfl

theorem push19Byte3DstOffset : pushByteDstOffset 19 3 = 15 := by
  rfl

theorem push19Byte4SrcOffset : pushByteSrcOffset 4 = 5 := by
  rfl

theorem push19Byte4DstOffset : pushByteDstOffset 19 4 = 14 := by
  rfl

theorem push19Byte5SrcOffset : pushByteSrcOffset 5 = 6 := by
  rfl

theorem push19Byte5DstOffset : pushByteDstOffset 19 5 = 13 := by
  rfl

theorem push19Byte6SrcOffset : pushByteSrcOffset 6 = 7 := by
  rfl

theorem push19Byte6DstOffset : pushByteDstOffset 19 6 = 12 := by
  rfl

theorem push19Byte7SrcOffset : pushByteSrcOffset 7 = 8 := by
  rfl

theorem push19Byte7DstOffset : pushByteDstOffset 19 7 = 11 := by
  rfl

theorem push19Byte8SrcOffset : pushByteSrcOffset 8 = 9 := by
  rfl

theorem push19Byte8DstOffset : pushByteDstOffset 19 8 = 10 := by
  rfl

theorem push19Byte9SrcOffset : pushByteSrcOffset 9 = 10 := by
  rfl

theorem push19Byte9DstOffset : pushByteDstOffset 19 9 = 9 := by
  rfl

theorem push19Byte10SrcOffset : pushByteSrcOffset 10 = 11 := by
  rfl

theorem push19Byte10DstOffset : pushByteDstOffset 19 10 = 8 := by
  rfl

theorem push19Byte11SrcOffset : pushByteSrcOffset 11 = 12 := by
  rfl

theorem push19Byte11DstOffset : pushByteDstOffset 19 11 = 7 := by
  rfl

theorem push19Byte12SrcOffset : pushByteSrcOffset 12 = 13 := by
  rfl

theorem push19Byte12DstOffset : pushByteDstOffset 19 12 = 6 := by
  rfl

theorem push19Byte13SrcOffset : pushByteSrcOffset 13 = 14 := by
  rfl

theorem push19Byte13DstOffset : pushByteDstOffset 19 13 = 5 := by
  rfl

theorem push19Byte14SrcOffset : pushByteSrcOffset 14 = 15 := by
  rfl

theorem push19Byte14DstOffset : pushByteDstOffset 19 14 = 4 := by
  rfl

theorem push19Byte15SrcOffset : pushByteSrcOffset 15 = 16 := by
  rfl

theorem push19Byte15DstOffset : pushByteDstOffset 19 15 = 3 := by
  rfl

theorem push19Byte16SrcOffset : pushByteSrcOffset 16 = 17 := by
  rfl

theorem push19Byte16DstOffset : pushByteDstOffset 19 16 = 2 := by
  rfl

theorem push19Byte17SrcOffset : pushByteSrcOffset 17 = 18 := by
  rfl

theorem push19Byte17DstOffset : pushByteDstOffset 19 17 = 1 := by
  rfl

theorem push19Byte18SrcOffset : pushByteSrcOffset 18 = 19 := by
  rfl

theorem push19Byte18DstOffset : pushByteDstOffset 19 18 = 0 := by
  rfl

theorem push20Byte0SrcOffset : pushByteSrcOffset 0 = 1 := by
  rfl

theorem push20Byte0DstOffset : pushByteDstOffset 20 0 = 19 := by
  rfl

theorem push20Byte1SrcOffset : pushByteSrcOffset 1 = 2 := by
  rfl

theorem push20Byte1DstOffset : pushByteDstOffset 20 1 = 18 := by
  rfl

theorem push20Byte2SrcOffset : pushByteSrcOffset 2 = 3 := by
  rfl

theorem push20Byte2DstOffset : pushByteDstOffset 20 2 = 17 := by
  rfl

theorem push20Byte3SrcOffset : pushByteSrcOffset 3 = 4 := by
  rfl

theorem push20Byte3DstOffset : pushByteDstOffset 20 3 = 16 := by
  rfl

theorem push20Byte4SrcOffset : pushByteSrcOffset 4 = 5 := by
  rfl

theorem push20Byte4DstOffset : pushByteDstOffset 20 4 = 15 := by
  rfl

theorem push20Byte5SrcOffset : pushByteSrcOffset 5 = 6 := by
  rfl

theorem push20Byte5DstOffset : pushByteDstOffset 20 5 = 14 := by
  rfl

theorem push20Byte6SrcOffset : pushByteSrcOffset 6 = 7 := by
  rfl

theorem push20Byte6DstOffset : pushByteDstOffset 20 6 = 13 := by
  rfl

theorem push20Byte7SrcOffset : pushByteSrcOffset 7 = 8 := by
  rfl

theorem push20Byte7DstOffset : pushByteDstOffset 20 7 = 12 := by
  rfl

theorem push20Byte8SrcOffset : pushByteSrcOffset 8 = 9 := by
  rfl

theorem push20Byte8DstOffset : pushByteDstOffset 20 8 = 11 := by
  rfl

theorem push20Byte9SrcOffset : pushByteSrcOffset 9 = 10 := by
  rfl

theorem push20Byte9DstOffset : pushByteDstOffset 20 9 = 10 := by
  rfl

theorem push20Byte10SrcOffset : pushByteSrcOffset 10 = 11 := by
  rfl

theorem push20Byte10DstOffset : pushByteDstOffset 20 10 = 9 := by
  rfl

theorem push20Byte11SrcOffset : pushByteSrcOffset 11 = 12 := by
  rfl

theorem push20Byte11DstOffset : pushByteDstOffset 20 11 = 8 := by
  rfl

theorem push20Byte12SrcOffset : pushByteSrcOffset 12 = 13 := by
  rfl

theorem push20Byte12DstOffset : pushByteDstOffset 20 12 = 7 := by
  rfl

theorem push20Byte13SrcOffset : pushByteSrcOffset 13 = 14 := by
  rfl

theorem push20Byte13DstOffset : pushByteDstOffset 20 13 = 6 := by
  rfl

theorem push20Byte14SrcOffset : pushByteSrcOffset 14 = 15 := by
  rfl

theorem push20Byte14DstOffset : pushByteDstOffset 20 14 = 5 := by
  rfl

theorem push20Byte15SrcOffset : pushByteSrcOffset 15 = 16 := by
  rfl

theorem push20Byte15DstOffset : pushByteDstOffset 20 15 = 4 := by
  rfl

theorem push20Byte16SrcOffset : pushByteSrcOffset 16 = 17 := by
  rfl

theorem push20Byte16DstOffset : pushByteDstOffset 20 16 = 3 := by
  rfl

theorem push20Byte17SrcOffset : pushByteSrcOffset 17 = 18 := by
  rfl

theorem push20Byte17DstOffset : pushByteDstOffset 20 17 = 2 := by
  rfl

theorem push20Byte18SrcOffset : pushByteSrcOffset 18 = 19 := by
  rfl

theorem push20Byte18DstOffset : pushByteDstOffset 20 18 = 1 := by
  rfl

theorem push20Byte19SrcOffset : pushByteSrcOffset 19 = 20 := by
  rfl

theorem push20Byte19DstOffset : pushByteDstOffset 20 19 = 0 := by
  rfl

theorem push21Byte0SrcOffset : pushByteSrcOffset 0 = 1 := by
  rfl

theorem push21Byte0DstOffset : pushByteDstOffset 21 0 = 20 := by
  rfl

theorem push21Byte1SrcOffset : pushByteSrcOffset 1 = 2 := by
  rfl

theorem push21Byte1DstOffset : pushByteDstOffset 21 1 = 19 := by
  rfl

theorem push21Byte2SrcOffset : pushByteSrcOffset 2 = 3 := by
  rfl

theorem push21Byte2DstOffset : pushByteDstOffset 21 2 = 18 := by
  rfl

theorem push21Byte3SrcOffset : pushByteSrcOffset 3 = 4 := by
  rfl

theorem push21Byte3DstOffset : pushByteDstOffset 21 3 = 17 := by
  rfl

theorem push21Byte4SrcOffset : pushByteSrcOffset 4 = 5 := by
  rfl

theorem push21Byte4DstOffset : pushByteDstOffset 21 4 = 16 := by
  rfl

theorem push21Byte5SrcOffset : pushByteSrcOffset 5 = 6 := by
  rfl

theorem push21Byte5DstOffset : pushByteDstOffset 21 5 = 15 := by
  rfl

theorem push21Byte6SrcOffset : pushByteSrcOffset 6 = 7 := by
  rfl

theorem push21Byte6DstOffset : pushByteDstOffset 21 6 = 14 := by
  rfl

theorem push21Byte7SrcOffset : pushByteSrcOffset 7 = 8 := by
  rfl

theorem push21Byte7DstOffset : pushByteDstOffset 21 7 = 13 := by
  rfl

theorem push21Byte8SrcOffset : pushByteSrcOffset 8 = 9 := by
  rfl

theorem push21Byte8DstOffset : pushByteDstOffset 21 8 = 12 := by
  rfl

theorem push21Byte9SrcOffset : pushByteSrcOffset 9 = 10 := by
  rfl

theorem push21Byte9DstOffset : pushByteDstOffset 21 9 = 11 := by
  rfl

theorem push21Byte10SrcOffset : pushByteSrcOffset 10 = 11 := by
  rfl

theorem push21Byte10DstOffset : pushByteDstOffset 21 10 = 10 := by
  rfl

theorem push21Byte11SrcOffset : pushByteSrcOffset 11 = 12 := by
  rfl

theorem push21Byte11DstOffset : pushByteDstOffset 21 11 = 9 := by
  rfl

theorem push21Byte12SrcOffset : pushByteSrcOffset 12 = 13 := by
  rfl

theorem push21Byte12DstOffset : pushByteDstOffset 21 12 = 8 := by
  rfl

theorem push21Byte13SrcOffset : pushByteSrcOffset 13 = 14 := by
  rfl

theorem push21Byte13DstOffset : pushByteDstOffset 21 13 = 7 := by
  rfl

theorem push21Byte14SrcOffset : pushByteSrcOffset 14 = 15 := by
  rfl

theorem push21Byte14DstOffset : pushByteDstOffset 21 14 = 6 := by
  rfl

theorem push21Byte15SrcOffset : pushByteSrcOffset 15 = 16 := by
  rfl

theorem push21Byte15DstOffset : pushByteDstOffset 21 15 = 5 := by
  rfl

theorem push21Byte16SrcOffset : pushByteSrcOffset 16 = 17 := by
  rfl

theorem push21Byte16DstOffset : pushByteDstOffset 21 16 = 4 := by
  rfl

theorem push21Byte17SrcOffset : pushByteSrcOffset 17 = 18 := by
  rfl

theorem push21Byte17DstOffset : pushByteDstOffset 21 17 = 3 := by
  rfl

theorem push21Byte18SrcOffset : pushByteSrcOffset 18 = 19 := by
  rfl

theorem push21Byte18DstOffset : pushByteDstOffset 21 18 = 2 := by
  rfl

theorem push21Byte19SrcOffset : pushByteSrcOffset 19 = 20 := by
  rfl

theorem push21Byte19DstOffset : pushByteDstOffset 21 19 = 1 := by
  rfl

theorem push21Byte20SrcOffset : pushByteSrcOffset 20 = 21 := by
  rfl

theorem push21Byte20DstOffset : pushByteDstOffset 21 20 = 0 := by
  rfl

theorem push22Byte0SrcOffset : pushByteSrcOffset 0 = 1 := by
  rfl

theorem push22Byte0DstOffset : pushByteDstOffset 22 0 = 21 := by
  rfl

theorem push22Byte1SrcOffset : pushByteSrcOffset 1 = 2 := by
  rfl

theorem push22Byte1DstOffset : pushByteDstOffset 22 1 = 20 := by
  rfl

theorem push22Byte2SrcOffset : pushByteSrcOffset 2 = 3 := by
  rfl

theorem push22Byte2DstOffset : pushByteDstOffset 22 2 = 19 := by
  rfl

theorem push22Byte3SrcOffset : pushByteSrcOffset 3 = 4 := by
  rfl

theorem push22Byte3DstOffset : pushByteDstOffset 22 3 = 18 := by
  rfl

theorem push22Byte4SrcOffset : pushByteSrcOffset 4 = 5 := by
  rfl

theorem push22Byte4DstOffset : pushByteDstOffset 22 4 = 17 := by
  rfl

theorem push22Byte5SrcOffset : pushByteSrcOffset 5 = 6 := by
  rfl

theorem push22Byte5DstOffset : pushByteDstOffset 22 5 = 16 := by
  rfl

theorem push22Byte6SrcOffset : pushByteSrcOffset 6 = 7 := by
  rfl

theorem push22Byte6DstOffset : pushByteDstOffset 22 6 = 15 := by
  rfl

theorem push22Byte7SrcOffset : pushByteSrcOffset 7 = 8 := by
  rfl

theorem push22Byte7DstOffset : pushByteDstOffset 22 7 = 14 := by
  rfl

theorem push22Byte8SrcOffset : pushByteSrcOffset 8 = 9 := by
  rfl

theorem push22Byte8DstOffset : pushByteDstOffset 22 8 = 13 := by
  rfl

theorem push22Byte9SrcOffset : pushByteSrcOffset 9 = 10 := by
  rfl

theorem push22Byte9DstOffset : pushByteDstOffset 22 9 = 12 := by
  rfl

theorem push22Byte10SrcOffset : pushByteSrcOffset 10 = 11 := by
  rfl

theorem push22Byte10DstOffset : pushByteDstOffset 22 10 = 11 := by
  rfl

theorem push22Byte11SrcOffset : pushByteSrcOffset 11 = 12 := by
  rfl

theorem push22Byte11DstOffset : pushByteDstOffset 22 11 = 10 := by
  rfl

theorem push22Byte12SrcOffset : pushByteSrcOffset 12 = 13 := by
  rfl

theorem push22Byte12DstOffset : pushByteDstOffset 22 12 = 9 := by
  rfl

theorem push22Byte13SrcOffset : pushByteSrcOffset 13 = 14 := by
  rfl

theorem push22Byte13DstOffset : pushByteDstOffset 22 13 = 8 := by
  rfl

theorem push22Byte14SrcOffset : pushByteSrcOffset 14 = 15 := by
  rfl

theorem push22Byte14DstOffset : pushByteDstOffset 22 14 = 7 := by
  rfl

theorem push22Byte15SrcOffset : pushByteSrcOffset 15 = 16 := by
  rfl

theorem push22Byte15DstOffset : pushByteDstOffset 22 15 = 6 := by
  rfl

theorem push22Byte16SrcOffset : pushByteSrcOffset 16 = 17 := by
  rfl

theorem push22Byte16DstOffset : pushByteDstOffset 22 16 = 5 := by
  rfl

theorem push22Byte17SrcOffset : pushByteSrcOffset 17 = 18 := by
  rfl

theorem push22Byte17DstOffset : pushByteDstOffset 22 17 = 4 := by
  rfl

theorem push22Byte18SrcOffset : pushByteSrcOffset 18 = 19 := by
  rfl

theorem push22Byte18DstOffset : pushByteDstOffset 22 18 = 3 := by
  rfl

theorem push22Byte19SrcOffset : pushByteSrcOffset 19 = 20 := by
  rfl

theorem push22Byte19DstOffset : pushByteDstOffset 22 19 = 2 := by
  rfl

theorem push22Byte20SrcOffset : pushByteSrcOffset 20 = 21 := by
  rfl

theorem push22Byte20DstOffset : pushByteDstOffset 22 20 = 1 := by
  rfl

theorem push22Byte21SrcOffset : pushByteSrcOffset 21 = 22 := by
  rfl

theorem push22Byte21DstOffset : pushByteDstOffset 22 21 = 0 := by
  rfl

theorem push23Byte0SrcOffset : pushByteSrcOffset 0 = 1 := by
  rfl

theorem push23Byte0DstOffset : pushByteDstOffset 23 0 = 22 := by
  rfl

theorem push23Byte1SrcOffset : pushByteSrcOffset 1 = 2 := by
  rfl

theorem push23Byte1DstOffset : pushByteDstOffset 23 1 = 21 := by
  rfl

theorem push23Byte2SrcOffset : pushByteSrcOffset 2 = 3 := by
  rfl

theorem push23Byte2DstOffset : pushByteDstOffset 23 2 = 20 := by
  rfl

theorem push23Byte3SrcOffset : pushByteSrcOffset 3 = 4 := by
  rfl

theorem push23Byte3DstOffset : pushByteDstOffset 23 3 = 19 := by
  rfl

theorem push23Byte4SrcOffset : pushByteSrcOffset 4 = 5 := by
  rfl

theorem push23Byte4DstOffset : pushByteDstOffset 23 4 = 18 := by
  rfl

theorem push23Byte5SrcOffset : pushByteSrcOffset 5 = 6 := by
  rfl

theorem push23Byte5DstOffset : pushByteDstOffset 23 5 = 17 := by
  rfl

theorem push23Byte6SrcOffset : pushByteSrcOffset 6 = 7 := by
  rfl

theorem push23Byte6DstOffset : pushByteDstOffset 23 6 = 16 := by
  rfl

theorem push23Byte7SrcOffset : pushByteSrcOffset 7 = 8 := by
  rfl

theorem push23Byte7DstOffset : pushByteDstOffset 23 7 = 15 := by
  rfl

theorem push23Byte8SrcOffset : pushByteSrcOffset 8 = 9 := by
  rfl

theorem push23Byte8DstOffset : pushByteDstOffset 23 8 = 14 := by
  rfl

theorem push23Byte9SrcOffset : pushByteSrcOffset 9 = 10 := by
  rfl

theorem push23Byte9DstOffset : pushByteDstOffset 23 9 = 13 := by
  rfl

theorem push23Byte10SrcOffset : pushByteSrcOffset 10 = 11 := by
  rfl

theorem push23Byte10DstOffset : pushByteDstOffset 23 10 = 12 := by
  rfl

theorem push23Byte11SrcOffset : pushByteSrcOffset 11 = 12 := by
  rfl

theorem push23Byte11DstOffset : pushByteDstOffset 23 11 = 11 := by
  rfl

theorem push23Byte12SrcOffset : pushByteSrcOffset 12 = 13 := by
  rfl

theorem push23Byte12DstOffset : pushByteDstOffset 23 12 = 10 := by
  rfl

theorem push23Byte13SrcOffset : pushByteSrcOffset 13 = 14 := by
  rfl

theorem push23Byte13DstOffset : pushByteDstOffset 23 13 = 9 := by
  rfl

theorem push23Byte14SrcOffset : pushByteSrcOffset 14 = 15 := by
  rfl

theorem push23Byte14DstOffset : pushByteDstOffset 23 14 = 8 := by
  rfl

theorem push23Byte15SrcOffset : pushByteSrcOffset 15 = 16 := by
  rfl

theorem push23Byte15DstOffset : pushByteDstOffset 23 15 = 7 := by
  rfl

theorem push23Byte16SrcOffset : pushByteSrcOffset 16 = 17 := by
  rfl

theorem push23Byte16DstOffset : pushByteDstOffset 23 16 = 6 := by
  rfl

theorem push23Byte17SrcOffset : pushByteSrcOffset 17 = 18 := by
  rfl

theorem push23Byte17DstOffset : pushByteDstOffset 23 17 = 5 := by
  rfl

theorem push23Byte18SrcOffset : pushByteSrcOffset 18 = 19 := by
  rfl

theorem push23Byte18DstOffset : pushByteDstOffset 23 18 = 4 := by
  rfl

theorem push23Byte19SrcOffset : pushByteSrcOffset 19 = 20 := by
  rfl

theorem push23Byte19DstOffset : pushByteDstOffset 23 19 = 3 := by
  rfl

theorem push23Byte20SrcOffset : pushByteSrcOffset 20 = 21 := by
  rfl

theorem push23Byte20DstOffset : pushByteDstOffset 23 20 = 2 := by
  rfl

theorem push23Byte21SrcOffset : pushByteSrcOffset 21 = 22 := by
  rfl

theorem push23Byte21DstOffset : pushByteDstOffset 23 21 = 1 := by
  rfl

theorem push23Byte22SrcOffset : pushByteSrcOffset 22 = 23 := by
  rfl

theorem push23Byte22DstOffset : pushByteDstOffset 23 22 = 0 := by
  rfl

theorem push24Byte0SrcOffset : pushByteSrcOffset 0 = 1 := by
  rfl

theorem push24Byte0DstOffset : pushByteDstOffset 24 0 = 23 := by
  rfl

theorem push24Byte1SrcOffset : pushByteSrcOffset 1 = 2 := by
  rfl

theorem push24Byte1DstOffset : pushByteDstOffset 24 1 = 22 := by
  rfl

theorem push24Byte2SrcOffset : pushByteSrcOffset 2 = 3 := by
  rfl

theorem push24Byte2DstOffset : pushByteDstOffset 24 2 = 21 := by
  rfl

theorem push24Byte3SrcOffset : pushByteSrcOffset 3 = 4 := by
  rfl

theorem push24Byte3DstOffset : pushByteDstOffset 24 3 = 20 := by
  rfl

theorem push24Byte4SrcOffset : pushByteSrcOffset 4 = 5 := by
  rfl

theorem push24Byte4DstOffset : pushByteDstOffset 24 4 = 19 := by
  rfl

theorem push24Byte5SrcOffset : pushByteSrcOffset 5 = 6 := by
  rfl

theorem push24Byte5DstOffset : pushByteDstOffset 24 5 = 18 := by
  rfl

theorem push24Byte6SrcOffset : pushByteSrcOffset 6 = 7 := by
  rfl

theorem push24Byte6DstOffset : pushByteDstOffset 24 6 = 17 := by
  rfl

theorem push24Byte7SrcOffset : pushByteSrcOffset 7 = 8 := by
  rfl

theorem push24Byte7DstOffset : pushByteDstOffset 24 7 = 16 := by
  rfl

theorem push24Byte8SrcOffset : pushByteSrcOffset 8 = 9 := by
  rfl

theorem push24Byte8DstOffset : pushByteDstOffset 24 8 = 15 := by
  rfl

theorem push24Byte9SrcOffset : pushByteSrcOffset 9 = 10 := by
  rfl

theorem push24Byte9DstOffset : pushByteDstOffset 24 9 = 14 := by
  rfl

theorem push24Byte10SrcOffset : pushByteSrcOffset 10 = 11 := by
  rfl

theorem push24Byte10DstOffset : pushByteDstOffset 24 10 = 13 := by
  rfl

theorem push24Byte11SrcOffset : pushByteSrcOffset 11 = 12 := by
  rfl

theorem push24Byte11DstOffset : pushByteDstOffset 24 11 = 12 := by
  rfl

theorem push24Byte12SrcOffset : pushByteSrcOffset 12 = 13 := by
  rfl

theorem push24Byte12DstOffset : pushByteDstOffset 24 12 = 11 := by
  rfl

theorem push24Byte13SrcOffset : pushByteSrcOffset 13 = 14 := by
  rfl

theorem push24Byte13DstOffset : pushByteDstOffset 24 13 = 10 := by
  rfl

theorem push24Byte14SrcOffset : pushByteSrcOffset 14 = 15 := by
  rfl

theorem push24Byte14DstOffset : pushByteDstOffset 24 14 = 9 := by
  rfl

theorem push24Byte15SrcOffset : pushByteSrcOffset 15 = 16 := by
  rfl

theorem push24Byte15DstOffset : pushByteDstOffset 24 15 = 8 := by
  rfl

theorem push24Byte16SrcOffset : pushByteSrcOffset 16 = 17 := by
  rfl

theorem push24Byte16DstOffset : pushByteDstOffset 24 16 = 7 := by
  rfl

theorem push24Byte17SrcOffset : pushByteSrcOffset 17 = 18 := by
  rfl

theorem push24Byte17DstOffset : pushByteDstOffset 24 17 = 6 := by
  rfl

theorem push24Byte18SrcOffset : pushByteSrcOffset 18 = 19 := by
  rfl

theorem push24Byte18DstOffset : pushByteDstOffset 24 18 = 5 := by
  rfl

theorem push24Byte19SrcOffset : pushByteSrcOffset 19 = 20 := by
  rfl

theorem push24Byte19DstOffset : pushByteDstOffset 24 19 = 4 := by
  rfl

theorem push24Byte20SrcOffset : pushByteSrcOffset 20 = 21 := by
  rfl

theorem push24Byte20DstOffset : pushByteDstOffset 24 20 = 3 := by
  rfl

theorem push24Byte21SrcOffset : pushByteSrcOffset 21 = 22 := by
  rfl

theorem push24Byte21DstOffset : pushByteDstOffset 24 21 = 2 := by
  rfl

theorem push24Byte22SrcOffset : pushByteSrcOffset 22 = 23 := by
  rfl

theorem push24Byte22DstOffset : pushByteDstOffset 24 22 = 1 := by
  rfl

theorem push24Byte23SrcOffset : pushByteSrcOffset 23 = 24 := by
  rfl

theorem push24Byte23DstOffset : pushByteDstOffset 24 23 = 0 := by
  rfl

theorem push25Byte0SrcOffset : pushByteSrcOffset 0 = 1 := by
  rfl

theorem push25Byte0DstOffset : pushByteDstOffset 25 0 = 24 := by
  rfl

theorem push25Byte1SrcOffset : pushByteSrcOffset 1 = 2 := by
  rfl

theorem push25Byte1DstOffset : pushByteDstOffset 25 1 = 23 := by
  rfl

theorem push25Byte2SrcOffset : pushByteSrcOffset 2 = 3 := by
  rfl

theorem push25Byte2DstOffset : pushByteDstOffset 25 2 = 22 := by
  rfl

theorem push25Byte3SrcOffset : pushByteSrcOffset 3 = 4 := by
  rfl

theorem push25Byte3DstOffset : pushByteDstOffset 25 3 = 21 := by
  rfl

theorem push25Byte4SrcOffset : pushByteSrcOffset 4 = 5 := by
  rfl

theorem push25Byte4DstOffset : pushByteDstOffset 25 4 = 20 := by
  rfl

theorem push25Byte5SrcOffset : pushByteSrcOffset 5 = 6 := by
  rfl

theorem push25Byte5DstOffset : pushByteDstOffset 25 5 = 19 := by
  rfl

theorem push25Byte6SrcOffset : pushByteSrcOffset 6 = 7 := by
  rfl

theorem push25Byte6DstOffset : pushByteDstOffset 25 6 = 18 := by
  rfl

theorem push25Byte7SrcOffset : pushByteSrcOffset 7 = 8 := by
  rfl

theorem push25Byte7DstOffset : pushByteDstOffset 25 7 = 17 := by
  rfl

theorem push25Byte8SrcOffset : pushByteSrcOffset 8 = 9 := by
  rfl

theorem push25Byte8DstOffset : pushByteDstOffset 25 8 = 16 := by
  rfl

theorem push25Byte9SrcOffset : pushByteSrcOffset 9 = 10 := by
  rfl

theorem push25Byte9DstOffset : pushByteDstOffset 25 9 = 15 := by
  rfl

theorem push25Byte10SrcOffset : pushByteSrcOffset 10 = 11 := by
  rfl

theorem push25Byte10DstOffset : pushByteDstOffset 25 10 = 14 := by
  rfl

theorem push25Byte11SrcOffset : pushByteSrcOffset 11 = 12 := by
  rfl

theorem push25Byte11DstOffset : pushByteDstOffset 25 11 = 13 := by
  rfl

theorem push25Byte12SrcOffset : pushByteSrcOffset 12 = 13 := by
  rfl

theorem push25Byte12DstOffset : pushByteDstOffset 25 12 = 12 := by
  rfl

theorem push25Byte13SrcOffset : pushByteSrcOffset 13 = 14 := by
  rfl

theorem push25Byte13DstOffset : pushByteDstOffset 25 13 = 11 := by
  rfl

theorem push25Byte14SrcOffset : pushByteSrcOffset 14 = 15 := by
  rfl

theorem push25Byte14DstOffset : pushByteDstOffset 25 14 = 10 := by
  rfl

theorem push25Byte15SrcOffset : pushByteSrcOffset 15 = 16 := by
  rfl

theorem push25Byte15DstOffset : pushByteDstOffset 25 15 = 9 := by
  rfl

theorem push25Byte16SrcOffset : pushByteSrcOffset 16 = 17 := by
  rfl

theorem push25Byte16DstOffset : pushByteDstOffset 25 16 = 8 := by
  rfl

theorem push25Byte17SrcOffset : pushByteSrcOffset 17 = 18 := by
  rfl

theorem push25Byte17DstOffset : pushByteDstOffset 25 17 = 7 := by
  rfl

theorem push25Byte18SrcOffset : pushByteSrcOffset 18 = 19 := by
  rfl

theorem push25Byte18DstOffset : pushByteDstOffset 25 18 = 6 := by
  rfl

theorem push25Byte19SrcOffset : pushByteSrcOffset 19 = 20 := by
  rfl

theorem push25Byte19DstOffset : pushByteDstOffset 25 19 = 5 := by
  rfl

theorem push25Byte20SrcOffset : pushByteSrcOffset 20 = 21 := by
  rfl

theorem push25Byte20DstOffset : pushByteDstOffset 25 20 = 4 := by
  rfl

theorem push25Byte21SrcOffset : pushByteSrcOffset 21 = 22 := by
  rfl

theorem push25Byte21DstOffset : pushByteDstOffset 25 21 = 3 := by
  rfl

theorem push25Byte22SrcOffset : pushByteSrcOffset 22 = 23 := by
  rfl

theorem push25Byte22DstOffset : pushByteDstOffset 25 22 = 2 := by
  rfl

theorem push25Byte23SrcOffset : pushByteSrcOffset 23 = 24 := by
  rfl

theorem push25Byte23DstOffset : pushByteDstOffset 25 23 = 1 := by
  rfl

theorem push25Byte24SrcOffset : pushByteSrcOffset 24 = 25 := by
  rfl

theorem push25Byte24DstOffset : pushByteDstOffset 25 24 = 0 := by
  rfl

theorem push26Byte0SrcOffset : pushByteSrcOffset 0 = 1 := by
  rfl

theorem push26Byte0DstOffset : pushByteDstOffset 26 0 = 25 := by
  rfl

theorem push26Byte1SrcOffset : pushByteSrcOffset 1 = 2 := by
  rfl

theorem push26Byte1DstOffset : pushByteDstOffset 26 1 = 24 := by
  rfl

theorem push26Byte2SrcOffset : pushByteSrcOffset 2 = 3 := by
  rfl

theorem push26Byte2DstOffset : pushByteDstOffset 26 2 = 23 := by
  rfl

theorem push26Byte3SrcOffset : pushByteSrcOffset 3 = 4 := by
  rfl

theorem push26Byte3DstOffset : pushByteDstOffset 26 3 = 22 := by
  rfl

theorem push26Byte4SrcOffset : pushByteSrcOffset 4 = 5 := by
  rfl

theorem push26Byte4DstOffset : pushByteDstOffset 26 4 = 21 := by
  rfl

theorem push26Byte5SrcOffset : pushByteSrcOffset 5 = 6 := by
  rfl

theorem push26Byte5DstOffset : pushByteDstOffset 26 5 = 20 := by
  rfl

theorem push26Byte6SrcOffset : pushByteSrcOffset 6 = 7 := by
  rfl

theorem push26Byte6DstOffset : pushByteDstOffset 26 6 = 19 := by
  rfl

theorem push26Byte7SrcOffset : pushByteSrcOffset 7 = 8 := by
  rfl

theorem push26Byte7DstOffset : pushByteDstOffset 26 7 = 18 := by
  rfl

theorem push26Byte8SrcOffset : pushByteSrcOffset 8 = 9 := by
  rfl

theorem push26Byte8DstOffset : pushByteDstOffset 26 8 = 17 := by
  rfl

theorem push26Byte9SrcOffset : pushByteSrcOffset 9 = 10 := by
  rfl

theorem push26Byte9DstOffset : pushByteDstOffset 26 9 = 16 := by
  rfl

theorem push26Byte10SrcOffset : pushByteSrcOffset 10 = 11 := by
  rfl

theorem push26Byte10DstOffset : pushByteDstOffset 26 10 = 15 := by
  rfl

theorem push26Byte11SrcOffset : pushByteSrcOffset 11 = 12 := by
  rfl

theorem push26Byte11DstOffset : pushByteDstOffset 26 11 = 14 := by
  rfl

theorem push26Byte12SrcOffset : pushByteSrcOffset 12 = 13 := by
  rfl

theorem push26Byte12DstOffset : pushByteDstOffset 26 12 = 13 := by
  rfl

theorem push26Byte13SrcOffset : pushByteSrcOffset 13 = 14 := by
  rfl

theorem push26Byte13DstOffset : pushByteDstOffset 26 13 = 12 := by
  rfl

theorem push26Byte14SrcOffset : pushByteSrcOffset 14 = 15 := by
  rfl

theorem push26Byte14DstOffset : pushByteDstOffset 26 14 = 11 := by
  rfl

theorem push26Byte15SrcOffset : pushByteSrcOffset 15 = 16 := by
  rfl

theorem push26Byte15DstOffset : pushByteDstOffset 26 15 = 10 := by
  rfl

theorem push26Byte16SrcOffset : pushByteSrcOffset 16 = 17 := by
  rfl

theorem push26Byte16DstOffset : pushByteDstOffset 26 16 = 9 := by
  rfl

theorem push26Byte17SrcOffset : pushByteSrcOffset 17 = 18 := by
  rfl

theorem push26Byte17DstOffset : pushByteDstOffset 26 17 = 8 := by
  rfl

theorem push26Byte18SrcOffset : pushByteSrcOffset 18 = 19 := by
  rfl

theorem push26Byte18DstOffset : pushByteDstOffset 26 18 = 7 := by
  rfl

theorem push26Byte19SrcOffset : pushByteSrcOffset 19 = 20 := by
  rfl

theorem push26Byte19DstOffset : pushByteDstOffset 26 19 = 6 := by
  rfl

theorem push26Byte20SrcOffset : pushByteSrcOffset 20 = 21 := by
  rfl

theorem push26Byte20DstOffset : pushByteDstOffset 26 20 = 5 := by
  rfl

theorem push26Byte21SrcOffset : pushByteSrcOffset 21 = 22 := by
  rfl

theorem push26Byte21DstOffset : pushByteDstOffset 26 21 = 4 := by
  rfl

theorem push26Byte22SrcOffset : pushByteSrcOffset 22 = 23 := by
  rfl

theorem push26Byte22DstOffset : pushByteDstOffset 26 22 = 3 := by
  rfl

theorem push26Byte23SrcOffset : pushByteSrcOffset 23 = 24 := by
  rfl

theorem push26Byte23DstOffset : pushByteDstOffset 26 23 = 2 := by
  rfl

theorem push26Byte24SrcOffset : pushByteSrcOffset 24 = 25 := by
  rfl

theorem push26Byte24DstOffset : pushByteDstOffset 26 24 = 1 := by
  rfl

theorem push26Byte25SrcOffset : pushByteSrcOffset 25 = 26 := by
  rfl

theorem push26Byte25DstOffset : pushByteDstOffset 26 25 = 0 := by
  rfl

theorem push32Byte0SrcOffset : pushByteSrcOffset 0 = 1 := by
  rfl

theorem push32Byte0DstOffset : pushByteDstOffset 32 0 = 31 := by
  rfl

theorem push32Byte31SrcOffset : pushByteSrcOffset 31 = 32 := by
  rfl

theorem push32Byte31DstOffset : pushByteDstOffset 32 31 = 0 := by
  rfl

/-- Read one immediate byte and store it into the new EVM stack slot.

    `n` is the PUSH width (1..32) and `i` is the byte index in
    `[0, n)` counted from the most-significant byte of the immediate.
    The big-endian semantics mean immediate byte `i` (which lives at
    `code[pc + 1 + i]`) is the byte at integer position `n - 1 - i`,
    so it goes into memory offset `n - 1 - i` from the new stack
    pointer (which holds limb 0's LSB at offset 0). -/
private def push_one_byte (n i : Nat) : Program :=
  LBU .x7 .x10 (BitVec.ofNat 12 (pushByteSrcOffset i)) ;;
  SB .x12 .x7 (BitVec.ofNat 12 (pushByteDstOffset n i))

/-- Sequence `push_one_byte n 0 ;; push_one_byte n 1 ;; ... ;; push_one_byte n (k-1)`.

    Defined by recursion on `k` so `evm_push n` can be expressed for
    arbitrary symbolic `n` while keeping the per-byte block uniform. -/
private def push_bytes (n : Nat) : Nat → Program
  | 0     => prog_skip
  | k + 1 => push_bytes n k ;; push_one_byte n k

private theorem push_one_byte_length (n i : Nat) :
    (push_one_byte n i).length = 2 := by
  unfold push_one_byte LBU SB single seq
  rfl

theorem push_bytes_length (n k : Nat) :
    (push_bytes n k).length = 2 * k := by
  induction k with
  | zero =>
      unfold push_bytes prog_skip
      rfl
  | succ k ih =>
      unfold push_bytes
      unfold seq
      rw [Program.length_append, ih, push_one_byte_length]
      omega

/-- Generic PUSHn program.

    Layout (5 + 2n instructions):
      1. `ADDI x12, x12, -32`       — allocate a new 32-byte stack slot
      2. four `SD x12, x0, 8*j`    — zero-fill the four 64-bit limbs
      3. n × (LBU + SB) pairs       — copy immediate bytes into place

    For PUSH1 through PUSH32 the offsets stay below 2^11, so the
    `BitVec.ofNat 12` casts in the helpers behave like the natural
    encoding (no sign-extension surprises). -/
def evm_push (n : Nat) : Program :=
  ADDI .x12 .x12 (-32) ;;
  SD .x12 .x0 0 ;; SD .x12 .x0 8 ;; SD .x12 .x0 16 ;; SD .x12 .x0 24 ;;
  push_bytes n n

theorem evm_push_length (n : Nat) :
    (evm_push n).length = 5 + 2 * n := by
  unfold evm_push ADDI SD single seq
  simp only [Program.length_append, List.length_cons, List.length_nil,
    push_bytes_length]
  omega

theorem evm_push1_length : (evm_push 1).length = 7 := by
  rw [evm_push_length]

theorem evm_push2_length : (evm_push 2).length = 9 := by
  rw [evm_push_length]

theorem evm_push32_length : (evm_push 32).length = 69 := by
  rw [evm_push_length]

/-- CodeReq for `evm_push n`.

    Symbolic `n` prevents `CodeReq.ofProg` from fully reducing, but for
    this slice (program-only) we only need a buildable definition. The
    spec slices (#101 slices 3-4) may refactor this into an explicit
    `CodeReq.singleton` union chain mirroring `evm_dup_code` if proofs
    require it. -/
abbrev evm_push_code (base : Word) (n : Nat) : CodeReq :=
  CodeReq.ofProg base (evm_push n)

end EvmAsm.Evm64
