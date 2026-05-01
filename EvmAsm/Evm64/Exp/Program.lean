/-
  EvmAsm.Evm64.Exp.Program

  256-bit EVM EXP opcode (`EXP(a, b) = a^b mod 2^256`) as a 64-bit RISC-V
  program.

  Skeleton placeholder for GH #92 (beads slice evm-asm-cf2c).

  The actual Program will be defined in the Program-definition slice
  (evm-asm-ahaz). Per `docs/92-exp-survey.md` the algorithm is binary
  square-and-multiply over 256 bits of exponent, invoking `evm_mul`
  (made callable via a `cc_ret` shim) once per squaring and conditionally
  once per set bit. The full bytecode will be assembled from sub-blocks
  `exp_prologue`, `exp_square_block`, `exp_cond_mul_block`, `exp_iter_body`,
  `exp_loop`, `exp_epilogue`.

  This file currently has no `evm_exp` definition; later slices will add
  it without breaking the umbrella import graph.
-/

import EvmAsm.Evm64.Stack

namespace EvmAsm.Evm64

open EvmAsm.Rv64

-- ============================================================================
-- Iteration sub-blocks (#92 slice 3a, beads evm-asm-dl98)
-- ============================================================================
--
-- Per `docs/92-exp-survey.md` §4 the per-iteration body of the
-- square-and-multiply loop decomposes into three sub-blocks:
--
--     exp_iter_body :=
--       exp_bit_test_block ;;     -- x10 := bit i of b; advance bit cursor
--       exp_square_block ;;       -- result := result * result   (JAL mul_callable)
--       exp_cond_mul_block        -- if x10 == 0 skip; else result := result * a
--                                 --   (BEQ ;; JAL mul_callable)
--
-- This slice introduces the three sub-blocks as parameterized `Program`s.
-- Argument-marshalling (copying `result` / `a` into the LP64 a/b slots
-- expected by `mul_callable`) and the surrounding 256-iteration loop scaffold
-- land in later slices (evm-asm-ahaz / evm-asm-mtj3 / evm-asm-w5mk).
--
-- Register usage (provisional, refined when slice 3b wires marshalling):
--   x5  — current limb of exponent b, shifted right one bit per iteration
--   x6  — remaining bits in the current limb (init 64, refilled at limb boundary)
--   x10 — current bit value (0 or 1) after `exp_bit_test_block`
--   x12 — EVM stack pointer (LP64 a2)
--   x1  — return address (set by `JAL .x1 …` into `mul_callable`)
--
-- The `mulOff : BitVec 21` parameter is the signed JAL offset from the JAL
-- site to the entry of `mul_callable`. The actual numeric value is pinned
-- once `evm_exp` is laid out (slice evm-asm-ahaz).

/-- Single iteration of the bit-cursor: extract the low bit of `x5` into
    `x10`, then shift `x5` right by one and decrement the remaining-bits
    counter `x6`. 3 instructions. -/
def exp_bit_test_block : Program :=
  ANDI .x10 .x5 1 ;;
  SRLI .x5 .x5 1 ;;
  ADDI .x6 .x6 (-1)

/-- Always-on squaring step: invoke `mul_callable` via a near `JAL`.
    Argument marshalling (placing both factors at the LP64 input slots
    relative to `x12`) is handled by the surrounding scaffold; this block
    is just the call. 1 instruction. -/
def exp_square_block (mulOff : BitVec 21) : Program :=
  JAL .x1 mulOff

/-- Conditional multiply by base `a`: if the current bit `x10` is zero,
    branch past the JAL using `skipOff` (the byte offset from the BEQ to
    the instruction immediately after the JAL). Otherwise fall through
    into a near `JAL` to `mul_callable`. 2 instructions. -/
def exp_cond_mul_block (mulOff : BitVec 21) (skipOff : BitVec 13) : Program :=
  BEQ .x10 .x0 skipOff ;;
  JAL .x1 mulOff

-- ----------------------------------------------------------------------------
-- Length lemmas
-- ----------------------------------------------------------------------------

theorem exp_bit_test_block_length : exp_bit_test_block.length = 3 := by decide

theorem exp_square_block_length (mulOff : BitVec 21) :
    (exp_square_block mulOff).length = 1 := rfl

theorem exp_cond_mul_block_length (mulOff : BitVec 21) (skipOff : BitVec 13) :
    (exp_cond_mul_block mulOff skipOff).length = 2 := rfl

-- Placeholder: `evm_exp : Program` lands in slice 3 (evm-asm-ahaz).
-- See `docs/92-exp-survey.md` for the algorithm and reuse points.

end EvmAsm.Evm64
