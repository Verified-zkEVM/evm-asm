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

-- ----------------------------------------------------------------------------
-- Per-iteration composite: exp_iter_body (#92 slice 3b, beads evm-asm-hdov)
-- ----------------------------------------------------------------------------
--
-- One full iteration of the square-and-multiply loop body, composed from the
-- three sub-blocks introduced in slice 3a. Per `docs/92-exp-survey.md` §4,
-- the iteration body decomposes as:
--
--     exp_iter_body :=
--       exp_bit_test_block ;;       -- 3 instr: x10 := bit i of b; advance cursor
--       exp_square_block mulOff ;;  -- 1 instr: result := result * result
--       exp_cond_mul_block mulOff skipOff
--                                   -- 2 instr: if x10 == 0 skip, else result := result * a
--
-- Total: 6 instructions per iteration. Argument-marshalling (copying
-- `result` / `a` into the LP64 a0/a1 slots expected by `mul_callable`) is
-- still handled by the surrounding 256-iteration scaffold introduced in
-- evm-asm-ahaz / evm-asm-w5mk; this slice is structural composition only.

/-- One full iteration of the EXP square-and-multiply loop body: bit test,
    unconditional squaring (JAL into `mul_callable`), conditional multiply
    by base `a` (BEQ-skipped JAL). 6 instructions.

    `mulOff` is the signed JAL offset to `mul_callable` (shared between the
    two JAL sites in this iteration; both call sites are at the same
    program-relative position when expanded across the loop, but the actual
    numeric value is pinned once `evm_exp` is laid out in slice
    evm-asm-ahaz). `skipOff` is the BEQ branch offset that skips past the
    second JAL when the current exponent bit is zero. -/
def exp_iter_body (mulOff : BitVec 21) (skipOff : BitVec 13) : Program :=
  exp_bit_test_block ;;
  exp_square_block mulOff ;;
  exp_cond_mul_block mulOff skipOff

theorem exp_iter_body_length (mulOff : BitVec 21) (skipOff : BitVec 13) :
    (exp_iter_body mulOff skipOff).length = 6 := by
  show ((exp_bit_test_block ;; exp_square_block mulOff) ;;
        exp_cond_mul_block mulOff skipOff).length = 6
  simp only [seq, Program.length_append, exp_bit_test_block_length,
    exp_square_block_length, exp_cond_mul_block_length]

-- ----------------------------------------------------------------------------
-- Loop-back tail: counter decrement + backward BNE (#92 slice 3c, beads
-- evm-asm-46ue)
-- ----------------------------------------------------------------------------
--
-- The square-and-multiply loop runs for exactly 256 iterations (one per bit
-- of the 256-bit exponent). Per `docs/92-exp-survey.md` §4 ("Iteration
-- counter via decrement-and-branch"), the master iteration counter lives in
-- a dedicated register (`x9`), initialized to 256 by the prologue, and the
-- bottom of every iteration decrements it and branches back to the top of
-- the loop body while it is still nonzero.
--
-- `exp_loop_back` packages those two trailing instructions as a standalone
-- `Program` block so the surrounding scaffold (`evm_exp`, slice
-- evm-asm-ahaz) and the loop-composition spec (slice evm-asm-w5mk) can
-- compose it independently of `exp_iter_body` and pin the concrete
-- backward `backOff` once `evm_exp` is laid out.
--
-- Register usage:
--   x9 — master iteration counter (decremented by 1 each iteration; loop
--        exits when it reaches 0). Distinct from `x6` in `exp_bit_test_block`,
--        which counts remaining bits in the current 64-bit limb of the
--        exponent and is refilled at limb boundaries by separate
--        scaffolding.
--
-- The `backOff : BitVec 13` parameter is the *signed* 13-bit BNE offset from
-- the BNE site back to the top of the iteration body. The offset is
-- byte-counted (4 bytes per RV64 instruction) and negative for a backward
-- branch. The actual numeric value is pinned in slice evm-asm-ahaz when
-- `evm_exp` is assembled and the loop body length is final.

/-- Tail of the EXP square-and-multiply loop: decrement the master 256-bit
    iteration counter `x9` by 1, then branch back to the top of the loop
    body if `x9` is still nonzero. 2 instructions.

    `backOff` is the signed 13-bit BNE byte offset from the BNE site back
    to the top of the iteration body (negative). The concrete value is
    pinned by the surrounding `evm_exp` layout in slice evm-asm-ahaz. -/
def exp_loop_back (backOff : BitVec 13) : Program :=
  ADDI .x9 .x9 (-1) ;;
  single (.BNE .x9 .x0 backOff)

theorem exp_loop_back_length (backOff : BitVec 13) :
    (exp_loop_back backOff).length = 2 := by
  show (ADDI .x9 .x9 (-1) ;; single (.BNE .x9 .x0 backOff)).length = 2
  rfl

-- Placeholder: `evm_exp : Program` lands in slice 3 (evm-asm-ahaz).
-- See `docs/92-exp-survey.md` for the algorithm and reuse points.

end EvmAsm.Evm64
