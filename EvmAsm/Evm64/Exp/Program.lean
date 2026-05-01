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

-- ----------------------------------------------------------------------------
-- Loop prologue: initialize accumulator + counter (#92 slice 3d, beads
-- evm-asm-yvfr)
-- ----------------------------------------------------------------------------
--
-- Per `docs/92-exp-survey.md` §2(b) and §4, the EXP body needs two pieces of
-- state initialized before the 256-iteration square-and-multiply loop runs:
--
--   1. The running accumulator `result` (a 256-bit value held as 4 LE 64-bit
--      limbs in the local RISC-V scratch frame at `sp+0 .. sp+24`) must be
--      initialized to 1, i.e. (limb0, limb1, limb2, limb3) = (1, 0, 0, 0).
--   2. The master iteration counter `x9` must be initialized to 256.
--
-- This block does NOT include the LP64 `cc_prologue` (which is emitted by the
-- surrounding non-leaf `evm_exp` wrapper) and does NOT marshal the EVM stack
-- operands `a` / `b` into LP64 a0/a1 slots (handled per-iteration by the
-- scaffold introduced in slice evm-asm-w5mk). It is the EXP-specific tail of
-- the prologue: counter init + accumulator init.
--
-- Convention assumed by this block: the `evm_exp` wrapper has already moved
-- `sp` (x2) down by enough bytes to give us a 32-byte 8-byte-aligned region
-- at offsets `[0, 24]` for the four `result` limbs (low limb at +0, high
-- limb at +24). The wrapper will lay out the rest of its scratch frame —
-- saved ra, alignment, any spilled values — at offsets ≥ 32, so the four
-- SDs here only touch the result slots.
--
-- Register usage:
--   x9  — master iteration counter (output: 256)
--   x5  — t0, used as a temporary to hold the literal `1` before the SD;
--          caller-saved per LP64, not live across calls so safe to clobber
--          before the loop body ever runs.
--   x2  — sp; read-only here.
--   x0  — zero register, used directly in the three high-limb SDs to avoid
--          a second ADDI for an additional zero temp.
--
-- 6 instructions, 24 bytes:
--   ADDI x9, x0, 256   — counter := 256
--   ADDI x5, x0, 1     — t0      := 1
--   SD   sp, t0, 0     — result.limb0 := 1
--   SD   sp, x0, 8     — result.limb1 := 0
--   SD   sp, x0, 16    — result.limb2 := 0
--   SD   sp, x0, 24    — result.limb3 := 0

/-- EXP-specific prologue: initialize the master iteration counter
    `x9 := 256` and the four limbs of the running accumulator `result`
    in the local scratch frame at `sp+0 .. sp+24` to `(1, 0, 0, 0)`.
    Excludes the LP64 `cc_prologue` (which the surrounding `evm_exp`
    wrapper emits separately) and operand marshalling. 6 instructions. -/
def exp_prologue : Program :=
  ADDI .x9 .x0 256 ;;
  ADDI .x5 .x0 1 ;;
  SD .x2 .x5 0 ;;
  SD .x2 .x0 8 ;;
  SD .x2 .x0 16 ;;
  SD .x2 .x0 24

theorem exp_prologue_length : exp_prologue.length = 6 := by decide

-- ----------------------------------------------------------------------------
-- Loop epilogue: result writeback + EVM stack advance (#92 slice 3e, beads
-- evm-asm-tesj)
-- ----------------------------------------------------------------------------
--
-- Per `docs/92-exp-survey.md` §"Result write-back" (line 178), once the
-- 256-iteration square-and-multiply loop has finished, the four limbs of the
-- running accumulator `result` (held in the local scratch frame at
-- `sp + 0 .. sp + 24`) must be copied out to the EVM stack at
-- `x12 + 32 .. x12 + 56` (the slot that originally held operand `a` on
-- entry, since both `a` and `b` are popped and a single 256-bit result is
-- pushed). Then `x12` advances by +32 (one EVM-word pop, since EXP pops
-- two 256-bit operands and pushes one result).
--
-- This block does NOT include the LP64 `cc_epilogue` (which the surrounding
-- `evm_exp` non-leaf wrapper emits separately, restoring `ra`/`sp` and
-- returning to the caller). It is the EXP-specific tail of the body:
-- writeback + EVM stack-pointer fixup, mirroring the role of `mul_epilogue`
-- in `Evm64/Multiply/Program.lean` but with an additional 4-limb LD/SD
-- copy because EXP holds its accumulator in the local scratch frame
-- rather than directly on the EVM stack.
--
-- Register usage:
--   x2  — sp; read-only (local scratch frame base for `result`).
--   x12 — EVM stack pointer (a2); advanced by +32 at the very end.
--   x5  — t0, used as a single-limb load/store temporary; caller-saved per
--          LP64 and not live across the surrounding loop, so safe to clobber.
--
-- 9 instructions, 36 bytes:
--   LD   t0, sp, 0     — t0          := result.limb0
--   SD   x12, t0, 32   — evm_stack[0] := t0
--   LD   t0, sp, 8     — t0          := result.limb1
--   SD   x12, t0, 40   — evm_stack[1] := t0
--   LD   t0, sp, 16    — t0          := result.limb2
--   SD   x12, t0, 48   — evm_stack[2] := t0
--   LD   t0, sp, 24    — t0          := result.limb3
--   SD   x12, t0, 56   — evm_stack[3] := t0
--   ADDI x12, x12, 32  — pop one EVM word

/-- EXP-specific epilogue: copy the four limbs of the running accumulator
    `result` from the local scratch frame at `sp + 0 .. sp + 24` to the
    EVM stack at `x12 + 32 .. x12 + 56`, then advance the EVM stack
    pointer `x12` by +32 (one EVM-word pop). Excludes the LP64
    `cc_epilogue` (which the surrounding `evm_exp` wrapper emits
    separately). 9 instructions. -/
def exp_epilogue : Program :=
  LD .x5 .x2 0 ;;
  SD .x12 .x5 32 ;;
  LD .x5 .x2 8 ;;
  SD .x12 .x5 40 ;;
  LD .x5 .x2 16 ;;
  SD .x12 .x5 48 ;;
  LD .x5 .x2 24 ;;
  SD .x12 .x5 56 ;;
  ADDI .x12 .x12 32

theorem exp_epilogue_length : exp_epilogue.length = 9 := by decide

-- Placeholder: `evm_exp : Program` lands in slice 3 (evm-asm-ahaz).
-- See `docs/92-exp-survey.md` for the algorithm and reuse points.

end EvmAsm.Evm64
