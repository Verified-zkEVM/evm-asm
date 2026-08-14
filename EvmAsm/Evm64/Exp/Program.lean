/-
  EvmAsm.Evm64.Exp.Program

  256-bit EVM EXP opcode (`EXP(a, b) = a^b mod 2^256`) as a 64-bit RISC-V
  program.

  GH #92 builds EXP by binary square-and-multiply over all 256 exponent bits,
  invoking `evm_mul` through the callable shim once per squaring and
  conditionally once per set bit.  This file contains the concrete sub-blocks,
  loop body, stack-pointer shims, and top-level `evm_exp` assembly used by the
  composition and semantic proof layers.
-/

import EvmAsm.Rv64.Program

namespace EvmAsm.Evm64

open EvmAsm.Rv64 (ADDI ANDI BEQ BNE Instr JAL LD Program SD SLLI SRLI seq single
  signExtend13 signExtend21)

-- ============================================================================
-- Iteration sub-blocks (#92 slice 3a, beads evm-asm-dl98)
-- ============================================================================
--
-- The per-iteration body of the
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

/-- MSB-first variant of the bit-cursor for the square-result EXP algorithm.
    Extracts the high bit of `x5` into `x10`, shifts `x5` left by one, and
    decrements the remaining-bits counter `x6`. 3 instructions. -/
def exp_msb_bit_test_block : Program :=
  SRLI .x10 .x5 63 ;;
  SLLI .x5 .x5 1 ;;
  ADDI .x6 .x6 (-1)

/-- Save the current EXP bit in `x18`, a callee-saved register that is not an
    LP64 argument/result register for `mul_callable`. This keeps the branch
    condition live across the unconditional squaring call. 1 instruction. -/
def exp_save_bit_block : Program :=
  ADDI .x18 .x10 0

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

theorem exp_msb_bit_test_block_length : exp_msb_bit_test_block.length = 3 := by decide

theorem exp_save_bit_block_length : exp_save_bit_block.length = 1 := rfl

theorem exp_square_block_length (mulOff : BitVec 21) :
    (exp_square_block mulOff).length = 1 := rfl

theorem exp_cond_mul_block_length (mulOff : BitVec 21) (skipOff : BitVec 13) :
    (exp_cond_mul_block mulOff skipOff).length = 2 := rfl

theorem exp_bit_test_block_byte_length :
    4 * exp_bit_test_block.length = 12 := by
  rw [exp_bit_test_block_length]

theorem exp_msb_bit_test_block_byte_length :
    4 * exp_msb_bit_test_block.length = 12 := by
  rw [exp_msb_bit_test_block_length]

theorem exp_save_bit_block_byte_length :
    4 * exp_save_bit_block.length = 4 := by
  rw [exp_save_bit_block_length]

theorem exp_square_block_byte_length (mulOff : BitVec 21) :
    4 * (exp_square_block mulOff).length = 4 := by
  rw [exp_square_block_length]

theorem exp_cond_mul_block_byte_length (mulOff : BitVec 21) (skipOff : BitVec 13) :
    4 * (exp_cond_mul_block mulOff skipOff).length = 8 := by
  rw [exp_cond_mul_block_length]

-- ----------------------------------------------------------------------------
-- Per-iteration composite: exp_iter_body (#92 slice 3b, beads evm-asm-hdov)
-- ----------------------------------------------------------------------------
--
-- One full iteration of the square-and-multiply loop body, composed from the
-- three sub-blocks introduced in slice 3a.
-- The iteration body decomposes as:
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

theorem exp_iter_body_byte_length (mulOff : BitVec 21) (skipOff : BitVec 13) :
    4 * (exp_iter_body mulOff skipOff).length = 24 := by
  rw [exp_iter_body_length]

-- ----------------------------------------------------------------------------
-- Loop-back tail: counter decrement + backward BNE (#92 slice 3c, beads
-- evm-asm-46ue)
-- ----------------------------------------------------------------------------
--
-- The square-and-multiply loop runs for exactly 256 iterations (one per bit
-- of the 256-bit exponent). Using an iteration
-- counter via decrement-and-branch, the master iteration counter lives in
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

theorem exp_loop_back_byte_length (backOff : BitVec 13) :
    4 * (exp_loop_back backOff).length = 8 := by
  rw [exp_loop_back_length]

-- ----------------------------------------------------------------------------
-- Per-iteration loop block: exp_loop (#92 slice 3d, beads evm-asm-j2h5)
-- ----------------------------------------------------------------------------
--
-- Structural composition of one full square-and-multiply iteration with its
-- trailing counter-decrement + backward branch. This is the unit that the
-- 256-iteration loop scaffold (`evm_exp`, slice evm-asm-ahaz) repeats and that
-- the loop-composition spec (slice evm-asm-w5mk) reasons about.
--
-- Layout (8 instructions = 32 bytes per iteration):
--
--     exp_loop mulOff skipOff backOff :=
--       exp_iter_body  mulOff skipOff ;;   -- 6 instr (bit test + sq + cond mul)
--       exp_loop_back  backOff             -- 2 instr (ADDI x9 -1 ;; BNE)
--
-- The three offsets stay parameters — they are only pinned once `evm_exp` is
-- assembled in slice evm-asm-ahaz and the absolute layout is final. No new
-- specs in this slice; per-block specs (4a/4b/4c/4d) are already merged and
-- the composed cpsTriple lands in slice 5 (evm-asm-w5mk).

/-- One full iteration of the EXP square-and-multiply loop, including the
    iteration-counter decrement and backward branch back to the top. 8
    instructions.

    `mulOff` is the signed JAL offset to `mul_callable` (shared between the
    two JAL sites inside the iteration body). `skipOff` is the BEQ branch
    offset that skips past the conditional-multiply JAL when the current
    exponent bit is zero. `backOff` is the signed 13-bit BNE byte offset from
    the BNE site back to the top of the iteration body (negative). All three
    are pinned by the surrounding `evm_exp` layout in slice evm-asm-ahaz. -/
def exp_loop (mulOff : BitVec 21) (skipOff backOff : BitVec 13) : Program :=
  exp_iter_body mulOff skipOff ;;
  exp_loop_back backOff

theorem exp_loop_length (mulOff : BitVec 21) (skipOff backOff : BitVec 13) :
    (exp_loop mulOff skipOff backOff).length = 8 := by
  show (exp_iter_body mulOff skipOff ;; exp_loop_back backOff).length = 8
  simp only [seq, Program.length_append,
    exp_iter_body_length, exp_loop_back_length]

theorem exp_loop_byte_length (mulOff : BitVec 21) (skipOff backOff : BitVec 13) :
    4 * (exp_loop mulOff skipOff backOff).length = 32 := by
  rw [exp_loop_length]

-- ----------------------------------------------------------------------------
-- Loop prologue: initialize accumulator + counter (#92 slice 3d, beads
-- evm-asm-yvfr)
-- ----------------------------------------------------------------------------
--
-- The EXP body needs two pieces of
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

theorem exp_prologue_byte_length : 4 * exp_prologue.length = 24 := by
  rw [exp_prologue_length]

-- ----------------------------------------------------------------------------
-- Loop epilogue: result writeback + EVM stack advance (#92 slice 3e, beads
-- evm-asm-tesj)
-- ----------------------------------------------------------------------------
--
-- On result write-back: once the
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

theorem exp_epilogue_byte_length : 4 * exp_epilogue.length = 36 := by
  rw [exp_epilogue_length]

-- ----------------------------------------------------------------------------
-- Per-iteration marshalling helpers (#92 slice 3-marshal-factor1, beads
-- evm-asm-6hue)
-- ----------------------------------------------------------------------------
--
-- Every
-- per-iteration MUL call (both the unconditional squaring and the
-- conditional multiply by base `a`) needs to copy the running accumulator
-- `result` (held in the local scratch frame at `sp + 0 .. sp + 24`) into
-- the LP64 MUL factor-1 slot at `x12 + 0 .. x12 + 24`. This is the same
-- 8-instruction LD/SD chain in both call sites; we factor it out here as a
-- reusable `Program` so the two marshalling Programs (squaring marshal,
-- conditional-multiply marshal) can share it.
--
-- Register usage:
--   x2  — sp; read-only (local scratch frame base for `result`).
--   x12 — EVM stack pointer (a2); pointed at `x12_loop = sp_evm0 + 64`
--          by the prologue, so writes at offsets +0 .. +24 land in the
--          factor-1 slot disjoint from the operand region (`sp_evm0 + 0
--          .. + 56`).
--   x5  — t0, single-limb temporary; caller-saved per LP64 and not live
--          across the surrounding marshalling.

/-- Copy the four limbs of `result` from the local scratch frame at
    `sp + 0 .. sp + 24` into the LP64 MUL factor-1 slot at
    `x12 + 0 .. x12 + 24`. 8 instructions, 32 bytes.

    Used by both the squaring marshal (where factor-1 = factor-2 = result)
    and the conditional-multiply marshal (where factor-1 = result and
    factor-2 = a). Pure Program definition; spec lands in the
    marshalling-spec slice (evm-asm-mtj3 / evm-asm-w5mk follow-up). -/
def exp_loop_marshal_factor1 : Program :=
  LD .x5 .x2 0 ;;
  SD .x12 .x5 0 ;;
  LD .x5 .x2 8 ;;
  SD .x12 .x5 8 ;;
  LD .x5 .x2 16 ;;
  SD .x12 .x5 16 ;;
  LD .x5 .x2 24 ;;
  SD .x12 .x5 24

theorem exp_loop_marshal_factor1_length :
    exp_loop_marshal_factor1.length = 8 := by decide

theorem exp_loop_marshal_factor1_byte_length :
    4 * exp_loop_marshal_factor1.length = 32 := by
  rw [exp_loop_marshal_factor1_length]

-- ----------------------------------------------------------------------------
-- Per-iteration marshalling helpers (#92 slice 3-marshal-result-to-factor2,
-- beads evm-asm-z5yv)
-- ----------------------------------------------------------------------------
--
-- The squaring
-- step copies the running accumulator `result` into BOTH MUL operand slots
-- on the EVM stack: factor-1 at `x12 + 0..+24` (handled by
-- `exp_loop_marshal_factor1` above) and factor-2 at `x12 + 32..+56`
-- (handled here). This block mirrors `exp_loop_marshal_factor1` line for
-- line, only with the SD offsets shifted by +32 to land in the factor-2
-- window.
--
-- Register usage:
--   x2  — sp; read-only (local scratch frame base for `result`).
--   x12 — EVM stack pointer (a2); pointed at `x12_loop = sp_evm0 + 64`
--          by the prologue, so writes at offsets +32 .. +56 land in the
--          factor-2 slot disjoint from the operand region.
--   x5  — t0, single-limb temporary; caller-saved per LP64 and not live
--          across the surrounding marshalling.

/-- Copy the four limbs of `result` from the local scratch frame at
    `sp + 0 .. sp + 24` into the LP64 MUL factor-2 slot at
    `x12 + 32 .. x12 + 56`. 8 instructions, 32 bytes.

    Used by the squaring marshal where factor-1 = factor-2 = result, so
    this block runs immediately after `exp_loop_marshal_factor1` to
    populate the second operand slot before the JAL into `mul_callable`.
    Pure Program definition; spec lands in the marshalling-spec slice
    (evm-asm-mtj3 / evm-asm-w5mk follow-up). -/
def exp_loop_marshal_result_to_factor2 : Program :=
  LD .x5 .x2 0 ;;
  SD .x12 .x5 32 ;;
  LD .x5 .x2 8 ;;
  SD .x12 .x5 40 ;;
  LD .x5 .x2 16 ;;
  SD .x12 .x5 48 ;;
  LD .x5 .x2 24 ;;
  SD .x12 .x5 56

theorem exp_loop_marshal_result_to_factor2_length :
    exp_loop_marshal_result_to_factor2.length = 8 := by decide

theorem exp_loop_marshal_result_to_factor2_byte_length :
    4 * exp_loop_marshal_result_to_factor2.length = 32 := by
  rw [exp_loop_marshal_result_to_factor2_length]

-- ----------------------------------------------------------------------------
-- Per-iteration marshalling helpers (#92 slice 3-marshal-a-to-factor2,
-- beads evm-asm-18wt)
-- ----------------------------------------------------------------------------
--
-- The
-- conditional-multiply step copies the EVM-stack base operand `a` (held in
-- the slot `x12 + (-64) .. x12 + (-40)` — i.e. the original `a` window
-- that survives below the loop's working `x12 = x12_loop = sp_evm0 + 64`)
-- into the LP64 MUL factor-2 slot at `x12 + 32 .. x12 + 56`. This block
-- mirrors `exp_loop_marshal_factor1` / `exp_loop_marshal_result_to_factor2`
-- line for line, only with the LD source offsets shifted to negative
-- signed 12-bit immediates addressing the saved `a` window.
--
-- Register usage:
--   x12 — EVM stack pointer (a2); pointed at `x12_loop = sp_evm0 + 64`
--          by the prologue. LDs at offsets -64..-40 read the original
--          `a` operand; SDs at offsets +32..+56 write the factor-2
--          window. Both windows are disjoint from the operand region
--          (`sp_evm0 + 0 .. + 56`) at the time the `cond_mul`
--          marshalling runs.
--   x5  — t0, single-limb temporary; caller-saved per LP64 and not live
--          across the surrounding marshalling.

/-- Copy the four limbs of EVM-stack base operand `a` from
    `x12 + (-64) .. x12 + (-40)` into the LP64 MUL factor-2 slot at
    `x12 + 32 .. x12 + 56`. 8 instructions, 32 bytes.

    Used by the conditional-multiply marshalling sequence (where
    factor-1 = `result` and factor-2 = `a`); runs immediately after
    `exp_loop_marshal_factor1` to populate the second operand slot
    before the JAL into `mul_callable`. Pure Program definition; spec
    lands in the marshalling-spec slice (evm-asm-mtj3 / evm-asm-w5mk
    follow-up). -/
def exp_loop_marshal_a_to_factor2 : Program :=
  LD .x5 .x12 (-64) ;;
  SD .x12 .x5 32 ;;
  LD .x5 .x12 (-56) ;;
  SD .x12 .x5 40 ;;
  LD .x5 .x12 (-48) ;;
  SD .x12 .x5 48 ;;
  LD .x5 .x12 (-40) ;;
  SD .x12 .x5 56

theorem exp_loop_marshal_a_to_factor2_length :
    exp_loop_marshal_a_to_factor2.length = 8 := by decide

theorem exp_loop_marshal_a_to_factor2_byte_length :
    4 * exp_loop_marshal_a_to_factor2.length = 32 := by
  rw [exp_loop_marshal_a_to_factor2_length]


-- ----------------------------------------------------------------------------
-- Per-iteration un-marshalling tail (#92 slice 3-un-marshal, beads
-- evm-asm-shtuc)
-- ----------------------------------------------------------------------------
--
-- On the squaring and cond-mul tails:
-- every per-iteration MUL call (both the unconditional
-- squaring and the taken branch of the conditional multiply by base `a`)
-- ends with the same 9-instruction tail. The MUL output sits at
-- `x12_loop + 32 .. x12_loop + 56`, but `mul_callable` advanced `x12` by
-- +32, so from the post-call EVM stack pointer the output is at
-- `x12 + 0 .. x12 + 24`. We copy it back into the local scratch frame at
-- `sp + 0 .. sp + 24` (so the next iteration sees `result` updated in
-- place), then `ADDI .x12 .x12 (-32)` to undo MUL's pop and restore
-- `x12 := x12_loop` for the next iteration's marshalling.
--
-- This helper is the same in both call sites (squaring and cond-mul taken
-- path), so we factor it out as a single `Program` block. Pure Program
-- definition; spec lands in the marshalling-spec slice (`evm-asm-mtj3` /
-- `evm-asm-w5mk` follow-up).
--
-- Register usage:
--   x12 — EVM stack pointer (a2); on entry points at `x12_loop + 32`
--          (MUL advanced it by +32). The four LDs at offsets +0..+24 read
--          the MUL output from that window. Final `ADDI .x12 .x12 (-32)`
--          restores `x12 := x12_loop` for the next iteration.
--   x2  — sp; read-only (local scratch frame base for `result`). The four
--          SDs at offsets +0..+24 write the new `result` limbs into the
--          local frame.
--   x5  — t0, single-limb load/store temporary; caller-saved per LP64 and
--          not live across the surrounding marshalling.

/-- Un-marshal MUL output and restore the loop EVM stack pointer.
    Copies the four limbs of MUL output from the post-call EVM-stack
    window at `x12 + 0 .. x12 + 24` (= `x12_loop + 32 .. x12_loop + 56`,
    since `mul_callable` advanced `x12` by +32) back into the local
    scratch frame at `sp + 0 .. sp + 24`, then advances `x12` by -32 to
    restore `x12 := x12_loop` for the next iteration. 9 instructions,
    36 bytes.

    Used by both the squaring tail (`evm-asm-mtj3`) and the
    conditional-multiply taken-branch tail (`evm-asm-w5mk` follow-up).
    Pure Program definition; spec lands in the marshalling-spec slice. -/
def exp_loop_un_marshal_and_restore : Program :=
  LD .x5 .x12 0 ;;
  SD .x2 .x5 0 ;;
  LD .x5 .x12 8 ;;
  SD .x2 .x5 8 ;;
  LD .x5 .x12 16 ;;
  SD .x2 .x5 16 ;;
  LD .x5 .x12 24 ;;
  SD .x2 .x5 24 ;;
  ADDI .x12 .x12 (-32)

theorem exp_loop_un_marshal_and_restore_length :
    exp_loop_un_marshal_and_restore.length = 9 := by decide

theorem exp_loop_un_marshal_and_restore_byte_length :
    4 * exp_loop_un_marshal_and_restore.length = 36 := by
  rw [exp_loop_un_marshal_and_restore_length]

-- ----------------------------------------------------------------------------
-- Per-iteration squaring call (#92 slice 3-squaring-call, beads evm-asm-ywrjr)
-- ----------------------------------------------------------------------------
--
-- The per-iteration squaring step
-- composes four already-merged sub-blocks:
--
--   exp_squaring_call_block mulOff :=
--     exp_loop_marshal_factor1                ;;  -- 8 instr (32 bytes)
--     exp_loop_marshal_result_to_factor2      ;;  -- 8 instr (32 bytes)
--     exp_square_block mulOff                 ;;  -- 1 instr (4 bytes; JAL → mul)
--     exp_loop_un_marshal_and_restore             -- 9 instr (36 bytes)
--
-- Total: 26 instructions = 104 bytes.
-- Pure structural composition: marshalling specs land in the limb-level
-- slice (`evm-asm-mtj3`) and the full-loop composition in `evm-asm-w5mk`.

/-- Per-iteration squaring step: marshal factor1 + result→factor2, JAL into
    `mul_callable`, then un-marshal and restore the scratch frame. 26
    instructions. -/
def exp_squaring_call_block (mulOff : BitVec 21) : Program :=
  exp_loop_marshal_factor1 ;;
  exp_loop_marshal_result_to_factor2 ;;
  exp_square_block mulOff ;;
  exp_loop_un_marshal_and_restore

theorem exp_squaring_call_block_length (mulOff : BitVec 21) :
    (exp_squaring_call_block mulOff).length = 26 := by
  show (((exp_loop_marshal_factor1 ;;
          exp_loop_marshal_result_to_factor2) ;;
         exp_square_block mulOff) ;;
        exp_loop_un_marshal_and_restore).length = 26
  simp only [seq, Program.length_append,
    exp_loop_marshal_factor1_length,
    exp_loop_marshal_result_to_factor2_length,
    exp_square_block_length,
    exp_loop_un_marshal_and_restore_length]

theorem exp_squaring_call_block_byte_length (mulOff : BitVec 21) :
    4 * (exp_squaring_call_block mulOff).length = 104 := by
  rw [exp_squaring_call_block_length]


-- ----------------------------------------------------------------------------
-- Conditional-multiply taken-branch composite: exp_cond_mul_call_block
-- (#92 slice 3-cond-mul-call, beads evm-asm-1uu01)
-- ----------------------------------------------------------------------------
--
-- Sibling of `exp_squaring_call_block` (slice evm-asm-ywrjr). The
-- conditional-multiply taken-branch performs the same 4-block composition
-- as the squaring tail, but loads the base `a` into the `factor2` slot
-- instead of copying `result` into it. The surrounding scaffold
-- (`evm_exp`, slice evm-asm-ahaz) hoists the BEQ that skips this block
-- when the current exponent bit is zero.
--
-- Layout (26 instructions = 104 bytes):
--
--     exp_cond_mul_call_block mulOff :=
--       exp_loop_marshal_factor1 ;;            -- 8 instr (place result at f1 slot)
--       exp_loop_marshal_a_to_factor2 ;;       -- 8 instr (place base `a` at f2 slot)
--       exp_square_block mulOff ;;             -- 1 instr (JAL mul_callable)
--       exp_loop_un_marshal_and_restore        -- 9 instr (copy MUL output back; ADDI x12 -32)
--
-- The block name retains `_call` to mirror `exp_squaring_call_block`; the
-- conditional gating (BEQ skip when `x10 == 0`) is composed in by the
-- top-level `evm_exp` layout, not by this block. Pure structural
-- composition; per-iteration limb specs land in evm-asm-mtj3 and the
-- full-loop spec in evm-asm-w5mk.

/-- Conditional-multiply (taken-branch) composite for one EXP iteration:
    marshal `result` into the LP64 `factor1` slot, marshal base `a` into
    the LP64 `factor2` slot, JAL into `mul_callable`, and copy the MUL
    output back into the local scratch frame while restoring `x12` to
    its pre-call position. 26 instructions, 104 bytes.

    `mulOff` is the signed 21-bit JAL offset to `mul_callable` (shared
    with `exp_squaring_call_block` and the bare `exp_square_block`; the
    concrete numeric value is pinned once the surrounding `evm_exp`
    layout is final in slice evm-asm-ahaz). -/
def exp_cond_mul_call_block (mulOff : BitVec 21) : Program :=
  exp_loop_marshal_factor1 ;;
  exp_loop_marshal_a_to_factor2 ;;
  exp_square_block mulOff ;;
  exp_loop_un_marshal_and_restore

theorem exp_cond_mul_call_block_length (mulOff : BitVec 21) :
    (exp_cond_mul_call_block mulOff).length = 26 := by
  show (((exp_loop_marshal_factor1 ;;
            exp_loop_marshal_a_to_factor2) ;;
            exp_square_block mulOff) ;;
          exp_loop_un_marshal_and_restore).length = 26
  simp only [seq, Program.length_append,
    exp_loop_marshal_factor1_length,
    exp_loop_marshal_a_to_factor2_length,
    exp_square_block_length,
    exp_loop_un_marshal_and_restore_length]

theorem exp_cond_mul_call_block_byte_length (mulOff : BitVec 21) :
    4 * (exp_cond_mul_call_block mulOff).length = 104 := by
  rw [exp_cond_mul_call_block_length]



-- ----------------------------------------------------------------------------
-- Conditional-multiply with BEQ skip gate: exp_cond_mul_call_with_skip_block
-- (#92 slice 3-cond-mul-with-skip, beads evm-asm-qqz3m)
-- ----------------------------------------------------------------------------
--
-- Wraps `exp_cond_mul_call_block` with the leading BEQ instruction that
-- skips past the entire 26-instruction taken-branch composite when the
-- current exponent bit is zero (`x10 == 0`). Per
-- The per-iteration conditional
-- multiply step has shape
--
--     BEQ x10, x0, +108                ;; skip taken branch (1 instr)
--     exp_cond_mul_call_block mulOff   ;; taken: marshal+JAL+un-marshal (26 instr)
--
-- Pure structural composition; no specs in this slice. The BEQ branch
-- offset is the byte distance from the BEQ site to the instruction
-- immediately past the taken branch — i.e. exactly the byte length of
-- `exp_cond_mul_call_block` (= 104 bytes / 26 instr). Callers must pin
-- `skipOff` accordingly when they assemble the surrounding `evm_exp`
-- layout in slice evm-asm-ahaz.

/-- Conditional-multiply step with BEQ skip gate: `BEQ x10, x0, skipOff`
    followed by the 26-instruction taken-branch composite
    `exp_cond_mul_call_block mulOff`. 27 instructions, 108 bytes. -/
def exp_cond_mul_call_with_skip_block
    (mulOff : BitVec 21) (skipOff : BitVec 13) : Program :=
  single (.BEQ .x10 .x0 skipOff) ;;
  exp_cond_mul_call_block mulOff

/-- Conditional-multiply step that branches on the saved EXP bit in `x18`
    rather than caller-saved `x10`. 27 instructions, 108 bytes. -/
def exp_cond_mul_call_with_saved_bit_skip_block
    (mulOff : BitVec 21) (skipOff : BitVec 13) : Program :=
  single (.BEQ .x18 .x0 skipOff) ;;
  exp_cond_mul_call_block mulOff

theorem exp_cond_mul_call_with_skip_block_length
    (mulOff : BitVec 21) (skipOff : BitVec 13) :
    (exp_cond_mul_call_with_skip_block mulOff skipOff).length = 27 := by
  show (single (.BEQ .x10 .x0 skipOff) ;;
        exp_cond_mul_call_block mulOff).length = 27
  simp only [seq, Program.length_append, exp_cond_mul_call_block_length]
  rfl

theorem exp_cond_mul_call_with_skip_block_byte_length
    (mulOff : BitVec 21) (skipOff : BitVec 13) :
    4 * (exp_cond_mul_call_with_skip_block mulOff skipOff).length = 108 := by
  rw [exp_cond_mul_call_with_skip_block_length]

theorem exp_cond_mul_call_with_saved_bit_skip_block_length
    (mulOff : BitVec 21) (skipOff : BitVec 13) :
    (exp_cond_mul_call_with_saved_bit_skip_block mulOff skipOff).length = 27 := by
  show (single (.BEQ .x18 .x0 skipOff) ;;
        exp_cond_mul_call_block mulOff).length = 27
  simp only [seq, Program.length_append, exp_cond_mul_call_block_length]
  rfl

theorem exp_cond_mul_call_with_saved_bit_skip_block_byte_length
    (mulOff : BitVec 21) (skipOff : BitVec 13) :
    4 * (exp_cond_mul_call_with_saved_bit_skip_block mulOff skipOff).length = 108 := by
  rw [exp_cond_mul_call_with_saved_bit_skip_block_length]



-- ----------------------------------------------------------------------------
-- Full per-iteration loop body: exp_iter_body_full
-- (#92 slice, beads evm-asm-cqsr9)
-- ----------------------------------------------------------------------------
--
-- One complete iteration of the EXP square-and-multiply loop, including the
-- per-iteration MUL marshalling for both the squaring step and the conditional
-- multiply, the BEQ skip gate around the conditional multiply, and the
-- counter-decrement + backward branch tail. This is the unit that the
-- 256-iteration `evm_exp` body (slice evm-asm-ahaz) repeats.
--
-- Layout (58 instructions = 232 bytes per iteration):
--
--     exp_iter_body_full mulOff skipOff backOff :=
--       exp_bit_test_block                              ;;  -- 3 instr (bit test)
--       exp_squaring_call_block mulOff                  ;;  -- 26 instr (marshal+JAL+un-marshal)
--       exp_cond_mul_call_with_skip_block mulOff skipOff ;;  -- 27 instr (BEQ skip + cond mul call)
--       exp_loop_back backOff                                -- 2 instr (ADDI x9 -1 ;; BNE)
--
-- Per-block specs are already merged (slices 4a..4d, beads evm-asm-mtj3 covers
-- the limb-level composition); this slice is structural composition only.
-- The full-loop cpsTriple lands in slice 5 (evm-asm-w5mk).

/-- One full iteration of the EXP square-and-multiply loop, including
    per-iteration MUL marshalling for both the squaring step and the
    conditional multiply, the BEQ skip gate around the conditional
    multiply, and the iteration-counter decrement + backward branch.
    58 instructions, 232 bytes.

    `mulOff` is the signed 21-bit JAL offset to `mul_callable` (shared by
    the squaring and conditional-multiply call sites). `skipOff` is the
    BEQ branch offset that skips past the conditional-multiply taken
    branch when the current exponent bit is zero (= 108 bytes when the
    surrounding layout is final). `backOff` is the signed 13-bit BNE byte
    offset back to the top of the iteration body (negative). All three
    are pinned by the surrounding `evm_exp` layout in slice
    evm-asm-ahaz. -/
def exp_iter_body_full
    (mulOff : BitVec 21) (skipOff backOff : BitVec 13) : Program :=
  exp_bit_test_block ;;
  exp_squaring_call_block mulOff ;;
  exp_cond_mul_call_with_skip_block mulOff skipOff ;;
  exp_loop_back backOff

/-- Corrected EXP iteration body for the square-result algorithm: scan the
    exponent limb MSB-first, save the tested bit before `mul_callable`
    clobbers caller-saved registers, then branch on the saved copy. 59
    instructions, 236 bytes. -/
def exp_iter_body_full_msb_saved_bit
    (mulOff : BitVec 21) (skipOff backOff : BitVec 13) : Program :=
  exp_msb_bit_test_block ;;
  exp_save_bit_block ;;
  exp_squaring_call_block mulOff ;;
  exp_cond_mul_call_with_saved_bit_skip_block mulOff skipOff ;;
  exp_loop_back backOff

/-- Corrected EXP iteration body with independent MUL-call offsets for the
    unconditional squaring call and the conditional-multiply call.  The two
    call sites sit at different PCs, so a single encoded JAL offset cannot
    target one shared `mul_callable` body from both sites. -/
def exp_iter_body_full_msb_saved_bit_two_mul
    (squaringMulOff condMulOff : BitVec 21)
    (skipOff backOff : BitVec 13) : Program :=
  exp_msb_bit_test_block ;;
  exp_save_bit_block ;;
  exp_squaring_call_block squaringMulOff ;;
  exp_cond_mul_call_with_saved_bit_skip_block condMulOff skipOff ;;
  exp_loop_back backOff

theorem exp_iter_body_full_length
    (mulOff : BitVec 21) (skipOff backOff : BitVec 13) :
    (exp_iter_body_full mulOff skipOff backOff).length = 58 := by
  show (((exp_bit_test_block ;;
          exp_squaring_call_block mulOff) ;;
         exp_cond_mul_call_with_skip_block mulOff skipOff) ;;
        exp_loop_back backOff).length = 58
  simp only [seq, Program.length_append,
    exp_bit_test_block_length,
    exp_squaring_call_block_length,
    exp_cond_mul_call_with_skip_block_length,
    exp_loop_back_length]

theorem exp_iter_body_full_byte_length
    (mulOff : BitVec 21) (skipOff backOff : BitVec 13) :
    4 * (exp_iter_body_full mulOff skipOff backOff).length = 232 := by
  rw [exp_iter_body_full_length]

theorem exp_iter_body_full_msb_saved_bit_length
    (mulOff : BitVec 21) (skipOff backOff : BitVec 13) :
    (exp_iter_body_full_msb_saved_bit mulOff skipOff backOff).length = 59 := by
  show ((((exp_msb_bit_test_block ;;
          exp_save_bit_block) ;;
          exp_squaring_call_block mulOff) ;;
         exp_cond_mul_call_with_saved_bit_skip_block mulOff skipOff) ;;
        exp_loop_back backOff).length = 59
  simp only [seq, Program.length_append,
    exp_msb_bit_test_block_length,
    exp_save_bit_block_length,
    exp_squaring_call_block_length,
    exp_cond_mul_call_with_saved_bit_skip_block_length,
    exp_loop_back_length]

theorem exp_iter_body_full_msb_saved_bit_byte_length
    (mulOff : BitVec 21) (skipOff backOff : BitVec 13) :
    4 * (exp_iter_body_full_msb_saved_bit mulOff skipOff backOff).length = 236 := by
  rw [exp_iter_body_full_msb_saved_bit_length]

theorem exp_iter_body_full_msb_saved_bit_two_mul_length
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13) :
    (exp_iter_body_full_msb_saved_bit_two_mul
      squaringMulOff condMulOff skipOff backOff).length = 59 := by
  show ((((exp_msb_bit_test_block ;;
          exp_save_bit_block) ;;
          exp_squaring_call_block squaringMulOff) ;;
         exp_cond_mul_call_with_saved_bit_skip_block condMulOff skipOff) ;;
        exp_loop_back backOff).length = 59
  simp only [seq, Program.length_append,
    exp_msb_bit_test_block_length,
    exp_save_bit_block_length,
    exp_squaring_call_block_length,
    exp_cond_mul_call_with_saved_bit_skip_block_length,
    exp_loop_back_length]

theorem exp_iter_body_full_msb_saved_bit_two_mul_byte_length
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13) :
    4 * (exp_iter_body_full_msb_saved_bit_two_mul
      squaringMulOff condMulOff skipOff backOff).length = 236 := by
  rw [exp_iter_body_full_msb_saved_bit_two_mul_length]


-- ----------------------------------------------------------------------------
-- EVM-stack pointer advance/restore (#92 slice, beads evm-asm-zk5v9)
-- ----------------------------------------------------------------------------
--
-- The EXP loop body runs with `x12`
-- pointed at `x12_loop = sp_evm0 + 64` rather than at the original EVM stack
-- base `sp_evm0`. The +64 advance moves the in-loop "MUL operand window"
-- (`x12 + 0 .. x12 + 56`) above the original `a`/`b` operand window
-- (`sp_evm0 + 0 .. + 56`) so MUL's outputs at `x12_loop + 32 .. + 56` do
-- NOT clobber the original operands. The advance is done once between the
-- prologue and the loop body; the inverse `-64` restore is done once after
-- the loop body (before `exp_epilogue` copies `result` out and applies the
-- final `+32` EVM `pop`).
--
-- These are single-instruction Programs; we package them as named blocks so
-- the surrounding `evm_exp` layout (slice evm-asm-ahaz) and the full-loop
-- composition (slice evm-asm-w5mk) can compose them structurally with the
-- other `exp_*` sub-blocks already defined above.

/-- Single-instruction block that advances the EVM stack pointer `x12` by
    +64 bytes (one EXP loop-frame offset), moving from `sp_evm0` to
    `x12_loop = sp_evm0 + 64`. Emitted once between the EXP prologue and
    the 256-iteration square-and-multiply loop body. 1 instruction. -/
def exp_loop_pointer_advance : Program :=
  ADDI .x12 .x12 64

theorem exp_loop_pointer_advance_length :
    exp_loop_pointer_advance.length = 1 := rfl

theorem exp_loop_pointer_advance_byte_length :
    4 * exp_loop_pointer_advance.length = 4 := by
  rw [exp_loop_pointer_advance_length]

/-- Single-instruction block that restores the EVM stack pointer `x12` from
    `x12_loop = sp_evm0 + 64` back to the original EVM stack base
    `sp_evm0`. Emitted once after the 256-iteration square-and-multiply
    loop body, immediately before `exp_epilogue` copies the running
    accumulator `result` out to the EVM stack and applies the final `+32`
    EVM `pop`. 1 instruction. -/
def exp_loop_pointer_restore : Program :=
  ADDI .x12 .x12 (-64)

theorem exp_loop_pointer_restore_length :
    exp_loop_pointer_restore.length = 1 := rfl

theorem exp_loop_pointer_restore_byte_length :
    4 * exp_loop_pointer_restore.length = 4 := by
  rw [exp_loop_pointer_restore_length]

-- ----------------------------------------------------------------------------
-- EVM-stack caller-slot SAVE / RESTORE (bug evm-asm-fjivz)
-- ----------------------------------------------------------------------------
--
-- The 256-iteration loop uses the EVM stack window `x12_loop + 0 .. + 56`
-- (= `sp_evm0 + 64 .. + 120`, the two caller stack words below the EXP
-- operands) as transient MUL marshalling scratch and never restores it.
-- For EXP to honour the standard stack contract (pop base+exp, push the
-- result, preserve the rest of the caller stack), those two words must be
-- preserved across the loop. We copy them, once, into the free headroom
-- below the live EVM stack top (`sp_evm0 - 64 .. - 8`, inside the 512-byte
-- slack guaranteed around the EVM stack) before the loop, and copy them
-- back afterwards. Both blocks run with `x12 = sp_evm0` (the SAVE block is
-- emitted between the prologue and `exp_loop_pointer_advance`; the RESTORE
-- block between `exp_loop_pointer_restore` and `exp_epilogue`). They use
-- `x6` as the copy temporary, which is `regOwn` (don't-care) at loop entry
-- and is freely clobbered by the loop body, so no live value is disturbed.

/-- Save the two caller EVM-stack words at `x12 + 64 .. + 120` (the eight
    8-byte limbs the loop overwrites as MUL scratch) into the free headroom
    at `x12 - 64 .. - 8`. Runs with `x12 = sp_evm0`. 16 instructions. -/
def exp_loop_stack_save : Program :=
  LD .x6 .x12 64 ;; SD .x12 .x6 (-64) ;;
  LD .x6 .x12 72 ;; SD .x12 .x6 (-56) ;;
  LD .x6 .x12 80 ;; SD .x12 .x6 (-48) ;;
  LD .x6 .x12 88 ;; SD .x12 .x6 (-40) ;;
  LD .x6 .x12 96 ;; SD .x12 .x6 (-32) ;;
  LD .x6 .x12 104 ;; SD .x12 .x6 (-24) ;;
  LD .x6 .x12 112 ;; SD .x12 .x6 (-16) ;;
  LD .x6 .x12 120 ;; SD .x12 .x6 (-8)

theorem exp_loop_stack_save_length : exp_loop_stack_save.length = 16 := by decide

theorem exp_loop_stack_save_byte_length :
    4 * exp_loop_stack_save.length = 64 := by
  rw [exp_loop_stack_save_length]

/-- Architecture-B operand copy: copy the two live EVM-stack operands
    `base` (`x12 + 0 .. + 24`) and `exponent` (`x12 + 32 .. + 56`) into the
    headroom loop frame below the live stack, at `base → x12 - 128 .. - 104`
    and `exponent → x12 - 96 .. - 72`. Runs with `x12 = sp_evm0` (the live
    stack top), before `exp_loop_pointer_advance` sets `x12 := sp_evm0 - 64`
    (= the headroom `evmSp_iter`, with `base` at `evmSp_iter - 64` and
    `exponent` at `evmSp_iter - 32`). The loop then runs entirely in the
    headroom slack, leaving the live stack untouched. 16 instructions. -/
def exp_loop_operand_copy : Program :=
  LD .x6 .x12 0 ;; SD .x12 .x6 (-128) ;;
  LD .x6 .x12 8 ;; SD .x12 .x6 (-120) ;;
  LD .x6 .x12 16 ;; SD .x12 .x6 (-112) ;;
  LD .x6 .x12 24 ;; SD .x12 .x6 (-104) ;;
  LD .x6 .x12 32 ;; SD .x12 .x6 (-96) ;;
  LD .x6 .x12 40 ;; SD .x12 .x6 (-88) ;;
  LD .x6 .x12 48 ;; SD .x12 .x6 (-80) ;;
  LD .x6 .x12 56 ;; SD .x12 .x6 (-72)

theorem exp_loop_operand_copy_length : exp_loop_operand_copy.length = 16 := by decide

/-- Restore the two caller EVM-stack words saved by `exp_loop_stack_save`
    from the headroom at `x12 - 64 .. - 8` back to `x12 + 64 .. + 120`.
    Runs with `x12 = sp_evm0` (after `exp_loop_pointer_restore`, before
    `exp_epilogue` writes the result to `x12 + 32 .. + 56`). 16 instructions. -/
def exp_loop_stack_restore : Program :=
  LD .x6 .x12 (-64) ;; SD .x12 .x6 64 ;;
  LD .x6 .x12 (-56) ;; SD .x12 .x6 72 ;;
  LD .x6 .x12 (-48) ;; SD .x12 .x6 80 ;;
  LD .x6 .x12 (-40) ;; SD .x12 .x6 88 ;;
  LD .x6 .x12 (-32) ;; SD .x12 .x6 96 ;;
  LD .x6 .x12 (-24) ;; SD .x12 .x6 104 ;;
  LD .x6 .x12 (-16) ;; SD .x12 .x6 112 ;;
  LD .x6 .x12 (-8) ;; SD .x12 .x6 120

theorem exp_loop_stack_restore_length : exp_loop_stack_restore.length = 16 := by decide

theorem exp_loop_stack_restore_byte_length :
    4 * exp_loop_stack_restore.length = 64 := by
  rw [exp_loop_stack_restore_length]

-- ----------------------------------------------------------------------------
-- Top-level `evm_exp` Program assembly (#92 slice 3, beads evm-asm-ahaz /
-- evm-asm-3pil2)
-- ----------------------------------------------------------------------------
--
-- Composes the EXP-specific sub-blocks defined above into the full EXP
-- Program. Layout (75 instructions, 300 bytes):
--
--     evm_exp mulOff skipOff backOff :=
--       exp_prologue                                   --  6 instr (init counter + accumulator)
--       exp_loop_pointer_advance                       --  1 instr (ADDI x12 +64)
--       exp_iter_body_full mulOff skipOff backOff      -- 58 instr (one square+cond-mul iter + BNE)
--       exp_loop_pointer_restore                       --  1 instr (ADDI x12 -64)
--       exp_epilogue                                   --  9 instr (writeback + ADDI x12 +32)
--
-- The `exp_iter_body_full` block already contains the trailing
-- `exp_loop_back` (counter decrement + BNE back-edge), so it is emitted
-- **once** in the static layout — the 256 dynamic iterations come from
-- the BNE re-entering the top of `exp_iter_body_full` until `x9` reaches
-- zero. The three offset parameters have canonical values pinned by
-- this layout:
--
--   `mulOff`  : signed 21-bit JAL byte offset from the JAL site (inside
--               `exp_iter_body_full`) to `mul_callable`. Concrete value
--               depends on where `mul_callable` is placed in the address
--               space relative to `evm_exp`; left as a parameter here so
--               the surrounding non-leaf wrapper / dispatcher can pin it
--               once the call site is final.
--   `skipOff` : signed 13-bit BEQ byte offset from the BEQ-skip site to
--               the instruction immediately past `exp_cond_mul_call_block`.
--               Canonical value: +108 (1 BEQ instr + 26-instr taken
--               branch = 27 × 4 = 108 bytes; RISC-V BEQ offset is added
--               to the BEQ's own PC, so the target is BEQ_pc + 108).
--   `backOff` : signed 13-bit BNE byte offset from the BNE site at the
--               tail of `exp_iter_body_full` back to the top of
--               `exp_iter_body_full`. Canonical value: -228 (the BNE
--               site sits at byte +256 within `evm_exp`, the iter-body
--               top sits at byte +28 within `evm_exp`, so the back-edge
--               offset is 28 - 256 = -228).
--
-- This slice is purely structural assembly + length lemmas. The
-- per-iteration cpsTriple specs land in slice 4 (evm-asm-mtj3 +
-- children) and the full-loop composition / stack-level spec land in
-- slices 5 and 6 (evm-asm-w5mk / evm-asm-6snn).

/-- Top-level EXP opcode Program: prologue ;; pointer-advance ;;
    one statically-emitted iteration body (which contains the BNE
    back-edge so 256 dynamic iterations re-execute it) ;; pointer-restore
    ;; epilogue. 75 instructions, 300 bytes.

    `mulOff` is the signed 21-bit JAL byte offset to `mul_callable`,
    shared by both JAL sites inside `exp_iter_body_full`. `skipOff` is
    the signed 13-bit BEQ byte offset that skips past the conditional
    multiply when the current exponent bit is zero (canonical: +108).
    `backOff` is the signed 13-bit BNE byte offset back to the top of
    the iteration body (canonical: -228). -/
def evm_exp (mulOff : BitVec 21) (skipOff backOff : BitVec 13) : Program :=
  exp_prologue ;;
  exp_loop_pointer_advance ;;
  exp_iter_body_full mulOff skipOff backOff ;;
  exp_loop_pointer_restore ;;
  exp_epilogue

/-- Corrected EXP opcode Program using the MSB-first saved-bit iteration body.
    This keeps the square-result algorithm aligned with the exponent bit order
    and preserves the tested bit across `mul_callable`. 76 instructions. -/
def evm_exp_msb_saved_bit
    (mulOff : BitVec 21) (skipOff backOff : BitVec 13) : Program :=
  exp_prologue ;;
  exp_loop_pointer_advance ;;
  exp_iter_body_full_msb_saved_bit mulOff skipOff backOff ;;
  exp_loop_pointer_restore ;;
  exp_epilogue

/-- Corrected EXP opcode Program with independent MUL-call offsets for the
    squaring and conditional-multiply JAL sites. -/
def evm_exp_msb_saved_bit_two_mul
    (squaringMulOff condMulOff : BitVec 21)
    (skipOff backOff : BitVec 13) : Program :=
  exp_prologue ;;
  exp_loop_pointer_advance ;;
  exp_iter_body_full_msb_saved_bit_two_mul
    squaringMulOff condMulOff skipOff backOff ;;
  exp_loop_pointer_restore ;;
  exp_epilogue

/-- Canonical BEQ offset for skipping the conditional-multiply taken branch. -/
def canonicalExpCondMulSkipOff : BitVec 13 := 108

/-- Canonical BNE back-edge offset from the loop tail to the iteration top. -/
def canonicalExpLoopBackOff : BitVec 13 := -228

/-- Canonical BNE back-edge for the corrected MSB-first saved-bit layout. -/
def canonicalExpMsbSavedBitLoopBackOff : BitVec 13 := -232

/-- Canonical BNE back-edge for the fixed x19 saved-bit layout. -/
def canonicalExpMsbSavedBitFixedLoopBackOff : BitVec 13 := -248

/-- Canonical JAL offset from the saved-bit squaring call site to an appended
    `mul_callable` body immediately after the 304-byte EXP wrapper. -/
def canonicalExpSquaringMulOff : BitVec 21 := 196

/-- Canonical JAL offset from the saved-bit conditional-multiply call site to an
    appended `mul_callable` body immediately after the 304-byte EXP wrapper. -/
def canonicalExpCondMulOff : BitVec 21 := 88

/-- EXP program with the internal branch offsets pinned by the canonical layout.
    The MUL call offset remains external because it depends on the caller's
    placement of `mul_callable`. -/
def evm_exp_canonical (mulOff : BitVec 21) : Program :=
  evm_exp mulOff canonicalExpCondMulSkipOff canonicalExpLoopBackOff

/-- Corrected EXP program with the internal branch offsets pinned by the
    MSB-first saved-bit layout. The MUL call offset remains external. -/
def evm_exp_msb_saved_bit_canonical (mulOff : BitVec 21) : Program :=
  evm_exp_msb_saved_bit mulOff
    canonicalExpCondMulSkipOff canonicalExpMsbSavedBitLoopBackOff

/-- Corrected EXP program with canonical internal branch offsets and separate
    external MUL-call offsets for the two JAL sites. -/
def evm_exp_msb_saved_bit_two_mul_canonical
    (squaringMulOff condMulOff : BitVec 21) : Program :=
  evm_exp_msb_saved_bit_two_mul squaringMulOff condMulOff
    canonicalExpCondMulSkipOff canonicalExpMsbSavedBitLoopBackOff

theorem canonicalExpCondMulSkipOff_eq :
    canonicalExpCondMulSkipOff = 108 := rfl

theorem canonicalExpLoopBackOff_eq :
    canonicalExpLoopBackOff = -228 := rfl

theorem canonicalExpMsbSavedBitLoopBackOff_eq :
    canonicalExpMsbSavedBitLoopBackOff = -232 := rfl

theorem canonicalExpMsbSavedBitFixedLoopBackOff_eq :
    canonicalExpMsbSavedBitFixedLoopBackOff = -248 := rfl

theorem canonicalExpSquaringMulOff_eq :
    canonicalExpSquaringMulOff = 196 := rfl

theorem canonicalExpCondMulOff_eq :
    canonicalExpCondMulOff = 88 := rfl

theorem canonicalExpCondMulSkip_target (base : Word) :
    (base + 148 : Word) + signExtend13 canonicalExpCondMulSkipOff =
      base + 256 := by
  rw [canonicalExpCondMulSkipOff_eq]
  have h : signExtend13 (108 : BitVec 13) = (108 : Word) := by decide
  simp only [h]; bv_omega

theorem canonicalExpMsbSavedBitLoopBack_target (base : Word) :
    ((base + 256) + 4 : Word) +
        signExtend13 canonicalExpMsbSavedBitLoopBackOff =
      base + 28 := by
  rw [canonicalExpMsbSavedBitLoopBackOff_eq]
  have h : signExtend13 ((-232 : BitVec 13)) = (18446744073709551384 : Word) := by decide
  simp only [h]; bv_omega

theorem canonicalExpMsbSavedBitFixedLoopBack_target (base : Word) :
    (((base + 44) + 244) + 4 : Word) +
        signExtend13 canonicalExpMsbSavedBitFixedLoopBackOff =
      base + 44 := by
  rw [canonicalExpMsbSavedBitFixedLoopBackOff_eq]
  have h : signExtend13 ((-248 : BitVec 13)) = (18446744073709551368 : Word) := by decide
  simp only [h]; bv_omega

theorem canonicalExpSquaringMul_target (base : Word) :
    ((base + 44) + 64 : Word) + signExtend21 canonicalExpSquaringMulOff =
      base + 304 := by
  rw [canonicalExpSquaringMulOff_eq]
  have h : signExtend21 (196 : BitVec 21) = (196 : Word) := by decide
  simp only [h]; bv_omega

theorem canonicalExpFixedSquaringMul_target (base : Word) :
    (((base + 44) + 32) + 64 : Word) +
        signExtend21 canonicalExpSquaringMulOff =
      base + 336 := by
  rw [canonicalExpSquaringMulOff_eq]
  have h : signExtend21 (196 : BitVec 21) = (196 : Word) := by decide
  simp only [h]; bv_omega

theorem canonicalExpFixedCondMulSkip_target (base : Word) :
    ((base + 44) + 136 : Word) +
        signExtend13 canonicalExpCondMulSkipOff =
      (base + 44) + 244 := by
  rw [canonicalExpCondMulSkipOff_eq]
  have h : signExtend13 (108 : BitVec 13) = (108 : Word) := by decide
  simp only [h]; bv_omega

theorem canonicalExpCondMul_target (base : Word) :
    ((base + 152) + 64 : Word) + signExtend21 canonicalExpCondMulOff =
      base + 304 := by
  rw [canonicalExpCondMulOff_eq]
  have h : signExtend21 (88 : BitVec 21) = (88 : Word) := by decide
  simp only [h]; bv_omega

theorem canonicalExpFixedCondMul_target (base : Word) :
    (((base + 44) + 140) + 64 : Word) +
        signExtend21 canonicalExpCondMulOff =
      base + 336 := by
  rw [canonicalExpCondMulOff_eq]
  have h : signExtend21 (88 : BitVec 21) = (88 : Word) := by decide
  simp only [h]; bv_omega

theorem evm_exp_canonical_eq (mulOff : BitVec 21) :
    evm_exp_canonical mulOff =
      evm_exp mulOff canonicalExpCondMulSkipOff canonicalExpLoopBackOff := rfl

theorem evm_exp_msb_saved_bit_canonical_eq (mulOff : BitVec 21) :
    evm_exp_msb_saved_bit_canonical mulOff =
      evm_exp_msb_saved_bit mulOff
        canonicalExpCondMulSkipOff canonicalExpMsbSavedBitLoopBackOff := rfl

theorem evm_exp_msb_saved_bit_two_mul_canonical_eq
    (squaringMulOff condMulOff : BitVec 21) :
    evm_exp_msb_saved_bit_two_mul_canonical squaringMulOff condMulOff =
      evm_exp_msb_saved_bit_two_mul squaringMulOff condMulOff
        canonicalExpCondMulSkipOff canonicalExpMsbSavedBitLoopBackOff := rfl

theorem evm_exp_length (mulOff : BitVec 21) (skipOff backOff : BitVec 13) :
    (evm_exp mulOff skipOff backOff).length = 75 := by
  show ((((exp_prologue ;;
            exp_loop_pointer_advance) ;;
            exp_iter_body_full mulOff skipOff backOff) ;;
            exp_loop_pointer_restore) ;;
          exp_epilogue).length = 75
  simp only [seq, Program.length_append,
    exp_prologue_length,
    exp_loop_pointer_advance_length,
    exp_iter_body_full_length,
    exp_loop_pointer_restore_length,
    exp_epilogue_length]

theorem evm_exp_byte_length (mulOff : BitVec 21) (skipOff backOff : BitVec 13) :
    4 * (evm_exp mulOff skipOff backOff).length = 300 := by
  rw [evm_exp_length]

theorem evm_exp_msb_saved_bit_length
    (mulOff : BitVec 21) (skipOff backOff : BitVec 13) :
    (evm_exp_msb_saved_bit mulOff skipOff backOff).length = 76 := by
  show ((((exp_prologue ;;
            exp_loop_pointer_advance) ;;
            exp_iter_body_full_msb_saved_bit mulOff skipOff backOff) ;;
            exp_loop_pointer_restore) ;;
          exp_epilogue).length = 76
  simp only [seq, Program.length_append,
    exp_prologue_length,
    exp_loop_pointer_advance_length,
    exp_iter_body_full_msb_saved_bit_length,
    exp_loop_pointer_restore_length,
    exp_epilogue_length]

theorem evm_exp_msb_saved_bit_byte_length
    (mulOff : BitVec 21) (skipOff backOff : BitVec 13) :
    4 * (evm_exp_msb_saved_bit mulOff skipOff backOff).length = 304 := by
  rw [evm_exp_msb_saved_bit_length]

theorem evm_exp_msb_saved_bit_two_mul_length
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13) :
    (evm_exp_msb_saved_bit_two_mul
      squaringMulOff condMulOff skipOff backOff).length = 76 := by
  show ((((exp_prologue ;;
            exp_loop_pointer_advance) ;;
            exp_iter_body_full_msb_saved_bit_two_mul
              squaringMulOff condMulOff skipOff backOff) ;;
            exp_loop_pointer_restore) ;;
          exp_epilogue).length = 76
  simp only [seq, Program.length_append,
    exp_prologue_length,
    exp_loop_pointer_advance_length,
    exp_iter_body_full_msb_saved_bit_two_mul_length,
    exp_loop_pointer_restore_length,
    exp_epilogue_length]

theorem evm_exp_msb_saved_bit_two_mul_byte_length
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13) :
    4 * (evm_exp_msb_saved_bit_two_mul
      squaringMulOff condMulOff skipOff backOff).length = 304 := by
  rw [evm_exp_msb_saved_bit_two_mul_length]

theorem evm_exp_canonical_length (mulOff : BitVec 21) :
    (evm_exp_canonical mulOff).length = 75 := by
  unfold evm_exp_canonical
  rw [evm_exp_length]

theorem evm_exp_canonical_byte_length (mulOff : BitVec 21) :
    4 * (evm_exp_canonical mulOff).length = 300 := by
  rw [evm_exp_canonical_length]

theorem evm_exp_msb_saved_bit_canonical_length (mulOff : BitVec 21) :
    (evm_exp_msb_saved_bit_canonical mulOff).length = 76 := by
  unfold evm_exp_msb_saved_bit_canonical
  rw [evm_exp_msb_saved_bit_length]

theorem evm_exp_msb_saved_bit_canonical_byte_length (mulOff : BitVec 21) :
    4 * (evm_exp_msb_saved_bit_canonical mulOff).length = 304 := by
  rw [evm_exp_msb_saved_bit_canonical_length]

theorem evm_exp_msb_saved_bit_two_mul_canonical_length
    (squaringMulOff condMulOff : BitVec 21) :
    (evm_exp_msb_saved_bit_two_mul_canonical
      squaringMulOff condMulOff).length = 76 := by
  unfold evm_exp_msb_saved_bit_two_mul_canonical
  rw [evm_exp_msb_saved_bit_two_mul_length]

theorem evm_exp_msb_saved_bit_two_mul_canonical_byte_length
    (squaringMulOff condMulOff : BitVec 21) :
    4 * (evm_exp_msb_saved_bit_two_mul_canonical
      squaringMulOff condMulOff).length = 304 := by
  rw [evm_exp_msb_saved_bit_two_mul_canonical_length]

-- ============================================================================
-- Fixed EXP prologue and iteration body: load exponent into x19 cursor
-- (GH #92, bead evm-asm-w5mk, bug: x5=1 at loop entry never reads exponent)
--
-- BUG ANALYSIS (2026-05-17): The original exp_prologue sets x5=1.
-- exp_msb_bit_test_block extracts MSB of x5 as the exponent bit.
-- But the squaring-call unmarshal (LD x5 x12 24) overwrites x5 with
-- (r^2).limb3 after every iteration. Since r starts at 1={1,0,0,0}
-- with limb3=0, x5→0 after iter 1 and never changes → bit=0 always.
-- The original loop computes r=1 for ALL inputs, not base^exp.
--
-- FIX DESIGN:
-- - Use x19 (callee-saved, preserved across mul_callable) as the
--   exponent cursor, initialized to exponentWord.getLimbN 3.
-- - Use x20 (callee-saved, preserved across mul_callable) as the per-limb
--   counter (counts down from 64 to 0). NOTE: x6 (caller-saved t1) is in
--   mul_callable's footprint and is clobbered by the squaring/cond-mul JALs,
--   so the counter must live in a callee-saved register like the x19 cursor.
-- - Use x16 as limb pointer (starts at &exponent.limb3, advances by -8
--   after each 64-bit limb is exhausted).
-- - Fixed prologue: load x19=exponent.limb3, x6=64, x16=&exponent.limb2.
-- - Fixed bit_test: extract from x19, shift x19, decrement x6;
--   when x6=0, reload x19 from x16 and advance x16.
-- - The rest of the iteration body (marshal/squaring/cond-mul) is
--   unchanged: x19 is callee-saved so it survives mul_callable calls.
-- ============================================================================

/-- Fixed EXP prologue: initialize accumulator to 1, master counter x9=256,
    per-limb counter x20=64, exponent cursor x19=exponent.getLimbN 3
    (loaded from x12+56 = evmSp+56 since x12=evmSp before pointer_advance),
    and limb pointer x16 pointing at the NEXT limb to reload (evmSp+48).
    10 instructions, 40 bytes. -/
def exp_prologue_fixed : Program :=
  ADDI .x9 .x0 256 ;;
  ADDI .x5 .x0 1 ;;
  SD .x2 .x5 0 ;;
  SD .x2 .x0 8 ;;
  SD .x2 .x0 16 ;;
  SD .x2 .x0 24 ;;
  ADDI .x20 .x0 64 ;;
  ADDI .x16 .x12 56 ;;
  LD .x19 .x16 0 ;;
  ADDI .x16 .x16 (-8)

theorem exp_prologue_fixed_length : exp_prologue_fixed.length = 10 := by decide

theorem exp_prologue_fixed_byte_length : 4 * exp_prologue_fixed.length = 40 := by
  rw [exp_prologue_fixed_length]

/-- Fixed MSB-first bit-test block: extract MSB of x19 (exponent cursor),
    advance cursor (SLLI x19 x19 1), decrement per-limb counter x20.
    When x20 = 0 (limb exhausted), reload x19 from x16 and advance x16 by -8.
    7 instructions (3 core + 4 reload). The reload branch skips 4 instructions
    (= 16 bytes) when x6 ≠ 0 after decrement. -/
def exp_msb_bit_test_block_fixed : Program :=
  SRLI .x10 .x19 63 ;;
  SLLI .x19 .x19 1 ;;
  ADDI .x20 .x20 (-1) ;;
  single (.BNE .x20 .x0 16) ;;
  LD .x19 .x16 0 ;;
  ADDI .x16 .x16 (-8) ;;
  ADDI .x20 .x0 64

theorem exp_msb_bit_test_block_fixed_length :
    exp_msb_bit_test_block_fixed.length = 7 := by decide

theorem exp_msb_bit_test_block_fixed_byte_length :
    4 * exp_msb_bit_test_block_fixed.length = 28 := by
  rw [exp_msb_bit_test_block_fixed_length]

/-- Fixed MSB-first saved-bit full iteration body using the corrected
    bit-test block (exp_msb_bit_test_block_fixed). All other blocks
    are unchanged: x19 is callee-saved and survives mul_callable calls. -/
def exp_iter_body_full_msb_saved_bit_two_mul_fixed
    (squaringMulOff condMulOff : BitVec 21)
    (skipOff backOff : BitVec 13) : Program :=
  exp_msb_bit_test_block_fixed ;;
  exp_save_bit_block ;;
  exp_squaring_call_block squaringMulOff ;;
  exp_cond_mul_call_with_saved_bit_skip_block condMulOff skipOff ;;
  exp_loop_back backOff

theorem exp_iter_body_full_msb_saved_bit_two_mul_fixed_length
    (squaringMulOff condMulOff : BitVec 21)
    (skipOff backOff : BitVec 13) :
    (exp_iter_body_full_msb_saved_bit_two_mul_fixed
      squaringMulOff condMulOff skipOff backOff).length = 63 := by
  show (((((exp_msb_bit_test_block_fixed ;;
            exp_save_bit_block) ;;
           exp_squaring_call_block squaringMulOff) ;;
          exp_cond_mul_call_with_saved_bit_skip_block condMulOff skipOff) ;;
         exp_loop_back backOff)).length = 63
  simp only [seq, Program.length_append,
    exp_msb_bit_test_block_fixed_length,
    exp_save_bit_block_length,
    exp_squaring_call_block_length,
    exp_cond_mul_call_with_saved_bit_skip_block_length,
    exp_loop_back_length]

theorem exp_iter_body_full_msb_saved_bit_two_mul_fixed_byte_length
    (squaringMulOff condMulOff : BitVec 21)
    (skipOff backOff : BitVec 13) :
    4 * (exp_iter_body_full_msb_saved_bit_two_mul_fixed
      squaringMulOff condMulOff skipOff backOff).length = 252 := by
  rw [exp_iter_body_full_msb_saved_bit_two_mul_fixed_length]

/-- Fixed EXP program with corrected prologue and bit-test block.
    The MUL call offsets and internal branch offsets are caller-supplied.
    NOTE: All internal branch offsets (skipOff, backOff) change relative
    to the original because the prologue is now 40 bytes (was 24) and
    the loop body is now 252 bytes/iter (was 236). -/
def evm_exp_msb_saved_bit_two_mul_fixed
    (squaringMulOff condMulOff : BitVec 21)
    (skipOff backOff : BitVec 13) : Program :=
  exp_prologue_fixed ;;
  exp_loop_pointer_advance ;;
  exp_iter_body_full_msb_saved_bit_two_mul_fixed
    squaringMulOff condMulOff skipOff backOff ;;
  exp_loop_pointer_restore ;;
  exp_epilogue

/-- Fixed x19 EXP program with canonical internal branch offsets and separate
    external MUL-call offsets for the two JAL sites. -/
def evm_exp_msb_saved_bit_two_mul_fixed_canonical
    (squaringMulOff condMulOff : BitVec 21) : Program :=
  evm_exp_msb_saved_bit_two_mul_fixed squaringMulOff condMulOff
    canonicalExpCondMulSkipOff canonicalExpMsbSavedBitFixedLoopBackOff

theorem evm_exp_msb_saved_bit_two_mul_fixed_canonical_eq
    (squaringMulOff condMulOff : BitVec 21) :
    evm_exp_msb_saved_bit_two_mul_fixed_canonical squaringMulOff condMulOff =
      evm_exp_msb_saved_bit_two_mul_fixed squaringMulOff condMulOff
        canonicalExpCondMulSkipOff canonicalExpMsbSavedBitFixedLoopBackOff := rfl

theorem evm_exp_msb_saved_bit_two_mul_fixed_length
    (squaringMulOff condMulOff : BitVec 21)
    (skipOff backOff : BitVec 13) :
    (evm_exp_msb_saved_bit_two_mul_fixed
      squaringMulOff condMulOff skipOff backOff).length = 84 := by
  show ((((exp_prologue_fixed ;;
           exp_loop_pointer_advance) ;;
          exp_iter_body_full_msb_saved_bit_two_mul_fixed
            squaringMulOff condMulOff skipOff backOff) ;;
         exp_loop_pointer_restore) ;;
        exp_epilogue).length = 84
  simp only [seq, Program.length_append,
    exp_prologue_fixed_length,
    exp_loop_pointer_advance_length,
    exp_iter_body_full_msb_saved_bit_two_mul_fixed_length,
    exp_loop_pointer_restore_length,
    exp_epilogue_length]

theorem evm_exp_msb_saved_bit_two_mul_fixed_byte_length
    (squaringMulOff condMulOff : BitVec 21)
    (skipOff backOff : BitVec 13) :
    4 * (evm_exp_msb_saved_bit_two_mul_fixed
      squaringMulOff condMulOff skipOff backOff).length = 336 := by
  rw [evm_exp_msb_saved_bit_two_mul_fixed_length]

/-- Corrected EXP program that SAVES the two caller EVM-stack words below the
    operands (`x12 + 64 .. + 120`, transiently clobbered by the loop's MUL
    factor marshalling) into the headroom slack (`x12 - 64 .. - 8`) before the
    loop and RESTORES them afterwards, so the caller stack tail is preserved.
    Fixes the stack-corruption bug `evm-asm-fjivz`:

        exp_prologue_fixed          -- 10 instr (init counter + accumulator)
        exp_loop_stack_save         -- 16 instr (back up slots [2],[3] to headroom)
        exp_loop_pointer_advance    --  1 instr (ADDI x12 +64)
        exp_iter_body_full_…_fixed  -- 63 instr (one square+cond-mul iter + BNE)
        exp_loop_pointer_restore    --  1 instr (ADDI x12 -64)
        exp_loop_stack_restore      -- 16 instr (restore slots [2],[3] from headroom)
        exp_epilogue                --  9 instr (writeback result + ADDI x12 +32)

    116 instructions, 464 bytes. The loop body now sits at byte offset +108
    (vs +44 without save), shifting all downstream code offsets by +64. -/
def evm_exp_msb_saved_bit_two_mul_fixed_saverestore
    (squaringMulOff condMulOff : BitVec 21)
    (skipOff backOff : BitVec 13) : Program :=
  exp_prologue_fixed ;;
  exp_loop_stack_save ;;
  exp_loop_pointer_advance ;;
  exp_iter_body_full_msb_saved_bit_two_mul_fixed
    squaringMulOff condMulOff skipOff backOff ;;
  exp_loop_pointer_restore ;;
  exp_loop_stack_restore ;;
  exp_epilogue

theorem evm_exp_msb_saved_bit_two_mul_fixed_saverestore_length
    (squaringMulOff condMulOff : BitVec 21)
    (skipOff backOff : BitVec 13) :
    (evm_exp_msb_saved_bit_two_mul_fixed_saverestore
      squaringMulOff condMulOff skipOff backOff).length = 116 := by
  show ((((((exp_prologue_fixed ;;
            exp_loop_stack_save) ;;
           exp_loop_pointer_advance) ;;
          exp_iter_body_full_msb_saved_bit_two_mul_fixed
            squaringMulOff condMulOff skipOff backOff) ;;
         exp_loop_pointer_restore) ;;
        exp_loop_stack_restore) ;;
       exp_epilogue).length = 116
  simp only [seq, Program.length_append,
    exp_prologue_fixed_length,
    exp_loop_stack_save_length,
    exp_loop_pointer_advance_length,
    exp_iter_body_full_msb_saved_bit_two_mul_fixed_length,
    exp_loop_pointer_restore_length,
    exp_loop_stack_restore_length,
    exp_epilogue_length]

theorem evm_exp_msb_saved_bit_two_mul_fixed_saverestore_byte_length
    (squaringMulOff condMulOff : BitVec 21)
    (skipOff backOff : BitVec 13) :
    4 * (evm_exp_msb_saved_bit_two_mul_fixed_saverestore
      squaringMulOff condMulOff skipOff backOff).length = 464 := by
  rw [evm_exp_msb_saved_bit_two_mul_fixed_saverestore_length]

/-- Corrected EXP program (architecture B) that runs the squaring loop entirely
    in the headroom slack so the live EVM stack is never clobbered. The prologue
    COPIES the two operands (`base`@`x12+0..24`, `exp`@`x12+32..56`) down into the
    headroom frame (`x12-128..-72`), the loop body then squares there (its MUL
    workspace at `x12_loop+0..56` lands in the slack, x12_loop = x12-64), and the
    epilogue writes the result back to the standard live slot `x12+32`. No
    save/restore block is needed (the live stack is framed through untouched), so
    `mul_callable` stays appended after the epilogue with no collision. Fixes
    `evm-asm-fjivz`:

        exp_prologue_fixed          -- 10 instr (init counter + accumulator, x12=evmSp)
        exp_loop_operand_copy       -- 16 instr (copy operands -> headroom)
        exp_loop_pointer_restore    --  1 instr (ADDI x12 -64 : the advance into headroom)
        exp_iter_body_full_…_fixed  -- 63 instr (square+cond-mul iter + BNE)
        exp_loop_pointer_advance    --  1 instr (ADDI x12 +64 : back to evmSp)
        exp_epilogue                --  9 instr (writeback result + ADDI x12 +32)

    100 instructions, 400 bytes; loop body at byte +108, exit (= mul_callable
    address) at +400. -/
def evm_exp_msb_saved_bit_two_mul_fixed_headroom
    (squaringMulOff condMulOff : BitVec 21)
    (skipOff backOff : BitVec 13) : Program :=
  exp_loop_operand_copy ;;
  exp_loop_pointer_restore ;;
  exp_loop_pointer_restore ;;
  exp_prologue_fixed ;;
  exp_loop_pointer_advance ;;
  exp_iter_body_full_msb_saved_bit_two_mul_fixed
    squaringMulOff condMulOff skipOff backOff ;;
  exp_loop_pointer_advance ;;
  exp_epilogue

theorem evm_exp_msb_saved_bit_two_mul_fixed_headroom_length
    (squaringMulOff condMulOff : BitVec 21)
    (skipOff backOff : BitVec 13) :
    (evm_exp_msb_saved_bit_two_mul_fixed_headroom
      squaringMulOff condMulOff skipOff backOff).length = 102 := by
  show (((((((exp_loop_operand_copy ;;
           exp_loop_pointer_restore) ;;
          exp_loop_pointer_restore) ;;
         exp_prologue_fixed) ;;
        exp_loop_pointer_advance) ;;
       exp_iter_body_full_msb_saved_bit_two_mul_fixed
         squaringMulOff condMulOff skipOff backOff) ;;
      exp_loop_pointer_advance) ;;
     exp_epilogue).length = 102
  simp only [seq, Program.length_append,
    exp_prologue_fixed_length,
    exp_loop_operand_copy_length,
    exp_loop_pointer_restore_length,
    exp_iter_body_full_msb_saved_bit_two_mul_fixed_length,
    exp_loop_pointer_advance_length,
    exp_epilogue_length]

theorem evm_exp_msb_saved_bit_two_mul_fixed_headroom_byte_length
    (squaringMulOff condMulOff : BitVec 21)
    (skipOff backOff : BitVec 13) :
    4 * (evm_exp_msb_saved_bit_two_mul_fixed_headroom
      squaringMulOff condMulOff skipOff backOff).length = 408 := by
  rw [evm_exp_msb_saved_bit_two_mul_fixed_headroom_length]

theorem evm_exp_msb_saved_bit_two_mul_fixed_loop_entry_byte_offset :
    4 * (exp_prologue_fixed.length + exp_loop_pointer_advance.length) = 44 := by
  rw [exp_prologue_fixed_length, exp_loop_pointer_advance_length]

theorem evm_exp_msb_saved_bit_two_mul_fixed_loop_body_end_byte_offset
    (squaringMulOff condMulOff : BitVec 21)
    (skipOff backOff : BitVec 13) :
    4 * (exp_prologue_fixed.length + exp_loop_pointer_advance.length +
      (exp_iter_body_full_msb_saved_bit_two_mul_fixed
        squaringMulOff condMulOff skipOff backOff).length) = 296 := by
  rw [exp_prologue_fixed_length, exp_loop_pointer_advance_length,
    exp_iter_body_full_msb_saved_bit_two_mul_fixed_length]

theorem evm_exp_msb_saved_bit_two_mul_fixed_epilogue_byte_offset
    (squaringMulOff condMulOff : BitVec 21)
    (skipOff backOff : BitVec 13) :
    4 * (exp_prologue_fixed.length + exp_loop_pointer_advance.length +
      (exp_iter_body_full_msb_saved_bit_two_mul_fixed
        squaringMulOff condMulOff skipOff backOff).length +
      exp_loop_pointer_restore.length) = 300 := by
  rw [exp_prologue_fixed_length, exp_loop_pointer_advance_length,
    exp_iter_body_full_msb_saved_bit_two_mul_fixed_length,
    exp_loop_pointer_restore_length]

-- ============================================================================
-- DOUBLE-FIXED EXP (x6 → x22): the per-limb counter clobber repair
--
-- The `_fixed` family above moved the exponent *cursor* to callee-saved x19,
-- but left the per-limb *counter* in x6. `mul_callable` (= `evm_mul ;; cc_ret`)
-- clobbers x6 ~51× per call, and the squaring / conditional-multiply blocks
-- call `mul_callable` MID-ITERATION — before the next `exp_msb_bit_test_block`
-- decrements/tests x6. So x6 is garbage on re-entry, producing wrong results
-- or an infinite reload loop (see `scripts/codegen-evm_exp-property-check.sh`).
--
-- This `_fixed_fixed` family is a pure register substitution x6 → x22 (s6) in
-- the prologue and bit-test block. x22 is callee-saved, untouched by
-- `evm_mul`/`cc_ret`, untouched by every other EXP block, and not reserved by
-- the codegen dispatcher (which reserves x10/x12/x13/x20/x21). Because it is a
-- pure substitution, all instruction counts and byte offsets are identical to
-- the `_fixed` family, so the canonical branch/MUL offsets carry over verbatim.
-- ============================================================================

/-- Double-fixed EXP prologue: identical to `exp_prologue_fixed` but the
    per-limb counter lives in callee-saved x22 (s6) instead of x6, which
    `mul_callable` clobbers. 10 instructions, 40 bytes. -/
def exp_prologue_fixed_fixed : Program :=
  ADDI .x9 .x0 256 ;;
  ADDI .x5 .x0 1 ;;
  SD .x2 .x5 0 ;;
  SD .x2 .x0 8 ;;
  SD .x2 .x0 16 ;;
  SD .x2 .x0 24 ;;
  ADDI .x22 .x0 64 ;;
  ADDI .x16 .x12 56 ;;
  LD .x19 .x16 0 ;;
  ADDI .x16 .x16 (-8)

theorem exp_prologue_fixed_fixed_length :
    exp_prologue_fixed_fixed.length = 10 := by decide

theorem exp_prologue_fixed_fixed_byte_length :
    4 * exp_prologue_fixed_fixed.length = 40 := by
  rw [exp_prologue_fixed_fixed_length]

/-- Double-fixed MSB-first bit-test block: identical to
    `exp_msb_bit_test_block_fixed` but the per-limb counter is x22 (s6),
    which survives `mul_callable` calls. 7 instructions, 28 bytes. -/
def exp_msb_bit_test_block_fixed_fixed : Program :=
  SRLI .x10 .x19 63 ;;
  SLLI .x19 .x19 1 ;;
  ADDI .x22 .x22 (-1) ;;
  single (.BNE .x22 .x0 16) ;;
  LD .x19 .x16 0 ;;
  ADDI .x16 .x16 (-8) ;;
  ADDI .x22 .x0 64

theorem exp_msb_bit_test_block_fixed_fixed_length :
    exp_msb_bit_test_block_fixed_fixed.length = 7 := by decide

theorem exp_msb_bit_test_block_fixed_fixed_byte_length :
    4 * exp_msb_bit_test_block_fixed_fixed.length = 28 := by
  rw [exp_msb_bit_test_block_fixed_fixed_length]

/-- Double-fixed MSB-first saved-bit full iteration body using the corrected
    counter register. All other blocks are unchanged: x16/x18/x19/x22 are all
    callee-saved (or untouched by `evm_mul`) and survive `mul_callable` calls. -/
def exp_iter_body_full_msb_saved_bit_two_mul_fixed_fixed
    (squaringMulOff condMulOff : BitVec 21)
    (skipOff backOff : BitVec 13) : Program :=
  exp_msb_bit_test_block_fixed_fixed ;;
  exp_save_bit_block ;;
  exp_squaring_call_block squaringMulOff ;;
  exp_cond_mul_call_with_saved_bit_skip_block condMulOff skipOff ;;
  exp_loop_back backOff

theorem exp_iter_body_full_msb_saved_bit_two_mul_fixed_fixed_length
    (squaringMulOff condMulOff : BitVec 21)
    (skipOff backOff : BitVec 13) :
    (exp_iter_body_full_msb_saved_bit_two_mul_fixed_fixed
      squaringMulOff condMulOff skipOff backOff).length = 63 := by
  show (((((exp_msb_bit_test_block_fixed_fixed ;;
            exp_save_bit_block) ;;
           exp_squaring_call_block squaringMulOff) ;;
          exp_cond_mul_call_with_saved_bit_skip_block condMulOff skipOff) ;;
         exp_loop_back backOff)).length = 63
  simp only [seq, Program.length_append,
    exp_msb_bit_test_block_fixed_fixed_length,
    exp_save_bit_block_length,
    exp_squaring_call_block_length,
    exp_cond_mul_call_with_saved_bit_skip_block_length,
    exp_loop_back_length]

theorem exp_iter_body_full_msb_saved_bit_two_mul_fixed_fixed_byte_length
    (squaringMulOff condMulOff : BitVec 21)
    (skipOff backOff : BitVec 13) :
    4 * (exp_iter_body_full_msb_saved_bit_two_mul_fixed_fixed
      squaringMulOff condMulOff skipOff backOff).length = 252 := by
  rw [exp_iter_body_full_msb_saved_bit_two_mul_fixed_fixed_length]

/-- Double-fixed EXP program: corrected prologue + bit-test block (x6 → x22).
    Byte-identical in layout to `evm_exp_msb_saved_bit_two_mul_fixed`, so the
    canonical branch/MUL offsets are reused unchanged. -/
def evm_exp_msb_saved_bit_two_mul_fixed_fixed
    (squaringMulOff condMulOff : BitVec 21)
    (skipOff backOff : BitVec 13) : Program :=
  exp_prologue_fixed_fixed ;;
  exp_loop_pointer_advance ;;
  exp_iter_body_full_msb_saved_bit_two_mul_fixed_fixed
    squaringMulOff condMulOff skipOff backOff ;;
  exp_loop_pointer_restore ;;
  exp_epilogue

/-- Double-fixed EXP with canonical internal branch offsets and separate
    external MUL-call offsets for the two JAL sites. -/
def evm_exp_msb_saved_bit_two_mul_fixed_fixed_canonical
    (squaringMulOff condMulOff : BitVec 21) : Program :=
  evm_exp_msb_saved_bit_two_mul_fixed_fixed squaringMulOff condMulOff
    canonicalExpCondMulSkipOff canonicalExpMsbSavedBitFixedLoopBackOff

theorem evm_exp_msb_saved_bit_two_mul_fixed_fixed_canonical_eq
    (squaringMulOff condMulOff : BitVec 21) :
    evm_exp_msb_saved_bit_two_mul_fixed_fixed_canonical squaringMulOff condMulOff =
      evm_exp_msb_saved_bit_two_mul_fixed_fixed squaringMulOff condMulOff
        canonicalExpCondMulSkipOff canonicalExpMsbSavedBitFixedLoopBackOff := rfl

theorem evm_exp_msb_saved_bit_two_mul_fixed_fixed_length
    (squaringMulOff condMulOff : BitVec 21)
    (skipOff backOff : BitVec 13) :
    (evm_exp_msb_saved_bit_two_mul_fixed_fixed
      squaringMulOff condMulOff skipOff backOff).length = 84 := by
  show ((((exp_prologue_fixed_fixed ;;
           exp_loop_pointer_advance) ;;
          exp_iter_body_full_msb_saved_bit_two_mul_fixed_fixed
            squaringMulOff condMulOff skipOff backOff) ;;
         exp_loop_pointer_restore) ;;
        exp_epilogue).length = 84
  simp only [seq, Program.length_append,
    exp_prologue_fixed_fixed_length,
    exp_loop_pointer_advance_length,
    exp_iter_body_full_msb_saved_bit_two_mul_fixed_fixed_length,
    exp_loop_pointer_restore_length,
    exp_epilogue_length]

theorem evm_exp_msb_saved_bit_two_mul_fixed_fixed_byte_length
    (squaringMulOff condMulOff : BitVec 21)
    (skipOff backOff : BitVec 13) :
    4 * (evm_exp_msb_saved_bit_two_mul_fixed_fixed
      squaringMulOff condMulOff skipOff backOff).length = 336 := by
  rw [evm_exp_msb_saved_bit_two_mul_fixed_fixed_length]

/-- Double-fixed (`x6 → x22`) EXP program in the architecture-B **headroom**
    layout — the dispatcher-safe combination of *both* EXP bug fixes.

    `evm_exp_msb_saved_bit_two_mul_fixed_headroom` fixes the stack-corruption
    bug `evm-asm-fjivz` (the loop's MUL scratch is marshalled into the headroom
    slack *below* the live stack instead of caller stack words [2]/[3]), but it
    is built from the `_fixed` blocks whose per-limb counter lives in `x20` — a
    register the codegen dispatcher reserves (`x20` = `evm_env` base, seeded
    once in `_start` and read on every dispatch iteration). Wiring that body
    into the dispatcher would clobber `x20` and corrupt dispatch state.

    This variant is byte-identical to `_headroom` (the `x20 → x22` counter
    substitution preserves every instruction count and offset) but keeps the
    counter in callee-saved `x22`, which `evm_mul`/`cc_ret` never touch and the
    dispatcher does not reserve. It is the body wired into `evmExpComposed`:

        exp_loop_operand_copy        -- 16 instr (copy operands -> headroom)
        exp_loop_pointer_restore     --  1 instr (ADDI x12 -64)
        exp_loop_pointer_restore     --  1 instr (ADDI x12 -64 : into headroom)
        exp_prologue_fixed_fixed     -- 10 instr (init counter x22 + accumulator)
        exp_loop_pointer_advance     --  1 instr (ADDI x12 +64 : loop frame)
        exp_iter_body_..._fixed_fixed -- 63 instr (square+cond-mul iter + BNE)
        exp_loop_pointer_advance     --  1 instr (ADDI x12 +64 : back to live)
        exp_epilogue                 --  9 instr (writeback result + ADDI x12 +32)

    102 instructions, 408 bytes; loop body at byte +116. The two interior
    MUL-call JAL sites and (once a skip-JAL + appended `mul_callable` follow)
    `mul_callable` itself both shift +72 bytes vs the non-headroom
    `_fixed_fixed` layout, so the canonical 200/92 call offsets used by
    `evmExpComposed` carry over unchanged. -/
def evm_exp_msb_saved_bit_two_mul_fixed_fixed_headroom
    (squaringMulOff condMulOff : BitVec 21)
    (skipOff backOff : BitVec 13) : Program :=
  exp_loop_operand_copy ;;
  exp_loop_pointer_restore ;;
  exp_loop_pointer_restore ;;
  exp_prologue_fixed_fixed ;;
  exp_loop_pointer_advance ;;
  exp_iter_body_full_msb_saved_bit_two_mul_fixed_fixed
    squaringMulOff condMulOff skipOff backOff ;;
  exp_loop_pointer_advance ;;
  exp_epilogue

theorem evm_exp_msb_saved_bit_two_mul_fixed_fixed_headroom_length
    (squaringMulOff condMulOff : BitVec 21)
    (skipOff backOff : BitVec 13) :
    (evm_exp_msb_saved_bit_two_mul_fixed_fixed_headroom
      squaringMulOff condMulOff skipOff backOff).length = 102 := by
  show (((((((exp_loop_operand_copy ;;
           exp_loop_pointer_restore) ;;
          exp_loop_pointer_restore) ;;
         exp_prologue_fixed_fixed) ;;
        exp_loop_pointer_advance) ;;
       exp_iter_body_full_msb_saved_bit_two_mul_fixed_fixed
         squaringMulOff condMulOff skipOff backOff) ;;
      exp_loop_pointer_advance) ;;
     exp_epilogue).length = 102
  simp only [seq, Program.length_append,
    exp_prologue_fixed_fixed_length,
    exp_loop_operand_copy_length,
    exp_loop_pointer_restore_length,
    exp_iter_body_full_msb_saved_bit_two_mul_fixed_fixed_length,
    exp_loop_pointer_advance_length,
    exp_epilogue_length]

theorem evm_exp_msb_saved_bit_two_mul_fixed_fixed_headroom_byte_length
    (squaringMulOff condMulOff : BitVec 21)
    (skipOff backOff : BitVec 13) :
    4 * (evm_exp_msb_saved_bit_two_mul_fixed_fixed_headroom
      squaringMulOff condMulOff skipOff backOff).length = 408 := by
  rw [evm_exp_msb_saved_bit_two_mul_fixed_fixed_headroom_length]

/-- Double-fixed headroom EXP with canonical internal branch offsets and
    separate external MUL-call offsets for the two JAL sites. -/
def evm_exp_msb_saved_bit_two_mul_fixed_fixed_headroom_canonical
    (squaringMulOff condMulOff : BitVec 21) : Program :=
  evm_exp_msb_saved_bit_two_mul_fixed_fixed_headroom squaringMulOff condMulOff
    canonicalExpCondMulSkipOff canonicalExpMsbSavedBitFixedLoopBackOff

theorem evm_exp_msb_saved_bit_two_mul_fixed_fixed_headroom_canonical_eq
    (squaringMulOff condMulOff : BitVec 21) :
    evm_exp_msb_saved_bit_two_mul_fixed_fixed_headroom_canonical squaringMulOff condMulOff =
      evm_exp_msb_saved_bit_two_mul_fixed_fixed_headroom squaringMulOff condMulOff
        canonicalExpCondMulSkipOff canonicalExpMsbSavedBitFixedLoopBackOff := rfl

end EvmAsm.Evm64
