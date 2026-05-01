# EXP opcode survey (GH issue #92, beads slice evm-asm-i8xy)

Authored by @pirapira; implemented by Hermes-bot (evm-hermes).

This document surveys the existing infrastructure that the EXP opcode
(`EXP(a, b) = a^b mod 2^256`) implementation will reuse. It is the
deliverable of slice 1 of evm-asm-20z6 / GH #92 and is referenced by
the directory-skeleton slice (evm-asm-cf2c) and Program-definition
slice (evm-asm-ahaz).

No code changes; this slice is documentation only.

## 1. Algorithm — square-and-multiply over 256-bit exponent

Standard binary square-and-multiply, processing the exponent `b` from
the most significant bit downward:

    result := 1
    for i in 255 .. 0:
        result := result * result            -- always (square)
        if bit i of b == 1:
            result := result * a             -- conditional multiply
    return result

EVM edge cases (must agree with execution-specs/.../vm/instructions/arithmetic.py
and yellow-paper §H.1):

  - `EXP(a, 0) = 1` — the loop performs zero multiplications, result stays 1.
  - `EXP(0, 0) = 1` — same as above; matches yellow paper.
  - `EXP(0, b) = 0` for b > 0 — falls out naturally (result starts 1,
    first set-bit triggers `result := result * 0 = 0`, then squares of 0
    stay 0 and conditional `* 0` stay 0).
  - `EXP(a, 1) = a` — the only set bit is bit 0; loop body squares 1
    repeatedly (still 1) until the last iteration, where bit 0 = 1 forces
    `result := 1 * a = a`.
  - `EXP(2, 256) = 0` — high bits of b nonzero, so we genuinely run 256
    squarings; `2^256 mod 2^256 = 0`.

256 iterations × (one squaring + at most one conditional multiply) gives
the natural loop bound. Each `result * result` and `result * a` is a
256-bit multiplication mod `2^256`.

## 2. Reuse from MUL — calling convention and call site

`EvmAsm/Evm64/Multiply/Program.lean` defines `evm_mul` and its sub-blocks
(`mul_col0` … `mul_col3`, plus `mul_epilogue`). The full program is 63
instructions = 252 bytes; `evm_mul_stack_spec_within` (in
`EvmAsm/Evm64/Multiply/Spec.lean`) is the verified entry point.

EXP must invoke `evm_mul` as a subroutine. Concrete reuse points:

(a) **MUL register/stack contract** — from `mul_col0`'s comments and from
    `evmMulStackPost` in `Multiply/Spec.lean`:

    Pre-call layout (sp = pre-call EVM stack pointer, x12 = sp):
        sp+0  .. sp+24:  a (4 LE limbs, limb 0 = LSB at sp+0)
        sp+32 .. sp+56:  b (4 LE limbs, limb 0 = LSB at sp+32)

    Post-call layout (x12 = sp + 32):
        sp+32 .. sp+56:  a * b (mod 2^256)
        sp, sp+8, sp+16, sp+24: scratch (memOwn, contents undefined)

    Scratch registers clobbered: x5, x6, x7, x10, x11.
    x12 advances by +32 (one EVM-word pop).

    Note: MUL today does **not** follow LP64 — it has no
    `cc_prologue` / `cc_epilogue`. It is invoked inline (not via `JAL x1`).
    EXP, being a non-leaf function that itself calls `evm_mul` 256+ times,
    SHOULD follow LP64 (`AGENTS.md` §"Calling Convention (LP64)"): use
    `cc_prologue` / `cc_epilogue` from `EvmAsm/Evm64/CallingConvention.lean`
    around the body, and invoke MUL via `JAL .x1 <off>` with `evm_mul`
    relocated as a subroutine block.

    Open question for slice-2 (skeleton): decide whether to call MUL via
    `JAL` (near call, fits in 21-bit signed offset = ±1 MiB — fine) and
    treat MUL as a verified callee, OR inline MUL's 252 bytes per
    iteration (would explode code size to ~130 KiB, infeasible). **The
    answer is JAL**: MUL must become callable. That has implications:
    `evm_mul` currently has no `cc_ret`, so we either (i) wrap it with
    a `mul_callable := evm_mul ;; cc_ret` shim and prove
    `callNear_function_spec` for it, or (ii) extend MUL itself to end in
    `cc_ret` (more invasive, would require a separate slice, ideally a
    sibling P3 task). Recommend (i) for slice-3.

(b) **EVM stack discipline for EXP** (binary opcode, pop 2 push 1):
    The EVM stack on entry holds `[..., a, b]` with `b` on top, i.e.
    `b` at `sp+0..sp+24` and `a` at `sp+32..sp+56`. EXP pops both and
    pushes `a^b` at `sp+32..sp+56`, with x12 advanced by +32.

    Inside the body, MUL expects `[..., factor1, factor2]` with the
    second factor at `sp+0..sp+24` and the first at `sp+32..sp+56`.
    EXP needs scratch space for `result` (the running accumulator).

    Proposed memory layout during EXP body, with `sp_local` = the local
    stack-frame base allocated by `cc_prologue` and `sp_evm` = x12:

        sp_evm + 0  .. sp_evm + 24:  exponent b (read-only, decremented bit
                                                 index lives in a register)
        sp_evm + 32 .. sp_evm + 56:  base a (read-only, copied into MUL slots
                                              for each multiply)
        scratch frame on RISC-V sp:  result (4 limbs, 32 B) + saved ra (8 B)
                                     + alignment (8 B) = 48 B frame

    Slice-2/3 will pin down the exact frame size and offsets. The key
    constraint: the body must NOT mutate `sp_evm + 0 .. sp_evm + 56`
    until the very end, when `result` is copied there for the push.

## 3. Bit extraction over a 256-bit exponent — reuse from Shift

`EvmAsm/Evm64/Shift/Program.lean` already extracts shift parameters
from a 256-bit value loaded as four 64-bit limbs. The relevant shapes:

  - `shr_phase_a` (lines 48-55): OR-reduces limbs 1..3 to detect "shift
    >= 256", then SLTIU on limb 0 against 256. EXP does NOT need this
    >= 256 short-circuit — the exponent is genuinely up to 256 bits.

  - `shr_phase_b` (lines 58-65): `ANDI x6, x5, 63` extracts bit-index
    within a limb; `SRLI x5, x5, 6` gives the limb index. EXP can reuse
    this exact pattern: maintain the bit index `i` from 255 down to 0,
    decompose `i = 64 * limb_idx + bit_idx`, load
    `b_limb[limb_idx]`, then test `(b_limb[limb_idx] >> bit_idx) & 1`
    via `SRL` + `ANDI 1`.

    However a simpler and more efficient pattern for the per-iteration
    bit test (recommended for slice-3) is:

        # invariant: x5 holds current limb of b, x6 = remaining bits in
        # this limb (init 64); shift x5 right by 1 each iter and refill
        # x5 from memory when x6 hits 0.

        # test bit:
        single (.ANDI .x10 .x5 1)   # x10 = current bit
        single (.SRLI .x5 .x5 1)    # advance
        single (.ADDI .x6 .x6 -1)   # decrement remaining bit count

    This avoids recomputing limb_idx / bit_idx each iteration. The
    "refill" path (when x6 == 0) advances limb_idx by +1 and reloads.

    Cross-reference: similar shift-and-test idioms appear in the SAR
    sign-fill cascade in `EvmAsm/Evm64/Shift/SarCompose.lean`.

## 4. Loop-body shape — reuse from DivMod

`EvmAsm/Evm64/DivMod/LoopBody/` and `LoopIterN1/` have the closest
analogue: a fixed-iteration-count outer loop with a per-iteration body
that conditionally branches on a flag (DivMod's borrow / "call vs skip"
maps onto EXP's "bit is 1 → multiply by a" vs "bit is 0 → skip").

Concrete patterns to mirror:

  - **Iteration counter via decrement-and-branch.** DivMod uses the
    fixed N=4 outer iteration unrolled; EXP at 256 iterations cannot
    unroll. Use a register (say x9) as `i` initialized to 256, with
    `ADDI x9, x9, -1` + `BNE x9, x0, <loop_top>` at the bottom. See
    `EvmAsm/Evm64/DivMod/Program.lean` for the BEQ/BNE-driven loop
    layout that survives the symbolic specs.

  - **Per-iteration `@[irreducible]` postcondition bundling.** Per
    `OPCODE_TEMPLATE.md` §"Unified-dispatch-first", the iteration
    postcondition `expIterPost (i : Nat) (a result : EvmWord) : Assertion`
    must be `@[irreducible]` from day one and have a single equation
    lemma `expIterPost_eq` (similar to DivMod's `loopIterPostN3Max_da`)
    so that consumers do not blow heartbeats unfolding `i` iterations
    of squaring + conditional multiply.

  - **Squaring + conditional multiply as TWO sub-blocks.** Following
    OPCODE_TEMPLATE's block-decomposition rule, the iteration body is:

        exp_iter_body :=
          exp_square_block ;;        -- always: result := result * result
          exp_cond_mul_block         -- branch on bit: maybe result := result * a

    Each gets its own LimbSpec entry; `exp_square_block` is a thin
    wrapper around a JAL into MUL with the `result, result` argument
    layout, and `exp_cond_mul_block` is a BEQ-skipped JAL into MUL with
    the `result, a` layout.

  - **Result write-back.** After the 256-iteration loop, copy `result`
    (4 limbs in scratch frame) to `sp_evm + 32 .. sp_evm + 56` and
    advance x12 by +32 (cf. MUL's `mul_epilogue` in
    `Multiply/Program.lean`).

## 5. Recommended directory layout (slice 2 input)

Per `EvmAsm/Evm64/OPCODE_TEMPLATE.md`:

    EvmAsm/Evm64/Exp/
      Program.lean        -- evm_exp Program, sub-blocks (square, cond_mul,
                             exp_iter_body, exp_loop, exp_prologue, exp_epilogue)
      LimbSpec.lean       -- per-block cpsTriple specs over the limb-level
                             memory model (raw memIs / regIs)
      AddrNormAttr.lean   -- declares @[exp_addr] (parallels @[divmod_addr])
      AddrNorm.lean       -- @[exp_addr]-tagged address equalities
      Compose/Base.lean   -- expCode, subsumption helpers, address normalization
      Compose/Loop.lean   -- 256-iteration loop composition with the
                             @[irreducible] iter postcondition + equation lemma
      Spec.lean           -- evm_exp_stack_spec_within: top-level cpsTripleWithin
                             with evmWordIs sp/sp+32 pre and post

Wire all six files into the umbrella in this order in `EvmAsm/Evm64.lean`:

    import EvmAsm.Evm64.Exp.AddrNormAttr   -- attr declared first
    import EvmAsm.Evm64.Exp.Program
    import EvmAsm.Evm64.Exp.LimbSpec
    import EvmAsm.Evm64.Exp.AddrNorm
    import EvmAsm.Evm64.Exp.Compose.Base
    import EvmAsm.Evm64.Exp.Compose.Loop
    import EvmAsm.Evm64.Exp.Spec

(See AGENTS.md §"New `.lean` files must be imported by the umbrella
module" for the `register_simp_attr` ordering rule.)

## 6. Open questions deferred to later slices

1. Make `evm_mul` callable: introduce `mul_callable := evm_mul ;; cc_ret`
   shim and prove `callNear_function_spec` for it. Propose as a
   sibling beads task, parent #92, before slice 3 (`evm_exp` Program).
   File as P3, blocks evm-asm-ahaz.

2. Exact frame size and offset map for the local RISC-V scratch frame
   (result + saved ra + alignment). Decide in slice 2 alongside the
   skeleton modules.

3. Whether to expose a `expIterPost_eq` equation lemma per-iteration or
   one polymorphic lemma keyed on `i`. The DivMod pattern (per-i
   equation lemmas proved once) scales; reuse it.

4. Native-decide tests for the EXP edge cases — file as part of the
   semantic-spec slice (evm-asm-6snn).

## 7. Summary table — concrete reuse points

| EXP need                  | Reuse from                          | File / decl                                          |
|---------------------------|-------------------------------------|------------------------------------------------------|
| 256-bit multiply          | MUL                                 | `EvmAsm/Evm64/Multiply/Spec.lean :: evm_mul_stack_spec_within` |
| Subroutine call/return    | LP64 calling convention             | `EvmAsm/Evm64/CallingConvention.lean :: cc_prologue, cc_epilogue, cc_ret, callNear_spec_within, ret_spec_within'` |
| Bit/limb decomposition    | SHR phase B                         | `EvmAsm/Evm64/Shift/Program.lean :: shr_phase_b`     |
| Fixed-count outer loop    | DivMod                              | `EvmAsm/Evm64/DivMod/Program.lean`, `DivMod/LoopBody/`, `DivMod/LoopDefs/` |
| Irreducible iter post     | DivMod's `loopIterPostN3Max_da`     | `EvmAsm/Evm64/DivMod/LoopDefs/` (pattern only)       |
| EvmWord stack assertion   | `evmWordIs`                         | `EvmAsm/Evm64/Stack.lean`                            |
| EvmWord post bridge       | MUL's `mul_stack_weaken`            | `EvmAsm/Evm64/Multiply/Spec.lean` (pattern only)     |

## 8. Acceptance / next-slice handoff

This slice is complete when:

  - This document is checked in under `docs/`.
  - The next slice (`evm-asm-cf2c`, directory skeleton) can read it
    and the §5 file list directly without further investigation.

No Lean code changes; CI should pass trivially.
