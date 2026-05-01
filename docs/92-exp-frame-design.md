# `evm_exp` scratch frame + per-iteration MUL marshalling — design note

GH issue [#92](https://github.com/Verified-zkEVM/evm-asm/issues/92),
beads slice `evm-asm-o2jv` (sub-slice of `evm-asm-ahaz`).

Authored by @pirapira; implemented by Hermes-bot (evm-hermes).

This note pins down the two pieces deferred from the
[`docs/92-exp-survey.md`](92-exp-survey.md) §6 open-question list:

1.  the exact local RISC-V scratch frame layout for `evm_exp` (size,
    offsets, role of each slot — open question 2);
2.  the per-iteration argument-marshalling sequence for the squaring
    JAL and the conditional-multiply JAL into `mul_callable`, plus the
    post-call un-marshalling that restores invariants for the next
    iteration (closes the gap flagged in the comment on
    `evm-asm-epgh`).

It is a documentation-only deliverable.  No `.lean` files change; the
output is consumed by the `evm_exp` Program-assembly slice
(`evm-asm-ahaz`) and the per-iteration cpsTriple compose slice
(`evm-asm-epgh` / `evm-asm-w5mk`).

## 1. EVM stack contract for EXP

EXP is a binary opcode (`pop 2, push 1`).  Following the standard EVM
convention (top-of-stack first), the EVM stack on entry holds
`[..., b, a]` with `a` (the base) on top, so the in-memory layout
relative to the entry EVM stack pointer `x12 = sp_evm0` is

    sp_evm0 + 0  .. sp_evm0 + 24:   a   (4 LE limbs, limb 0 at +0)
    sp_evm0 + 32 .. sp_evm0 + 56:   b   (4 LE limbs, limb 0 at +32)

EXP pops both operands and pushes one 256-bit result, so on exit
`x12 = sp_evm0 + 32` and the result occupies `sp_evm0 + 32 .. +56`.
This matches the "binary opcode advances `x12` by +32" convention
shared with MUL/ADD/SUB/etc.

Note (one delta from `docs/92-exp-survey.md` §2(b)): the survey said
"`b` on top", which would put `b` at `sp+0..sp+24`.  In practice EVM
operand order for `EXP(base, exponent)` is `base = a` on top of `b =
exponent`, see
`execution-specs/.../vm/instructions/arithmetic.py::exp`.  The
exponent is consumed by the bit-test cursor; the base is the factor
we feed into MUL on each conditional-multiply.  We use the convention
`a = base, b = exponent` consistently below.  Either choice is fine
provided the direction the bits of the exponent are scanned matches
which limb-set the bit-test register `x5` is preloaded from; we make
that explicit in §3.

## 2. MUL contract — restated

`mul_callable := evm_mul ;; cc_ret` (PR #1614, beads
`evm-asm-pp56`).  Called via `JAL .x1 mulOff`, expects:

  * pre-call:  `x12 = sp_M`,
                `sp_M + 0 .. sp_M + 24` holds factor `f1` (LE),
                `sp_M + 32 .. sp_M + 56` holds factor `f2` (LE).
  * scratch register clobber: `x5 x6 x7 x10 x11`.
  * post-call: `x12 = sp_M + 32`,
                `sp_M + 32 .. sp_M + 56` holds `f1 * f2 mod 2^256`,
                cells at `sp_M + 0 .. + 24` are clobbered (memOwn),
                `x1` overwritten by JAL return-address.

So **MUL eats one EVM word**: `x12` advances by +32.  In an EXP
iteration we run MUL up to twice without making net progress on the
EVM stack, so each MUL call must be bracketed with a
`x12 := x12 - 32` un-advance to restore the operand layout for the
next iteration's marshalling.

## 3. Local scratch frame layout

Per AGENTS.md §"Calling Convention (LP64)" `evm_exp` is a non-leaf
function (it calls `mul_callable`), so it emits `cc_prologue` /
`cc_epilogue` and decrements `sp` (= `x2`) at entry.  Total frame is
40 bytes, 8-byte aligned:

    Offset (rel. to local sp)   Size   Role
    -------------------------   ----   --------------------------------
    sp + 0  .. sp + 24           32    `result` accumulator, 4 LE limbs
    sp + 32                       8    saved `ra` (LP64 `cc_prologue`)
                                       Frame size = 40 B (5 dwords)

The accumulator `result` lives on the local frame, NOT on the EVM
stack: during the loop the EVM-stack region at `x12 + 0 .. x12 + 56`
is owned by MUL's argument layout and would be clobbered.

### Why a `b`-shadow is NOT needed

The survey raised the option of stashing `b` (the exponent) and `a`
(the base) into local-frame shadow slots so we can refill MUL's
factor slots cheaply each iteration.  After working it out, neither
shadow is necessary:

  * **Exponent `b`.**  Phase A (still part of the prologue, runs
    once before the loop) loads the four limbs of `b` into a
    register-resident shift cursor — concretely `x5` holds the
    "current limb" with bits already shifted past, and `x6` holds the
    bit-count remaining inside `x5`.  When `x6` hits zero we reload
    `x5` from the next limb of `b`, which still lives in its original
    EVM-stack slot at `x12 + 32 + 8*j`.  We **read** `b` from the EVM
    stack but never write into those slots inside the loop, because
    MUL's outputs go to `sp_M + 32 .. + 56` (= `x12 + 32 .. + 56` if
    `x12` is set to the EVM stack base = `sp_evm0`), which is the
    same region — so we MUST move `x12` away from `sp_evm0` for the
    loop body.  See §4.
  * **Base `a`.**  Same story.  `a` originally lives at
    `sp_evm0 + 0 .. + 24`.  We need it intact across all 256
    iterations.  Easiest is to keep `x12 = sp_evm0` only conceptually
    — actually we move `x12` forward by +64 at the top of the loop
    so that the in-loop "MUL slot region" is `sp_evm0 + 64 ..
    sp_evm0 + 120`, leaving `a` and `b` untouched at their original
    positions.  See §4 for the precise pointer dance.

### Updated frame size

40 bytes (5 dwords) — only `result` and saved `ra`.  Counter `x9` and
shift cursor `x5`/`x6` are register-resident.

## 4. EVM-stack pointer convention inside the loop

Let `x12_loop := sp_evm0 + 64`.  The prologue's pointer setup is

    ADDI .x12 .x12 64           -- x12 := sp_evm0 + 64

so that the in-loop "MUL operand slots" land at

    x12_loop + 0  .. x12_loop + 24   (= sp_evm0 + 64 .. + 88)
    x12_loop + 32 .. x12_loop + 56   (= sp_evm0 + 96 .. + 120)

These slots are owned by `evm_exp` for the duration of the loop and
are disjoint from both the operand region (`sp_evm0 + 0 .. + 56`) and
the local frame (`sp + 0 .. sp + 32`).  This requires that the caller
guarantees `sp_evm0 + 120` is below the EVM-stack guard — same
liveness condition as MUL but with one extra word of headroom (one
word, since MUL itself only needs 56 bytes above its `x12`).  Per
PLAN.md the EVM stack is checked-in-bulk at function entry; we add an
explicit acceptance criterion for the wrapper.

The epilogue (after the 256-iteration loop) un-does the pointer
move and copies `result` out:

  1. `ADDI .x12 .x12 (-64)` — restore `x12 := sp_evm0`.
  2. Copy `result` (4 limbs from `sp + 0 .. sp + 24`) to
     `sp_evm0 + 32 .. sp_evm0 + 56` via 4 × `(LD .x5 sp k ;; SD .x12
     .x5 (32+k))`.
  3. `ADDI .x12 .x12 32` — final EVM `pop`.

(This is exactly the existing `exp_epilogue` block from
`evm-asm-tesj`, plus the one-shot `-64` un-advance.)

## 5. Per-iteration marshalling — squaring JAL

Squaring is unconditional: `result := result * result`.  Both MUL
factors are the SAME 4-limb value held at `sp + 0 .. sp + 24` (local
frame).  We marshal:

    -- write `result` into MUL factor-1 slot at x12_loop + 0..+24
    LD   .x5  .x2  0          -- t0 := result.limb0
    SD   .x12 .x5  0          -- mul.f1.limb0 := t0
    LD   .x5  .x2  8
    SD   .x12 .x5  8
    LD   .x5  .x2  16
    SD   .x12 .x5  16
    LD   .x5  .x2  24
    SD   .x12 .x5  24

    -- write `result` into MUL factor-2 slot at x12_loop + 32..+56
    LD   .x5  .x2  0
    SD   .x12 .x5  32
    LD   .x5  .x2  8
    SD   .x12 .x5  40
    LD   .x5  .x2  16
    SD   .x12 .x5  48
    LD   .x5  .x2  24
    SD   .x12 .x5  56

    -- call MUL
    JAL  .x1  mulOff          -- exp_square_block

    -- un-marshal: read result from MUL output (x12 + 32 .. + 56,
    -- since MUL advanced x12 by +32 to x12_loop + 32) back into the
    -- local frame, and undo the +32 advance.
    LD   .x5  .x12 0          -- now reading from x12_loop + 32 + 0
    SD   .x2  .x5  0          --   = old MUL output limb0
    LD   .x5  .x12 8
    SD   .x2  .x5  8
    LD   .x5  .x12 16
    SD   .x2  .x5  16
    LD   .x5  .x12 24
    SD   .x2  .x5  24
    ADDI .x12 .x12 (-32)      -- restore x12 := x12_loop

Cost: 16 marshal + 1 JAL + 8 un-marshal + 1 ADDI = **26 instructions
per squaring**.

(Optimisation pass deferred: we could avoid 4 of the marshal writes
by doing the f1-write before MUL, then COPYING f1 into f2 with `LD/SD
sp+k offset+32` — saves 4 LDs.  Skipped from this design pass; track
as a separate beads task once the unoptimised assembly is verified.)

## 6. Per-iteration marshalling — conditional multiply JAL

Conditional multiply is `if x10 != 0 then result := result * a`.
Factor-1 is `result` (local frame), factor-2 is `a` (still at
`sp_evm0 + 0 .. + 24`).  But our pointer convention put MUL's slots
at `x12_loop + 0 .. + 56` = `sp_evm0 + 64 .. + 120`, so we cannot
just point MUL at `sp_evm0`; we must copy `a` into `x12_loop + 32 ..
+ 56`.

    BEQ  .x10 .x0  skipOff     -- skip past JAL if current bit = 0

    -- factor-1: result -> x12_loop + 0..+24  (8 instr)
    LD   .x5  .x2  0
    SD   .x12 .x5  0
    LD   .x5  .x2  8
    SD   .x12 .x5  8
    LD   .x5  .x2  16
    SD   .x12 .x5  16
    LD   .x5  .x2  24
    SD   .x12 .x5  24

    -- factor-2: a -> x12_loop + 32..+56  (8 instr)
    -- a lives at sp_evm0 = x12_loop - 64; reach via negative
    -- signExtend12 immediates on the LD.
    LD   .x5  .x12 (-64)       -- a.limb0 (sp_evm0 + 0  = x12_loop - 64)
    SD   .x12 .x5  32
    LD   .x5  .x12 (-56)       -- a.limb1
    SD   .x12 .x5  40
    LD   .x5  .x12 (-48)
    SD   .x12 .x5  48
    LD   .x5  .x12 (-40)
    SD   .x12 .x5  56

    -- call MUL
    JAL  .x1  mulOff

    -- un-marshal + restore x12 (same 9 instr as squaring tail)
    LD   .x5  .x12 0
    SD   .x2  .x5  0
    LD   .x5  .x12 8
    SD   .x2  .x5  8
    LD   .x5  .x12 16
    SD   .x2  .x5  16
    LD   .x5  .x12 24
    SD   .x2  .x5  24
    ADDI .x12 .x12 (-32)

Cost: 1 BEQ + 16 marshal + 1 JAL + 9 un-marshal = **27
instructions** on the taken path, 1 instruction on the skipped path.

`skipOff` (the BEQ branch offset) is `4 + 16*4 + 4 + 9*4 = 108` bytes
forward of the BEQ — i.e. branch past everything down to and
including the ADDI un-advance.  When skipped, we never executed
`JAL`, so `x12` was never advanced and we don't need the ADDI; the
BEQ target is therefore the instruction *after* the ADDI (the next
iteration's prologue / loop_back).

## 7. Updated per-iteration instruction count

| sub-block                     | instr | cumulative |
|-------------------------------|------:|-----------:|
| `exp_bit_test_block`          |     3 |          3 |
| **squaring marshal+call+un**  |  *26* |         29 |
| `exp_cond_mul_block`          |     2 |         31 |
| **cond-mul marshal+un**       |  *25* |         56 |
| `exp_loop_back`               |     2 |         58 |

Compared to the survey's "8 instructions per iteration" estimate
(which counted only the structural sub-blocks), the marshalling adds
~50 instructions per iteration — i.e. a ~7× expansion.  Total loop
body ≈ 232 bytes × 256 iterations ≈ 60 KiB, comfortably within the
±1 MiB JAL range.

This means the existing `exp_square_block` / `exp_cond_mul_block` /
`exp_iter_body` sub-blocks (slices 3a/3b, merged) are too narrow to
serve as the cpsTriple unit for slice 5 (`evm-asm-w5mk`); the
correct cpsTriple unit is `(marshal ;; JAL ;; un-marshal ;; ADDI)`,
where the marshal+un-marshal are themselves `runBlock`-shaped LD/SD
chains amenable to the standard byte-pack idioms in
`Evm64/MLoad/LimbSpec.lean`.

## 8. Action items handed off to slice 3 (`evm-asm-ahaz`)

1.  Define `exp_loop_marshal_factor1 : Program` (8 LD/SD pairs, copy
    local-frame `result` to `x12 + 0..+24`).
2.  Define `exp_loop_marshal_result_to_factor2 : Program` (8 LD/SD
    pairs, copy local-frame `result` to `x12 + 32..+56`) — the
    second half of the squaring marshal.  Reuses `factor1` only if
    we add a separate "copy local frame to x12+k" parameterized
    helper; not for this slice.
3.  Define `exp_loop_marshal_a_to_factor2 : Program` (8 LD/SD pairs
    with negative `signExtend12` LDs from `x12 + (-64..-40)`, copy
    `a` to `x12 + 32..+56`).
4.  Define `exp_loop_un_marshal_and_restore : Program` (4 LD/SD
    pairs writing MUL output back to `sp + 0..+24`, plus
    `ADDI .x12 .x12 (-32)`).
5.  Re-compose `exp_iter_body` from §3a's three sub-blocks PLUS the
    marshalling helpers above.  The current 6-instruction
    `exp_iter_body` (slice 3b, PR #1670) is structurally still
    correct as a sub-component but is not the iteration unit; it
    becomes the inner core wrapped by marshalling.
6.  Pin `mulOff`, `skipOff`, `backOff` once the full layout is
    fixed: prologue size, loop body size (~232 bytes), epilogue size
    are all final.

## 9. Action items for downstream slices

  * Slice 4 (`evm-asm-mtj3`) per-block specs already exist for
    `bit_test`, `square`, `cond_mul`, `loop_back`.  Add specs for the
    new marshalling blocks (`exp_loop_marshal_*` — runBlocks of
    LD/SD chains over the `regIs` + `memIs` model, no surprises).
  * Slice 4-compose (`evm-asm-epgh`) — re-target.  Per the comment
    on that slice the current 4-spec compose is not the right unit;
    after this design lands, the compose is
    `bit_test ;; (marshal_f1 ;; marshal_f2 ;; square ;;
    un_marshal) ;; cond_mul ;; (marshal_f1 ;; marshal_a ;; JAL ;;
    un_marshal)`, an 8-spec composition over 56 instructions.
    Defer further until slice 3 (`evm-asm-ahaz`) has assembled the
    program and pinned offsets.
  * Slice 5 (`evm-asm-w5mk`) full-loop composition: 256 iterations
    of a 58-instr body.  Loop invariant unchanged from the survey:
    `result_after_k_iterations = a^(top-k bits of b) mod 2^256`.

## 10. Acceptance for this slice

  * This document is checked in under `docs/`.
  * Slice 3 (`evm-asm-ahaz`) can read it and produce
    `evm_exp : Program` plus the marshalling helper Programs without
    further investigation.
  * No code changes; lake build is unaffected.
