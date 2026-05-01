# DIV/MOD stack-level spec inventory (issue #61, slice evm-asm-6e2o)

Audit produced by Hermes-bot (evm-hermes) for slice 1 of the
`evmWordIs`-level stack-spec parent (beads `evm-asm-pb40`, GH #61).
No code change. The goal is to make the inventory of all per-path
`evm_{div,mod}_*_stack_spec[_within]` entry points explicit and to
sketch the unified surface that slices 3 (DIV) and 4 (MOD) will
introduce.

This document is an audit, not a roadmap. It states what exists today
and what shape the unified theorems should take; the actual unified
definitions and their case-split proofs are the job of slices 3 / 4.

## 1. Per-path entry points

The dimensions of the existing API are:

* opcode  = `div` | `mod`
* `n` tier (clz-derived limb count of normalised divisor):
  `n=1`, `n=2`, `n=3`, `n=4`
* branch / dispatcher path:
  * `bzero`         — divisor is zero, skips the loop entirely
  * `max_skip`      — non-call, skip path of the loop body
  * `max_addback_beq` — non-call, add-back-after-BEQ path (vacuous when shift ≠ 0)
  * `call_skip`     — call path, skip
  * `call_addback_beq` — call path, add-back-after-BEQ
  * `call`          — combined call (rcases internally on skip vs add-back)
  * `shift0_call_skip` / `shift0_call_addback_beq` / `shift0` — shift = 0 call dispatcher
* surface = full `cpsTriple` or `cpsTripleWithin` (the latter passes through
  the "within `divCode base`" frame)

The full table below lists every theorem that already mentions
`stack_spec` in `EvmAsm/Evm64/DivMod/`.

| theorem | file:line | n | path | within? |
|---|---|---|---|---|
| `evm_div_bzero_stack_spec_within`                         | `Spec/Base.lean:904`         | (any) | bzero            | yes |
| `evm_mod_bzero_stack_spec_within`                         | `Spec/Base.lean:961`         | (any) | bzero            | yes |
| `evm_div_n1_stack_spec_within`                            | `Spec/Dispatcher.lean:299`   | 1     | full unified     | yes |
| `evm_div_n1_stack_spec_within_word`                       | `Spec/Dispatcher.lean:466`   | 1     | full unified, EvmWord-level | yes |
| `evm_mod_n1_stack_spec_within`                            | `Spec/Dispatcher.lean:753`   | 1     | full unified     | yes |
| `evm_mod_n1_stack_spec_within_word`                       | `Spec/Dispatcher.lean:823`   | 1     | full unified, EvmWord-level | yes |
| `evm_div_n4_max_skip_stack_spec`                          | `Spec/Base.lean:1229`        | 4     | max_skip         | no  |
| `evm_mod_n4_max_skip_stack_spec_within`                   | `Spec/Base.lean:1291`        | 4     | max_skip         | yes |
| `evm_div_n4_max_addback_beq_stack_spec_within`            | `Spec/Base.lean:1383`        | 4     | max_addback_beq (vacuous) | yes |
| `evm_mod_n4_max_addback_beq_stack_spec_within`            | `Spec/Base.lean:1399`        | 4     | max_addback_beq (vacuous) | yes |
| `evm_div_n4_call_skip_stack_spec`                         | `Spec/CallSkip.lean:1060`    | 4     | call_skip        | no  |
| `evm_mod_n4_call_skip_stack_spec_within`                  | `Spec/CallSkip.lean:1204`    | 4     | call_skip        | yes |
| `evm_div_n4_call_skip_stack_spec_unconditional`           | `Spec/CallSkip.lean:1312`    | 4     | call_skip (no-`hsem`)  | no  |
| `evm_mod_n4_call_skip_stack_spec_unconditional_within`    | `Spec/CallSkip.lean:1335`    | 4     | call_skip (no-`hsem`) | yes |
| `evm_div_n4_call_addback_beq_stack_spec`                  | `Spec/CallAddback.lean:2734` | 4     | call_addback_beq | no  |
| `evm_mod_n4_call_addback_beq_stack_spec_within`           | `Spec/CallAddbackMod.lean:318` | 4   | call_addback_beq | yes |
| `evm_div_n4_call_stack_spec`                              | `Spec/CallAddbackMod.lean:391` | 4   | call (combined)  | no  |
| `evm_mod_n4_call_stack_spec_within`                       | `Spec/CallAddbackMod.lean:427` | 4   | call (combined)  | yes |
| `evm_div_n4_shift0_stack_spec`                            | `Shift0Dispatcher.lean:46`   | 4 (shift=0) | shift0 (combined) | no |
| `evm_mod_n4_shift0_stack_spec`                            | `Shift0Dispatcher.lean:81`   | 4 (shift=0) | shift0 (combined) | no |
| `evm_div_n4_shift0_call_skip_stack_spec`                  | `SpecCallShift0.lean:164`    | 4 (shift=0) | shift0_call_skip | no |
| `evm_mod_n4_shift0_call_skip_stack_spec`                  | `SpecCallShift0.lean:295`    | 4 (shift=0) | shift0_call_skip | no |
| `evm_div_n4_shift0_call_addback_beq_stack_spec`           | `SpecCallShift0.lean:513`    | 4 (shift=0) | shift0_call_addback_beq | no |
| `evm_mod_n4_shift0_call_addback_beq_stack_spec`           | `Shift0AddbackMod.lean:465`  | 4 (shift=0) | shift0_call_addback_beq | no |

## 2. Pre / post surfaces in use

The five pre / post pairs that occur:

| pre | post | scratch model | uses | defined |
|---|---|---|---|---|
| `divModStackDispatchPre` | `divStackDispatchPost`   | call-scratch (`divScratchValuesCall` → `divScratchOwnCall`) | `evm_div_n1_stack_spec_within[_word]` | `Spec/Dispatcher.lean:22, 51` |
| `divModStackDispatchPre` | `modStackDispatchPost`   | call-scratch                                                  | `evm_mod_n1_stack_spec_within[_word]` | `Spec/Dispatcher.lean:22, 96` |
| `divN4StackPre`          | `divN4MaxSkipStackPost` | non-call scratch (no `retMem/dMem/dloMem/scratch_un0`)        | `evm_div_n4_max_*`                  | `Spec/Base.lean:232, 215` |
| `divN4StackPre`          | `modN4MaxSkipStackPost`| non-call scratch                                              | `evm_mod_n4_max_*`                  | `Spec/Base.lean:232, 532` |
| `divN4StackPreCall`      | `divN4CallSkipStackPost`| call-scratch                                                  | every `*_n4_call_*` and `*_n4_shift0*` | `Spec/Base.lean:316`, `Spec/CallSkip.lean:97` |
| `divN4StackPreCall`      | `modN4CallSkipStackPost`| call-scratch                                                  | every `*_n4_call_*` (mod)           | `Spec/Base.lean:316`, `Spec/CallSkip.lean:130` |
| ad-hoc small pre / post  | (inline)                | only `(.x12, .x5, .x10, .x0)` plus `evmWordIs (sp+32) b`      | `evm_{div,mod}_bzero_stack_spec_within` | `Spec/Base.lean:904, 961` |

The dispatcher-level pair (row 1/2) is the most general:
`divModStackDispatchPre` already exposes `(.x1, .x2, .x5, .x6, .x7, .x10, .x11, .x12, .x0)`,
the operand `evmWordIs sp a` and `evmWordIs (sp+32) b`, and the full
`divScratchValuesCall` block. Its post owns those scratch cells back via
`divScratchOwnCall` and rewrites `(sp+32)` to `EvmWord.{div,mod} a b`.
That is the surface a unified `evm_div_stack_spec` should consume and
return.

The `divN4StackPre` / `divN4StackPreCall` pair is identical except:

* `divN4StackPre` omits the call-only scratch cells
  (`retMem, dMem, dloMem, scratch_un0`); `divN4StackPreCall` includes them.
* The non-call post (`divN4MaxSkipStackPost`) owns only the non-call scratch.

So `divModStackDispatchPre` *is* `divN4StackPreCall` modulo packaging
(both use `divScratchValuesCall`); the n=1 dispatcher already chose the
call-scratch surface as the canonical one.

The bzero pair is genuinely smaller — it does not assume any of the
loop scratch cells. To plug into the unified post we need to weaken it
the same way `divModStackDispatchPre_unfold` does for n=1: the bzero
caller already knows the loop scratch is owned but unused, so the
unified theorem has to thread that ownership through (assertion
weakening, no semantic content).

## 3. Dispatcher gaps

The four `n=k` clz tiers are realised in EVM dispatcher code, but only
`n=1` has a `*_stack_spec_within` entry point at the dispatcher
surface (`divModStackDispatchPre → divStackDispatchPost`). The work in
`Spec/Base.lean` and friends for `n=4` exposes only the per-path
versions (max-skip, call-skip, call-addback-beq, shift0); there is no
`evm_div_n4_stack_spec_within` that internally case-splits on the call
flag and the borrow / addback-beq branch flags.

Slice 2 (`evm-asm-wp69`) explicitly tracks wiring the missing
`n=2` and `n=3` `*_stack_spec_within` entry points in
`Spec/Dispatcher.lean`. That work mirrors `evm_div_n1_stack_spec_within`:
each `n=k` should consume `divModStackDispatchPre` and yield the same
`divStackDispatchPost`, internally invoking the existing per-trial-row
(`fullDivNk*` / `fullModNk*`) full unified specs that already exist for
`n=1`.

## 4. Sketch of the unified theorem (slice 3 / 4)

The target shape, to be defined in `EvmAsm/Evm64/DivMod/Spec/Unified.lean`:

```lean
theorem evm_div_stack_spec
    (sp base : Word) (a b : EvmWord)
    (v1 v2 v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratch_un0 : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12))
              &&& ~~~(1 : Word) = base + div128CallRetOff) :
    cpsTripleWithin (divCodeMaxSteps base) base (base + nopOff) (divCode base)
      (divModStackDispatchPre sp a b v1 v2 v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (divStackDispatchPost sp a b)
```

and the analogous `evm_mod_stack_spec` with `modStackDispatchPost`.

The proof is a four-way case split:

1. `b = 0`  ⇒  `evm_div_bzero_stack_spec_within` after weakening the
   call-scratch cells (they are unused but owned in the post via
   `divScratchOwnCall`).
2. `b ≠ 0`, `n = 1` (i.e. `b.getLimbN 1 = b.getLimbN 2 = b.getLimbN 3 = 0`)
   ⇒  `evm_div_n1_stack_spec_within`.
3. `b ≠ 0`, `n = 2` / `n = 3`  ⇒  `evm_div_n{2,3}_stack_spec_within`
   (slice 2 prerequisite).
4. `b ≠ 0`, `n = 4` (`b.getLimbN 3 ≠ 0`)
   * `(clzResult b3).1 = 0`  ⇒  `evm_div_n4_shift0_stack_spec`
   * `(clzResult b3).1 ≠ 0`  ⇒  `evm_div_n4_call_stack_spec`
     (which already internally case-splits on skip vs add-back-beq).

The step bound can be the worst-case `cpsTripleWithin_mono_nSteps`
ceiling of all branches (each per-path spec already gives a concrete
count; the unified theorem just takes the max).

The MOD theorem is mechanically identical with `mod` substituted
throughout and `EvmWord.mod a b` replacing `EvmWord.div a b` in the
post.

## 5. Open questions deferred to slices 2 / 3 / 4

* Whether `evm_div_stack_spec` should expose `cpsTriple` or
  `cpsTripleWithin`. The existing dispatcher / shift0 entries are
  asymmetric (some `*_within`, some not). The unified surface should be
  `cpsTripleWithin` so it composes with outer dispatchers; non-`within`
  variants can be derived via `cpsTripleWithin_to_cpsTriple` if needed.
* Whether the unified theorem should bundle the `halign` hypothesis as
  a once-per-`base` lemma (it is identical across all call paths).
* Whether `evm_div_n4_call_stack_spec_unconditional` (no `hsem` /
  `hborrow` bundles) is the right combinator for slice 3 to invoke — it
  may simplify the n=4 case to "no manual flag splits, just the clz
  tier".

These are intentionally not resolved in this slice. The unified
theorem statement above and the four-way case split are the contract
for slices 3 / 4.

Authored by @pirapira; implemented by Hermes-bot (evm-hermes).
