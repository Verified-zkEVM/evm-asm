# PUSH1..PUSH32 design note (GH #101)

This is the survey deliverable for `evm-asm-ftjv` (slice 1 of #101). It
extracts the parameterized-opcode pattern used by `Dup.lean` /
`Swap.lean` so subsequent slices (#101 slices 2-6) can land on a fixed
substrate. No code changes — purely a design contract.

## File layout

Mirror the existing parameterized-opcode subtrees:

```
EvmAsm/Evm64/Push/Program.lean   -- evm_push (n : Nat) + evm_push_code
EvmAsm/Evm64/Push/Spec.lean      -- spec hierarchy, top = evm_push_n_stack_spec
EvmAsm/Evm64/Push.lean           -- one-liner: import EvmAsm.Evm64.Push.Spec
EvmAsm/Evm64.lean                -- add: import EvmAsm.Evm64.Push (next to Dup/Swap)
```

Reference shapes:

- `EvmAsm/Evm64/Dup/Program.lean` (39 LoC)
- `EvmAsm/Evm64/Dup/Spec.lean` (178 LoC, three-level hierarchy)
- `EvmAsm/Evm64/Swap/Program.lean` (51 LoC)
- `EvmAsm/Evm64/Swap/Spec.lean` (198 LoC)
- `EvmAsm/Evm64/Push0/Program.lean` (the n=0 special case — uses
  `CodeReq.ofProg` because there is no symbolic `n`)

## Parameter handling

`n` is a *meta-level* `Nat`, not a runtime register. Plumb it through
`Program` via a `private` per-limb helper plus a top-level `def`:

```
private def push_one_byte (n i : Nat) : Program := ...
def evm_push (n : Nat) : Program := ... helpers indexed 0..n-1 ...
```

Side conditions on `n` (`1 ≤ n`, `n ≤ 32`) are theorem hypotheses
(`hn1 hn32 : ...`), exactly matching `evm_dup_spec_within`'s `hn1 hn16`
and `evm_swap_spec_within`'s analogous bounds.

## CodeReq construction

Because `n` is symbolic, `CodeReq.ofProg base (evm_push n)` does NOT
reduce. Use the explicit `CodeReq.singleton` union chain pattern from
`evm_dup_code` / `evm_swap_code`:

```
abbrev evm_push_code (base : Word) (n : Nat) : CodeReq :=
  CodeReq.singleton base (.ADDI .x12 .x12 (-32))
  |>.union (CodeReq.singleton (base + 4)  ...)
  |>.union ...
```

`Push0` is the only exception — it uses `CodeReq.ofProg` because `n` is
fixed at 0.

## Spec hierarchy (three levels — same as Dup)

1. **Per-byte / per-limb helper** (`push_one_byte_spec_within` or
   similar): closes one `LBU` + bookkeeping pair via `runBlock`, mirrors
   `dup_pair_spec_within` (LD+SD pair).
2. **Low-level generic spec** (`evm_push_spec_within`): operates on
   raw 64-bit memory cells (`↦ₘ`), parameterized by `n` and the four
   limb values, composed via `runBlock`. Mirrors `evm_dup_spec_within`.
   Body is roughly: prove four `signExtend12`-normalization `have`s for
   the symbolic offsets, instantiate the per-byte helpers, `runBlock`.
3. **EvmWord-level spec** (`evm_push_evmword_spec_within`): wraps the
   `↦ₘ` quad into an `evmWordIs` via `cpsTripleWithin_weaken` +
   `xperm_hyp` (see lines 105-133 of `Dup/Spec.lean`).
4. **Stack-level spec** (`evm_push_n_stack_spec` — the acceptance
   target): frames the EvmWord spec against `evmStackIs` using
   `cpsTripleWithin_frameR`, in the style of `evm_dup_stack_spec_within`
   (lines 142-175 of `Dup/Spec.lean`). For PUSH the postcondition
   prepends rather than substitutes, so the framing setup differs
   slightly (no `evmStackIs_split_at` is needed — just append the new
   `evmWordIs` at offset `nsp` to the existing stack).

## PC advance

There is no separate "PC advance" obligation in the
`cpsTripleWithin n base end ...` framework — the second/third arguments
are start-pc and end-pc. For `evm_push` with k RISC-V instructions, use
`cpsTripleWithin k base (base + 4*k) (evm_push_code base n) ...` exactly
as `evm_dup_spec_within` writes `cpsTripleWithin 9 base (base + 36) ...`.

The EVM-level "PC advances by 1+n" claim lives in the spec's
postcondition register state — `evm_pc` (or whatever register the
project elects) is shown to equal `evm_pc + (1+n)` in the post. This
will be discharged in slice 4 when the parameterized spec is finalized.

## Reading code bytes

PUSH reads the n immediate bytes that live in the EVM code region (not
the EVM stack memory). Use `LBU` against the code region with the
`extractByte_packBytes` / `extractByte_codeRegion_at` lemmas already
exported from `EvmAsm/Evm64/CodeRegion.lean`. The `evmCodeIs base bytes`
assertion frames the code region; `pcFree_evmCodeIs` lets it ride along
during the run.

For the zero-extend-to-256-bit big-endian semantics:
- The n bytes occupy the low n bytes of the resulting `EvmWord`,
  big-endian (byte 0 = highest-order of the n).
- Bytes beyond position n are zero. For 1 ≤ n ≤ 32 this means the
  `EvmWord`'s `getLimbN i` is constructible from the input byte list by
  `packDword`-style packing (use `EvmWord.fromLimbs`).

## Pitfalls picked up from Dup/Swap

- `signExtend12_ofNat_small` requires `omega` proofs; for `n ∈ [1,32]`
  the offsets `n*32 + i*8 + j` stay below 2^11 so the same lemma works.
- The `symbolic-n prevents ofProg reduction` comment on `evm_dup_code`
  applies verbatim. Don't try `simp [CodeReq.ofProg]` — write the union
  chain.
- New file must be wired into `EvmAsm/Evm64.lean` (issue #1209/#1440 CI
  enforces transitive reachability from `EvmAsm.lean`).
- Naming: camelCase for value identifiers, snake_case for `h_*`
  hypotheses (per AGENTS.md "Critical Rules" / Mathlib alignment).
- Keep `set_option maxHeartbeats` out of these files — `Swap/Spec.lean`
  has one bump (`800000`) which is the project ceiling for a non-Shift
  composition file; PUSH should not need any.

## Slice mapping

The remaining child tasks of `evm-asm-f0f5` line up as:

- slice 2 (`evm-asm-fj5w`): `Evm64/Push/Program.lean` + `evm_push_code`.
- slice 3 (`evm-asm-ou3t`): concrete PUSH1 spec — degenerate n=1 case,
  no zero-fill loop, sanity `native_decide` test.
- slice 4 (`evm-asm-o8w3`): parameterized `evm_push_n_stack_spec` for
  n ∈ [1, 32]. The bulk of the proof work; uses the three-level
  hierarchy above.
- slice 5 (`evm-asm-8nt5`): `native_decide` instantiation tests for
  PUSH2 and PUSH32.
- slice 6 (`evm-asm-7uc7`): wire `EvmAsm.Evm64.Push` into the umbrella,
  close GH #101.

Authored by @pirapira; implemented by Hermes-bot (evm-hermes).
