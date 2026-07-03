# ADDMOD total runtime plan

> **Status (2026-07-03, issue #9704):** LANDED. The verified total program is
> `evm_addmod_total` (`EvmAsm/Evm64/AddMod/Program.lean`), functionally tested
> in `AddMod/ProgramTest.lean`, and the dispatcher handler
> (`EvmAsm/Codegen/Programs/EvmSelfCallingHandlers.lean`) now emits it inlined
> with `evm_mod_callable_v5` — replacing both the no-carry-only `evm_addmod`
> composition and the hand-written `.Laddmod_*` carry tail described below
> (which also carried a borrow-chain bug in its conditional subtract and
> called the buggy v4 callable). The block layout below documents the design
> rationale; the landed layout differs in two ways: the parking scratch lives
> below `x12` (at `F − 192/−224/−256`, under the callable's own
> `F − 160..F − 8` scratch band) instead of in `addmod_runtime_scratch`
> symbols, and all MOD calls share the single frame base `F = sp + 32`.
> Remaining work is the unconditional stack spec + `.proven` flip.

This note is the implementation handoff for total ADDMOD runtime work, tracked by
beads `evm-asm-fhsxz.2.4.2.60.2.4.*`.

## Spec contract

`execution-specs/src/ethereum/forks/cancun/vm/instructions/arithmetic.py`
implements ADDMOD as a total operation:

- pop `x`, `y`, `z`;
- charge `OPCODE_ADDMOD`;
- if `z == 0`, push `0`;
- otherwise push `U256((x + y) % z)`.

There is no invalid-op or unsupported branch for a 257-bit carry-out. A runtime
case such as `(2^256 - 1) + 1` with modulus `7` must return `2`, because
`2^256 % 7 = 2`.

## Existing verified/pure surface

The semantic target already exists in `EvmAsm/Evm64/EvmWordArith/AddMod.lean`:

- `EvmWord.addCarry` and `EvmWord.addCarry_spec` describe the carry bit plus
  truncated 256-bit sum.
- `EvmWord.addmod` and `EvmWord.addmod_correct` state the execution-specs
  semantics at full 257-bit precision.
- `EvmWord.addmod_eq_carry_split` rewrites nonzero-modulus ADDMOD to the
  carry-split shape emitted by the RISC-V prologue.
- `EvmWord.pow256ModN` and `EvmWord.pow256ModN_correct` provide the pure
  `2^256 mod N` value for the carry contribution.

The runtime/proof work should target these declarations, not introduce an
unsupported halt-kind model.

## Current runtime state after phase 1

`EvmAsm/Evm64/AddMod/Program.lean` currently has this prefix:

1. `evm_addmod_prologue = evm_add`, length 30 instructions / 120 bytes.
2. `evm_addmod_phase1_carry`, length 1 instruction / 4 bytes.

After those 31 instructions:

- `x12 = sp + 32`;
- `r = (a + b) mod 2^256` is in the stack cell at `x12 + 0..24`;
- `N` is in the stack cell at `x12 + 32..56`;
- `x7` is the carry bit `c` from `a.toNat + b.toNat`.

The current dispatcher composition in `EvmAsm/Codegen/Programs/Evm.lean` is the
no-carry-compatible path:

- byte 0: prologue starts;
- byte 120: `phase1_carry` starts;
- byte 124: `phase2_reduce 8` JAL site;
- byte 128: skip-JAL site;
- byte 132: `evm_mod_callable_v4` starts;
- byte 1504: handler tail starts after the callable.

The JAL at byte 124 uses offset `8` to reach the callable at byte 132. The
skip-JAL at byte 128 uses offset `1376`, which is 4 bytes for the skip-JAL plus
`evm_mod_callable_v4` length 1372 bytes.

That path is not total by itself: when `x7 = 1`, it reduces only the low
256-bit sum and silently drops the `2^256` contribution.

## Required total branch shape

The total runtime must branch on `N` and `x7` after phase 1:

1. `N = 0`: store zero as the ADDMOD result and finish with total stack advance
   of 64 bytes from the original top.
2. `N != 0` and `x7 = 0`: reuse the current low-sum reduction path, because
   `(a + b) = r` in this branch.
3. `N != 0` and `x7 = 1`: compute `(2^256 + r) % N`; never jump to
   `.exit_invalid_op`.

A concrete carry path should use only 256/256 helper calls:

1. Reduce the low part: `rMod := r mod N`, reusing `evm_mod_callable_v4`.
2. Compute the carry contribution `m := 2^256 mod N`. The runtime-friendly
   construction is `m = ((2^256 - 1) mod N + 1) mod N`, so the helper only has
   to materialize the all-ones 256-bit word, call `evm_mod_callable_v4`, and
   perform one modular add with the constant one.
3. Compute `result := (m + rMod) mod N` with the same modular-add helper.

Both modular additions have pre-reduced operands `< N`, so each can be a
carry-aware add plus at most one conditional subtract of `N`. This corresponds
to the existing pure `EvmWord.modAdd` helper.

## Helper blocks to add next

Add these blocks in `EvmAsm/Evm64/AddMod/Program.lean` unless splitting is
needed for file size:

- `evm_addmod_phase2_nonzero_test`: wire the existing `evm_addmod_phase2_n_zero_test`
  into the top-level layout instead of relying on callable zero behavior.
- `evm_addmod_phase2_reduce_low`: a named version of the current low-sum
  `evm_mod_callable_v4` call/marshal path, with byte-length lemmas.
- `evm_addmod_phase2_prepare_max_word`: materialize `2^256 - 1` in the dividend
  cell while preserving `N` and the saved `rMod` cell.
- `evm_addmod_phase2_pow256_mod_n`: compute `((2^256 - 1) mod N + 1) mod N`.
- `evm_addmod_phase2_mod_add`: shared pre-reduced modular-add block for
  `(lhs + rhs) mod N`, preserving the EVM stack contract and exposing carry for
  the proof.
- `evm_addmod_total`: assemble the zero, no-carry, and carry paths with concrete
  branch/call offsets and length lemmas.

Dispatcher wiring in `EvmAsm/Codegen/Programs/Evm.lean` should then replace the
current `evmAddmodComposed` body with `evm_addmod_total` plus any inlined
callable blocks it requires. Runtime tests must include:

- `N = 0` returns zero;
- no-carry nonzero modulus still matches current cases;
- `(2^256 - 1) + 1 mod 7 = 2` succeeds with normal halt kind;
- at least one wide nonzero modulus carry case.

## Proof direction

The total stack proof should use:

- `EvmWord.addmod_correct` for the external semantic statement;
- `EvmWord.addmod_eq_carry_split` after the prologue/phase1 proof exposes `x7`
  and `r`;
- `EvmWord.pow256ModN_correct` for the carry-contribution helper;
- `EvmWord.modAdd_correct` for the two pre-reduced modular additions.

Keep branch postconditions folded before applying broad frame permutation tactics.
The proof must cover all three runtime branches above; no branch should model a
valid ADDMOD input as invalid or unsupported.
