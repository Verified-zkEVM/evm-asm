# #175 Slice 1 — Survey: Saturated 256-bit arithmetic in EvmAsm

Tracking GH issue [#175](https://github.com/Verified-zkEVM/evm-asm/issues/175)
("Unsaturated 256-bit arithmetic to reduce instruction count"). beads
`evm-asm-3bdk`, parent `evm-asm-0t2f`.

This is the slice-1 deliverable: a static inventory of the places where
EvmAsm currently emits **saturated** 64-bit-limb arithmetic with `SLTU`-based
carry / borrow chains. Saturated here means: every 64-bit limb of the
256-bit operand is allowed to take its full `[0, 2^64)` range, so the
hardware ADD/SUB result wraps mod 2^64 and a separate `SLTU` is needed to
recover the carry / borrow bit. The alternative being investigated under
\#175 is **unsaturated** representation, where each limb is kept strictly
below `2^64` (e.g. `< 2^63`), so a sum of two limbs cannot overflow and
no `SLTU` carry-recovery is needed inside the per-limb loop.

No code changes in this slice — inventory only. The numbers below are
direct counts from the current `main` (`SLTU` occurrences in
`EvmAsm/Evm64/**/Program.lean`).

## Scope decision: comparison-style SLTU is excluded

`SLTU` is overloaded in this codebase:

1. **Carry / borrow recovery** — `SLTU rd, sum, op` after an `ADD`, or
   `SLTU rd, minuend, subtrahend` before/after a `SUB`. This is the
   saturated-arithmetic pattern \#175 targets.
2. **Boolean comparison** — used as a primitive less-than / equal-to
   gadget (e.g. `LT`, `GT`, `SLT`, `SGT`, `ISZERO`, mask construction in
   `Shift`). These would not change under unsaturated arithmetic.

This survey only counts category 1. `Lt/Gt/Slt/Sgt/Eq/IsZero/Shift` use
`SLTU` exclusively as a comparison primitive and are out of scope, even
though `rg SLTU` finds matches there.

## Per-file inventory

| File | SLTU total | Of which carry/borrow | Saturated invariant maintained |
|---|---|---|---|
| `Evm64/Add/Program.lean` | 9 | 9 | Each limb of `(a + b) mod 2^256` is `mod 2^64`; carry `c_i ∈ {0,1}` is recovered by `SLTU sum, addend`. Limb 0 = 1 SLTU, limbs 1..3 = 2 SLTUs each + `OR` to merge two carry sources. |
| `Evm64/Sub/Program.lean` | 9 | 9 | Symmetric to Add: `SLTU minuend, subtrahend` recovers borrow. Limb 0 = 1 SLTU, limbs 1..3 = 2 SLTUs each + `OR`. |
| `Evm64/Multiply/Program.lean` | 6 | 6 | Schoolbook 4×4 column-wise accumulation. After each `ADD acc, partial`, `SLTU` recovers the column carry that is propagated to the next-higher result limb. |
| `Evm64/DivMod/Program.lean` | 17 | 17 | Two distinct sub-patterns: (a) **mulsub** at sp+8/+0/-8/-16/-24 of the trial-quotient kernel — each limb does `ADD prod_lo, carry; SLTU borrowAdd; ADD partial_carry, prod_hi; LD u; SLTU borrowSub; SUB uNew`. (b) **addback** correction loop — each limb does `ADD u, carryIn; SLTU c1; ADD u, v[i]; SLTU c2; OR carryOut, c1, c2`. |
| `Evm64/Shift/Program.lean` | 2 | 0 | Both `SLTU` instructions construct a Boolean mask (`bit_shift > 0`); neither is a saturated-arithmetic carry chain. Out of scope. |
| `Evm64/Lt,Gt,Slt,Sgt/Program.lean` | 5–7 each | 0 | Comparison primitives. Out of scope. |

**Total in-scope `SLTU` carry/borrow occurrences: 9 + 9 + 6 + 17 = 41.**

Each of these `SLTU` is paired with at least one `ADD` (or `SUB`), and
limbs 1..3 of `Add`/`Sub` and the addback inner loop also pay an extra
`OR` to merge two carry sources. So the cycle / instruction cost
attributable to saturated arithmetic is roughly:

| Routine | Saturated overhead per execution |
|---|---|
| `evm_add` (4 limbs)   | 9 SLTU + 3 OR + 3 redundant ADDs propagating carry  ≈ 15 of 29 instructions |
| `evm_sub` (4 limbs)   | 9 SLTU + 3 OR + 3 redundant SUBs propagating borrow ≈ 15 of 29 instructions |
| `evm_mul` (63 instr)  | 6 SLTU + 6 carry-propagating ADDs                   ≈ 12 of 63 instructions |
| `evm_div`/`evm_mod` mulsub | 5 SLTU per inner iteration (×~5 iter/digit, ×4 digits) — dominant inner-loop cost |
| `evm_div`/`evm_mod` addback | 8 SLTU+OR per addback limb (rarely taken in practice) |

## Saturated invariant

In every routine above the limb-level invariant is the trivial one:
`limb_i ∈ [0, 2^64)`, i.e. each cell stores any 64-bit pattern with no
high-bit slack. Operands loaded from the EVM stack inherit this
invariant directly from the caller; results spilled to memory preserve
it bit-for-bit because the underlying RV64 `ADD`/`SUB`/`MUL` already
return the low 64 bits of the mathematical result.

There is no *redundant* representation today: the limb-level value
function `(limb_0, limb_1, limb_2, limb_3) ↦ Σ limb_i · 2^(64·i)` is
injective on `[0, 2^256)`. An unsaturated representation would break
injectivity (multiple bit-patterns for the same 256-bit integer) and
require an explicit normalization step before SD / before equality
checks in the stack spec.

## Non-EVM uses

`Rv64/` itself does not implement saturated 256-bit arithmetic — it
defines the underlying instruction semantics. `EL/RLP` is byte-string
manipulation with no multi-limb arithmetic. So the inventory above is
exhaustive within `EvmAsm/`.

## Output for downstream slices

* **Slice 2 (design note, evm-asm-87oa):** decide a limb width
  (likely 63 bits with one slack bit, or 60 bits with four slack bits to
  absorb up to 16 schoolbook column terms before a normalization
  pass) and write the redundant-representation invariant.
* **Slice 3 (prototype, evm-asm-akvk):** build `evm_add_alt` parallel
  to `evm_add` using the chosen layout, **without** migrating
  callers, so cost & proof-effort can be compared head-to-head against
  the 9-SLTU baseline above.
* **Slice 4 (venue decision, evm-asm-j4o5):** with the prototype's
  numbers in hand, choose whether the result lives as a GH issue, a
  CLAUDE.md / TACTICS.md note, or a skill.

## References

* Bernstein, *fast-arith handout*, https://cryptojedi.org/peter/data/croatia-20150604.pdf
* `fiat-crypto/UnsaturatedSolinasHeuristics.v`
* Per-file program definitions cited above on `main`.

Authored by @pirapira; implemented by Hermes-bot (evm-hermes).
