# #175 Slice 1 — Saturated 256-bit arithmetic inventory

Inventory of EvmAsm modules that emit **saturated** 64-bit limb arithmetic
(each 256-bit EVM word is stored as four full 64-bit limbs, with explicit
carry/borrow chains via `SLTU`). This is the baseline an unsaturated
representation would aim to undercut (per @alexanderlhicks's suggestion in
GH #175 — see Bernstein/Schwabe Croatia 2015 talk and `fiat-crypto`'s
`UnsaturatedSolinasHeuristics`).

The "saturated invariant" preserved by every routine below is simply
`limb_i : BitVec 64` with no extra slack bits — every wraparound is detected
by an `SLTU` against an operand and propagated as a 0/1 carry to the next
limb. Switching to unsaturated would relax the per-limb width (e.g. 51-bit
limbs in 64-bit storage) so individual ADDs can accumulate without carry
emission for a bounded number of operations, deferring the carry-chain to a
single "freeze" at the end.

This document is informational; no Lean changes. Slice 2 (#175) will
propose the limb width and reduction discipline; slice 3 will prototype
`evm_add_alt` parallel to `evm_add` for a measurable comparison.

## Scope

`SLTU`-based carry/borrow chains and `MUL`/`MULHU` schoolbook column
accumulators are the load-bearing pattern. Bitwise opcodes (AND/OR/XOR/NOT)
and pure logical/byte routines have no carry chain and are not in scope.
`Lt`/`Gt`/`Slt`/`Sgt` use `SLTU` for limb compare not for carry — listed
for completeness because an unsaturated encoding would also redesign
comparison.

## Per-file inventory

| File | LOC | Pattern | SLTU sites | MUL/MULHU | Per-limb instr count |
| --- | ---:| --- | ---:| ---:| --- |
| EvmAsm/Evm64/Add/Program.lean | 40 | 4-limb add, carry chain | 7 (1 limb0, 2×3 limbs1-3) | 0 | 5 / 8 / 8 / 8 + 1 sp |
| EvmAsm/Evm64/Sub/Program.lean | 39 | 4-limb sub, borrow chain | 7 (1 limb0, 2×3 limbs1-3) | 0 | 5 / 8 / 8 / 8 + 1 sp |
| EvmAsm/Evm64/Multiply/Program.lean | 306 | 4×4 schoolbook, column-wise carry | 13 carry SLTUs across cols | 16 (8 MUL + 8 MULHU) | col0=21, col1=23, col2=13, col3=5, +1 sp = 63 instrs |
| EvmAsm/Evm64/Shift/Program.lean | 850 | SHL/SHR/SAR by byte+bit | 1 (mask predicate, not a carry) | 0 | n/a (variable) |
| EvmAsm/Evm64/DivMod/Program.lean | 808 | Knuth Algorithm D, full pipeline | ~15 carry/borrow sites | reuses MulSub + AddBack helpers | n/a (multi-phase) |
| EvmAsm/Evm64/DivMod/LimbSpec/AddBack.lean | — | inner add-back: u' = u + v with carry | partA: SLTU carry1 (5 instrs LD/LD/ADD/SLTU/ADD); partB: SLTU carry2 + OR + SD (3 instrs) | 0 | 5 + 3 per limb |
| EvmAsm/Evm64/DivMod/LimbSpec/MulSub.lean | — | inner mul-sub: u -= q*v with carry/borrow | partA: ADD + SLTU carry; partB: LD u + SLTU borrow + SUB + ADD + SD | partA: 1 MUL + 1 MULHU per limb | 6 + 5 per limb |
| EvmAsm/Evm64/DivMod/LimbSpec/SubCarryStoreQj.lean | — | tail subtract + store quotient limb | 1 (SLTU borrow) | 0 | 4 |
| EvmAsm/Evm64/Compare/LimbSpec.lean | 159 | LT/GT/SLT/SGT limb building blocks | 5 (LT base + LT carry: SLTU, SLTU, SLTU, OR; reused by GT) | 0 | base=3, carry=6 |
| EvmAsm/Evm64/Lt/Program.lean | 37 | 4-limb LT via Compare.LimbSpec | 7 (1 base + 3×2) | 0 | n/a |
| EvmAsm/Evm64/Gt/Program.lean | 36 | 4-limb GT (operand-swapped LT) | 7 | 0 | n/a |
| EvmAsm/Evm64/Slt/Program.lean | 39 | signed LT: sign-flip then unsigned LT | 5 | 0 | n/a |
| EvmAsm/Evm64/Sgt/Program.lean | 38 | signed GT | 5 | 0 | n/a |
| EvmAsm/Evm64/EvmWordArith/MultiLimb.lean | — | pure-Word multi-limb arithmetic helpers | 1 (proof-side reference, no emit) | 0 | n/a |
| EvmAsm/Evm64/EvmWordArith/DivMulSubLimb.lean | — | pure-Word reasoning lemmas | 3 (proof-side) | 0 | n/a |

(Counts taken from `search_files SLTU|MULHU` against `EvmAsm/Evm64/`; the
inner `DivMod/LimbSpec/*.lean` files are component specs whose code-region
constraints emit the SLTUs — they don't define `Program` values directly.)

## Where unsaturated arithmetic would help

Highest-payoff candidates (instruction count savings × frequency on the
critical path toward `run_stateless_guest`):

1. **Multiply / DivMod inner loops** — 4×4 schoolbook column accumulation
   currently spends 1–2 SLTUs per cross-limb addition. With a 51-bit
   unsaturated representation you can accumulate ~16 cross products into a
   64-bit limb before requiring a freeze. Net effect: drop most of the
   13 column-walk SLTUs in `Multiply/Program.lean` and the 5×N inner SLTUs
   in `DivMod/LimbSpec/MulSub.lean` and `AddBack.lean`. This is the single
   biggest win and also the area with the deepest existing proofs (so
   migration cost is highest).

2. **ADD / SUB** — saves 6 SLTUs each (one chain). Modest absolute saving
   per call but ADD/SUB run every block, so it compounds. ADD/SUB are also
   the simplest to migrate as a parallel `evm_add_alt` proof-of-concept
   (slice 3 in the parent plan).

3. **DivMod tail** — `SubCarryStoreQj` and the addback Part B's SLTU+OR
   "carryOut" pattern. Smaller but inside a hot loop.

Comparison opcodes (LT/GT/SLT/SGT) are NOT a good target: they need a
true full-width comparison and an unsaturated encoding doesn't reduce
operation count there (you'd still need to freeze before comparing).

## Proposed slice-2 inputs

For the design note (slice 2, evm-asm-87oa), the key questions to answer
are:

- **Limb width**: 51 bits (Curve25519-style, max 13-deep accumulation
  before freeze) vs 56 bits (max 256-deep, fewer freezes but tighter
  bounds), vs other.
- **Storage**: keep 4×64-bit memory layout (slack bits zeroed) so the
  EVM-stack `evmWordIs` boundary is unchanged, OR widen to 5×64-bit so
  a 256-bit value fits with carry-room baked in.
- **Boundary discipline**: where do `freeze` (canonicalize to saturated)
  calls land? Most likely at every `evmWordIs` enter/exit so caller code
  sees no change.
- **Proof migration shape**: parallel `_alt` programs/specs (no migration)
  vs swap underneath the existing `evm_add` (forces all proofs to update
  at once). Slice 3 picks the parallel route.

Authored by @pirapira; implemented by Hermes-bot (evm-hermes).
