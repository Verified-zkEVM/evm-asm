# DIV-Perf Phase 3 Bootstrap — Algorithm Redesign Under Real Weights

> **What this file is.** A self-contained kickoff for Phase 3 of the DIV opcode
> performance effort. Open a *fresh* session, read **only** this file, and you
> have everything needed to do Phase 3 without re-deriving context.
>
> **Per-phase workflow.** Each phase gets (1) its own branch off the **latest**
> `origin/main`, (2) its own clean session, (3) a bootstrap file like this.
> Start with `git fetch origin && git checkout -b perf/div-algorithm-redesign origin/main`.
> **Carry forward the Phase 2 deliverables** — they are committed on
> `perf/div-evm-workload-data` (merge/cherry-pick or rebase onto it): the weights
> file `bench/div-weights.json`, the raw data `bench/div-operands-mainnet.jsonl.gz`,
> and `docs/divmod-evm-workload.md`. The Phase 1 harness `bench/DivBench.lean`
> lives on `perf/div-divisor-fast-paths` (Phase 1 branch, draft PR).
> **Bootstrap files are LOCAL / UNCOMMITTED.** Phase 3 *deliverables* (new
> `Program`s, proofs, benchmark numbers, updated docs) commit as normal; push is
> gated by a Lean guardrail — hand the push command to the user to run manually.
>
> **Your last task this session is to generate the Phase 4 bootstrap** (if the
> work spills past one session): `docs/agents/div-perf-phase4-*.md`, local.

---

## 0. The big picture (why this effort exists)

We optimize the verified 256-bit EVM **DIV** opcode (`evm_div` in
`EvmAsm/Evm64/DivMod/Program.lean`), a RISC-V macro-assembly subroutine
**formally verified** against `EvmWord.div` (`EvmAsm/Evm64/EvmWordArith/Div.lean`:
`div a b = if b=0 then 0 else BitVec.udiv a b`). Motivation: a gas-repricing
question from @pirapira (Yoichi) — DIV is flat `LOW`=5 gas regardless of operand
size, but its real RISC-V/zkVM proving cost varies ~3.4× with divisor size.

### The zkVM cost model (ground truth — DO NOT re-litigate)
From Gassmann, Chaliasos, Sotiropoulos, Su, *"Evaluating Compiler Optimization
Impacts on zkVM Performance"* (arXiv:2508.17518v2; RISC0 + SP1):
- **Dynamic instruction (cycle) count is the PRIMARY, near-linear proving-cost
  driver** (Pearson > 0.9). Minimizing executed instructions is the objective.
- **Per-instruction cost is ~uniform; "division is not expensive"** (MUL = ADD,
  DIVU = 1 row). Knuth-D's normalization / trial-quotient / add-back machinery is
  largely an artifact of "divides are expensive" hardware instinct and is a
  candidate to **delete** in favor of divide-heavy methods.
- **Branches are cheap (no misprediction) but speculation is wasteful** →
  compute exactly ONE path per input; never branchless-select among candidates.
- **Paging is a 2nd axis** (page-in/out ≈ 1130 cycles) but Phase 1 showed it does
  not discriminate for a single DIV (working set is a constant 28 dwords / 2
  pages — purely an algorithmic artifact of phaseB zeroing all scratch).

### Phase 1 — DONE (branch `perf/div-divisor-fast-paths`, draft PR)
`bench/DivBench.lean`: a two-axis cost harness running the **verified** `step`
semantics (`EvmAsm/Rv64/Execution.lean`) on concrete inputs, reporting `steps`
(instructions — primary), `loads/stores/memOps`, `dwords` (working set), `pages`,
and `correct` (vs `a/b`). Baseline (current `evm_div`, all correct):

| divisor | n | steps | memOps | dwords | pages |
|---|---|---|---|---|---|
| b=2 / b=7 (small) | 1 | 689 / 688 | 201 | 28 | 2 |
| b≈2⁶⁴ (bench #2) | 2 | 628 | 193 | 28 | 2 |
| b=2⁶⁴−1 | 1 | 623 | 179 | 28 | 2 |
| b≈2¹²⁸ (bench #1) | 3 | 449 | 143 | 28 | 2 |
| b full 256-bit | 4 | 204 | 71 | 28 | 2 |

**Key Phase-1 findings:** (a) the cost curve is **inverted** — small divisors
cost the *most* (the loop runs `5−n` iterations); (b) memOps ≈ 29 % of steps
across all classes → the two cost axes are correlated, so instruction count is a
faithful single objective; (c) working set is a constant 28 dwords / 2 pages for
every divisor → paging does not discriminate; the only memory lever is
**algorithmic** (a register-resident method would cut working set to ~4–8 dwords).

Run it:
```
lake build EvmAsm.Evm64.DivMod.Program EvmAsm.Rv64.Execution EvmAsm.Evm64.Basic
lake env lean bench/DivBench.lean
```

### Phase 2 — DONE (branch `perf/div-evm-workload-data`)
Replaced the reasoned divisor distribution with **real mainnet data**: 145,888
division ops from 32 distinct mainnet blocks (~27 days, June 2026), traced
opcode-level and **frequency-weighted over the sample** (not a uniform random
sample — only 32 blocks, see the caveats below). See `docs/divmod-evm-workload.md`;
weights in `bench/div-weights.json` (`divmod` block, use `partition`); raw in
`bench/div-operands-mainnet.jsonl.gz`. **The four findings that drive Phase 3:**

1. **DIV is 91.7 %** of all division ops (MOD 3.3 %, SDIV 4.0 %, SMOD 1.0 %).
2. **Small divisors dominate:** unsigned n=1 (<2⁶⁴) = **49 %**, n=2 = 21 %.
   These are *also* the most expensive in today's impl (inverted curve) → double
   justification to optimize them.
3. **54 % of all divides are "cheap"** (95 % CI [48 %, 61 %]): `a<b`→ early-out
   (q=0,r=a) (**23 %**), divisor power-of-two →shift (**46 %**, but 85 % of that is
   `2^(8k)` byte-extraction — vintage-sensitive, see §1 caveats), or `b=0` (0.2 %).
4. **The benchmark's worst case is rare:** 89 % of real n=3 divisors and 97 % of
   n=4 are powers of two; **genuine non-cheap divides needing n≥3 are only 1.8 %
   of all divides (n=3 alone: 1.6 %)**, and **96 % of all genuine divides are
   n≤2** (91 % of genuine *multi-word* (n≥2) divides are n=2).

**Genuine (non-cheap) work, as a share of all divides** — the dispatch to optimize:
| n=1 single-word | n=2 double-word | n≥3 Knuth-D tail |
|--:|--:|--:|
| 26.0 % | 18.2 % | **1.8 %** |

---

## 1. Phase 3 goal

Re-derive the DIV algorithm under the **corrected objective**: minimize
**frequency-weighted dynamic instruction count** (weights from Phase 2), keep
operands **register-resident** (kill scratch spills), lean on cheap `DIVU`,
compute **exactly one path per input**.

The optimization target the harness should compute:
```
cost = Σ_class  weight[class] · steps(candidate, class)        (weights: bench/div-weights.json)
```
where the dispatch classes are the **non-overlapping partition** in
`bench/div-weights.json` → `divmod.partition` (sums to 1.000):

| class | weight | path |
|---|--:|---|
| `b == 0` | 0.002 | return 0 |
| `a < b` (precedence first) | 0.228 | q=0, r=a — early-out |
| `pow2(b)`, a≥b, not a<b | 0.311 | `q = a >> ctz(b)`, `r = a & (b-1)` — shift/mask |
| genuine n=1 | 0.260 | register-resident single-word |
| genuine n=2 | 0.182 | double-word specialized |
| genuine n=3 | 0.016 | existing Knuth-D tail (correctness only) |
| genuine n=4 | 0.002 | existing Knuth-D tail |

> ⚠️ Weight against `divmod.partition` (above). **Do NOT** add `a_lt_b_frac`
> (0.228) + `pow2_frac` (0.460): they overlap ~15 pp (byte-extraction with zero
> high bytes is both) and sum past 1. `cheap_frac` = 0.54 is the a<b+pow2+b0 union.
>
> ⚠️ **Two caveats on the cheap/pow2 win before you over-invest in it** (from the
> Phase-2 adversarial review): (1) **85 % of the pow2 class is `2^(8k)`
> byte/word-extraction** (`2^224`, `2^160`), not Q96/Q128 fixed-point — real DIV
> opcodes a shift path helps, but contract-vintage-sensitive (modern Solidity
> emits SHR), so treat 46 % as an upper bound. (2) The 54 % cheap figure has a
> block-bootstrap **95 % CI of [48 %, 61 %]** (only 32 blocks, high per-block
> variance), and the heaviest ~3–8 % of txs were dropped to trace timeouts with
> **unmeasured** divisor mix — the bias direction is unproven. Genuine n=1/n=2
> (0.26 / 0.18) are the most defensible, vintage-independent targets.

### Candidate designs to evaluate with `bench/DivBench.lean`
Prototype each as an *unverified* `Program`, rank by the weighted harness, pick
the winner, *then* verify. Roughly in priority order (by weight × current cost):

1. **Cheap-dispatch front-end (biggest single win, ~54 % of calls).**
   - `b==0 → 0`; `a<b → (0, a)`; `pow2(b) → (a >> ctz(b), a & (b−1))`.
   - Power-of-two detection is `b & (b−1) == 0 ∧ b≠0`; `ctz` via the RISC-V
     `CTZ`/`CLZ` if modeled, else a small unrolled bit scan. This alone should
     collapse ~46 % of calls (all the n=3/n=4 pow2 shifts the current loop grinds
     through) to O(1).
2. **Register-resident single-word path (n=1, ~26 % genuine + the n=1 cheap share).**
   - When the divisor fits one limb (`b1=b2=b3=0`), the quotient/remainder come
     from at most 4 chained 64-bit divides (schoolbook over 4 dividend limbs) —
     **no normalization, no trial-quotient, no add-back**. With `DIVU` ~free, this
     is a handful of instructions, register-only.
   - **This already partly exists** (PLAN.md ~line 502; issue #9303):
     `EvmAsm/Evm64/DivMod/FastN1Program.lean` defines `evm_div_v6` / `evm_mod_v6`,
     which prepend a runtime dispatch routing single-limb divisors to a
     lightweight path (normalize one limb, 4 exact per-limb 128/64 divides via
     `divK_div128_v5`, remainder threaded with one MUL/SUB), falling through to
     the untouched `evm_div_v5`/`evm_mod_v5` for n≥2 and b=0. **Status per PLAN.md:
     executable + `#guard` tests landed (`FastN1ProgramTest.lean`), ~700→~420 step
     est, not yet verified.** *First Phase-3 action:* benchmark `evm_div_v6` in
     `bench/DivBench.lean` to confirm the n=1 win, decide whether to verify it,
     and treat it as the template for the still-missing pow2 / a<b / n=2 dispatch.
3. **Double-word path (n=2, ~18 % genuine).** The case the benchmark actually
   rewards. A specialized 2-limb divisor divide (still divide-heavy, no Knuth
   normalization) — evaluate divide-heavy reciprocal vs. schoolbook.
4. **Keep Knuth-D as the n≥3 tail (~1.8 %).** Correctness, not speed; do not
   invest further. Verify dispatch exhaustiveness reaches it.
5. **Divide-heavy vs Knuth-D for n=3,4 (optional study).** Since divides are ~free
   in the cost model, test whether a reciprocal/divide-heavy method beats Knuth-D
   even on the tail — but remember it's 1.8 %, so only if cheap to try.

Also: **MOD shares the core** (same buckets, n=1 = 68 %) — ensure paths return
both q and r so `evm_mod` reuses them. **SDIV/SMOD** (5 % of ops) are ~80 %
single-word on magnitude; a signed wrapper over the unsigned single-word path
covers most of them.

## 2. Verification leverage
- **`bv_udiv_umod_unique`** (in `EvmAsm/Evm64/EvmWordArith/Div.lean`) turns any
  fast path into "exhibit `(q, r)` with `a = b·q + r ∧ r < b`" — the universal
  hook for proving a new path correct against `BitVec.udiv`.
- The **`N1*` / `N1V5` single-limb-exact lemma corpus** in
  `EvmAsm/Evm64/DivMod/Spec/` is reusable for the single-word path.
- **Power-of-two path:** `a >> k` and `a & (2^k − 1)` give `(q, r)` with
  `a = 2^k·q + r ∧ r < 2^k` directly — feed to `bv_udiv_umod_unique`. Bitvector
  identities via `BitVec.eq_of_getLsbD_eq` / `getLsbD_ushiftRight` etc.
- Each path = **one sub-domain theorem** (correct on its class) + **one dispatch
  exhaustiveness proof** (the class predicates partition all inputs and route to
  the right path). Existing Knuth-D paths stay as the n≥3 tail unchanged.
- **NO `native_decide` / `bv_decide`** (CI-forbidden; see CLAUDE.md). Use
  `decide` (kernel `Nat` is GMP-backed), `omega`/`bv_omega`, `simp`/`ext`. Two CI
  gates enforce this: `scripts/check-forbidden-tactics.sh` and
  `scripts/check-axioms.sh` (trust base must stay the 3 classical axioms).

## 3. Method
1. Prototype candidates as **unverified** `Program`s.
2. Rank by the **weighted two-axis harness** (extend `bench/DivBench.lean` to
   read `bench/div-weights.json` and emit a single weighted cost per candidate;
   include the cheap classes — pow2, a<b — which the current baseline table omits).
3. Pick the winner per class; **then** verify (sub-domain theorem + dispatch
   exhaustiveness).
4. Report before/after weighted-cost deltas vs the Phase-1 baseline table above.

**Sanity targets** (rough, from the inverted curve + weights): cheap dispatch
should take the ~46 % pow2 calls and ~23 % a<b calls from 200–690 steps down to
tens of steps; the n=1 path should pull the dominant 49 % bucket well below its
current 620–690 steps. A frequency-weighted average step count is the headline
metric — compute it for the baseline first, then for each candidate.

## 4. Deliverables (Phase 3)
1. New/modified `Program`(s) in `EvmAsm/Evm64/DivMod/` implementing the dispatch.
2. Correctness proofs (sub-domain + exhaustiveness), trust base unchanged.
3. Extended `bench/DivBench.lean` consuming `bench/div-weights.json` → weighted
   cost; before/after table.
4. Updated `docs/divmod-evm-workload.md` (or a new `docs/divmod-evm-redesign.md`)
   with the measured deltas, feeding back into the gas-repricing discussion.
5. Phase 4 bootstrap (local) if work continues.

## 5. What NOT to do
- Don't re-derive the cost model or the workload data; both are settled (§0).
- Don't over-invest in the n≥3 tail — it's 1.8 % of *all* divides (≈3.8 % of
  genuine divides).
- Don't use branchless select across candidate quotients (speculation is wasteful
  in the cost model) — dispatch to exactly one path.
- Don't add `native_decide`/`bv_decide` anywhere (CI-forbidden).
- Don't optimize MOD/SDIV/SMOD separately first — make DIV's core reusable and
  wrap it.
