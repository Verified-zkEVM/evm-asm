# DIV-Perf Phase 2 Bootstrap — Real EVM Divisor-Distribution Data

> **What this file is.** A self-contained kickoff for Phase 2 of the DIV opcode
> performance effort. Open a *fresh* session, read **only** this file, and you
> have everything needed to do Phase 2 without re-deriving context.
>
> **Per-phase workflow.** Each phase gets (1) its own branch off the **latest**
> `origin/main`, (2) its own clean session, (3) a bootstrap file like this,
> generated at hand-off. Start with
> `git fetch origin && git checkout -b perf/div-evm-workload-data origin/main`.
> **Your last task this session is to generate the Phase 3 bootstrap**
> (`docs/agents/div-perf-phase3-algorithm-bootstrap.md`) — see Hand-off below.
>
> **Bootstrap files are LOCAL / UNCOMMITTED.** Do not commit or push this file
> or the Phase 3 bootstrap. Phase 2 *deliverables* (the workload doc + weights
> file + any instrumentation script) are committed as normal.

---

## 0. The big picture (why this effort exists)

We are optimizing the verified 256-bit EVM **DIV** opcode (`evm_div` in
`EvmAsm/Evm64/DivMod/Program.lean`), which is implemented as a RISC-V macro-
assembly subroutine and is **formally verified** against `EvmWord.div`
(`EvmAsm/Evm64/EvmWordArith/Div.lean`: `div a b = if b=0 then 0 else BitVec.udiv a b`).
The motivation is a gas-repricing question raised by @pirapira (Yoichi): DIV is
flat **`LOW` = 5 gas regardless of operand size**, but its real RISC-V/zkVM
proving cost varies ~3.4× with divisor size. Yoichi's benchmark
(`execution-specs/tests/benchmark/compute/instruction/test_arithmetic.py`)
deliberately picks divisors *just over* 2⁶⁴ and 2¹²⁸ — "the worst case for a
division algorithm with optimized paths for division by 1 and 2 words" — i.e. it
*presumes* fast paths we have not built.

### The zkVM cost model (ground truth — DO NOT re-litigate)
From Gassmann, Chaliasos, Sotiropoulos, Su, *"Evaluating Compiler Optimization
Impacts on zkVM Performance"* (arXiv:2508.17518v2; RISC0 + SP1):
- **Dynamic instruction (cycle) count is the PRIMARY, near-linear proving-cost
  driver** (Pearson > 0.9). Minimizing executed instructions is the objective.
- **Per-instruction cost is ~uniform; "division is not expensive"** (MUL = ADD,
  DIVU = 1 row). This overturns hardware instinct — Knuth-D's normalization /
  trial-quotient / add-back machinery is largely an artifact of "divides are
  expensive" and is a candidate to delete in favor of divide-heavy methods.
- **Branches are cheap (no misprediction) but speculation is wasteful** →
  compute exactly ONE path per input; never branchless-select among candidates.
- **Paging is a 2nd axis** (page-in/out ≈ 1130 cycles) — but Phase 1 showed it
  does **not** discriminate for a single DIV (see below).

### Phase 1 — DONE (already on branch `perf/div-divisor-fast-paths`)
Built `bench/DivBench.lean`: a two-axis cost harness that runs the **verified**
`step` semantics (`EvmAsm/Rv64/Execution.lean`) on concrete inputs and reports
`steps` (instructions), `loads/stores/memOps`, `dwords` (distinct 8-byte cells =
working set), `pages` (distinct 1 KiB pages), and `correct` (vs `a/b`).

Baseline numbers (dynamic instruction count of current `evm_div`, all correct):

| divisor | n | steps | memOps | dwords | pages |
|---|---|---|---|---|---|
| b=2 / b=7 (small) | 1 | 689 / 688 | 201 | 28 | 2 |
| b≈2⁶⁴ (bench #2) | 2 | 628 | 193 | 28 | 2 |
| b=2⁶⁴−1 | 1 | 623 | 179 | 28 | 2 |
| b≈2¹²⁸ (bench #1) | 3 | 449 | 143 | 28 | 2 |
| b full 256-bit | 4 | 204 | 71 | 28 | 2 |

**Key Phase-1 findings:** (a) cost curve is **inverted** — small divisors (the
common real case) are the *most* expensive, because the loop runs `5−n`
iterations; (b) memOps ≈ 29% of steps across all classes → the two cost axes are
**correlated**, so instruction count is a faithful single objective; (c) working
set is a **constant 28 dwords / 2 pages** for every divisor (phaseB zeroes all
scratch unconditionally) → paging does not discriminate; the only memory lever is
**algorithmic** (a register-resident method would cut working set to ~4–8 dwords).

Run it:
```
lake build EvmAsm.Evm64.DivMod.Program EvmAsm.Rv64.Execution EvmAsm.Evm64.Basic
lake env lean bench/DivBench.lean
```

---

## 1. Phase 2 goal

Replace the **reasoned-not-measured** divisor distribution with **real data**, so
Phase 3 can optimize a *frequency-weighted* objective instead of guessing which
divisor classes matter. Concretely, produce an empirical distribution for EVM
`DIV` (and ideally `MOD`, and signed `SDIV`/`SMOD`) operands, bucketed by what the
algorithm cares about:

- **divisor word-count `n`** ∈ {0 (b=0), 1 (<2⁶⁴), 2 (<2¹²⁸), 3 (<2¹⁹²), 4} — the
  primary dispatch dimension;
- **fraction with `a < b`** (→ quotient 0, a cheap early-out);
- **fraction with divisor a power of two** (→ could be a shift);
- **dividend word-count** (secondary; affects iteration count);
- ideally the joint (dividend-n, divisor-n) histogram.

The current educated guess (to confirm or refute): bimodal — small/constant
divisors dominate (÷2, ÷100, ÷10000 bps, ÷10¹⁸), a fixed-point cluster sits at
the word boundaries (Uniswap Q96/Q128 → 2⁹⁶/2¹²⁸), and a full-width tail
(balances/reserves).

## 2. Approach (suggested; adapt as you learn)

The cleanest instrumentation point is the **execution-specs Python EVM**, which
this repo vendors at `execution-specs/`. The DIV implementation is
`execution-specs/src/ethereum/forks/<fork>/vm/instructions/arithmetic.py`
(`divide`, ~line 117: `dividend = pop(...)`, `divisor = pop(...)`,
`quotient = dividend // divisor`). Add a hook that records `(dividend, divisor)`
each call, then run it over representative workloads:

1. **Yoichi's benchmark suite** (`execution-specs/tests/benchmark/`) — adversarial
   worst-cases, NOT frequency-representative; useful as a lower bound / sanity set.
2. **EEST / execution-spec-tests state tests** — broader, still synthetic.
3. **Real mainnet transactions / blocks** — the gold standard. Options: replay a
   block range with a tracing-capable client (geth `debug_traceBlock` with a
   custom JS/struct tracer that filters opcode `0x04`=DIV / `0x06`=MOD /
   `0x05`=SDIV / `0x07`=SMOD and logs the top-2 stack items), or an existing
   public opcode-trace dataset. Capturing a few hundred recent **DeFi-heavy**
   blocks is far more informative than uniform sampling.

**Caveat to surface in the writeup:** representativeness. The benchmark suite is
adversarial; EEST is synthetic; only real traces give true frequencies. State
clearly which source each number comes from and weight accordingly.

## 3. Deliverables

1. **`docs/divmod-evm-workload.md`** (committed) — the distribution tables, data
   sources, methodology, representativeness caveats, and the resulting
   recommended frequency weights per divisor class.
2. **A machine-readable weights file** (e.g. `bench/div-weights.json` — `{n0, n1,
   n2, n3, n4, a_lt_b_frac, pow2_frac, ...}`) that Phase 3's harness can consume
   to compute a single frequency-weighted cost number per candidate algorithm.
3. **The instrumentation script** (committed under `scripts/` or
   `execution-specs/`-adjacent) so the measurement is reproducible.
4. **The Phase 3 bootstrap** (`docs/agents/div-perf-phase3-algorithm-bootstrap.md`,
   LOCAL/UNCOMMITTED) — see Hand-off.

## 4. What NOT to do
- Don't optimize or touch `evm_div` yet — that's Phase 3.
- Don't re-derive the cost model; it's settled (§0).
- Don't trust the benchmark suite as a frequency distribution — it's worst-case.
- Don't add `native_decide`/`bv_decide` anywhere (CI-forbidden; see CLAUDE.md).

---

## Hand-off (your last task this session)

Generate `docs/agents/div-perf-phase3-algorithm-bootstrap.md` (LOCAL, uncommitted),
self-contained, covering:

- **Phase 3 goal:** re-derive the DIV algorithm under the corrected objective —
  minimize frequency-weighted instruction count (weights from your Phase 2
  data), keep operands register-resident (kill scratch spills), lean on cheap
  `DIVU`, one path per input. Candidate designs to evaluate with `bench/DivBench.lean`:
  (i) single-word register-resident schoolbook (4 exact 128/64 divides, no
  normalization/mulsub/addback — the dominant case per the inverted curve);
  (ii) `a<b → 0` and both-single-word → one `DIVU` early-outs;
  (iii) double-word specialized path; (iv) whether a divide-heavy / reciprocal
  method beats Knuth D for n=3,4 too once divides are free.
- **Verification leverage:** `bv_udiv_umod_unique` (in `EvmWordArith/Div.lean`)
  turns any fast path into "exhibit `(q,r)` with `a = b·q+r ∧ r<b`"; the `N1*`/
  `N1V5` single-limb-exact lemma corpus in `EvmAsm/Evm64/DivMod/Spec/` is
  reusable for the single-word path. Each path = one sub-domain theorem +
  one dispatch-exhaustiveness proof; existing Knuth-D paths stay as the n≥3 tail.
- **Method:** prototype candidates as *unverified* `Program`s, rank by the
  weighted two-axis harness, pick the winner, *then* verify. Carry forward the
  Phase 2 weights file and the baseline table above for before/after deltas.
- Embed the §0 cost model and the Phase-1 baseline table so Phase 3 is
  self-contained.
