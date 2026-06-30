# EVM DIV/MOD Operand Workload — Empirical Distribution (Phase 2)

> **Purpose.** Replace the *reasoned-not-measured* divisor distribution from
> Phase 1 with **real mainnet data**, so the Phase 3 algorithm redesign optimizes
> a *frequency-weighted* objective instead of guessing which divisor classes
> matter. Machine-readable output: [`bench/div-weights.json`](../bench/div-weights.json).

## TL;DR — the four findings that reshape Phase 3

Across **145,888 division ops** from **32 distinct mainnet blocks** (frequency-representative — see Methodology):

1. **DIV dominates.** Of all division-family ops, **91.7 % are DIV**, 3.3 % MOD,
   4.0 % SDIV, 1.0 % SMOD. Optimize DIV first; MOD shares its core.
2. **Most divisors are small.** For the unsigned DIV+MOD core, divisor
   word-count **n=1 (<2⁶⁴) is 49 %**, n=2 is 21 %. **Small divisors — the
   *most expensive* case in today's `evm_div` (inverted cost curve, Phase 1) —
   are also the *most common*.** Optimizing them is doubly justified.
3. **Over half of all divides are not really divides.** **54 % are "cheap"**:
   `a < b` → quotient 0 (**23 %**), or **divisor is a power of two** (**46 %**) →
   a shift, or `b == 0` (0.2 %). A correct early-out / shift dispatch removes
   the division entirely for the majority of calls.
4. **The benchmark's worst case is real but rare.** Yoichi's repricing benchmark
   targets *genuine* (non-pow2) divisors just over 2⁶⁴ and 2¹²⁸ — i.e. n=2 and
   n=3 schoolbook work. But **89 % of real n=3 divisors and 97 % of real n=4
   divisors are powers of two**, and 67 % of n=3 are also `a<b`. **Genuine
   non-cheap divides needing n≥3 are only 1.8 % of all divides; 96 % of all
   genuine multi-word divides are n≤2.** The boundary worst-case the benchmark
   presumes "has no fast path" is a thin tail in practice.

**Net steer for Phase 3:** the win is a dispatch that (a) early-outs `a<b`,
(b) shifts on power-of-two divisors, (c) runs a register-resident single-word
(`n=1`) and double-word (`n=2`) path covering ~96 % of *genuine* work — and
keeps a correct-but-unoptimized Knuth-D tail for the ~1.8 % of n≥3 genuine cases.

---

## 1. Methodology & data sources

Three tiers, in decreasing order of representativeness. The headline numbers use
**Tier 1 only**; the others are documented for contrast/reproducibility.

### Tier 1 — real mainnet traces (gold; the headline data)
Opcode-level `debug_traceTransaction` against a public archive node
(`drpc.org`, free tier) with a custom JS tracer that emits the top-two stack
items at every `DIV`/`SDIV`/`MOD`/`SMOD` opcode. We trace **whole blocks
transaction-by-transaction**, so the operand stream is **frequency-representative
by construction**: a contract that executes many divisions contributes
proportionally many samples. DeFi math dominates naturally — no hand-picking.

- **Collector:** [`scripts/collect-div-operands.py`](../scripts/collect-div-operands.py)
- **Sample:** 32 distinct blocks, `25238313 .. 25431308` (~27 days, June 2026),
  sampled at two prime strides for temporal spread; **145,888 division ops**.
- **Raw data (committed, gzip):** [`bench/div-operands-mainnet.jsonl.gz`](../bench/div-operands-mainnet.jsonl.gz)
  — one JSON record per op `{blk, tx, op, a (dividend hex), b (divisor hex)}`.

### Tier 2 — execution-specs Python EVM instrumentation (offline, reproducible)
A monkeypatch hook that wraps the **real** spec opcode implementations
(`ethereum.forks.<fork>.vm.instructions.arithmetic.{div,sdiv,mod,smod}`) and
drives them with actual EVM bytecode through a minimal interpreter loop.

- **Script:** [`scripts/instrument-spec-div.py`](../scripts/instrument-spec-div.py)
- Used here to (a) **validate the Tier-1 tracer's operand semantics** — confirmed
  the dividend is stack-top and the divisor is next, matching the spec's pop
  order — and (b) provide a node-free path. By default it replays the benchmark's
  adversarial operands (Tier 3).

### Tier 3 — repricing benchmark (adversarial; NOT a distribution)
The operands in
`execution-specs/tests/benchmark/compute/instruction/test_arithmetic.py`
are deliberately worst-case (divisors just over 2⁶⁴ / 2¹²⁸). Captured to
[`bench/div-operands-benchmark.jsonl`](../bench/div-operands-benchmark.jsonl) as
the point-set the benchmark assumes. **These are 6 hand-chosen pairs, not a
frequency distribution** — they bound the worst case, nothing more.

### Representativeness caveats (read before trusting any number)
- **Heavy-tx under-sampling.** The free-tier node returns a server-side trace
  timeout (HTTP 408) on the heaviest ~3–8 % of transactions — typically the
  largest aggregator/MEV swaps, which are the most division-dense. Those drop
  out, so the *genuine multi-word* tail (n≥2) is, if anything, **under-counted**;
  the "cheap/small dominates" conclusion is conservative w.r.t. this bias.
- **Temporal window.** ~27 days of mid-2026 mainnet. DeFi composition shifts over
  time; re-run the collector to refresh. The patterns (small + pow2 dominate) are
  structural (fixed-point math, bps, decimals) and unlikely to invert.
- **No L2s / no historical forks.** Mainnet only. L2 workloads may differ.

`n` (divisor word-count): **0** = `b==0`, **1** = `b<2⁶⁴`, **2** = `b<2¹²⁸`,
**3** = `b<2¹⁹²`, **4** = `b<2²⁵⁶`. "Cheap" = `a<b ∨ pow2(b) ∨ b==0`.
SDIV/SMOD are bucketed on the **magnitude** (what the verified unsigned core
divides) and reported separately.

---

## 2. The distribution (Tier 1, 145,888 ops)

### 2.1 Op mix
| op | count | share |
|---|--:|--:|
| DIV  (0x04) | 133,716 | 91.7 % |
| SDIV (0x05) |   5,783 |  4.0 % |
| MOD  (0x06) |   4,885 |  3.3 % |
| SMOD (0x07) |   1,504 |  1.0 % |

### 2.2 Divisor word-count `n` — and how much of each `n` is cheap
DIV+MOD combined (the unsigned core, n=138,601). "pow2 within n" / "a<b within n"
are shares *of that n-bucket*; "genuine %" is the non-cheap remainder as a share
of **all** divides.

| n | share of all | pow2 within n | a<b within n | **genuine % of all** |
|--:|--:|--:|--:|--:|
| 0 (`b=0`) |  0.2 % |   — |   — | 0.0 % |
| 1 (`<2⁶⁴`) | **49.3 %** | 32 % | 24 % | **26.0 %** |
| 2 (`<2¹²⁸`) | **21.4 %** | 14 % |  2 % | **18.2 %** |
| 3 (`<2¹⁹²`) | 14.5 % | **89 %** | **67 %** | **1.6 %** |
| 4 (`<2²⁵⁶`) | 14.7 % | **97 %** |  5 % | **0.2 %** |

**Reading this table:** the n=3/n=4 buckets look substantial by raw share
(~15 % each) but are *almost entirely* powers of two (shifts) or `a<b`
(early-outs). After removing cheap cases, **genuine schoolbook work** is:
**n=1 → 26 %, n=2 → 18 %, n=3 → 1.6 %, n=4 → 0.2 %** of all divides.
**96 % of all genuine multi-word divides are n≤2.**

### 2.3 Cheap-vs-genuine summary (DIV+MOD core)
| class | share |
|---|--:|
| `a < b` → quotient 0 | 22.8 % |
| divisor power-of-two → shift | 46.0 % |
| `b == 0` → 0 | 0.2 % |
| **CHEAP total (`a<b ∨ pow2 ∨ b=0`)** | **54.1 %** |
| **GENUINE divide** | **45.9 %** |
| &nbsp;&nbsp;↳ genuine n=1 (single-word `DIVU`) | 26.0 % |
| &nbsp;&nbsp;↳ genuine n=2 (double-word) | 18.2 % |
| &nbsp;&nbsp;↳ genuine n≥3 (Knuth-D tail) | **1.8 %** |

### 2.4 Most common notable constant divisors (DIV+MOD)
| divisor | meaning | share |
|---|---|--:|
| `1`        | `/1` (no-op, often `mulDiv` denom) | 6.7 % |
| `10^4`     | basis points (10000) | 3.8 % |
| `10^18`    | wei→ether / 18-decimals | 3.7 % |
| `2`        | halving | 3.0 % |
| `10^2`     | percent | 2.0 % |
| `10^3`     | per-mille / k | 1.7 % |
| `3`        | (thirds) | 1.6 % |
| `2^128`    | Q128 fixed-point | 1.5 % |
| `10^6`     | USDC/USDT 6-decimals | 1.4 % |
| `2^96`     | Uniswap V3 Q96 | 1.0 % |
| `10^27`    | ray (Aave/Compound) | 0.6 % |

These few constants alone cover ~27 % of all divides. They confirm the structural
drivers: **fixed-point (Q96/Q128), decimals (10⁶/10¹⁸/ray), and basis points.**

### 2.5 Dividend word-count (secondary; affects iteration count)
DIV+MOD: m=0 16.0 %, m=1 13.1 %, m=2 17.0 %, m=3 **29.6 %**, m=4 **24.4 %**.
Dividends skew *large* (54 % are n≥3) even though divisors skew small — the
common shape is **big numerator ÷ small denominator** (token amounts ÷ rates).

### 2.6 Joint (dividend_n, divisor_n) — top cells (DIV+MOD)
| dividend_n | divisor_n | share | interpretation |
|--:|--:|--:|---|
| 4 | 4 | 13.9 % | full÷full — but 97 % of these divisors are pow2 (shift) |
| 2 | 1 | 13.2 % | medium ÷ small word |
| 3 | 2 | 13.1 % | large ÷ double-word |
| 1 | 1 | 12.9 % | **single-word ÷ single-word → one `DIVU`** |
| 0 | 1 | 11.5 % | `a<b` early-out (dividend 0 or < divisor) |
| 3 | 1 | 9.2 %  | large ÷ small word |

### 2.7 Signed SDIV+SMOD (on magnitude, n=7,287)
Even more concentrated on small magnitudes: **n=1 = 80 %**, n=2 = 20 %, n≥3 ≈ 0.
Cheap fraction is lower (30 %) — fewer pow2 (26 %) and far fewer `a<b` (4 %) — so
signed division is mostly **genuine single-word** work. Top divisors: `1` (11.5 %),
`10^18` (8.7 %), `10` (5.4 %). A single-word signed path covers ~80 % of signed
divides; magnitude reuse lets it share the unsigned core.

---

## 3. Contrast with the adversarial benchmark (Tier 3)

The repricing benchmark's DIV cases use dividend ≈ 2²⁵⁶−1 with divisors
`0x10000000000000033` (just over 2⁶⁴, **n=2, non-pow2**) and
`0x100000000000000000000000000000033` (just over 2¹²⁸, **n=3, non-pow2**),
explicitly chosen as "the worst case for a division algorithm with optimized
paths for division by 1 and 2 words."

| | benchmark assumes | mainnet reality |
|---|---|---|
| n=2 genuine (non-pow2) | the common case to beat | 18.2 % of divides ✓ (real, worth a path) |
| n=3 genuine (non-pow2) | the headline worst case | **1.6 %** of divides (thin tail) |
| n=4 genuine | — | **0.2 %** |
| pow2 divisor | (not exercised) | **46 %** — the single biggest class |
| `a<b` early-out | (not exercised) | **23 %** |

The benchmark is a fair *worst-case lower bound* for a 1-and-2-word-optimized
algorithm, but it is **not** where the real cost lives. Building the n=2 path it
demands is justified (18 % genuine); chasing the n=3 boundary beyond
correctness is optimizing a 1.6 % tail. The unexercised pow2 (46 %) and `a<b`
(23 %) classes are where the dynamic-instruction budget actually goes.

---

## 4. Recommended frequency weights for Phase 3

Use [`bench/div-weights.json`](../bench/div-weights.json) (`divmod` block) as the
canonical weights for the `bench/DivBench.lean` cost objective. The single number
to minimize is **frequency-weighted dynamic instruction count**:

```
cost = Σ_class  weight[class] · steps(candidate_algorithm, class)
```

Suggested dispatch classes and weights (DIV+MOD core, rounded; exact values in
the JSON):

| class | weight | Phase-3 path |
|---|--:|---|
| `b == 0` | 0.002 | return 0 |
| `a < b`  (and `b≠0`) | ~0.23 | return q=0, r=a (early-out) |
| `pow2(b)` (and `a≥b`) | ~0.42 | shift: `q = a >> log2(b)` |
| genuine n=1 | ~0.26 | register-resident single-word (≤ a few `DIVU`) |
| genuine n=2 | ~0.18 | double-word specialized path |
| genuine n≥3 | ~0.018 | existing Knuth-D tail (correctness, not speed) |

(`a<b` and `pow2` overlap slightly; the JSON keeps them as independent fractions
plus a combined `cheap_frac`. For a non-overlapping partition use `genuine_by_n`
for the divide paths and treat cheap as one early-out bucket totaling 0.54.)

**Weight-design notes:**
- Phase 1 showed the *current* `evm_div` is **most expensive on small divisors**
  (the loop runs `5−n` iterations). Since small + cheap divisors are also the
  most *frequent*, the frequency-weighted cost of today's implementation is
  dominated by exactly its worst region — the redesign upside is large.
- A correct `a<b` and `pow2` dispatch alone addresses 54 % of calls with O(1)
  work; this should be the first thing the Phase-3 harness measures.
- Keep operands register-resident (Phase 1: working set is a constant 28
  dwords / 2 pages regardless of divisor — purely an algorithmic artifact, not
  fundamental).

---

## 5. Reproduction

```bash
# Tier 1 — real mainnet (needs a debug_traceTransaction-capable endpoint):
python3 scripts/collect-div-operands.py --count 25 --stride 7919 --workers 3 \
    -o bench/div-operands-mainnet.jsonl
python3 scripts/analyze-div-operands.py bench/div-operands-mainnet.jsonl \
    --label mainnet --weights bench/div-weights.json

# Re-bucket the committed raw data without re-tracing:
zcat bench/div-operands-mainnet.jsonl.gz | \
    python3 scripts/analyze-div-operands.py /dev/stdin --label committed

# Tier 2/3 — offline spec-EVM instrumentation (adversarial operands):
execution-specs/.venv/bin/python scripts/instrument-spec-div.py --fork prague \
    -o bench/div-operands-benchmark.jsonl
```

Endpoint note: opcode-level full-block tracing exceeds free-tier limits; the
collector traces one tx per request and parallelizes with `--workers 3` (higher
concurrency triggers rate-limiting). It fail-fasts and circuit-breaks per block
so a throttled/heavy block is skipped rather than stalling the run.
